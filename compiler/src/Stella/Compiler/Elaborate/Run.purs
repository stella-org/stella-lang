-- | Running `Elab` from outside: one attempt of a pending job, and the admission
-- | of what a postponed attempt waits on (D40).
-- |
-- | An attempt is a boundary and not a combinator of `Elab`. What it reaches is
-- | handed back as the `Outcome` it is, so a defect is never a value some later
-- | step could go on from.
module Stella.Compiler.Elaborate.Run
  ( Attempt(..)
  , Runner
  , runAttempt
  , admit
  , hostRunner
  , attemptPending
  , attemptPendingWith
  ) where

import Prelude

import Stella.Compiler.Elaborate.Diagnostic (Defect(..), Diagnostic, Inadmissible(..))
import Stella.Compiler.Elaborate.Handle (emptyArena)
import Stella.Compiler.Elaborate.Elab (Cause(..), Elab, Outcome(..), SessionEnv, SolverState, break, checkSynthesisTarget, runElabIn, unify, withFrame)
import Stella.Compiler.Elaborate.Pending (Job(..), Pending, PendingId, goalOf)
import Stella.Compiler.Elaborate.Scheduler (complete, lookupPending, reblock, unwakeable)
import Stella.Compiler.Elaborate.Type (MetaVar)
import Stella.Compiler.Elaborate.Unify (MetaBinding(..), MetaContext, lookupMeta)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Set as Set
import Data.Show.Generic (genericShow)
import Data.Tuple (Tuple(..))

-- | What attempting a pending job came to, once the scheduler has acted on it.
data Attempt
  -- | Solved and committed; the job is gone from every table.
  = Committed
  -- | Postponed, and registered under the metavariables admitted.
  | Registered (Set MetaVar)
  -- | Failed; the job is gone from every table, and the diagnostic is what to
  -- | report.
  | Rejected Diagnostic
  -- | A defect. Nothing further is attempted.
  | Halted Defect

-- | One attempt: a transaction over what it owns.
-- |
-- | **The write set is emptied before the checkpoint is taken.** The checkpoint
-- | is what a rollback restores, so a set emptied afterwards would be put back —
-- | with the previous job's assignments in it — by this attempt's own rollback,
-- | at the moment a postponement is about to read it. An abandoned attempt
-- | therefore needs no emptying of its own, and a committed one is emptied again
-- | so that nothing it wrote reaches the next job's dependencies.
-- |
-- | **The arena is emptied at the same two points, for the same reason.** A
-- | handle lives for the attempt that issued it: what a synthesizer returns is
-- | resolved before the attempt commits, and one that postpones or fails leaves
-- | the checkpoint's empty arena behind.
-- |
-- | Every outcome but `Done` rolls back, what is retained being kept. The action
-- | reads the session given and no frame; `attemptPendingWith` is what runs one
-- | under a job's frame.
runAttempt :: forall a. SessionEnv -> Elab a -> SolverState -> Tuple (Outcome a) SolverState
runAttempt session action s0 =
  case runElabIn session checkpoint action of
    Tuple (Done a) s ->
      Tuple (Done a) (s { tentative { written = Set.empty, arena = emptyArena } })
    Tuple outcome s ->
      Tuple outcome { tentative: checkpoint.tentative, retained: s.retained }
  where
  checkpoint = s0 { tentative { written = Set.empty, arena = emptyArena } }

-- | The metavariables a postponement may be registered under, read against `Ψ`
-- | as the rollback left it.
-- |
-- | A metavariable the rollback left unsolved is one that existed before the
-- | attempt and that an assignment can still reach; one the attempt created is
-- | gone, and one already solved has had its assignment.
-- |
-- | **A postponement raised above the mechanism is admitted as it stands**: every
-- | metavariable it names must be one of those, and the set may not be empty. A
-- | name that fails is a defect in whoever postponed, and dropping it instead
-- | would hide the reading that produced it.
-- |
-- | **One the mechanism raised has its dependencies extracted.** A fresh row tail
-- | can be the only thing an equation is stuck on, and it is gone after the
-- | rollback; what would change the re-run is a solution for one of the
-- | metavariables whose refinement produced it, which the attempt's write set
-- | names. So the dependencies are what survives of the two sets together, and
-- | only where nothing survives is the postponement a defect.
admit :: MetaContext -> Cause -> Either Inadmissible (Set MetaVar)
admit metas = case _ of
  ExplicitPostponement ms
    | Set.isEmpty ms -> Left AwaitsNothing
    | otherwise ->
        case Array.head (Array.mapMaybe unwakeable (Set.toUnfoldable ms)) of
          Just reason -> Left reason
          Nothing -> Right ms

  SolverStuck { blockedOn, written } ->
    let
      durable = Set.filter unsolved (Set.union blockedOn written)
    in
      if Set.isEmpty durable then Left NothingDurable else Right durable

  where
  unwakeable m = case lookupMeta metas m of
    Just (Unsolved _) -> Nothing
    Just (Assigned _) -> Just (AwaitsSolved m)
    Nothing -> Just (AwaitsAbsent m)

  unsolved m = case lookupMeta metas m of
    Just (Unsolved _) -> true
    _ -> false

-- | What carries a job out inside an attempt.
-- |
-- | The attempt, the rollback, and the admission are the same whoever runs the
-- | job, so a host implementation and a guest one running on Steam are two
-- | runners handed to the one boundary.
type Runner = Pending -> Elab Unit

-- | The host's runner, for the jobs the mechanism itself carries out. It holds
-- | no synthesizer, so a synthesis job is one it cannot run.
hostRunner :: Runner
hostRunner p = case p.job of
  JobUnify goal -> unify p.site goal
  JobSynthesis goal -> break (SynthesizerUnavailable (goalOf goal).synthesizer)

-- | `attemptPendingWith hostRunner`.
attemptPending :: SessionEnv -> PendingId -> SolverState -> Tuple Attempt SolverState
attemptPending session = attemptPendingWith session hostRunner

-- | Attempt the pending job named with the runner given, and act on the outcome.
-- |
-- | **The job is one no queue holds**: `pending` holds it, it awaits nothing,
-- | and it is not on the ready queue. A job is in that state at two points —
-- | just after `create`, before its first attempt, and just after `takeReady`,
-- | once a `wake` has queued it for another. `unwakeable` reads `awaiting` and the
-- | ready queue, and that the blocked table does not hold the job either follows
-- | from the scheduler's invariant that it registers a job exactly under what the
-- | job awaits.
-- |
-- | **A postponement is admitted in the same step as the rollback**, against the
-- | `Ψ` that rollback left, so no postponement reaches the scheduler unchecked. A
-- | solved or failed job is removed from every table, and a defect leaves the
-- | state as the rollback left it.
attemptPendingWith :: SessionEnv -> Runner -> PendingId -> SolverState -> Tuple Attempt SolverState
attemptPendingWith session runner id s0 = case lookupPending s0.tentative.scheduler id of
  Nothing ->
    Tuple (Halted (PendingAbsent id)) s0
  Just p
    | not (Array.elem id (unwakeable s0.tentative.scheduler)) ->
        Tuple (Halted (PendingStillScheduled id)) s0
    | otherwise -> attempted p
  where
  attempted p = case runAttempt session (withFrame (frameOf p) (checked p *> runner p)) s0 of
    Tuple (Done _) s ->
      Tuple Committed (finish s)
    Tuple (Failed diagnostic) s ->
      Tuple (Rejected diagnostic) (finish s)
    Tuple (Broke defect) s ->
      Tuple (Halted defect) s
    Tuple (Postponed cause) s -> case admit s.tentative.metas cause of
      Left reason ->
        Tuple
          (Halted (PostponementInadmissible { origin: p.site.origin, job: p.job, reason }))
          s
      Right ms ->
        Tuple (Registered ms) (s { tentative { scheduler = reblock p ms s.tentative.scheduler } })

  finish s = s { tentative { scheduler = complete id s.tentative.scheduler } }

  -- A synthesis job's target is checked inside the attempt and before the
  -- runner, so a job that fails it runs no synthesizer and is rolled back.
  -- The site the job was created at, and its goal where it has one. Nothing
  -- inside the attempt changes either.
  frameOf p =
    { site: p.site
    , goal: case p.job of
        JobSynthesis goal -> Just { id: p.id, goal }
        JobUnify _ -> Nothing
    }

  checked p = case p.job of
    JobSynthesis goal -> checkSynthesisTarget p.id p.site goal
    JobUnify _ -> pure unit

derive instance Eq Attempt
derive instance Generic Attempt _

instance Show Attempt where
  show x = genericShow x
