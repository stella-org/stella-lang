-- | The driver of the scheduler: submitting a job, and running the ready queue
-- | until nothing is left to retry.
-- |
-- | Both stand outside every attempt. Submitting from inside one would open an
-- | attempt within an attempt, so neither is an `Elab` operation; an equation
-- | met inside an attempt goes through `unify` instead.
module Stella.Compiler.Elaborate.Driver.Loop
  ( Submission(..)
  , Submitted
  , PendingReport
  , RunResult(..)
  , RunReport
  , Attempter
  , submitAttempting
  , submitWith
  , submitEquality
  , runAttempting
  , runWith
  , run
  ) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.Vocabulary.Diagnostic (Defect(..), Diagnostic, Warning)
import Stella.Compiler.Elaborate.Kernel.Elab (SessionEnv, SolverState, drainWarnings)
import Stella.Compiler.Elaborate.CorePlus.Context (Origin)
import Stella.Compiler.Elaborate.Mechanism.Pending (EqualityGoal, Job(..), Pending, PendingId, Site)
import Stella.Compiler.Elaborate.Driver.Attempt (Attempt, Runner, attemptPendingWith, hostRunner)
import Stella.Compiler.Elaborate.Driver.Attempt as Run
import Stella.Compiler.Elaborate.Mechanism.Scheduler (Phase(..), create, invariants, lookupPending, nextReady, takeReady, unwakeable)
import Stella.Compiler.Elaborate.CorePlus.Type (MetaVar)
import Control.Monad.Rec.Class (Step(..), tailRec)
import Data.Array as Array
import Data.Array.NonEmpty (NonEmptyArray)
import Data.Array.NonEmpty as NonEmptyArray
import Data.Generic.Rep (class Generic)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Show.Generic (genericShow)
import Data.Tuple (Tuple(..))

-- | What submitting a job came to.
-- |
-- | **A first attempt that commits or registers lets elaboration go on; one that
-- | fails or breaks stops it, with the report a loop stopping there would
-- | make.** Stopping is where the warnings committed so far are drained, by the
-- | one finalizer a loop ends with, so a driver that stops at a submission reads
-- | them as it would after a loop, and needs no loop run to read them — which
-- | would retry jobs a failure should have stopped short of.
data Submission
  = Continue Submitted
  | Stop RunReport

-- | A job just submitted whose first attempt committed or registered, and what
-- | that attempt came to.
type Submitted =
  { id :: PendingId
  , attempt :: Attempt
  }

-- | A job the loop stopped at, as a report names it.
-- |
-- | The job is carried whole, since the origin and the metavariables alone do
-- | not say which goal it was. `awaiting` is what it is registered under, and is
-- | empty for a job still on the ready queue.
type PendingReport =
  { id :: PendingId
  , origin :: Origin
  , job :: Job
  , awaiting :: Set MetaVar
  }

-- | Where the driver stopped — at the end of a loop, or at a submission whose
-- | first attempt failed or broke — and the warnings the attempts that committed
-- | before then made.
type RunReport =
  { result :: RunResult
  , warnings :: P.Array Warning
  }

-- | Where the driver stopped, running the ready queue or submitting a job.
data RunResult
  -- | No job is left.
  = Completed
  -- | An attempt failed, a job's first on submission or a retry. The driver
  -- | stops at the first failure: the equation it rolled back is information
  -- | the other jobs would have been retried without, and nothing yet tells a
  -- | failure of their own from one that follows from it.
  | Rejected Diagnostic
  -- | The ready queue is empty and these jobs wait on metavariables no
  -- | assignment has reached, in identifier order. Each awaits at least one.
  | Blocked (NonEmptyArray PendingReport)
  -- | The fuel ran out with this job next on the ready queue, where it stays.
  | Exhausted PendingReport
  -- | A defect, on submission or on a retry. Nothing further is attempted.
  | Halted Defect

-- | How the driver attempts the job named: one attempt, from a state in which no
-- | queue holds the job, with the scheduler acted on as the attempt comes to.
-- | Which job is attempted, and the fuel a retry spends, are the driver's; how
-- | the job is carried out is the attempter's.
type Attempter = PendingId -> SolverState -> Tuple Attempt SolverState

-- | Create a job and attempt it at once, with the attempter given.
-- |
-- | Just after `create` is one of the two points at which a job may be
-- | attempted. A first attempt spends no fuel, fuel bounding the scheduler's
-- | retries alone.
submitAttempting :: Attempter -> Site -> Job -> SolverState -> Tuple Submission SolverState
submitAttempting attempter site job s0 = case attempt of
  Run.Rejected diagnostic -> stop (Rejected diagnostic)
  Run.Halted defect -> stop (Halted defect)
  Run.Committed -> Tuple (Continue { id, attempt }) s
  Run.Registered _ -> Tuple (Continue { id, attempt }) s
  where
  Tuple id scheduler = create site job s0.tentative.scheduler
  Tuple attempt s = attempter id (s0 { tentative { scheduler = scheduler } })
  stop result = case stopped result s of
    Tuple stoppedWith s' -> Tuple (Stop stoppedWith) s'

-- | `submitAttempting`, each job carried out by the runner given.
submitWith :: SessionEnv -> Runner -> Site -> Job -> SolverState -> Tuple Submission SolverState
submitWith session runner = submitAttempting (attemptPendingWith session runner)

-- | `submitWith hostRunner`, for an equation.
submitEquality :: SessionEnv -> Site -> EqualityGoal -> SolverState -> Tuple Submission SolverState
submitEquality session site goal = submitWith session hostRunner site (JobUnify goal)

-- | `runWith hostRunner`.
run :: SessionEnv -> SolverState -> Tuple RunReport SolverState
run session = runWith session hostRunner

-- | Retry the jobs on the ready queue until it is empty, or until something
-- | stops the loop.
-- |
-- | **The loop records no trace of its own**: a trace is the attempts', kept
-- | where they record it, and the loop neither reads nor drains it.
-- |
-- | **Fuel is checked before a retry is taken, and spent once it is.** A retry
-- | the fuel does not reach stays on the ready queue and is named, and one that
-- | has been attempted has spent a unit whatever it came to. A job on the queue
-- | for its first attempt — one created inside another attempt — spends none,
-- | as a job submitted and attempted at once spends none. The loop is a `tailRec`,
-- | since the number of retries is bounded by fuel rather than by the stack.
-- |
-- | The attempter is given once and every attempt of the loop is its: the
-- | session it reads is assembled before the first job and never changes.
-- |
-- | At quiescence, a scheduler whose tables disagree, and a job awaiting
-- | nothing, are defects; otherwise every job left is reported as blocked.
-- |
-- | **The warnings are drained where the loop stops**, every one the attempts
-- | that committed made, those made before the loop by a job submitted and
-- | attempted at once among them, into the report and out of the state: a
-- | driver reading them reads them once.
runAttempting :: Attempter -> SolverState -> Tuple RunReport SolverState
runAttempting attempter s0 =
  let
    Tuple result s = tailRec step s0
  in
    stopped result s
  where
  step s = case nextReady s.tentative.scheduler of
    Nothing ->
      Done (Tuple (quiesce s) s)
    Just next
      | next.phase == Retry && s.retained.fuel <= 0 ->
          Done (Tuple (exhausted s next.id) s)
      | otherwise -> case takeReady s.tentative.scheduler of
          Nothing ->
            Done (Tuple (quiesce s) s)
          Just (Tuple id scheduler) ->
            let
              spent = if next.phase == Retry then 1 else 0
              taken = s
                { tentative { scheduler = scheduler }
                , retained { fuel = s.retained.fuel - spent }
                }
            in
              case attempter id taken of
                Tuple Run.Committed s' -> Loop s'
                Tuple (Run.Registered _) s' -> Loop s'
                Tuple (Run.Rejected diagnostic) s' -> Done (Tuple (Rejected diagnostic) s')
                Tuple (Run.Halted defect) s' -> Done (Tuple (Halted defect) s')

  exhausted s id = case lookupPending s.tentative.scheduler id of
    Just p -> Exhausted (report p)
    Nothing -> Halted (PendingAbsent id)

-- | `runAttempting`, each job carried out by the runner given.
runWith :: SessionEnv -> Runner -> SolverState -> Tuple RunReport SolverState
runWith session runner = runAttempting (attemptPendingWith session runner)

-- | The report of a driver stopping with the result given, the warnings
-- | committed so far drained into it and out of the state.
stopped :: RunResult -> SolverState -> Tuple RunReport SolverState
stopped result s =
  let
    Tuple warnings drained = drainWarnings s
  in
    Tuple { result, warnings } drained

-- | Where the loop stopped with nothing on the ready queue.
-- |
-- | **A defect of the scheduler comes before anything is reported as waiting.**
-- | A job whose registrations disagree with its `awaiting`, or one awaiting
-- | nothing, is one no assignment reaches, so it is checked first; only then is
-- | a job left a job waiting on the program.
quiesce :: SolverState -> RunResult
quiesce s = case NonEmptyArray.fromArray (invariants scheduler) of
  Just broken ->
    Halted (SchedulerBroken broken)
  Nothing -> case NonEmptyArray.fromArray (Array.sort (unwakeable scheduler)) of
    Just lost ->
      Halted (UnreachablePending lost)
    Nothing -> case NonEmptyArray.fromArray (map report (Array.fromFoldable (Map.values scheduler.pending))) of
      Nothing -> Completed
      Just waiting -> Blocked waiting
  where
  scheduler = s.tentative.scheduler

report :: Pending -> PendingReport
report p = { id: p.id, origin: p.site.origin, job: p.job, awaiting: p.awaiting }

derive instance Eq Submission
derive instance Generic Submission _

instance Show Submission where
  show x = genericShow x

derive instance Eq RunResult
derive instance Generic RunResult _

instance Show RunResult where
  show x = genericShow x
