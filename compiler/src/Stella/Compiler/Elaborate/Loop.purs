-- | The driver of the scheduler: submitting a job, and running the ready queue
-- | until nothing is left to retry.
-- |
-- | Both stand outside every attempt. Submitting from inside one would open an
-- | attempt within an attempt, so neither is an `Elab` operation; an equation
-- | met inside an attempt goes through `unify` instead.
module Stella.Compiler.Elaborate.Loop
  ( Submitted
  , PendingReport
  , RunResult(..)
  , submitWith
  , submitEquality
  , runWith
  , run
  ) where

import Prelude

import Stella.Compiler.Elaborate.Diagnostic (Defect(..), Diagnostic)
import Stella.Compiler.Elaborate.Elab (SolverState)
import Stella.Compiler.Elaborate.Context (Origin)
import Stella.Compiler.Elaborate.Pending (EqualityGoal, Job(..), Pending, PendingId, Site)
import Stella.Compiler.Elaborate.Run (Attempt, Runner, attemptPendingWith, hostRunner)
import Stella.Compiler.Elaborate.Run as Run
import Stella.Compiler.Elaborate.Scheduler (Phase(..), create, invariants, lookupPending, nextReady, takeReady, unwakeable)
import Stella.Compiler.Elaborate.Type (MetaVar)
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

-- | A job just submitted, and what its first attempt came to.
-- |
-- | `Committed` and `Registered` let elaboration go on; `Rejected` stops the
-- | compilation, and `Halted` the session.
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

-- | Where running the ready queue stopped.
data RunResult
  -- | No job is left.
  = Completed
  -- | A retried job failed. The loop stops at the first failure: the equation
  -- | it rolled back is information the other jobs would have been retried
  -- | without, and nothing yet tells a failure of their own from one that
  -- | follows from it.
  | Rejected Diagnostic
  -- | The ready queue is empty and these jobs wait on metavariables no
  -- | assignment has reached, in identifier order. Each awaits at least one.
  | Blocked (NonEmptyArray PendingReport)
  -- | The fuel ran out with this job next on the ready queue, where it stays.
  | Exhausted PendingReport
  -- | A defect. Nothing further is attempted.
  | Halted Defect

-- | Create a job and attempt it at once, with the runner given.
-- |
-- | Just after `create` is one of the two points at which a job may be
-- | attempted. A first attempt spends no fuel, fuel bounding the scheduler's
-- | retries alone.
submitWith :: Runner -> Site -> Job -> SolverState -> Tuple Submitted SolverState
submitWith runner site job s0 =
  let
    Tuple id scheduler = create site job s0.tentative.scheduler
    Tuple attempt s = attemptPendingWith runner id (s0 { tentative { scheduler = scheduler } })
  in
    Tuple { id, attempt } s

-- | `submitWith hostRunner`, for an equation.
submitEquality :: Site -> EqualityGoal -> SolverState -> Tuple Submitted SolverState
submitEquality site goal = submitWith hostRunner site (JobUnify goal)

-- | `runWith hostRunner`.
run :: SolverState -> Tuple RunResult SolverState
run = runWith hostRunner

-- | Retry the jobs on the ready queue until it is empty, or until something
-- | stops the loop.
-- |
-- | **Fuel is checked before a retry is taken, and spent once it is.** A retry
-- | the fuel does not reach stays on the ready queue and is named, and one that
-- | has been attempted has spent a unit whatever it came to. A job on the queue
-- | for its first attempt — one created inside another attempt — spends none,
-- | as a job submitted and attempted at once spends none. The loop is a `tailRec`,
-- | since the number of retries is bounded by fuel rather than by the stack.
-- |
-- | At quiescence, a scheduler whose tables disagree, and a job awaiting
-- | nothing, are defects; otherwise every job left is reported as blocked.
runWith :: Runner -> SolverState -> Tuple RunResult SolverState
runWith runner = tailRec step
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
              case attemptPendingWith runner id taken of
                Tuple Run.Committed s' -> Loop s'
                Tuple (Run.Registered _) s' -> Loop s'
                Tuple (Run.Rejected diagnostic) s' -> Done (Tuple (Rejected diagnostic) s')
                Tuple (Run.Halted defect) s' -> Done (Tuple (Halted defect) s')

  exhausted s id = case lookupPending s.tentative.scheduler id of
    Just p -> Exhausted (report p)
    Nothing -> Halted (PendingAbsent id)

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

derive instance Eq RunResult
derive instance Generic RunResult _

instance Show RunResult where
  show x = genericShow x
