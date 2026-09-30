-- | Running synthesis jobs: a registry of synthesizers written in the host, the
-- | attempt of a job by whichever runner its kind needs, and the loop and
-- | submission over both.
-- |
-- | **The registry is how the host is set up to bootstrap and to be tested**,
-- | and not where a standard resolver lives: a synthesizer a program names is
-- | resolved in it, and one it does not hold is a defect of the session.
module Stella.Compiler.Elaborate.Driver.Synthesis
  ( Registry
  , resolveSynthesizer
  , attemptJob
  , submitSynthesis
  , submitSynthesisM
  , runSynthesis
  ) where

import Prelude

import Stella.Compiler.Elaborate.CorePlus.Term (Region, TermMetaVar)
import Stella.Compiler.Elaborate.CorePlus.Type (XType)
import Stella.Compiler.Elaborate.Driver.Attempt (attemptPending)
import Stella.Compiler.Elaborate.Driver.Conversation (runSynthesizerWith)
import Stella.Compiler.Elaborate.Driver.Loop (Attempter, AttempterM, RunReport, Submission, runAttempting, submitAttemptingM)
import Stella.Compiler.Elaborate.Kernel.Elab (SessionEnv, SolverState)
import Stella.Compiler.Elaborate.Mechanism.Pending (Job(..), Site, SynthRef, goalOf, newGoal)
import Stella.Compiler.Elaborate.Mechanism.Scheduler (lookupPending)
import Stella.Compiler.Elaborate.Protocol.Facade (Synthesizer)
import Data.Identity (Identity(..))
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))

-- | The synthesizers a session can run, by the name a goal gives.
type Registry = Map SynthRef Synthesizer

resolveSynthesizer :: Registry -> SynthRef -> Maybe Synthesizer
resolveSynthesizer registry name = Map.lookup name registry

-- | Attempt the job named by the runner its kind needs: a synthesis job by a
-- | conversation with the synthesizer its goal names, resolved in the registry
-- | once the attempt has opened, and any other by the host's own runner. A job
-- | `pending` does not hold is not known to be a synthesis job, and is reported
-- | by the host's runner, which traces nothing.
attemptJob :: SessionEnv -> Registry -> Attempter
attemptJob session registry id s = case lookupPending s.tentative.scheduler id of
  Just { job: JobSynthesis _ } -> runSynthesizerWith session (resolveSynthesizer registry) id s
  _ -> attemptPending session id s

-- | `⟨ τ by f ⟩` at a site and in a region of cells, from outside every
-- | attempt: the goal and the target its result is assigned to installed in one
-- | state transition with the job, and the job attempted at once. The target is
-- | returned for the caller to place as `ETermMeta`.
submitSynthesis
  :: SessionEnv
  -> Registry
  -> Site
  -> XType
  -> SynthRef
  -> Maybe Region
  -> SolverState
  -> Tuple { target :: TermMetaVar, submission :: Submission } SolverState
submitSynthesis session registry site expectedType synthesizer region s0 =
  case submitSynthesisM (\id s -> Identity (attemptJob session registry id s)) site expectedType synthesizer region s0 of
    Identity submitted -> submitted

-- | `submitSynthesis`, the job attempted by the attempter given in its monad.
submitSynthesisM
  :: forall m
   . Monad m
  => AttempterM m
  -> Site
  -> XType
  -> SynthRef
  -> Maybe Region
  -> SolverState
  -> m (Tuple { target :: TermMetaVar, submission :: Submission } SolverState)
submitSynthesisM attempter site expectedType synthesizer region s0 =
  submitAttemptingM attempter site (JobSynthesis goal) (s0 { tentative { metas = metas } }) <#> case _ of
    Tuple submission s -> Tuple { target: (goalOf goal).target, submission } s
  where
  Tuple goal metas = newGoal site expectedType synthesizer region s0.tentative.metas

-- | Retry the jobs on the ready queue, each attempted by `attemptJob`.
runSynthesis :: SessionEnv -> Registry -> SolverState -> Tuple RunReport SolverState
runSynthesis session registry = runAttempting (attemptJob session registry)
