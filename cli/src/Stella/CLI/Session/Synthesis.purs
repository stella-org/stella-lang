-- | A build's synthesis jobs carried out on its compile-time session: a goal's
-- | synthesizer run as a guest, on the session its macros' parsers run on.
-- |
-- | **A synthesizer of the build runs from the bytecode the build wrote**: before
-- | it is invoked, the module declaring it is loaded, as
-- | [CompileTime](CompileTime.purs) loads one. A module is compiled after every
-- | module it imports, so a synthesizer an import reaches has its bytecode
-- | written by then.
-- |
-- | **What a run comes to is the attempter's** ([Attempter](Broker/Attempter.purs)),
-- | but for what says nothing of the program. A fault and a budget used up are
-- | the synthesizer's, and the session lost and the interpreter's own defect the
-- | session's: each is thrown as a failure of compile-time execution.
module Stella.CLI.Session.Synthesis
  ( SynthesisSettings
  , defaultSynthesisSettings
  , Synthesizing
  , openingSynthesis
  ) where

import Prelude

import Control.Monad.Except (runExceptT)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Effect.Ref (Ref)
import Run (AFF, EFFECT, Run)
import Run.Except (EXCEPT, throw)
import Stella.CLI.Effect.Process (PROCESS)
import Stella.CLI.Session.Broker (Cancellation, SessionHealth)
import Stella.CLI.Session.Broker.Attempter (Interrupted(..), guestAttempter)
import Stella.CLI.Session.Client (Launch, Session)
import Stella.CLI.Session.CompileTime (CompileTimeError(..), Loading, ensureLoaded, opened)
import Stella.Compiler.Build (BuiltModules)
import Stella.Compiler.Elaborate.Driver.Attempt (attemptPending)
import Stella.Compiler.Elaborate.Driver.Loop (AttempterM)
import Stella.Compiler.Elaborate.Kernel.Elab (SessionEnv)
import Stella.Compiler.Elaborate.Mechanism.Pending (Job(..), goalOf)
import Stella.Compiler.Elaborate.Mechanism.Scheduler (lookupPending)
import Stella.Compiler.Elaborate.Protocol.Guest.Shape (Descriptor)
import Stella.Compiler.Elaborate.Vocabulary.Diagnostic as Defect
import Stella.Compiler.Elaborate.Vocabulary.Outcome (Attempt(..))
import Stella.Compiler.TypedCore.Name (Qualified(..))
import Type.Row (type (+))

-- | How a synthesizer run on the machine is bounded: the steps one invocation
-- | may take, each attempt being one invocation, and no total over the build.
type SynthesisSettings = { budget :: Int }

defaultSynthesisSettings :: SynthesisSettings
defaultSynthesisSettings = { budget: 1_000_000 }

-- | What running a build's synthesizers takes: the session shared with its
-- | parsers and how to open it, `Stella.Elab`'s descriptor, the modules loaded
-- | so far, the budget of every invocation, and the compilation's
-- | cancellation, attempt numbers, and session health.
type Synthesizing r =
  { held :: Ref (Maybe Session)
  , launch :: Launch
  , descriptor :: Descriptor
  , loading :: Loading (PROCESS + r)
  , budget :: Int
  , cancellation :: Cancellation
  , attempts :: Ref Int
  , health :: Ref SessionHealth
  }

-- | Attempt the job named: a synthesis job by its synthesizer on the session,
-- | opened where it is not yet, the synthesizer's module loaded first; any
-- | other job by the host.
openingSynthesis :: forall r. Synthesizing r -> BuiltModules -> SessionEnv -> AttempterM (Run (EXCEPT CompileTimeError + PROCESS + AFF + EFFECT + r))
openingSynthesis running built env id s = case lookupPending s.tentative.scheduler id of
  Just { job: JobSynthesis record, site } -> do
    let synthesizer@(Qualified declaring _) = (goalOf record).synthesizer
    session <- opened running.held running.launch
    ensureLoaded running.loading session built declaring
    let
      guests =
        { session
        , descriptor: running.descriptor
        , env
        , budget: running.budget
        , cancellation: running.cancellation
        , attempts: running.attempts
        , health: running.health
        }
    runExceptT (guestAttempter guests id s) >>= case _ of
      Left (CalledOff _ _) -> throw (SessionBroke "the compilation was called off while a synthesizer ran")
      Right (Tuple attempt s') -> case attempt of
        Halted (Defect.SynthesizerFaulted _ detail) -> throw (SynthesizerFaulted { synthesizer, goal: site.origin, detail })
        Halted (Defect.SynthesizerExhausted _ budget) -> throw (SynthesizerBudgetExhausted { synthesizer, goal: site.origin, budget })
        Halted (Defect.GuestSessionBroke why) -> throw (SessionBroke why)
        Halted (Defect.InterpreterDefect why) -> throw (SessionBroke ("the interpreter's own defect: " <> why))
        _ -> pure (Tuple attempt s')
  _ -> pure (attemptPending env id s)
