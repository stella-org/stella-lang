-- | Carrying out the scheduler's attempts on one session: a synthesis job by its
-- | guest, anything else by the host.
-- |
-- | **The scheduler's loop is the compiler's, run in a monad that can wait on the
-- | session** ([Loop](../../../../../../compiler/src/Stella/Compiler/Elaborate/Driver/Loop.purs)).
-- | A synthesis job is run as its goal's synthesizer names, the name being the
-- | guest's global, as a new invocation every time it is attempted, so a retry
-- | starts the guest from its beginning. An equation, or any job whose kind is not
-- | known, is the host's own runner's.
-- |
-- | **What a run comes to is settled here, and nothing of it is lost**
-- | ([Settle](Settle.purs)). An attempt ended — by the guest, by the host, or as the
-- | defect an invocation's failure is — goes back to the scheduler. A session to be
-- | replaced is recorded where the one holding the session reads it. A run cancelled
-- | is no attempt: it stops the driver there and then, with the state the
-- | cancellation left and whether the session is still to be used. **The
-- | cancellation is the whole compilation's**, so the host's job is not attempted
-- | once it is asked for either: the driver stops at that job, taken and not run.
-- |
-- | **An attempt names one invocation for good**: the numbers are drawn in order and
-- | never again, and a session that has drawn every number it can is to be
-- | replaced. Every invocation is given the same budget.
module Stella.CLI.Session.Broker.Attempter
  ( Guests
  , Interrupted(..)
  , GuestRun
  , guestAttempter
  , runGuests
  , submitGuest
  , submitGuestSynthesis
  , lastAttempt
  ) where

import Prelude

import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.Trans.Class (lift)
import Data.Either (Either)
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Run (AFF, EFFECT, Run, liftEffect)
import Stella.CLI.Session.Broker (Cancellation, SessionHealth(..), cancelRequested, runGuest)
import Stella.CLI.Session.Broker.Settle (Settled(..), settle)
import Stella.CLI.Session.Client (Session)
import Stella.Compiler.Elaborate.CorePlus.Term (Region, TermMetaVar)
import Stella.Compiler.Elaborate.CorePlus.Type (XType)
import Stella.Compiler.Elaborate.Driver.Attempt (Attempt, OpenResult(..), attemptPending)
import Stella.Compiler.Elaborate.Driver.Conversation (abandoned, openConversation)
import Stella.Compiler.Elaborate.Driver.Loop (AttempterM, RunReport, Submission, runAttemptingM, submitAttemptingM)
import Stella.Compiler.Elaborate.Driver.Synthesis (submitSynthesisM)
import Stella.Compiler.Elaborate.Kernel.Elab (SessionEnv, SolverState)
import Stella.Compiler.Elaborate.Mechanism.Pending (Job(..), Site, SynthRef, goalOf)
import Stella.Compiler.Elaborate.Mechanism.Scheduler (lookupPending)
import Stella.Compiler.Elaborate.Protocol.Guest.Shape (Descriptor)
import Stella.Compiler.Elaborate.Vocabulary.Diagnostic (Defect(..))
import Stella.Compiler.TypedCore (Ident(..), ModuleName(..), Qualified(..))
import Type.Row (type (+))

-- | What runs the synthesis jobs of one compilation on one session: the session and
-- | `Stella.Elab`'s descriptor, the compiler's session environment, the budget of
-- | every invocation, the compilation's cancellation, the last attempt number drawn,
-- | and whether the session is still to be used.
type Guests =
  { session :: Session
  , descriptor :: Descriptor
  , env :: SessionEnv
  , budget :: Int
  , cancellation :: Cancellation
  , attempts :: Ref Int
  , health :: Ref SessionHealth
  }

-- | The largest attempt number a session admits.
lastAttempt :: Int
lastAttempt = 2147483647

-- | The driver stopped without an attempt: the compilation was called off, with
-- | the state it was left in and whether the session is still to be used.
data Interrupted = CalledOff SolverState SessionHealth

type GuestRun r = ExceptT Interrupted (Run (AFF + EFFECT + r))

-- | Attempt the job named on the session, or by the host where it is not a
-- | synthesis job.
guestAttempter :: forall r. Guests -> AttempterM (GuestRun r)
guestAttempter guests id s = case lookupPending s.tentative.scheduler id of
  Just { job: JobSynthesis record } -> synthesizing (goalOf record).synthesizer
  _ -> do
    stopped <- lift (liftEffect (cancelRequested guests.cancellation))
    if stopped then do
      health <- lift (liftEffect (Ref.read guests.health))
      throwError (CalledOff s health)
    else pure (attemptPending guests.env id s)
  where
  synthesizing :: SynthRef -> GuestRun r (Tuple Attempt SolverState)
  synthesizing (Qualified (ModuleName m) (Ident name)) = do
    drawn <- lift (liftEffect draw)
    case drawn of
      Nothing -> do
        lift (liftEffect (Ref.write Replace guests.health))
        pure case openConversation guests.env id s of
          OpenStopped attempt s' -> Tuple attempt s'
          Opened c -> abandoned c GuestAttemptsExhausted
      Just attempt -> do
        brokered <- lift
          (runGuest guests.session guests.descriptor { global: { module: m, name }, attempt, budget: guests.budget } guests.cancellation guests.env id s)
        case settle { budget: guests.budget } brokered of
          Settled ended s' health -> do
            lift (liftEffect (recorded health))
            pure (Tuple ended s')
          Cancelled s' health -> do
            lift (liftEffect (recorded health))
            throwError (CalledOff s' health)

  -- the next attempt number, where one is left
  draw = do
    last <- Ref.read guests.attempts
    if last >= lastAttempt then pure Nothing
    else Ref.write (last + 1) guests.attempts $> Just (last + 1)

  recorded = case _ of
    Replace -> Ref.write Replace guests.health
    Reusable -> pure unit

-- | Retry the jobs on the ready queue, each attempted on the session or by the host.
runGuests :: forall r. Guests -> SolverState -> Run (AFF + EFFECT + r) (Either Interrupted (Tuple RunReport SolverState))
runGuests guests s = runExceptT (runAttemptingM (guestAttempter guests) s)

-- | Create a job and attempt it at once, on the session or by the host.
submitGuest :: forall r. Guests -> Site -> Job -> SolverState -> Run (AFF + EFFECT + r) (Either Interrupted (Tuple Submission SolverState))
submitGuest guests site job s = runExceptT (submitAttemptingM (guestAttempter guests) site job s)

-- | `⟨ τ by f ⟩` at a site and in a region of cells, its goal attempted at once on
-- | the session.
submitGuestSynthesis
  :: forall r
   . Guests
  -> Site
  -> XType
  -> SynthRef
  -> Maybe Region
  -> SolverState
  -> Run (AFF + EFFECT + r) (Either Interrupted (Tuple { target :: TermMetaVar, submission :: Submission } SolverState))
submitGuestSynthesis guests site expectedType synthesizer region s =
  runExceptT (submitSynthesisM (guestAttempter guests) site expectedType synthesizer region s)
