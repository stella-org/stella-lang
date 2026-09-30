-- | Running a guest synthesizer on Steam as an attempt: the compiler's
-- | conversation answering each command the guest sends.
-- |
-- | **The conversation is the compiler's, and the broker only carries it.** The
-- | attempt is opened, the goal handed to the guest as a token, each `kernel`
-- | request read as a command and answered by `command` where the conversation
-- | stands, and the handle the guest returns sent to finish the attempt. The
-- | transaction a command stands in is always read off the conversation: a failed
-- | candidate closes the innermost there, and the guest, told only that the
-- | candidate failed, closes its own innermost with it.
-- |
-- | **Who is at fault decides what a thing that does not read ends.** A command
-- | that is no canonical value is Steam breaking the protocol, answered as such,
-- | which ends the session. A canonical value that is no `GuestCommand` ends the
-- | attempt as a defect and tells the guest it was abandoned. A result that is no
-- | handle ends the attempt too, with nothing left to tell. A handle of the right
-- | shape and the wrong session, class, or age is the compiler's to refuse, where
-- | it finishes.
-- |
-- | **An attempt ended first stays ended**: one the host ended while the guest
-- | waited, and one finished with what the guest returned, are what they are
-- | whatever the invocation then answers or a cancellation then asks.
-- |
-- | **A run is cancelled by the caller asking, not by stopping the caller.** The
-- | cancellation asks the session to stop the invocation and answers any command
-- | still to come with `abandoned`, and the run waits for the invocation to settle,
-- | holding the session meanwhile, so the state it hands back is the attempt
-- | rolled back with nothing issued in it forgotten. An invocation that does not
-- | settle within the cancellation's grace, or a cancel the session does not take,
-- | ends the session: a guest that never returns to the loop between its steps
-- | cannot be stopped any other way. A run cancelled while it still waits for the session
-- | sends nothing at all: it is rolled back where it stands, and the session, busy
-- | with another run, hears nothing of it.
module Stella.CLI.Session.Broker
  ( Brokered(..)
  , SessionHealth(..)
  , Cancellation
  , newCancellation
  , cancel
  , runGuest
  ) where

import Prelude

import Control.Alt ((<|>))
import Control.Parallel (parallel, sequential)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.AVar (AVar)
import Effect.AVar as EffectAVar
import Effect.Aff (Milliseconds, delay, error, forkAff, joinFiber, killFiber)
import Effect.Aff.AVar as AVar
import Effect.Class as Effect
import Effect.Ref as Ref
import Run (AFF, EFFECT, Run, liftAff, liftEffect, runBaseAff')
import Stella.CLI.Session.Broker.Codec (decodeCommand, encodeAnswer, handleOfToken, tokenOfHandle)
import Stella.CLI.Session.Client (ClientFailure, RequestFailure(RequestRefused), Session)
import Stella.CLI.Session.Client as Client
import Stella.CLI.Session.Guest (GlobalName, InvocationFailure, Token)
import Stella.CLI.Session.Kernel (abandonedKind, answeredKind, encodeAbandoned, encodeAnswered)
import Stella.CLI.Session.Peer as Peer
import Stella.CLI.Session.ProtocolError (ProtocolError(..), encodeProtocolError, protocolErrorKind)
import Stella.CLI.Session.Value (decodeValue, encodeValue, renderPath)
import Stella.Compiler.Elaborate.Driver.Attempt (Attempt, Conversation, OpenResult(..), Response(..), Step(..), envelopeOf)
import Stella.Compiler.Elaborate.Driver.Conversation (abandoned, cancelled, command, openConversation)
import Stella.Compiler.Elaborate.Kernel.Elab (SessionEnv, SolverState)
import Stella.Compiler.Elaborate.Mechanism.Pending (PendingId)
import Stella.Compiler.Elaborate.Protocol.Guest.Shape (Descriptor)
import Stella.Compiler.Elaborate.Vocabulary.Diagnostic (Defect(..))
import Stella.Compiler.Elaborate.Vocabulary.Request (Command(..))
import Type.Row (type (+))

-- | How running a guest ended.
data Brokered
  -- | The attempt ended: finished with what the guest returned, or ended by the
  -- | host while the guest waited, or as a defect.
  = Ended Attempt SolverState
  -- | The invocation failed, as the session said why; the attempt is still open.
  | InvocationFailed InvocationFailure Conversation
  -- | The session refused the `invoke` and goes on; the attempt is still open.
  | RequestRejected { code :: String, detail :: String } Conversation
  -- | The session was lost; the attempt is still open.
  | SessionLost ClientFailure Conversation
  -- | The run was cancelled: the attempt rolled back, the state the last of a
  -- | compilation called off, and whether the session is still to be used.
  | Cancelled SolverState SessionHealth

-- | Whether a session goes on being used. This is about the process, and not
-- | about any compiler state a run handed back.
data SessionHealth
  = Reusable
  | Replace

derive instance Eq SessionHealth

instance Show SessionHealth where
  show = case _ of
    Reusable -> "Reusable"
    Replace -> "Replace"

-- | A caller's request that a run stop, and how long a stop asked for may take
-- | before the session is ended instead. The clock is the caller's: a deadline
-- | is a timer that cancels.
newtype Cancellation = Cancellation
  { requested :: AVar Unit
  , grace :: Milliseconds
  }

newCancellation :: Milliseconds -> Effect Cancellation
newCancellation grace = (\requested -> Cancellation { requested, grace }) <$> EffectAVar.empty

-- | Ask for the run to stop. Asking again asks nothing more.
cancel :: Cancellation -> Effect Unit
cancel (Cancellation c) = void (EffectAVar.tryPut unit c.requested)

-- | Where the conversation stands while the guest runs.
data Progress
  = Talking Conversation
  | Over Attempt SolverState

-- | Run the guest function named, as the attempt given with the budget given, on
-- | the synthesis job named. The descriptor is `Stella.Elab`'s, which the caller
-- | has from the compiler's bundle: a bundle that does not read is the
-- | toolchain's defect, settled before any guest runs.
runGuest
  :: forall r
   . Session
  -> Descriptor
  -> { global :: GlobalName, attempt :: Int, budget :: Int }
  -> Cancellation
  -> SessionEnv
  -> PendingId
  -> SolverState
  -> Run (AFF + EFFECT + r) Brokered
runGuest session descriptor guest (Cancellation cancellation) env id s0 = case openConversation env id s0 of
  OpenStopped attempt s -> pure (Ended attempt s)
  Opened conversation -> case conversation.goal of
    Nothing -> pure (ended (abandoned conversation NoGoal))
    Just goal -> do
      progress <- liftEffect (Ref.new (Talking conversation))
      cancelling <- liftEffect (Ref.new false)
      sent <- liftEffect (Ref.new false)
      forced <- liftEffect (Ref.new false)
      let
        -- asked once the session is held: a run cancelled while it waited for the
        -- session sends nothing, and one not cancelled is sent from here on
        sending = Ref.read cancelling >>= if _ then pure false else Ref.write true sent $> true
      liftAff do
        invocation <- forkAff $ runBaseAff' $ Client.invokeAnswering session
          { global: guest.global, arguments: [ tokenOfHandle goal ], attempt: guest.attempt, budget: guest.budget }
          (answering descriptor progress cancelling)
          { withdrawn: AVar.read cancellation.requested, sending }
        watcher <- forkAff do
          AVar.read cancellation.requested
          Effect.liftEffect (Ref.write true cancelling)
          -- a run not yet sent withdraws where it would send, and the session
          -- hears nothing of it; the grace runs only for an invocation in flight
          inFlight <- Effect.liftEffect (Ref.read sent)
          when inFlight do
            taken <- runBaseAff' (Client.cancel session guest.attempt)
            settled <- case taken of
              Left _ -> pure false
              Right _ -> sequential
                (parallel (joinFiber invocation $> true) <|> parallel (delay cancellation.grace $> false))
            unless settled do
              Effect.liftEffect (Ref.write true forced)
              void (runBaseAff' (Client.kill session))
        outcome <- joinFiber invocation
        killFiber (error "the invocation settled") watcher
        killed <- Effect.liftEffect (Ref.read forced)
        at <- Effect.liftEffect (Ref.read progress)
        case outcome of
          -- withdrawn before it was sent: nothing ran, and the session was not touched
          Nothing -> pure case at of
            Over attempt s -> Ended attempt s
            Talking c -> Cancelled (cancelled c) Reusable
          Just result -> do
            stopped <- Effect.liftEffect (Ref.read cancelling)
            pure (settledAs at stopped killed result)
  where
  ended (Tuple attempt s) = Ended attempt s

  settledAs at stopped killed result = case at, result of
    -- the host ended it while the guest waited, whatever came after
    Over attempt s, _ -> Ended attempt s
    -- the guest finished before a cancellation took hold
    Talking c, Right (Right token) -> finished c token
    Talking c, _
      | stopped -> Cancelled (cancelled c) (if killed || lost result then Replace else Reusable)
    Talking c, Right (Left failure) -> InvocationFailed failure c
    Talking c, Left (RequestRefused refusal) -> RequestRejected refusal c
    Talking c, Left (Client.SessionLost failure) -> SessionLost failure c

  lost = case _ of
    Left (Client.SessionLost _) -> true
    _ -> false

  finished :: Conversation -> Token -> Brokered
  finished c token = case handleOfToken token of
    Left why -> ended (abandoned c (GuestResultUnreadable why))
    Right result -> case command (envelopeOf c) (Finish result) c of
      Finished attempt s -> Ended attempt s
      Answered (Returned answer) c' -> ended (abandoned c' (CommandAnswerMismatch (Finish result) answer))
      Answered (CandidateFailed token' _) c' -> ended (abandoned c' (UnmatchedCandidateFailure token'))

-- | Answer one `kernel` request where the conversation stands. **Once the run is
-- | being cancelled, a command is answered `abandoned`** and not taken: the
-- | conversation stays where it was, to be rolled back as cancelled.
answering :: Descriptor -> Ref.Ref Progress -> Ref.Ref Boolean -> Client.Answering
answering descriptor progress cancelling call = Effect.liftEffect do
  stopping <- Ref.read cancelling
  Ref.read progress >>= case _ of
    -- nothing is asked of an attempt that has ended
    Over _ _ -> pure (refusing (KindUnexpected "kernel"))
    Talking _ | stopping -> pure abandonedAnswer
    Talking c -> case decodeValue call.command of
      Left _ -> pure (refusing (PayloadInvalid "kernel"))
      Right wire -> case decodeCommand descriptor wire of
        Left why -> end (abandoned c (GuestCommandUnreadable why))
        Right sent -> case command (envelopeOf c) sent c of
          Finished attempt s -> end (Tuple attempt s)
          Answered response c' -> case encodeAnswer response of
            Left why -> end (abandoned c' (GuestAnswerUnwritable why))
            Right answer -> case encodeValue answer of
              Left problem ->
                end (abandoned c' (GuestAnswerUnwritable ("answer" <> renderPath problem.path <> ": " <> problem.problem)))
              Right json -> do
                Ref.write (Talking c') progress
                pure (Peer.answer { kind: answeredKind, payload: encodeAnswered json })
  where
  end (Tuple attempt s) = do
    Ref.write (Over attempt s) progress
    pure abandonedAnswer

  abandonedAnswer = Peer.answer { kind: abandonedKind, payload: encodeAbandoned }

  refusing error = Peer.answer { kind: protocolErrorKind, payload: encodeProtocolError error }
