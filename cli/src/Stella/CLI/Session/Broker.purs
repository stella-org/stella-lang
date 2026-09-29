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
-- | **An attempt the host ended while the guest waited stays ended**: the guest is
-- | told it was abandoned, and whatever the invocation then answers, the ending
-- | kept is the host's.
module Stella.CLI.Session.Broker
  ( Brokered(..)
  , runGuest
  ) where

import Prelude

import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Effect.Class as Effect
import Effect.Ref as Ref
import Run (AFF, EFFECT, Run, liftEffect)
import Stella.CLI.Session.Broker.Codec (decodeCommand, encodeAnswer, handleOfToken, tokenOfHandle)
import Stella.CLI.Session.Client (ClientFailure, RequestFailure(RequestRefused), Session)
import Stella.CLI.Session.Client as Client
import Stella.CLI.Session.Guest (GlobalName, InvocationFailure)
import Stella.CLI.Session.Kernel (abandonedKind, answeredKind, encodeAbandoned, encodeAnswered)
import Stella.CLI.Session.Peer as Peer
import Stella.CLI.Session.ProtocolError (ProtocolError(..), encodeProtocolError, protocolErrorKind)
import Stella.CLI.Session.Value (decodeValue, encodeValue, renderPath)
import Stella.Compiler.Elaborate.Driver.Attempt (Attempt, Conversation, OpenResult(..), Response(..), Step(..), envelopeOf)
import Stella.Compiler.Elaborate.Driver.Conversation (abandoned, command, openConversation)
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

-- | Where the conversation stands while the guest runs.
data Progress
  = Talking Conversation
  | Over Attempt SolverState

-- | Run the guest function named, as the attempt given, on the synthesis job named.
-- | The descriptor is `Stella.Elab`'s, which the caller has from the compiler's
-- | bundle: a bundle that does not read is the toolchain's defect, settled before
-- | any guest runs.
runGuest
  :: forall r
   . Session
  -> Descriptor
  -> { global :: GlobalName, attempt :: Int }
  -> SessionEnv
  -> PendingId
  -> SolverState
  -> Run (AFF + EFFECT + r) Brokered
runGuest session descriptor guest env id s0 = case openConversation env id s0 of
  OpenStopped attempt s -> pure (Ended attempt s)
  Opened conversation -> case conversation.goal of
    Nothing -> pure (ended (abandoned conversation NoGoal))
    Just goal -> do
      progress <- liftEffect (Ref.new (Talking conversation))
      result <- Client.invokeAnswering session
        { global: guest.global, arguments: [ tokenOfHandle goal ], attempt: guest.attempt }
        (answering descriptor progress)
      liftEffect (Ref.read progress) <#> case _, result of
        -- the host ended it while the guest waited, whatever the invocation says
        Over attempt s, _ -> Ended attempt s
        Talking c, Right (Right token) -> case handleOfToken token of
          Left why -> ended (abandoned c (GuestResultUnreadable why))
          Right result' -> case command (envelopeOf c) (Finish result') c of
            Finished attempt s -> Ended attempt s
            Answered (Returned answer) c' -> ended (abandoned c' (CommandAnswerMismatch (Finish result') answer))
            Answered (CandidateFailed token' _) c' -> ended (abandoned c' (UnmatchedCandidateFailure token'))
        Talking c, Right (Left failure) -> InvocationFailed failure c
        Talking c, Left (RequestRefused refusal) -> RequestRejected refusal c
        Talking c, Left (Client.SessionLost failure) -> SessionLost failure c
  where
  ended (Tuple attempt s) = Ended attempt s

-- | Answer one `kernel` request where the conversation stands.
answering :: Descriptor -> Ref.Ref Progress -> Client.Answering
answering descriptor progress call = Effect.liftEffect do
  Ref.read progress >>= case _ of
    -- nothing is asked of an attempt that has ended
    Over _ _ -> pure (refusing (KindUnexpected "kernel"))
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
    pure (Peer.answer { kind: abandonedKind, payload: encodeAbandoned })

  refusing error = Peer.answer { kind: protocolErrorKind, payload: encodeProtocolError error }

