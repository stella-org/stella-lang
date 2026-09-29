-- | The `session` command: a long-lived process a compiler talks to.
-- |
-- | The session's messages travel on the channel this process was started with,
-- | reached through the `TRANSPORT` effect; on Node that is descriptor 3, and
-- | standard output and standard error stay for logs and for what host modules
-- | print. A session opens with a handshake that fixes its profile, answers
-- | requests until it is asked to close, and answers a message it cannot take with a
-- | protocol error rather than ending.
-- |
-- | How it ended is what `serve` answers with: normally after `close`, and
-- | otherwise as an `ErrorType` the command reports and exits by. Every final
-- | response is written out and the channel released before `serve` returns.
module Steam.CLI.Session (serve) where

import Prelude

import Data.Array (elem)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Aff (Aff, makeAff, nonCanceler)
import Effect.Class (liftEffect)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Foreign.Object as Object
import Run (AFF, EFFECT, Run, liftAff)
import Run.Except (EXCEPT)
import Run.Except as Except
import Steam.CLI.Error (ErrorType(..))
import Stella.CLI.Effect.Transport (Channel, TRANSPORT, ownChannel)
import Stella.CLI.Session.Peer (Answer, Incoming, Peer, SessionFailure, answer)
import Stella.CLI.Session.Peer as Peer
import Stella.CLI.Session.Protocol (Refusal, capabilityFor, closeKind, closedKind, decodeHello, emptyPayload, encodeReady, encodeRefusal, helloKind, negotiate, pingKind, pongKind, readyKind, refusedKind)
import Stella.CLI.Session.ProtocolError (ProtocolError(..), encodeProtocolError, protocolErrorKind)
import Type.Row (type (+))

-- | Where the session stands. An open session holds the capabilities its handshake
-- | put in force, which decide the requests beyond the lifecycle it answers.
data Stage = AwaitingHello | Open (Array String) | Ending

-- | How a session ended.
data Ending
  = Closed
  | Refused Refusal
  | Lost SessionFailure

-- | Serve a session on this process's channel until it ends.
serve :: forall r. Run (TRANSPORT + EXCEPT ErrorType + AFF + EFFECT + r) Unit
serve = ownChannel >>= case _ of
  Left reason -> Except.throw (SessionChannelMissing reason)
  Right channel -> liftAff (serveOn channel) >>= case _ of
    Closed -> pure unit
    Refused refusal -> Except.throw (SessionRefused refusal)
    Lost failure -> Except.throw (SessionFailed failure)

serveOn :: Channel -> Aff Ending
serveOn channel = makeAff \done -> do
  let end = done <<< Right
  stage <- Ref.new AwaitingHello
  self <- Ref.new Nothing
  peer <- Peer.start channel
    { request: \incoming -> liftEffect do
        peer <- Ref.read self
        respond stage peer end incoming
    , notification: \incoming -> Ref.read self >>= notified incoming
    , failed: end <<< Lost
    }
  Ref.write (Just peer) self
  pure nonCanceler

respond :: Ref Stage -> Maybe Peer -> (Ending -> Effect Unit) -> Incoming -> Effect Answer
respond stage self end incoming = Ref.read stage >>= case _, incoming.kind of
  AwaitingHello, kind | kind == helloKind -> case decodeHello incoming.payload of
    Nothing -> problem (PayloadInvalid kind)
    Just hello -> case negotiate hello of
      Right ready -> do
        Ref.write (Open ready.capabilities) stage
        pure (answer { kind: readyKind, payload: encodeReady ready })
      Left refusal -> do
        Ref.write Ending stage
        pure
          { kind: refusedKind
          , payload: encodeRefusal refusal
          , afterwards: endWith (Refused refusal)
          }
  Open capabilities, kind
    | kind == pingKind -> lifecycle kind pongKind (pure unit)
    | kind == closeKind -> lifecycle kind closedKind (endWith Closed)
    | Just capability <- capabilityFor kind
    , not (capability `elem` capabilities) -> problem (CapabilityNotInForce kind)
  _, kind
    | kind `elem` lifecycleKinds -> problem (KindUnexpected kind)
    | otherwise -> problem (KindUnknown kind)
  where
  -- a lifecycle request carries an empty payload
  lifecycle kind reply afterwards
    | Object.isEmpty incoming.payload = do
        when (reply == closedKind) (Ref.write Ending stage)
        pure { kind: reply, payload: emptyPayload, afterwards }
    | otherwise = problem (PayloadInvalid kind)

  problem error = pure (answer { kind: protocolErrorKind, payload: encodeProtocolError error })

  -- the last response is written out and the channel released before the session
  -- is over
  endWith ending = case self of
    Nothing -> end ending
    Just peer -> Peer.shutdown peer (end ending)

lifecycleKinds :: Array String
lifecycleKinds = [ helloKind, pingKind, closeKind ]

notified :: Incoming -> Maybe Peer -> Effect Unit
notified incoming = case _ of
  Nothing -> pure unit
  Just peer
    -- a protocol error is not answered, or two sides could answer each other forever
    | incoming.kind == protocolErrorKind -> pure unit
    | incoming.kind `elem` lifecycleKinds ->
        Peer.notify peer protocolErrorKind
          (encodeProtocolError (KindUnexpected incoming.kind))
    | otherwise -> Peer.notify peer protocolErrorKind
        (encodeProtocolError (KindUnknown incoming.kind))
