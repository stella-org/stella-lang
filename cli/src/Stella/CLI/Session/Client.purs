-- | The client side of a session: starting `steam session`, the handshake, and
-- | telling how the session ended.
-- |
-- | **Starting the process is an effect** ([Process](../Effect/Process.purs)), so
-- | none of this names the host it runs on.
-- |
-- | **How a session ended is read off two things together**, what arrived on the
-- | channel and how the process exited:
-- |
-- | | Seen | Judged |
-- | | --- | --- |
-- | | `closed`, then exit 0 | closed normally |
-- | | `refused`, then exit | not opened, for the reason given; the exit does not override it |
-- | | an exit without `closed`, exit 0 included, or the channel ending | the session failed |
-- | | a `protocolError` answering a request | that request failed; the session goes on |
module Stella.CLI.Session.Client
  ( Launch
  , Session
  , OpenFailure(..)
  , ClientFailure(..)
  , RequestFailure(..)
  , open
  , ready
  , request
  , ping
  , load
  , invoke
  , Answering
  , invokeAnswering
  , cancel
  , close
  , abandon
  , kill
  ) where

import Prelude

import Data.Argonaut.Core (Json)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..))
import Data.Show.Generic (genericShow)
import Effect (Effect)
import Control.Alt ((<|>))
import Control.Parallel (parallel, sequential)
import Effect.Aff (Aff, bracket)
import Effect.Class as Effect
import Effect.Aff.AVar (AVar)
import Effect.Aff.AVar as AVar
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Foreign.Object (Object)
import Foreign.Object as Object
import Run (AFF, EFFECT, Run, liftAff, liftEffect, runBaseAff')
import Stella.CLI.Effect.Process (Child, Exit, Output, PROCESS, spawnSession)
import Stella.CLI.Session.Guest (InvocationFailure, InvokeRequest, LoadFailure, Token, cancelKind, cancelledKind, encodeCancel, decodeInvocationFailed, decodeLoadFailed, decodeLoaded, decodeReturned, encodeInvoke, encodeLoad, invocationFailedKind, invokeKind, loadFailedKind, loadKind, loadedKind, returnedKind)
import Stella.CLI.Session.Kernel (KernelCall, decodeKernel, kernelKind)
import Stella.CLI.Session.Peer (Peer, Reply, SessionFailure)
import Stella.CLI.Session.Peer as Peer
import Stella.CLI.Session.Protocol (Hello, Ready, Refusal, closeKind, closedKind, decodeReady, decodeRefusal, emptyPayload, encodeHello, helloKind, kernelCapability, pingKind, pongKind, readyKind, refusedKind)
import Stella.CLI.Session.ProtocolError (decodeProtocolError, protocolErrorKind)
import Stella.CLI.Session.ProtocolError as ProtocolError
import Type.Row (type (+))

-- | What starts a session: the command and its arguments, where its output goes,
-- | and what the handshake asks for.
type Launch =
  { command :: String
  , args :: Array String
  , output :: Output
  , hello :: Hello
  }

newtype Session = Session
  { peer :: Peer
  , child :: Child
  , ready :: Ready
  -- | The invocation whose `kernel` requests are answered, and how: there is at
  -- | most one, for the length of its `invoke`.
  , guest :: Ref (Maybe { attempt :: Int, answering :: Answering })
  -- | Held for the length of an invocation answering its `kernel` requests, so
  -- | that two are never in flight at once.
  , serial :: AVar Unit
  }

-- | How the `kernel` requests of an invocation are answered.
type Answering = KernelCall -> Aff Peer.Answer

-- | Why a session did not open.
data OpenFailure
  -- | The session refused the handshake, as it said why.
  = Refused Refusal
  -- | The session answered the handshake with a protocol error, as its code and
  -- | detail.
  | HandshakeRejected { code :: String, detail :: String }
  -- | The session failed before it opened.
  | OpenFailed ClientFailure

derive instance Eq OpenFailure
derive instance Generic OpenFailure _
instance Show OpenFailure where
  show = genericShow

-- | How a session failed, as the client sees it.
data ClientFailure
  -- | The process never started, as what the host said.
  = NotStarted String
  -- | The channel failed, and then the process ended as given.
  | ChannelLost SessionFailure Exit
  -- | The process ended without saying `closed`, whatever its status.
  | ExitedUnannounced Exit
  -- | The process said `closed` and then ended other than with status 0.
  | ExitedAfterClosed Exit
  -- | A response whose kind is not one the request is answered with, as the kind.
  | AnswerUnexpected String
  -- | A response of a kind the request is answered with, whose payload is not of
  -- | that kind's shape, as the kind.
  | AnswerMalformed String
  -- | A `ready` that does not settle what the handshake asked for, as what it
  -- | said and why it is refused.
  | ReadyUnacceptable Ready String

derive instance Eq ClientFailure
derive instance Generic ClientFailure _
instance Show ClientFailure where
  show = genericShow

-- | Why one request failed.
data RequestFailure
  -- | The session refused the request and goes on, as the code and detail.
  = RequestRefused { code :: String, detail :: String }
  -- | The session failed.
  | SessionLost ClientFailure

derive instance Eq RequestFailure
derive instance Generic RequestFailure _
instance Show RequestFailure where
  show = genericShow

-- | Start the process and shake hands.
open :: forall r. Launch -> Run (PROCESS + AFF + EFFECT + r) (Either OpenFailure Session)
open launch = do
  child <- spawnSession { command: launch.command, args: launch.args, output: launch.output }
  case child.channel of
    Nothing -> do
      exit <- liftAff child.exit
      pure (Left (OpenFailed (NotStarted (describeExit exit))))
    Just channel -> do
      guest <- liftEffect (Ref.new Nothing)
      opened <- liftEffect (Ref.new Nothing)
      serial <- liftAff (AVar.new unit)
      peer <- liftEffect $ Peer.start channel
        { request: answeringIn opened guest
        , notification: \_ -> pure unit
        , failed: \_ -> pure unit
        }
      answer <- liftAff (Peer.request peer helloKind (encodeHello launch.hello))
      let
        -- a handshake answered outside the protocol leaves nothing to talk to
        stop :: forall a. OpenFailure -> Run (PROCESS + AFF + EFFECT + r) (Either OpenFailure a)
        stop failure = do
          liftEffect (Peer.shutdown peer (pure unit))
          liftEffect child.kill
          pure (Left failure)
      case answer of
        Left failure -> Left <<< OpenFailed <$> lostWith child failure
        Right reply
          | reply.kind == readyKind -> case decodeReady reply.payload of
              Nothing -> stop (OpenFailed (AnswerMalformed reply.kind))
              Just r -> case unacceptable launch.hello r of
                Just why -> stop (OpenFailed (ReadyUnacceptable r why))
                Nothing -> do
                  liftEffect (Ref.write (Just r) opened)
                  pure (Right (Session { peer, child, ready: r, guest, serial }))
          | reply.kind == refusedKind -> case decodeRefusal reply.payload of
              Nothing -> stop (OpenFailed (AnswerMalformed reply.kind))
              Just refusal -> do
                _ <- liftAff child.exit
                pure (Left (Refused refusal))
          | reply.kind == protocolErrorKind -> case decodeProtocolError reply.payload of
              Nothing -> stop (OpenFailed (AnswerMalformed reply.kind))
              Just e -> stop (HandshakeRejected e)
          | otherwise -> stop (OpenFailed (AnswerUnexpected reply.kind))
  where
  -- a request of the session is judged as the session judges one: the stage `ready`
  -- has settled, then the kind, then the capability, and only then the payload.
  -- A `kernel` request is answered by the invocation it names, where that one is
  -- running and answering; nothing else the session asks is the client's
  answeringIn opened guest incoming = Effect.liftEffect (Ref.read opened) >>= case _ of
    Nothing -> pure (refusing (ProtocolError.KindUnexpected incoming.kind))
    Just r
      | incoming.kind /= kernelKind -> pure (refusing (ProtocolError.KindUnknown incoming.kind))
      | not (kernelCapability `Array.elem` r.capabilities) ->
          pure (refusing (ProtocolError.CapabilityNotInForce incoming.kind))
      | otherwise -> case decodeKernel incoming.payload of
          Nothing -> pure (refusing (ProtocolError.PayloadInvalid incoming.kind))
          Just call -> Effect.liftEffect (Ref.read guest) >>= case _ of
            Just running | running.attempt == call.attempt -> running.answering call
            _ -> pure (refusing (ProtocolError.KindUnexpected incoming.kind))

  refusing error = Peer.answer
    { kind: protocolErrorKind, payload: ProtocolError.encodeProtocolError error }

-- | Why a `ready` does not answer a `hello`, where it does not: it names another
-- | protocol or profile, leaves a required capability out, or puts in force one
-- | nobody asked for.
unacceptable :: Hello -> Ready -> Maybe String
unacceptable hello r
  | r.protocol /= hello.protocol = Just "it names another protocol"
  | r.profile /= hello.profile = Just "it names another profile"
  | not (Array.all (_ `Array.elem` r.capabilities) hello.requires) =
      Just "it leaves out a capability the client requires"
  | not (Array.all (\c -> Array.elem c hello.offers || Array.elem c hello.requires) r.capabilities) =
      Just "it puts in force a capability the client did not ask for"
  | otherwise = Nothing

-- | What the handshake settled.
ready :: Session -> Ready
ready (Session s) = s.ready

-- | Ask the session, and have its response. A protocol error is the request
-- | failing, and the session goes on. **A protocol error that does not read as
-- | one is the session misbehaving**, not a request refused: the session is ended
-- | and the request fails with it.
request
  :: forall r
   . Session
  -> String
  -> Object Json
  -> Run (AFF + EFFECT + r) (Either RequestFailure Reply)
request (Session s) kind payload = liftAff (Peer.request s.peer kind payload) >>= case _ of
  Left failure -> Left <<< SessionLost <$> lostWith s.child failure
  Right reply
    | reply.kind == protocolErrorKind -> case decodeProtocolError reply.payload of
        Just e -> pure (Left (RequestRefused e))
        Nothing -> Left <<< SessionLost <$> misbehaved (Session s) (AnswerMalformed reply.kind)
    | otherwise -> pure (Right reply)

ping :: forall r. Session -> Run (AFF + EFFECT + r) (Either RequestFailure Unit)
ping session = request session pingKind emptyPayload >>= case _ of
  Left failure -> pure (Left failure)
  Right reply
    | reply.kind == pongKind -> pure (Right unit)
    | otherwise -> Left <<< SessionLost <$> misbehaved session (AnswerUnexpected reply.kind)

-- | Load the module at that path into the session: its name, or why the session
-- | did not load it. A path is resolved against the session's working directory.
load
  :: forall r
   . Session
  -> String
  -> Run (AFF + EFFECT + r) (Either RequestFailure (Either LoadFailure String))
load session path = request session loadKind (encodeLoad path) >>= case _ of
  Left failure -> pure (Left failure)
  Right reply
    | reply.kind == loadedKind -> answered (Right <$> decodeLoaded reply.payload) reply.kind
    | reply.kind == loadFailedKind -> answered (Left <$> decodeLoadFailed reply.payload) reply.kind
    | otherwise -> Left <<< SessionLost <$> misbehaved session (AnswerUnexpected reply.kind)
  where
  answered decoded kind = case decoded of
    Just outcome -> pure (Right outcome)
    Nothing -> Left <<< SessionLost <$> misbehaved session (AnswerMalformed kind)

-- | Apply a guest function to tokens, as an attempt: the token it returned, or why
-- | it did not return one.
invoke
  :: forall r
   . Session
  -> InvokeRequest
  -> Run (AFF + EFFECT + r) (Either RequestFailure (Either InvocationFailure Token))
invoke session invocation = request session invokeKind (encodeInvoke invocation) >>= case _ of
  Left failure -> pure (Left failure)
  Right reply
    | reply.kind == returnedKind -> answered (Right <$> decodeReturned reply.payload) reply.kind
    | reply.kind == invocationFailedKind -> answered (Left <$> decodeInvocationFailed reply.payload) reply.kind
    | otherwise -> Left <<< SessionLost <$> misbehaved session (AnswerUnexpected reply.kind)
  where
  answered decoded kind = case decoded of
    Just outcome -> pure (Right outcome)
    Nothing -> Left <<< SessionLost <$> misbehaved session (AnswerMalformed kind)

-- | `invoke`, answering the `kernel` requests the invocation makes with the
-- | function given.
-- |
-- | **Answering is set up before the `invoke` goes out and taken down however it
-- | ends** — answered, refused, the session lost, or the caller cancelled — so a
-- | `kernel` request arriving at once finds it, and one arriving late, or naming
-- | another attempt, is refused as unexpected. **One such invocation runs at a
-- | time in a session**: a second waits for the first, the session running
-- | invocations one after another in any case, so neither answers the other's
-- | requests.
-- |
-- | **A caller may withdraw until the invocation is sent**, and nothing reaches the
-- | session of one withdrawn. Waiting for the session is raced against
-- | `withdrawn`: where it settles first, the wait is given up. Once the session is
-- | held, `sending` is asked at that moment, before anything is sent, and where it
-- | says not to, nothing is. Either way the answer is `Nothing`.
invokeAnswering
  :: forall r
   . Session
  -> InvokeRequest
  -> Answering
  -> { withdrawn :: Aff Unit, sending :: Effect Boolean }
  -> Run (AFF + EFFECT + r) (Maybe (Either RequestFailure (Either InvocationFailure Token)))
invokeAnswering session@(Session s) invocation answering caller = liftAff do
  held <- sequential (parallel (caller.withdrawn $> false) <|> parallel (AVar.take s.serial $> true))
  if not held then pure Nothing
  else bracket
    (Effect.liftEffect (Ref.write (Just { attempt: invocation.attempt, answering }) s.guest))
    ( \_ -> do
        Effect.liftEffect (Ref.write Nothing s.guest)
        AVar.put unit s.serial
    )
    ( \_ -> Effect.liftEffect caller.sending >>= if _ then Just <$> runBaseAff' (invoke session invocation) else pure Nothing
    )

-- | Ask the session to stop a queued or running invocation. **That the request was
-- | taken is all its answer says**: whether the invocation stopped is what that
-- | invocation's own answer says.
cancel :: forall r. Session -> Int -> Run (AFF + EFFECT + r) (Either RequestFailure Unit)
cancel session attempt = request session cancelKind (encodeCancel attempt) >>= case _ of
  Left failure -> pure (Left failure)
  Right reply
    | reply.kind == cancelledKind ->
        if Object.isEmpty reply.payload then pure (Right unit)
        else Left <<< SessionLost <$> misbehaved session (AnswerMalformed reply.kind)
    | otherwise -> Left <<< SessionLost <$> misbehaved session (AnswerUnexpected reply.kind)

-- | Close the session: `close`, `closed`, and then the process ending with 0.
close :: forall r. Session -> Run (AFF + EFFECT + r) (Either ClientFailure Unit)
close session@(Session s) = request session closeKind emptyPayload >>= case _ of
  Left (SessionLost failure) -> pure (Left failure)
  Left (RequestRefused e) -> Left <$> misbehaved session (AnswerUnexpected e.code)
  Right reply
    | reply.kind == closedKind -> do
        liftEffect (Peer.shutdown s.peer (pure unit))
        exit <- liftAff s.child.exit
        pure case exit.code of
          Just 0 -> Right unit
          _ -> Left (ExitedAfterClosed exit)
    | otherwise -> Left <$> misbehaved session (AnswerUnexpected reply.kind)

-- | End a session that answered outside the protocol: nothing it says afterwards
-- | can be trusted, so the channel is released and the process ended.
misbehaved :: forall r. Session -> ClientFailure -> Run (AFF + EFFECT + r) ClientFailure
misbehaved (Session s) failure = do
  liftEffect (Peer.shutdown s.peer (pure unit))
  liftEffect s.child.kill
  _ <- liftAff s.child.exit
  pure failure

-- | End the channel without `close`, and learn how the process took it.
abandon :: forall r. Session -> Run (AFF + EFFECT + r) Exit
abandon (Session s) = do
  liftEffect (Peer.shutdown s.peer (pure unit))
  liftAff s.child.exit

-- | End the process at once, as a client being interrupted does.
kill :: forall r. Session -> Run (AFF + EFFECT + r) Exit
kill (Session s) = do
  liftEffect s.child.kill
  liftAff s.child.exit

-- | A channel failure, judged once the process has ended: a process that ended
-- | without saying `closed` is that, whatever the channel reported first.
lostWith :: forall r. Child -> SessionFailure -> Run (AFF + r) ClientFailure
lostWith child failure = do
  exit <- liftAff child.exit
  pure case exit.error of
    Just reason -> NotStarted reason
    Nothing -> case failure of
      Peer.ChannelEnded -> ExitedUnannounced exit
      _ -> ChannelLost failure exit

describeExit :: Exit -> String
describeExit exit = case exit.error of
  Just reason -> reason
  Nothing -> "the process ended before its channel opened"
