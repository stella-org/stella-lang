-- | One side of a session: the resident receiver, the table of requests awaiting a
-- | response, and the writer.
-- |
-- | **Every side receives in one place and nowhere else.** One fiber reads the
-- | channel, the chunks are cut into frames, and each message is dispatched: a response to
-- | the request it answers, a request to the handler, a notification to its own
-- | handler. A request never reads the channel itself, so while one waits for its
-- | response the side still answers a request the other side makes in the meantime
-- | — the nesting a callback from inside a request needs. Every message leaves
-- | through `send`, one frame at a time, so frames never interleave.
-- |
-- | A message that cannot be taken is answered with a protocol error and the
-- | session goes on. What leaves no frame boundary to trust, the channel ending or
-- | failing, and a side running out of request numbers end the session, and every
-- | request still awaiting a response fails with the same reason.
module Stella.CLI.Session.Peer
  ( Peer
  , Reply
  , Answer
  , answer
  , Incoming
  , Handlers
  , SessionFailure(..)
  , start
  , request
  , notify
  , shutdown
  ) where

import Prelude

import Data.Argonaut.Core (Json)
import Data.Either (Either(..), either)
import Data.Foldable (for_)
import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Show.Generic (genericShow)
import Effect (Effect)
import Effect.Aff (Aff, Canceler(..), Error, makeAff, nonCanceler, runAff_)
import Effect.Class (liftEffect)
import Effect.Exception (message)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Foreign.Object (Object)
import Stella.CLI.Session.Envelope (Message(..), MessageId, decodeMessage, encodeMessage, firstMessageId, nextMessageId)
import Stella.CLI.Session.Frame (FrameFailure, Reader, emptyReader, feed, finish, frame, parsePayload, renderPayload)
import Stella.CLI.Session.ProtocolError (ProtocolError(..), encodeProtocolError, protocolErrorKind)
import Stella.CLI.Effect.Transport (Channel, ChannelEvent(..))
import Stella.Compiler.Bytecode.Bytes (Bytes)

-- | What a response carries.
type Reply = { kind :: String, payload :: Object Json }

-- | What a handler answers a request with, and what to do once the response has
-- | been written: a side ending the session after its last response ends it there,
-- | so the response is not lost.
type Answer = { kind :: String, payload :: Object Json, afterwards :: Effect Unit }

-- | A response with nothing to do after it.
answer :: Reply -> Answer
answer reply = { kind: reply.kind, payload: reply.payload, afterwards: pure unit }

-- | A request or a notification as a handler receives it.
type Incoming = { kind :: String, payload :: Object Json }

-- | What a side does with what the other side sends.
-- |
-- | `request` answers a request, and may itself make requests while it does.
-- | `failed` is told once, when the session ends without this side having shut it
-- | down.
type Handlers =
  { request :: Incoming -> Aff Answer
  , notification :: Incoming -> Effect Unit
  , failed :: SessionFailure -> Effect Unit
  }

-- | Why a session cannot go on.
data SessionFailure
  -- | Bytes with no frame boundary left to trust.
  = FrameUnreadable FrameFailure
  -- | The channel ended.
  | ChannelEnded
  -- | The channel failed, as what the host said.
  | ChannelFailed String
  -- | This side has used every request number.
  | IdsExhausted
  -- | This side built a message above the size a frame carries, as its kind.
  | OutgoingTooLarge String
  -- | This side built a message its serializer did not write as UTF-8, as its kind.
  | OutgoingUnencodable String
  -- | A handler of this side failed rather than answering, as what it raised.
  | HandlerFailed String
  -- | This side shut the session down, and something was still asked of it.
  | ShutDown

derive instance Eq SessionFailure
derive instance Generic SessionFailure _
instance Show SessionFailure where
  show = genericShow

-- | An outstanding request: `Just` its continuation, or `Nothing` once the side
-- | that made it stopped waiting. A response to an abandoned request is dropped,
-- | the request having been this side's own.
type Awaiting = Map MessageId (Maybe (Either SessionFailure Reply -> Effect Unit))

data Life = Alive | Over SessionFailure

newtype Peer = Peer
  { channel :: Channel
  , handlers :: Handlers
  , reader :: Ref Reader
  , nextId :: Ref (Maybe MessageId)
  -- the highest request number received, which every later one must be above
  , lastReceived :: Ref (Maybe MessageId)
  , awaiting :: Ref Awaiting
  , life :: Ref Life
  }

-- | Start receiving on a channel.
start :: Channel -> Handlers -> Effect Peer
start channel handlers = do
  reader <- Ref.new emptyReader
  nextId <- Ref.new (Just firstMessageId)
  lastReceived <- Ref.new Nothing
  awaiting <- Ref.new Map.empty
  life <- Ref.new Alive
  let peer = Peer { channel, handlers, reader, nextId, lastReceived, awaiting, life }
  runAff_ (either (\err -> fail peer (HandlerFailed (message err))) pure) (receiving peer)
  pure peer

-- The one reader of the channel, for as long as the session lives.
receiving :: Peer -> Aff Unit
receiving peer@(Peer p) = do
  event <- p.channel.receive
  continue <- liftEffect case event of
    Received bytes -> received peer bytes *> alive
    Ended -> ended peer $> false
    Failed reason -> fail peer (ChannelFailed reason) $> false
  when continue (receiving peer)
  where
  alive = Ref.read p.life <#> case _ of
    Alive -> true
    Over _ -> false

-- | Ask the other side, and wait for its response. A response of the kind
-- | `protocolError` is a response like any other; what it means is the caller's.
request :: Peer -> String -> Object Json -> Aff (Either SessionFailure Reply)
request peer@(Peer p) kind payload = makeAff \done -> do
  let resolve = done <<< Right
  Ref.read p.life >>= case _ of
    Over failure -> do
      resolve (Left failure)
      pure nonCanceler
    Alive -> Ref.read p.nextId >>= case _ of
      Nothing -> do
        fail peer IdsExhausted
        resolve (Left IdsExhausted)
        pure nonCanceler
      Just id -> do
        Ref.write (nextMessageId id) p.nextId
        Ref.modify_ (Map.insert id (Just resolve)) p.awaiting
        send peer (Request { kind, id, payload })
        -- a caller that stops waiting leaves the number outstanding, so the
        -- response it still gets is dropped rather than refused
        pure $ Canceler \_ -> liftEffect $
          Ref.modify_ (Map.update (const (Just Nothing)) id) p.awaiting

-- | Tell the other side something that asks for no response.
notify :: Peer -> String -> Object Json -> Effect Unit
notify peer kind payload = send peer (Notification { kind, payload })

-- | Write nothing more, and run the callback once what was written has been
-- | handed on. The channel ending afterwards is not a failure, and a request
-- | still awaiting a response fails as `ShutDown`.
shutdown :: Peer -> Effect Unit -> Effect Unit
shutdown (Peer p) flushed = Ref.read p.life >>= case _ of
  Over _ -> flushed
  Alive -> do
    Ref.write (Over ShutDown) p.life
    failAwaiting p.awaiting ShutDown
    runAff_ (\_ -> p.channel.destroy *> flushed) p.channel.end

-- Writing ---------------------------------------------------------------------------

send :: Peer -> Message -> Effect Unit
send peer@(Peer p) message = Ref.read p.life >>= case _ of
  Over _ -> pure unit
  Alive -> case renderPayload (encodeMessage message) of
    Nothing -> fail peer (OutgoingUnencodable (kindOfMessage message))
    Just payload -> case frame payload of
      Left _ -> fail peer (OutgoingTooLarge (kindOfMessage message))
      Right bytes -> p.channel.send bytes

kindOfMessage :: Message -> String
kindOfMessage = case _ of
  Request r -> r.kind
  Response r -> r.kind
  Notification r -> r.kind

-- | Answer a message that cannot be taken: as a response where it is a request
-- | whose number can be claimed, and as a notification otherwise.
answerProblem :: Peer -> Maybe MessageId -> ProtocolError -> Effect Unit
answerProblem peer answerable problem = do
  fresh <- case answerable of
    Just id -> claim peer id
    Nothing -> pure false
  send peer case answerable of
    Just replyTo | fresh ->
      Response { kind: protocolErrorKind, replyTo, payload: encodeProtocolError problem }
    _ -> Notification { kind: protocolErrorKind, payload: encodeProtocolError problem }

-- | Record a request number received, where it is above every one received before.
-- | **Each request is answered once**: one whose number is not above them is a
-- | request sent again or out of order, and running it would act twice.
claim :: Peer -> MessageId -> Effect Boolean
claim (Peer p) id = Ref.read p.lastReceived >>= case _ of
  Just last | id <= last -> pure false
  _ -> Ref.write (Just id) p.lastReceived $> true

-- Receiving -------------------------------------------------------------------------

received :: Peer -> Bytes -> Effect Unit
received peer@(Peer p) chunk = Ref.read p.life >>= case _ of
  Over _ -> pure unit
  Alive -> do
    reader <- Ref.read p.reader
    case feed chunk reader of
      Left failure -> fail peer (FrameUnreadable failure)
      Right { payloads, reader: next } -> do
        Ref.write next p.reader
        for_ payloads (dispatchPayload peer)

dispatchPayload :: Peer -> Bytes -> Effect Unit
dispatchPayload peer@(Peer p) payload = Ref.read p.life >>= case _ of
  Over _ -> pure unit
  Alive -> case parsePayload payload of
    Left problem -> answerProblem peer Nothing (PayloadUnreadable problem)
    Right object -> case decodeMessage object of
      Left { reason, answerable } -> answerProblem peer answerable (EnvelopeInvalid reason)
      Right message -> dispatch peer message

dispatch :: Peer -> Message -> Effect Unit
dispatch peer@(Peer p) = case _ of
  Request { kind, id, payload } -> claim peer id >>=
    if _ then
      runAff_ (answered id) (p.handlers.request { kind, payload })
    else answerProblem peer Nothing IdReused
  Response { kind, replyTo, payload } -> do
    waiting <- Ref.read p.awaiting
    case Map.lookup replyTo waiting of
      Nothing -> answerProblem peer Nothing ReplyUnexpected
      Just continuation -> do
        Ref.modify_ (Map.delete replyTo) p.awaiting
        for_ continuation \k -> k (Right { kind, payload })
  Notification incoming -> p.handlers.notification incoming
  where
  answered :: MessageId -> Either Error Answer -> Effect Unit
  answered replyTo = case _ of
    Right reply -> do
      send peer (Response { kind: reply.kind, replyTo, payload: reply.payload })
      reply.afterwards
    Left err -> fail peer (HandlerFailed (message err))

ended :: Peer -> Effect Unit
ended peer@(Peer p) = do
  reader <- Ref.read p.reader
  fail peer case finish reader of
    Just failure -> FrameUnreadable failure
    Nothing -> ChannelEnded

-- | End the session, once: the handler is told, then every request still awaiting
-- | a response fails with the same reason.
fail :: Peer -> SessionFailure -> Effect Unit
fail (Peer p) failure = Ref.read p.life >>= case _ of
  Over _ -> pure unit
  Alive -> do
    Ref.write (Over failure) p.life
    p.handlers.failed failure
    failAwaiting p.awaiting failure
    p.channel.destroy

failAwaiting :: Ref Awaiting -> SessionFailure -> Effect Unit
failAwaiting awaiting failure = do
  waiting <- Ref.read awaiting
  Ref.write Map.empty awaiting
  for_ waiting \continuation -> for_ continuation \k -> k (Left failure)
