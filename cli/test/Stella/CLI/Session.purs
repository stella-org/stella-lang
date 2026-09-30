module Test.Stella.CLI.Session (spec) where

import Prelude

import Data.Argonaut.Core (Json, fromArray, fromNumber, fromObject, fromString, jsonNull, stringify)
import Data.Array as Array
import Data.Either (Either(..), hush)
import Data.Foldable (for_)
import Data.Int (toNumber)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Aff (Aff, Milliseconds(..), delay, forkAff, joinFiber)
import Effect.Class (liftEffect)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Foreign.Object (Object)
import Foreign.Object as Object
import Stella.CLI.Session.Envelope (EnvelopeReason(..), Message(..), decodeMessage, encodeMessage, firstMessageId, messageId, nextMessageId)
import Stella.CLI.Session.Frame (FrameFailure(..), PayloadProblem(..), emptyReader, feed, finish, frame, maxPayload, parsePayload, renderPayload, u32BE)
import Stella.CLI.Session.Guest (InvocationReason(..), LoadStage(..), ValueClass(..), decodeCancel, encodeCancel, decodeInvocationFailed, decodeInvoke, decodeLoad, decodeLoadFailed, decodeLoaded, decodeReturned, encodeInvocationFailed, encodeInvoke, encodeLoad, encodeLoadFailed, encodeLoaded, encodeReturned)
import Stella.CLI.Session.Kernel (decodeAbandoned, decodeAnswered, decodeKernel, encodeAbandoned, encodeAnswered, encodeKernel)
import Stella.CLI.Session.Peer (Incoming, SessionFailure(..), answer)
import Stella.CLI.Session.Peer as Peer
import Stella.CLI.Session.Protocol (RefusalReason(..), decodeHello, decodeReady, decodeRefusal, elaborationProfile, encodeHello, encodeReady, encodeRefusal, negotiate, protocolVersion)
import Stella.CLI.Session.ProtocolError (decodeProtocolError, protocolErrorKind)
import Stella.CLI.Effect.Transport (Channel, ChannelEvent(..))
import Stella.Compiler.Bytecode.Bytes (Bytes, utf8)
import Test.Stella.CLI.Session.Memory (memoryPair)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

spec :: Spec Unit
spec = describe "Stella.CLI.Session" do
  frames
  envelopes
  handshakes
  guests
  peers

-- Frames -----------------------------------------------------------------------------

object :: Array (Tuple String Json) -> Object Json
object = Object.fromFoldable

payloadOf :: String -> Object Json
payloadOf s = object [ Tuple "text" (fromString s) ]

text :: Object Json -> String
text = stringify <<< fromObject

framed :: Object Json -> Bytes
framed o = fromMaybe [] (renderPayload o >>= (frame >>> hush))

encodeText :: String -> Bytes
encodeText s = fromMaybe [] (hush (utf8 s))

-- | Feed the chunks one after the other, collecting every payload.
feedAll :: Array Bytes -> Either FrameFailure (Array String)
feedAll chunks = go emptyReader [] chunks
  where
  go reader acc remaining = case Array.uncons remaining of
    Nothing -> Right acc
    Just { head, tail } -> case feed head reader of
      Left failure -> Left failure
      Right r -> go r.reader (acc <> Array.mapMaybe parsed r.payloads) tail
  parsed p = case parsePayload p of
    Right o -> Just (text o)
    Left _ -> Nothing

bytesOf :: Bytes -> Array Bytes
bytesOf c = map (\b -> [ b ]) c

frames :: Spec Unit
frames = describe "frames" do
  let
    one = payloadOf "one"
    two = payloadOf "星と「二」😀"

  it "reads a frame handed over one byte at a time" do
    feedAll (bytesOf (framed two)) `shouldEqual` Right [ text two ]

  it "reads several frames from one chunk" do
    feedAll [ append (framed one) (framed two) ] `shouldEqual` Right [ text one, text two ]

  it "reads a frame split inside its prefix and inside its payload" do
    let
      whole = append (framed one) (framed two)
      n = Array.length whole
      at i j = Array.slice i j whole
    feedAll [ at 0 2, at 2 7, at 7 (n - 3), at (n - 3) n ] `shouldEqual` Right [ text one, text two ]

  it "counts the length in UTF-8 bytes" do
    let rendered = fromMaybe [] (renderPayload two)
    (Array.slice 0 4 (framed two))
      `shouldEqual` (u32BE (Array.length rendered))

  it "fails on a length above the limit, before the payload arrives" do
    feedAll [ u32BE (maxPayload + 1) ]
      `shouldEqual` Left (Oversized (toNumber (maxPayload + 1)))

  it "refuses to frame a payload above the limit" do
    case frame ((Array.replicate (maxPayload + 1) 32)) of
      Left (Oversized _) -> pure unit
      _ -> fail "an oversized payload was framed"

  it "tells an end between frames from an end inside one" do
    let
      whole = framed one
      at i = case feed (Array.slice 0 i whole) emptyReader of
        Right r -> finish r.reader
        Left _ -> Nothing
    at 0 `shouldEqual` Nothing
    at 3 `shouldEqual` Just (TruncatedPrefix 3)
    at 6 `shouldEqual` Just (TruncatedPayload { expected: Array.length whole - 4, received: 2 })
    at (Array.length whole) `shouldEqual` Nothing

  it "keeps the boundary around a payload that is not an object" do
    let
      raw bytes = append (u32BE (Array.length bytes)) bytes
      problems =
        case
          feed
            ( Array.concat
                [ raw []
                , raw (encodeText "{nope")
                , raw (encodeText "[1]")
                , raw ([ 0xC3, 0x28 ])
                , framed one
                ]
            )
            emptyReader
          of
          Right r -> map classify r.payloads
          Left _ -> []
      classify p = case parsePayload p of
        Left EmptyPayload -> "empty"
        Left NotUtf8 -> "utf8"
        Left (NotJson _) -> "json"
        Left NotAnObject -> "object"
        Right _ -> "ok"
    problems `shouldEqual` [ "empty", "json", "object", "utf8", "ok" ]

-- Envelopes --------------------------------------------------------------------------

envelopes :: Spec Unit
envelopes = describe "envelopes" do
  let
    p = payloadOf "x"
    kind = Tuple "kind" (fromString "ping")
    body = Tuple "payload" (fromString "")
    payload = Tuple "payload" (fromObject p)
    num n = Tuple "id" (fromNumber n)
    reply n = Tuple "replyTo" (fromNumber n)
    decoded = decodeMessage <<< object

  it "reads the three shapes" do
    case messageId 7 of
      Nothing -> fail "7 is a message number"
      Just seven -> do
        decoded [ kind, num 7.0, payload ]
          `shouldEqual` Right (Request { kind: "ping", id: seven, payload: p })
        decoded [ kind, reply 7.0, payload ]
          `shouldEqual` Right (Response { kind: "ping", replyTo: seven, payload: p })
    decoded [ kind, payload ] `shouldEqual` Right (Notification { kind: "ping", payload: p })

  it "round-trips what it writes" do
    case messageId 3 of
      Nothing -> fail "3 is a message number"
      Just three -> do
        let m = Request { kind: "hello", id: three, payload: p }
        decodeMessage (encodeMessage m) `shouldEqual` Right m

  it "answers a problem by the id where one can be read, and by nothing otherwise" do
    let answerable = messageId 9
    decoded [ kind, num 9.0, body ]
      `shouldEqual` Left { reason: PayloadMissing, answerable }
    decoded [ kind, num 9.0, reply 9.0, payload ]
      `shouldEqual` Left { reason: IdAndReplyTo, answerable: Nothing }
    decoded [ kind, num 0.0, payload ]
      `shouldEqual` Left { reason: IdMalformed, answerable: Nothing }
    decoded [ kind, num 2147483648.0, payload ]
      `shouldEqual` Left { reason: IdMalformed, answerable: Nothing }
    decoded [ kind, num 1.5, payload ]
      `shouldEqual` Left { reason: IdMalformed, answerable: Nothing }
    decoded [ num 9.0, payload ]
      `shouldEqual` Left { reason: KindMissing, answerable }
    decoded [ kind, num 9.0, payload, Tuple "extra" (fromString "") ]
      `shouldEqual` Left { reason: FieldUnknown "extra", answerable }

  it "stops numbering rather than wrapping" do
    (messageId 2147483647 >>= nextMessageId) `shouldEqual` Nothing
    map show (nextMessageId firstMessageId) `shouldEqual` map show (messageId 2)

-- Handshakes -------------------------------------------------------------------------

handshakes :: Spec Unit
handshakes = describe "handshakes" do
  let
    hello =
      { protocol: protocolVersion
      , profile: elaborationProfile
      , offers: [ "someday" ]
      , requires: []
      }

  it "puts in force only the capabilities asked for that this side supports" do
    negotiate hello `shouldEqual` Right
      { protocol: 1, profile: "elaboration", capabilities: [] }
    negotiate (hello { offers = [ "invoke", "someday" ], requires = [ "modules" ] }) `shouldEqual` Right
      { protocol: 1, profile: "elaboration", capabilities: [ "modules", "invoke" ] }
    negotiate (hello { offers = [ "modules" ] }) `shouldEqual` Right
      { protocol: 1, profile: "elaboration", capabilities: [ "modules" ] }

  it "refuses another protocol, another profile, and a capability it lacks" do
    let reasonOf h = map _.reason (either Just (const Nothing) (negotiate h))
    reasonOf (hello { protocol = 2 }) `shouldEqual` Just ProtocolUnsupported
    reasonOf (hello { profile = "repl" }) `shouldEqual` Just ProfileUnsupported
    reasonOf (hello { requires = [ "someday" ] }) `shouldEqual` Just CapabilityUnsupported

  it "round-trips its messages" do
    decodeHello (encodeHello hello) `shouldEqual` Just hello
    let ready = { protocol: 1, profile: "elaboration", capabilities: [ "someday" ] }
    decodeReady (encodeReady ready) `shouldEqual` Just ready
    case negotiate (hello { profile = "repl" }) of
      Left refusal -> decodeRefusal (encodeRefusal refusal) `shouldEqual` Just refusal
      Right _ -> fail "the repl profile opened"
  where
  either f g = case _ of
    Left a -> f a
    Right b -> g b

-- Guest requests --------------------------------------------------------------------

guests :: Spec Unit
guests = describe "load and invoke payloads" do
  let
    tok = object [ Tuple "slot" (fromNumber 3.0) ]
    name = { module: "Guest", name: "identity" }

  it "round-trip what they write" do
    decodeLoad (encodeLoad "a/b.dmo") `shouldEqual` Just "a/b.dmo"
    decodeLoaded (encodeLoaded "Guest") `shouldEqual` Just "Guest"
    decodeLoadFailed (encodeLoadFailed { stage: Initialization, detail: "d" })
      `shouldEqual` Just { stage: Initialization, detail: "d" }
    map (\r -> { global: r.global, arguments: map text r.arguments, attempt: r.attempt, budget: r.budget })
      (decodeInvoke (encodeInvoke { global: name, arguments: [ tok ], attempt: 7, budget: 9 }))
      `shouldEqual` Just { global: name, arguments: [ text tok ], attempt: 7, budget: 9 }
    map text (decodeReturned (encodeReturned tok)) `shouldEqual` Just (text tok)
    for_
      [ NotAToken ClassPartialApplication
      , KernelNotInForce
      , CommandNotEncodable ClassClosure
      , Abandoned
      , BudgetExhausted
      , Cancelled
      ]
      \reason ->
        decodeInvocationFailed (encodeInvocationFailed { reason, detail: "d" })
          `shouldEqual` Just { reason, detail: "d" }

  it "refuse a missing field, a field of another type, and one they do not know" do
    decodeLoad Object.empty `shouldEqual` Nothing
    decodeLoad (object [ Tuple "path" (fromNumber 1.0) ]) `shouldEqual` Nothing
    decodeLoad (Object.insert "more" (fromString "") (encodeLoad "x")) `shouldEqual` Nothing
    map (const unit) (decodeInvoke (object [ Tuple "global" (fromObject (object [ Tuple "module" (fromString "M") ])), Tuple "arguments" (fromArray []) ]))
      `shouldEqual` Nothing
    map (const unit) (decodeInvoke (object [ Tuple "global" (fromObject (object [ Tuple "module" (fromString "M"), Tuple "name" (fromString "f") ])), Tuple "arguments" (fromArray [ fromNumber 1.0 ]) ]))
      `shouldEqual` Nothing

  it "refuse an attempt that is not an integer from 1 to 2147483647, or none" do
    let
      withAttempt a = Object.insert "attempt" a (encodeInvoke { global: name, arguments: [], attempt: 1, budget: 1 })
    for_ [ fromNumber 0.0, fromNumber (-1.0), fromNumber 1.5, fromNumber 2147483648.0, fromString "1" ] \a ->
      map (const unit) (decodeInvoke (withAttempt a)) `shouldEqual` Nothing
    map _.attempt (decodeInvoke (withAttempt (fromNumber 2147483647.0))) `shouldEqual` Just 2147483647
    map (const unit) (decodeInvoke (Object.delete "attempt" (withAttempt (fromNumber 1.0)))) `shouldEqual` Nothing

  it "carry a class exactly where the reason is notAToken or commandNotEncodable" do
    let
      withClass = object [ Tuple "reason" (fromString "fault"), Tuple "detail" (fromString ""), Tuple "class" (fromString "int") ]
      withoutClass = object [ Tuple "reason" (fromString "notAToken"), Tuple "detail" (fromString "") ]
      unknownClass = object [ Tuple "reason" (fromString "notAToken"), Tuple "detail" (fromString ""), Tuple "class" (fromString "thing") ]
    decodeInvocationFailed withClass `shouldEqual` Nothing
    decodeInvocationFailed withoutClass `shouldEqual` Nothing
    decodeInvocationFailed unknownClass `shouldEqual` Nothing
    Object.member "class" (encodeInvocationFailed { reason: Fault, detail: "" }) `shouldEqual` false
    Object.member "class" (encodeInvocationFailed { reason: Abandoned, detail: "" }) `shouldEqual` false
    decodeInvocationFailed
      (object [ Tuple "reason" (fromString "commandNotEncodable"), Tuple "detail" (fromString "") ])
      `shouldEqual` Nothing
    decodeInvocationFailed
      (object [ Tuple "reason" (fromString "abandoned"), Tuple "detail" (fromString ""), Tuple "class" (fromString "int") ])
      `shouldEqual` Nothing

  it "carry a cancel, exactly as shown" do
    decodeCancel (encodeCancel 5) `shouldEqual` Just 5
    decodeCancel (object [ Tuple "attempt" (fromNumber 0.0) ]) `shouldEqual` Nothing
    decodeCancel (Object.insert "more" jsonNull (encodeCancel 5)) `shouldEqual` Nothing

  it "carry a kernel request and its two answers, exactly as shown" do
    let command = fromObject (object [ Tuple "int" (fromNumber 1.0) ])
    map (\c -> Tuple c.attempt (stringify c.command)) (decodeKernel (encodeKernel { attempt: 3, command }))
      `shouldEqual` Just (Tuple 3 (stringify command))
    map stringify (decodeAnswered (encodeAnswered command)) `shouldEqual` Just (stringify command)
    decodeAbandoned encodeAbandoned `shouldEqual` Just unit
    map (const unit) (decodeKernel (object [ Tuple "attempt" (fromNumber 0.0), Tuple "command" command ]))
      `shouldEqual` Nothing
    map (const unit) (decodeKernel (object [ Tuple "attempt" (fromNumber 1.0) ])) `shouldEqual` Nothing
    map (const unit) (decodeAnswered (Object.insert "more" jsonNull (encodeAnswered command))) `shouldEqual` Nothing
    decodeAbandoned (object [ Tuple "reason" (fromString "") ]) `shouldEqual` Nothing

-- Peers ------------------------------------------------------------------------------

-- | Two transports joined in memory, every chunk cut into single bytes.
bytewisePair :: Effect { left :: Channel, right :: Channel }
bytewisePair = memoryPair bytesOf

wholePair :: Effect { left :: Channel, right :: Channel }
wholePair = memoryPair (\c -> [ c ])

-- | A side that records what it is told and fails nothing on its own.
type Recorder =
  { notifications :: Ref (Array Incoming)
  , failures :: Ref (Array SessionFailure)
  }

recorder :: Effect Recorder
recorder = { notifications: _, failures: _ } <$> Ref.new [] <*> Ref.new []

quietHandlers
  :: Recorder
  -> (Incoming -> Aff Peer.Answer)
  -> Peer.Handlers
quietHandlers r request =
  { request
  , notification: \n -> Ref.modify_ (_ <> [ n ]) r.notifications
  , failed: \f -> Ref.modify_ (_ <> [ f ]) r.failures
  }

echo :: Incoming -> Aff Peer.Answer
echo incoming = pure (answer { kind: incoming.kind <> "Done", payload: incoming.payload })

-- | Wait for a turn of the event loop, so what is in flight arrives.
settle :: Aff Unit
settle = delay (Milliseconds 0.0)

peers :: Spec Unit
peers = describe "peers" do
  it "answers a request made from inside a request, and then the outer one" do
    pair <- liftEffect bytewisePair
    clientRec <- liftEffect recorder
    serverRec <- liftEffect recorder
    order <- liftEffect (Ref.new [])
    let log s = liftEffect (Ref.modify_ (_ <> [ s ]) order)
    serverSelf <- liftEffect (Ref.new Nothing)
    client <- liftEffect $ Peer.start pair.left $ quietHandlers clientRec \incoming -> do
      log ("client answers " <> incoming.kind)
      pure (answer { kind: "B-done", payload: incoming.payload })
    server <- liftEffect $ Peer.start pair.right $ quietHandlers serverRec \incoming -> do
      log ("server received " <> incoming.kind)
      self <- liftEffect (Ref.read serverSelf)
      inner <- case self of
        Nothing -> pure (Left ShutDown)
        Just s -> Peer.request s "B" (payloadOf "inner")
      log ("server got " <> either' inner)
      pure (answer { kind: "A-done", payload: incoming.payload })
    liftEffect (Ref.write (Just server) serverSelf)
    outer <- Peer.request client "A" (payloadOf "outer")
    map _.kind outer `shouldEqual` Right "A-done"
    map (text <<< _.payload) outer `shouldEqual` Right (text (payloadOf "outer"))
    liftEffect (Ref.read order) >>= shouldEqual
      [ "server received A", "client answers B", "server got B-done" ]
    liftEffect (Ref.read clientRec.failures) >>= shouldEqual []
    liftEffect (Ref.read serverRec.failures) >>= shouldEqual []

  it "matches responses to requests by number, whatever order they come in" do
    pair <- liftEffect wholePair
    rec <- liftEffect recorder
    client <- liftEffect $ Peer.start pair.left (quietHandlers rec echo)
    _ <- liftEffect $ Peer.start pair.right $ quietHandlers rec \incoming ->
      -- the first request is answered only after the second
      if incoming.kind == "slow" then do
        settle
        settle
        pure (answer { kind: "slowDone", payload: incoming.payload })
      else
        pure (answer { kind: "fastDone", payload: incoming.payload })
    arrived <- liftEffect (Ref.new [])
    let
      tracked kind = do
        r <- Peer.request client kind (payloadOf kind)
        liftEffect (Ref.modify_ (_ <> [ kind ]) arrived)
        pure r
    slow <- forkAff (tracked "slow")
    fast <- forkAff (tracked "fast")
    s <- joinFiber slow
    f <- joinFiber fast
    map _.kind s `shouldEqual` Right "slowDone"
    map _.kind f `shouldEqual` Right "fastDone"
    liftEffect (Ref.read arrived) >>= shouldEqual [ "fast", "slow" ]

  it "answers bytes that are not a message and goes on" do
    pair <- liftEffect bytewisePair
    rec <- liftEffect recorder
    received <- liftEffect (Ref.new [])
    _ <- liftEffect $ Peer.start pair.right (quietHandlers rec echo)
    _ <- forkAff (collect pair.left received)
    let
      raw bytes = append (u32BE (Array.length bytes)) bytes
      request n = framed $ object
        [ Tuple "kind" (fromString "ping")
        , Tuple "id" (fromNumber n)
        , Tuple "payload" (fromObject Object.empty)
        ]
    liftEffect do
      pair.left.send (raw (encodeText "not json"))
      pair.left.send (framed (object [ Tuple "kind" (fromString "ping"), Tuple "id" (fromNumber 4.0) ]))
      pair.left.send (framed (object [ Tuple "kind" (fromString "ping"), Tuple "replyTo" (fromNumber 1.0), Tuple "payload" (fromObject Object.empty) ]))
      pair.left.send (request 5.0)
    settleMany 200
    chunks <- liftEffect (Ref.read received)
    let
      messages = case feed (Array.concat chunks) emptyReader of
        Right r -> traverse (\p -> either'' (parsePayload p) >>= (decodeMessage >>> either'')) r.payloads
        Left _ -> Nothing
      codeOf m = case m of
        Response r | r.kind == protocolErrorKind -> map _.code (decodeProtocolError r.payload)
        Notification r | r.kind == protocolErrorKind -> map _.code (decodeProtocolError r.payload)
        _ -> Nothing
      shape m = case m of
        Request r -> "request " <> r.kind
        Response r -> "response " <> r.kind <> " " <> show r.replyTo
        Notification r -> "notification " <> r.kind
    map (map shape) messages `shouldEqual` Just
      [ "notification protocolError"
      , "response protocolError (MessageId 4)"
      , "notification protocolError"
      , "response pingDone (MessageId 5)"
      ]
    map (map codeOf) messages `shouldEqual` Just
      [ Just "payloadUnreadable", Just "envelopeInvalid", Just "replyUnexpected", Nothing ]
    liftEffect (Ref.read rec.failures) >>= shouldEqual []

  it "runs a request once, refusing a number it has seen or one below it" do
    pair <- liftEffect wholePair
    rec <- liftEffect recorder
    runs <- liftEffect (Ref.new 0)
    received <- liftEffect (Ref.new [])
    _ <- liftEffect $ Peer.start pair.right $ quietHandlers rec \incoming -> do
      liftEffect (Ref.modify_ (_ + 1) runs)
      echo incoming
    _ <- forkAff (collect pair.left received)
    let
      request n = framed $ object
        [ Tuple "kind" (fromString "ping")
        , Tuple "id" (fromNumber n)
        , Tuple "payload" (fromObject Object.empty)
        ]
      malformed n = framed $ object [ Tuple "kind" (fromString "ping"), Tuple "id" (fromNumber n) ]
    liftEffect do
      pair.left.send (request 5.0)
      pair.left.send (request 5.0)
      pair.left.send (request 3.0)
      pair.left.send (malformed 7.0)
      pair.left.send (request 7.0)
      pair.left.send (request 8.0)
    settleMany 20
    chunks <- liftEffect (Ref.read received)
    let
      messages = case feed (Array.concat chunks) emptyReader of
        Right r -> traverse (\p -> hush (parsePayload p) >>= (decodeMessage >>> hush)) r.payloads
        Left _ -> Nothing
      shape m = case m of
        Request r -> "request " <> r.kind
        Response r -> "response " <> r.kind <> " " <> show r.replyTo <> code r.payload
        Notification r -> "notification " <> r.kind <> code r.payload
      code p = case decodeProtocolError p of
        Just e -> " " <> e.code
        Nothing -> ""
    map (map shape) messages `shouldEqual` Just
      [ "response pingDone (MessageId 5)"
      , "notification protocolError idReused"
      , "notification protocolError idReused"
      , "response protocolError (MessageId 7) envelopeInvalid"
      , "notification protocolError idReused"
      , "response pingDone (MessageId 8)"
      ]
    liftEffect (Ref.read runs) >>= shouldEqual 2

  it "fails what is outstanding when the channel ends, and reports the failure once" do
    pair <- liftEffect wholePair
    rec <- liftEffect recorder
    client <- liftEffect $ Peer.start pair.left (quietHandlers rec echo)
    pending <- forkAff (Peer.request client "ping" Object.empty)
    settle
    pair.right.end
    result <- joinFiber pending
    map _.kind result `shouldEqual` Left ChannelEnded
    liftEffect (Ref.read rec.failures) >>= shouldEqual [ ChannelEnded ]
    after <- Peer.request client "ping" Object.empty
    map _.kind after `shouldEqual` Left ChannelEnded

  it "fails with the frame when the channel ends inside one" do
    pair <- liftEffect wholePair
    rec <- liftEffect recorder
    _ <- liftEffect $ Peer.start pair.left (quietHandlers rec echo)
    liftEffect (pair.right.send [ 0, 0 ])
    pair.right.end
    settleMany 5
    liftEffect (Ref.read rec.failures) >>= shouldEqual [ FrameUnreadable (TruncatedPrefix 2) ]

  it "does not report an end it asked for" do
    pair <- liftEffect wholePair
    rec <- liftEffect recorder
    otherRec <- liftEffect recorder
    client <- liftEffect $ Peer.start pair.left (quietHandlers rec echo)
    other <- liftEffect $ Peer.start pair.right (quietHandlers otherRec echo)
    liftEffect (Peer.shutdown client (pure unit))
    settleMany 5
    liftEffect (Ref.read rec.failures) >>= shouldEqual []
    liftEffect (Ref.read otherRec.failures) >>= shouldEqual [ ChannelEnded ]
    r <- Peer.request client "ping" Object.empty
    map _.kind r `shouldEqual` Left ShutDown
    r' <- Peer.request other "ping" Object.empty
    map _.kind r' `shouldEqual` Left ChannelEnded
  where
  either' = case _ of
    Right r -> r.kind
    Left f -> show f

  either'' :: forall e a. Either e a -> Maybe a
  either'' = case _ of
    Right a -> Just a
    Left _ -> Nothing

settleMany :: Int -> Aff Unit
settleMany n
  | n <= 0 = pure unit
  | otherwise = settle *> settleMany (n - 1)

-- | Everything a channel receives, into a reference, until it ends.
collect :: Channel -> Ref (Array Bytes) -> Aff Unit
collect channel into = channel.receive >>= case _ of
  Received bytes -> liftEffect (Ref.modify_ (_ <> [ bytes ]) into) *> collect channel into
  _ -> pure unit
