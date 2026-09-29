-- | The `session` command, as a process a client starts.
-- |
-- | What is asserted is what a client sees: the answers on descriptor 3 and how the
-- | process ended. A server written inline stands in for `steam` where a case needs
-- | a way of ending that `steam` itself never takes.
module Test.Steam.Session
  ( spec
  , Streams
  , streams
  , draining
  , hello
  , node
  , open'
  , close'
  , ping'
  , request'
  , opened
  ) where

import Prelude

import Data.Argonaut.Core (Json, fromString)
import Data.Array as Array
import Data.Either (Either(..), either)
import Data.Maybe (Maybe(..))
import Data.String as String
import Data.Tuple (Tuple(..))
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Foreign.Object as Object
import Run (AFF, EFFECT, Run, runBaseAff')
import Stella.CLI.Effect.Process (Child, Exit, Output(..), PROCESS, spawnSession)
import Stella.CLI.Effect.Process as Process
import Stella.CLI.Runner.Node (nodeProcessHandler)
import Stella.CLI.Session.Frame (u32BE)
import Stella.Compiler.Bytecode.Bytes (utf8)
import Type.Row (type (+))
import Stella.CLI.Session.Client (ClientFailure(..), OpenFailure(..), RequestFailure(..), Session)
import Stella.CLI.Session.Client as Client
import Stella.CLI.Session.Peer as Peer
import Stella.CLI.Session.Protocol (Hello, RefusalReason(..), encodeHello, helloKind, pingKind, supported)
import Stella.CLI.Session.ProtocolError (decodeProtocolError, protocolErrorKind)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual, shouldSatisfy)

type Streams = { stdout :: Ref String, stderr :: Ref String }

streams :: Aff Streams
streams = liftEffect ({ stdout: _, stderr: _ } <$> Ref.new "" <*> Ref.new "")

draining :: Streams -> Output
draining s = Drain
  { stdout: \t -> Ref.modify_ (_ <> t) s.stdout
  , stderr: \t -> Ref.modify_ (_ <> t) s.stderr
  }

hello :: Hello
hello = { protocol: 1, profile: "elaboration", offers: [], requires: [] }

steam :: Streams -> Hello -> Client.Launch
steam s h = { command: "node", args: [ "steam/index.dev.js", "session" ], output: draining s, hello: h }

-- | A server written inline, reading frames on descriptor 3 and handing each
-- | message to `on`, with `send` to answer and `socket` to end the channel.
fake :: Streams -> String -> Client.Launch
fake s behaviour =
  { command: "node"
  , args: [ "-e", prelude <> behaviour ]
  , output: draining s
  , hello
  }
  where
  prelude = String.joinWith "\n"
    [ "const socket = new (require('net').Socket)({ fd: 3 });"
    , "const send = (o) => { const b = Buffer.from(JSON.stringify(o)); const h = Buffer.alloc(4); h.writeUInt32BE(b.length); socket.write(Buffer.concat([h, b])); };"
    , "const ready = (m) => send({ kind: 'ready', replyTo: m.id, payload: { protocol: 1, profile: 'elaboration', capabilities: [] } });"
    , "let buf = Buffer.alloc(0);"
    , "socket.on('data', (d) => { buf = Buffer.concat([buf, d]); while (buf.length >= 4) { const n = buf.readUInt32BE(0); if (buf.length < 4 + n) break; const m = JSON.parse(buf.subarray(4, 4 + n)); buf = buf.subarray(4 + n); on(m); } });"
    , ""
    ]

-- | Run what a client does, starting processes as this host does.
node :: forall a. Run (PROCESS + AFF + EFFECT + ()) a -> Aff a
node = runBaseAff' <<< Process.interpret nodeProcessHandler

open' :: Client.Launch -> Aff (Either OpenFailure Session)
open' = node <<< Client.open

ping' :: Session -> Aff (Either RequestFailure Unit)
ping' = node <<< Client.ping

close' :: Session -> Aff (Either ClientFailure Unit)
close' = node <<< Client.close

request' :: Session -> String -> Object.Object Json -> Aff (Either RequestFailure Peer.Reply)
request' session kind payload = node (Client.request session kind payload)

abandon' :: Session -> Aff Exit
abandon' = node <<< Client.abandon

kill' :: Session -> Aff Exit
kill' = node <<< Client.kill

-- | `steam session`, started as a client would, without a handshake.
steamChild :: Streams -> Aff Child
steamChild s = node (spawnSession { command: "node", args: [ "steam/index.dev.js", "session" ], output: draining s })

opened :: Client.Launch -> (Session -> Aff Unit) -> Aff Unit
opened launch k = open' launch >>= case _ of
  Right session -> k session
  Left failure -> fail ("the session did not open: " <> show failure)

spec :: Spec Unit
spec = describe "steam session" do
  describe "against steam" do
    it "opens with no capability in force, answers a ping, and closes with status 0" do
      s <- streams
      -- the lifecycle requests are the protocol itself and need no capability
      opened (steam s hello) \session -> do
        (Client.ready session).capabilities `shouldEqual` []
        ping' session >>= shouldEqual (Right unit)
        close' session >>= shouldEqual (Right unit)

    it "refuses another protocol, another profile, and a capability it lacks" do
      let
        refusal h = do
          s <- streams
          open' (steam s h) >>= case _ of
            Left (Refused r) -> pure (Just r)
            _ -> pure Nothing
      protocol <- refusal (hello { protocol = 2 })
      map _.reason protocol `shouldEqual` Just ProtocolUnsupported
      map _.supported protocol `shouldEqual` Just supported
      profile <- refusal (hello { profile = "repl" })
      map _.reason profile `shouldEqual` Just ProfileUnsupported
      capability <- refusal (hello { requires = [ "kernel" ] })
      map _.reason capability `shouldEqual` Just CapabilityUnsupported

    it "writes out its refusal and then ends with status 1" do
      s <- streams
      child <- steamChild s
      case child.channel of
        Nothing -> fail "no channel"
        Just channel -> do
          peer <- liftEffect $ Peer.start channel
            { request: \_ -> pure (Peer.answer { kind: "unused", payload: Object.empty })
            , notification: \_ -> pure unit
            , failed: \_ -> pure unit
            }
          answer <- Peer.request peer helloKind (encodeHello (hello { protocol = 2 }))
          map _.kind answer `shouldEqual` Right "refused"
          exit <- child.exit
          exit.code `shouldEqual` Just 1

    it "puts in force no capability it does not have, however much is offered" do
      s <- streams
      opened (steam s (hello { offers = [ "kernel", "someday" ] })) \session -> do
        (Client.ready session).capabilities `shouldEqual` []
        ping' session >>= shouldEqual (Right unit)
        close' session >>= shouldEqual (Right unit)

    it "refuses one request and answers the next" do
      s <- streams
      opened (steam s hello) \session -> do
        request' session "evaluate" Object.empty >>= case _ of
          Left (RequestRefused e) -> e.code `shouldEqual` "kindUnknown"
          _ -> fail "an unknown kind was answered"
        request' session helloKind (encodeHello hello) >>= case _ of
          Left (RequestRefused e) -> e.code `shouldEqual` "kindUnexpected"
          _ -> fail "a second hello was answered"
        request' session pingKind (Object.singleton "x" (fromString "")) >>= case _ of
          Left (RequestRefused e) -> e.code `shouldEqual` "payloadInvalid"
          _ -> fail "a ping with a payload was answered"
        ping' session >>= shouldEqual (Right unit)
        close' session >>= shouldEqual (Right unit)

    it "answers bytes that are not a message and goes on" do
      s <- streams
      child <- steamChild s
      case child.channel of
        Nothing -> fail "no channel"
        Just channel -> do
          notes <- liftEffect (Ref.new [])
          peer <- liftEffect $ Peer.start channel
            { request: \_ -> pure (Peer.answer { kind: "unused", payload: Object.empty })
            , notification: \n -> Ref.modify_ (_ <> [ n ]) notes
            , failed: \_ -> pure unit
            }
          liftEffect do
            channel.send [ 0, 0, 0, 0 ]
            let junk = either (const []) identity (utf8 "{ not json")
            channel.send (u32BE (Array.length junk) <> junk)
          answer <- Peer.request peer helloKind (encodeHello hello)
          map _.kind answer `shouldEqual` Right "ready"
          pong <- Peer.request peer pingKind Object.empty
          map _.kind pong `shouldEqual` Right "pong"
          seen <- liftEffect (Ref.read notes)
          map (\n -> Tuple n.kind (map _.code (decodeProtocolError n.payload))) seen
            `shouldEqual`
              [ Tuple protocolErrorKind (Just "payloadUnreadable")
              , Tuple protocolErrorKind (Just "payloadUnreadable")
              ]
          liftEffect child.kill
          _ <- child.exit
          pure unit

    it "ends with status 1 when the channel ends without close" do
      s <- streams
      opened (steam s hello) \session -> do
        exit <- abandon' session
        exit.code `shouldEqual` Just 1
        err <- liftEffect (Ref.read s.stderr)
        err `shouldSatisfy` String.contains (String.Pattern "without `close`")

    it "is lost to a request after the process is killed" do
      s <- streams
      opened (steam s hello) \session -> do
        exit <- kill' session
        exit.signal `shouldEqual` Just "SIGKILL"
        ping' session >>= case _ of
          Left (SessionLost _) -> pure unit
          other -> fail ("a killed session answered: " <> show other)

  describe "judged by the client" do
    it "takes an exit 0 before the handshake for a failure" do
      s <- streams
      open' (fake s "process.exit(0);") >>= case _ of
        Left (OpenFailed (ExitedUnannounced exit)) -> exit.code `shouldEqual` Just 0
        other -> fail ("unexpected: " <> show (map (const unit) other))

    it "takes an exit 0 without closed for a failure" do
      s <- streams
      opened (fake s "function on(m) { if (m.kind === 'hello') ready(m); else if (m.kind === 'close') process.exit(0); }") \session ->
        close' session >>= case _ of
          Left (ExitedUnannounced exit) -> exit.code `shouldEqual` Just 0
          other -> fail ("unexpected: " <> show other)

    it "takes closed followed by another status for a failure" do
      s <- streams
      opened (fake s "function on(m) { if (m.kind === 'hello') ready(m); else if (m.kind === 'close') { send({ kind: 'closed', replyTo: m.id, payload: {} }); socket.end(() => process.exit(2)); } }") \session ->
        close' session >>= case _ of
          Left (ExitedAfterClosed exit) -> exit.code `shouldEqual` Just 2
          other -> fail ("unexpected: " <> show other)

    it "keeps a refusal whatever the exit that follows it" do
      s <- streams
      open' (fake s "function on(m) { send({ kind: 'refused', replyTo: m.id, payload: { reason: 'profile', supported: { protocols: [1], profiles: [], capabilities: [] } } }); socket.end(() => process.exit(3)); }") >>= case _ of
        Left (Refused r) -> r.reason `shouldEqual` ProfileUnsupported
        other -> fail ("unexpected: " <> show (map (const unit) other))

    it "reads a child that writes a lot before answering" do
      s <- streams
      let
        flood = "process.stdout.write('o'.repeat(4 << 20)); process.stderr.write('e'.repeat(4 << 20));\n"
          <> "function on(m) { if (m.kind === 'hello') ready(m); else if (m.kind === 'close') { send({ kind: 'closed', replyTo: m.id, payload: {} }); socket.end(); process.exitCode = 0; } }"
      opened (fake s flood) \session -> do
        close' session >>= shouldEqual (Right unit)
        out <- liftEffect (Ref.read s.stdout)
        err <- liftEffect (Ref.read s.stderr)
        String.length out `shouldEqual` (4 * 1024 * 1024)
        String.length err `shouldEqual` (4 * 1024 * 1024)

    it "does not open on a ready that does not answer the hello" do
      let
        readyWith payload = "function on(m) { send({ kind: 'ready', replyTo: m.id, payload: " <> payload <> " }); }"
        judged launch = do
          outcome <- open' launch
          pure case outcome of
            Left (OpenFailed (ReadyUnacceptable _ why)) -> Just why
            _ -> Nothing
      s <- streams
      judged (fake s (readyWith "{ protocol: 2, profile: 'elaboration', capabilities: [] }"))
        >>= shouldEqual (Just "it names another protocol")
      judged (fake s (readyWith "{ protocol: 1, profile: 'repl', capabilities: [] }"))
        >>= shouldEqual (Just "it names another profile")
      judged ((fake s (readyWith "{ protocol: 1, profile: 'elaboration', capabilities: [] }")) { hello = hello { requires = [ "kernel" ] } })
        >>= shouldEqual (Just "it leaves out a capability the client requires")
      judged (fake s (readyWith "{ protocol: 1, profile: 'elaboration', capabilities: ['kernel'] }"))
        >>= shouldEqual (Just "it puts in force a capability the client did not ask for")

    it "takes a protocol error that does not read as one for a failed session" do
      s <- streams
      opened (fake s "function on(m) { if (m.kind === 'hello') ready(m); else send({ kind: 'protocolError', replyTo: m.id, payload: {} }); }") \session -> do
        ping' session >>= shouldEqual (Left (SessionLost (AnswerMalformed "protocolError")))
        ping' session >>= case _ of
          Left (SessionLost _) -> pure unit
          other -> fail ("the session answered after misbehaving: " <> show other)

    it "keeps a character whole when the output splits it across chunks" do
      s <- streams
      let
        split = "process.stdout.write(Buffer.from([0xE6])); setTimeout(() => process.stdout.write(Buffer.from([0x98, 0x9F])), 50);\n"
          <> "function on(m) { if (m.kind === 'hello') ready(m); else if (m.kind === 'close') { send({ kind: 'closed', replyTo: m.id, payload: {} }); socket.end(); process.exitCode = 0; } }"
      opened (fake s split) \session -> do
        close' session >>= shouldEqual (Right unit)
        liftEffect (Ref.read s.stdout) >>= shouldEqual "星"

    it "reports a command that never starts" do
      s <- streams
      open' ((fake s "") { command = "/nonexistent/steam" }) >>= case _ of
        Left (OpenFailed (NotStarted _)) -> pure unit
        other -> fail ("unexpected: " <> show (map (const unit) other))
