-- | A guest synthesizer run as an attempt, the compiler's conversation answering
-- | its commands.
-- |
-- | The session is a process written inline standing in for Steam: it answers the
-- | handshake, and runs each `invoke` as the test's guest says — sending `kernel`
-- | requests, reading what they are answered with, and ending the invocation. What
-- | it saw it writes to standard error, one line of JSON a test reads back.
module Test.Stella.CLI.Session.Broker
  ( spec
  , withSession
  , node
  , descriptor
  ) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Argonaut.Core (toArray, toString)
import Data.Argonaut.Parser (jsonParser)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Map as Map
import Data.String as String
import Data.Tuple (Tuple(..))
import Effect.Aff (Aff, Milliseconds(..), delay, forkAff, joinFiber)
import Effect.Class (liftEffect)
import Effect.Exception (throw)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Run (AFF, EFFECT, Run, runBaseAff')
import Stella.CLI.Effect.Process (Output(..), PROCESS)
import Stella.CLI.Effect.Process as Process
import Stella.CLI.Runner.Node (nodeProcessHandler)
import Stella.CLI.Session.Broker (Brokered(..), Cancellation, SessionHealth(..), cancel, newCancellation, runGuest)
import Stella.CLI.Session.Broker.Settle (Settled(Settled), settle)
import Stella.CLI.Session.Broker.Settle as Settle
import Stella.CLI.Session.Client (ClientFailure(..), Session)
import Stella.CLI.Session.Guest (InvocationReason(Abandoned, BudgetExhausted, CommandNotEncodable, Fault, KernelNotInForce, NoSuchModule, NotAToken), ValueClass(..))
import Stella.Compiler.Elaborate.Driver.Attempt (OpenResult(..))
import Stella.Compiler.Elaborate.Driver.Conversation (openConversation)
import Stella.CLI.Session.Client as Client
import Stella.Compiler.Elaborate.CorePlus.Context (Origin(..), emptyXContext)
import Stella.Compiler.Elaborate.CorePlus.Type (XType(..))
import Stella.Compiler.Elaborate.Environment.Catalog (EntrySort(..), catalogOf)
import Stella.Compiler.Elaborate.Environment.Constructors (constructorsOf)
import Stella.Compiler.Elaborate.Environment.Effects (effectsOf)
import Stella.Compiler.Elaborate.Kernel.Elab (Outcome(..), SessionEnv, SolverState, createSynthesis, initialState, runElabIn)
import Stella.Compiler.Elaborate.Mechanism.Kinding (kindingOf)
import Stella.Compiler.Elaborate.Mechanism.Pending (PendingId)
import Stella.Compiler.Elaborate.Mechanism.Scheduler (takeReady)
import Stella.Compiler.Elaborate.Protocol.Guest (bundle)
import Stella.Compiler.Elaborate.Protocol.Guest.Shape (Descriptor)
import Stella.Compiler.Elaborate.Vocabulary.Diagnostic (Defect(..))
import Stella.Compiler.Elaborate.Vocabulary.Handle (SessionId(..))
import Stella.Compiler.Elaborate.Vocabulary.Outcome (Attempt(..))
import Stella.Compiler.Elaborate.Vocabulary.Trace (TraceEvent(..), Tracing(..))
import Stella.Compiler.TypedCore (AttrValue(..), Ident(..), ModuleName(..), Qualified(..))
import Stella.Compiler.TypedCore.Prim (intTy, primSignature)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual, shouldSatisfy)
import Type.Row (type (+))

-- The compiler's side ------------------------------------------------------------------------

env :: SessionEnv
env =
  { catalog: catalogOf
      [ { name: Qualified (ModuleName "Main") (Ident "bad\xD800")
        , sort: ValueEntry
        , scheme: { kindVars: [], body: XCon intTy [] }
        , attributes: [ { key: "marked", value: AttrUnit } ]
        }
      ]
  , kinding: kindingOf primSignature
  , constructors: constructorsOf primSignature
  , effects: effectsOf primSignature
  , tracing: TraceEnabled
  }

-- | A synthesis job at `Int`, taken from the ready queue.
type Job = { id :: PendingId, state :: SolverState }

job :: Either String Job
job = case runElabIn env (initialState (SessionId 1) 10) created of
  Tuple (Done id) queued -> case takeReady queued.tentative.scheduler of
    Just (Tuple _ scheduler) -> Right { id, state: queued { tentative { scheduler = scheduler } } }
    Nothing -> Left "no job was queued"
  Tuple other _ -> Left ("the job was not created: " <> show other)
  where
  created = do
    Tuple id _ <- createSynthesis site (XCon intTy []) (Qualified (ModuleName "Typeclass") (Ident "resolve")) Nothing
    pure id
  site = { context: emptyXContext, origin: InDeclaration (Qualified (ModuleName "User") (Ident "answer")) }

-- The session standing in for Steam ------------------------------------------------------------

type Streams = { stdout :: Ref String, stderr :: Ref String }

-- | A session whose `invoke`s are run by `guest`, an async JavaScript function of
-- | the invocation's payload that ends in `{ kind, payload }`. `kernel(attempt,
-- | command)` asks the client and gives its response; `note(x)` records what the
-- | guest saw, and `onPing` is run on a `ping` before it is answered.
launch :: Streams -> String -> Client.Launch
launch s = launchOffering [ "modules", "invoke", "kernel" ] s

-- | The same, the client offering those capabilities and the session putting them
-- | all in force.
launchOffering :: Array String -> Streams -> String -> Client.Launch
launchOffering offers s guest =
  { command: "node"
  , args: [ "-e", String.joinWith "\n" prelude <> "\n" <> guest ]
  , output: Drain
      { stdout: \t -> Ref.modify_ (_ <> t) s.stdout
      , stderr: \t -> Ref.modify_ (_ <> t) s.stderr
      }
  , hello: { protocol: 1, profile: "elaboration", offers, requires: [] }
  }
  where
  prelude =
    [ "const socket = new (require('net').Socket)({ fd: 3 });"
    , "const send = (o) => { const b = Buffer.from(JSON.stringify(o)); const h = Buffer.alloc(4); h.writeUInt32BE(b.length); socket.write(Buffer.concat([h, b])); };"
    , "let nextId = 1; const waiting = new Map(); const seen = [];"
    , "const note = (x) => seen.push(x);"
    , "const ask = (kind, payload) => new Promise((resolve) => { const id = nextId++; waiting.set(id, resolve); send({ kind, id, payload }); });"
    , "const kernel = (attempt, command) => ask('kernel', { attempt, command });"
    , "const d = (name, fields = []) => ({ data: { module: 'Stella.Elab', name }, fields });"
    , "const list = (xs) => xs.reduceRight((rest, x) => d('Cons', [x, rest]), d('Nil'));"
    , "const cmd = (family, request) => d('Kernel', [d(family, [request])]);"
    , "const handleOf = (r) => r.kind === 'answered' && r.payload.answer.fields[0].fields[0].token;"
    , "const answerOf = (r) => r.kind === 'answered' ? r.payload.answer.data.name : r.kind === 'protocolError' ? 'protocolError ' + r.payload.code : r.kind;"
    , "const caps = " <> show offers <> ";"
    , "let onPing = async () => {};"
    , "let onHello = async () => {};"
    , "let cancelSeen; const cancelArrived = new Promise((r) => { cancelSeen = r; });"
    , "let onCancel = async (m) => { send({ kind: 'cancelled', replyTo: m.id, payload: {} }); cancelSeen(m.payload.attempt); };"
    , "let buf = Buffer.alloc(0);"
    , "function on(m) {"
    , "  if (m.replyTo !== undefined) { const r = waiting.get(m.replyTo); waiting.delete(m.replyTo); if (r) r(m); return; }"
    , "  if (m.kind === 'hello') return onHello().then(() => send({ kind: 'ready', replyTo: m.id, payload: { protocol: 1, profile: 'elaboration', capabilities: caps } }));"
    , "  if (m.kind === 'cancel') return onCancel(m);"
    , "  if (m.kind === 'ping') return onPing().then(() => send({ kind: 'pong', replyTo: m.id, payload: {} }));"
    , "  if (m.kind === 'close') { process.stderr.write('SEEN ' + JSON.stringify(seen) + '\\n'); send({ kind: 'closed', replyTo: m.id, payload: {} }); socket.end(); return; }"
    , "  if (m.kind === 'invoke') return guest(m.payload).then((r) => send({ kind: r.kind, replyTo: m.id, payload: r.payload }));"
    , "}"
    , "socket.on('data', (chunk) => { buf = Buffer.concat([buf, chunk]); while (buf.length >= 4) { const n = buf.readUInt32BE(0); if (buf.length < 4 + n) break; const m = JSON.parse(buf.subarray(4, 4 + n)); buf = buf.subarray(4 + n); on(m); } });"
    , "const returned = (token) => ({ kind: 'returned', payload: { token } });"
    , "const failed = (reason) => ({ kind: 'invocationFailed', payload: { reason, detail: '' } });"
    -- the synthesizer answering `1`: a root scope, and the literal built in it
    , "const answerOne = async (a) => { const root = handleOf(await kernel(a, cmd('BuildRequest', d('RootScope')))); return handleOf(await kernel(a, cmd('TermRequest', d('LiteralTerm', [{ token: root }, d('LitInt', [{ int: 1 }])])))); };"
    , "const throwing = (a) => kernel(a, cmd('ReportRequest', d('Throw', [list([d('TextPart', [{ string: 'no' }])])])));"
    ]

node :: forall a. Run (PROCESS + AFF + EFFECT + ()) a -> Aff a
node = runBaseAff' <<< Process.interpret nodeProcessHandler

-- | Open the session, run what the test does with it, close it, and hand back what
-- | the guest saw.
withSession :: String -> (Session -> Aff Unit) -> Aff (Array String)
withSession = withSessionOffering [ "modules", "invoke", "kernel" ]

withSessionOffering :: Array String -> String -> (Session -> Aff Unit) -> Aff (Array String)
withSessionOffering offers guest k = do
  s <- liftEffect ({ stdout: _, stderr: _ } <$> Ref.new "" <*> Ref.new "")
  node (Client.open (launchOffering offers s guest)) >>= case _ of
    Left failure -> fail ("the session did not open: " <> show failure) *> pure []
    Right session -> do
      k session
      _ <- node (Client.close session)
      err <- liftEffect (Ref.read s.stderr)
      pure (seenIn err)

-- | The notes the guest wrote, one string each.
seenIn :: String -> Array String
seenIn err = case Array.find (String.contains (String.Pattern "SEEN ")) (String.split (String.Pattern "\n") err) of
  Just line -> case jsonParser (String.drop 5 line) of
    Right json -> Array.mapMaybe toString (fromMaybe [] (toArray json))
    Left _ -> []
  Nothing -> []

running :: Session -> Int -> Aff Brokered
running session attempt = do
  never <- liftEffect (newCancellation (Milliseconds 1000.0))
  runningWith never session attempt

runningWith :: Cancellation -> Session -> Int -> Aff Brokered
runningWith cancellation session attempt = case job of
  Left err -> liftEffect (throw err)
  Right j -> node (runGuest session descriptor { global: { module: "Synth", name: "synth" }, attempt, budget: 1000000 } cancellation env j.id j.state)

-- | `Stella.Elab`'s descriptor, which the compiler's bundle holds.
descriptor :: Descriptor
descriptor = case bundle of
  Right trusted -> trusted.descriptor
  Left _ -> Map.empty

-- | How a run ended, as far as a test needs it.
endedAs :: Brokered -> String
endedAs = case _ of
  Ended attempt _ -> "Ended " <> show attempt
  InvocationFailed failure _ -> "InvocationFailed " <> show failure.reason
  RequestRejected refusal _ -> "RequestRejected " <> refusal.code
  SessionLost failure _ -> "SessionLost " <> show failure
  Cancelled _ health -> "Cancelled " <> show health

stateOf :: Brokered -> Maybe SolverState
stateOf = case _ of
  Ended _ s -> Just s
  _ -> Nothing

abandonedTraced :: Brokered -> Boolean
abandonedTraced b = case stateOf b of
  Just s -> Array.any
    ( case _ of
        AttemptAbandoned _ -> true
        _ -> false
    )
    s.retained.trace
  Nothing -> false

spec :: Spec Unit
spec = describe "Stella.CLI.Session.Broker" do
  describe "an attempt run by a guest" do
    it "answers each command where the conversation stands, and finishes with what the guest returned" do
      result <- liftEffect (Ref.new "")
      seen <- withSession
        "const guest = async (p) => { const e = await answerOne(p.attempt); note(p.arguments[0].class); return returned(e); };"
        \session -> do
          b <- running session 1
          liftEffect (Ref.write (endedAs b) result)
      liftEffect (Ref.read result) >>= shouldEqual "Ended Committed"
      seen `shouldEqual` [ "goal" ]

    it "opens and closes transactions with the guest, a failure inside closing the innermost on both sides" do
      result <- liftEffect (Ref.new "")
      seen <- withSession
        ( "const guest = async (p) => { const a = p.attempt;"
            <> " note(answerOf(await kernel(a, d('BeginTransaction'))));"
            <> " note(answerOf(await kernel(a, d('BeginTransaction'))));"
            <> " note(answerOf(await throwing(a)));"
            <> " note(answerOf(await kernel(a, d('CommitTransaction'))));"
            <> " return returned(await answerOne(a)); };"
        )
        \session -> do
          b <- running session 1
          liftEffect (Ref.write (endedAs b) result)
      liftEffect (Ref.read result) >>= shouldEqual "Ended Committed"
      seen `shouldEqual` [ "TransactionBegun", "TransactionBegun", "CandidateFailed", "TransactionCommitted" ]

    it "keeps the ending the host gave while the guest waited, whatever the invocation then says" do
      result <- liftEffect (Ref.new "")
      seen <- withSession
        "const guest = async (p) => { note(answerOf(await throwing(p.attempt))); return failed('abandoned'); };"
        \session -> do
          b <- running session 1
          liftEffect (Ref.write (endedAs b) result)
      liftEffect (Ref.read result) >>= \r -> r `shouldSatisfy` (String.contains (String.Pattern "Ended (Rejected"))
      seen `shouldEqual` [ "abandoned" ]

  describe "what does not read" do
    it "ends the attempt as a defect, traced, where a command is canonical and no GuestCommand" do
      result <- liftEffect (Ref.new Nothing)
      seen <- withSession
        "const guest = async (p) => { note(answerOf(await kernel(p.attempt, { boolean: true }))); return failed('abandoned'); };"
        \session -> do
          b <- running session 1
          liftEffect (Ref.write (Just b) result)
      liftEffect (Ref.read result) >>= case _ of
        Just b@(Ended (Halted (GuestCommandUnreadable _)) _) -> abandonedTraced b `shouldEqual` true
        Just other -> fail ("ended otherwise: " <> endedAs other)
        Nothing -> fail "no result"
      seen `shouldEqual` [ "abandoned" ]

    it "refuses a command that is no canonical value, which ends the session" do
      s <- liftEffect ({ stdout: _, stderr: _ } <$> Ref.new "" <*> Ref.new "")
      node (Client.open (launch s "const guest = async (p) => { const r = await kernel(p.attempt, { int: 1.5 }); process.stderr.write('ANSWER ' + answerOf(r) + '\\n'); socket.destroy(); process.exitCode = 1; return new Promise(() => {}); };")) >>= case _ of
        Left failure -> fail (show failure)
        Right session -> do
          b <- running session 1
          endedAs b `shouldSatisfy` String.contains (String.Pattern "SessionLost")
          err <- liftEffect (Ref.read s.stderr)
          err `shouldSatisfy` String.contains (String.Pattern "ANSWER protocolError payloadInvalid")

    it "ends the attempt as a defect, traced, where the host's answer has no guest form, and goes on" do
      result <- liftEffect (Ref.new Nothing)
      pinged <- liftEffect (Ref.new false)
      seen <- withSession
        "const guest = async (p) => { note(answerOf(await kernel(p.attempt, cmd('ObserveRequest', d('DeclsWithAttr', [{ string: 'marked' }]))))); return failed('abandoned'); };"
        \session -> do
          b <- running session 1
          liftEffect (Ref.write (Just b) result)
          node (Client.ping session) >>= case _ of
            Right _ -> liftEffect (Ref.write true pinged)
            Left _ -> pure unit
      liftEffect (Ref.read result) >>= case _ of
        Just b@(Ended (Halted (GuestAnswerUnwritable _)) _) -> abandonedTraced b `shouldEqual` true
        Just other -> fail ("ended otherwise: " <> endedAs other)
        Nothing -> fail "no result"
      seen `shouldEqual` [ "abandoned" ]
      liftEffect (Ref.read pinged) >>= shouldEqual true

    it "ends the attempt, with nothing sent, where the result is no handle" do
      result <- liftEffect (Ref.new Nothing)
      seen <- withSession
        "const guest = async (p) => returned({ handle: 'x' });"
        \session -> do
          b <- running session 1
          liftEffect (Ref.write (Just b) result)
      liftEffect (Ref.read result) >>= case _ of
        Just b@(Ended (Halted (GuestResultUnreadable _)) _) -> abandonedTraced b `shouldEqual` true
        Just other -> fail ("ended otherwise: " <> endedAs other)
        Nothing -> fail "no result"
      seen `shouldEqual` []

    it "hands a handle of the right shape and the wrong age to the compiler to refuse" do
      result <- liftEffect (Ref.new "")
      _ <- withSession
        "const guest = async (p) => { const g = p.arguments[0]; return returned({ ...g, generation: g.generation + 100 }); };"
        \session -> do
          b <- running session 1
          liftEffect (Ref.write (endedAs b) result)
      liftEffect (Ref.read result) >>= \r -> r `shouldSatisfy` (String.contains (String.Pattern "InvalidHandle"))

  describe "the kernel requests a client answers" do
    it "refuses one naming another attempt, and one arriving after the invocation" do
      result <- liftEffect (Ref.new "")
      seen <- withSession
        ( "const guest = async (p) => { note(answerOf(await kernel(p.attempt + 1, d('BeginTransaction'))));"
            <> " onPing = async () => note(answerOf(await kernel(p.attempt, d('BeginTransaction'))));"
            <> " return returned(await answerOne(p.attempt)); };"
        )
        \session -> do
          b <- running session 1
          liftEffect (Ref.write (endedAs b) result)
          _ <- node (Client.ping session)
          pure unit
      liftEffect (Ref.read result) >>= shouldEqual "Ended Committed"
      seen `shouldEqual` [ "protocolError kindUnexpected", "protocolError kindUnexpected" ]

    it "refuses one arriving before ready as unexpected, before reading its payload" do
      seen <- withSession
        ( "onHello = async () => note(answerOf(await ask('kernel', { attempt: 'not one' })));"
            <> " const guest = async (p) => returned(await answerOne(p.attempt));"
        )
        \_ -> pure unit
      seen `shouldEqual` [ "protocolError kindUnexpected" ]

    it "refuses one where kernel is not in force, before reading its payload, whatever runs" do
      result <- liftEffect (Ref.new "")
      seen <- withSessionOffering [ "modules", "invoke" ]
        ( "const guest = async (p) => { note(answerOf(await kernel(p.attempt, d('BeginTransaction'))));"
            <> " note(answerOf(await ask('kernel', { attempt: 'not one' })));"
            <> " return failed('kernelNotInForce'); };"
        )
        \session -> do
          b <- running session 1
          liftEffect (Ref.write (endedAs b) result)
      liftEffect (Ref.read result) >>= shouldEqual "InvocationFailed KernelNotInForce"
      seen `shouldEqual` [ "protocolError capabilityNotInForce", "protocolError capabilityNotInForce" ]

    it "runs two guests one after the other, neither answering the other's requests" do
      results <- liftEffect (Ref.new [])
      seen <- withSession
        "const guest = async (p) => { note('start ' + p.attempt); const e = await answerOne(p.attempt); note('end ' + p.attempt); return returned(e); };"
        \session -> do
          first <- forkAff (running session 1)
          second <- forkAff (running session 2)
          one <- joinFiber first
          two <- joinFiber second
          liftEffect (Ref.write [ endedAs one, endedAs two ] results)
      liftEffect (Ref.read results) >>= shouldEqual [ "Ended Committed", "Ended Committed" ]
      seen `shouldEqual` [ "start 1", "end 1", "start 2", "end 2" ]

    it "wraps a failure of the invocation, and a refusal of it, leaving the attempt open" do
      result <- liftEffect (Ref.new [])
      _ <- withSession
        "const guest = async (p) => failed('noSuchModule');"
        \session -> do
          b <- running session 1
          liftEffect (Ref.write [ endedAs b ] result)
      liftEffect (Ref.read result) >>= shouldEqual [ "InvocationFailed NoSuchModule" ]
      invalid <- liftEffect (Ref.new "")
      _ <- withSession
        "const guest = async (p) => ({ kind: 'protocolError', payload: { code: 'attemptNotAbove', detail: '' } });"
        \session -> do
          b <- running session 1
          liftEffect (Ref.write (endedAs b) invalid)
      liftEffect (Ref.read invalid) >>= shouldEqual "RequestRejected attemptNotAbove"

  describe "a run cancelled" do
    it "stops the guest, rolls the attempt back traced, and leaves the session to be used" do
      result <- liftEffect (Ref.new Nothing)
      pinged <- liftEffect (Ref.new false)
      _ <- withSession
        "const guest = async (p) => { await cancelArrived; return failed('cancelled'); };"
        \session -> do
          token <- liftEffect (newCancellation (Milliseconds 1000.0))
          run <- forkAff (runningWith token session 1)
          delay (Milliseconds 100.0)
          liftEffect (cancel token)
          b <- joinFiber run
          liftEffect (Ref.write (Just b) result)
          node (Client.ping session) >>= case _ of
            Right _ -> liftEffect (Ref.write true pinged)
            Left _ -> pure unit
      liftEffect (Ref.read result) >>= case _ of
        Just (Cancelled s health) -> do
          health `shouldEqual` Reusable
          Array.any cancelledEvent s.retained.trace `shouldEqual` true
        Just other -> fail ("ended otherwise: " <> endedAs other)
        Nothing -> fail "no result"
      liftEffect (Ref.read pinged) >>= shouldEqual true

    it "answers abandoned a command asked after the cancel" do
      result <- liftEffect (Ref.new "")
      seen <- withSession
        "const guest = async (p) => { await cancelArrived; note(answerOf(await kernel(p.attempt, d('BeginTransaction')))); return failed('cancelled'); };"
        \session -> do
          token <- liftEffect (newCancellation (Milliseconds 1000.0))
          run <- forkAff (runningWith token session 1)
          delay (Milliseconds 100.0)
          liftEffect (cancel token)
          b <- joinFiber run
          liftEffect (Ref.write (endedAs b) result)
      liftEffect (Ref.read result) >>= shouldEqual "Cancelled Reusable"
      seen `shouldEqual` [ "abandoned" ]

    it "withdraws a run still waiting for the session, touching neither the session nor the run ahead" do
      results <- liftEffect (Ref.new [])
      seen <- withSession
        ( "let release; const released = new Promise((r) => { release = r; }); onPing = async () => release();"
            <> " const guest = async (p) => { note('start ' + p.attempt); await released; return returned(await answerOne(p.attempt)); };"
        )
        \session -> do
          ahead <- forkAff (running session 1)
          delay (Milliseconds 100.0)
          token <- liftEffect (newCancellation (Milliseconds 100.0))
          behind <- forkAff (runningWith token session 2)
          delay (Milliseconds 100.0)
          liftEffect (cancel token)
          withdrawn <- joinFiber behind
          -- the run ahead is still in flight, and goes on once released
          _ <- node (Client.ping session)
          finished <- joinFiber ahead
          liftEffect (Ref.write [ endedAs withdrawn, endedAs finished ] results)
      liftEffect (Ref.read results) >>= shouldEqual [ "Cancelled Reusable", "Ended Committed" ]
      seen `shouldEqual` [ "start 1" ]

    it "loses the session where cancelled is answered with a payload" do
      s <- liftEffect ({ stdout: _, stderr: _ } <$> Ref.new "" <*> Ref.new "")
      node (Client.open (launch s "onCancel = async (m) => send({ kind: 'cancelled', replyTo: m.id, payload: { extra: 1 } }); const guest = async (p) => new Promise(() => {});")) >>= case _ of
        Left failure -> fail (show failure)
        Right session -> node (Client.cancel session 1) >>= case _ of
          Left (Client.SessionLost _) -> pure unit
          other -> fail ("taken as " <> show other)

    it "ends the session where the invocation does not stop within the grace, or the cancel is refused" do
      for_'
        [ "const guest = async (p) => new Promise(() => {});"
        , "onCancel = async (m) => send({ kind: 'protocolError', replyTo: m.id, payload: { code: 'kindUnknown', detail: '' } }); const guest = async (p) => new Promise(() => {});"
        ]
        \guest -> do
          s <- liftEffect ({ stdout: _, stderr: _ } <$> Ref.new "" <*> Ref.new "")
          node (Client.open (launch s guest)) >>= case _ of
            Left failure -> fail (show failure)
            Right session -> do
              token <- liftEffect (newCancellation (Milliseconds 200.0))
              run <- forkAff (runningWith token session 1)
              delay (Milliseconds 100.0)
              liftEffect (cancel token)
              b <- joinFiber run
              endedAs b `shouldEqual` "Cancelled Replace"

    it "keeps an attempt the guest finished, or the host ended, before the cancel took hold" do
      finished <- liftEffect (Ref.new "")
      _ <- withSession
        "const guest = async (p) => { const e = await answerOne(p.attempt); await cancelArrived; return returned(e); };"
        \session -> do
          token <- liftEffect (newCancellation (Milliseconds 1000.0))
          run <- forkAff (runningWith token session 1)
          delay (Milliseconds 200.0)
          liftEffect (cancel token)
          b <- joinFiber run
          liftEffect (Ref.write (endedAs b) finished)
      liftEffect (Ref.read finished) >>= shouldEqual "Ended Committed"
      rejected <- liftEffect (Ref.new "")
      _ <- withSession
        "const guest = async (p) => { await throwing(p.attempt); await cancelArrived; return failed('cancelled'); };"
        \session -> do
          token <- liftEffect (newCancellation (Milliseconds 1000.0))
          run <- forkAff (runningWith token session 1)
          delay (Milliseconds 200.0)
          liftEffect (cancel token)
          b <- joinFiber run
          liftEffect (Ref.write (endedAs b) rejected)
      liftEffect (Ref.read rejected) >>= \r -> r `shouldSatisfy` String.contains (String.Pattern "Ended (Rejected")

  describe "settling a run" do
    it "halts an attempt the invocation left open as the defect its failure is, keeping the session unless it was lost" do
      case job of
        Left err -> fail err
        Right j -> case openConversation env j.id j.state of
          OpenStopped attempt _ -> fail (show attempt)
          Opened c -> do
            let
              failed reason = InvocationFailed { reason, detail: "d" } c
              exit code = { code: Just code, signal: Nothing, error: Nothing }
              settled b = case settle { budget: 77 } b of
                Settled attempt s health -> Tuple (Array.any abandonedEvent s.retained.trace) (show attempt <> " " <> show health)
                Settle.Cancelled _ health -> Tuple false ("Cancelled " <> show health)
            for_'
              [ Tuple (failed Fault) "SynthesizerFaulted"
              , Tuple (failed BudgetExhausted) "SynthesizerExhausted"
              , Tuple (failed (NotAToken ClassInt)) "GuestValueOutsideContract"
              , Tuple (failed (CommandNotEncodable ClassClosure)) "GuestValueOutsideContract"
              , Tuple (failed NoSuchModule) "GuestSessionUnprepared"
              , Tuple (failed KernelNotInForce) "GuestSessionUnprepared"
              , Tuple (RequestRejected { code: "attemptNotAbove", detail: "" } c) "GuestRequestRejected"
              ]
              \(Tuple b name) -> do
                let Tuple traced text = settled b
                traced `shouldEqual` true
                text `shouldSatisfy` String.contains (String.Pattern name)
                text `shouldSatisfy` String.contains (String.Pattern "Reusable")
            for_'
              [ Tuple (SessionLost (ExitedUnannounced (exit 3)) c) "InterpreterDefect"
              , Tuple (SessionLost (ExitedUnannounced (exit 1)) c) "GuestSessionBroke"
              , Tuple (failed Abandoned) "GuestSessionBroke"
              ]
              \(Tuple b name) -> do
                let Tuple _ text = settled b
                text `shouldSatisfy` String.contains (String.Pattern name)
                text `shouldSatisfy` String.contains (String.Pattern "Replace")
            case settle { budget: 77 } (failed BudgetExhausted) of
              Settled (Halted (SynthesizerExhausted _ budget)) _ _ -> budget `shouldEqual` 77
              _ -> fail "not halted as exhausted"

abandonedEvent :: TraceEvent -> Boolean
abandonedEvent = case _ of
  AttemptAbandoned _ -> true
  _ -> false

cancelledEvent :: TraceEvent -> Boolean
cancelledEvent = case _ of
  AttemptCancelled _ -> true
  _ -> false

for_' :: forall a. Array a -> (a -> Aff Unit) -> Aff Unit
for_' xs f = void (Array.foldM (\_ x -> f x) unit xs)
