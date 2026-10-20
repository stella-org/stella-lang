-- | Loading modules into a session and applying guest functions to tokens.
-- |
-- | What is asserted is what a client sees: the answer to each request, the order
-- | answers come in, and how the process ended. The guests are built from
-- | `fixtures/source/guests/session-guest` and `fixtures/source/common-lib/slow-loud`,
-- | beside the modules of the `steam run` tests, and two `.dmo`s are written by hand
-- | for states no compiler produces.
module Test.E2E.SessionGuest (spec) where

import Prelude

import Prim as P

import Data.Argonaut.Core (Json, fromNumber, fromString, stringify, fromObject)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.String as String
import Data.Tuple (Tuple(..))
import Effect.Aff (Aff, Milliseconds(..), delay, forkAff, joinFiber)
import Effect.Class (liftEffect)
import Effect.Ref as Ref
import Foreign.Object (Object)
import Foreign.Object as Object
import Node.Buffer as Buffer
import Node.FS.Aff as FS
import Stella.CLI.Session.Client (ClientFailure(..), RequestFailure(..), Session)
import Stella.CLI.Session.Client as Client
import Stella.CLI.Session.Guest (GlobalName, InvocationFailure, InvocationReason(..), LoadFailure, LoadStage(..), Token, ValueClass(..), encodeInvoke, encodeLoad)
import Stella.CLI.Session.Protocol (Hello, closeKind)
import Stella.Compiler.Bytecode (Dmo, encode)
import Stella.Compiler.Bytecode.Instr (ConstIx(..), ForeignIx(..), FuncIx(..), Instr(..), PrimIx(..), Reg(..), Tail(..))
import Stella.Compiler.Bytecode.Module (Constant(..), GlobalInit(..))
import Stella.Compiler.MiddleEnd.Rep (Rep(..))
import Stella.Compiler.Primitive (PrimOp(..))
import Stella.Compiler.TypedCore (Ident(..), ModuleName(..), Qualified(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual, shouldSatisfy)
import E2E.Build (Sources, builtFrom)
import Data.Foldable (for_)
import Test.E2E.Command (bugModule, dir, manifestPath, pathOf, requiring, writeModules)
import Test.E2E.Command as Command
import Test.E2E.Session (Streams, close', hello, node, open', opened, ping', request', steamWith, streams)
import Test.E2E.SlowLoud (slowLoud, writeSlowLoud)

-- The guests -----------------------------------------------------------------------------

-- | `OpaqueGuest.fresh`, which hands back a new array: an opaque value, and not a
-- | token.
opaqueGuest :: Dmo
opaqueGuest = bugModule
  { name = ModuleName "OpaqueGuest"
  , imports = []
  , constants = [ CInt 2 ]
  , foreignRefs = []
  , prims = [ ArrayUnsafeNew ]
  , functions =
      [ { nparams: 1
        , regs: Array.replicate 3 RepVal
        , captures: []
        , joins: []
        , body:
            { code: [ LOADK (Reg 1) (ConstIx 0), PRIM (Reg 2) (PrimIx 0) [ Reg 1 ] ]
            , tail: RET (Reg 2)
            }
        }
      ]
  , globals = [ { name: Qualified (ModuleName "OpaqueGuest") (Ident "fresh"), init: GFunc (FuncIx 0) } ]
  }

-- | `BugGuest.boom`, which builds a `bind` whose first argument is an `Int` when it
-- | is applied: a state no compiler produces, reached while an invocation runs.
bugGuest :: Dmo
bugGuest = bugModule
  { name = ModuleName "BugGuest"
  , functions =
      [ { nparams: 1
        , regs: Array.replicate 4 RepVal
        , captures: []
        , joins: []
        , body:
            { code:
                [ LOADK (Reg 1) (ConstIx 0)
                , CLOS (Reg 2) (FuncIx 1) []
                , FFI (Reg 3) (ForeignIx 1) [ Reg 1, Reg 2 ]
                ]
            , tail: RET (Reg 3)
            }
        }
      , { nparams: 1
        , regs: [ RepVal ]
        , captures: []
        , joins: []
        , body: { code: [], tail: RET (Reg 0) }
        }
      ]
  , globals = [ { name: Qualified (ModuleName "BugGuest") (Ident "boom"), init: GFunc (FuncIx 0) } ]
  }

-- | What the guests are loaded beside: the modules of the `steam run` tests, `Guest`,
-- | and `Slow` and `Loud`.
type Fixture = { command :: Command.Fixture, guest :: P.Array Dmo, hosts :: P.Array Dmo }

fixtureOf :: Sources -> Either P.String Fixture
fixtureOf sources = do
  command <- Command.compiled sources
  guest <- builtFrom sources [ "guests/session-guest" ]
  hosts <- slowLoud sources
  pure { command, guest, hosts }

writeGuests :: Fixture -> Aff Unit
writeGuests made = do
  writeModules made.command
  for_ made.guest \dmo -> write dmo
  write opaqueGuest
  write bugGuest
  writeSlowLoud dir made.hosts
  where
  write dmo = case dmo.name, encode dmo of
    ModuleName name, Right bytes -> do
      buffer <- liftEffect (Buffer.fromArray bytes)
      FS.writeFile (pathOf name) buffer
    ModuleName name, Left err -> fail ("could not encode " <> name <> ": " <> show err)

-- Talking to a session ---------------------------------------------------------------------

both :: Hello
both = hello { offers = [ "modules", "invoke" ] }

load' :: Session -> P.String -> Aff (Either RequestFailure (Either LoadFailure P.String))
load' session path = node (Client.load session path)

-- | Apply a global to tokens as that attempt.
invoke' :: Session -> P.Int -> GlobalName -> P.Array Token -> Aff (Either RequestFailure (Either InvocationFailure Token))
invoke' session attempt name arguments = node (Client.invoke session { global: name, arguments, attempt, budget: 1000000 })

token :: Token
token = Object.fromFoldable
  [ Tuple "session" (fromNumber 1.0), Tuple "slot" (fromNumber 7.0), Tuple "note" (fromString "星") ]

text :: Object Json -> P.String
text = stringify <<< fromObject

global :: P.String -> P.String -> GlobalName
global m name = { module: m, name }

-- | Wait until the process has written that to standard error.
waitFor :: Streams -> P.String -> Aff Unit
waitFor s mark = go 500
  where
  go n = do
    err <- liftEffect (Ref.read s.stderr)
    if String.contains (String.Pattern mark) err then pure unit
    else if n <= 0 then fail ("never written: " <> mark)
    else delay (Milliseconds 10.0) *> go (n - 1)

-- | Load these, in order, each expected to load.
loadAll :: Session -> P.Array P.String -> Aff Unit
loadAll session names = void $ Array.foldM
  ( \_ name -> load' session (pathOf name) >>= case _ of
      Right (Right _) -> pure unit
      other -> fail ("did not load " <> name <> ": " <> show (map (map (const unit)) other))
  )
  unit
  names

stageOf :: Either RequestFailure (Either LoadFailure P.String) -> Maybe LoadStage
stageOf = case _ of
  Right (Left f) -> Just f.stage
  _ -> Nothing

reasonOf :: Either RequestFailure (Either InvocationFailure Token) -> Maybe InvocationReason
reasonOf = case _ of
  Right (Left f) -> Just f.reason
  _ -> Nothing

codeOf :: forall a. Either RequestFailure a -> Maybe P.String
codeOf = case _ of
  Left (RequestRefused e) -> Just e.code
  _ -> Nothing

-- Cases ---------------------------------------------------------------------------------------

spec :: Sources -> Spec Unit
spec sources = describe "steam session, loading and invoking" $ requiring (fixtureOf sources) \made -> do
  it "writes the fixture" do
    writeGuests made

  describe "loading" do
    it "loads modules over Base alone with no manifest, and names each" do
      s <- streams
      opened (steamWith [] s both) \session -> do
        (Client.ready session).capabilities `shouldEqual` [ "modules", "invoke" ]
        load' session (pathOf "Base.String") >>= shouldEqual (Right (Right "Base.String"))
        load' session (pathOf "Guest") >>= shouldEqual (Right (Right "Guest"))
        close' session >>= shouldEqual (Right unit)

    it "refuses a module declaring a host foreign when no manifest was given" do
      s <- streams
      opened (steamWith [] s both) \session -> do
        stageOf <$> load' session (pathOf "Host") >>= shouldEqual (Just Refused)
        close' session >>= shouldEqual (Right unit)

    it "loads a module whose foreign a manifest supplies" do
      s <- streams
      opened (steamWith [ "--manifest", manifestPath "good" ] s both) \session -> do
        load' session (pathOf "Host") >>= shouldEqual (Right (Right "Host"))
        close' session >>= shouldEqual (Right unit)

    it "answers each stage a load fails at, and goes on" do
      s <- streams
      opened (steamWith [ "--manifest", manifestPath "missing-module" ] s both) \session -> do
        stageOf <$> load' session (pathOf "Nowhere") >>= shouldEqual (Just Unreadable)
        stageOf <$> load' session (pathOf "Garbage") >>= shouldEqual (Just NotBytecode)
        stageOf <$> load' session (pathOf "Host") >>= shouldEqual (Just Foreigns)
        stageOf <$> load' session (pathOf "BadInit") >>= shouldEqual (Just Refused)
        loadAll session [ "Base.String" ]
        stageOf <$> load' session (pathOf "BadInit") >>= shouldEqual (Just Initialization)
        ping' session >>= shouldEqual (Right unit)
        close' session >>= shouldEqual (Right unit)

    it "leaves nothing of a module whose load failed after its foreigns were reached" do
      s <- streams
      opened (steamWith [ "--manifest", manifestPath "refusing" ] s both) \session -> do
        stageOf <$> load' session (pathOf "Host") >>= shouldEqual (Just Initialization)
        reasonOf <$> invoke' session 1 (global "Host" "greet") [ token ]
          >>= shouldEqual (Just NoSuchModule)
        -- and the name is free: a failed load committed no module under it
        stageOf <$> load' session (pathOf "Host") >>= shouldEqual (Just Initialization)
        close' session >>= shouldEqual (Right unit)

    it "runs loads sent without waiting in the order they arrived, initializing once" do
      s <- streams
      opened (steamWith [] s both) \session -> do
        first <- forkAff (load' session (pathOf "Base.String"))
        second <- forkAff (load' session (pathOf "Guest"))
        again <- forkAff (load' session (pathOf "Guest"))
        joinFiber first >>= shouldEqual (Right (Right "Base.String"))
        joinFiber second >>= shouldEqual (Right (Right "Guest"))
        stageOf <$> joinFiber again >>= shouldEqual (Just Refused)
        close' session >>= shouldEqual (Right unit)

  describe "invoking" do
    it "sees the module a load sent just before it loaded" do
      s <- streams
      opened (steamWith [] s both) \session -> do
        loadAll session [ "Base.String" ]
        loading <- forkAff (load' session (pathOf "Guest"))
        invoking <- forkAff (invoke' session 1 (global "Guest" "identity") [ token ])
        joinFiber loading >>= shouldEqual (Right (Right "Guest"))
        map (map text) <$> joinFiber invoking >>= shouldEqual (Right (Right (text token)))
        close' session >>= shouldEqual (Right unit)

    it "hands back the token a guest returns, as the same JSON" do
      s <- streams
      opened (steamWith [] s both) \session -> do
        loadAll session [ "Base.String", "Guest" ]
        invoke' session 1 (global "Guest" "identity") [ token ] >>= case _ of
          Right (Right back) -> text back `shouldEqual` text token
          other -> fail ("no token came back: " <> show (map (map (const unit)) other))
        close' session >>= shouldEqual (Right unit)

    it "says why it did not return a token, and goes on" do
      s <- streams
      opened (steamWith [] s both) \session -> do
        loadAll session [ "Base.String", "Guest", "OpaqueGuest" ]
        let reason attempt g n = reasonOf <$> invoke' session attempt (global g n) [ token ]
        reason 1 "Nowhere" "identity" >>= shouldEqual (Just NoSuchModule)
        reason 2 "Guest" "nothing" >>= shouldEqual (Just NoSuchGlobal)
        reason 3 "Guest" "seven" >>= shouldEqual (Just NotCallable)
        reason 4 "Guest" "faulting" >>= shouldEqual (Just Fault)
        reason 5 "Guest" "constant" >>= shouldEqual (Just (NotAToken ClassInt))
        reason 6 "OpaqueGuest" "fresh" >>= shouldEqual (Just (NotAToken ClassOpaque))
        ping' session >>= shouldEqual (Right unit)
        close' session >>= shouldEqual (Right unit)

  describe "what a session will not do" do
    it "refuses load and invoke where the capability is not in force, whatever the payload" do
      s <- streams
      opened (steamWith [] s hello) \session -> do
        codeOf <$> request' session "load" (encodeLoad (pathOf "Guest"))
          >>= shouldEqual (Just "capabilityNotInForce")
        codeOf <$> request' session "invoke" (encodeInvoke { global: global "Guest" "identity", arguments: [ token ], attempt: 1, budget: 1000000 })
          >>= shouldEqual (Just "capabilityNotInForce")
        codeOf <$> request' session "load" (Object.singleton "path" (fromNumber 5.0))
          >>= shouldEqual (Just "capabilityNotInForce")
        close' session >>= shouldEqual (Right unit)

    it "refuses a payload of another shape as a protocol error, not a failed load" do
      s <- streams
      opened (steamWith [] s both) \session -> do
        codeOf <$> request' session "load" (Object.singleton "path" (fromNumber 5.0))
          >>= shouldEqual (Just "payloadInvalid")
        codeOf <$> request' session "load" (Object.insert "extra" (fromString "") (encodeLoad "x"))
          >>= shouldEqual (Just "payloadInvalid")
        codeOf <$> request' session "invoke" (Object.singleton "arguments" (fromNumber 1.0))
          >>= shouldEqual (Just "payloadInvalid")
        close' session >>= shouldEqual (Right unit)

    it "finishes what arrived before close, and refuses what arrived after it" do
      s <- streams
      opened (steamWith [] s both) \session -> do
        loadAll session [ "Base.String" ]
        loading <- forkAff (load' session (pathOf "Guest"))
        invoking <- forkAff (invoke' session 1 (global "Guest" "identity") [ token ])
        closing <- forkAff (request' session closeKind Object.empty)
        late <- forkAff (request' session "load" (Object.singleton "path" (fromNumber 5.0)))
        latePing <- forkAff (ping' session)
        joinFiber loading >>= shouldEqual (Right (Right "Guest"))
        map (map text) <$> joinFiber invoking >>= shouldEqual (Right (Right (text token)))
        map _.kind <$> joinFiber closing >>= shouldEqual (Right "closed")
        codeOf <$> joinFiber late >>= shouldEqual (Just "kindUnexpected")
        codeOf <$> joinFiber latePing >>= shouldEqual (Just "kindUnexpected")

    it "initializes a module queued behind a slow one, the channel kept" do
      s <- streams
      opened (steamWith [ "--manifest", manifestPath "slow-loud" ] s both) \session -> do
        slow <- forkAff (load' session (pathOf "Slow"))
        loud <- forkAff (load' session (pathOf "Loud"))
        joinFiber slow >>= shouldEqual (Right (Right "Slow"))
        joinFiber loud >>= shouldEqual (Right (Right "Loud"))
        close' session >>= shouldEqual (Right unit)
        err <- liftEffect (Ref.read s.stderr)
        err `shouldSatisfy` String.contains (String.Pattern "shouted")

    it "finishes the load running when the channel is lost, and starts none queued" do
      s <- streams
      opened (steamWith [ "--manifest", manifestPath "slow-loud" ] s both) \session -> do
        -- `Slow` is running: its host module has been reached and is still waiting
        _ <- forkAff (load' session (pathOf "Slow"))
        waitFor s "slow reached"
        -- `Loud` is admitted behind it: a ping sent after it is answered only once
        -- the receiver has taken both, in the order they arrived
        _ <- forkAff (load' session (pathOf "Loud"))
        ping' session >>= shouldEqual (Right unit)
        err <- liftEffect (Ref.read s.stderr)
        err `shouldSatisfy` (not <<< String.contains (String.Pattern "slow ready"))
        -- and then the channel goes
        exit <- node (Client.abandon session)
        exit.code `shouldEqual` Just 1
        after <- liftEffect (Ref.read s.stderr)
        after `shouldSatisfy` String.contains (String.Pattern "waited")
        after `shouldSatisfy` (not <<< String.contains (String.Pattern "shouted"))
        after `shouldSatisfy` String.contains (String.Pattern "without `close`")

    it "ends with status 3 on a defect of the interpreter, answering nothing more" do
      s <- streams
      opened (steamWith [] s both) \session -> do
        loadAll session [ "Base.IO", "BugGuest" ]
        invoke' session 1 (global "BugGuest" "boom") [ token ] >>= case _ of
          Left (SessionLost (ExitedUnannounced exit)) -> exit.code `shouldEqual` Just 3
          other -> fail ("the defect was answered: " <> show (map (map (const unit)) other))
        ping' session >>= case _ of
          Left (SessionLost _) -> pure unit
          other -> fail ("the session answered after a defect: " <> show other)
        err <- liftEffect (Ref.read s.stderr)
        err `shouldSatisfy` String.contains (String.Pattern "Internal error in the interpreter")

    it "ends with status 3 on a defect reached while a module initializes" do
      s <- streams
      opened (steamWith [] s both) \session -> do
        loadAll session [ "Base.IO" ]
        load' session (pathOf "BugInit") >>= case _ of
          Left (SessionLost (ExitedUnannounced exit)) -> exit.code `shouldEqual` Just 3
          other -> fail ("the defect was answered: " <> show (map (map (const unit)) other))

    it "does not start with a manifest that does not read, or names another target" do
      let
        notStarted m = do
          s <- streams
          open' (steamWith [ "--manifest", manifestPath m ] s both) >>= case _ of
            Left (Client.OpenFailed (ExitedUnannounced exit)) -> exit.code `shouldEqual` Just 1
            other -> fail ("a session opened with the manifest " <> m <> ": " <> show (map (const unit) other))
      notStarted "garbage"
      notStarted "other-target"
