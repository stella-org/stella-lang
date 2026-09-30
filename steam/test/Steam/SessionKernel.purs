-- | A session answering a guest's commands through the client: the trusted
-- | `Stella.Elab` a session installs as it opens, the `kernel` request an invocation
-- | makes for each command, and what the client's answers come to.
-- |
-- | The client here is written on the peer directly, answering `kernel` requests as
-- | each test says. The guest is a Core module compiled against `Stella.Elab`, with
-- | one `.dmo` written by hand for a command no compiler produces.
module Test.Steam.SessionKernel (spec) where

import Prelude

import Prim as P

import Data.Argonaut.Core (Json, fromBoolean, fromNumber, fromObject, fromString, jsonNull)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Foldable (traverse_)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Effect.Aff (Aff, Milliseconds(..), delay, forkAff, joinFiber)
import Effect.Class (liftEffect)
import Effect.Exception (throw)
import Effect.Ref as Ref
import Foreign.Object (Object)
import Foreign.Object as Object
import Node.Buffer as Buffer
import Node.FS.Aff as FS
import Stella.CLI.Effect.Process (Child)
import Stella.CLI.Session.Frame (renderJson)
import Stella.CLI.Session.Guest (InvocationReason(..), ValueClass(..), decodeInvocationFailed, decodeReturned, encodeCancel, encodeInvoke, encodeLoad)
import Stella.CLI.Session.Kernel (KernelCall, abandonedKind, answeredKind, decodeKernel, encodeAbandoned, encodeAnswered, kernelKind)
import Stella.CLI.Session.Peer (Peer, Reply)
import Stella.CLI.Session.Peer as Peer
import Stella.CLI.Session.ProtocolError (decodeProtocolError, protocolErrorKind)
import Stella.CLI.Session.Protocol (encodeHello, helloKind, pingKind)
import Stella.CLI.Session.Value (WireValue(..), encodeValue)
import Stella.Compiler.Bytecode (Dmo, encode, lower)
import Stella.Compiler.Bytecode.Instr (FuncIx(..), Instr(..), JoinName(..), KeyIx(..), OpIx(..), Reg(..), Tail(..))
import Stella.Compiler.Bytecode.Module (GlobalInit(..), Key(..))
import Stella.Compiler.Elaborate.Protocol.Guest (commandOp, elabModule, guestModule, handleTy, kernelEffect, withGuest)
import Stella.Compiler.Interface (importsOf, interfaceOf, noImports)
import Stella.Compiler.MiddleEnd (translate)
import Stella.Compiler.MiddleEnd.Rep (Rep(..))
import Stella.Compiler.TypedCore (DecisionTree(..), Decl(..), Expr(..), Ident(..), Module, ModuleName(..), Occurrence(..), Qualified(..), RowEntry(..), RowKey(..), TyName(..), Type(..), declareAnnotated, monoScheme, primSignature)
import Stella.Compiler.TypedCore.Prim (fn)
import Steam.CLI.Elaboration (TakenAnswer(..), prepare, takeAnswer)
import Steam.Foreign (emptyTable)
import Steam.Load (emptyStore, noIdentities)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)
import Test.Steam.Command (bugModule, pathOf)
import Test.Steam.Session (Streams, hello, steamChild, streams)

-- The guests ------------------------------------------------------------------------------

elab :: P.String -> Qualified Ident
elab c = Qualified elabModule (Ident c)

handle :: Type
handle = TCon handleTy []

answerTy :: Type
answerTy = TCon (Qualified elabModule (TyName "GuestAnswer")) []

kernelRow :: Type
kernelRow = TRowExtend (RowEffectEntry kernelEffect []) TRowEmpty

-- | `Synth.synth`: asks for its goal's type, asks for the weak head normal form of
-- | the handle the first answer carries, and returns the handle the second answer
-- | carries. Where an answer carries no handle it returns the goal.
synthModule :: Module Unit
synthModule =
  { annotation: unit
  , name: ModuleName "Synth"
  , imports: [ elabModule ]
  , exports: []
  , decls:
      [ DeclNonRec unit
          { name: Ident "synth"
          , scheme: monoScheme (fn handle kernelRow handle)
          , value: Lam unit goal handle
              ( asking (Ident "first") (observe "GoalType" (Var unit goal))
                  \found -> asking (Ident "second") (observe "Whnf" (Var unit found)) (Var unit)
              )
          , attributes: []
          }
      ]
  }
  where
  goal = Ident "goal"

  -- a constructor applied inside the kernel row, constructor arrows being pure
  app c x = App unit (OpenEff unit kernelRow (Global unit (elab c) [])) x

  observe request h = app "Kernel" (app "ObserveRequest" (app request h))

  -- perform the command, and go on with the handle its answer carries
  asking name command k =
    Let unit name answerTy (Perform unit (EffectKey kernelEffect) commandOp [] command)
      ( Case unit [ Var unit name ]
          ( SwitchCtor (OccScrutinee 0)
              [ { ctor: elab "Returned"
                , tree: SwitchCtor returned
                    [ { ctor: elab "HandleAnswer"
                      , tree: Bind carried (OccField returned (elab "HandleAnswer") 0) (Leaf (k carried))
                      }
                    ]
                    (Just (Leaf (Var unit goal)))
                }
              ]
              (Just (Leaf (Var unit goal)))
          )
      )
    where
    returned = OccField (OccScrutinee 0) (elab "Returned") 0
    carried = Ident ("in " <> show name)

compiledSynth :: Either P.String Dmo
compiledSynth = do
  elabDeclared <- declared (withGuest primSignature) guestModule
  elabMid <- translated noImports guestModule elabDeclared
  imports <- case importsOf [ interfaceOf elabMid.module ] of
    Left err -> Left (show err)
    Right imports -> Right imports
  synthDeclared <- declared elabDeclared.signature synthModule
  mid <- translated imports synthModule synthDeclared
  case lower mid of
    Left err -> Left (show err)
    Right out -> Right out.dmo
  where
  declared signature m = case declareAnnotated signature m of
    Left err -> Left (show err.error)
    Right d -> Right d
  translated imports m d = case translate imports m d of
    Left err -> Left (show err)
    Right mid -> Right mid

-- | `Unencodable.ask`, which performs the command with a closure for its argument:
-- | a command no typed guest can build.
unencodable :: Dmo
unencodable = bugModule
  { name = ModuleName "Unencodable"
  , imports = [ elabModule ]
  , constants = []
  , keys = [ KEffect kernelEffect ]
  , ops = [ commandOp ]
  , foreignRefs = []
  , functions =
      [ { nparams: 1
        , regs: Array.replicate 3 RepVal
        , captures: []
        , joins: []
        , body:
            { code: [ CLOS (Reg 1) (FuncIx 1) [], PERF (Reg 2) (KeyIx 0) (OpIx 0) (Reg 1) ]
            , tail: RET (Reg 2)
            }
        }
      , { nparams: 1, regs: [ RepVal ], captures: [], joins: [], body: { code: [], tail: RET (Reg 0) } }
      ]
  , globals = [ { name: Qualified (ModuleName "Unencodable") (Ident "ask"), init: GFunc (FuncIx 0) } ]
  }

-- | `Loop.spin`, which jumps to itself for good: a guest that never returns.
looping :: Dmo
looping = bugModule
  { name = ModuleName "Loop"
  , imports = []
  , constants = []
  , foreignRefs = []
  , functions =
      [ { nparams: 1
        , regs: [ RepVal ]
        , captures: []
        , joins: [ { name: JoinName 0, params: [ Reg 0 ], body: { code: [], tail: JMP (JoinName 0) [ Reg 0 ] } } ]
        , body: { code: [], tail: JMP (JoinName 0) [ Reg 0 ] }
        }
      ]
  , globals = [ { name: Qualified (ModuleName "Loop") (Ident "spin"), init: GFunc (FuncIx 0) } ]
  }

-- | A module under a name of its own, with nothing in it.
named :: P.String -> Dmo
named name = bugModule
  { name = ModuleName name
  , imports = []
  , constants = []
  , foreignRefs = []
  , functions = []
  , globals = []
  }

writeGuests :: Aff Unit
writeGuests = do
  case compiledSynth of
    Left err -> fail ("Synth did not compile: " <> err)
    Right synth -> write "Synth" synth
  write "Unencodable" unencodable
  write "Loop" looping
  for [ "Stella", "Stella.Elab", "Stella.Other", "Stellar" ] \name -> write name (named name)
  where
  for xs f = void (Array.foldM (\_ x -> f x) unit xs)
  write name dmo = case encode dmo of
    Left err -> fail ("could not encode " <> name <> ": " <> show err)
    Right bytes -> do
      buffer <- liftEffect (Buffer.fromArray bytes)
      FS.writeFile (pathOf name) buffer

-- Values -----------------------------------------------------------------------------------

tokenNamed :: P.String -> Object Json
tokenNamed name = Object.singleton "handle" (fromString name)

wireOf :: P.String -> P.Array WireValue -> WireValue
wireOf c = WData (elab c)

-- | `Kernel (ObserveRequest (request token))`, as the session writes it.
observed :: P.String -> P.String -> P.String
observed request name = rendered
  (wireOf "Kernel" [ wireOf "ObserveRequest" [ wireOf request [ WToken (tokenNamed name) ] ] ])

-- | `Returned (HandleAnswer token)`.
handleAnswer :: P.String -> Json
handleAnswer name = case encodeValue (wireOf "Returned" [ wireOf "HandleAnswer" [ WToken (tokenNamed name) ] ]) of
  Right json -> json
  Left _ -> jsonNull

rendered :: WireValue -> P.String
rendered v = case encodeValue v of
  Right json -> renderJson json
  Left _ -> "no encoding"

-- The client ------------------------------------------------------------------------------

-- | A session on steam, and the `kernel` requests it has made so far, each as its
-- | attempt and its command's text.
type Raw =
  { peer :: Peer
  , child :: Child
  , asked :: Ref.Ref (P.Array (Tuple P.Int P.String))
  }

-- | How the client answers a `kernel` request.
type Answering = KernelCall -> Aff Peer.Answer

-- | Open a session offering those capabilities, answering `kernel` requests as
-- | told, and load the modules.
session :: Streams -> P.Array P.String -> Answering -> P.Array P.String -> Aff Raw
session s offers answering modules = do
  child <- steamChild s
  asked <- liftEffect (Ref.new [])
  channel <- case child.channel of
    Just channel -> pure channel
    Nothing -> liftEffect (throw "steam did not start")
  peer <- liftEffect $ Peer.start channel
    { request: \incoming -> case decodeKernel incoming.payload of
        Just call | incoming.kind == kernelKind -> do
          liftEffect (Ref.modify_ (_ <> [ Tuple call.attempt (renderJson call.command) ]) asked)
          answering call
        _ -> pure (Peer.answer { kind: "unexpected", payload: Object.empty })
    , notification: \_ -> pure unit
    , failed: \_ -> pure unit
    }
  ready <- Peer.request peer helloKind (encodeHello (hello { offers = offers }))
  map _.kind ready `shouldEqual` Right "ready"
  _ <- Array.foldM (\_ m -> loading peer m) unit modules
  pure { peer, child, asked }
  where
  loading peer m = do
    loaded <- Peer.request peer "load" (encodeLoad (pathOf m))
    map _.kind loaded `shouldEqual` Right "loaded"

every :: P.Array P.String
every = [ "modules", "invoke", "kernel" ]

invoking :: Raw -> P.Int -> P.String -> P.String -> Aff (Either Peer.SessionFailure Reply)
invoking raw = invokingWithin raw 1000000

invokingWithin :: Raw -> P.Int -> P.Int -> P.String -> P.String -> Aff (Either Peer.SessionFailure Reply)
invokingWithin raw budget attempt m g = Peer.request raw.peer "invoke"
  (encodeInvoke { global: { module: m, name: g }, arguments: [ tokenNamed "goal" ], attempt, budget })

cancelling :: Peer -> P.Int -> Aff (Either Peer.SessionFailure Reply)
cancelling peer attempt = Peer.request peer "cancel" (encodeCancel attempt)

-- | What an `invoke` came back with, as far as a test needs it.
data Came
  = TokenBack P.String
  | FailedWith InvocationReason
  | ErrorCode P.String
  | Ended
  | Otherwise P.String

came :: Either Peer.SessionFailure Reply -> Came
came = case _ of
  Left _ -> Ended
  Right reply
    | reply.kind == "returned" -> case decodeReturned reply.payload of
        Just token -> TokenBack (renderJson (fromObject token))
        Nothing -> Otherwise "returned"
    | reply.kind == "invocationFailed" -> case decodeInvocationFailed reply.payload of
        Just failure -> FailedWith failure.reason
        Nothing -> Otherwise "invocationFailed"
    | reply.kind == protocolErrorKind -> case decodeProtocolError reply.payload of
        Just error -> ErrorCode error.code
        Nothing -> Otherwise protocolErrorKind
    | otherwise -> Otherwise reply.kind

answered :: Json -> Aff Peer.Answer
answered json = pure (Peer.answer { kind: answeredKind, payload: encodeAnswered json })

-- | Answer every command with `Returned (HandleAnswer token)`, a new token each time.
handing :: Ref.Ref P.Int -> Answering
handing counter _ = do
  n <- liftEffect (Ref.modify (_ + 1) counter)
  answered (handleAnswer ("h" <> show n))

closeAndWait :: Raw -> Aff (Maybe P.Int)
closeAndWait raw = do
  _ <- Peer.request raw.peer "close" Object.empty
  _.code <$> raw.child.exit

-- | What a violation ends in: the invocation unanswered, and the process's status.
violating :: Streams -> Peer.Answer -> Aff (Tuple Came (Maybe P.Int))
violating s reply = do
  raw <- session s every (\_ -> pure reply) [ "Synth" ]
  result <- invoking raw 1 "Synth" "synth"
  exit <- raw.child.exit
  pure (Tuple (came result) exit.code)

spec :: Spec Unit
spec = describe "steam session, answering a guest's commands" do
  it "writes the guests" writeGuests

  describe "opening" do
    it "installs Stella.Elab before ready, and refuses every module under Stella by name" do
      s <- streams
      -- `Synth` imports `Stella.Elab`, so it loads only where that is installed
      raw <- session s every (\_ -> pure (Peer.answer { kind: "unused", payload: Object.empty })) [ "Synth" ]
      let stageOf reply = map _.kind reply
      for_' [ "Stella", "Stella.Elab", "Stella.Other" ] \m -> do
        refused <- Peer.request raw.peer "load" (encodeLoad (pathOf m))
        stageOf refused `shouldEqual` Right "loadFailed"
      stellar <- Peer.request raw.peer "load" (encodeLoad (pathOf "Stellar"))
      stageOf stellar `shouldEqual` Right "loaded"
      closeAndWait raw >>= shouldEqual (Just 0)

    it "answers nothing a request is answered with before ready, a refusal included" do
      s <- streams
      child <- steamChild s
      channel <- case child.channel of
        Just channel -> pure channel
        Nothing -> liftEffect (throw "steam did not start")
      order <- liftEffect (Ref.new [])
      peer <- liftEffect $ Peer.start channel
        { request: \_ -> pure (Peer.answer { kind: "unused", payload: Object.empty })
        , notification: \_ -> pure unit
        , failed: \_ -> pure unit
        }
      let
        noting kind payload = forkAff do
          reply <- Peer.request peer kind payload
          liftEffect (Ref.modify_ (_ <> [ answeredWith reply ]) order)
      -- sent without waiting: an answer settled on arrival is held behind the
      -- opening, and so is one settled after `close` made the session closing
      sent <- traverse (\(Tuple kind payload) -> noting kind payload)
        [ Tuple helloKind (encodeHello hello)
        , Tuple pingKind Object.empty
        , Tuple "evaluate" Object.empty
        , Tuple helloKind (encodeHello hello)
        , Tuple "load" (encodeLoad (pathOf "Synth"))
        , Tuple "close" Object.empty
        , Tuple pingKind Object.empty
        ]
      traverse_ joinFiber sent
      liftEffect (Ref.read order) >>= shouldEqual
        [ "ready"
        , "pong"
        , "protocolError kindUnknown"
        , "protocolError kindUnexpected"
        , "protocolError capabilityNotInForce"
        , "closed"
        , "protocolError kindUnexpected"
        ]
      _.code <$> child.exit >>= shouldEqual (Just 0)

  describe "a guest's commands" do
    it "asks the client once per command, and the invocation goes on with each answer" do
      s <- streams
      counter <- liftEffect (Ref.new 0)
      raw <- session s every (handing counter) [ "Synth" ]
      result <- invoking raw 1 "Synth" "synth"
      came result `shouldEqual` TokenBack (renderJson (fromObject (tokenNamed "h2")))
      liftEffect (Ref.read raw.asked) >>= shouldEqual
        [ Tuple 1 (observed "GoalType" "goal"), Tuple 1 (observed "Whnf" "h1") ]
      closeAndWait raw >>= shouldEqual (Just 0)

    it "fails the invocation where kernel is not in force, and goes on" do
      s <- streams
      raw <- session s [ "modules", "invoke" ] (\_ -> pure (Peer.answer { kind: "unused", payload: Object.empty })) [ "Synth" ]
      came <$> invoking raw 1 "Synth" "synth" >>= shouldEqual (FailedWith KernelNotInForce)
      liftEffect (Ref.read raw.asked) >>= shouldEqual []
      closeAndWait raw >>= shouldEqual (Just 0)

    it "fails the invocation whose command has no generic value, naming its class" do
      s <- streams
      raw <- session s every (\_ -> pure (Peer.answer { kind: "unused", payload: Object.empty })) [ "Unencodable" ]
      came <$> invoking raw 1 "Unencodable" "ask" >>= shouldEqual (FailedWith (CommandNotEncodable ClassClosure))
      closeAndWait raw >>= shouldEqual (Just 0)

    it "stops the guest where the client abandons the attempt, and answers the next request" do
      s <- streams
      raw <- session s every (\_ -> pure (Peer.answer { kind: abandonedKind, payload: encodeAbandoned })) [ "Synth" ]
      came <$> invoking raw 1 "Synth" "synth" >>= shouldEqual (FailedWith Abandoned)
      liftEffect (Ref.read raw.asked) >>= shouldEqual [ Tuple 1 (observed "GoalType" "goal") ]
      came <$> invoking raw 2 "Synth" "synth" >>= shouldEqual (FailedWith Abandoned)
      closeAndWait raw >>= shouldEqual (Just 0)

  describe "budgets and quanta" do
    it "stops a guest that never returns once its budget is spent, and answers the next request" do
      s <- streams
      counter <- liftEffect (Ref.new 0)
      raw <- session s every (handing counter) [ "Loop", "Synth" ]
      came <$> invokingWithin raw 5000 1 "Loop" "spin" >>= shouldEqual (FailedWith BudgetExhausted)
      came <$> invoking raw 2 "Synth" "synth" >>= shouldEqual (TokenBack (renderJson (fromObject (tokenNamed "h2"))))
      closeAndWait raw >>= shouldEqual (Just 0)

  describe "cancelling" do
    it "stops a running invocation at the next stretch, and answers the next request" do
      s <- streams
      counter <- liftEffect (Ref.new 0)
      raw <- session s every (handing counter) [ "Loop", "Synth" ]
      running <- forkAff (invokingWithin raw 2147483647 1 "Loop" "spin")
      delay (Milliseconds 100.0)
      map _.kind <$> cancelling raw.peer 1 >>= shouldEqual (Right "cancelled")
      came <$> joinFiber running >>= shouldEqual (FailedWith Cancelled)
      came <$> invoking raw 2 "Synth" "synth" >>= shouldEqual (TokenBack (renderJson (fromObject (tokenNamed "h2"))))
      closeAndWait raw >>= shouldEqual (Just 0)

    it "stops a queued invocation before it begins" do
      s <- streams
      counter <- liftEffect (Ref.new 0)
      raw <- session s every (handing counter) [ "Loop", "Synth" ]
      running <- forkAff (invokingWithin raw 2147483647 1 "Loop" "spin")
      queued <- forkAff (invoking raw 2 "Synth" "synth")
      delay (Milliseconds 100.0)
      map _.kind <$> cancelling raw.peer 2 >>= shouldEqual (Right "cancelled")
      map _.kind <$> cancelling raw.peer 1 >>= shouldEqual (Right "cancelled")
      came <$> joinFiber running >>= shouldEqual (FailedWith Cancelled)
      came <$> joinFiber queued >>= shouldEqual (FailedWith Cancelled)
      -- the queued one asked nothing: it never began
      liftEffect (Ref.read raw.asked) >>= shouldEqual []
      closeAndWait raw >>= shouldEqual (Just 0)

    it "leaves alone an attempt neither queued nor running: one to come, and one done" do
      s <- streams
      counter <- liftEffect (Ref.new 0)
      raw <- session s every (handing counter) [ "Synth" ]
      map _.kind <$> cancelling raw.peer 7 >>= shouldEqual (Right "cancelled")
      came <$> invoking raw 7 "Synth" "synth" >>= shouldEqual (TokenBack (renderJson (fromObject (tokenNamed "h2"))))
      map _.kind <$> cancelling raw.peer 7 >>= shouldEqual (Right "cancelled")
      came <$> invoking raw 8 "Synth" "synth" >>= shouldEqual (TokenBack (renderJson (fromObject (tokenNamed "h4"))))
      closeAndWait raw >>= shouldEqual (Just 0)

    it "fails as cancelled an invocation cancelled while its answer was awaited, whatever the client then answers" do
      s <- streams
      holder <- liftEffect (Ref.new Nothing)
      let
        answering call = do
          peer <- liftEffect (Ref.read holder)
          case peer of
            Just p -> void (cancelling p call.attempt)
            Nothing -> pure unit
          pure (Peer.answer { kind: abandonedKind, payload: encodeAbandoned })
      raw <- session s every answering [ "Synth" ]
      liftEffect (Ref.write (Just raw.peer) holder)
      came <$> invoking raw 1 "Synth" "synth" >>= shouldEqual (FailedWith Cancelled)
      closeAndWait raw >>= shouldEqual (Just 0)

  describe "attempts" do
    it "refuses an attempt not above every one admitted, or out of range, before it begins" do
      s <- streams
      counter <- liftEffect (Ref.new 0)
      raw <- session s every (handing counter) [ "Synth" ]
      came <$> invoking raw 0 "Synth" "synth" >>= shouldEqual (ErrorCode "payloadInvalid")
      came <$> invoking raw 5 "Synth" "synth" >>= shouldEqual (TokenBack (renderJson (fromObject (tokenNamed "h2"))))
      came <$> invoking raw 5 "Synth" "synth" >>= shouldEqual (ErrorCode "attemptNotAbove")
      came <$> invoking raw 4 "Synth" "synth" >>= shouldEqual (ErrorCode "attemptNotAbove")
      -- an attempt that failed is not taken again either
      came <$> invoking raw 6 "Nowhere" "synth" >>= shouldEqual (FailedWith NoSuchModule)
      came <$> invoking raw 6 "Synth" "synth" >>= shouldEqual (ErrorCode "attemptNotAbove")
      -- the refused attempts began nothing: only attempt 5 asked
      map (map (\(Tuple attempt _) -> attempt)) (liftEffect (Ref.read raw.asked)) >>= shouldEqual [ 5, 5 ]
      closeAndWait raw >>= shouldEqual (Just 0)

  describe "a client breaking the protocol" do
    it "ends the session with status 1, the invocation unanswered" do
      let
        reply kind payload = Peer.answer { kind, payload }
        answer json = reply answeredKind (encodeAnswered json)
        value = fromObject <<< Object.fromFoldable
      for_'
        [ Tuple "an answer that is no canonical value" (answer (value [ Tuple "int" (fromNumber 1.5) ]))
        , Tuple "a boolean for the whole answer" (answer (value [ Tuple "boolean" (fromBoolean true) ]))
        , Tuple "an answer of another type" (answer (handleAnswerOf "Whnf"))
        , Tuple "an `answered` of another shape" (reply answeredKind Object.empty)
        , Tuple "an `abandoned` that is not empty" (reply abandonedKind (Object.singleton "why" jsonNull))
        , Tuple "a protocol error" (reply protocolErrorKind (Object.fromFoldable [ Tuple "code" (fromString "kindUnknown"), Tuple "detail" (fromString "") ]))
        , Tuple "an answer of an unknown kind" (reply "maybe" Object.empty)
        ]
        \(Tuple what r) -> do
          s <- streams
          outcome <- violating s r
          Tuple what outcome `shouldEqual` Tuple what (Tuple Ended (Just 1))
  describe "taking an answer" do
    it "calls an answer the descriptor admits and the store cannot take in the interpreter's own defect" do
      case prepare of
        Left err -> fail err
        Right elaboration -> do
          -- a store `Stella.Elab` was never installed in: the answer is a
          -- `GuestAnswer`, and its constructors are nowhere
          identities <- liftEffect (Ref.new noIdentities)
          let bare = emptyStore emptyTable identities
          taken <- liftEffect $ takeAnswer bare elaboration.descriptor
            { kind: answeredKind, payload: encodeAnswered (handleAnswer "h") }
          case taken of
            Inconsistent _ -> pure unit
            Violated why -> fail ("taken for the client's violation: " <> why)
            _ -> fail "taken in"

-- | A canonical value of another type: a request, where a `GuestAnswer` stands.
handleAnswerOf :: P.String -> Json
handleAnswerOf request = case encodeValue (wireOf "ObserveRequest" [ wireOf request [ WToken (tokenNamed "x") ] ]) of
  Right json -> json
  Left _ -> jsonNull

-- | A response by its kind, and a protocol error by its code as well.
answeredWith :: Either Peer.SessionFailure Reply -> P.String
answeredWith = case _ of
  Left failure -> "lost: " <> show failure
  Right reply
    | reply.kind == protocolErrorKind -> case decodeProtocolError reply.payload of
        Just error -> "protocolError " <> error.code
        Nothing -> "protocolError"
    | otherwise -> reply.kind

for_' :: forall a. P.Array a -> (a -> Aff Unit) -> Aff Unit
for_' xs f = Array.foldM (\_ x -> f x) unit xs

derive instance Eq Came

instance Show Came where
  show = case _ of
    TokenBack t -> "TokenBack " <> t
    FailedWith reason -> "FailedWith " <> show reason
    ErrorCode code -> "ErrorCode " <> code
    Ended -> "Ended"
    Otherwise kind -> "Otherwise " <> kind
