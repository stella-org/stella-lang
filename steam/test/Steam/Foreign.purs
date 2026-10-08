-- | The host's foreign table: resolving against it at load, and calling what it
-- | holds
-- | ([Abstract Machine](../../../docs/technical-references/07-Runtime/01-Abstract-Machine.md)).
-- |
-- | **The interpreter is handed a table already assembled**, so nothing here
-- | imports anything: a table written by hand is what each case supplies.
-- |
-- | The first group is `load`, over modules written directly as `.dmo` records. The
-- | second is the machine, over a fixture whose `FOREIGNREFS` and `CALLEES` already
-- | hold bodies — which is what loading leaves behind, resolution happening there
-- | and never while a program runs.
module Test.Steam.Foreign (spec) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldl)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (error, throwException)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Effect.Uncurried (mkEffectFn1)
import Run (runBaseEffect)
import Run.Except as Except
import Steam.Eval (Failure(..), enter)
import Steam.Fault (Fault(..))
import Steam.Foreign (ForeignTable, emptyTable, insert)
import Steam.Load (LoadError(..), Store, emptyStore, globalNamed, load, moduleNamed, noIdentities)
import Steam.Module (CalleeTarget(..), Loaded, Registry, prepare)
import Steam.Value (Closure, CtorId(..), Foreign(..), ForeignBody, ForeignOutcome(..), IOValue(..), KeyId(..), ModuleId(..), Value(..))
import Stella.Compiler.Bytecode.Instr (CalleeIx(..), ConstIx(..), ForeignIx(..), FuncIx(..), Function, HandlerIx(..), Instr(..), Node, PrimIx(..), Reg(..), Tail(..))
import Stella.Compiler.Bytecode.Module (Constant(..), Dmo, GlobalInit(..))
import Stella.Compiler.MiddleEnd.Rep (Rep(..))
import Stella.Compiler.Primitive (PrimOp(..), arityOfOp)
import Stella.Compiler.TypedCore.Name (Ident(..), ModuleName(..), Qualified(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

-- Names --------------------------------------------------------------------------

hostModule :: ModuleName
hostModule = ModuleName "Host"

-- | A foreign the host supplies, taking one argument.
hostEcho :: Qualified Ident
hostEcho = Qualified hostModule (Ident "echo")

-- | A second, taking two, which the partial application stands over.
hostJoin :: Qualified Ident
hostJoin = Qualified hostModule (Ident "join")

hostResult :: Qualified Ident
hostResult = Qualified hostModule (Ident "result")

intModule :: ModuleName
intModule = ModuleName "Base.Int"

-- | An entry the interpreter claims, so the table is never consulted for it.
intAdd :: Qualified Ident
intAdd = Qualified intModule (Ident "add")

ioModule :: ModuleName
ioModule = ModuleName "Base.IO"

ioPure :: Qualified Ident
ioPure = Qualified ioModule (Ident "pure")

ioAction :: Qualified Ident
ioAction = Qualified ioModule (Ident "action")

intSum :: Qualified Ident
intSum = Qualified intModule (Ident "sum")

-- Bodies -------------------------------------------------------------------------

-- | A host function that throws where it is **applied**, which is not where an
-- | effect it returned would be performed. Written in JavaScript because that is
-- | the shape the hazard has: nothing in PureScript separates the two moments once
-- | a body is an `EffectFn1`, and this is what a careless adapter looks like.
foreign import throwsOnCall :: ForeignBody

-- | A body that counts the calls it is given, so a case can assert that one was
-- | never reached.
counting :: Ref P.Int -> (P.Array Value -> ForeignOutcome) -> ForeignBody
counting calls answer = mkEffectFn1 \args -> do
  Ref.modify_ (_ + 1) calls
  pure (answer args)

-- | The first argument, which is all any body here reads.
first :: P.Array Value -> Value
first args = case Array.head args of
  Just value -> value
  Nothing -> VBoolean false

-- | The sum of the ints among the arguments.
total :: P.Array Value -> P.Int
total = foldl add 0
  where
  add acc = case _ of
    VInt n -> acc + n
    _ -> acc

-- Modules written as `.dmo` ----------------------------------------------------------

-- | A node of instructions ending in a return.
returning :: P.Array Instr -> Reg -> Node
returning code reg = { code, tail: RET reg }

-- | A function of no parameters and no captures. The `Rep`s are descriptive and
-- | this interpreter reads none (D31).
plain :: P.Int -> Node -> Function
plain nregs body =
  { nparams: 0
  , regs: Array.replicate nregs RepVal
  , captures: []
  , joins: []
  , body
  }

-- | A `.dmo` holding nothing but what a case fills in.
bare :: ModuleName -> Dmo
bare name =
  { formatVersion: 0
  , abiVersion: "stella-base-0.1"
  , name
  , imports: []
  , constants: []
  , keys: []
  , ops: []
  , ctors: []
  , effects: []
  , foreigns: []
  , ctorRefs: []
  , foreignRefs: []
  , globalRefs: []
  , callees: []
  , prims: []
  , handlers: []
  , regions: []
  , functions: []
  , globals: []
  , exports: []
  }

-- | `module Host where foreign echo`, with a global whose initialization calls it.
-- | The arity the declaration states is the case's to choose, and whether anything
-- | calls the foreign is as well.
hostDmo :: { arity :: P.Int, calls :: P.Boolean } -> Dmo
hostDmo options = (bare hostModule)
  { constants = [ CInt 1 ]
  , foreigns = [ { name: hostEcho, arity: options.arity } ]
  , foreignRefs = if options.calls then [ hostEcho ] else []
  , functions =
      [ plain 2
          if options.calls then
            returning
              [ LOADK (Reg 0) (ConstIx 0)
              , FFI (Reg 1) (ForeignIx 0) (Array.replicate options.arity (Reg 0))
              ]
              (Reg 1)
          else
            returning [ LOADK (Reg 0) (ConstIx 0) ] (Reg 0)
      ]
  , globals = [ { name: hostResult, init: GRun (FuncIx 0) } ]
  }

-- | `module Base.Int where foreign add`, with `sum` calling it. The interpreter
-- | claims the name, so what the arity is checked against is the ABI's.
intDmo :: P.Int -> Dmo
intDmo arity = (bare intModule)
  { constants = [ CInt 1, CInt 2 ]
  , foreigns = [ { name: intAdd, arity } ]
  , foreignRefs = [ intAdd ]
  , functions =
      [ plain 3
          ( returning
              [ LOADK (Reg 0) (ConstIx 0)
              , LOADK (Reg 1) (ConstIx 1)
              , FFI (Reg 2) (ForeignIx 0) (argsOf arity)
              ]
              (Reg 2)
          )
      ]
  , globals = [ { name: intSum, init: GRun (FuncIx 0) } ]
  }
  where
  argsOf n = Array.mapWithIndex (\i _ -> Reg (min i 1)) (Array.replicate n unit)

-- | `module Base.IO where foreign pure`, with a global that applies it.
-- |
-- | The interpreter claims the name like an operation and it is not one: it returns
-- | `IO`, so the call is an `FFI` and no operation code stands for it.
ioDmo :: P.Int -> Dmo
ioDmo arity = (bare ioModule)
  { constants = [ CInt 1 ]
  , foreigns = [ { name: ioPure, arity } ]
  , foreignRefs = [ ioPure ]
  , functions =
      [ plain 2
          ( returning
              [ LOADK (Reg 0) (ConstIx 0)
              , FFI (Reg 1) (ForeignIx 0) (Array.replicate arity (Reg 0))
              ]
              (Reg 1)
          )
      ]
  , globals = [ { name: ioAction, init: GRun (FuncIx 0) } ]
  }

-- Running a load --------------------------------------------------------------------

fresh :: ForeignTable -> Effect Store
fresh table = map (emptyStore table) (Ref.new noIdentities)

loads :: Store -> Dmo -> Aff (Either LoadError Store)
loads store dmo = liftEffect (runBaseEffect (Except.runExcept (load store dmo)))

-- | The int a module's global was initialized to.
valueOf :: Store -> Qualified Ident -> Aff (Maybe P.Int)
valueOf store name = liftEffect case globalNamed store name of
  Nothing -> pure Nothing
  Just slot -> map
    ( case _ of
        Just (VInt n) -> Just n
        _ -> Nothing
    )
    (Ref.read slot)

-- The machine's fixture ---------------------------------------------------------------

-- | The functions the second group runs.
-- |
-- | | Function | What it exercises |
-- | | --- | --- |
-- | | 0 | a saturated `FFI` |
-- | | 1 | a body returning an `IO` value, handed on to a second foreign |
-- | | 2 | a `PAP` one below the arity, applied to the rest |
-- | | 3 | a body that refuses |
-- | | 4 | a body that throws |
-- | | 5 | function 3 under an installed handler |
-- | | 6 | a call whose callee ends in a `TAILFFI` |
-- | | 7 | that callee |
-- | | 8 | the return clause of the handler, which a discarded marker never runs |
-- | | 9 | a body that throws where it is applied rather than where it is run |
-- | | 10 | an array allocated, written, and read back through `PRIM` |
-- | | 11 | the same write, reached through a `PAP` over the operation |
-- | | 12 | the slot count an array reports back |
machineFunctions :: P.Array Function
machineFunctions =
  [ plain 2
      ( returning
          [ LOADK (Reg 0) (ConstIx 0)
          , FFI (Reg 1) (ForeignIx 0) [ Reg 0 ]
          ]
          (Reg 1)
      )

  , plain 3
      ( returning
          [ LOADK (Reg 0) (ConstIx 0)
          , FFI (Reg 1) (ForeignIx 1) [ Reg 0 ]
          , FFI (Reg 2) (ForeignIx 2) [ Reg 1 ]
          ]
          (Reg 2)
      )

  , plain 4
      ( returning
          [ LOADK (Reg 0) (ConstIx 0)
          , LOADK (Reg 1) (ConstIx 1)
          , PAP (Reg 2) (CalleeIx 0) [ Reg 0 ]
          , CALLU (Reg 3) (Reg 2) [ Reg 1 ]
          ]
          (Reg 3)
      )

  , plain 2
      ( returning
          [ LOADK (Reg 0) (ConstIx 0)
          , FFI (Reg 1) (ForeignIx 3) [ Reg 0 ]
          ]
          (Reg 1)
      )

  , plain 2
      ( returning
          [ LOADK (Reg 0) (ConstIx 0)
          , FFI (Reg 1) (ForeignIx 4) [ Reg 0 ]
          ]
          (Reg 1)
      )

  , plain 3
      ( returning
          [ CLOS (Reg 0) (FuncIx 3) []
          , CLOS (Reg 1) (FuncIx 8) []
          , HNDL (Reg 2) (HandlerIx 0) (Reg 0) (Reg 1) []
          ]
          (Reg 2)
      )

  -- the `Resume` this call pushes is what the tail call's value has to reach
  , plain 3
      ( returning
          [ LOADK (Reg 0) (ConstIx 0)
          , CLOS (Reg 1) (FuncIx 7) []
          , CALLU (Reg 2) (Reg 1) [ Reg 0 ]
          ]
          (Reg 2)
      )

  , { nparams: 1
    , regs: [ RepVal ]
    , captures: []
    , joins: []
    , body: { code: [], tail: TAILFFI (ForeignIx 0) [ Reg 0 ] }
    }

  , { nparams: 1
    , regs: [ RepVal, RepVal ]
    , captures: []
    , joins: []
    , body: returning [ LOADK (Reg 1) (ConstIx 2) ] (Reg 1)
    }

  , plain 2
      ( returning
          [ LOADK (Reg 0) (ConstIx 0)
          , FFI (Reg 1) (ForeignIx 5) [ Reg 0 ]
          ]
          (Reg 1)
      )

  -- 10: an array written and read back through `PRIM`
  , plain 5
      ( returning
          [ LOADK (Reg 0) (ConstIx 1)
          , PRIM (Reg 1) (PrimIx 0) [ Reg 0 ]
          , LOADK (Reg 2) (ConstIx 0)
          , PRIM (Reg 3) (PrimIx 1) [ Reg 2, Reg 0, Reg 1 ]
          , PRIM (Reg 4) (PrimIx 2) [ Reg 1, Reg 2 ]
          ]
          (Reg 4)
      )

  -- 11: the same write, reached through a partial application over the operation
  , plain 6
      ( returning
          [ LOADK (Reg 0) (ConstIx 1)
          , PRIM (Reg 1) (PrimIx 0) [ Reg 0 ]
          , LOADK (Reg 2) (ConstIx 0)
          , PAP (Reg 3) (CalleeIx 1) [ Reg 2, Reg 0 ]
          , CALLU (Reg 4) (Reg 3) [ Reg 1 ]
          , PRIM (Reg 5) (PrimIx 2) [ Reg 1, Reg 2 ]
          ]
          (Reg 5)
      )

  -- 12: the slot count an array reports back
  , plain 3
      ( returning
          [ LOADK (Reg 0) (ConstIx 1)
          , PRIM (Reg 1) (PrimIx 0) [ Reg 0 ]
          , PRIM (Reg 2) (PrimIx 3) [ Reg 1 ]
          ]
          (Reg 2)
      )
  ]

-- | The fixture, with the bodies its `FOREIGNREFS` hold and the counter one of them
-- | writes.
machine :: Effect { registry :: Registry, echoes :: Ref P.Int }
machine = do
  echoes <- Ref.new 0
  let
    echo :: ForeignBody
    echo = counting echoes (Produced <<< first)

    buildsIO :: ForeignBody
    buildsIO = mkEffectFn1 \_ -> pure (Produced (VIO (IOPure (VInt 7))))

    -- what it answers is whether the `IO` arrived as it was built
    readsIO :: ForeignBody
    readsIO = mkEffectFn1 \args -> pure
      ( Produced
          ( VBoolean case first args of
              VIO (IOPure (VInt 7)) -> true
              _ -> false
          )
      )

    refuses :: ForeignBody
    refuses = mkEffectFn1 \_ -> pure (Refused "nothing to give")

    throws :: ForeignBody
    throws = mkEffectFn1 \_ -> throwException (error "boom")

    joined :: ForeignBody
    joined = mkEffectFn1 \args -> pure (Produced (VInt (total args)))

    hosted name body arity = { carriedOutBy: ForeignHosted name body, arity }

    loaded :: Loaded
    loaded =
      { id: ModuleId 0
      , constants: [ CInt 1, CInt 2, CInt 999 ]
      , keys: []
      , ops: []
      , ctors: []
      , globals: []
      , foreigns:
          [ hosted hostEcho echo 1
          , hosted (Qualified hostModule (Ident "buildsIO")) buildsIO 1
          , hosted (Qualified hostModule (Ident "readsIO")) readsIO 1
          , hosted (Qualified hostModule (Ident "refuses")) refuses 1
          , hosted (Qualified hostModule (Ident "throws")) throws 1
          , hosted throwsOnCallName throwsOnCall 1
          ]
      , callees:
          [ TargetForeign (ForeignHosted hostJoin joined) 2
          , TargetPrim ArrayUnsafeSet
          ]
      , prims: [ ArrayUnsafeNew, ArrayUnsafeSet, ArrayUnsafeIndex, ArrayLength ]
      , handlers: [ { key: KeyId 1, opClauses: [] } ]
      , regions: []
      , unit: VData (CtorId 999) []
      , functions: Array.mapMaybe prepared machineFunctions
      }
  pure { registry: Map.fromFoldable [ Tuple (ModuleId 0) loaded ], echoes }
  where
  prepared function = case prepare function of
    Right p -> Just p
    Left _ -> Nothing

-- Assertions ---------------------------------------------------------------------------

-- | What a run left, as far as a case reads it. `Value` has no equality of its own,
-- | an `IO` value and a closure having none to have.
data Held
  = AnInt P.Int
  | ABool P.Boolean
  | Elsewhere

derive instance Eq Held

instance Show Held where
  show = case _ of
    AnInt n -> "AnInt " <> show n
    ABool b -> "ABool " <> show b
    Elsewhere -> "Elsewhere"

reads :: Either Failure Value -> Either Failure Held
reads = map case _ of
  VInt n -> AnInt n
  VBoolean b -> ABool b
  _ -> Elsewhere

-- | That the fixture's function at that index leaves what the case expects.
returns
  :: { registry :: Registry, echoes :: Ref P.Int }
  -> P.Int
  -> Either Failure Held
  -> Aff Unit
returns fixture i expected = do
  outcome <- liftEffect do
    closure <- closureOf i
    runBaseEffect (Except.runExcept (enter fixture.registry closure []))
  reads outcome `shouldEqual` expected

closureOf :: P.Int -> Effect Closure
closureOf i = do
  captures <- Ref.new Map.empty
  pure { func: { module: ModuleId 0, func: FuncIx i }, captures }

spec :: Spec Unit
spec = describe "Steam.Foreign" do

  describe "resolving a declaration at load" do

    it "refuses a foreign the table does not hold" do
      store <- liftEffect (fresh emptyTable)
      outcome <- loads store (hostDmo { arity: 1, calls: true })
      map (const unit) outcome `shouldEqual` Left (ForeignWithoutImplementation hostEcho)

    -- reachability is not what decides it: a program whose foreigns are incomplete
    -- does not start
    it "refuses it where nothing calls it either" do
      store <- liftEffect (fresh emptyTable)
      outcome <- loads store (hostDmo { arity: 1, calls: false })
      map (const unit) outcome `shouldEqual` Left (ForeignWithoutImplementation hostEcho)

    it "refuses one the table holds at another arity, as the disagreement it is" do
      calls <- liftEffect (Ref.new 0)
      let table = insert hostEcho { arity: 2, body: counting calls (Produced <<< first) } emptyTable
      store <- liftEffect (fresh table)
      outcome <- loads store (hostDmo { arity: 1, calls: true })
      map (const unit) outcome `shouldEqual` Left (ForeignArityDisagrees hostEcho 1 2)
      -- the body is not reached by a load that refused
      liftEffect (Ref.read calls) >>= (_ `shouldEqual` 0)

    it "leaves the store as it was after a refusal" do
      store <- liftEffect (fresh emptyTable)
      refused <- loads store (hostDmo { arity: 1, calls: true })
      map (const unit) refused `shouldEqual` Left (ForeignWithoutImplementation hostEcho)
      moduleNamed store hostModule `shouldEqual` Nothing

      -- and the same store takes the module once the table holds the entry
      calls <- liftEffect (Ref.new 0)
      let
        table = insert hostEcho
          { arity: 1, body: counting calls (const (Produced (VInt 5))) }
          emptyTable
      again <- loads (store { hostForeigns = table }) (hostDmo { arity: 1, calls: true })
      case again of
        Left err -> fail (show err)
        Right loaded -> do
          valueOf loaded hostResult >>= (_ `shouldEqual` Just 5)
          liftEffect (Ref.read calls) >>= (_ `shouldEqual` 1)

    -- what is unwound is the interpreter's own state. A body may write where the
    -- reduction relation records nothing (D41), and nothing here can take that back
    it "leaves what a body wrote before refusing, the module uncommitted" do
      wrote <- liftEffect (Ref.new false)
      let
        table = insert hostEcho
          { arity: 1
          , body: mkEffectFn1 \_ -> do
              Ref.write true wrote
              pure (Refused "after the write")
          }
          emptyTable
      store <- liftEffect (fresh table)
      outcome <- loads store (hostDmo { arity: 1, calls: true })

      -- the failure is the initialization's, so the declaration resolved and the
      -- body ran
      case outcome of
        Left (InitializationFailed name _) -> name `shouldEqual` hostResult
        other -> fail ("expected an initialization failure, got " <> show (map (const unit) other))

      moduleNamed store hostModule `shouldEqual` Nothing
      liftEffect (Ref.read wrote) >>= (_ `shouldEqual` true)

    it "carries out the interpreter's own entry, the table holding that name too" do
      calls <- liftEffect (Ref.new 0)
      let
        table = insert intAdd
          { arity: arityOfOp IntAdd, body: counting calls (const (Produced (VInt 999))) }
          emptyTable
      store <- liftEffect (fresh table)
      outcome <- loads store (intDmo (arityOfOp IntAdd))
      case outcome of
        Left err -> fail (show err)
        Right loaded -> do
          -- `1 + 2`, which is the operation's answer and not the body's
          valueOf loaded intSum >>= (_ `shouldEqual` Just 3)
          liftEffect (Ref.read calls) >>= (_ `shouldEqual` 0)

    it "refuses the interpreter's own entry declared at another arity" do
      store <- liftEffect (fresh emptyTable)
      outcome <- loads store (intDmo 3)
      map (const unit) outcome
        `shouldEqual` Left (InterpreterEntryDeclaredAtWrongArity intAdd (arityOfOp IntAdd) 3)

    -- `Base.IO.pure` and `Base.IO.bind` are the interpreter's like an operation and
    -- are not operations, and the rule that selects the source is the same one
    it "carries out a Base.IO entry itself, at the arity the ABI gives it" do
      store <- liftEffect (fresh emptyTable)
      outcome <- loads store (ioDmo 1)
      case outcome of
        Left err -> fail (show err)
        Right _ -> pure unit

    it "refuses a Base.IO entry declared at another arity" do
      store <- liftEffect (fresh emptyTable)
      outcome <- loads store (ioDmo 2)
      map (const unit) outcome
        `shouldEqual` Left (InterpreterEntryDeclaredAtWrongArity ioPure 1 2)

    it "never consults the host's table for a Base.IO entry" do
      calls <- liftEffect (Ref.new 0)
      let
        table = insert ioPure
          { arity: 1, body: counting calls (const (Produced (VInt 0))) }
          emptyTable
      store <- liftEffect (fresh table)
      outcome <- loads store (ioDmo 1)
      case outcome of
        Left err -> fail (show err)
        Right _ -> liftEffect (Ref.read calls) >>= (_ `shouldEqual` 0)

    -- selecting the source on the name **together with** an arity is what would let
    -- a host implementation stand where the ABI fixes an operation's meaning
    it "refuses it even where the table holds that name at exactly that arity" do
      calls <- liftEffect (Ref.new 0)
      let table = insert intAdd { arity: 3, body: counting calls (const (Produced (VInt 0))) } emptyTable
      store <- liftEffect (fresh table)
      outcome <- loads store (intDmo 3)
      map (const unit) outcome
        `shouldEqual` Left (InterpreterEntryDeclaredAtWrongArity intAdd (arityOfOp IntAdd) 3)
      liftEffect (Ref.read calls) >>= (_ `shouldEqual` 0)

  describe "calling what the table held" do

    it "calls a saturated FFI once, with every argument at once" do
      fixture <- liftEffect machine
      returns fixture 0 (Right (AnInt 1))
      liftEffect (Ref.read fixture.echoes) >>= (_ `shouldEqual` 1)

    -- no instruction examines an `IO` value, so nothing wraps it, unwraps it, or
    -- executes it; carrying one needs no drive loop
    it "hands an IO value on to another foreign as it stands" do
      fixture <- liftEffect machine
      returns fixture 1 (Right (ABool true))

    it "calls the body once, where a partial application completed the arity" do
      fixture <- liftEffect machine
      returns fixture 2 (Right (AnInt 3))

    it "faults where the body refuses" do
      fixture <- liftEffect machine
      returns fixture 3 (Left (Faults (ForeignRefused refusesName "nothing to give")))

    -- a fault discards the continuation entire, the handler marker included, so the
    -- return clause that would have replaced the value never runs
    it "discards an installed handler along with the rest" do
      fixture <- liftEffect machine
      returns fixture 5 (Left (Faults (ForeignRefused refusesName "nothing to give")))

    -- an exception escaping would end the run outside the fault path, leaving the
    -- stack undiscarded and a session unable to answer the next entry
    it "catches what a body throws, and keeps it apart from a refusal" do
      fixture <- liftEffect machine
      returns fixture 4 (Left (Faults (ForeignThrew throwsName "boom")))

    -- **the call itself is inside the `try`**, not only what the call returns: a
    -- host function may throw where it is applied, and that throw must not reach
    -- past the boundary either
    it "catches one thrown where the body was called rather than where it ran" do
      fixture <- liftEffect machine
      returns fixture 9
        (Left (Faults (ForeignThrew throwsOnCallName "thrown where it was called")))

    it "carries a TAILFFI's value to what the call below it left waiting" do
      fixture <- liftEffect machine
      returns fixture 6 (Right (AnInt 1))
      liftEffect (Ref.read fixture.echoes) >>= (_ `shouldEqual` 1)

  describe "the array operations, through the machine" do

    -- the same value reaches the register, whether the operation was named by a
    -- `PRIM` or completed from a partial application over it
    it "writes and reads an array back through PRIM" do
      fixture <- liftEffect machine
      returns fixture 10 (Right (AnInt 2))

    it "does the same where a PAP over the operation completed the arity" do
      fixture <- liftEffect machine
      returns fixture 11 (Right (AnInt 2))

    it "reports the slot count the array was created with" do
      fixture <- liftEffect machine
      returns fixture 12 (Right (AnInt 2))

-- | The names the two failing bodies of the fixture were resolved for, which a
-- | fault carries.
refusesName :: Qualified Ident
refusesName = Qualified hostModule (Ident "refuses")

throwsName :: Qualified Ident
throwsName = Qualified hostModule (Ident "throws")

throwsOnCallName :: Qualified Ident
throwsOnCallName = Qualified hostModule (Ident "throwsOnCall")
