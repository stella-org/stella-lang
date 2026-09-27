-- | `execute`, over `IO` values built by hand.
-- |
-- | The fixture's functions are the continuations a `Bind` holds, written in
-- | bytecode as everywhere else, and its native actions are written here: an action
-- | is a host function of no arguments, which an `Effect` already is.
-- |
-- | | Function | What it is |
-- | | --- | --- |
-- | | 0 | `\x -> Base.IO.pure x`, the continuation that wraps what it is given |
-- | | 1 | `\x -> Base.IO.pure (x + 1)`, which a chain can be counted by |
-- | | 2 | `\x -> x`, returning what is not an `IO` |
-- | | 3 | `\x -> Base.IO.pure (unsafeNew (-1))`, which faults before it wraps |
module Test.Steam.Drive (spec) where

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
import Effect.Uncurried (mkEffectFn1)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Run (runBaseAff', runBaseEffect)
import Run.Except as Except
import Steam.Drive (execute)
import Steam.Eval (Bug(..), Failure(..), enter)
import Steam.Fault (Fault(..))
import Steam.Module (Loaded, Registry, prepare)
import Steam.Value (ActionOutcome(..), Callee(..), Continuation(..), CtorId(..), Foreign(..), ForeignOutcome(..), IOEntry(..), IOValue(..), KeyId(..), MarkerKind(..), ModuleId(..), NativeAction, Opaque, StackEntry(..), Value(..))
import Stella.Compiler.Bytecode.Instr (ConstIx(..), ForeignIx(..), FuncIx(..), Function, Instr(..), Node, PrimIx(..), Reg(..), Tail(..))
import Stella.Compiler.Bytecode.Module (Constant(..))
import Stella.Compiler.MiddleEnd.Rep (Rep(..))
import Stella.Compiler.Primitive (PrimOp(..))
import Stella.Compiler.TypedCore.Name (Ident(..), ModuleName(..), Qualified(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

-- The fixture ----------------------------------------------------------------------

returning :: P.Array Instr -> Reg -> Node
returning code reg = { code, tail: RET reg }

-- | A function of one parameter and no captures.
unary :: P.Int -> Node -> Function
unary nregs body =
  { nparams: 1
  , regs: Array.replicate nregs RepVal
  , captures: []
  , joins: []
  , body
  }

functions :: P.Array Function
functions =
  -- 0: wrap what it is given
  [ unary 2 (returning [ FFI (Reg 1) (ForeignIx 0) [ Reg 0 ] ] (Reg 1))

  -- 1: wrap one more than what it is given
  , unary 3
      ( returning
          [ LOADK (Reg 1) (ConstIx 0)
          , PRIM (Reg 2) (PrimIx 0) [ Reg 0, Reg 1 ]
          , FFI (Reg 1) (ForeignIx 0) [ Reg 2 ]
          ]
          (Reg 1)
      )

  -- 2: hand back what is not an `IO`
  , unary 1 (returning [] (Reg 0))

  -- 3: fault before anything is wrapped
  , unary 3
      ( returning
          [ LOADK (Reg 1) (ConstIx 1)
          , PRIM (Reg 2) (PrimIx 1) [ Reg 1 ]
          , FFI (Reg 1) (ForeignIx 0) [ Reg 2 ]
          ]
          (Reg 1)
      )

  -- 4: `Base.IO.bind (Base.IO.pure 1) k`, built where a `.dmo` would build it
  , unary 4
      ( returning
          [ LOADK (Reg 1) (ConstIx 0)
          , FFI (Reg 2) (ForeignIx 0) [ Reg 1 ]
          , FFI (Reg 3) (ForeignIx 1) [ Reg 2, Reg 0 ]
          ]
          (Reg 3)
      )
  ]

loaded :: Loaded
loaded =
  { id: ModuleId 0
  , constants: [ CInt 1, CInt (-1) ]
  , keys: []
  , ops: []
  , ctors: []
  , globals: []
  , foreigns:
      [ { carriedOutBy: ForeignIO IOPureEntry, arity: 1 }
      , { carriedOutBy: ForeignIO IOBindEntry, arity: 2 }
      ]
  , callees: []
  , prims: [ IntAdd, ArrayUnsafeNew ]
  , handlers: []
  , unit: VData (CtorId 999) []
  , functions: Array.mapMaybe prepared functions
  }
  where
  prepared function = case prepare function of
    Right p -> Just p
    Left _ -> Nothing

registry :: Registry
registry = Map.fromFoldable [ Tuple (ModuleId 0) loaded ]

-- | A closure over the fixture's function at that index, which is what a `Bind`
-- | holds.
continuation :: P.Int -> Effect Value
continuation i = do
  captures <- Ref.new Map.empty
  pure (VClos { func: { module: ModuleId 0, func: FuncIx i }, captures })

-- Native actions ---------------------------------------------------------------------

foreign import aPromise :: Opaque

foreign import isThePromise :: Opaque -> P.Boolean

-- | An action done when it returns, recording that it ran.
produces :: Ref (P.Array P.String) -> P.String -> Value -> NativeAction
produces trail name value = do
  Ref.modify_ (_ <> [ name ]) trail
  pure (ActionProduced value)

-- | An action answering with a promise, which the loop neither awaits nor inspects.
givesPromise :: NativeAction
givesPromise = pure (ActionProduced (VOpaque aPromise))

-- | A continuation that ignores its argument and hands back an `IO` holding a
-- | native action, which is what lets **one** chain carry two actions.
-- |
-- | It is a partial application over a hosted foreign rather than a bytecode
-- | function, there being no instruction that builds a native action: one is the
-- | host's, and reaches a program through an entry that returns `IO`.
continuationGiving :: NativeAction -> Value
continuationGiving action = VPap
  { callee: CalleeForeign (ForeignHosted hostName body) 1
  , args: []
  }
  where
  body = mkEffectFn1 \_ -> pure (Produced (VIO (IONative action)))

-- | `Base.IO.pure` one argument short, which serves wherever a function value that
-- | wraps its argument is wanted.
papOverPure :: Value
papOverPure = VPap { callee: CalleeForeign (ForeignIO IOPureEntry) 1, args: [] }

-- | `Base.IO.bind` applied through the machine, which is what a `.dmo` does: the
-- | entry constructs and the drive loop is what later applies `k`.
buildsBind :: Value -> Effect (Either Failure Value)
buildsBind k = do
  captures <- Ref.new Map.empty
  let closure = { func: { module: ModuleId 0, func: FuncIx 4 }, captures }
  runBaseEffect (Except.runExcept (enter registry closure [ k ]))

hostName :: Qualified Ident
hostName = Qualified (ModuleName "Host") (Ident "nextAction")

refuses :: NativeAction
refuses = pure (ActionRefused "nothing to give")

-- | **Throwing where it is performed**, which for an action of no arguments is the
-- | one moment there is: an `Effect` is the host function, so running it is calling
-- | it.
throws :: NativeAction
throws = throwException (error "thrown where it was performed")

-- Running ------------------------------------------------------------------------------

runs :: IOValue -> Aff (Either Failure Value)
runs io = runBaseAff' (Except.runExcept (execute registry io))

-- | What a run left, as far as a case reads it.
data Held
  = AnInt P.Int
  | ThePromise
  | Elsewhere

derive instance Eq Held

instance Show Held where
  show = case _ of
    AnInt n -> "AnInt " <> show n
    ThePromise -> "ThePromise"
    Elsewhere -> "Elsewhere"

held :: Either Failure Value -> Either Failure Held
held = map case _ of
  VInt n -> AnInt n
  VOpaque o | isThePromise o -> ThePromise
  _ -> Elsewhere

spec :: Spec Unit
spec = describe "Steam.Drive" do

  it "holds a fixture loading accepts" do
    Array.length loaded.functions `shouldEqual` Array.length functions

  describe "the three forms" do

    it "yields what a Pure holds" do
      held <$> runs (IOPure (VInt 7)) >>= (_ `shouldEqual` Right (AnInt 7))

    it "performs a native action and yields what it gives" do
      trail <- liftEffect (Ref.new [])
      held <$> runs (IONative (produces trail "one" (VInt 3)))
        >>= (_ `shouldEqual` Right (AnInt 3))
      liftEffect (Ref.read trail) >>= (_ `shouldEqual` [ "one" ])

    -- **the case that catches a thenable test being reintroduced.** Stella fixes no
    -- meaning for asynchrony, so a promise is an opaque host value like any other;
    -- a loop that awaited would answer with what it resolved to, or fault
    it "answers with a promise as it stands, and does not await it" do
      held <$> runs (IONative givesPromise) >>= (_ `shouldEqual` Right ThePromise)

    -- the same value reaching the function of a `Bind`, which is where a loop that
    -- waited between the two steps would show itself
    it "hands a promise to what is bound after it, still unawaited" do
      held <$> runs (IOBind (IONative givesPromise) papOverPure)
        >>= (_ `shouldEqual` Right ThePromise)

    it "applies the function of a Bind to what the inner IO produced" do
      wrap <- liftEffect (continuation 0)
      held <$> runs (IOBind (IOPure (VInt 5)) wrap)
        >>= (_ `shouldEqual` Right (AnInt 5))

    -- `k` is a function value and not a closure in particular, so a partial
    -- application one argument short of `Base.IO.pure` serves as one
    it "applies a partial application the way any unknown call applies one" do
      held <$> runs (IOBind (IOPure (VInt 4)) papOverPure)
        >>= (_ `shouldEqual` Right (AnInt 4))

  describe "what the two Base.IO entries do" do

    -- **constructing is all either does** (D25). A `bind` that applied its function
    -- where it was called would give the same answer once the result was executed,
    -- and would differ here
    it "builds a Bind without applying the function it holds" do
      trail <- liftEffect (Ref.new [])
      let
        k = continuationGiving (produces trail "applied" (VInt 9))
        built = IOBind (IOPure (VInt 1)) k
      -- nothing ran while the value was built
      liftEffect (Ref.read trail) >>= (_ `shouldEqual` [])
      held <$> runs built >>= (_ `shouldEqual` Right (AnInt 9))
      liftEffect (Ref.read trail) >>= (_ `shouldEqual` [ "applied" ])

    it "builds a Bind through the machine, and executing it is what applies k" do
      trail <- liftEffect (Ref.new [])
      built <- liftEffect (buildsBind (continuationGiving (produces trail "later" (VInt 8))))
      case built of
        Right (VIO io) -> do
          liftEffect (Ref.read trail) >>= (_ `shouldEqual` [])
          held <$> runs io >>= (_ `shouldEqual` Right (AnInt 8))
        other -> fail ("expected a Bind, got " <> show (held other))

    -- applying one is `resume`, the path every unknown call over a continuation
    -- takes, so the drive loop reaches it the same way
    it "applies a continuation the way any unknown call applies one" do
      let
        answering = VCont
          ( Continuation
              [ HandlerMarker
                  { kind: Owner
                  , ownsRegion: false
                  , key: KeyId 0
                  , clauses: []
                  , returnClause: papOverPure
                  }
              ]
          )
      held <$> runs (IOBind (IOPure (VInt 6)) answering)
        >>= (_ `shouldEqual` Right (AnInt 6))

  describe "sequencing" do

    -- **one chain carrying two actions**, which is what makes this a test of the
    -- pending order. Two separate executions would record the same trail whatever
    -- the loop did between them
    it "runs the actions of one chain in order" do
      trail <- liftEffect (Ref.new [])
      let
        second = continuationGiving (produces trail "second" (VInt 2))
        chain = IOBind (IONative (produces trail "first" (VInt 1))) second
      _ <- runs chain
      liftEffect (Ref.read trail) >>= (_ `shouldEqual` [ "first", "second" ])

    -- a chain of three, so that a loop popping its pending functions in the wrong
    -- order is caught as well as one running them at the wrong time
    it "keeps the order over a chain of three actions" do
      trail <- liftEffect (Ref.new [])
      let
        third = continuationGiving (produces trail "third" (VInt 3))
        second = continuationGiving (produces trail "second" (VInt 2))
        chain = IOBind (IOBind (IONative (produces trail "first" (VInt 1))) second) third
      _ <- runs chain
      liftEffect (Ref.read trail) >>= (_ `shouldEqual` [ "first", "second", "third" ])

    -- **the case the pending stack exists for**, and the one an executor keeping its
    -- pending functions in host frames passes every other test while failing
    it "runs a chain longer than the host's call stack would carry" do
      increment <- liftEffect (continuation 1)
      let
        deep = foldl (\io _ -> IOBind io increment) (IOPure (VInt 0))
          (Array.replicate 20000 unit)
      held <$> runs deep >>= (_ `shouldEqual` Right (AnInt 20000))

  describe "what ends an execution" do

    it "faults where an action refuses" do
      held <$> runs (IONative refuses)
        >>= (_ `shouldEqual` Left (Faults (NativeRefused "nothing to give")))

    it "faults where an action throws, and reports it apart from a refusal" do
      held <$> runs (IONative throws)
        >>= (_ `shouldEqual` Left (Faults (NativeThrew "thrown where it was performed")))

    -- the value the pending continuations would have produced is not what comes
    -- back: they are discarded with the stack the fault threw away
    it "ends the execution where a continuation faults, and what was pending is lost" do
      faulting <- liftEffect (continuation 3)
      increment <- liftEffect (continuation 1)
      let
        after = IOBind (IOBind (IOPure (VInt 1)) faulting) increment
      held <$> runs (IOBind after increment)
        >>= (_ `shouldEqual` Left (Faults (NegativeArrayLength (-1))))

    -- the culprit is a lowering or an adapter and the machine cannot tell which, so
    -- this is the class that says the defect is above the interpreter
    it "reports a continuation returning what is not an IO as a bug, not a fault" do
      notAnIO <- liftEffect (continuation 2)
      outcome <- runs (IOBind (IOPure (VInt 1)) notAnIO)
      case outcome of
        Left (Bug NotAnIOFromContinuation) -> pure unit
        other -> fail ("expected the IO boundary bug, got " <> show (held other))
