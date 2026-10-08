-- | Calls, tail calls, partial application, and applying a continuation.
-- |
-- | The fixture module is written in bytecode by hand, and its global slots hold
-- | the closures its `CALLK`s reach — which is what initialization would have put
-- | there.
-- |
-- | | Function | What it is |
-- | | --- | --- |
-- | | 0 | `identity`, of one parameter |
-- | | 1 | `second`, of two |
-- | | 2 | one parameter, returning a closure over `identity` |
-- | | 10 | one parameter, returning its capture |
-- | | 12, 13 | a pair of closures capturing each other |
-- | | 14 | one parameter, tail calling `identity` |
-- | | 16 | one parameter, tail calling itself once |
-- | | 20 | the function a hand-built continuation is suspended in |
-- |
-- | The rest are callers, each the subject of one case.
module Test.Steam.Calls (spec) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Either (Either(..))
import Data.Generic.Rep (class Generic)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Show.Generic (genericShow)
import Data.Traversable (traverse)
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Ref as Ref
import Run (runBaseEffect)
import Run.Except as Except
import Steam.Eval (Bug(..), Class(..), Failure(..), enter)
import Data.Tuple (Tuple(..))
import Steam.Module (CalleeTarget(..), GlobalSlot, Loaded, Prepared, Registry, prepare)
import Steam.Value (Closure, Continuation(..), CtorId(..), Foreign(..), ModuleId(..), StackEntry(..), Value(..))
import Stella.Compiler.Primitive (PrimOp(..))
import Stella.Compiler.Bytecode.Instr (CalleeIx(..), ConstIx(..), FuncIx(..), Function, GlobalIx(..), Instr(..), Node, Reg(..), Tail(..))
import Stella.Compiler.Bytecode.Module (Constant(..))
import Stella.Compiler.MiddleEnd.Rep (Rep(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

-- The fixture module -------------------------------------------------------------

pairCtor :: CtorId
pairCtor = CtorId 100

returning :: P.Array Instr -> Reg -> Node
returning code reg = { code, tail: RET reg }

fn :: { nparams :: P.Int, nregs :: P.Int, ncaptures :: P.Int } -> Node -> Function
fn counts body =
  { nparams: counts.nparams
  , regs: Array.replicate counts.nregs RepVal
  , captures: Array.replicate counts.ncaptures RepVal
  , joins: []
  , body
  }

plain :: P.Int -> Node -> Function
plain nregs = fn { nparams: 0, nregs, ncaptures: 0 }

-- | The fixture's functions, as a file holds them.
functions :: P.Array Function
functions =
  -- 0: identity
  [ fn { nparams: 1, nregs: 1, ncaptures: 0 } (returning [] (Reg 0))

  -- 1: the second of two arguments
  , fn { nparams: 2, nregs: 2, ncaptures: 0 } (returning [] (Reg 1))

  -- 2: a function whose value is itself a function
  , fn { nparams: 1, nregs: 2, ncaptures: 0 }
      (returning [ CLOS (Reg 1) (FuncIx 0) [] ] (Reg 1))

  -- 3: a saturated call to a global
  , plain 2
      ( returning
          [ LOADK (Reg 0) (ConstIx 0)
          , CALLK (Reg 1) (GlobalIx 0) [ Reg 0 ]
          ]
          (Reg 1)
      )

  -- 4: two arguments given one at a time, the first yielding a partial
  -- application and the second saturating it
  , plain 5
      ( returning
          [ LOADK (Reg 0) (ConstIx 0)
          , LOADK (Reg 1) (ConstIx 1)
          , LOADG (Reg 2) (GlobalIx 1)
          , CALLU (Reg 3) (Reg 2) [ Reg 0 ]
          , CALLU (Reg 4) (Reg 3) [ Reg 1 ]
          ]
          (Reg 4)
      )

  -- 5: one argument more than the callee takes, so the rest applies to what it
  -- returns
  , plain 4
      ( returning
          [ LOADK (Reg 0) (ConstIx 0)
          , LOADK (Reg 1) (ConstIx 1)
          , LOADG (Reg 2) (GlobalIx 2)
          , CALLU (Reg 3) (Reg 2) [ Reg 0, Reg 1 ]
          ]
          (Reg 3)
      )

  -- 6: a partial application built by `PAP` over a global, saturated after
  , plain 4
      ( returning
          [ LOADK (Reg 0) (ConstIx 0)
          , LOADK (Reg 1) (ConstIx 1)
          , PAP (Reg 2) (CalleeIx 0) [ Reg 0 ]
          , CALLU (Reg 3) (Reg 2) [ Reg 1 ]
          ]
          (Reg 3)
      )

  -- 7: the same over a constructor, which is callable only this way
  , plain 4
      ( returning
          [ LOADK (Reg 0) (ConstIx 0)
          , LOADK (Reg 1) (ConstIx 1)
          , PAP (Reg 2) (CalleeIx 1) [ Reg 0 ]
          , CALLU (Reg 3) (Reg 2) [ Reg 1 ]
          ]
          (Reg 3)
      )

  -- 8: a partial application that is not partial
  , plain 3
      ( returning
          [ LOADK (Reg 0) (ConstIx 0)
          , LOADK (Reg 1) (ConstIx 1)
          , PAP (Reg 2) (CalleeIx 0) [ Reg 0, Reg 1 ]
          ]
          (Reg 2)
      )

  -- 9: a closure over a capture, applied
  , plain 4
      ( returning
          [ LOADK (Reg 0) (ConstIx 1)
          , CLOS (Reg 1) (FuncIx 10) [ Reg 0 ]
          , LOADK (Reg 2) (ConstIx 0)
          , CALLU (Reg 3) (Reg 1) [ Reg 2 ]
          ]
          (Reg 3)
      )

  -- 10: the function that closure runs, which returns what it closed over
  , fn { nparams: 1, nregs: 2, ncaptures: 1 } (returning [ CAPT (Reg 1) 0 ] (Reg 1))

  -- 11: two closures capturing each other, allocated before either is filled
  , plain 4
      ( returning
          [ CLOSN (Reg 0) (FuncIx 12) 1
          , CLOSN (Reg 1) (FuncIx 13) 1
          , SETCAP (Reg 0) 0 (Reg 1)
          , SETCAP (Reg 1) 0 (Reg 0)
          , LOADK (Reg 2) (ConstIx 0)
          , CALLU (Reg 3) (Reg 0) [ Reg 2 ]
          ]
          (Reg 3)
      )

  -- 12: calls its partner with the argument it was given
  , fn { nparams: 1, nregs: 3, ncaptures: 1 }
      ( returning
          [ CAPT (Reg 1) 0
          , CALLU (Reg 2) (Reg 1) [ Reg 0 ]
          ]
          (Reg 2)
      )

  -- 13: the partner, which returns it
  , fn { nparams: 1, nregs: 1, ncaptures: 1 } (returning [] (Reg 0))

  -- 14: a tail call, which pushes nothing
  , fn { nparams: 1, nregs: 1, ncaptures: 0 }
      { code: [], tail: TAILK (GlobalIx 0) [ Reg 0 ] }

  -- 15: a call to that one, whose value must reach this register rather than its
  -- caller's
  , plain 2
      ( returning
          [ LOADK (Reg 0) (ConstIx 0)
          , CALLK (Reg 1) (GlobalIx 3) [ Reg 0 ]
          ]
          (Reg 1)
      )

  -- 16: a function that tail calls itself once and returns on the second pass
  , fn { nparams: 1, nregs: 3, ncaptures: 0 }
      { code: []
      , tail: BRIF (Reg 0)
          { code: [ LOADK (Reg 1) (ConstIx 2) ]
          , tail: TAILK (GlobalIx 4) [ Reg 1 ]
          }
          (returning [ LOADK (Reg 2) (ConstIx 1) ] (Reg 2))
      }

  -- 17: a global that holds a value rather than a function
  , plain 1 (returning [ LOADG (Reg 0) (GlobalIx 5) ] (Reg 0))

  -- 18: a global whose module has not been initialized
  , plain 1 (returning [ LOADG (Reg 0) (GlobalIx 6) ] (Reg 0))

  -- 19: a value applied that is not callable
  , plain 2
      ( returning
          [ LOADK (Reg 0) (ConstIx 0)
          , CALLU (Reg 1) (Reg 0) [ Reg 0 ]
          ]
          (Reg 1)
      )

  -- 20: the function a hand-built continuation is suspended in, which returns
  -- what the resumption wrote
  , plain 6 (returning [] (Reg 5))

  -- 21: a continuation applied to one argument
  , fn { nparams: 2, nregs: 3, ncaptures: 0 }
      (returning [ CALLU (Reg 2) (Reg 0) [ Reg 1 ] ] (Reg 2))

  -- 22: a continuation applied to two
  , fn { nparams: 3, nregs: 4, ncaptures: 0 }
      (returning [ CALLU (Reg 3) (Reg 0) [ Reg 1, Reg 2 ] ] (Reg 3))

  -- 23: a continuation applied to nothing
  , fn { nparams: 1, nregs: 2, ncaptures: 0 }
      (returning [ CALLU (Reg 1) (Reg 0) [] ] (Reg 1))

  -- 24: a closure built over more captures than its function declares
  , plain 2
      ( returning
          [ LOADK (Reg 0) (ConstIx 0)
          , CLOS (Reg 1) (FuncIx 0) [ Reg 0 ]
          ]
          (Reg 1)
      )

  -- 25: capture slots allocated in a number its function does not have
  , plain 1 (returning [ CLOSN (Reg 0) (FuncIx 12) 2 ] (Reg 0))

  -- 26: a capture slot outside what the closure has
  , plain 2
      ( returning
          [ CLOSN (Reg 0) (FuncIx 12) 1
          , LOADK (Reg 1) (ConstIx 0)
          , SETCAP (Reg 0) 1 (Reg 1)
          ]
          (Reg 0)
      )

  -- 27: a capture slot filled twice
  , plain 2
      ( returning
          [ CLOSN (Reg 0) (FuncIx 12) 1
          , LOADK (Reg 1) (ConstIx 0)
          , SETCAP (Reg 0) 0 (Reg 1)
          , SETCAP (Reg 0) 0 (Reg 1)
          ]
          (Reg 0)
      )

  -- 28: an operation applied below its arity, which stores the argument
  , plain 2
      ( returning
          [ LOADK (Reg 0) (ConstIx 0)
          , PAP (Reg 1) (CalleeIx 2) [ Reg 0 ]
          ]
          (Reg 1)
      )

  -- 29: the same, saturated
  , plain 3
      ( returning
          [ LOADK (Reg 0) (ConstIx 0)
          , PAP (Reg 1) (CalleeIx 2) [ Reg 0 ]
          , CALLU (Reg 2) (Reg 1) [ Reg 0 ]
          ]
          (Reg 2)
      )

  -- 30: a foreign applied below its arity
  , plain 2
      ( returning
          [ LOADK (Reg 0) (ConstIx 0)
          , PAP (Reg 1) (CalleeIx 3) [ Reg 0 ]
          ]
          (Reg 1)
      )

  -- 31: the same, saturated
  , plain 3
      ( returning
          [ LOADK (Reg 0) (ConstIx 0)
          , PAP (Reg 1) (CalleeIx 3) [ Reg 0 ]
          , CALLU (Reg 2) (Reg 1) [ Reg 0 ]
          ]
          (Reg 2)
      )

  -- 32: a known call to a global of another module, whose function reads that
  -- module's own constant pool
  , plain 2
      ( returning
          [ LOADK (Reg 0) (ConstIx 0)
          , CALLK (Reg 1) (GlobalIx 7) [ Reg 0 ]
          ]
          (Reg 1)
      )

  -- 33: a known call supplying fewer arguments than the entry takes
  , plain 1 (returning [ CALLK (Reg 0) (GlobalIx 0) [] ] (Reg 0))

  -- 34: a known call on a slot that holds no closure
  , plain 2
      ( returning
          [ LOADK (Reg 0) (ConstIx 0)
          , CALLK (Reg 1) (GlobalIx 5) [ Reg 0 ]
          ]
          (Reg 1)
      )
  ]

-- | Another module, whose one function returns a constant of its own pool. What a
-- | call to it reads is that pool and not the caller's.
libFunctions :: P.Array Function
libFunctions =
  [ fn { nparams: 1, nregs: 2, ncaptures: 0 }
      (returning [ LOADK (Reg 1) (ConstIx 0) ] (Reg 1))
  ]

-- | A closure over the function of the fixture at that index, over an empty
-- | capture list.
closureOf :: P.Int -> Effect Closure
closureOf i = do
  captures <- Ref.new Map.empty
  pure { func: { module: ModuleId 0, func: FuncIx i }, captures }

-- | The fixture module, with the global slots initialization would have filled.
-- |
-- | | Slot | What it holds |
-- | | --- | --- |
-- | | 0 | a closure over `identity` |
-- | | 1 | a closure over `second` |
-- | | 2 | a closure over the function returning a closure |
-- | | 3 | a closure over the one that tail calls |
-- | | 4 | a closure over the one that tail calls itself |
-- | | 5 | an `Int`, as a global evaluated at initialization holds |
-- | | 6 | nothing |
-- | The modules this fixture runs against.
registryOf :: Effect Registry
registryOf = do
  lib <- libModule
  main <- loadedModule lib
  pure (Map.fromFoldable [ Tuple (ModuleId 0) main, Tuple (ModuleId 1) lib ])

-- | The other module, holding one function and its own constant pool.
libModule :: Effect Loaded
libModule = pure
  { id: ModuleId 1
  , constants: [ CInt 42 ]
  , keys: []
  , ops: []
  , ctors: []
  , foreigns: []
  , globals: []
  , callees: []
  , prims: []
  , handlers: []
  , regions: []
  , unit: VData (CtorId 999) []
  , functions: Array.mapMaybe prepared libFunctions
  }

loadedModule :: Loaded -> Effect Loaded
loadedModule lib = do
  identity' <- filled =<< map VClos (closureOf 0)
  second <- filled =<< map VClos (closureOf 1)
  higher <- filled =<< map VClos (closureOf 2)
  middle <- filled =<< map VClos (closureOf 14)
  self <- filled =<< map VClos (closureOf 16)
  value <- filled (VInt 7)
  empty <- Ref.new Nothing
  captures <- Ref.new Map.empty
  elsewhere <- filled (VClos { func: { module: lib.id, func: FuncIx 0 }, captures })
  pure
    { id: ModuleId 0
    , constants: [ CInt 1, CInt 2, CBoolean false, CBoolean true ]
    , keys: []
    , ops: []
    , ctors: [ { id: pairCtor, arity: 2 } ]
    , foreigns: []
    , globals: [ identity', second, higher, middle, self, value, empty, elsewhere ]
    , callees:
        [ TargetGlobal second
        , TargetCtor pairCtor 2
        , TargetPrim IntAdd
        , TargetForeign (ForeignOperation IntSub) 2
        ]
    , prims: [ IntAdd ]
    , handlers: []
    , regions: []
    , unit: VData (CtorId 999) []
    , functions: Array.mapMaybe prepared functions
    }
  where
  filled :: Value -> Effect GlobalSlot
  filled = Ref.new <<< Just

-- | What loading makes of a function of the fixture.
prepared :: Function -> Maybe Prepared
prepared function = case prepare function of
  Right p -> Just p
  Left _ -> Nothing

-- Running one ---------------------------------------------------------------------

-- | The value a function of the fixture returns, or what ended the run.
runs :: P.Int -> P.Array Value -> Aff (Either Failure Value)
runs i args = liftEffect do
  registry <- registryOf
  closure <- closureOf i
  runBaseEffect (Except.runExcept (enter registry closure args))

-- | A continuation suspended in function 20, waiting for a value in the register
-- | that function returns.
continuation :: Effect Value
continuation = do
  closure <- closureOf 20
  regs <- Ref.new Map.empty
  let
    activation =
      { func: closure.func
      , closure
      , regs
      , node: returning [] (Reg 5)
      , ip: 0
      }
  pure (VCont (Continuation [ Resume activation (Reg 5) ]))

-- | What a returned value holds, as far as a test needs it.
data Held
  = AnInt P.Int
  | ABool P.Boolean
  | AData CtorId P.Int
  | APap P.Int
  | Elsewhere

held :: Either Failure Value -> Either Failure Held
held = map case _ of
  VInt n -> AnInt n
  VBoolean b -> ABool b
  VData ctor fields -> AData ctor (Array.length fields)
  VPap pap -> APap (Array.length pap.args)
  _ -> Elsewhere

spec :: Spec Unit
spec = describe "Steam.Calls" do

  describe "the fixture" do
    it "holds functions loading accepts" do
      map (const unit) (traverse prepare functions) `shouldEqual` Right unit
      map (const unit) (traverse prepare libFunctions) `shouldEqual` Right unit
      registry <- liftEffect registryOf
      map (\loaded -> Array.length loaded.functions) (Map.values registry # Array.fromFoldable)
        `shouldEqual` [ Array.length functions, Array.length libFunctions ]

  describe "calling" do
    it "calls the closure a global slot holds" do
      result <- runs 3 []
      held result `shouldEqual` Right (AnInt 1)

    it "builds a partial application from too few arguments, and saturates it" do
      result <- runs 4 []
      held result `shouldEqual` Right (AnInt 2)

    it "applies what a call returns to the arguments left over" do
      result <- runs 5 []
      held result `shouldEqual` Right (AnInt 2)

    it "applies a value that is not callable nowhere" do
      result <- runs 19 []
      held result `shouldEqual` Left (Bug (NotOfClass ACallable))

  describe "partial application" do
    it "carries a global's closure, and calls it once saturated" do
      result <- runs 6 []
      held result `shouldEqual` Right (AnInt 2)

    it "carries a constructor, and builds the value once saturated" do
      result <- runs 7 []
      held result `shouldEqual` Right (AData pairCtor 2)

    it "is refused where it is not below the callee's arity" do
      result <- runs 8 []
      held result `shouldEqual` Left (Bug (PapNotBelowArity 2 2))

  describe "closures" do
    it "carries what it captured to the function it runs" do
      result <- runs 9 []
      held result `shouldEqual` Right (AnInt 2)

    it "lets two closures capture each other, being allocated before either is filled" do
      result <- runs 11 []
      held result `shouldEqual` Right (AnInt 1)

  describe "capture slots" do
    it "are as many as the function declares" do
      result <- runs 24 []
      held result `shouldEqual` Left (Bug (WrongCaptureCount (FuncIx 0) 0 1))

    it "are allocated in that number where a group is built" do
      result <- runs 25 []
      held result `shouldEqual` Left (Bug (WrongCaptureCount (FuncIx 12) 1 2))

    it "cannot be filled outside what the closure has" do
      result <- runs 26 []
      held result `shouldEqual` Left (Bug (CaptureOutOfRange (FuncIx 12) 1))

    it "are each filled once" do
      result <- runs 27 []
      held result `shouldEqual` Left (Bug (CaptureAlreadyFilled 0))

  describe "an operation or a foreign below its arity" do
    it "stores the arguments an operation has so far" do
      -- the count decides before the kind does: nothing is carried out until the
      -- last argument arrives
      result <- runs 28 []
      held result `shouldEqual` Right (APap 1)

    it "carries out the operation once saturated" do
      -- the count decides before the kind: at the last argument the entry runs
      result <- runs 29 []
      held result `shouldEqual` Right (AnInt 2)

    it "stores the arguments a foreign has so far" do
      result <- runs 30 []
      held result `shouldEqual` Right (APap 1)

    it "carries out the foreign once saturated" do
      -- the fixture stands over `Base.Int.sub`, which the interpreter carries out
      -- itself: 1 - 1
      result <- runs 31 []
      held result `shouldEqual` Right (AnInt 0)

  describe "a known call" do
    it "reaches a global of another module, and that module's own tables" do
      -- the function it enters reads constant 0 of its own pool, which is not the
      -- caller's constant 0
      result <- runs 32 []
      held result `shouldEqual` Right (AnInt 42)

    it "supplies exactly the arity the entry takes" do
      result <- runs 33 []
      held result `shouldEqual` Left (Bug (WrongArgumentCount (FuncIx 0) 1 0))

    it "is refused where the slot holds no closure" do
      result <- runs 34 []
      held result `shouldEqual` Left (Bug (NotOfClass AClosure))

  describe "tail calls" do
    it "returns to the caller of the activation it replaced" do
      -- the tail call pushes nothing, so `identity`'s value reaches the register
      -- of the call two frames up rather than the one that tail called
      result <- runs 15 []
      held result `shouldEqual` Right (AnInt 1)

    it "calls itself without a frame of its own" do
      result <- runs 16 [ VBoolean true ]
      held result `shouldEqual` Right (AnInt 2)

  describe "globals" do
    it "reads what a slot holds" do
      result <- runs 17 []
      held result `shouldEqual` Right (AnInt 7)

    it "refuses a slot nothing has filled" do
      result <- runs 18 []
      held result `shouldEqual` Left (Bug (GlobalHoldsNothing (GlobalIx 6)))

  describe "applying a continuation" do
    it "resumes from the value it is given" do
      k <- liftEffect continuation
      result <- runs 21 [ k, VInt 5 ]
      held result `shouldEqual` Right (AnInt 5)

    it "resumes once for each application, from the value each is given" do
      -- that each application proceeds from the captured state rather than from
      -- where the last one stopped is what `reinstate` sees to
      k <- liftEffect continuation
      first <- runs 21 [ k, VInt 5 ]
      second <- runs 21 [ k, VInt 6 ]
      held first `shouldEqual` Right (AnInt 5)
      held second `shouldEqual` Right (AnInt 6)

    it "applies an argument past the first to what the segment returns" do
      k <- liftEffect continuation
      identity' <- liftEffect (map VClos (closureOf 0))
      result <- runs 22 [ k, identity', VInt 9 ]
      held result `shouldEqual` Right (AnInt 9)

    it "is refused where nothing is applied to it" do
      k <- liftEffect continuation
      result <- runs 23 [ k ]
      held result `shouldEqual` Left (Bug NoArgument)

derive instance Eq Held
derive instance Generic Held _

instance Show Held where
  show = genericShow
