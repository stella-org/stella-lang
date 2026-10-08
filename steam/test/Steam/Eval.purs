-- | `enter`, over the instructions that stay inside one activation.
-- |
-- | Each function of the fixture module is a small program written in bytecode by
-- | hand, and what it returns is the assertion.
-- |
-- | | Function | What it exercises |
-- | | --- | --- |
-- | | 0 | `RNEW`, `REXT`, `RSEL` |
-- | | 1 | `RUPD`, `RRES`, `RMRG` |
-- | | 2 | `CTOR`, `FIELD` |
-- | | 3 | `LOADC` and a `BRC` whose cases exhaust |
-- | | 4 | `VINJ`, `BRK` with a default, `VPAY` |
-- | | 5 | `BRL`, which separates `0.0` from `-0.0` (D37) |
-- | | 6 | `BRIF` |
-- | | 7 | `JMP`, whose writes are a parallel move |
-- | | 8 | `CAPT`, which reads the closure rather than a register |
-- | | 9 | `MOVE` |
-- |
-- | Each function after those is one state no `.dmo` admits, and is otherwise a
-- | function a reader would accept: the register and capture counts it declares
-- | cover what its code names, so what a case tests is the one thing it is about.
module Test.Steam.Eval (spec) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Either (Either(..))
import Data.Generic.Rep (class Generic)
import Data.Map (Map)
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
import Steam.Module (Loaded, Registry, prepare)
import Steam.Value (Closure, CtorId(..), KeyId(..), ModuleId(..), Value(..))
import Stella.Compiler.Bytecode.Instr (ConstIx(..), CtorIx(..), FuncIx(..), Function, Instr(..), Join, JoinName(..), KeyIx(..), Node, PrimIx(..), Reg(..), RegionIx(..), Tail(..))
import Stella.Compiler.Bytecode.Module (Constant(..))
import Stella.Compiler.MiddleEnd.Rep (Rep(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

-- The fixture module -------------------------------------------------------------

-- | A key of the fixture, under the identity a registry would have assigned.
keyA :: KeyId
keyA = KeyId 10

keyB :: KeyId
keyB = KeyId 11

-- | A constructor of two fields, and one of none.
pairCtor :: CtorId
pairCtor = CtorId 100

nilCtor :: CtorId
nilCtor = CtorId 101

-- | A node of instructions ending in a return.
returning :: P.Array Instr -> Reg -> Node
returning code reg = { code, tail: RET reg }

-- | A function of the fixture.
-- |
-- | `regs` carries one `Rep` per register the code names and `captures` one per
-- | capture slot, which is what a `.dmo` states and what a reader validates. The
-- | `Rep`s themselves are descriptive, and this interpreter reads none (D31).
fn
  :: { nparams :: P.Int, nregs :: P.Int, ncaptures :: P.Int }
  -> P.Array Join
  -> Node
  -> Function
fn counts joins body =
  { nparams: counts.nparams
  , regs: Array.replicate counts.nregs RepVal
  , captures: Array.replicate counts.ncaptures RepVal
  , joins
  , body
  }

-- | A function of no parameters, no captures, and no join points.
plain :: P.Int -> Node -> Function
plain nregs = fn { nparams: 0, nregs, ncaptures: 0 } []

-- | The fixture's functions, as a file holds them.
functions :: P.Array Function
functions =
  -- 0: { keyA: 1 } extended at keyB with 2, then keyB selected
  [ plain 6
      ( returning
          [ RNEW (Reg 0)
          , LOADK (Reg 1) (ConstIx 0)
          , REXT (Reg 2) (KeyIx 0) (Reg 1) (Reg 0)
          , LOADK (Reg 3) (ConstIx 1)
          , REXT (Reg 4) (KeyIx 1) (Reg 3) (Reg 2)
          , RSEL (Reg 5) (KeyIx 1) (Reg 4)
          ]
          (Reg 5)
      )

  -- 1: { keyA: 1 } updated at keyA to 2, restricted, merged with { keyB: 1 }, and
  -- keyB selected back out
  , plain 9
      ( returning
          [ RNEW (Reg 0)
          , LOADK (Reg 1) (ConstIx 0)
          , REXT (Reg 2) (KeyIx 0) (Reg 1) (Reg 0)
          , LOADK (Reg 3) (ConstIx 1)
          , RUPD (Reg 4) (KeyIx 0) (Reg 2) (Reg 3)
          , RRES (Reg 5) (KeyIx 0) (Reg 4)
          , REXT (Reg 6) (KeyIx 1) (Reg 1) (Reg 5)
          , RMRG (Reg 7) (Reg 5) (Reg 6)
          , RSEL (Reg 8) (KeyIx 1) (Reg 7)
          ]
          (Reg 8)
      )

  -- 2: a pair of 1 and 2, its second field read back
  , plain 4
      ( returning
          [ LOADK (Reg 0) (ConstIx 0)
          , LOADK (Reg 1) (ConstIx 1)
          , CTOR (Reg 2) (CtorIx 0) [ Reg 0, Reg 1 ]
          , FIELD (Reg 3) (Reg 2) (CtorIx 0) 1
          ]
          (Reg 3)
      )

  -- 3: the nullary constructor, dispatched on; the cases exhaust, so there is no
  -- default to fall through to
  , plain 3
      { code:
          [ LOADC (Reg 0) (CtorIx 1)
          , LOADK (Reg 1) (ConstIx 0)
          , LOADK (Reg 2) (ConstIx 1)
          ]
      , tail: BRC (Reg 0)
          [ { ctor: CtorIx 0, body: returning [] (Reg 1) }
          , { ctor: CtorIx 1, body: returning [] (Reg 2) }
          ]
          Nothing
      }

  -- 4: a variant at keyA, dispatched where only keyB has a case, and the default
  -- reads the payload back out
  , plain 4
      { code: [ LOADK (Reg 0) (ConstIx 1), VINJ (Reg 1) (KeyIx 0) (Reg 0) ]
      , tail: BRK (Reg 1)
          [ { key: KeyIx 1, body: returning [ LOADK (Reg 2) (ConstIx 0) ] (Reg 2) } ]
          (Just (returning [ VPAY (Reg 3) (KeyIx 0) (Reg 1) ] (Reg 3)))
      }

  -- 5: `0.0` against cases for `-0.0` and `0.0`
  , plain 4
      { code: [ LOADK (Reg 0) (ConstIx 2) ]
      , tail: BRL (Reg 0)
          [ { lit: ConstIx 3, body: returning [ LOADK (Reg 1) (ConstIx 0) ] (Reg 1) }
          , { lit: ConstIx 2, body: returning [ LOADK (Reg 2) (ConstIx 1) ] (Reg 2) }
          ]
          (returning [ LOADC (Reg 3) (CtorIx 1) ] (Reg 3))
      }

  -- 6: a branch on the boolean constant
  , plain 3
      { code: [ LOADK (Reg 0) (ConstIx 4), LOADK (Reg 1) (ConstIx 1) ]
      , tail: BRIF (Reg 0)
          (returning [] (Reg 1))
          (returning [ LOADK (Reg 2) (ConstIx 0) ] (Reg 2))
      }

  -- 7: a join point entered with its own parameters exchanged, which a sequence of
  -- writes would get wrong
  , fn { nparams: 2, nregs: 2, ncaptures: 0 }
      [ { name: JoinName 0, params: [ Reg 0, Reg 1 ], body: returning [] (Reg 0) } ]
      { code: [], tail: JMP (JoinName 0) [ Reg 1, Reg 0 ] }

  -- 8: a capture, which is not a register
  , fn { nparams: 0, nregs: 1, ncaptures: 1 } [] (returning [ CAPT (Reg 0) 0 ] (Reg 0))

  -- 9: a move
  , plain 2 (returning [ LOADK (Reg 0) (ConstIx 1), MOVE (Reg 1) (Reg 0) ] (Reg 1))

  -- 10: a register nothing wrote
  , plain 1 (returning [] (Reg 0))

  -- 11: a key selected from a record that does not carry it
  , plain 2 (returning [ RNEW (Reg 0), RSEL (Reg 1) (KeyIx 0) (Reg 0) ] (Reg 1))

  -- 12: a key extended onto a record already carrying it, which sharp rows make
  -- impossible (D4)
  , plain 4
      ( returning
          [ RNEW (Reg 0)
          , LOADK (Reg 1) (ConstIx 0)
          , REXT (Reg 2) (KeyIx 0) (Reg 1) (Reg 0)
          , REXT (Reg 3) (KeyIx 0) (Reg 1) (Reg 2)
          ]
          (Reg 3)
      )

  -- 13: two records merged over one key
  , plain 4
      ( returning
          [ RNEW (Reg 0)
          , LOADK (Reg 1) (ConstIx 0)
          , REXT (Reg 2) (KeyIx 0) (Reg 1) (Reg 0)
          , RMRG (Reg 3) (Reg 2) (Reg 2)
          ]
          (Reg 3)
      )

  -- 14: a field read at a constructor the value does not carry
  , plain 2
      ( returning
          [ LOADC (Reg 0) (CtorIx 1)
          , FIELD (Reg 1) (Reg 0) (CtorIx 0) 0
          ]
          (Reg 1)
      )

  -- 15: a constructor applied to fewer fields than it has
  , plain 2
      ( returning
          [ LOADK (Reg 0) (ConstIx 0)
          , CTOR (Reg 1) (CtorIx 0) [ Reg 0 ]
          ]
          (Reg 1)
      )

  -- 16: a record operation on a value that is not a record
  , plain 2
      ( returning
          [ LOADK (Reg 0) (ConstIx 0)
          , RSEL (Reg 1) (KeyIx 0) (Reg 0)
          ]
          (Reg 1)
      )

  -- 17: `VABS`, which nothing reaches
  , plain 2 (returning [ LOADK (Reg 0) (ConstIx 0), VABS (Reg 1) (Reg 0) ] (Reg 1))

  -- 18: a cell read through a value that is no region's identity
  , plain 2
      ( returning
          [ LOADK (Reg 0) (ConstIx 0)
          , CGET (Reg 1) (Reg 0) 0
          ]
          (Reg 1)
      )

  -- 19: a constructor of fields, loaded as though it had none
  , plain 1 (returning [ LOADC (Reg 0) (CtorIx 0) ] (Reg 0))

  -- 20: an index naming nothing
  , plain 1 (returning [ LOADK (Reg 0) (ConstIx 9) ] (Reg 0))

  -- 21: an operation this module's `PRIMS` does not hold
  , plain 2
      ( returning
          [ LOADK (Reg 0) (ConstIx 0)
          , PRIM (Reg 1) (PrimIx 0) [ Reg 0, Reg 0 ]
          ]
          (Reg 1)
      )

  -- 22: a dispatch whose cases do not match and which carries no default
  , plain 1
      { code: [ LOADC (Reg 0) (CtorIx 1) ]
      , tail: BRC (Reg 0) [ { ctor: CtorIx 0, body: returning [] (Reg 0) } ] Nothing
      }

  -- 23: the body of a region, handing back the region's identity
  , fn { nparams: 1, nregs: 1, ncaptures: 0 } [] (returning [] (Reg 0))

  -- 24: a cell of a region read after the region has closed, through the identity
  -- its body handed back
  , plain 4
      ( returning
          [ CLOS (Reg 0) (FuncIx 23) []
          , LOADK (Reg 1) (ConstIx 0)
          , RGN (Reg 2) (RegionIx 0) (Reg 0) [ Reg 1 ]
          , CGET (Reg 3) (Reg 2) 0
          ]
          (Reg 3)
      )
  ]

-- | One function under two join points of one name, which loading refuses.
nameTwice :: Function
nameTwice =
  fn { nparams: 0, nregs: 1, ncaptures: 0 }
    [ { name: JoinName 0, params: [], body: returning [] (Reg 0) }
    , { name: JoinName 0, params: [], body: returning [] (Reg 0) }
    ]
    { code: [], tail: JMP (JoinName 0) [] }

loaded :: Loaded
loaded =
  { id: ModuleId 0
  , constants: [ CInt 1, CInt 2, CNumber 0.0, CNumber (-0.0), CBoolean true ]
  , keys: [ keyA, keyB ]
  , ops: []
  , ctors:
      [ { id: pairCtor, arity: 2 }
      , { id: nilCtor, arity: 0 }
      ]
  , foreigns: []
  -- the instructions here name no global, callee, or operation
  , globals: []
  , callees: []
  , prims: []
  , handlers: []
  , regions: [ { cells: [ keyA ] } ]
  , unit: VData (CtorId 999) []
  , functions: Array.mapMaybe prepared functions
  }
  where
  prepared function = case prepare function of
    Right p -> Just p
    Left _ -> Nothing

-- Running one ---------------------------------------------------------------------

-- | A closure over the function of the fixture at that index, and the captures it
-- | was built with.
closureOf :: P.Int -> Map P.Int Value -> Effect Closure
closureOf i captured = do
  captures <- Ref.new captured
  pure { func: { module: ModuleId 0, func: FuncIx i }, captures }

-- | The value a function of the fixture returns, or what ended the run.
runs :: P.Int -> P.Array Value -> Aff (Either Failure Value)
runs = runsWith Map.empty

runsWith :: Map P.Int Value -> P.Int -> P.Array Value -> Aff (Either Failure Value)
runsWith captured i args = liftEffect do
  closure <- closureOf i captured
  runBaseEffect (Except.runExcept (enter registry closure args))

-- | The one module of this fixture, as the registry holds it.
registry :: Registry
registry = Map.fromFoldable [ Tuple (ModuleId 0) loaded ]

-- | What a returned value holds, as far as a test needs it.
data Held
  = AnInt P.Int
  | ANumber P.Number
  | AData CtorId P.Int
  | Elsewhere

held :: Either Failure Value -> Either Failure Held
held = map case _ of
  VInt n -> AnInt n
  VNumber n -> ANumber n
  VData ctor fields -> AData ctor (Array.length fields)
  _ -> Elsewhere

spec :: Spec Unit
spec = describe "Steam.Eval" do

  describe "the fixture" do
    it "holds functions loading accepts" do
      -- every index below stands for the function written under it, which a
      -- refusal would silently shift
      map (const unit) (traverse prepare functions) `shouldEqual` Right unit
      Array.length loaded.functions `shouldEqual` Array.length functions

    it "is refused where one name stands over two join points" do
      map (const unit) (prepare nameTwice) `shouldEqual` Left (JoinName 0)

  describe "records" do
    it "extends and selects" do
      result <- runs 0 []
      held result `shouldEqual` Right (AnInt 2)

    it "updates, restricts, and merges" do
      result <- runs 1 []
      held result `shouldEqual` Right (AnInt 1)

  describe "data" do
    it "builds a constructor value and reads a field of it" do
      result <- runs 2 []
      held result `shouldEqual` Right (AnInt 2)

    it "dispatches on the constructor a value carries" do
      result <- runs 3 []
      held result `shouldEqual` Right (AnInt 2)

  describe "variants" do
    it "takes the default where no case carries the key, and reads the payload" do
      result <- runs 4 []
      held result `shouldEqual` Right (AnInt 2)

  describe "literals" do
    it "separates 0.0 from -0.0, which the host's equality does not (D37)" do
      result <- runs 5 []
      held result `shouldEqual` Right (AnInt 2)

  describe "control" do
    it "branches on a boolean" do
      result <- runs 6 []
      held result `shouldEqual` Right (AnInt 2)

    it "enters a join point with its arguments exchanged" do
      result <- runs 7 [ VInt 1, VInt 2 ]
      held result `shouldEqual` Right (AnInt 2)

    it "reads a capture of the closure it was entered through" do
      result <- runsWith (Map.singleton 0 (VInt 7)) 8 []
      held result `shouldEqual` Right (AnInt 7)

    it "moves a register" do
      result <- runs 9 []
      held result `shouldEqual` Right (AnInt 2)

  describe "what no .dmo admits" do
    it "a register nothing wrote" do
      result <- runs 10 []
      held result `shouldEqual` Left (Bug (RegisterHoldsNothing (Reg 0)))

    it "a capture slot nothing filled" do
      result <- runs 8 []
      held result `shouldEqual` Left (Bug (CaptureHoldsNothing 0))

    it "a key a record does not carry" do
      result <- runs 11 []
      held result `shouldEqual` Left (Bug (KeyAbsent keyA))

    it "a key extended twice" do
      result <- runs 12 []
      held result `shouldEqual` Left (Bug (KeyPresent keyA))

    it "two records merged over one key" do
      result <- runs 13 []
      held result `shouldEqual` Left (Bug (KeyPresent keyA))

    it "a field read at another constructor" do
      result <- runs 14 []
      held result `shouldEqual` Left (Bug (CtorMismatch pairCtor nilCtor))

    it "a constructor applied to too few fields" do
      result <- runs 15 []
      held result `shouldEqual` Left (Bug (WrongCtorArity pairCtor 2 1))

    it "a record operation on something else" do
      result <- runs 16 []
      held result `shouldEqual` Left (Bug (NotOfClass ARecord))

    it "VABS, which nothing reaches" do
      result <- runs 17 []
      held result `shouldEqual` Left (Bug Unreachable)

    it "a constructor of fields loaded as though it had none" do
      result <- runs 19 []
      held result `shouldEqual` Left (Bug (WrongCtorArity pairCtor 2 0))

    it "an index naming nothing" do
      result <- runs 20 []
      held result `shouldEqual` Left (Bug (NoSuchConstant (ConstIx 9)))

    it "arguments the function does not take" do
      result <- runs 0 [ VInt 1 ]
      held result `shouldEqual` Left (Bug (WrongArgumentCount (FuncIx 0) 0 1))

    it "an index naming nothing in PRIMS" do
      result <- runs 21 []
      held result `shouldEqual` Left (Bug (NoSuchPrim (PrimIx 0)))

    it "a dispatch with no case and no default" do
      result <- runs 22 []
      held result `shouldEqual` Left (Bug NoBranchTaken)

    it "a closure of a module the registry does not hold" do
      -- the closure says which function runs, and the module it belongs to is
      -- where that function is found
      result <- liftEffect do
        captures <- Ref.new Map.empty
        let elsewhere = { func: { module: ModuleId 1, func: FuncIx 0 }, captures }
        runBaseEffect (Except.runExcept (enter registry elsewhere []))
      held result `shouldEqual` Left (Bug (NoSuchModule (ModuleId 1)))

    it "a cell read through a value that is no region's identity" do
      result <- runs 18 []
      held result `shouldEqual` Left (Bug NotARegion)

    it "a cell of a region no longer open" do
      -- typing rules this out: an identity reaches no code running where its region
      -- has closed
      result <- runs 24 []
      held result `shouldEqual` Left (Bug RegionNotOpen)

derive instance Eq Held
derive instance Generic Held _

instance Show Held where
  show = genericShow
