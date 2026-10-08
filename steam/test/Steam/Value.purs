-- | What a constant becomes, and what copying a segment owes an application.
-- |
-- | The interesting half of `matchesConstant` is `Number`: identity is equality of
-- | the bit pattern with all NaNs taken as one (D37), which the host's `==` decides
-- | neither way.
-- |
-- | `reinstate` is what one application of a continuation pushes: it keeps two
-- | applications from sharing the state that was captured, and it keeps the
-- | identity of every region frame it copies. Applying one is the machine's, and
-- | what is fixed here are the invariants every application rests on.
module Test.Steam.Value (spec) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Foldable (traverse_)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Traversable (traverse)
import Effect (Effect)
import Effect.Class (liftEffect)
import Effect.Ref as Ref
import Steam.Region as Region
import Steam.Value (Continuation(..), ModuleId(..), RegionId, StackEntry(..), Value(..), matchesConstant, reinstate, valueOfConstant)
import Stella.Compiler.Bytecode.Instr (FuncIx(..), Reg(..), Tail(..))
import Stella.Compiler.Bytecode.Module (Constant(..))
import Stella.Compiler.TypedCore.Domain (ScalarString, ScalarValue, scalarString, scalarValue)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

nan :: P.Number
nan = 0.0 / 0.0

infinity :: P.Number
infinity = 1.0 / 0.0

-- | `A`, which every `Char` case here stands on.
letterA :: Maybe ScalarValue
letterA = scalarValue 0x41

letterB :: Maybe ScalarValue
letterB = scalarValue 0x42

text :: P.String -> Maybe ScalarString
text = scalarString

-- | What a constant of the pool becomes, asked of itself. Every constant is the
-- | value it stands for, which is the first thing `LOADK` and `BRL` have to
-- | agree on.
carries :: Constant -> P.Boolean
carries c = matchesConstant (valueOfConstant c) c

-- A segment, and what it holds ---------------------------------------------------

-- | A segment holding one activation's register and one region cell, which is
-- | everything an application of a continuation can change, the region under the
-- | identity given.
segmentOf :: RegionId -> P.Int -> P.Int -> Effect (P.Array StackEntry)
segmentOf identity inRegister inCell = do
  captures <- Ref.new Map.empty
  regs <- Ref.new (Map.singleton (Reg 0) (VInt inRegister))
  cell <- Ref.new (VInt inCell)
  let
    func = { module: ModuleId 0, func: FuncIx 0 }
    activation =
      { func
      , closure: { func, captures }
      , regs
      , node: { code: [], tail: RET (Reg 0) }
      , ip: 0
      }
  pure
    [ Resume activation (Reg 1)
    , RegionFrame { identity, cells: [ cell ] }
    ]

-- | A fresh segment, under an identity of its own.
freshSegment :: P.Int -> P.Int -> Effect (P.Array StackEntry)
freshSegment inRegister inCell = do
  identity <- Region.fresh
  segmentOf identity inRegister inCell

-- | Whether each region frame a segment holds stands under that identity, in the
-- | order its entries stand.
under :: RegionId -> P.Array StackEntry -> P.Array (Maybe P.Boolean)
under identity = map case _ of
  RegionFrame region -> Just (Region.same region.identity identity)
  _ -> Nothing

-- | The integers a segment holds, in the order its entries stand.
holds :: P.Array StackEntry -> Effect (P.Array (Maybe P.Int))
holds = traverse entry
  where
  entry = case _ of
    Resume activation _ -> map (register <=< Map.lookup (Reg 0)) (Ref.read activation.regs)
    RegionFrame region -> case Array.head region.cells of
      Just cell -> map register (Ref.read cell)
      Nothing -> pure Nothing
    _ -> pure Nothing

  register = case _ of
    VInt n -> Just n
    _ -> Nothing

-- | What one application does to the state it was given.
writeInto :: P.Array StackEntry -> P.Int -> P.Int -> Effect Unit
writeInto segment inRegister inCell = traverse_ entry segment
  where
  entry = case _ of
    Resume activation _ -> Ref.modify_ (Map.insert (Reg 0) (VInt inRegister)) activation.regs
    RegionFrame region -> traverse_ (Ref.write (VInt inCell)) region.cells
    _ -> pure unit

spec :: Spec Unit
spec = describe "Steam.Value" do

  describe "a constant is the value it stands for" do
    it "carries an Int, a Boolean, a Char, and a String" do
      carries (CInt 42) `shouldEqual` true
      carries (CInt (-1)) `shouldEqual` true
      carries (CBoolean false) `shouldEqual` true
      case letterA, text "ab" of
        Just a, Just s -> do
          carries (CChar a) `shouldEqual` true
          carries (CString s) `shouldEqual` true
        _, _ -> fail "the fixtures are scalar values"

    it "carries a Number, NaN and the zeros among them" do
      carries (CNumber 1.5) `shouldEqual` true
      carries (CNumber 0.0) `shouldEqual` true
      carries (CNumber (-0.0)) `shouldEqual` true
      carries (CNumber nan) `shouldEqual` true
      carries (CNumber infinity) `shouldEqual` true

  describe "what a literal is identical to" do
    it "separates the two zeros, which the host's equality does not" do
      matchesConstant (VNumber 0.0) (CNumber (-0.0)) `shouldEqual` false
      matchesConstant (VNumber (-0.0)) (CNumber 0.0) `shouldEqual` false

    it "makes every NaN one literal, which the host's equality does not" do
      matchesConstant (VNumber nan) (CNumber nan) `shouldEqual` true
      matchesConstant (VNumber (nan * 2.0)) (CNumber nan) `shouldEqual` true
      matchesConstant (VNumber nan) (CNumber 1.0) `shouldEqual` false

    it "distinguishes values of one class" do
      matchesConstant (VInt 1) (CInt 2) `shouldEqual` false
      matchesConstant (VBoolean true) (CBoolean false) `shouldEqual` false
      case letterA, letterB of
        Just a, Just b -> matchesConstant (VChar a) (CChar b) `shouldEqual` false
        _, _ -> fail "the fixtures are scalar values"

    it "compares a String by the scalar values it holds" do
      case text "ab", text "ab", text "abc" of
        Just s, Just same, Just longer -> do
          matchesConstant (VString s) (CString same) `shouldEqual` true
          matchesConstant (VString s) (CString longer) `shouldEqual` false
        _, _, _ -> fail "the fixtures are scalar strings"

    it "is false where the classes differ, a question no dispatch asks" do
      matchesConstant (VInt 1) (CNumber 1.0) `shouldEqual` false
      matchesConstant (VNumber 1.0) (CInt 1) `shouldEqual` false
      matchesConstant (VBoolean true) (CInt 1) `shouldEqual` false

  describe "what one application of a continuation is given" do
    it "gives a second application the state that was captured" do
      -- what the first application wrote is its own, and the second begins where
      -- the capture left off (D33)
      values <- liftEffect do
        segment <- freshSegment 1 10
        first <- reinstate (Continuation segment)
        writeInto first 2 20
        second <- reinstate (Continuation segment)
        holds second
      values `shouldEqual` [ Just 1, Just 10 ]

    it "leaves the captured segment as it was" do
      values <- liftEffect do
        segment <- freshSegment 1 10
        clone <- reinstate (Continuation segment)
        writeInto clone 2 20
        holds segment
      values `shouldEqual` [ Just 1, Just 10 ]

    it "gives each application a state of its own" do
      values <- liftEffect do
        segment <- freshSegment 1 10
        first <- reinstate (Continuation segment)
        second <- reinstate (Continuation segment)
        writeInto first 2 20
        holds second
      values `shouldEqual` [ Just 1, Just 10 ]

    it "keeps the identity of every region frame it copies" do
      -- the code the segment holds, and every closure made before the capture,
      -- name the region by its identity, and a copy is what they must reach
      sameness <- liftEffect do
        identity <- Region.fresh
        segment <- segmentOf identity 1 10
        copy <- reinstate (Continuation segment)
        pure (under identity copy)
      sameness `shouldEqual` [ Nothing, Just true ]

    it "gives no two openings one identity" do
      sameness <- liftEffect do
        identity <- Region.fresh
        other <- freshSegment 1 10
        pure (under identity other)
      sameness `shouldEqual` [ Nothing, Just false ]
