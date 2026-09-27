-- | The operations of `stella-base-0.1`, as this interpreter carries them out.
-- |
-- | What each one means is the ABI's
-- | ([Prim and Base](../../../docs/technical-references/06-Modules/02-Prim-and-Base.md)),
-- | so these cases are that document read back, and above all its cases where a
-- | host's own operator gives another answer: arithmetic wraps, division truncates and
-- | faults on a zero divisor, a `Number` compares by IEEE 754, a string is ordered by
-- | scalar value, and a bound or an index outside what it indexes faults.
-- |
-- | **Reading a slot nothing wrote is not here.** It violates the precondition of
-- | `Base.Array.unsafeIndex`, so a case asserting what this interpreter produces
-- | would be fixing what the specification declines to fix (D42). Nor is the
-- | converse asserted: a backend that tracked written slots and faulted would be
-- | conformant, so "no initialization bit is kept" is a decision of this
-- | interpreter rather than a property to test.
module Test.Steam.Ops (spec) where

import Prelude

import Prim as P

import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..), fromJust)
import Partial.Unsafe (unsafePartial)
import Data.Show.Generic (genericShow)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Steam.Fault (Fault(..))
import Steam.Op (Refusal(..), carryOut)
import Steam.Value (CtorId(..), Opaque, Value(..))
import Stella.Compiler.Primitive (PrimOp(..), primTable)
import Stella.Compiler.TypedCore.Domain (ScalarString, codePointOf, scalarString, scalarValue, textOf)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

-- | An opaque value that is a bare host array, which a different entry might hand
-- | back. It is what separates a brand from a shape test: `Array.isArray` accepts
-- | this and the brand the payload carries does not.
foreign import notAnArray :: Opaque

foreign import describeNumber :: P.Number -> P.String

foreign import nan :: P.Number

-- | The largest and smallest `Int`, which is where wrapping shows.
maxInt :: P.Int
maxInt = 2147483647

minInt :: P.Int
minInt = -2147483648

-- | Two scalar values and an astral one, which a count of code units would get
-- | wrong.
text :: Maybe ScalarString
text = scalarString "a😀"

-- | `Prim.Unit` under an identity of this fixture's choosing. **The identity is
-- | what the cases check**: `carryOut` takes it as an argument so that a write
-- | answers with the value the registry assigned, and one built inside would
-- | compare unequal to every other `Prim.Unit` in the program.
unitCtorId :: CtorId
unitCtorId = CtorId 77

unitValue :: Value
unitValue = VData unitCtorId []

-- | What an operation produced, as far as a test needs it.
data Held
  = AnInt P.Int
  | AChar P.Int
  | AData CtorId
  | ANumber P.String
  | ABoolean P.Boolean
  | AString P.String
  | AnArray
  | Elsewhere

held :: Either Refusal Value -> Either Refusal Held
held = map case _ of
  VInt n -> AnInt n
  VChar c -> AChar (codePointOf c)
  VNumber x -> ANumber (describeNumber x)
  VBoolean b -> ABoolean b
  VString s -> AString (textOf s)
  VOpaque _ -> AnArray
  VData ctor [] -> AData ctor
  _ -> Elsewhere

-- | One operation carried out, as far as a test reads it.
runs :: PrimOp -> P.Array Value -> Aff (Either Refusal Held)
runs op args = liftEffect (map held (carryOut unitValue op args))

-- | The same, keeping the value so a later operation can be handed it.
produces :: PrimOp -> P.Array Value -> Aff (Either Refusal Value)
produces op args = liftEffect (carryOut unitValue op args)

-- | A string or a character the cases write out, each a scalar value by construction.
str :: P.String -> Value
str s = VString (unsafePartial (fromJust (scalarString s)))

char :: P.Int -> Value
char code = VChar (unsafePartial (fromJust (scalarValue code)))

-- | One set of operands each operation takes, `array` standing for the array an
-- | entry of `Base.Array` is handed.
-- |
-- | **Every operation is named, and nothing falls to a default**, so an operation the
-- | version gains is one this does not compile without.
operandsOf :: Value -> PrimOp -> P.Array Value
operandsOf array = case _ of
  IntAdd -> [ VInt 1, VInt 2 ]
  IntSub -> [ VInt 1, VInt 2 ]
  IntMul -> [ VInt 1, VInt 2 ]
  IntQuot -> [ VInt 1, VInt 2 ]
  IntRem -> [ VInt 1, VInt 2 ]
  IntEq -> [ VInt 1, VInt 2 ]
  IntLt -> [ VInt 1, VInt 2 ]
  IntToNumber -> [ VInt 1 ]
  IntToString -> [ VInt 1 ]
  NumberAdd -> [ VNumber 1.0, VNumber 2.0 ]
  NumberSub -> [ VNumber 1.0, VNumber 2.0 ]
  NumberMul -> [ VNumber 1.0, VNumber 2.0 ]
  NumberDivide -> [ VNumber 1.0, VNumber 2.0 ]
  NumberNegate -> [ VNumber 1.0 ]
  NumberEq -> [ VNumber 1.0, VNumber 2.0 ]
  NumberLt -> [ VNumber 1.0, VNumber 2.0 ]
  NumberFloor -> [ VNumber 1.5 ]
  NumberCeil -> [ VNumber 1.5 ]
  NumberTrunc -> [ VNumber 1.5 ]
  NumberToInt -> [ VNumber 1.5 ]
  NumberToString -> [ VNumber 1.5 ]
  StringLength -> [ str "ab" ]
  StringCodePointAt -> [ VInt 0, str "ab" ]
  StringAppend -> [ str "a", str "b" ]
  StringSlice -> [ VInt 0, VInt 1, str "ab" ]
  StringSingleton -> [ char 0x61 ]
  StringEq -> [ str "a", str "b" ]
  StringLt -> [ str "a", str "b" ]
  CharToCodePoint -> [ char 0x61 ]
  CharFromCodePoint -> [ VInt 0x61 ]
  ArrayLength -> [ array ]
  ArrayUnsafeNew -> [ VInt 1 ]
  ArrayUnsafeSet -> [ VInt 0, VInt 1, array ]
  ArrayUnsafeIndex -> [ array, VInt 0 ]

-- | An array of that many slots, or a failure the case reports.
arrayOf :: P.Int -> Aff Value
arrayOf n = do
  outcome <- produces ArrayUnsafeNew [ VInt n ]
  case outcome of
    Right value -> pure value
    Left refusal -> do
      fail ("unsafeNew " <> show n <> " refused: " <> show refusal)
      pure (VInt 0)

spec :: Spec Unit
spec = describe "Steam.Op" do

  -- a code this interpreter does not implement is a load error, so an operation it
  -- lists but does not carry out would admit a module and then refuse its operands.
  -- Each is run once on operands it takes, and what is asserted is only that it was
  -- carried out: a value or a fault, and never operands refused
  it "carries out every operation of the version, on operands it takes" do
    array <- arrayOf 1
    for_ primTable \{ op } -> do
      outcome <- runs op (operandsOf array op)
      case outcome of
        Left WrongOperands -> fail (show op <> " refused operands it takes")
        Left (NotImplemented _) -> fail (show op <> " is not carried out")
        _ -> pure unit

  describe "arithmetic" do
    it "adds and subtracts" do
      runs IntAdd [ VInt 2, VInt 3 ] >>= (_ `shouldEqual` Right (AnInt 5))
      runs IntSub [ VInt 2, VInt 3 ] >>= (_ `shouldEqual` Right (AnInt (-1)))

    it "wraps at 32 bits, and faults on nothing" do
      -- what every backend owes, whatever its host does on overflow
      runs IntAdd [ VInt maxInt, VInt 1 ] >>= (_ `shouldEqual` Right (AnInt minInt))
      runs IntSub [ VInt minInt, VInt 1 ] >>= (_ `shouldEqual` Right (AnInt maxInt))

  describe "integer arithmetic" do
    it "multiplies modulo 2³², keeping the low bits binary64 would lose" do
      runs IntMul [ VInt 65536, VInt 65536 ] >>= (_ `shouldEqual` Right (AnInt 0))
      -- the exact product needs more than 53 bits, so a multiplication through
      -- binary64 answers `0` here
      runs IntMul [ VInt maxInt, VInt maxInt ] >>= (_ `shouldEqual` Right (AnInt 1))

    it "divides towards zero, the remainder taking the dividend's sign" do
      runs IntQuot [ VInt 7, VInt (-2) ] >>= (_ `shouldEqual` Right (AnInt (-3)))
      runs IntRem [ VInt (-7), VInt 2 ] >>= (_ `shouldEqual` Right (AnInt (-1)))

    -- the one overflow division has, where a host that traps checks first
    it "wraps minInt divided by -1, and leaves no remainder" do
      runs IntQuot [ VInt minInt, VInt (-1) ] >>= (_ `shouldEqual` Right (AnInt minInt))
      runs IntRem [ VInt minInt, VInt (-1) ] >>= (_ `shouldEqual` Right (AnInt 0))

    it "faults on a zero divisor rather than answering 0" do
      runs IntQuot [ VInt 1, VInt 0 ] >>= (_ `shouldEqual` Left (Faulted (ZeroDivisor 1)))
      runs IntRem [ VInt 1, VInt 0 ] >>= (_ `shouldEqual` Left (Faulted (ZeroDivisor 1)))

    it "compares with eq and lt" do
      runs IntEq [ VInt 3, VInt 3 ] >>= (_ `shouldEqual` Right (ABoolean true))
      runs IntLt [ VInt minInt, VInt maxInt ] >>= (_ `shouldEqual` Right (ABoolean true))
      runs IntLt [ VInt 3, VInt 3 ] >>= (_ `shouldEqual` Right (ABoolean false))

    it "converts to a Number exactly, and to a decimal numeral" do
      runs IntToNumber [ VInt minInt ] >>= (_ `shouldEqual` Right (ANumber "-2147483648"))
      runs IntToString [ VInt minInt ] >>= (_ `shouldEqual` Right (AString "-2147483648"))
      runs IntToString [ VInt 0 ] >>= (_ `shouldEqual` Right (AString "0"))

  describe "number arithmetic" do
    it "is IEEE 754 binary64, a zero divisor included" do
      runs NumberAdd [ VNumber 0.1, VNumber 0.2 ]
        >>= (_ `shouldEqual` Right (ANumber "0.30000000000000004"))
      runs NumberSub [ VNumber 0.3, VNumber 0.1 ]
        >>= (_ `shouldEqual` Right (ANumber "0.19999999999999998"))
      runs NumberMul [ VNumber 0.1, VNumber 3.0 ]
        >>= (_ `shouldEqual` Right (ANumber "0.30000000000000004"))
      runs NumberMul [ VNumber (-2.0), VNumber 0.0 ] >>= (_ `shouldEqual` Right (ANumber "-0"))
      runs NumberDivide [ VNumber 1.0, VNumber 0.0 ] >>= (_ `shouldEqual` Right (ANumber "Infinity"))
      runs NumberDivide [ VNumber 0.0, VNumber 0.0 ] >>= (_ `shouldEqual` Right (ANumber "NaN"))

    -- which is why the entry exists: no subtraction produces `-0.0`
    it "negates 0.0 to -0.0" do
      runs NumberNegate [ VNumber 0.0 ] >>= (_ `shouldEqual` Right (ANumber "-0"))
      runs NumberSub [ VNumber 0.0, VNumber 0.0 ] >>= (_ `shouldEqual` Right (ANumber "0"))

    -- the opposite of literal identity in both, which a `switchLit` keeps deciding by
    it "compares by IEEE 754 and not by literal identity" do
      runs NumberEq [ VNumber nan, VNumber nan ] >>= (_ `shouldEqual` Right (ABoolean false))
      runs NumberEq [ VNumber 0.0, VNumber (-0.0) ] >>= (_ `shouldEqual` Right (ABoolean true))
      runs NumberLt [ VNumber nan, VNumber 1.0 ] >>= (_ `shouldEqual` Right (ABoolean false))
      runs NumberLt [ VNumber 1.0, VNumber nan ] >>= (_ `shouldEqual` Right (ABoolean false))

    it "rounds to an integral value in the direction each names" do
      runs NumberFloor [ VNumber (-0.5) ] >>= (_ `shouldEqual` Right (ANumber "-1"))
      runs NumberCeil [ VNumber (-0.5) ] >>= (_ `shouldEqual` Right (ANumber "-0"))
      runs NumberTrunc [ VNumber (-0.5) ] >>= (_ `shouldEqual` Right (ANumber "-0"))
      runs NumberFloor [ VNumber nan ] >>= (_ `shouldEqual` Right (ANumber "NaN"))

    -- a conversion by `| 0` answers `1410065408` for `1e10`
    it "converts to an Int by truncating and saturating" do
      runs NumberToInt [ VNumber nan ] >>= (_ `shouldEqual` Right (AnInt 0))
      runs NumberToInt [ VNumber 1.0e10 ] >>= (_ `shouldEqual` Right (AnInt maxInt))
      runs NumberToInt [ VNumber (-1.0e10) ] >>= (_ `shouldEqual` Right (AnInt minInt))
      runs NumberToInt [ VNumber (-2.9) ] >>= (_ `shouldEqual` Right (AnInt (-2)))

    it "writes the numeral ECMA-262's Number::toString gives" do
      runs NumberToString [ VNumber 1.0e21 ] >>= (_ `shouldEqual` Right (AString "1e+21"))
      runs NumberToString [ VNumber 1.0e20 ]
        >>= (_ `shouldEqual` Right (AString "100000000000000000000"))
      runs NumberToString [ VNumber 1.0e-7 ] >>= (_ `shouldEqual` Right (AString "1e-7"))
      runs NumberToString [ VNumber 0.1 ] >>= (_ `shouldEqual` Right (AString "0.1"))
      runs NumberToString [ VNumber (-0.0) ] >>= (_ `shouldEqual` Right (AString "0"))

  describe "strings" do
    it "counts scalar values rather than code units" do
      case text of
        Nothing -> fail "the fixture is a scalar string"
        Just s -> runs StringLength [ VString s ] >>= (_ `shouldEqual` Right (AnInt 2))

    it "indexes by scalar value, astral characters among them" do
      case text of
        Nothing -> fail "the fixture is a scalar string"
        Just s -> do
          runs StringCodePointAt [ VInt 0, VString s ]
            >>= (_ `shouldEqual` Right (AChar 0x61))
          runs StringCodePointAt [ VInt 1, VString s ]
            >>= (_ `shouldEqual` Right (AChar 0x1F600))

    it "faults outside the string" do
      case text of
        Nothing -> fail "the fixture is a scalar string"
        Just s -> do
          runs StringCodePointAt [ VInt 2, VString s ]
            >>= (_ `shouldEqual` Left (Faulted (IndexOutsideString 2 2)))
          runs StringCodePointAt [ VInt (-1), VString s ]
            >>= (_ `shouldEqual` Left (Faulted (IndexOutsideString (-1) 2)))

    it "appends, and makes a string of one character" do
      runs StringAppend [ str "a😀", str "b" ] >>= (_ `shouldEqual` Right (AString "a😀b"))
      runs StringSingleton [ char 0x1F600 ] >>= (_ `shouldEqual` Right (AString "😀"))

    it "slices by scalar index" do
      runs StringSlice [ VInt 1, VInt 3, str "a😀bc" ] >>= (_ `shouldEqual` Right (AString "😀b"))
      runs StringSlice [ VInt 2, VInt 2, str "ab" ] >>= (_ `shouldEqual` Right (AString ""))

    -- a host's own `slice` clamps, and counts a negative index from the end
    it "faults on bounds out of order, past the end, or negative" do
      runs StringSlice [ VInt 2, VInt 1, str "abc" ]
        >>= (_ `shouldEqual` Left (Faulted (SliceOutsideString 2 1 3)))
      runs StringSlice [ VInt 0, VInt 4, str "abc" ]
        >>= (_ `shouldEqual` Left (Faulted (SliceOutsideString 0 4 3)))
      runs StringSlice [ VInt (-1), VInt 2, str "abc" ]
        >>= (_ `shouldEqual` Left (Faulted (SliceOutsideString (-1) 2 3)))
      runs StringSlice [ VInt 0, VInt (-1), str "abc" ]
        >>= (_ `shouldEqual` Left (Faulted (SliceOutsideString 0 (-1) 3)))

    -- JavaScript's `<` compares UTF-16 code units and says false here
    it "orders by scalar value, a proper prefix first" do
      runs StringLt [ str "\xE000", str "😀" ] >>= (_ `shouldEqual` Right (ABoolean true))
      runs StringLt [ str "ab", str "abc" ] >>= (_ `shouldEqual` Right (ABoolean true))
      runs StringLt [ str "abc", str "abc" ] >>= (_ `shouldEqual` Right (ABoolean false))
      runs StringEq [ str "a😀", str "a😀" ] >>= (_ `shouldEqual` Right (ABoolean true))

  describe "characters" do
    it "converts to its scalar value and back" do
      runs CharToCodePoint [ char 0x1F600 ] >>= (_ `shouldEqual` Right (AnInt 0x1F600))
      runs CharFromCodePoint [ VInt 0x1F600 ] >>= (_ `shouldEqual` Right (AChar 0x1F600))

    it "faults on a code that names no scalar value" do
      runs CharFromCodePoint [ VInt 0xD800 ]
        >>= (_ `shouldEqual` Left (Faulted (NotAScalarValue 0xD800)))
      runs CharFromCodePoint [ VInt 0x110000 ]
        >>= (_ `shouldEqual` Left (Faulted (NotAScalarValue 0x110000)))
      runs CharFromCodePoint [ VInt (-1) ]
        >>= (_ `shouldEqual` Left (Faulted (NotAScalarValue (-1))))

  describe "arrays" do
    it "allocates the slots it was asked for, and reports that count back" do
      array <- arrayOf 3
      runs ArrayLength [ array ] >>= (_ `shouldEqual` Right (AnInt 3))

    it "allocates none where the count is zero, which is not an error" do
      array <- arrayOf 0
      runs ArrayLength [ array ] >>= (_ `shouldEqual` Right (AnInt 0))

    it "faults on a negative count" do
      runs ArrayUnsafeNew [ VInt (-1) ]
        >>= (_ `shouldEqual` Left (Faulted (NegativeArrayLength (-1))))

    -- the whole of what the pair is for, and what a machine copying an array on
    -- write would fail while passing everything else here
    it "reads back what was written into a slot" do
      array <- arrayOf 2
      -- the write answers with the `Prim.Unit` it was handed, identity and all: a
      -- nullary constructor of any other identity would be a different value
      runs ArrayUnsafeSet [ VInt 1, VInt 42, array ]
        >>= (_ `shouldEqual` Right (AData unitCtorId))
      runs ArrayUnsafeIndex [ array, VInt 1 ] >>= (_ `shouldEqual` Right (AnInt 42))

    it "writes the slot again, and the later write is what is read" do
      array <- arrayOf 1
      _ <- runs ArrayUnsafeSet [ VInt 0, VInt 1, array ]
      _ <- runs ArrayUnsafeSet [ VInt 0, VInt 2, array ]
      runs ArrayUnsafeIndex [ array, VInt 0 ] >>= (_ `shouldEqual` Right (AnInt 2))

    -- two calls of `unsafeNew` give two arrays, which is the identity that makes
    -- the entry observational (D41)
    it "gives two arrays for two allocations of one count" do
      one <- arrayOf 1
      other <- arrayOf 1
      _ <- runs ArrayUnsafeSet [ VInt 0, VInt 7, one ]
      _ <- runs ArrayUnsafeSet [ VInt 0, VInt 8, other ]
      runs ArrayUnsafeIndex [ one, VInt 0 ] >>= (_ `shouldEqual` Right (AnInt 7))

    it "faults on an index outside the array, and leaves it as it was" do
      array <- arrayOf 2
      _ <- runs ArrayUnsafeSet [ VInt 0, VInt 5, array ]
      runs ArrayUnsafeSet [ VInt 2, VInt 9, array ]
        >>= (_ `shouldEqual` Left (Faulted (IndexOutsideArray 2 2)))
      runs ArrayUnsafeSet [ VInt (-1), VInt 9, array ]
        >>= (_ `shouldEqual` Left (Faulted (IndexOutsideArray (-1) 2)))
      runs ArrayLength [ array ] >>= (_ `shouldEqual` Right (AnInt 2))
      runs ArrayUnsafeIndex [ array, VInt 0 ] >>= (_ `shouldEqual` Right (AnInt 5))

    it "faults on a read outside the array" do
      array <- arrayOf 2
      runs ArrayUnsafeIndex [ array, VInt 2 ]
        >>= (_ `shouldEqual` Left (Faulted (IndexOutsideArray 2 2)))
      runs ArrayUnsafeIndex [ array, VInt (-1) ]
        >>= (_ `shouldEqual` Left (Faulted (IndexOutsideArray (-1) 2)))

    it "carries an array as an opaque value, whatever it holds" do
      array <- arrayOf 1
      runs ArrayUnsafeNew [ VInt 1 ] >>= (_ `shouldEqual` Right AnArray)
      -- an array holds the interpreter's values, an array among them
      _ <- runs ArrayUnsafeSet [ VInt 0, array, array ]
      runs ArrayUnsafeIndex [ array, VInt 0 ] >>= (_ `shouldEqual` Right AnArray)

  describe "what is not an operation's to decide" do
    it "refuses operands it does not take" do
      runs IntAdd [ VInt 1 ] >>= (_ `shouldEqual` Left WrongOperands)
      runs IntAdd [ VInt 1, VBoolean true ] >>= (_ `shouldEqual` Left WrongOperands)

    it "refuses an array entry handed something that is not an array" do
      runs ArrayLength [ VInt 1 ] >>= (_ `shouldEqual` Left WrongOperands)
      runs ArrayUnsafeIndex [ VInt 1, VInt 0 ] >>= (_ `shouldEqual` Left WrongOperands)

    -- what the brand buys: a `.dmo` carries no type, so an opaque value another
    -- entry produced reaches here, and writing through one would corrupt whatever
    -- that entry holds
    it "refuses an opaque value another entry produced, array-shaped or not" do
      runs ArrayLength [ VOpaque notAnArray ] >>= (_ `shouldEqual` Left WrongOperands)
      runs ArrayUnsafeIndex [ VOpaque notAnArray, VInt 0 ]
        >>= (_ `shouldEqual` Left WrongOperands)
      runs ArrayUnsafeSet [ VInt 0, VInt 1, VOpaque notAnArray ]
        >>= (_ `shouldEqual` Left WrongOperands)

derive instance Eq Held
derive instance Generic Held _

instance Show Held where
  show = genericShow
