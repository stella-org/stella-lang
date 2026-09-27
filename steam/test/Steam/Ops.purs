-- | The operations of `stella-base-0.1`, as this interpreter carries them out.
-- |
-- | What each one means is the ABI's
-- | ([Prim and Base](../../../docs/technical-references/06-Modules/02-Prim-and-Base.md)),
-- | so these cases are that document read back: arithmetic wraps and faults on
-- | nothing, a length counts scalar values, an index outside a string or an array
-- | faults, and a negative slot count faults.
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
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..))
import Data.Show.Generic (genericShow)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Steam.Fault (Fault(..))
import Steam.Op (Refusal(..), carryOut, implemented)
import Steam.Value (CtorId(..), Opaque, Value(..))
import Stella.Compiler.Primitive (PrimOp(..), primTable)
import Stella.Compiler.TypedCore.Domain (ScalarString, codePointOf, scalarString)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

-- | An opaque value that is a bare host array, which a different entry might hand
-- | back. It is what separates a brand from a shape test: `Array.isArray` accepts
-- | this and the brand the payload carries does not.
foreign import notAnArray :: Opaque

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
  | AnArray
  | Elsewhere

held :: Either Refusal Value -> Either Refusal Held
held = map case _ of
  VInt n -> AnInt n
  VChar c -> AChar (codePointOf c)
  VOpaque _ -> AnArray
  VData ctor [] -> AData ctor
  _ -> Elsewhere

-- | One operation carried out, as far as a test reads it.
runs :: PrimOp -> P.Array Value -> Aff (Either Refusal Held)
runs op args = liftEffect (map held (carryOut unitValue op args))

-- | The same, keeping the value so a later operation can be handed it.
produces :: PrimOp -> P.Array Value -> Aff (Either Refusal Value)
produces op args = liftEffect (carryOut unitValue op args)

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

  it "carries out every operation of the version, each exactly once" do
    -- a code this interpreter does not implement is a load error, so an operation
    -- missing here refuses a module the version admits. Counting alone would let a
    -- duplicate cover an omission, which is why the entries are compared
    implemented `shouldEqual` map _.op primTable

  describe "arithmetic" do
    it "adds and subtracts" do
      runs IntAdd [ VInt 2, VInt 3 ] >>= (_ `shouldEqual` Right (AnInt 5))
      runs IntSub [ VInt 2, VInt 3 ] >>= (_ `shouldEqual` Right (AnInt (-1)))

    it "wraps at 32 bits, and faults on nothing" do
      -- what every backend owes, whatever its host does on overflow
      runs IntAdd [ VInt maxInt, VInt 1 ] >>= (_ `shouldEqual` Right (AnInt minInt))
      runs IntSub [ VInt minInt, VInt 1 ] >>= (_ `shouldEqual` Right (AnInt maxInt))

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
