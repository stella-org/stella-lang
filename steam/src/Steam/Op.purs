-- | Carrying out an operation of `stella-base-0.1`
-- | ([Prim and Base](../../../docs/technical-references/06-Modules/02-Prim-and-Base.md)).
-- |
-- | An **operation** is a `Base` ABI entry a machine carries out itself rather than
-- | through a foreign implementation. What each one means, and which of them may
-- | fault, is the ABI's and is one meaning for every backend; this module is where
-- | this interpreter implements what is written there.
module Steam.Op
  ( Refusal(..)
  , carryOut
  , implemented
  ) where

import Prelude

import Prim as P

import Data.Either (Either(..))
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..))
import Data.Show.Generic (genericShow)
import Effect (Effect)
import Effect.Uncurried (runEffectFn1, runEffectFn2, runEffectFn3)
import Steam.Array as Arr
import Steam.Fault (Fault(..))
import Steam.Value (Value(..))
import Stella.Compiler.Primitive (PrimOp(..), primTable)
import Stella.Compiler.TypedCore.Domain (scalarAt, scalarLength)

-- | Why an operation produced no value.
data Refusal
  = Faulted Fault
  -- | Operands the entry does not take. Their classes and their number are settled
  -- | before a `.dmo` exists, so this is a defect above the interpreter rather than
  -- | a failure of the program.
  | WrongOperands
  -- | An operation outside what this interpreter carries out. A module naming one
  -- | is refused where it is loaded, so this is what a `.dmo` that got past that
  -- | would produce.
  | NotImplemented PrimOp

-- | The operations this interpreter carries out. A module naming any other is one
-- | it cannot load.
-- | **Derived from the version's own table rather than listed again.** This
-- | interpreter carries out every operation of `stella-base-0.1`, and a second list
-- | saying so is one that can fall behind it: an entry duplicated here and another
-- | omitted would leave a module refused at load for an operation the version holds.
implemented :: P.Array PrimOp
implemented = map _.op primTable

-- | What an operation computes from the arguments it is given.
-- |
-- | **Carrying one out reaches the host**, which the array entries are why: four of
-- | the eight compute from scalar arguments alone, and every entry of `Base.Array`
-- | reaches the payload of an array instead. The operation boundary is the same
-- | kind of boundary as the foreign one and not a second one (D41).
-- | **`unit` is passed in rather than built here.** `Prim.Unit` is a constructor
-- | whose identity the registry assigned, so the value a write answers with is the
-- | one the loaded module holds; one built here would compare unequal to every
-- | other `Prim.Unit` in the program.
carryOut :: Value -> PrimOp -> P.Array Value -> Effect (Either Refusal Value)
carryOut unit' op args = case op, args of
  -- **32-bit wrapping arithmetic**, which every backend owes whatever its host
  -- does: neither of these faults.
  IntAdd, [ VInt a, VInt b ] -> produce (VInt (a + b))
  IntSub, [ VInt a, VInt b ] -> produce (VInt (a - b))

  -- the number of Unicode scalar values, which is what the length of a `String`
  -- is (D27)
  StringLength, [ VString s ] -> produce (VInt (scalarLength s))

  -- the scalar value at a **scalar index**, counting from zero
  StringCodePointAt, [ VInt i, VString s ] -> case scalarAt i s of
    Just scalar -> produce (VChar scalar)
    Nothing -> faults (IndexOutsideString i (scalarLength s))

  -- a slot count is fixed where the array is created and nothing changes it, so
  -- this reads an immutable property of its argument and faults on nothing
  ArrayLength, [ VOpaque o ] -> overArray o \array ->
    map (Right <<< VInt) (runEffectFn1 Arr.length array)

  -- **the slots are not written**, and reading one nothing wrote is the
  -- precondition of `ArrayUnsafeIndex`, violated (D42)
  ArrayUnsafeNew, [ VInt n ]
    | n < 0 -> faults (NegativeArrayLength n)
    | otherwise -> map (Right <<< VOpaque <<< Arr.toOpaque) (runEffectFn1 Arr.allocate n)

  ArrayUnsafeSet, [ VInt i, value, VOpaque o ] -> overArray o \array -> do
    size <- runEffectFn1 Arr.length array
    if i < 0 || i >= size then pure (Left (Faulted (IndexOutsideArray i size)))
    else do
      runEffectFn3 Arr.write array i value
      pure (Right unit')

  -- the range is decided here; whether the slot was written is not asked, and
  -- nothing records it
  ArrayUnsafeIndex, [ VOpaque o, VInt i ] -> overArray o \array -> do
    size <- runEffectFn1 Arr.length array
    if i < 0 || i >= size then pure (Left (Faulted (IndexOutsideArray i size)))
    else map Right (runEffectFn2 Arr.read array i)

  _, _ -> pure (Left WrongOperands)
  where
  produce = pure <<< Right
  faults = pure <<< Left <<< Faulted

  -- an opaque value some other entry produced is operands this entry does not
  -- take, and a `.dmo` carries no type that would have caught it
  overArray o k = case Arr.fromOpaque o of
    Just array -> k array
    Nothing -> pure (Left WrongOperands)

derive instance Eq Refusal
derive instance Generic Refusal _

instance Show Refusal where
  show = genericShow
