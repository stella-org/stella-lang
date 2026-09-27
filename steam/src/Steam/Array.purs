-- | The payload of a `Base.Array.Array`
-- | ([Abstract Machine](../../../docs/technical-references/07-Runtime/01-Abstract-Machine.md)).
-- |
-- | `Base.Array.Array` is an `intrinsic opaque`, so an array reaches the rest of the
-- | interpreter as a `VOpaque` and nothing outside this module takes one apart. What
-- | the payload is belongs to the interpreter and to no `.dmo`, so this one is the
-- | host's own mutable array, holding the interpreter's values.
-- |
-- | **A slot that has not been written holds nothing, and reading one is the
-- | precondition of `Base.Array.unsafeIndex`, violated** (D42). Nothing here tracks
-- | which slots have been written: the ABI requires no such check and the check
-- | would stand on every read. A backend that chose to pay for it would be
-- | conformant too — this is a decision of this interpreter and not a reading of
-- | the specification
-- | ([Prim and Base](../../../docs/technical-references/06-Modules/02-Prim-and-Base.md)).
module Steam.Array
  ( MutableArray
  , fromOpaque
  , toOpaque
  , allocate
  , length
  , read
  , write
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Effect.Uncurried (EffectFn1, EffectFn2, EffectFn3)
import Prim as P
import Steam.Value (Opaque, Value)
import Unsafe.Coerce (unsafeCoerce)

foreign import data MutableArray :: P.Type

-- | Whether an opaque value is one of these, by a **brand the payload carries**.
-- |
-- | **This is a check of the operand's class and not of a slot.** A `.dmo` carries
-- | no types, so an operation reaching an opaque value some other entry produced
-- | would otherwise write through it; the brand is what separates this module's
-- | payload from another entry's, and it is asked once where an operation takes its
-- | array apart rather than once per slot.
foreign import isArray :: Opaque -> P.Boolean

foreign import allocate :: EffectFn1 P.Int MutableArray

foreign import length :: EffectFn1 MutableArray P.Int

-- | The slot's value, which is nothing where nothing wrote it. What comes back
-- | then is not a value of the element type and is not a value of any type; a
-- | program reaching this has violated the precondition of the entry above it.
foreign import read :: EffectFn2 MutableArray P.Int Value

foreign import write :: EffectFn3 MutableArray P.Int Value Unit

unsafeAsArray :: Opaque -> MutableArray
unsafeAsArray = unsafeCoerce

toOpaque :: MutableArray -> Opaque
toOpaque = unsafeCoerce

fromOpaque :: Opaque -> Maybe MutableArray
fromOpaque opaque
  | isArray opaque = Just (unsafeAsArray opaque)
  | otherwise = Nothing
