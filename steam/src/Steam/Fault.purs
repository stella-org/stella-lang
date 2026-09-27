-- | A failure the ABI admits
-- | ([Semantics](../../../docs/technical-references/03-Typed-Core/06-Semantics.md)).
-- |
-- | A fault is not an effect: no handler intercepts one, it appears in no row, and
-- | producing one discards the stack and ends the run.
-- |
-- | **Both sources of one are here.** An operation the interpreter carries out
-- | faults as the ABI says it may, and a foreign the host supplies refuses; the two
-- | are one class and are told apart by what a report says rather than by how they
-- | propagate.
module Steam.Fault
  ( Fault(..)
  ) where

import Prelude

import Prim as P

import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Stella.Compiler.TypedCore.Name (Ident, Qualified)

data Fault
  -- | An index outside the string, as the index and the number of scalar values
  -- | the string holds.
  = IndexOutsideString P.Int P.Int
  -- | An index outside the array, as the index and the number of slots the array
  -- | has. **An index inside the array naming a slot nothing wrote is not this**:
  -- | the range is decided first, and what is left is the precondition of
  -- | `Base.Array.unsafeIndex` rather than a failure it reports (D42).
  | IndexOutsideArray P.Int P.Int
  -- | A negative slot count handed to `Base.Array.unsafeNew`, as the count. A count
  -- | of zero is an array of no slots and is not this.
  | NegativeArrayLength P.Int
  -- | A foreign that produced no value, as the reason its body gave. This is the
  -- | failure the ABI admits an implementation may report.
  | ForeignRefused (Qualified Ident) P.String
  -- | A foreign whose body threw where it should have refused, as the message the
  -- | host exception carried.
  -- |
  -- | **Kept apart from a refusal.** The two propagate alike, and one is a failure
  -- | the ABI admits while the other is a body in breach of what it owes
  -- | ([Abstract Machine](../../../docs/technical-references/07-Runtime/01-Abstract-Machine.md)).
  | ForeignThrew (Qualified Ident) P.String

derive instance Eq Fault
derive instance Generic Fault _

instance Show Fault where
  show = genericShow
