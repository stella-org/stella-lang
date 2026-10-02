-- | The names the Surface AST holds at a binding position or a reference to a
-- | local binding.
-- |
-- | A global is held as Core holds it, qualified by the module that declares
-- | it (`Qualified Ident`, `Qualified TyName`, `Qualified EffName`). A local
-- | binding is held as the binding it is: a number that tells it apart from
-- | every other binding of the module, and the name it was written with, which
-- | is kept for diagnostics and for the names Core is given. Labels and tags
-- | are keys of rows, which no scope holds, and stay as written (`Symbol`,
-- | `Tag`).
module Stella.Compiler.Surface.Name
  ( BindingId(..)
  , LocalVar(..)
  , TypeVar(..)
  , CellVar(..)
  , OperatorName(..)
  ) where

import Prelude

import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Stella.Compiler.TypedCore.Name (Ident, TyVar)

-- | The number of a binding, unique within the module it is bound in.
newtype BindingId = BindingId Int

-- | A value variable: a parameter, a `let` or `where` binding, a variable of a
-- | pattern, or a binder of a handler clause.
newtype LocalVar = LocalVar { id :: BindingId, name :: Ident }

-- | A type variable, bound by a `forall`, by the parameters of a declaration,
-- | or implicitly by a signature.
newtype TypeVar = TypeVar { id :: BindingId, name :: TyVar }

-- | A cell of a handler, `var x := e`. Cells have a namespace of their own and
-- | are reached by `x!` and `x := e` alone.
newtype CellVar = CellVar { id :: BindingId, name :: Ident }

-- | The operator a fixity declaration introduces, `+` in `infixl 6 add as +`.
newtype OperatorName = OperatorName String

derive instance Eq BindingId
derive instance Ord BindingId
derive newtype instance Show BindingId

derive instance Eq LocalVar
derive instance Ord LocalVar
derive instance Generic LocalVar _

instance Show LocalVar where
  show = genericShow

derive instance Eq TypeVar
derive instance Ord TypeVar
derive instance Generic TypeVar _

instance Show TypeVar where
  show = genericShow

derive instance Eq CellVar
derive instance Ord CellVar
derive instance Generic CellVar _

instance Show CellVar where
  show = genericShow

derive instance Eq OperatorName
derive instance Ord OperatorName
derive newtype instance Show OperatorName
