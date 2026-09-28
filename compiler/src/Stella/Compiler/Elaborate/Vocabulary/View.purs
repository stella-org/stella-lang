-- | What a synthesizer sees of a type, a kind, a constraint, and a declaration.
-- |
-- | A view is a projection with a shape of its own, and it is what the
-- | compile-time session's interface fixes; the host's own representations stay
-- | behind the handles a view carries for its parts, so they can change without
-- | the interface changing.
-- |
-- | A row is shown as its normal form. Two rows are the same row exactly when
-- | their normal forms agree, so how one happened to be written — extensions or
-- | unions, in which order — is nothing a synthesizer can rely on.
module Stella.Compiler.Elaborate.Vocabulary.View
  ( TypeView(..)
  , RowView
  , PayloadView(..)
  , KindView(..)
  , ConstraintView(..)
  , DeclView
  , ContextEntry
  ) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.Environment.Catalog (EntrySort)
import Stella.Compiler.Elaborate.Vocabulary.Handle (Handle)
import Stella.Compiler.TypedCore (Attribute, EffName, Ident, KindVar, Qualified, RowElemKind, RowKey, TyName, TyVar)
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe)
import Data.Show.Generic (genericShow)

-- | A type, one level deep. Each part that is itself a type is a Type handle.
data TypeView
  = VarType TyVar
  -- | An unsolved type metavariable, as a Meta handle. The Type handle a
  -- | metavariable was made as is where a synthesizer gets the Meta handle it
  -- | postpones on.
  | MetaType Handle
  | ConType (Qualified TyName) (P.Array KindView)
  | AppType Handle Handle
  | ForallType TyVar KindView Handle
  | ConstrainedType ConstraintView Handle
  | NormalRow RowView

-- | A row in normal form.
-- |
-- | `elementKind` is the row kind it is shown at: `Nothing` for a row that
-- | stands at any, having no element and no tail. `known` is in ascending order
-- | of key, `rigid` of name, and `flexible` of metavariable, so one row has one
-- | view.
-- |
-- | A flexible tail is shown twice over: as the metavariable, which is what
-- | `postpone` is given, and as the type standing for it, built where the row
-- | was and at the row's kind, which is what a row is rebuilt from. A metavariable
-- | alone says nothing of where it was observed, so it could not be turned back
-- | into a type without letting a part of a type that belongs to no build scope
-- | into one.
type RowView =
  { elementKind :: Maybe RowElemKind
  , known :: P.Array { key :: RowKey, payload :: PayloadView }
  , rigid :: P.Array TyVar
  , flexible :: P.Array { meta :: Handle, type :: Handle }
  }

-- | What an element carries. At `Row Type` it is a type; at `Row Effect` an
-- | effect applied to its arguments, or a region.
data PayloadView
  = TypePayload Handle
  | EffectPayload (Qualified EffName) (P.Array Handle)
  | RegionPayload Handle Handle

-- | A settled kind. `KindAnyRow` is what a row with no element and no tail
-- | stands at, and no kind metavariable is shown.
data KindView
  = KindType
  | KindEffect
  | KindRow RowElemKind
  | KindFun KindView KindView
  | KindVar KindVar
  | KindAnyRow

data ConstraintView
  = LacksView RowKey Handle
  | DisjointView Handle Handle

-- | A catalog entry. `scheme` is a Type handle to the scheme's body, at `Type`;
-- | `kindVars` are what that body's kinds may mention.
type DeclView =
  { name :: Qualified Ident
  , sort :: EntrySort
  , kindVars :: P.Array KindVar
  , scheme :: Handle
  , attributes :: P.Array Attribute
  }

-- | One binding of the local context: a name and a Type handle to its type.
type ContextEntry =
  { name :: Ident
  , type :: Handle
  }

derive instance Eq TypeView
derive instance Generic TypeView _

instance Show TypeView where
  show x = genericShow x

derive instance Eq PayloadView
derive instance Generic PayloadView _

instance Show PayloadView where
  show x = genericShow x

derive instance Eq KindView
derive instance Generic KindView _

instance Show KindView where
  show x = genericShow x

derive instance Eq ConstraintView
derive instance Generic ConstraintView _

instance Show ConstraintView where
  show x = genericShow x
