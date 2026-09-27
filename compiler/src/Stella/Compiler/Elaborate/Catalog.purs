-- | The module catalog: every value name a compile-time session may resolve,
-- | with its attributes and its scheme.
-- |
-- | It is assembled once, before the first job exists, from the entries the
-- | imported modules' interfaces publish and every top-level value name the
-- | module being compiled declares, and its domain never changes afterwards. A
-- | scheme still being inferred is provisional: it carries metavariables, which a
-- | reader zonks against the current `Ψ`, so the schemes sharpen while the names
-- | stay fixed. Otherwise what a synthesizer found would depend on when its goal
-- | was attempted.
module Stella.Compiler.Elaborate.Catalog
  ( EntrySort(..)
  , XScheme
  , CatalogEntry
  , ModuleCatalog
  , catalogOf
  , lookupEntry
  , namesWithAttr
  ) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.Type (XType)
import Stella.Compiler.TypedCore (Attribute, Ident, KindVar, Qualified)
import Data.Array as Array
import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe)
import Data.Show.Generic (genericShow)
import Data.Tuple (Tuple(..))

-- | What a value name is. Each can be referred to by a term.
data EntrySort
  = ValueEntry
  | ForeignEntry
  | ConstructorEntry

-- | `forall k̄. τ⁺`, the scheme of a catalog entry.
type XScheme =
  { kindVars :: P.Array KindVar
  , body :: XType
  }

type CatalogEntry =
  { name :: Qualified Ident
  , sort :: EntrySort
  , scheme :: XScheme
  , attributes :: P.Array Attribute
  }

newtype ModuleCatalog = ModuleCatalog (Map (Qualified Ident) CatalogEntry)

-- | The catalog of the entries given. A name belongs to the module declaring
-- | it, so one entry reached through two import paths is one entry; the caller
-- | refuses two different entries under one name before this is built.
catalogOf :: P.Array CatalogEntry -> ModuleCatalog
catalogOf entries = ModuleCatalog (Map.fromFoldable (map (\e -> Tuple e.name e) entries))

lookupEntry :: ModuleCatalog -> Qualified Ident -> Maybe CatalogEntry
lookupEntry (ModuleCatalog entries) name = Map.lookup name entries

-- | The names of the entries carrying an attribute of the key given, in
-- | ascending order of their qualified names, so that a search over them takes
-- | one order whatever order the interfaces were read in.
namesWithAttr :: ModuleCatalog -> P.String -> P.Array (Qualified Ident)
namesWithAttr (ModuleCatalog entries) key =
  Array.fromFoldable (Map.keys (Map.filter (\e -> Array.any (\a -> a.key == key) e.attributes) entries))

derive instance Eq EntrySort
derive instance Generic EntrySort _

instance Show EntrySort where
  show x = genericShow x
