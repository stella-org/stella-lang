-- | The implicit handlers a module may have inserted, `Ξ`
-- | ([Effect Handlers](../../../../../docs/technical-references/02-Surface-Language/02-Effect-Handlers.md#the-judgement)),
-- | and the cycles among them.
-- |
-- | **An imported handler is read through the value exports of the modules
-- | the header imports directly.** An export names the global it publishes by
-- | its identity, a re-export the same identity, and where the interface of
-- | the module declaring that global records it as an implicit handler, it is
-- | a candidate. How the header writes an import — a list of names, `hiding`,
-- | `lazy`, an alias — selects among names, never among candidates. A handler
-- | a module reaches only through another, or imports without exporting, is
-- | no candidate.
-- |
-- | **Candidates are told apart by their identity** and listed in its order,
-- | the module's name and then the global's compared by scalar value; which
-- | one the search takes is decided by its source's key alone.
module Stella.Compiler.Elaborate.Environment.Implicit
  ( ImplicitCandidate
  , importedImplicits
  , compareIdentity
  , cyclicComponents
  ) where

import Prelude

import Data.Array as Array
import Data.Foldable (foldMap)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Stella.Compiler.Elaborate.Surface.Group (groups)
import Stella.Compiler.Interface.Environment (ModuleView, exportsOf, lookupImplicitHandler, lookupValue, reachable)
import Stella.Compiler.Interface.Scheme (coreScheme)
import Stella.Compiler.TypedCore.Domain (compareByScalar)
import Stella.Compiler.TypedCore.Name (Ident(..), ModuleName(..), Qualified(..))
import Stella.Compiler.TypedCore.Prim (primModule)
import Stella.Compiler.TypedCore.Type (RowEntry, TypeScheme, rowEntryKey)

-- | An implicit handler the search may take: the global, the element it
-- | handles, the elements it performs in its place, and its scheme, which an
-- | insertion instantiates.
type ImplicitCandidate =
  { handler :: Qualified Ident
  , source :: RowEntry
  , targets :: Array RowEntry
  , scheme :: TypeScheme
  }

-- | The implicit handlers the value exports of the modules a view's header
-- | imports publish, each once, in the order of their identities. `Prim`, which
-- | every module sees without importing it, publishes none.
importedImplicits :: ModuleView -> Array ImplicitCandidate
importedImplicits view = Array.sortBy (\a b -> compareIdentity a.handler b.handler) (Array.mapMaybe candidate published)
  where
  published = Array.nubBy compareIdentity
    (foldMap (\m -> foldMap (map _.entity <<< Array.fromFoldable <<< Map.values <<< _.values) (exportsOf m view)) (Array.filter (_ /= primModule) (Array.fromFoldable (reachable view))))
  candidate q = do
    h <- lookupImplicitHandler q view
    entry <- lookupValue q view
    pure { handler: q, source: h.source, targets: h.targets, scheme: coreScheme entry.scheme }

-- | The order of identities: the module's name, then the global's, each
-- | compared by scalar value.
compareIdentity :: Qualified Ident -> Qualified Ident -> Ordering
compareIdentity (Qualified (ModuleName m) (Ident a)) (Qualified (ModuleName n) (Ident b)) =
  compareByScalar m n <> compareByScalar a b

-- | The candidates that lower into one another, each strongly connected
-- | component of the graph in which a handler leads to every one whose source
-- | it performs: a component of several, or of one leading to itself. Each
-- | lists its members in the order of their identities, and the components
-- | stand in the order of their first members.
cyclicComponents :: Array ImplicitCandidate -> Array (Array (Qualified Ident))
cyclicComponents candidates = Array.sortBy compareFirst (map membersOf (Array.filter _.recursive (groups (map leadsTo ordered))))
  where
  ordered = Array.sortBy (\a b -> compareIdentity a.handler b.handler) candidates
  leadsTo h = Set.fromFoldable (Array.catMaybes (Array.mapWithIndex (\i h' -> if Array.elem (rowEntryKey h'.source) (map rowEntryKey h.targets) then Just i else Nothing) ordered))
  membersOf g = Array.mapMaybe (\i -> _.handler <$> Array.index ordered i) g.members
  compareFirst a b = case Array.head a, Array.head b of
    Just x, Just y -> compareIdentity x y
    _, _ -> EQ
