-- | What the surface elaborator reads of the imports and the module beyond the
-- | signature and the catalog: the type synonyms types are read through, the
-- | operations with the arguments they are written with, the effects with their
-- | operations in order, the values whose schemes take a synthesized parameter,
-- | and the schemes of the module's values without a signature
-- | ([Elaboration](../../../../../docs/technical-references/02-Surface-Language/01-Elaboration.md)).
-- |
-- | **Neither is the kernel's.** A synonym is expanded before any type reaches
-- | the mechanism, and a synthesized parameter is a parameter of its
-- | type in Core; what a reference to such a value owes is the
-- | surface elaborator's to supply. **A value without a signature is in no
-- | catalog**: the module's synthesizers never read it, generalized or not.
module Stella.Compiler.Elaborate.Environment.Surface
  ( SurfaceEnv
  , SurfaceBinding(..)
  , emptySurface
  , importedSurface
  , takesSynthesized
  ) where

import Prelude

import Data.Array as Array
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Set as Set
import Data.Tuple (Tuple(..))
import Stella.Compiler.Elaborate.Environment.Implicit (ImplicitCandidate, importedImplicits)
import Stella.Compiler.Elaborate.Environment.Synonyms (SynonymEnv, emptySynonyms, importedSynonyms)
import Stella.Compiler.Interface.Environment (BuildEnvironment, ModuleView, lookupInterface, reachable)
import Stella.Compiler.Interface.Module (ValueSort(..))
import Stella.Compiler.Interface.Scheme (Scheme, SchemeBody(..))
import Stella.Compiler.TypedCore.Name (Ident, Qualified(..))
import Stella.Compiler.TypedCore.Type (TypeScheme)
import Stella.Compiler.Elaborate.CorePlus.Type (XType)
import Stella.Compiler.Elaborate.Environment.Operations (EffectEnv, OperationEnv, importedEffects, importedOperations)

-- | The synonyms, the operations, the effects, the values taking a synthesized
-- | argument at the spine their interface gives them, and the module's values
-- | without a signature, each by the qualified name of its declaration; the
-- | implicit handlers the imports publish; and the values the modules the
-- | imports reach declare and export as values.
type SurfaceEnv =
  { synonyms :: SynonymEnv
  , operations :: OperationEnv
  , effects :: EffectEnv
  , synthesizing :: Map (Qualified Ident) SchemeBody
  , bindings :: Map (Qualified Ident) SurfaceBinding
  , implicits :: Array ImplicitCandidate
  , exportedValues :: Set (Qualified Ident)
  }

-- | A value without a signature, as a reference to it reads it: at the scheme
-- | its group's generalization made final, or, from inside its group while
-- | the group is elaborated, at the one type it has there.
data SurfaceBinding
  = Final TypeScheme
  | Provisional XType
  -- | A member of the group being elaborated whose partial signature is a
  -- | scheme, its quantifiers or its constraints instantiated where it is
  -- | referred to, which a reference inside the group cannot be.
  | ProvisionalScheme

emptySurface :: SurfaceEnv
emptySurface = { synonyms: emptySynonyms, operations: Map.empty, effects: Map.empty, synthesizing: Map.empty, bindings: Map.empty, implicits: [], exportedValues: Set.empty }

-- | What the modules the imports reach declare.
importedSurface :: BuildEnvironment -> ModuleView -> SurfaceEnv
importedSurface env view =
  { synonyms: importedSynonyms env view
  , operations: importedOperations env view
  , effects: importedEffects env view
  , synthesizing: Map.fromFoldable (Array.concatMap synthesizingOf (Set.toUnfoldable (reachable view)))
  , bindings: Map.empty
  , implicits: importedImplicits view
  , exportedValues: Set.fromFoldable (Array.concatMap exportedOf (Set.toUnfoldable (reachable view)))
  }
  where
  synthesizingOf m = case lookupInterface m env of
    Nothing -> []
    Just i -> Array.mapMaybe
      (\(Tuple name entry) -> if takesSynthesized entry.scheme then Just (Tuple (Qualified m name) entry.scheme.body) else Nothing)
      (Map.toUnfoldable i.declarations.values)
  -- the values a module exports that it declares itself, as values, under
  -- the identities it declares them at
  exportedOf m = case lookupInterface m env of
    Nothing -> []
    Just i -> Array.filter (declaredValueOf i) (map _.entity (Array.fromFoldable (Map.values i.exports.values)))
  declaredValueOf i (Qualified owner name) = owner == i.name && case Map.lookup name i.declarations.values of
    Just { sort: SortValue } -> true
    _ -> false

-- | Whether a scheme's spine holds a synthesized parameter.
takesSynthesized :: Scheme -> Boolean
takesSynthesized s = go s.body
  where
  go = case _ of
    Synthesized _ _ -> true
    Forall _ _ body -> go body
    Constrained _ body -> go body
    _ -> false
