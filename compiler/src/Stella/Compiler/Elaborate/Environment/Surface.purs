-- | What the surface elaborator reads of the imports beyond the signature and
-- | the catalog: the type synonyms types are read through, and the values
-- | whose schemes take a synthesized argument
-- | ([Elaboration](../../../../../docs/technical-references/02-Surface-Language/01-Elaboration.md)).
-- |
-- | **Neither is the kernel's.** A synonym is expanded before any type reaches
-- | the mechanism, and a synthesized argument is a parameter of the
-- | dictionary's type in Core; what a reference to such a value owes is the
-- | surface elaborator's to supply.
module Stella.Compiler.Elaborate.Environment.Surface
  ( SurfaceEnv
  , emptySurface
  , importedSurface
  , takesSynthesized
  ) where

import Data.Array as Array
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Set as Set
import Data.Tuple (Tuple(..))
import Stella.Compiler.Elaborate.Environment.Synonyms (SynonymEnv, emptySynonyms, importedSynonyms)
import Stella.Compiler.Interface.Environment (BuildEnvironment, ModuleView, lookupInterface, reachable)
import Stella.Compiler.Interface.Scheme (Scheme, SchemeBody(..))
import Stella.Compiler.TypedCore.Name (Ident, Qualified(..))

-- | The synonyms, and the values taking a synthesized argument, each by the
-- | qualified name of its declaration.
type SurfaceEnv =
  { synonyms :: SynonymEnv
  , synthesizing :: Set (Qualified Ident)
  }

emptySurface :: SurfaceEnv
emptySurface = { synonyms: emptySynonyms, synthesizing: Set.empty }

-- | What the modules the imports reach declare.
importedSurface :: BuildEnvironment -> ModuleView -> SurfaceEnv
importedSurface env view =
  { synonyms: importedSynonyms env view
  , synthesizing: Set.fromFoldable (Array.concatMap synthesizingOf (Set.toUnfoldable (reachable view)))
  }
  where
  synthesizingOf m = case lookupInterface m env of
    Nothing -> []
    Just i -> Array.mapMaybe
      (\(Tuple name entry) -> if takesSynthesized entry.scheme then Just (Qualified m name) else Nothing)
      (Map.toUnfoldable i.declarations.values)

-- | Whether a scheme's spine holds a synthesized argument.
takesSynthesized :: Scheme -> Boolean
takesSynthesized s = go s.body
  where
  go = case _ of
    Synthesized _ _ -> true
    Forall _ _ body -> go body
    Constrained _ body -> go body
    _ -> false
