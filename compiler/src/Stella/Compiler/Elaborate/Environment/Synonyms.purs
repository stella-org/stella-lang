-- | The type synonyms a module's types are read through
-- | ([Elaboration](../../../../../docs/technical-references/02-Surface-Language/01-Elaboration.md)).
-- |
-- | **A synonym is no entry of the signature**, being expanded wherever it is
-- | used, so what elaboration reads of one is kept apart: its kind scheme, its
-- | parameters, and the type it stands for. An interface holds a synonym's body
-- | with every synonym in it expanded already, so expanding a use never reaches
-- | another synonym.
module Stella.Compiler.Elaborate.Environment.Synonyms
  ( SynonymEntry
  , SynonymEnv
  , emptySynonyms
  , importedSynonyms
  , lookupSynonym
  ) where

import Prim hiding (Type)

import Data.Array as Array
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Data.Tuple (Tuple(..))
import Stella.Compiler.Interface.Environment (BuildEnvironment, ModuleView, lookupInterface, reachable)
import Stella.Compiler.Interface.Module (TypeSort(..))
import Stella.Compiler.TypedCore.Kind (KindScheme)
import Stella.Compiler.TypedCore.Name (Qualified(..), TyName)
import Stella.Compiler.TypedCore.Type (TyBinder, Type)

-- | A synonym: its kind scheme, its parameters, and the type it stands for,
-- | written in terms of them.
type SynonymEntry =
  { kind :: KindScheme
  , params :: Array TyBinder
  , body :: Type
  }

type SynonymEnv = Map (Qualified TyName) SynonymEntry

emptySynonyms :: SynonymEnv
emptySynonyms = Map.empty

-- | Every synonym a module the imports reach declares, by the qualified name
-- | of its declaration.
importedSynonyms :: BuildEnvironment -> ModuleView -> SynonymEnv
importedSynonyms env view = Map.fromFoldable (Array.concatMap synonymsOf (Set.toUnfoldable (reachable view)))
  where
  synonymsOf m = case lookupInterface m env of
    Nothing -> []
    Just i -> Array.mapMaybe
      ( \(Tuple name entry) -> case entry.sort of
          Synonym s -> Just (Tuple (Qualified m name) { kind: entry.kind, params: s.params, body: s.body })
          _ -> Nothing
      )
      (Map.toUnfoldable i.declarations.types)

lookupSynonym :: Qualified TyName -> SynonymEnv -> Maybe SynonymEntry
lookupSynonym = Map.lookup
