-- | The operations a module's values may call and the effects its handlers may
-- | handle, as the surface elaborator reads them
-- | ([Effects](../../../../../docs/technical-references/03-Typed-Core/03-Effects.md)).
-- |
-- | **An operation is read from its effect's declaration**, with the arguments
-- | it is written with: the imports' from the effects their interfaces declare,
-- | and the module's from its own. The type it is called at is the one its
-- | interface publishes (`Stella.Compiler.Interface.Operation`). **An effect
-- | keeps its operations in the order it declares them**, which a handler's
-- | clauses are given to Core in.
module Stella.Compiler.Elaborate.Environment.Operations
  ( EffectEnv
  , HandledEffect
  , OperationEnv
  , importedEffects
  , importedOperations
  ) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Data.Tuple (Tuple(..))
import Stella.Compiler.Interface.Environment (BuildEnvironment, ModuleView, lookupInterface, reachable)
import Stella.Compiler.Interface.Operation (Operation, operationOf)
import Stella.Compiler.TypedCore.Name (EffName, Ident(..), ModuleName, OpName(..), Qualified(..))
import Stella.Compiler.TypedCore.Type (TyBinder)

type OperationEnv = Map (Qualified Ident) Operation

-- | The operations of every effect a module the imports reach declares, each
-- | by the qualified name it is referred to by.
importedOperations :: BuildEnvironment -> ModuleView -> OperationEnv
importedOperations env view = Map.fromFoldable (Array.concatMap operationsOf (Set.toUnfoldable (reachable view)))
  where
  operationsOf :: ModuleName -> P.Array (Tuple (Qualified Ident) Operation)
  operationsOf m = case lookupInterface m env of
    Nothing -> []
    Just i -> Array.concatMap
      ( \(Tuple e entry) -> map
          (\o -> Tuple (Qualified m o.name) (operationOf (Qualified m e) entry.params { name: opName o.name, binders: o.binders, arguments: o.arguments, resumesWith: o.resumesWith }))
          entry.operations
      )
      (Map.toUnfoldable i.declarations.effects)

  opName (Ident x) = OpName x

-- | An effect as a handler reads it: its parameters, and its operations, each
-- | by the qualified name it is referred to by, in the order it declares them.
type HandledEffect = { params :: P.Array TyBinder, operations :: P.Array (Qualified Ident) }

type EffectEnv = Map (Qualified EffName) HandledEffect

-- | Every effect a module the imports reach declares.
importedEffects :: BuildEnvironment -> ModuleView -> EffectEnv
importedEffects env view = Map.fromFoldable (Array.concatMap effectsOf (Set.toUnfoldable (reachable view)))
  where
  effectsOf :: ModuleName -> P.Array (Tuple (Qualified EffName) HandledEffect)
  effectsOf m = case lookupInterface m env of
    Nothing -> []
    Just i -> map
      (\(Tuple e entry) -> Tuple (Qualified m e) { params: entry.params, operations: map (\o -> Qualified m o.name) entry.operations })
      (Map.toUnfoldable i.declarations.effects)
