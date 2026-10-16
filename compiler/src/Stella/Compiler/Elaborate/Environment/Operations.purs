-- | The operations a module's values may call, as the surface elaborator reads
-- | them ([Effects](../../../../../docs/technical-references/03-Typed-Core/03-Effects.md)).
-- |
-- | **An operation is read from its effect's declaration**, with the arguments
-- | it is written with: the imports' from the effects their interfaces declare,
-- | and the module's from its own. The type it is called at is the one its
-- | interface publishes (`Stella.Compiler.Interface.Operation`).
module Stella.Compiler.Elaborate.Environment.Operations
  ( OperationEnv
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
import Stella.Compiler.TypedCore.Name (Ident(..), ModuleName, OpName(..), Qualified(..))

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
