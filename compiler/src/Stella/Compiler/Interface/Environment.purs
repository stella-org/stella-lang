-- | The build environment: the interfaces of the modules compiled so far,
-- | shared by the whole build
-- | ([Modules](../../../../docs/technical-references/06-Modules/01-Modules.md)).
-- |
-- | A module is compiled on its own, against the environment, and its interface
-- | is added once it is compiled; what an optimizer downstream reads of a
-- | module reaches it the same way. The environment begins with `Prim`, and
-- | holds what the ABI manifest supplies to the modules it names.
-- |
-- | **An interface is added after every module it imports.** So the
-- | environment is ordered as the import graph is, a cycle cannot enter it, and
-- | everything a module's header reaches is there when the module is compiled.
-- |
-- | **A module compiled against the environment sees what its header reaches
-- | and nothing else**: the export tables of the modules it imports, and the
-- | declarations of every module those import in turn, `Prim` among them. A
-- | name resolves through the first, and an entity a name stands for is read
-- | from the second, wherever it is declared (D22).
module Stella.Compiler.Interface.Environment
  ( BuildEnvironment
  , EnvironmentError(..)
  , initialEnvironment
  , addInterface
  , lookupInterface
  , abiOf
  , ModuleView
  , viewFor
  , exportsOf
  , reachable
  , lookupValue
  , lookupType
  , lookupEffect
  , lookupOperator
  , lookupTypeOperator
  , lookupAttribute
  ) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldM)
import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Set (Set)
import Data.Set as Set
import Data.Show.Generic (genericShow)
import Stella.Compiler.Interface.Module (AttributeEntry, EffectEntry, Exports, ModuleInterface, OperatorEntry, TypeEntry, TypeOperatorEntry, ValueEntry)
import Stella.Compiler.Interface.Prim (primInterface)
import Stella.Compiler.Surface.Name (OperatorName)
import Stella.Compiler.TypedCore.Name (EffName, Ident, ModuleName, Qualified(..), TyName)
import Stella.Compiler.TypedCore.Prim (primModule)

type BuildEnvironment =
  { interfaces :: Map ModuleName ModuleInterface
  -- | The type constructors the ABI manifest supplies to each module it names,
  -- | which that module's own declarations are checked with
  -- | ([Prim and Base](../../../../docs/technical-references/06-Modules/02-Prim-and-Base.md)).
  , abi :: Map ModuleName (Map TyName TypeEntry)
  }

data EnvironmentError
  -- | A second interface of a module the environment holds one of.
  = ModuleTwice ModuleName
  -- | An interface added before a module it imports, the second name.
  | ImportNotAdded ModuleName ModuleName
  -- | A header naming a module the environment does not hold.
  | NotInEnvironment ModuleName

-- | The environment a build starts from: `Prim`, and nothing the ABI manifest
-- | supplies.
initialEnvironment :: BuildEnvironment
initialEnvironment =
  { interfaces: Map.singleton primModule primInterface
  , abi: Map.empty
  }

addInterface :: ModuleInterface -> BuildEnvironment -> Either EnvironmentError BuildEnvironment
addInterface i env
  | Map.member i.name env.interfaces = Left (ModuleTwice i.name)
  | otherwise = case Array.find (\m -> not (Map.member m env.interfaces)) i.imports of
      Just missing -> Left (ImportNotAdded i.name missing)
      Nothing -> Right env { interfaces = Map.insert i.name i env.interfaces }

lookupInterface :: ModuleName -> BuildEnvironment -> Maybe ModuleInterface
lookupInterface m env = Map.lookup m env.interfaces

-- | What the ABI manifest supplies to a module, which is nothing for a module it
-- | does not name.
abiOf :: ModuleName -> BuildEnvironment -> Map TyName TypeEntry
abiOf m env = fromMaybe Map.empty (Map.lookup m env.abi)

-- | The environment as one module compiled against it sees it.
newtype ModuleView = ModuleView
  { environment :: BuildEnvironment
  , imports :: Set ModuleName
  , reachable :: Set ModuleName
  }

-- | The view of a module whose header imports the modules given.
viewFor :: Array ModuleName -> BuildEnvironment -> Either EnvironmentError ModuleView
viewFor imports env = do
  closure <- foldM visit (Set.singleton primModule) imports
  pure (ModuleView { environment: env, imports: Set.fromFoldable imports, reachable: closure })
  where
  visit seen m
    | Set.member m seen = Right seen
    | otherwise = case lookupInterface m env of
        Nothing -> Left (NotInEnvironment m)
        Just i -> foldM visit (Set.insert m seen) i.imports

-- | The export tables of a module the header imports, or of `Prim`, which every
-- | module sees without importing it. A module reached only through another
-- | publishes no name to this one.
exportsOf :: ModuleName -> ModuleView -> Maybe Exports
exportsOf m (ModuleView v)
  | m == primModule || Set.member m v.imports = map _.exports (lookupInterface m v.environment)
  | otherwise = Nothing

-- | Every module whose declarations the view reaches.
reachable :: ModuleView -> Set ModuleName
reachable (ModuleView v) = v.reachable

-- | The interface of the module declaring an entity, where the view reaches it.
declaring :: forall a. Qualified a -> ModuleView -> Maybe ModuleInterface
declaring (Qualified m _) (ModuleView v)
  | Set.member m v.reachable = lookupInterface m v.environment
  | otherwise = Nothing

lookupValue :: Qualified Ident -> ModuleView -> Maybe ValueEntry
lookupValue q@(Qualified _ name) view = declaring q view >>= \i -> Map.lookup name i.declarations.values

lookupType :: Qualified TyName -> ModuleView -> Maybe TypeEntry
lookupType q@(Qualified _ name) view = declaring q view >>= \i -> Map.lookup name i.declarations.types

lookupEffect :: Qualified EffName -> ModuleView -> Maybe EffectEntry
lookupEffect q@(Qualified _ name) view = declaring q view >>= \i -> Map.lookup name i.declarations.effects

lookupOperator :: Qualified OperatorName -> ModuleView -> Maybe OperatorEntry
lookupOperator q@(Qualified _ name) view = declaring q view >>= \i -> Map.lookup name i.declarations.operators

lookupTypeOperator :: Qualified OperatorName -> ModuleView -> Maybe TypeOperatorEntry
lookupTypeOperator q@(Qualified _ name) view = declaring q view >>= \i -> Map.lookup name i.declarations.typeOperators

lookupAttribute :: Qualified Ident -> ModuleView -> Maybe AttributeEntry
lookupAttribute q@(Qualified _ name) view = declaring q view >>= \i -> Map.lookup name i.declarations.attributes

derive instance Eq EnvironmentError
derive instance Generic EnvironmentError _

instance Show EnvironmentError where
  show = genericShow
