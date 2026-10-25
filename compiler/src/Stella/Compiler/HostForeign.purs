module Stella.Compiler.HostForeign
  ( hostForeigns
  ) where

import Prelude

import Data.Array as Array
import Data.Bifunctor (lmap)
import Data.Either (Either)
import Data.Map as Map
import Data.Maybe (isNothing)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Stella.Compiler.Elaborate.Environment.Imported (importedSignature)
import Stella.Compiler.ForeignBoundary (crossingOf)
import Stella.Compiler.ForeignManifest (Signature)
import Stella.Compiler.Interface.Environment (BuildEnvironment, viewFor)
import Stella.Compiler.Interface.Module (ModuleInterface, ValueSort(..))
import Stella.Compiler.Interface.Scheme (coreScheme)
import Stella.Compiler.Primitive (runtimeEntryNamed)
import Stella.Compiler.TypedCore.Name (Ident(..), Qualified(..))

-- | The module was compiled only where each of its foreigns crossed, so one
-- | that does not is the compiler's fault.
hostForeigns :: BuildEnvironment -> ModuleInterface -> Either String (Array (Tuple String Signature))
hostForeigns env i = do
  view <- lmap (\err -> "the module has no view: " <> show err) (viewFor [ i.name ] env)
  signature <- lmap (\err -> "the module has no signature: " <> show err) (importedSignature env view)
  traverse (crossing signature) (Array.filter host (Map.toUnfoldable i.declarations.values))
  where
  host (Tuple n entry) = case entry.sort of
    SortForeign _ -> isNothing (runtimeEntryNamed (Qualified i.name n))
    _ -> false

  crossing signature (Tuple (Ident name) entry) =
    Tuple name <$> lmap (\refused -> "`" <> name <> "` does not cross to the host: " <> show refused) (crossingOf signature (coreScheme entry.scheme))
