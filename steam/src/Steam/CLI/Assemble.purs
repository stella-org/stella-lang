-- | Building the foreign table from a manifest
-- | ([Foreign Manifest](../../../docs/technical-references/05-Backend/04-Foreign-Manifest.md),
-- | D43).
-- |
-- | **What is fixed is when the table must be ready, not when it is built**: it is
-- | complete for a module before that module is loaded. A run reaches everything
-- | before the first load, a session reaches a module's implementations as that
-- | module arrives, and both go through `entriesFor` below.
-- |
-- | **Nothing here is eager over the manifest.** An entry for a module nothing
-- | declares against is never asked for, so a host the program does not use is not
-- | reached and its top-level does not run.
module Steam.CLI.Assemble
  ( AssembleError(..)
  , entriesFor
  , tableFor
  ) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Either (Either(..))
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Foldable (foldl)
import Data.Traversable (sequence, traverse)
import Data.Tuple (Tuple(..))
import Run (Run)
import Stella.CLI.Effect.Foreigns (FOREIGNS, HostExport, reach)
import Steam.Foreign (ForeignEntry, ForeignTable, emptyTable, insert)
import Steam.Value (ForeignBody, ForeignOutcome(..), Value)
import Stella.Compiler.Bytecode.Module (Dmo)
import Stella.Compiler.ForeignManifest (Manifest, entryFor)
import Stella.Compiler.TypedCore.Name (Ident(..), ModuleName, Qualified(..))
import Type.Row (type (+))

data AssembleError
  -- | The manifest names the module and the target could not reach it, as the module
  -- | and what the target said.
  = ModuleUnreachable ModuleName P.String
  -- | Reached, and holding no export of that name.
  | NoSuchExport ModuleName P.String
  -- | Reached, and the export is not callable. **A `.dmo` carries no type**, so this
  -- | is the one shape that can be checked.
  | ExportNotCallable ModuleName P.String

-- | The entries the foreigns of these modules need.
-- |
-- | **A module the manifest does not name yields nothing rather than a failure.**
-- | What is unmet is a declaration, and the loader is where a declaration nothing
-- | carries out is refused — naming the foreign, which is what a reader can act on,
-- | rather than a file that was not consulted.
entriesFor
  :: forall r
   . P.String
  -> Maybe Manifest
  -> P.Array Dmo
  -> Run (FOREIGNS + r) (Either AssembleError (Map (Qualified Ident) ForeignEntry))
entriesFor base manifest modules = case manifest of
  Nothing -> pure (Right Map.empty)
  Just held -> do
    reached <- traverse (perModule held) declaring
    pure (map (Map.fromFoldable <<< Array.concat) (sequence reached))
  where
  -- one reach per host module, and only for modules that declare something
  declaring = Array.filter (\dmo -> not (Array.null dmo.foreigns)) modules

  perModule held dmo = case entryFor held dmo.name of
    Nothing -> pure (Right [])
    Just entry -> do
      reached <- reach base entry
      pure case reached of
        Left reason -> Left (ModuleUnreachable dmo.name reason)
        Right exports -> traverse (bind' dmo.name exports) dmo.foreigns

  bind' name exports declared = case declared.name of
    Qualified _ (Ident unqualified) -> case Map.lookup unqualified exports of
      Nothing -> Left (NoSuchExport name unqualified)
      Just export
        | isCallable export ->
            Right (Tuple declared.name { arity: declared.arity, body: asBody export })
        | otherwise -> Left (ExportNotCallable name unqualified)

-- | The whole table for a run, which is given every module at once.
tableFor
  :: forall r
   . P.String
  -> Maybe Manifest
  -> P.Array Dmo
  -> Run (FOREIGNS + r) (Either AssembleError ForeignTable)
tableFor base manifest modules =
  map (map built) (entriesFor base manifest modules)
  where
  built entries = foldl (\table (Tuple name entry) -> insert name entry table) emptyTable
    (Map.toUnfoldable entries :: P.Array _)

-- | **The declared arity is adopted, and there is no second number.** A manifest
-- | carries none, and none can be read off a reached export: on JavaScript
-- | `Function.length` counts neither a rest parameter nor one with a default, and an
-- | adapter is usually written as one of those.
-- |
-- | What can be checked is that the export is callable at all, which is what
-- | `isCallable` asks.
foreign import isCallable :: HostExport -> P.Boolean

-- | The one place a host value becomes a body.
-- |
-- | The coercion is the boundary the type system cannot see across: the effect that
-- | reached it has no name for what the interpreter wants, and the interpreter is
-- | what knows. What makes it sound is the check above and the contract an adapter
-- | owes ([Abstract Machine](../../../docs/technical-references/07-Runtime/01-Abstract-Machine.md)).
asBody :: HostExport -> ForeignBody
asBody = wrapAdapterImpl Produced Refused

-- | Putting the interpreter's `Outcome` on what an adapter handed back.
-- |
-- | **An adapter constructs no outcome.** It returns the value it produced, or an
-- | object carrying a reason under a well-known symbol; the two constructors come
-- | from here, so an adapter imports nothing and never sees the form the interpreter
-- | matches on
-- | ([Foreign Manifest](../../../docs/technical-references/05-Backend/04-Foreign-Manifest.md)).
foreign import wrapAdapterImpl
  :: (Value -> ForeignOutcome)
  -> (P.String -> ForeignOutcome)
  -> HostExport
  -> ForeignBody
