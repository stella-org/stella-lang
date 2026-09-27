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
import Data.Foldable (foldl)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Traversable (sequence, traverse)
import Data.Tuple (Tuple(..))
import Run (Run)
import Steam.CLI.Marshal (bodyFor, isCallable)
import Steam.Foreign (ForeignEntry, ForeignTable, emptyTable, insert)
import Steam.Load (claimedByInterpreter)
import Steam.Value (Value)
import Stella.CLI.Effect.Foreigns (FOREIGNS, reach)
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
  -- | The module's entry says nothing of how that foreign crosses, so there is no
  -- | signature to marshal its values by.
  | NoSignature ModuleName P.String
  -- | The entry's `params` are of a different length from the arity the module
  -- | declares, as the foreign, the declared arity, and the length. **Both came from
  -- | the same compiler**, so a disagreement is a defect in what produced them — or
  -- | a manifest and a `.dmo` that do not belong together — and is refused rather
  -- | than believed.
  | SignatureDisagrees ModuleName P.String P.Int P.Int

-- | The entries the foreigns of these modules need.
-- |
-- | `unit` is `Prim.Unit` under the identity the registry assigns it, which a `unit`
-- | result stands for.
-- |
-- | **A module the manifest does not name yields nothing rather than a failure.**
-- | What is unmet is a declaration, and the loader is where a declaration nothing
-- | carries out is refused — naming the foreign, which is what a reader can act on,
-- | rather than a file that was not consulted.
entriesFor
  :: forall r
   . P.String
  -> Maybe Manifest
  -> Value
  -> P.Array Dmo
  -> Run (FOREIGNS + r) (Either AssembleError (Map (Qualified Ident) ForeignEntry))
entriesFor base manifest unit modules = case manifest of
  Nothing -> pure (Right Map.empty)
  Just held -> do
    reached <- traverse (perModule held) declaring
    pure (map (Map.fromFoldable <<< Array.concat) (sequence reached))
  where
  -- **a name the interpreter claims is never looked up in a manifest**: it is
  -- carried out by the interpreter whatever an entry says, so an entry covering one
  -- is dead rather than an override, and is neither reached nor asked for a
  -- signature. One reach per host module, and only for a module that declares a
  -- foreign the host must supply
  declaring = Array.mapMaybe hostBacked modules

  hostBacked dmo = case Array.filter (\declared -> not (claimedByInterpreter declared.name)) dmo.foreigns of
    [] -> Nothing
    foreigns -> Just { name: dmo.name, foreigns }

  perModule held dmo = case entryFor held dmo.name of
    Nothing -> pure (Right [])
    Just entry -> do
      reached <- reach base entry
      pure case reached of
        Left reason -> Left (ModuleUnreachable dmo.name reason)
        Right exports -> traverse (entryOf dmo.name entry.foreigns exports) dmo.foreigns

  -- **the declared arity is adopted, and there is no second number**: a manifest
  -- carries none beside its `params`, and none can be read off a reached export
  entryOf name signatures exports declared = case declared.name of
    Qualified _ (Ident unqualified) -> case Map.lookup unqualified signatures of
      Nothing -> Left (NoSignature name unqualified)
      Just signature
        | Array.length signature.params /= declared.arity ->
            Left
              ( SignatureDisagrees name unqualified declared.arity
                  (Array.length signature.params)
              )
        | otherwise -> case Map.lookup unqualified exports of
            Nothing -> Left (NoSuchExport name unqualified)
            Just export
              | isCallable export ->
                  Right
                    ( Tuple declared.name
                        { arity: declared.arity
                        , body: bodyFor declared.name unit signature export
                        }
                    )
              | otherwise -> Left (ExportNotCallable name unqualified)

-- | The whole table for a run, which is given every module at once.
tableFor
  :: forall r
   . P.String
  -> Maybe Manifest
  -> Value
  -> P.Array Dmo
  -> Run (FOREIGNS + r) (Either AssembleError ForeignTable)
tableFor base manifest unit modules =
  map (map built) (entriesFor base manifest unit modules)
  where
  built entries = foldl (\table (Tuple name entry) -> insert name entry table) emptyTable
    (Map.toUnfoldable entries :: P.Array _)
