-- | The foreign manifest
-- | ([Foreign Manifest](../../../../docs/technical-references/05-Backend/04-Foreign-Manifest.md)).
-- |
-- | A `foreign` declaration says a name and a type and nothing about what carries it
-- | out. A manifest is where that is said: one file per program, naming for each
-- | module the thing a runtime reaches its implementations through.
-- |
-- | **What is read here is the envelope, and the payload is left alone.** The field
-- | `module` is the only one inside an entry that this format fixes; everything
-- | beside it belongs to the target the file names, and passing it through unread is
-- | what keeps the format open to a backend nothing here knows about (D43).
module Stella.Compiler.ForeignManifest
  ( Manifest
  , ManifestEntry
  , ManifestError(..)
  , formatVersion
  , parse
  , entryFor
  ) where

import Prelude

import Prim as P

import Data.Argonaut.Core (Json, caseJsonObject, toArray, toNumber, toString)
import Data.Argonaut.Parser (jsonParser)
import Data.Either (Either(..), note)
import Data.Foldable (foldM)
import Data.Generic.Rep (class Generic)
import Data.Int (fromNumber)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Show.Generic (genericShow)
import Data.Traversable (traverse)
import Foreign.Object as Object
import Stella.Compiler.TypedCore.Name (ModuleName(..))

-- | The version of the format this module reads and writes.
formatVersion :: P.Int
formatVersion = 1

type Manifest =
  { target :: P.String
  , entries :: Map ModuleName ManifestEntry
  }

-- | One module's implementations, as the target it was written for describes them.
-- |
-- | `payload` is the entry with `module` still in it, handed on whole: the handler
-- | that understands the target is the one that reads it, and nothing between here
-- | and there needs to.
type ManifestEntry =
  { module :: ModuleName
  , payload :: Json
  }

data ManifestError
  = NotJson P.String
  -- | The version this reader implements, and the one the file names.
  | UnknownFormatVersion P.Int P.Int
  -- | The target this reader is, and the one the file names. **Not read past**: the
  -- | payloads describe a machine that is not this one.
  | WrongTarget P.String P.String
  -- | A field the format fixes, absent or of the wrong shape.
  | MalformedManifest P.String
  -- | One module named twice. **First-wins and last-wins both make the meaning
  -- | depend on the order of writing**, which a hand-edited or half-updated file
  -- | cannot be trusted about.
  | ModuleTwice ModuleName

-- | Read a manifest, for a runtime that is the target named.
parse :: P.String -> P.String -> Either ManifestError Manifest
parse target source = do
  json <- case jsonParser source of
    Left err -> Left (NotJson err)
    Right json -> Right json
  fields <- object "the manifest" json
  version <- intField fields "formatVersion"
  when (version /= formatVersion)
    (Left (UnknownFormatVersion formatVersion version))
  named <- stringField fields "target"
  when (named /= target) (Left (WrongTarget target named))
  raw <- arrayField fields "modules"
  entries <- traverse entry raw
  collected <- foldM insert Map.empty entries
  pure { target: named, entries: collected }
  where
  entry json = do
    fields <- object "a module entry" json
    name <- stringField fields "module"
    pure { module: ModuleName name, payload: json }

  insert acc e
    | Map.member e.module acc = Left (ModuleTwice e.module)
    | otherwise = Right (Map.insert e.module e acc)

-- | What the manifest says about that module, where it says anything.
-- |
-- | **An entry for a module nothing declares against is never asked for**, so a
-- | manifest holding one costs nothing and reaches nothing.
entryFor :: Manifest -> ModuleName -> Maybe ManifestEntry
entryFor manifest name = Map.lookup name manifest.entries

-- Reading the fields the format fixes -------------------------------------------------

object :: P.String -> Json -> Either ManifestError (Object.Object Json)
object what = caseJsonObject (Left (MalformedManifest (what <> " is not an object"))) Right

field :: Object.Object Json -> P.String -> Either ManifestError Json
field fields name =
  note (MalformedManifest ("no `" <> name <> "`")) (Object.lookup name fields)

stringField :: Object.Object Json -> P.String -> Either ManifestError P.String
stringField fields name = do
  json <- field fields name
  note (MalformedManifest ("`" <> name <> "` is not a string")) (toString json)

intField :: Object.Object Json -> P.String -> Either ManifestError P.Int
intField fields name = do
  json <- field fields name
  note (MalformedManifest ("`" <> name <> "` is not a whole number"))
    (fromNumber =<< toNumber json)

arrayField :: Object.Object Json -> P.String -> Either ManifestError (P.Array Json)
arrayField fields name = do
  json <- field fields name
  note (MalformedManifest ("`" <> name <> "` is not an array")) (toArray json)

derive instance Eq ManifestError
derive instance Generic ManifestError _

instance Show ManifestError where
  show = genericShow
