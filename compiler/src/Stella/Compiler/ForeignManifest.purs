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
  , ResultKind(..)
  , Signature
  , ValueKind(..)
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
import Data.Tuple (Tuple(..))
import Foreign.Object as Object
import Stella.Compiler.TypedCore.Name (ModuleName(..))

-- | The version of the format this module reads and writes.
formatVersion :: P.Int
formatVersion = 1

type Manifest =
  { target :: P.String
  , entries :: Map ModuleName ManifestEntry
  }

-- | How one value crosses the boundary.
-- |
-- | **A signature is derived from the declared type and written down because the
-- | runtime cannot derive it.** A `.dmo` carries no type, so without this the
-- | boundary would have to guess — and for a host value that is a number there is
-- | nothing to guess from, `Int` and `Number` being one host representation and two
-- | Stella values (D37).
data ValueKind
  = AsInt
  | AsNumber
  | AsChar
  | AsString
  | AsBoolean
  | AsUnit
  | AsOpaque

-- | How a result crosses. **An action stands here and nowhere else**: `IO (IO τ)` is
-- | not writable because it is not declarable (D44), and an argument of type `IO τ`
-- | is excluded the same way.
data ResultKind
  = AsValue ValueKind
  -- | What the action produces, `IO τ` losing its `τ` otherwise and the drive loop
  -- | having nothing to make a value out of once the action has run.
  | AsAction ValueKind

-- | How each argument and the result of one foreign crosses.
type Signature =
  { params :: P.Array ValueKind
  , result :: ResultKind
  }

-- | One module's implementations, as the target it was written for describes them.
-- |
-- | `payload` is the entry with `module` still in it, handed on whole: the handler
-- | that understands the target is the one that reads it, and nothing between here
-- | and there needs to.
type ManifestEntry =
  { module :: ModuleName
  , foreigns :: Map P.String Signature
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
  -- | One foreign named twice inside one entry, for the reason above read one level
  -- | down: an array makes order meaningful where order means nothing.
  | ForeignTwice ModuleName P.String
  -- | A `kind` this reader does not implement. **Rejected as an unknown
  -- | `formatVersion` is**: widening the kinds is what a later version does, and
  -- | reading past one would be guessing what it meant.
  | UnknownKind P.String

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
    let named = ModuleName name
    raw <- arrayField fields "foreigns"
    signatures <- traverse signature raw
    foreigns <- foldM (insertForeign named) Map.empty signatures
    pure { module: named, foreigns, payload: json }

  insertForeign named acc (Tuple name sig)
    | Map.member name acc = Left (ForeignTwice named name)
    | otherwise = Right (Map.insert name sig acc)

  signature json = do
    fields <- object "a foreign entry" json
    name <- stringField fields "name"
    params <- traverse valueKind =<< arrayField fields "params"
    result <- resultKind =<< field fields "result"
    pure (Tuple name { params, result })

  -- **the two grammars are separate so that the restriction is the format**: an
  -- action stands in a result and what it produces is a plain value
  resultKind json = case toString json of
    Just spelled -> map AsValue (kindNamed spelled)
    Nothing -> do
      fields <- object "a result" json
      map AsAction (valueKind =<< field fields "action")

  valueKind json = do
    spelled <- note (MalformedManifest "a kind is not a string") (toString json)
    kindNamed spelled

  kindNamed = case _ of
    "int" -> Right AsInt
    "number" -> Right AsNumber
    "char" -> Right AsChar
    "string" -> Right AsString
    "boolean" -> Right AsBoolean
    "unit" -> Right AsUnit
    "opaque" -> Right AsOpaque
    other -> Left (UnknownKind other)

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

derive instance Eq ValueKind
derive instance Generic ValueKind _

instance Show ValueKind where
  show = genericShow

derive instance Eq ResultKind
derive instance Generic ResultKind _

instance Show ResultKind where
  show = genericShow

derive instance Eq ManifestError
derive instance Generic ManifestError _

instance Show ManifestError where
  show = genericShow
