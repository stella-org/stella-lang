-- | `validate` is the one statement of what a descriptor must be of the
-- | bytecode it lists, so that every runner holds it to the same rules.
module Stella.Compiler.ProgramDescriptor
  ( Descriptor
  , Listed
  , DescriptorError(..)
  , formatVersion
  , parse
  , print
  , validate
  ) where

import Prelude

import Prim as P

import Data.Argonaut.Core (Json, caseJsonObject, fromArray, fromNumber, fromObject, fromString, stringifyWithIndent, toArray, toNumber, toObject, toString)
import Data.Argonaut.Parser (jsonParser)
import Data.Array as Array
import Data.Either (Either(..), note)
import Data.Foldable (for_, foldM)
import Data.Generic.Rep (class Generic)
import Data.Int (fromNumber, toNumber) as Int
import Data.Maybe (Maybe(..), maybe)
import Data.Set (Set)
import Data.Set as Set
import Data.Show.Generic (genericShow)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Foreign.Object (Object)
import Foreign.Object as Object
import Stella.Compiler.Bytecode.Module (Dmo)
import Stella.Compiler.TypedCore.Name (Ident(..), ModuleName(..), Qualified(..))
import Stella.Compiler.TypedCore.Prim (primModule)

formatVersion :: P.Int
formatVersion = 0

type Listed = { module :: ModuleName, object :: P.String }

-- | `foreign` is kept as written: reading it is for a runner of the target it
-- | names.
type Descriptor =
  { entry :: Qualified Ident
  , modules :: P.Array Listed
  , foreign :: Maybe Json
  }

data DescriptorError
  = NotJson P.String
  | UnknownFormatVersion P.Int P.Int
  | MalformedDescriptor P.String
  | UnknownField P.String P.String
  | ModuleTwice ModuleName
  | EntryUnlisted ModuleName
  | ObjectOfAnother ModuleName ModuleName
  | ImportNotBefore ModuleName ModuleName
  | Unreached ModuleName
  | NoEntryGlobal (Qualified Ident)
  | ObjectsUnmatched P.Int P.Int

derive instance Eq DescriptorError
derive instance Generic DescriptorError _

instance Show DescriptorError where
  show = genericShow

parse :: P.String -> Either DescriptorError Descriptor
parse source = do
  json <- case jsonParser source of
    Left err -> Left (NotJson err)
    Right json -> Right json
  fields <- object "the descriptor" [ "formatVersion", "entry", "modules", "foreign" ] json
  version <- intField fields "formatVersion"
  when (version /= formatVersion) (Left (UnknownFormatVersion formatVersion version))
  entryFields <- object "`entry`" [ "module", "global" ] =<< field fields "entry"
  entry <- Qualified <$> (ModuleName <$> stringField entryFields "module") <*> (Ident <$> stringField entryFields "global")
  modules <- traverse listed =<< arrayField fields "modules"
  _ <- foldM once Set.empty modules
  let Qualified entryModule _ = entry
  unless (Array.any (\m -> m.module == entryModule) modules) (Left (EntryUnlisted entryModule))
  foreign' <- case Object.lookup "foreign" fields of
    Nothing -> Right Nothing
    Just f -> Just f <$ note (MalformedDescriptor "`foreign` is not an object") (toObject f)
  pure { entry, modules, foreign: foreign' }
  where
  listed json = do
    fields <- object "a module entry" [ "module", "object" ] json
    { module: _, object: _ } <$> (ModuleName <$> stringField fields "module") <*> stringField fields "object"

  once seen m
    | Set.member m.module seen = Left (ModuleTwice m.module)
    | otherwise = Right (Set.insert m.module seen)

print :: Descriptor -> P.String
print d = stringifyWithIndent 2 $ fromObject $ Object.fromFoldable $
  [ Tuple "formatVersion" (fromNumber (Int.toNumber formatVersion))
  , Tuple "entry" (fromObject (Object.fromFoldable [ Tuple "module" (fromString (moduleText entryModule)), Tuple "global" (fromString global) ]))
  , Tuple "modules" (fromArray (map (\m -> fromObject (Object.fromFoldable [ Tuple "module" (fromString (moduleText m.module)), Tuple "object" (fromString m.object) ])) d.modules))
  ]
    <> maybe [] (\f -> [ Tuple "foreign" f ]) d.foreign
  where
  Qualified entryModule (Ident global) = d.entry
  moduleText (ModuleName m) = m

-- | Exactly the runtime closure, so that a runner initializes nothing the
-- | program never reaches.
validate :: Descriptor -> P.Array Dmo -> Either DescriptorError Unit
validate d dmos = do
  unless (Array.length d.modules == Array.length dmos) (Left (ObjectsUnmatched (Array.length d.modules) (Array.length dmos)))
  for_ (Array.zip d.modules dmos) \(Tuple m dmo) ->
    when (dmo.name /= m.module) (Left (ObjectOfAnother m.module dmo.name))
  _ <- foldM before Set.empty dmos
  let reached = reach Set.empty [ entryModule ]
  for_ d.modules \m -> unless (Set.member m.module reached) (Left (Unreached m.module))
  case Array.find (\dmo -> dmo.name == entryModule) dmos of
    Just dmo | Array.any (\g -> g.name == d.entry) dmo.globals -> Right unit
    _ -> Left (NoEntryGlobal d.entry)
  where
  Qualified entryModule _ = d.entry

  importsOf m = maybe [] runtimeImports (Array.find (\dmo -> dmo.name == m) dmos)
  runtimeImports dmo = Array.filter (_ /= primModule) dmo.imports

  before :: Set ModuleName -> Dmo -> Either DescriptorError (Set ModuleName)
  before loaded dmo = do
    for_ (runtimeImports dmo) \i -> unless (Set.member i loaded) (Left (ImportNotBefore dmo.name i))
    pure (Set.insert dmo.name loaded)

  reach seen = case _ of
    [] -> seen
    pending -> case Array.uncons pending of
      Nothing -> seen
      Just { head, tail }
        | Set.member head seen -> reach seen tail
        | otherwise -> reach (Set.insert head seen) (tail <> importsOf head)

object :: P.String -> P.Array P.String -> Json -> Either DescriptorError (Object Json)
object what taken = caseJsonObject (Left (MalformedDescriptor (what <> " is not an object"))) \fields ->
  case Array.find (\k -> not (Array.elem k taken)) (Array.sort (Object.keys fields)) of
    Just other -> Left (UnknownField what other)
    Nothing -> Right fields

field :: Object Json -> P.String -> Either DescriptorError Json
field fields name =
  note (MalformedDescriptor ("no `" <> name <> "`")) (Object.lookup name fields)

stringField :: Object Json -> P.String -> Either DescriptorError P.String
stringField fields name = do
  json <- field fields name
  case toString json of
    Just s | s /= "" -> Right s
    _ -> Left (MalformedDescriptor ("`" <> name <> "` is not a non-empty string"))

intField :: Object Json -> P.String -> Either DescriptorError P.Int
intField fields name = do
  json <- field fields name
  note (MalformedDescriptor ("`" <> name <> "` is not a whole number"))
    (Int.fromNumber =<< toNumber json)

arrayField :: Object Json -> P.String -> Either DescriptorError (P.Array Json)
arrayField fields name = do
  json <- field fields name
  note (MalformedDescriptor ("`" <> name <> "` is not an array")) (toArray json)
