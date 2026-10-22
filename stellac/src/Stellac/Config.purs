-- | `stella.json`: the modules to build with their files, the modules built
-- | elsewhere with theirs, and the options. Whatever drives the compiler
-- | writes it, and `codec` both reads and writes it.
-- |
-- | ```json
-- | { "formatVersion": 0,
-- |   "options": { "output": "output", "emitCore": false, "traceOptimizer": [],
-- |                "steamCmd": "steam", "logLevel": "info", "monochrome": false },
-- |   "modules": [ { "module": "A.B", "path": "src/A/B.stel" } ],
-- |   "dependencies": [ { "module": "Lib.Core", "interface": "lib/Lib.Core.dmi", "object": "lib/Lib.Core.dmo" } ] }
-- | ```
-- |
-- | Every field is required and no other is accepted. Each has one kind, and
-- | no string is empty. A file the codec refuses is reported by the first
-- | field found wrong. Relative paths are resolved against the file's
-- | directory and normalized. `steamCmd` is resolved only when it contains
-- | a `/`, and then to an absolute path so that it stays a path; a bare name is
-- | looked up on `PATH`.
-- |
-- | The rules checked here are those of the file, which every command checks:
-- | no module twice in `modules` or in `dependencies`, no file twice in
-- | `modules` (compared once resolved), no `Prim`, no module in both lists, and
-- | `traceOptimizer` naming listed modules once each. Rules of the build
-- | environment, such as a seed module in `modules`, belong to the command
-- | that builds.
module Stellac.Config
  ( Config
  , Options
  , Listed
  , ConfigError(..)
  , formatVersion
  , codec
  , decode
  , encode
  , load
  , printConfigError
  , normalize
  ) where

import Prelude

import Data.Argonaut.Core (stringify, stringifyWithIndent, toString)
import Data.Argonaut.Parser (jsonParser)
import Data.Array as Array
import Data.Array.NonEmpty (NonEmptyArray)
import Data.Array.NonEmpty as NonEmptyArray
import Data.Bifunctor (lmap)
import Data.Codec as Codec
import Data.Codec.Argonaut (JsonCodec, JsonDecodeError(..))
import Data.Codec.Argonaut as CA
import Data.Codec.Argonaut.Record as CAR
import Data.Either (Either(..))
import Data.Foldable (foldl)
import Data.Generic.Rep (class Generic)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Profunctor (dimap)
import Data.Set as Set
import Data.Show.Generic (genericShow)
import Data.String as String
import Data.String.CodeUnits as SCU
import Data.Traversable (for)
import Data.Tuple (Tuple(..))
import Fmt (fmt)
import Foreign.Object as Object
import Prim.RowList as RL
import Record.Extra (class Keys, keys)
import Run (Run)
import Stella.CLI.Effect.FS (FS, FilePath)
import Stella.CLI.Effect.FS as FS
import Stella.CLI.Effect.Log (LogLevel(..))
import Stella.Compiler.TypedCore (ModuleName(..))
import Stella.Compiler.TypedCore.Prim (primModule)
import Stellac.Dependencies (Dependency)
import Type.Row (type (+))

-- | The version of the file this compiler reads.
formatVersion :: Int
formatVersion = 0

type Options =
  { output :: FilePath
  , emitCore :: Boolean
  , traceOptimizer :: Array ModuleName
  , steamCmd :: String
  , logLevel :: LogLevel
  , monochrome :: Boolean
  }

-- | A module to build: its name, its file resolved, and its file as written.
type Listed = { module :: ModuleName, path :: FilePath, written :: String }

type Config =
  { options :: Options
  , modules :: Array Listed
  , dependencies :: Array Dependency
  }

-- | What is wrong with a file. A rule of the file names the field it is about
-- | by its place, such as `options.traceOptimizer[2]` or `modules[2].path`.
data ConfigError
  = Unreadable String
  | NotJson String
  | Undecodable JsonDecodeError
  -- | `modules` or `dependencies`, and the module it lists more than once.
  | ListedTwice String ModuleName
  -- | A field naming a file an earlier entry of `modules` names, and the file
  -- | as written there.
  | FileTwice String String
  | PrimListed String
  | BuiltAndDepended ModuleName
  -- | A field of `traceOptimizer`, and the module it names.
  | TracedUnlisted String ModuleName
  | TracedTwice ModuleName

derive instance Eq ConfigError
derive instance Generic ConfigError _

instance Show ConfigError where
  show = genericShow

-- | `stella.json` as written, its paths not yet resolved. Writing a `Listed`
-- | writes its `path`; reading one gives the path as `written` too.
codec :: JsonCodec Config
codec =
  dimap (\c -> { formatVersion: unit, options: c.options, modules: c.modules, dependencies: c.dependencies })
    (\c -> { options: c.options, modules: c.modules, dependencies: c.dependencies })
    $ exactly "stella.json"
        { formatVersion: version
        , options: exactly "options"
            { output: nonEmpty
            , emitCore: CA.boolean
            , traceOptimizer: CA.array moduleName
            , steamCmd: nonEmpty
            , logLevel
            , monochrome: CA.boolean
            }
        , modules: CA.array listed
        , dependencies: CA.array (exactly "dependency" { module: moduleName, interface: nonEmpty, object: nonEmpty })
        }
  where
  version = CA.prismaticCodec (fmt @"{formatVersion}, the version this compiler reads" { formatVersion }) (\v -> if v == formatVersion then Just unit else Nothing) (const formatVersion) CA.int

  listed = dimap (\l -> { module: l.module, path: l.path }) (\l -> { module: l.module, path: l.path, written: l.path })
    $ exactly "module" { module: moduleName, path: nonEmpty }

  nonEmpty = CA.prismaticCodec "a string with something in it" (\s -> if s == "" then Nothing else Just s) identity CA.string

  moduleName = CA.prismaticCodec "a module's name" named (\(ModuleName m) -> m) CA.string
    where
    named m = if Array.all isProperName (String.split (String.Pattern ".") m) then Just (ModuleName m) else Nothing

  logLevel = CA.prismaticCodec "one of `debug`, `info`, `warn`, and `error`" level written CA.string
    where
    level = case _ of
      "debug" -> Just Debug
      "info" -> Just Info
      "warn" -> Just Warn
      "error" -> Just Error
      _ -> Nothing
    written = case _ of
      Debug -> "debug"
      Info -> "info"
      Warn -> "warn"
      Error -> "error"

-- | An object of exactly the fields the record gives a codec for. A field of
-- | no codec is refused as `AtKey` the field and `UnexpectedValue` alone,
-- | which no other codec of the file reports unnamed.
exactly
  :: forall ri ro rl
   . RL.RowToList ri rl
  => CAR.RowListCodec rl ri ro
  => Keys rl
  => String
  -> Record ri
  -> JsonCodec (Record ro)
exactly name codecs = Codec.codec' decoded (Codec.encode object)
  where
  object = CAR.object name codecs
  taken = Array.fromFoldable (keys codecs)
  decoded json = do
    fields <- Codec.decode CA.jobject json
    case Array.find (\k -> not (Array.elem k taken)) (Array.sort (Object.keys fields)) of
      Just other -> Left (Named name (AtKey other (UnexpectedValue (fromMaybe json (Object.lookup other fields)))))
      Nothing -> Codec.decode object json

-- | `stella.json` as written, its paths not yet resolved.
decode :: String -> Either (NonEmptyArray ConfigError) Config
decode text = case jsonParser text of
  Left why -> Left (pure (NotJson why))
  Right json -> lmap (pure <<< Undecodable) (Codec.decode codec json)

-- | The file as `codec` writes it, indented.
encode :: Config -> String
encode config = stringifyWithIndent 2 (Codec.encode codec config)

-- | A segment of a module's name: an upper case letter, then letters, digits,
-- | `_`, and `'`.
isProperName :: String -> Boolean
isProperName segment = case SCU.uncons segment of
  Just { head, tail } -> isUpper head && Array.all isNameChar (SCU.toCharArray tail)
  Nothing -> false
  where
  isUpper c = c >= 'A' && c <= 'Z'
  isNameChar c = c >= 'a' && c <= 'z' || isUpper c || c >= '0' && c <= '9' || c == '_' || c == '\''

-- | The file at the path given, decoded, its paths resolved, and checked
-- | against the rules of the file.
load :: forall r. FilePath -> Run (FS + r) (Either (NonEmptyArray ConfigError) Config)
load file = FS.readText file >>= case _ of
  Left why -> pure (Left (pure (Unreadable why)))
  Right text -> case decode text of
    Left errors -> pure (Left errors)
    Right written -> do
      output <- resolved written.options.output
      -- a command given as a path stays one: `./steam` normalizes to `steam`,
      -- so it is resolved to an absolute path
      steamCmd <-
        if String.contains (String.Pattern "/") written.options.steamCmd then resolved written.options.steamCmd >>= FS.resolve
        else pure written.options.steamCmd
      modules <- for written.modules \m -> m { path = _ } <$> resolved m.path
      dependencies <- for written.dependencies \d -> { module: d.module, interface: _, object: _ } <$> resolved d.interface <*> resolved d.object
      absolute <- for modules \m -> FS.resolve m.path
      let config = { options: written.options { output = output, steamCmd = steamCmd }, modules, dependencies }
      pure case NonEmptyArray.fromArray (fileRules config absolute) of
        Just errors -> Left errors
        Nothing -> Right config
  where
  -- the directory the file stands in
  directory = case String.lastIndexOf (String.Pattern "/") file of
    Just 0 -> "/"
    Just i -> String.take i file
    Nothing -> "."

  resolved :: forall r'. FilePath -> Run (FS + r') FilePath
  resolved path = FS.isAbsolute path <#> \absolute ->
    normalize (if absolute then path else fmt @"{directory}/{path}" { directory, path })

-- | The errors the rules of the file find, given the absolute path of each
-- | file of `modules`.
fileRules :: Config -> Array String -> Array ConfigError
fileRules config absolute =
  twice "modules" (map _.module config.modules)
    <> filesTwice
    <> primListed "modules" (map _.module config.modules)
    <> twice "dependencies" (map _.module config.dependencies)
    <> primListed "dependencies" (map _.module config.dependencies)
    <> map BuiltAndDepended (Array.filter (\m -> Set.member m built) (Array.nub (map _.module config.dependencies)))
    <> traced
  where
  built = Set.fromFoldable (map _.module config.modules)

  twice at names = map (ListedTwice at) (Array.fromFoldable (Map.keys (Map.filter (_ > 1) (counted names))))

  counted names = foldl (\acc n -> Map.insertWith (+) n 1 acc) Map.empty names

  filesTwice = (foldl seen { paths: Set.empty, errors: [] } (Array.mapWithIndex Tuple (Array.zip absolute config.modules))).errors
    where
    seen acc (Tuple i (Tuple path m))
      | Set.member path acc.paths = acc { errors = Array.snoc acc.errors (FileTwice (fmt @"modules[{i}].path" { i }) m.written) }
      | otherwise = acc { paths = Set.insert path acc.paths }

  primListed at names = Array.catMaybes (Array.mapWithIndex (\i n -> if n == primModule then Just (PrimListed (fmt @"{at}[{i}].module" { at, i })) else Nothing) names)

  traced =
    Array.catMaybes (Array.mapWithIndex (\i m -> if Set.member m built then Nothing else Just (TracedUnlisted (fmt @"options.traceOptimizer[{i}]" { i }) m)) config.options.traceOptimizer)
      <> map TracedTwice (Array.fromFoldable (Map.keys (Map.filter (_ > 1) (counted config.options.traceOptimizer))))

-- | A path with `.` and `..` taken away where possible. A leading `..` of a
-- | relative path stays; one above the root of an absolute path is dropped.
normalize :: FilePath -> FilePath
normalize path = case String.joinWith "/" segments, absolute of
  joined, true -> "/" <> joined
  "", false -> "."
  joined, false -> joined
  where
  absolute = String.take 1 path == "/"
  segments = foldl step [] (String.split (String.Pattern "/") path)
  step acc = case _ of
    "" -> acc
    "." -> acc
    ".." -> case Array.unsnoc acc of
      Just { init, last } | last /= ".." -> init
      _ | absolute -> acc
      _ -> Array.snoc acc ".."
    segment -> Array.snoc acc segment

printConfigError :: FilePath -> ConfigError -> String
printConfigError file = case _ of
  Unreadable why -> fmt @"`{file}` could not be read: {why}" { file, why }
  NotJson why -> fmt @"`{file}` is not JSON: {why}" { file, why }
  Undecodable error -> undecodable "" error
  ListedTwice at m -> fmt @"{file}: `{at}` lists `{m}` more than once" { file, at, m: text m }
  FileTwice at path -> fmt @"{file}: `{at}`, `{path}`, is a file `modules` lists before it" { file, at, path }
  PrimListed at -> fmt @"{file}: `{at}` is `Prim`, which the compiler provides" { file, at }
  BuiltAndDepended m -> fmt @"{file}: `{m}` is listed by both `modules` and `dependencies`" { file, m: text m }
  TracedUnlisted at m -> fmt @"{file}: `{at}`, `{m}`, is no module `modules` lists" { file, at, m: text m }
  TracedTwice m -> fmt @"{file}: `options.traceOptimizer` names `{m}` more than once" { file, m: text m }
  where
  text (ModuleName m) = m

  -- the field the error is about, by its place from the field given
  undecodable at = case _ of
    AtKey key error -> undecodable (if at == "" then key else fmt @"{at}.{key}" { at, key }) error
    AtIndex i error -> undecodable (fmt @"{at}[{i}]" { at, i }) error
    Named what (UnexpectedValue value) -> case shown value of
      "" -> fmt @"{file}: {place} is empty" { file, place: place at }
      given -> fmt @"{file}: {place}, `{given}`, is not {what}" { file, place: place at, given, what }
    Named _ error -> undecodable at error
    UnexpectedValue _ -> fmt @"{file}: {place} is no field this compiler takes" { file, place: place at }
    MissingValue -> fmt @"{file}: {place} is missing" { file, place: place at }
    TypeMismatch kind -> fmt @"{file}: {place} is not {kind}" { file, place: place at, kind: kindOf kind }

  place at = if at == "" then "the file" else fmt @"`{at}`" { at }

  shown value = fromMaybe (stringify value) (toString value)

  kindOf = case _ of
    "Object" -> "an object"
    "Array" -> "a list"
    "String" -> "a string"
    "Boolean" -> "a boolean"
    "Int" -> "a whole number"
    kind -> kind
