-- | `stella.json`: the modules to build with their files, the modules built
-- | elsewhere with theirs, and the options. Whatever drives the compiler
-- | writes it.
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
-- | no string is empty. Relative paths are resolved against the file's
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
  , decode
  , load
  , printConfigError
  , normalize
  ) where

import Prelude

import Data.Argonaut.Core (Json, toArray, toBoolean, toNumber, toObject, toString)
import Data.Argonaut.Parser (jsonParser)
import Data.Array as Array
import Data.Array.NonEmpty (NonEmptyArray)
import Data.Array.NonEmpty as NonEmptyArray
import Data.Either (Either(..))
import Data.Foldable (foldl)
import Data.Generic.Rep (class Generic)
import Data.Int (fromNumber)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.Set as Set
import Data.Show.Generic (genericShow)
import Data.String as String
import Data.String.CodeUnits as SCU
import Data.Traversable (for, traverse)
import Data.Tuple (Tuple(..))
import Data.Validation.Semigroup (V, invalid, toEither)
import Fmt (fmt)
import Foreign.Object (Object)
import Foreign.Object as Object
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

-- | What is wrong with a file. All but the first two name the field they are
-- | about by its place, such as `options.logLevel` or `modules[2].path`.
data ConfigError
  = Unreadable String
  | NotJson String
  | Missing String
  | NotTaken String
  -- | A field, and the kind of value it must have.
  | NotOfKind String String
  | EmptyString String
  | OtherFormatVersion Int
  -- | A field, and what it holds.
  | NotAModuleName String String
  | NotALogLevel String String
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

-- | What a field gives, or every error found in it.
type Checked = V (Array ConfigError)

-- | `stella.json` as written, its paths not yet resolved.
decode :: String -> Either (NonEmptyArray ConfigError) Config
decode text = case jsonParser text of
  Left why -> Left (pure (NotJson why))
  Right json -> case toEither (file json) of
    Left errors -> Left (fromMaybe (pure (NotJson "no error said")) (NonEmptyArray.fromArray errors))
    Right config -> Right config
  where
  file json = fields "" [ "formatVersion", "options", "modules", "dependencies" ] json `andThen` \o ->
    ( { options: _, modules: _, dependencies: _ }
        <$ field o "" "formatVersion" version
        <*> field o "" "options" options
        <*> field o "" "modules" (list module_)
        <*> field o "" "dependencies" (list dependency)
    )

  version at json = case fromNumber =<< toNumber json of
    Nothing -> invalid [ NotOfKind at "a whole number" ]
    Just v
      | v == formatVersion -> pure unit
      | otherwise -> invalid [ OtherFormatVersion v ]

  options at json = fields at [ "output", "emitCore", "traceOptimizer", "steamCmd", "logLevel", "monochrome" ] json `andThen` \o ->
    { output: _, emitCore: _, traceOptimizer: _, steamCmd: _, logLevel: _, monochrome: _ }
      <$> field o at "output" string
      <*> field o at "emitCore" boolean
      <*> field o at "traceOptimizer" (list moduleName)
      <*> field o at "steamCmd" string
      <*> field o at "logLevel" logLevel
      <*> field o at "monochrome" boolean

  module_ at json = fields at [ "module", "path" ] json `andThen` \o ->
    (\name path -> { module: name, path, written: path })
      <$> field o at "module" moduleName
      <*> field o at "path" string

  dependency at json = fields at [ "module", "interface", "object" ] json `andThen` \o ->
    { module: _, interface: _, object: _ }
      <$> field o at "module" moduleName
      <*> field o at "interface" string
      <*> field o at "object" string

  logLevel at json = string at json `andThen` case _ of
    "debug" -> pure Debug
    "info" -> pure Info
    "warn" -> pure Warn
    "error" -> pure Error
    other -> invalid [ NotALogLevel at other ]

  moduleName at json = string at json `andThen` \name ->
    if Array.all isProperName (String.split (String.Pattern ".") name) then pure (ModuleName name)
    else invalid [ NotAModuleName at name ]

-- | The fields of an object: exactly the ones named.
fields :: String -> Array String -> Json -> Checked (Object Json)
fields at names json = case toObject json of
  Nothing -> invalid [ NotOfKind (orFile at) "an object" ]
  Just o ->
    let
      missing = Array.filter (\n -> not (Object.member n o)) names
      other = Array.filter (\n -> not (Array.elem n names)) (Array.sort (Object.keys o))
    in
      if Array.null missing && Array.null other then pure o
      else invalid (map (Missing <<< inside at) missing <> map (NotTaken <<< inside at) other)
  where
  orFile a = if a == "" then "the file" else a

-- | A field of the object, read by the reader given.
field :: forall a. Object Json -> String -> String -> (String -> Json -> Checked a) -> Checked a
field o at name read = maybe (invalid [ Missing (inside at name) ]) (read (inside at name)) (Object.lookup name o)

inside :: String -> String -> String
inside at name = if at == "" then name else fmt @"{at}.{name}" { at, name }

list :: forall a. (String -> Json -> Checked a) -> String -> Json -> Checked (Array a)
list read at json = case toArray json of
  Nothing -> invalid [ NotOfKind at "a list" ]
  Just items -> traverse (\(Tuple i item) -> read (fmt @"{at}[{i}]" { at, i }) item) (Array.mapWithIndex Tuple items)

string :: String -> Json -> Checked String
string at json = case toString json of
  Nothing -> invalid [ NotOfKind at "a string" ]
  Just "" -> invalid [ EmptyString at ]
  Just s -> pure s

boolean :: String -> Json -> Checked Boolean
boolean at json = maybe (invalid [ NotOfKind at "a boolean" ]) pure (toBoolean json)

andThen :: forall a b. Checked a -> (a -> Checked b) -> Checked b
andThen checked next = case toEither checked of
  Left errors -> invalid errors
  Right a -> next a

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
  Missing at -> fmt @"{file}: `{at}` is missing" { file, at }
  NotTaken at -> fmt @"{file}: `{at}` is no field this compiler takes" { file, at }
  NotOfKind at kind -> fmt @"{file}: `{at}` is not {kind}" { file, at, kind }
  EmptyString at -> fmt @"{file}: `{at}` is empty" { file, at }
  OtherFormatVersion v -> fmt @"{file}: `formatVersion` is {v}; this compiler reads version {formatVersion}" { file, v, formatVersion }
  NotAModuleName at name -> fmt @"{file}: `{at}`, `{name}`, is no module's name" { file, at, name }
  NotALogLevel at level -> fmt @"{file}: `{at}`, `{level}`, is none of `debug`, `info`, `warn`, and `error`" { file, at, level }
  ListedTwice at m -> fmt @"{file}: `{at}` lists `{m}` more than once" { file, at, m: text m }
  FileTwice at path -> fmt @"{file}: `{at}`, `{path}`, is a file `modules` lists before it" { file, at, path }
  PrimListed at -> fmt @"{file}: `{at}` is `Prim`, which the compiler provides" { file, at }
  BuiltAndDepended m -> fmt @"{file}: `{m}` is listed by both `modules` and `dependencies`" { file, m: text m }
  TracedUnlisted at m -> fmt @"{file}: `{at}`, `{m}`, is no module `modules` lists" { file, at, m: text m }
  TracedTwice m -> fmt @"{file}: `options.traceOptimizer` names `{m}` more than once" { file, m: text m }
  where
  text (ModuleName m) = m
