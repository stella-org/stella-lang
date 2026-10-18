-- | `--dependencies`: the interfaces of modules built elsewhere, which a build
-- | is compiled against.
-- |
-- | The **dependency map** is a JSON file naming, for each module, its
-- | interface (`.dmi`) and its bytecode (`.dmo`):
-- |
-- | ```json
-- | { "formatVersion": 0,
-- |   "modules": [ { "module": "Lib.Core", "interface": "lib/Lib.Core.dmi", "object": "lib/Lib.Core.dmo" } ] }
-- | ```
-- |
-- | A relative path is resolved against the directory the map stands in. Every
-- | interface the map lists is read and checked, whether or not the build
-- | imports it; a bytecode path is resolved and kept, and not read. The
-- | interfaces are added to the build environment in the order their imports
-- | give, whatever order the map lists them in, so each imports only modules of
-- | the map and modules the compiler provides. Artifacts are supported only
-- | where the compiler build reading them is the one that wrote them.
module Stellac.Dependencies
  ( Dependency
  , Loaded
  , DependencyError(..)
  , formatVersion
  , parse
  , extend
  , dependedOn
  , printDependencyError
  ) where

import Prelude

import Data.Argonaut.Core (Json, caseJsonObject, toArray, toNumber, toString)
import Data.Argonaut.Parser (jsonParser)
import Data.Array as Array
import Data.Array.NonEmpty (NonEmptyArray)
import Data.Array.NonEmpty as NonEmptyArray
import Data.Either (Either(..), either, note)
import Data.Foldable (foldl)
import Data.Generic.Rep (class Generic)
import Data.Int (fromNumber)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), isJust, maybe)
import Data.Set (Set)
import Data.Set as Set
import Data.Show.Generic (genericShow)
import Data.String as String
import Data.Traversable (for, traverse)
import Data.Tuple (Tuple(..))
import Fmt (fmt)
import Foreign.Object (Object)
import Foreign.Object as Object
import Run (Run)
import Run.Except (EXCEPT, throw)
import Run.Except as Except
import Stella.CLI.Effect.FS (FS, FilePath)
import Stella.CLI.Effect.FS as FS
import Stella.Compiler.Bytecode.Bytes (DecodeError)
import Stella.Compiler.Interface.Environment (BuildEnvironment, EnvironmentError(..), addInterface, lookupInterface)
import Stella.Compiler.Interface.File as Interface
import Stella.Compiler.Interface.Module (ModuleInterface)
import Stella.Compiler.TypedCore (ModuleName(..))
import Type.Row (type (+))

-- | A module the map lists, with its two paths.
type Dependency = { module :: ModuleName, interface :: FilePath, object :: FilePath }

-- | A listed module and the interface its file holds.
type Loaded = { dependency :: Dependency, interface :: ModuleInterface }

data DependencyError
  = MapUnreadable FilePath String
  | MapMalformed FilePath String
  | NoFormatVersion FilePath
  | UnsupportedFormatVersion FilePath Int
  | ListedTwice ModuleName
  | InterfaceUnreadable Dependency String
  | InterfaceRejected Dependency DecodeError
  -- | A file holding the interface of another module than the one listed, the
  -- | second name.
  | InterfaceOfAnother Dependency ModuleName
  | ProvidedByCompiler ModuleName
  -- | An import of a listed module, the second name, that is neither listed nor
  -- | in the environment the map extends.
  | ImportUnlisted ModuleName ModuleName
  -- | Listed modules importing one another, in order of their names.
  | ImportCycle (NonEmptyArray ModuleName)

derive instance Eq DependencyError
derive instance Generic DependencyError _

instance Show DependencyError where
  show = genericShow

-- | The version of the map this compiler reads.
formatVersion :: Int
formatVersion = 0

-- | The entries of the map at the path given, their paths as written.
parse :: FilePath -> String -> Either DependencyError (Array Dependency)
parse path source = do
  json <- either (Left <<< malformed) Right (jsonParser source)
  fields <- object "the map" json
  version <- case Object.lookup "formatVersion" fields of
    Nothing -> Left (NoFormatVersion path)
    Just v -> note (malformed "`formatVersion` is not a whole number") (fromNumber =<< toNumber v)
  when (version /= formatVersion) (Left (UnsupportedFormatVersion path version))
  modules <- note (malformed "the map has no `modules`") (Object.lookup "modules" fields)
  traverse entry =<< note (malformed "`modules` is not an array") (toArray modules)
  where
  malformed = MapMalformed path

  entry json = do
    fields <- object "an entry of `modules`" json
    name <- stringField fields "module"
    interface <- stringField fields "interface"
    obj <- stringField fields "object"
    pure { module: ModuleName name, interface, object: obj }

  object :: String -> Json -> Either DependencyError (Object Json)
  object what = caseJsonObject (Left (malformed (fmt @"{what} is not an object" { what }))) Right

  stringField fields name = do
    json <- note (malformed (fmt @"an entry of `modules` has no `{name}`" { name })) (Object.lookup name fields)
    note (malformed (fmt @"`{name}` is not a string" { name })) (toString json)

-- | The environment given, with the interfaces added by `addInterface` in the
-- | order their imports give. A listed module is ready once the environment
-- | holds every module it imports, or holds the module itself, which
-- | `addInterface` then refuses; the modules ready together are added in order
-- | of their names. Where none is ready, an import of a module neither listed
-- | nor in the environment is reported, and so is each set of listed modules
-- | importing one another; a module that only imports one of those is not.
extend :: BuildEnvironment -> Array Loaded -> Either (NonEmptyArray DependencyError) BuildEnvironment
extend base loaded = go base [] (Array.sortWith _.dependency.module loaded)
  where
  go env errors pending = case Array.partition (ready env) pending of
    { yes: [], no: [] } -> finish env errors
    { yes: [], no: waiting } -> finish env (errors <> stuck env waiting)
    { yes, no: waiting } ->
      let
        added = foldl add { env, errors } yes
      in
        go added.env added.errors waiting

  finish env errors = maybe (Right env) Left (NonEmptyArray.fromArray (Array.nubEq errors))

  ready env l =
    Map.member l.interface.name env.interfaces
      || Array.all (\m -> isJust (lookupInterface m env)) l.interface.imports

  add acc l = case addInterface l.interface acc.env of
    Right env -> acc { env = env }
    Left err -> acc { errors = Array.snoc acc.errors (refused l err) }

  refused l = case _ of
    ModuleTwice m
      | Map.member m base.interfaces -> ProvidedByCompiler m
      | otherwise -> ListedTwice m
    ImportNotAdded m missing -> ImportUnlisted m missing
    NotInEnvironment missing -> ImportUnlisted l.interface.name missing

  stuck env waiting =
    let
      names = Set.fromFoldable (map _.interface.name waiting)
      unlisted l = Array.filter (\m -> not (Set.member m names || isJust (lookupInterface m env))) l.interface.imports
      edges = Map.fromFoldableWith (<>) (map (\l -> Tuple l.interface.name (Array.filter (\m -> Set.member m names) l.interface.imports)) waiting)
    in
      (waiting >>= \l -> map (ImportUnlisted l.interface.name) (unlisted l))
        <> map ImportCycle (cycles names edges)

-- | The sets of names reaching one another through the edges, each in order of
-- | the names and listed by its least; a name on no cycle is in none.
cycles :: Set ModuleName -> Map ModuleName (Array ModuleName) -> Array (NonEmptyArray ModuleName)
cycles names edges = Array.mapMaybe component (Set.toUnfoldable names)
  where
  successors m = maybe [] identity (Map.lookup m edges)

  reach m = visit Set.empty (successors m)

  visit seen todo = case Array.uncons todo of
    Nothing -> seen
    Just { head, tail }
      | Set.member head seen -> visit seen tail
      | otherwise -> visit (Set.insert head seen) (tail <> successors head)

  component m =
    let
      from = reach m
      members = Set.insert m (Set.filter (\o -> Set.member m (reach o)) from)
    in
      if Set.member m from && Set.findMin members == Just m then NonEmptyArray.fromFoldable members
      else Nothing

-- | The environment given, extended with the interfaces the map at the path
-- | given lists, and the entries of the map, their paths resolved.
dependedOn
  :: forall r
   . FilePath
  -> BuildEnvironment
  -> Run (FS + r) (Either (NonEmptyArray DependencyError) { environment :: BuildEnvironment, dependencies :: Array Dependency })
dependedOn path env = Except.runExcept do
  source <- FS.readText path >>= either (throw <<< pure <<< MapUnreadable path) pure
  written <- either (throw <<< pure) pure (parse path source)
  entries <- for written \e -> do
    interface <- resolved e.interface
    obj <- resolved e.object
    pure e { interface = interface, object = obj }
  results <- for entries (Except.runExcept <<< load)
  case NonEmptyArray.fromArray (Array.mapMaybe (either Just (const Nothing)) results) of
    Just errors -> throw errors
    Nothing -> do
      environment <- either throw pure (extend env (Array.mapMaybe (either (const Nothing) Just) results))
      pure { environment, dependencies: entries }
  where
  -- the directory of the map, which a map named without one has none of
  base = map (\i -> String.take i path) (String.lastIndexOf (String.Pattern "/") path)

  resolved :: forall r'. FilePath -> Run (FS + r') FilePath
  resolved p = FS.isAbsolute p <#> case _, base of
    false, Just dir -> fmt @"{dir}/{p}" { dir, p }
    _, _ -> p

  load :: forall r'. Dependency -> Run (EXCEPT DependencyError + FS + r') Loaded
  load d = do
    bytes <- FS.readBytes d.interface >>= either (throw <<< InterfaceUnreadable d) pure
    stored <- either (throw <<< InterfaceRejected d) pure (Interface.decode bytes)
    when (stored.interface.name /= d.module) (throw (InterfaceOfAnother d stored.interface.name))
    pure { dependency: d, interface: stored.interface }

printDependencyError :: DependencyError -> String
printDependencyError = case _ of
  MapUnreadable path why -> fmt @"The dependency map `{path}` could not be read: {why}" { path, why }
  MapMalformed path why -> fmt @"The dependency map `{path}` is malformed: {why}" { path, why }
  NoFormatVersion path -> fmt @"The dependency map `{path}` gives no `formatVersion`; this compiler reads version {formatVersion}" { path, formatVersion }
  UnsupportedFormatVersion path v -> fmt @"The dependency map `{path}` is of format version {v}; this compiler reads version {formatVersion}" { path, v, formatVersion }
  ListedTwice m -> fmt @"The dependency map lists `{m}` more than once" { m: text m }
  InterfaceUnreadable d why -> fmt @"The interface of `{m}`, `{path}`, could not be read: {why}" { m: text d.module, path: d.interface, why }
  InterfaceRejected d err -> fmt @"The interface of `{m}`, `{path}`, is not one this compiler reads: {why}" { m: text d.module, path: d.interface, why: show err }
  InterfaceOfAnother d other -> fmt @"The dependency map gives `{path}` as the interface of `{m}`, but it is the interface of `{other}`" { path: d.interface, m: text d.module, other: text other }
  ProvidedByCompiler m -> fmt @"The dependency map lists `{m}`, which the compiler provides" { m: text m }
  ImportUnlisted m missing -> fmt @"The interface of `{m}` imports `{missing}`, which the dependency map does not list" { m: text m, missing: text missing }
  ImportCycle members -> fmt @"These modules of the dependency map import one another: {names}" { names: String.joinWith ", " (map text (NonEmptyArray.toArray members)) }
  where
  text (ModuleName m) = m
