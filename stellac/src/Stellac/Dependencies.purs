-- | `dependencies` of `stella.json` ([Config](Config.purs)): the modules built
-- | elsewhere that a build is compiled against, each with the paths of its
-- | `.dmi` and `.dmo`, already resolved.
-- |
-- | Every listed interface is read and checked, whether or not the build
-- | imports it; bytecode paths are kept but not read. The interfaces enter the
-- | build environment in the order their imports give, whatever order they are
-- | listed in, so each may import only listed modules and those the compiler
-- | provides.
-- |
-- | A seed module may be listed with the interface of the seed module the
-- | compiler holds; with any other it is refused. The build is then compiled
-- | against the module the compiler holds, and the listed bytecode path is
-- | kept for running the program, never loaded into the compile-time session.
-- | Interfaces are compared whole, as decoded. Equal interfaces say nothing of
-- | the bytecode: artifacts are supported only when read by the compiler build
-- | that wrote them.
module Stellac.Dependencies
  ( Dependency
  , Loaded
  , DependencyError(..)
  , extend
  , dependedOn
  , printDependencyError
  ) where

import Prelude

import Data.Array as Array
import Data.Array.NonEmpty (NonEmptyArray)
import Data.Array.NonEmpty as NonEmptyArray
import Data.Either (Either(..), either)
import Data.Foldable (foldl)
import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), isJust, maybe)
import Data.Set (Set)
import Data.Set as Set
import Data.Show.Generic (genericShow)
import Data.String as String
import Data.Traversable (for)
import Data.Tuple (Tuple(..))
import Fmt (fmt)
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
import Stella.Compiler.TypedCore.Prim (primModule)
import Type.Row (type (+))

-- | A module `dependencies` lists, with its two paths.
type Dependency = { module :: ModuleName, interface :: FilePath, object :: FilePath }

-- | A listed module and the interface its file holds.
type Loaded = { dependency :: Dependency, interface :: ModuleInterface }

data DependencyError
  = ListedTwice ModuleName
  | InterfaceUnreadable Dependency String
  | InterfaceRejected Dependency DecodeError
  -- | A file holding the interface of another module than the one listed, the
  -- | second name.
  | InterfaceOfAnother Dependency ModuleName
  -- | `Prim`, which `dependencies` never lists.
  | ProvidedByCompiler ModuleName
  -- | A seed module, listed with another interface than the one of the seed
  -- | module the compiler holds.
  | DiffersFromCarried ModuleName
  -- | An import of a listed module, the second name, that is neither listed nor
  -- | in the environment `dependencies` extends.
  | ImportUnlisted ModuleName ModuleName
  -- | Listed modules importing one another, in order of their names.
  | ImportCycle (NonEmptyArray ModuleName)

derive instance Eq DependencyError
derive instance Generic DependencyError _

instance Show DependencyError where
  show = genericShow

-- | The environment given, the compiler's, with the interfaces added by
-- | `addInterface` in the order their imports give. A module listed more than
-- | once is refused. A listed module the environment holds is not added: it is
-- | accepted where it is no `Prim` and its interface is the one the environment
-- | holds. Of the others, a module is ready once the environment holds every
-- | module it imports, or holds the module itself, which `addInterface` then
-- | refuses; the modules ready together are added in order of their names.
-- | Where none is ready, an import of a module neither listed nor in the
-- | environment is reported, and so is each set of listed modules importing
-- | one another; a module that only imports one of those is not.
extend :: BuildEnvironment -> Array Loaded -> Either (NonEmptyArray DependencyError) BuildEnvironment
extend base loaded = go base (twice <> Array.mapMaybe carriedOne provided) listed
  where
  sorted = Array.sortWith _.interface.name loaded
  twice = map (\g -> ListedTwice (NonEmptyArray.head g).interface.name) (Array.filter (\g -> NonEmptyArray.length g > 1) (Array.groupBy (\a b -> a.interface.name == b.interface.name) sorted))
  { yes: provided, no: listed } = Array.partition (\l -> Map.member l.interface.name base.interfaces) sorted

  carriedOne l
    | l.interface.name == primModule = Just (ProvidedByCompiler primModule)
    | Map.lookup l.interface.name base.interfaces == Just l.interface = Nothing
    | otherwise = Just (DiffersFromCarried l.interface.name)

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
    ModuleTwice m -> ListedTwice m
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

-- | The environment given, extended with the interfaces of the modules given.
dependedOn
  :: forall r
   . Array Dependency
  -> BuildEnvironment
  -> Run (FS + r) (Either (NonEmptyArray DependencyError) BuildEnvironment)
dependedOn entries env = Except.runExcept do
  results <- for entries (Except.runExcept <<< load)
  case NonEmptyArray.fromArray (Array.mapMaybe (either Just (const Nothing)) results) of
    Just errors -> throw errors
    Nothing -> either throw pure (extend env (Array.mapMaybe (either (const Nothing) Just) results))
  where
  load :: forall r'. Dependency -> Run (EXCEPT DependencyError + FS + r') Loaded
  load d = do
    bytes <- FS.readBytes d.interface >>= either (throw <<< InterfaceUnreadable d) pure
    stored <- either (throw <<< InterfaceRejected d) pure (Interface.decode bytes)
    when (stored.interface.name /= d.module) (throw (InterfaceOfAnother d stored.interface.name))
    pure { dependency: d, interface: stored.interface }

printDependencyError :: DependencyError -> String
printDependencyError = case _ of
  ListedTwice m -> fmt @"`dependencies` lists `{m}` more than once" { m: text m }
  InterfaceUnreadable d why -> fmt @"The interface of `{m}`, `{path}`, could not be read: {why}" { m: text d.module, path: d.interface, why }
  InterfaceRejected d err -> fmt @"The interface of `{m}`, `{path}`, is not one this compiler reads: {why}" { m: text d.module, path: d.interface, why: show err }
  InterfaceOfAnother d other -> fmt @"`dependencies` gives `{path}` as the interface of `{m}`, but it is the interface of `{other}`" { path: d.interface, m: text d.module, other: text other }
  ProvidedByCompiler m -> fmt @"`dependencies` lists `{m}`, which the compiler provides" { m: text m }
  DiffersFromCarried m -> fmt @"`dependencies` lists `{m}` with an interface that differs from the one of the seed module the compiler holds" { m: text m }
  ImportUnlisted m missing -> fmt @"The interface of `{m}` imports `{missing}`, which `dependencies` does not list" { m: text m, missing: text missing }
  ImportCycle members -> fmt @"These modules of `dependencies` import one another: {names}" { names: String.joinWith ", " (map text (NonEmptyArray.toArray members)) }
  where
  text (ModuleName m) = m
