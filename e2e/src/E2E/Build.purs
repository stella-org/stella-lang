-- | The modules of a bytecode fixture built from source.
-- |
-- | **A fixture's source is its directory of `fixtures/source`**, with the
-- | directories of `fixtures/source/common-lib` it names beside it, and the
-- | modules of the packages in `stella-packages` — `base`, `lists`, `maybe` —
-- | that those reach by their imports. They are built as a package is, against
-- | the modules the compiler carries; `Base.Int`, which the compiler carries, is
-- | compiled from its source on its own once, for every fixture, and stands first
-- | among a fixture's modules where they reach it. The modules of a fixture are
-- | those, in the order they are built, and nothing else of the packages.
module E2E.Build
  ( Sources
  , readSources
  , builtFrom
  , packageModules
  ) where

import Prelude

import Control.Monad.State (State, modify_, runState)
import Data.Array as Array
import Data.Array.NonEmpty as NonEmptyArray
import Data.Either (Either(..), note)
import Data.Bifunctor (lmap)
import Data.Foldable (foldM)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Set as Set
import Data.String as String
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Stella.Compiler.Build (CompilerAction, PackageFile, build, buildMessages, compileModule, defaultHooks, ordinary, printBuildMessage, printCompileError, withoutSynthesizers)
import Stella.Compiler.Bytecode (Dmo)
import Stella.Compiler.CST (parseHeader)
import Stella.Compiler.CST.Types (Import(..), Item(..), Module(..))
import Stella.Compiler.Interface.Environment (BuildEnvironment, addInterface, initialEnvironment)
import Stella.Compiler.Macro.Compiled (compiled)
import Stella.Compiler.Macro.Run (ExecutionReason(..), ParseOutcome(..), defaultSettings)
import Stella.Compiler.TypedCore (ModuleName(..))

foreign import readStelUnder :: Array String -> Effect (Array { path :: String, text :: String })

-- | The sources a fixture may be built from, by their paths from the
-- | repository's root, and what every build of one shares: the environment of
-- | the modules the compiler carries, and `Base.Int` compiled from its source.
type Sources =
  { files :: Map String String
  , environment :: BuildEnvironment
  , baseInt :: Dmo
  }

-- | The directories the sources are read from.
sourceDirectories :: Array String
sourceDirectories = [ "fixtures/source" ] <> map (\p -> "stella-packages/" <> p <> "/src") packages

-- | The packages a fixture may reach.
packages :: Array String
packages = [ "base", "lists", "maybe" ]

-- | The sources read, with what the builds share made once, or why that could
-- | not be made.
readSources :: Effect (Either String Sources)
readSources = readStelUnder sourceDirectories <#> \found -> do
  let files = Map.fromFoldable (map (\f -> Tuple f.path f.text) found)
  carried <- compiled
  environment <- lmap show (foldM (flip addInterface) initialEnvironment carried.moduleInterfaces)
  baseInt <- baseIntDmo files
  pure { files, environment, baseInt }

baseIntName :: ModuleName
baseIntName = ModuleName "Base.Int"

-- | `Base.Int` compiled from its source against `Prim` alone.
baseIntDmo :: Map String String -> Either String Dmo
baseIntDmo files = do
  text <- note "no source of Base.Int" (Map.lookup "stella-packages/base/src/Base/Int.stel" files)
  case runState (compileModule (action files []) defaultSettings initialEnvironment Map.empty text) [] of
    Tuple (Left errors) _ -> Left (String.joinWith "; " (map printCompileError (NonEmptyArray.toArray errors)))
    Tuple (Right made) _ -> Right made.dmo

-- | A build reading the files placed, and collecting the `.dmo` of each module
-- | it lowers.
action :: Map String String -> Array Placed -> CompilerAction (State (Array Dmo))
action files placed =
  { readSource: \path -> pure (note ("no source " <> path) (if Array.any (\f -> f.path == path) placed then Map.lookup path files else Nothing))
  , runParser: \_ _ _ -> pure (ExecutionFailedAs { reason: NoSuchModule, detail: "no parser runs" })
  , synthesis: withoutSynthesizers
  , hooks: defaultHooks { onLowered = \made -> modify_ (_ `Array.snoc` made.dmo) }
  }

-- | A source file as a build is given it: its path, and where it stands under
-- | the one source directory of the build, so that its place names its module.
type Placed = { path :: String, within :: Array String, name :: ModuleName }

-- | Each file under the directory given, placed by its path below it.
placedUnder :: Map String String -> String -> Array Placed
placedUnder files dir = Array.mapMaybe place (Array.fromFoldable (Map.keys files))
  where
  prefix = dir <> "/"
  place path = do
    rest <- String.stripPrefix (String.Pattern prefix) path
    let segments = String.split (String.Pattern "/") rest
    stem <- String.stripSuffix (String.Pattern ".stel") rest
    pure { path, within: [ "src" ] <> segments, name: ModuleName (String.replaceAll (String.Pattern "/") (String.Replacement ".") stem) }

-- | The fixture's modules built from the directories of `fixtures/source`
-- | given, the first its own, or why they could not be.
builtFrom :: Sources -> Array String -> Either String (Array Dmo)
builtFrom sources dirs = do
  let
    own = Array.concatMap (\d -> placedUnder sources.files ("fixtures/source/" <> d)) dirs
    library = Map.fromFoldable (map (\p -> Tuple p.name p) (Array.concatMap (\p -> placedUnder sources.files ("stella-packages/" <> p <> "/src")) packages))
  reached <- reach sources.files library own
  let
    placed = own <> Array.mapMaybe (\m -> Map.lookup m library) (Array.fromFoldable (Set.delete baseIntName reached))
    Tuple result dmos = runState (build (action sources.files placed) defaultSettings (ordinary sources.environment) [ { prefix: [], dir: [ "src" ] } ] (map (\f -> { path: f.path, within: f.within } :: PackageFile) placed)) []
  case result of
    Left err -> Left (String.joinWith "; " (map printBuildMessage (NonEmptyArray.toArray (buildMessages err))))
    Right _ -> pure (if Set.member baseIntName reached then Array.cons sources.baseInt dmos else dmos)

-- | The modules of the package of `stella-packages` named.
packageModules :: Sources -> String -> Array ModuleName
packageModules sources p = map _.name (placedUnder sources.files ("stella-packages/" <> p <> "/src"))

-- | The library modules the fixture's own reach by their imports, transitively.
reach :: Map String String -> Map ModuleName Placed -> Array Placed -> Either String (Set ModuleName)
reach files library own = go Set.empty (Array.concat <$> traverse importsOfFile own)
  where
  go seen pending = pending >>= \ms -> case Array.uncons (Array.filter (\m -> not (Set.member m seen) && Map.member m library) ms) of
    Nothing -> Right seen
    Just { head, tail } -> case Map.lookup head library of
      Just f -> go (Set.insert head seen) (map (tail <> _) (importsOfFile f))
      Nothing -> go seen (Right tail)

  importsOfFile f = case Map.lookup f.path files of
    Nothing -> Left ("no source " <> f.path)
    Just text -> case parseHeader text of
      Left _ -> Left (f.path <> " has no header")
      Right (Module m) -> Right (Array.mapMaybe importOf m.items)

  importOf = case _ of
    ItemImport (Import r) -> Just (ModuleName r.module.name)
    _ -> Nothing

