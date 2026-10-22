-- | The modules of a bytecode fixture built from source.
-- |
-- | **A fixture's source is its directory of `fixtures/source`**, with the
-- | directories of `fixtures/source/common-lib` it names beside it, and the
-- | modules of the packages in `stella-packages` — `base`, `lists`, `maybe` —
-- | that those reach by their imports. They are built as a package is, against
-- | the seed modules, each after the modules it imports; `Base.Int`, a seed
-- | module, is compiled from its source on its own once, for every fixture, and
-- | stands first among the modules built where they reach it. The modules built
-- | are those, in the order they are built, and nothing else of the packages.
-- |
-- | **A fixture holds what its program needs to run**, and no more: of the
-- | modules built, those its runtime roots reach through the imports of their
-- | bytecode (D51), in the order built. A module a header imports is built, and
-- | held only where what the values became names something it declares.
module E2E.Build
  ( Sources
  , readSources
  , builtFrom
  , collectedFrom
  , packageModules
  , Prebuilt
  , OnSession
  , OnSessionBuilt
  , builtOnSession
  ) where

import Prelude

import Type.Row (type (+))

import Control.Monad.State (State, modify_, runState)
import Data.Array as Array
import Data.Array.NonEmpty as NonEmptyArray
import Data.Either (Either(..), note)
import Data.Bifunctor (lmap)
import Data.Foldable (foldM, for_)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Set as Set
import Data.String as String
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw)
import Effect.Ref as Ref
import Node.Buffer as Buffer
import Node.FS.Aff as FS
import Node.FS.Perms as Perms
import Run (AFF, EFFECT, Run, liftAff, runBaseAff')
import Run.Except (EXCEPT)
import Run.Except as Except
import Stella.CLI.Effect.Process (PROCESS)
import Stella.CLI.Effect.Process as Process
import Stella.CLI.Runner.Node (nodeProcessHandler)
import Stella.CLI.Session.Client (Session)
import Stella.CLI.Session.Client as Client
import Stella.CLI.Session.CompileTime (CompileTimeError(..))
import Stella.CLI.Session.RunParser (loadingParser)
import Stella.Compiler.Build (CompilerAction, build, buildMessages, compileModule, defaultHooks, printBuildMessage, printCompileError, withoutSynthesizers)
import Stella.Compiler.Bytecode (Dmo, encode)
import Stella.Compiler.CST (parseHeader)
import Stella.Compiler.CST.Types (Import(..), Item(..), Module(..))
import Stella.Compiler.Interface.Environment (BuildEnvironment, addInterface, initialEnvironment)
import Stella.Compiler.Interface.Module (ModuleInterface)
import Stella.Compiler.Macro.Compiled (compiled)
import Stella.Compiler.Macro.Run (ExecutionReason(..), ParseOutcome(..), defaultSettings)
import Stella.Compiler.TypedCore (ModuleName(..))

foreign import readStelUnder :: Array String -> Effect (Array { path :: String, text :: String })

-- | The sources a fixture may be built from, by their paths from the
-- | repository's root, and what every build of one shares: the environment of
-- | the seed modules, and `Base.Int` compiled from its source.
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

-- | A source file as a build is given it: its path, and the module its place
-- | under its directory names.
type Placed = { path :: String, name :: ModuleName }

-- | Each file under the directory given, named by its path below it.
placedUnder :: Map String String -> String -> Array Placed
placedUnder files dir = Array.mapMaybe place (Array.fromFoldable (Map.keys files))
  where
  prefix = dir <> "/"
  place path = do
    rest <- String.stripPrefix (String.Pattern prefix) path
    stem <- String.stripSuffix (String.Pattern ".stel") rest
    pure { path, name: ModuleName (String.replaceAll (String.Pattern "/") (String.Replacement ".") stem) }

-- | The fixture's modules built from the directories of `fixtures/source`
-- | given, the first its own, or why they could not be.
builtFrom :: Sources -> Array String -> Either String (Array Dmo)
builtFrom sources dirs = do
  let
    own = Array.concatMap (\d -> placedUnder sources.files ("fixtures/source/" <> d)) dirs
    library = Map.fromFoldable (map (\p -> Tuple p.name p) (Array.concatMap (\p -> placedUnder sources.files ("stella-packages/" <> p <> "/src")) packages))
  reached <- reach sources.files library own
  placed <- inBuildOrder sources.files (own <> Array.mapMaybe (\m -> Map.lookup m library) (Array.fromFoldable (Set.delete baseIntName reached)))
  let Tuple result dmos = runState (build (action sources.files placed) defaultSettings sources.environment placed) []
  case result of
    Left err -> Left (String.joinWith "; " (map printBuildMessage (NonEmptyArray.toArray (buildMessages err))))
    Right _ -> pure (if Set.member baseIntName reached then Array.cons sources.baseInt dmos else dmos)

-- | Of the modules given, those the roots named reach through the imports of
-- | their bytecode, themselves among them, in the order given; or why not: a
-- | root, or a module one of them imports, that is not among them.
collectedFrom :: Array ModuleName -> Array Dmo -> Either String (Array Dmo)
collectedFrom roots dmos = do
  reached <- go Set.empty roots
  pure (Array.filter (\d -> Set.member d.name reached) dmos)
  where
  byName = Map.fromFoldable (map (\d -> Tuple d.name d) dmos)
  go seen pending = case Array.uncons pending of
    Nothing -> Right seen
    Just { head, tail }
      | Set.member head seen -> go seen tail
      | otherwise -> case Map.lookup head byName of
          Nothing -> Left (nameText head <> " is not among the modules built")
          Just d -> go (Set.insert head seen) (d.imports <> tail)

-- Built on a session ----------------------------------------------------------------------

-- | A module built before, outside the build at hand: its interface stands in the
-- | build's environment, and its bytecode is loaded into the session before the
-- | build runs.
type Prebuilt = { dmo :: Dmo, interface :: ModuleInterface }

-- | The session a build runs its parsers on, the directory it writes each module's
-- | bytecode to as the module is lowered, the modules whose bytecode it does not
-- | write, and the modules built before it.
type OnSession =
  { session :: Session
  , dir :: String
  , unwritten :: Array String
  , prebuilt :: Array Prebuilt
  }

-- | What a build on a session gave: the modules it built, by name in the order
-- | built, or why it did not — its messages, or what stopped a parser running —
-- | and every module it lowered, with its interface.
type OnSessionBuilt = { outcome :: Either String (Array String), lowered :: Array Prebuilt }

-- | The modules the directories of `fixtures/source` given build, as `builtFrom`
-- | builds them, each macro a module calls run on the session given from the
-- | bytecode the build wrote for the module declaring it. `Base.Int` is neither
-- | built nor loaded: the session holds it. A module built before is not built
-- | again, though the sources reach it.
builtOnSession :: Sources -> OnSession -> Array String -> Aff OnSessionBuilt
builtOnSession sources on dirs = case prepared of
  Left err -> pure { outcome: Left err, lowered: [] }
  Right { syntax, env } -> case reach sources.files library own >>= placedOf of
    Left err -> pure { outcome: Left err, lowered: [] }
    Right placed -> do
      FS.mkdir' on.dir { recursive: true, mode: Perms.mkPerms Perms.all Perms.all Perms.all }
      for_ on.prebuilt \p -> write p.dmo
      loaded <- liftEffect (Ref.new Set.empty)
      preloaded <- runOnNode (Except.runExcept (for_ on.prebuilt \p -> preload loaded p.dmo.name))
      case preloaded of
        Left failure -> pure { outcome: Left (failureText failure), lowered: [] }
        Right _ -> do
          lowered <- liftEffect (Ref.new [])
          written <- liftEffect (Ref.new Set.empty)
          let
            loading =
              { seed: syntax.preloaded
              , importsOf: const Nothing
              , loaded
              , locate: \name -> liftEffect (Ref.read written) <#> \names ->
                  if Set.member name names then Just (pathOf name) else Nothing
              }

            onSession :: CompilerAction (Run (EXCEPT CompileTimeError + PROCESS + AFF + EFFECT + ()))
            onSession =
              { readSource: \path -> pure (note ("no source " <> path) (if Array.any (\f -> f.path == path) placed then Map.lookup path sources.files else Nothing))
              , runParser: loadingParser loading on.session syntax.descriptor
              , synthesis: withoutSynthesizers
              , hooks: defaultHooks
                  { onLowered = \made -> do
                      liftEffect (Ref.modify_ (_ `Array.snoc` { dmo: made.dmo, interface: made.interface }) lowered)
                      unless (Array.elem (nameText made.dmo.name) on.unwritten) do
                        liftAff (write made.dmo)
                        liftEffect (Ref.modify_ (Set.insert made.dmo.name) written)
                  }
              }
          outcome <- runOnNode (Except.runExcept (build onSession defaultSettings env placed))
          made <- liftEffect (Ref.read lowered)
          pure
            { outcome: case outcome of
                Left failure -> Left (failureText failure)
                Right (Left err) -> Left (String.joinWith "\n" (map printBuildMessage (NonEmptyArray.toArray (buildMessages err))))
                Right (Right names) -> Right (map (\b -> nameText b.name) names)
            , lowered: made
            }
  where
  prepared = do
    syntax <- compiled
    env <- lmap show (foldM (flip addInterface) sources.environment (map _.interface on.prebuilt))
    pure { syntax, env }
  own = Array.concatMap (\d -> placedUnder sources.files ("fixtures/source/" <> d)) dirs
  library = Map.fromFoldable (map (\p -> Tuple p.name p) (Array.concatMap (\p -> placedUnder sources.files ("stella-packages/" <> p <> "/src")) packages))
  prebuiltNames = Set.fromFoldable (map _.dmo.name on.prebuilt)
  placedOf reached = inBuildOrder sources.files (own <> Array.mapMaybe (\m -> Map.lookup m library) (Array.fromFoldable (Set.difference reached (Set.insert baseIntName prebuiltNames))))

  pathOf name = on.dir <> "/" <> nameText name <> ".dmo"

  write dmo = case encode dmo of
    Left err -> liftEffect (throw ("could not encode " <> nameText dmo.name <> ": " <> show err))
    Right bytes -> do
      buffer <- liftEffect (Buffer.fromArray bytes)
      FS.writeFile (pathOf dmo.name) buffer

  preload loaded name = Client.load on.session (pathOf name) >>= case _ of
    Right (Right _) -> liftEffect (Ref.modify_ (Set.insert name) loaded)
    _ -> Except.throw (ModuleUnavailable name)

  failureText = case _ of
    ModuleUnavailable m -> "unavailable " <> nameText m
    failure -> show failure

-- | A computation of the client's run in this process, with Node's processes.
runOnNode :: forall a. Run (PROCESS + AFF + EFFECT + ()) a -> Aff a
runOnNode = runBaseAff' <<< Process.interpret nodeProcessHandler

nameText :: ModuleName -> String
nameText (ModuleName m) = m

-- | The modules of the package of `stella-packages` named.
packageModules :: Sources -> String -> Array ModuleName
packageModules sources p = map _.name (placedUnder sources.files ("stella-packages/" <> p <> "/src"))

-- | The library modules the fixture's own reach by their imports, transitively.
reach :: Map String String -> Map ModuleName Placed -> Array Placed -> Either String (Set ModuleName)
reach files library own = go Set.empty (Array.concat <$> traverse (importsOf files) own)
  where
  go seen pending = pending >>= \ms -> case Array.uncons (Array.filter (\m -> not (Set.member m seen) && Map.member m library) ms) of
    Nothing -> Right seen
    Just { head, tail } -> case Map.lookup head library of
      Just f -> go (Set.insert head seen) (map (tail <> _) (importsOf files f))
      Nothing -> go seen (Right tail)

-- | The files given in an order their imports allow, the one given first taken
-- | first among those ready; or why not: files importing one another.
inBuildOrder :: Map String String -> Array Placed -> Either String (Array Placed)
inBuildOrder files placed = traverse (\f -> { file: f, imports: _ } <$> importsOf files f) placed >>= go []
  where
  go done remaining = case Array.find (ready remaining) remaining of
    Just r -> go (Array.snoc done r.file) (Array.filter (\other -> other.file.path /= r.file.path) remaining)
    Nothing
      | Array.null remaining -> Right done
      | otherwise -> Left (String.joinWith ", " (map (nameText <<< _.file.name) remaining) <> " import one another")

  ready remaining r = not (Array.any (\other -> Array.elem other.file.name r.imports) remaining)

-- | The modules the header of the file given imports.
importsOf :: Map String String -> Placed -> Either String (Array ModuleName)
importsOf files f = case Map.lookup f.path files of
  Nothing -> Left ("no source " <> f.path)
  Just text -> case parseHeader text of
    Left _ -> Left (f.path <> " has no header")
    Right (Module m) -> Right (Array.mapMaybe importOf m.items)
  where
  importOf = case _ of
    ItemImport (Import r) -> Just (ModuleName r.module.name)
    _ -> Nothing

