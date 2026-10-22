-- | The build driver: the modules of a package compiled to bytecode one at a
-- | time, each after the modules of the package it imports.
-- |
-- | The driver is neutral about effects. Reading a file, running a macro's
-- | parser, and taking what each phase makes (to show it or to write it) are
-- | the host's, handed in as a `CompilerAction` over a monad of its choosing.
-- | The driver asks only for `Monad`, and a build that cannot go on returns
-- | `Left`. Which files to build, and what becomes of the bytecode, are the
-- | host's too.
-- |
-- | Each file comes with the module it holds, and its header must name that
-- | module; nothing is read off a path.
-- |
-- | A build holds one module at a time. It reads every header first (name and
-- | imports, declarations left unread) and settles the compile order before
-- | compiling anything. Each module is then read again and compiled, and only
-- | the build environment carries over from one module to the next.
-- |
-- | Every stage of a module runs against one environment that does not hold
-- | the module; its interface is added once it is assembled, for the modules
-- | after it. A stage that could see the module's own interface would take
-- | what the module published for what it is compiling (an optimizer inlining
-- | the module's functions into themselves), so no module of the build may
-- | share a name with one the environment holds.
-- |
-- | The driver is made of parts: reading the headers, ordering them by their
-- | imports, and compiling one module and committing its interface. Each entry
-- | composes the parts it needs and decides which modules of the build may
-- | share a name with one the environment holds.
-- |
-- | An ordinary build (`build`) replaces and reorders nothing. The modules are
-- | compiled in the order given, and a module given before a module of the
-- | build it imports is refused before any is compiled.
-- |
-- | A seed build (`buildSeeds`) compiles modules of the environment anew from
-- | their sources; it is how the seed modules, loaded as the compiler
-- | bootstraps, are built. It orders the modules by their imports, the order
-- | given breaking ties, and reports modules importing one another before
-- | compiling any. Each is compiled against the environment without it, and
-- | its new interface replaces the old one. Where a module the build keeps
-- | imports the old one, the new interface must be the same. Which modules
-- | import it is read off the environment the build starts from, so a module
-- | rebuilt earlier hides nothing.
-- |
-- | Within a module, a phase's result lives only until the next phase reads
-- | it: it is handed to the host as the phase ends.
-- |
-- | A module's stages run in this order: the text is lexed, laid out, and
-- | parsed; the syntax is checked for what no later stage reads; the module is
-- | resolved and its macro calls expanded; its imports are looked up, and the
-- | signature and catalog they give are made, with the types the ABI manifest
-- | supplies to the module itself; it is elaborated and its Core checked; the
-- | interfaces translation reads are gathered; it is translated to Mid IR,
-- | optimized, and lowered to bytecode; and its interface is assembled. A
-- | stage that reports an error is the last to run, every error it reports is
-- | returned, and a module that does not compile is the last the build
-- | compiles.
module Stella.Compiler.Build
  ( Progress
  , CompilerAction
  , Header
  , readHeaders
  , BuiltModules
  , CompilerHooks
  , defaultHooks
  , withoutSynthesizers
  , build
  , buildSeeds
  , compileModule
  , module Stella.Compiler.Build.Report
  ) where

import Prelude

import Control.Monad.Error.Class (throwError)
import Control.Monad.Except.Trans (ExceptT(..), except, runExceptT)
import Control.Monad.Rec.Class (class MonadRec, Step(..), tailRecM)
import Control.Monad.Trans.Class (lift)
import Data.Bifunctor (lmap)
import Data.Array as Array
import Data.Array.NonEmpty (NonEmptyArray)
import Data.Array.NonEmpty as NonEmptyArray
import Data.Either (Either(..))
import Data.Foldable (foldl, for_)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), maybe)
import Data.Set (Set)
import Data.Set as Set
import Data.Tuple (Tuple(..))
import Stella.Compiler.Build.Report (BackendProblem(..), BuildError(..), BuildMessage, CompileError(..), CompileWarning, DiagnosticLocation, EnvironmentProblem(..), MessageLocation, SyntaxProblem(..), WrittenFile(..), WrittenLocation, WrittenSource(..), buildMessages, locationOf, locationsOf, originMessage, primaryLocationOf, printBuildMessage, printCompileError, printCompileWarning, warningLocationOf, warningMessage)
import Stella.Compiler.Bytecode.Lower (lower)
import Stella.Compiler.Bytecode.Module (Debug, Dmo) as Bytecode
import Stella.Compiler.CST (parseHeader, parseModule)
import Stella.Compiler.CST.Check (checkModule)
import Stella.Compiler.CST.Types (Import(..), Item(..), Module(..))
import Stella.Compiler.Elaborate.Environment.Imported (compilationSignature, importedCatalog)
import Stella.Compiler.Elaborate.Surface.Group (groups)
import Stella.Compiler.Elaborate.Environment.Surface (importedSurface)
import Stella.Compiler.Elaborate.Surface.Module (elaborateModuleM)
import Stella.Compiler.Elaborate.Driver.Attempt (attemptPending)
import Stella.Compiler.Elaborate.Driver.Loop (AttempterM)
import Stella.Compiler.Elaborate.Kernel.Elab (SessionEnv)
import Stella.Compiler.Interface (Imports, aritiesOf, importsOf)
import Stella.Compiler.Interface.Assemble (CoreInterface, SurfaceInterface, assemble, surfaceInterface)
import Stella.Compiler.Interface.Environment (BuildEnvironment, addInterface, lookupInterface, reachable, viewFor, withoutInterface)
import Stella.Compiler.Interface.Module (ModuleInterface)
import Stella.Compiler.Macro.Run (ExpansionSettings, RunParser)
import Stella.Compiler.MiddleEnd.IR (Debug, Module) as MIR
import Stella.Compiler.MiddleEnd.Translate (translate)
import Stella.Compiler.Resolve.Module (Resolved, resolveModuleExpanding)
import Stella.Compiler.Resolve.Scope (isElaborationOnlyValue)
import Stella.Compiler.Surface.Origin (Origin) as Surface
import Stella.Compiler.TypedCore (Declared, Module) as Core
import Stella.Compiler.TypedCore.Name (ModuleName(..))
import Stella.Compiler.TypedCore.Prim (primModule)

-- | How far a build has gone: the module now compiled, counting from 1, of how
-- | many.
type Progress = { current :: Int, total :: Int }

-- | What the host does for a build: read a file, run a macro's parser, carry
-- | out the jobs of a module's elaboration, and take what each phase makes as
-- | it ends. Parsers and attempters get the modules of the build compiled so
-- | far, since a macro or synthesizer of the build is declared by one of them.
-- | What an attempter stops with in `m` is the host's, not a diagnostic of the
-- | module.
type CompilerAction m =
  { readSource :: String -> m (Either String String)
  , runParser :: BuiltModules -> RunParser m
  , synthesis :: BuiltModules -> SessionEnv -> AttempterM m
  , hooks :: CompilerHooks m
  }

-- | The attempter of a build that provides no synthesizer: every job the
-- | host's, and a synthesis job a defect of the build, there being nothing to
-- | run it by.
withoutSynthesizers :: forall m. Applicative m => BuiltModules -> SessionEnv -> AttempterM m
withoutSynthesizers _ session id s = pure (attemptPending session id s)

-- | The modules of the build compiled so far, each by its interface.
type BuiltModules = Map ModuleName ModuleInterface

-- | What an entry lets its build replace: the environment each module is
-- | compiled against, made from the one the build has reached, and a check
-- | that may refuse the interface the module made.
type Replacing =
  { against :: ModuleName -> BuildEnvironment -> BuildEnvironment
  , refused :: Header -> ModuleInterface -> Maybe BuildError
  }

-- | An ordinary build replaces nothing and refuses no interface.
replacingNothing :: Replacing
replacingNothing = { against: \_ env -> env, refused: \_ _ -> Nothing }

-- | A seed build compiles each module given against the environment without
-- | it, and refuses a new interface that differs from the old one while a kept
-- | module of the starting environment reaches it.
replacingAnew :: BuildEnvironment -> Set ModuleName -> Replacing
replacingAnew before anew =
  { against: \name env -> if Set.member name anew then withoutInterface name env else env
  , refused: \header made -> do
      observers <- NonEmptyArray.fromArray =<< Map.lookup header.name observed
      old <- lookupInterface header.name before
      if old == made then Nothing else Just (RebuiltDiverges { path: header.path, name: header.name, observers })
  }
  where
  observed = Map.fromFoldable (map (\r -> Tuple r (Array.filter (reaches r) kept)) (Array.fromFoldable anew))
  kept = Array.filter (\m -> not (Set.member m anew)) (Array.fromFoldable (Map.keys before.interfaces))
  reaches r m = case lookupInterface m before of
    Just i | Right view <- viewFor i.imports before -> Set.member r (reachable view)
    _ -> false

-- | What the host is handed as a build goes. `onStartCompile` comes as a
-- | module's compiling begins, and each phase hook as its phase ends. The
-- | optimizer's three come before the first round, after each round that
-- | changed the module, and when it stops. `onLowered` brings the bytecode and
-- | interface once the module is in the build environment, and `onModuleDone`
-- | the warnings, after it.
type CompilerHooks m =
  { onStartCompile :: Progress -> { path :: String, name :: ModuleName } -> m Unit
  , onElaborated :: Core.Module Surface.Origin -> m Unit
  , onTranslated :: MIR.Module -> m Unit
  , onEnterOptimizeIter :: MIR.Module -> m Unit
  , onContinueOptimizeIter :: Int -> MIR.Module -> m Unit
  , onLeaveOptimizeIter :: MIR.Module -> m Unit
  , onLowered :: { dmo :: Bytecode.Dmo, interface :: ModuleInterface, debug :: Bytecode.Debug Surface.Origin } -> m Unit
  , onModuleDone :: { path :: String, name :: ModuleName, warnings :: Array CompileWarning, paths :: Map ModuleName String } -> m Unit
  }

defaultHooks :: forall m. Applicative m => CompilerHooks m
defaultHooks =
  { onStartCompile: \_ _ -> pure unit
  , onElaborated: \_ -> pure unit
  , onTranslated: \_ -> pure unit
  , onEnterOptimizeIter: \_ -> pure unit
  , onContinueOptimizeIter: \_ _ -> pure unit
  , onLeaveOptimizeIter: \_ -> pure unit
  , onLowered: \_ -> pure unit
  , onModuleDone: \_ -> pure unit
  }

-- | What a header gives a build: the module's file and name, and the modules
-- | it imports, in the order written and each with where it is written. `Prim`
-- | is left out, since importing it adds no dependency.
type Header =
  { path :: String
  , name :: ModuleName
  , imports :: Array { module :: ModuleName, at :: DiagnosticLocation }
  }

-- | An ordinary build of the files given, each with its module, against the
-- | environment given and in the order given. No module may share a name with
-- | one the environment holds, and each must come after the modules of the
-- | build it imports. Returns the modules built, in order.
build
  :: forall m
   . MonadRec m
  => CompilerAction m
  -> ExpansionSettings
  -> BuildEnvironment
  -> Array { path :: String, name :: ModuleName }
  -> m (Either BuildError (Array { path :: String, name :: ModuleName }))
build action settings env named = runExceptT do
  except (pathsOnce (map _.path named))
  except (namesOnce named)
  for_ (Array.find (\f -> Map.member f.name env.interfaces) named) (throwError <<< NameInEnvironment)
  let paths = Map.fromFoldable (map (\f -> Tuple f.name f.path) named)
  headers <- headersOf action.readSource paths named
  except (inOrder headers)
  compileAll action settings replacingNothing env paths headers

-- | A seed build of the files given, each with its module, every one a
-- | module of the environment other than `Prim`, compiled anew in an order
-- | their imports allow. Returns the modules built, in order.
buildSeeds
  :: forall m
   . MonadRec m
  => CompilerAction m
  -> ExpansionSettings
  -> BuildEnvironment
  -> Array { path :: String, name :: ModuleName }
  -> m (Either BuildError (Array { path :: String, name :: ModuleName }))
buildSeeds action settings env named = runExceptT do
  except (pathsOnce (map _.path named))
  except (namesOnce named)
  for_ (Array.find (\f -> f.name == primModule || not (Map.member f.name env.interfaces)) named) (throwError <<< NotRebuildable <<< _.name)
  let paths = Map.fromFoldable (map (\f -> Tuple f.name f.path) named)
  headers <- headersOf action.readSource paths named
  order <- except (ordered headers)
  compileAll action settings (replacingAnew env (Set.fromFoldable (map _.name named))) env paths order

-- | The header of each file given, read as a build reads them before it
-- | compiles anything: no file given twice, no module held by two files, and
-- | each header naming the module its file is given as. Nothing past a header
-- | is read, the headers keep the order given, and modules importing one
-- | another are not refused.
readHeaders
  :: forall m
   . MonadRec m
  => (String -> m (Either String String))
  -> Array { path :: String, name :: ModuleName }
  -> m (Either BuildError (Array Header))
readHeaders readSource named = runExceptT do
  except (pathsOnce (map _.path named))
  except (namesOnce named)
  headersOf readSource (Map.fromFoldable (map (\f -> Tuple f.name f.path) named)) named

-- | No file given twice.
pathsOnce :: Array String -> Either BuildError Unit
pathsOnce paths = for_ (foldl seen { paths: Set.empty, twice: Nothing } paths).twice (Left <<< ListedTwice)
  where
  seen acc path
    | Just _ <- acc.twice = acc
    | Set.member path acc.paths = acc { twice = Just path }
    | otherwise = acc { paths = Set.insert path acc.paths }

-- | No module held by two files.
namesOnce :: Array { path :: String, name :: ModuleName } -> Either BuildError Unit
namesOnce named = for_ (foldl once { names: Map.empty, twice: Nothing } named).twice (Left <<< NamedTwice)
  where
  once acc f
    | Just _ <- acc.twice = acc
    | Just first <- Map.lookup f.name acc.names = acc { twice = Just { name: f.name, paths: [ first, f.path ] } }
    | otherwise = acc { names = Map.insert f.name f.path acc.names }

-- | The header of each file, read one file at a time.
headersOf
  :: forall m
   . MonadRec m
  => (String -> m (Either String String))
  -> Map ModuleName String
  -> Array { path :: String, name :: ModuleName }
  -> ExceptT BuildError m (Array Header)
headersOf readSource paths named = tailRecM step { headers: [], i: 0 }
  where
  step { headers, i } = case Array.index named i of
    Nothing -> pure (Done headers)
    Just file -> do
      header <- headerOf readSource paths file
      pure (Loop { headers: Array.snoc headers header, i: i + 1 })

-- | A file's header, its declarations left unread; the header must name the
-- | module the file is given as.
headerOf
  :: forall m
   . Monad m
  => (String -> m (Either String String))
  -> Map ModuleName String
  -> { path :: String, name :: ModuleName }
  -> ExceptT BuildError m Header
headerOf readSource paths file = do
  text <- readSource file.path # orFailWithM (\detail -> Unreadable { path: file.path, detail })
  Module m <- parseHeader text # orFailWith (\err -> ModuleFailed { path: file.path, name: file.name, errors: pure (Syntax (Unparsed err)), paths })
  let written = ModuleName m.name.name
  when (written /= file.name) do
    throwError (NameMismatch { path: file.path, written, expected: file.name, at: locationOf m.name.range })
  pure { path: file.path, name: file.name, imports: Array.mapMaybe importOf m.items }
  where
  importOf = case _ of
    ItemImport (Import r) | ModuleName r.module.name /= primModule -> Just { module: ModuleName r.module.name, at: locationOf r.module.range }
    _ -> Nothing

-- | Each header comes after those of the build its module imports. The first
-- | import of a module given at or after the importing one is refused where it
-- | is written.
inOrder :: Array Header -> Either BuildError Unit
inOrder headers = for_ (Array.mapWithIndex Tuple headers) \(Tuple i h) ->
  for_ (Array.find (\imported -> maybe false (_ >= i) (Map.lookup imported.module indexOf)) h.imports) \imported ->
    Left (ImportedLater { path: h.path, name: h.name, imported: imported.module, at: imported.at })
  where
  indexOf = Map.fromFoldable (Array.mapWithIndex (\i h -> Tuple h.name i) headers)

-- | The headers in an order their imports allow, the one given first taken
-- | first among those ready; or the first modules found importing one
-- | another.
ordered :: Array Header -> Either BuildError (Array Header)
ordered headers = case Array.findMap cycleOf grouped of
  Just cycle -> Left (ImportCycle cycle)
  Nothing -> Right (Array.mapMaybe (\g -> Array.head g.members >>= Array.index headers) grouped)
  where
  indexOf = Map.fromFoldable (Array.mapWithIndex (\i h -> Tuple h.name i) headers)
  grouped = groups (map (\h -> Set.fromFoldable (Array.mapMaybe (\i -> Map.lookup i.module indexOf) h.imports)) headers)
  cycleOf g
    | g.recursive = NonEmptyArray.fromArray (Array.mapMaybe (\i -> map (\h -> { path: h.path, name: h.name }) (Array.index headers i)) g.members)
    | otherwise = Nothing

-- | Every module in the order given, one at a time, each against the
-- | environment holding the modules before it, as the entry's `Replacing`
-- | shapes it; its interface is committed unless `Replacing` refuses it.
compileAll
  :: forall m
   . MonadRec m
  => CompilerAction m
  -> ExpansionSettings
  -> Replacing
  -> BuildEnvironment
  -> Map ModuleName String
  -> Array Header
  -> ExceptT BuildError m (Array { path :: String, name :: ModuleName })
compileAll action settings replacing env0 paths order = tailRecM step { env: env0, built: Map.empty, done: [], i: 0 }
  where
  total = Array.length order
  step { env, built, done, i } = case Array.index order i of
    Nothing -> pure (Done done)
    Just header -> do
      let against = replacing.against header.name env
      made <- compileOne action settings against built paths { current: i + 1, total } header
      for_ (replacing.refused header made.interface) throwError
      committed <- commit action paths header against built made
      pure (Loop { env: committed.env, built: committed.built, done: Array.snoc done { path: header.path, name: header.name }, i: i + 1 })

-- | A module of the build read and compiled against the environment and the
-- | modules of the build given, neither of which it changes.
compileOne
  :: forall m
   . MonadRec m
  => CompilerAction m
  -> ExpansionSettings
  -> BuildEnvironment
  -> BuiltModules
  -> Map ModuleName String
  -> Progress
  -> Header
  -> ExceptT BuildError m Compiled
compileOne action settings env built paths progress header = do
  text <- action.readSource header.path # orFailWithM (\detail -> Unreadable { path: header.path, detail })
  lift (action.hooks.onStartCompile progress { path: header.path, name: header.name })
  compileModule action settings env built text # orFailWithM (\errors -> ModuleFailed { path: header.path, name: header.name, errors, paths })

-- | A module compiled to the end made available to the modules after it: its
-- | interface added to the environment and to the modules of the build. Only
-- | then are its bytecode and interface handed over, so that nothing the host
-- | is handed is in reach of what the module itself was compiled against.
commit
  :: forall m
   . Monad m
  => CompilerAction m
  -> Map ModuleName String
  -> Header
  -> BuildEnvironment
  -> BuiltModules
  -> Compiled
  -> ExceptT BuildError m { env :: BuildEnvironment, built :: BuiltModules }
commit action paths header env built made = do
  env' <- addInterface made.interface env
    # orFailWith (\e -> ModuleFailed { path: header.path, name: header.name, errors: pure (Environment (InterfaceNotAdded e)), paths })
  lift (action.hooks.onLowered { dmo: made.dmo, interface: made.interface, debug: made.debug })
  lift (action.hooks.onModuleDone { path: header.path, name: header.name, warnings: made.warnings, paths })
  pure { env: env', built: Map.insert header.name made.interface built }

-- | What compiling a module makes: its bytecode and interface, and the
-- | warnings compiling it gave.
type Compiled =
  { dmo :: Bytecode.Dmo
  , debug :: Bytecode.Debug Surface.Origin
  , interface :: ModuleInterface
  , warnings :: Array CompileWarning
  }

-- | Compile a module's source against the build environment, its macros'
-- | parsers run with the modules of the build compiled so far, and what each
-- | phase but the last makes handed over through the action given.
-- |
-- | Each phase is a function of what it reads alone, so nothing an earlier
-- | phase made outlives its last reader.
compileModule
  :: forall m
   . MonadRec m
  => CompilerAction m
  -> ExpansionSettings
  -> BuildEnvironment
  -> BuiltModules
  -> String
  -> m (Either (NonEmptyArray CompileError) Compiled)
compileModule action settings env built text = runExceptT do
  cst <- parseModule text # orFailWith (pure <<< Syntax <<< Unparsed)
  checkModule cst # failingWith (Syntax <<< IllFormed)
  resolved <- lift (resolveModuleExpanding (action.runParser built) settings env cst)
  elaborated action env built resolved

-- | What a phase of a module gives, or the errors it stops at.
type Phase m = ExceptT (NonEmptyArray CompileError) m

-- | What resolving and elaborating a module decide of its interface, carried to
-- | where lowering decides the rest.
type Decided = { surface :: SurfaceInterface, core :: CoreInterface }

-- | The checked Core, what translation reads of the modules it imports, and
-- | what is decided of the interface.
type Checked =
  { core :: Core.Module Surface.Origin
  , declared :: Core.Declared Surface.Origin
  , imports :: Imports
  , decided :: Decided
  }

-- | The module resolved, elaborated, and checked, handed on with the warnings
-- | alone of what resolving it gave.
elaborated
  :: forall m
   . MonadRec m
  => CompilerAction m
  -> BuildEnvironment
  -> BuiltModules
  -> Resolved
  -> Phase m Compiled
elaborated action env built resolved = checkedCore action env built resolved >>= checked action resolved.warnings

checkedCore
  :: forall m
   . MonadRec m
  => CompilerAction m
  -> BuildEnvironment
  -> BuiltModules
  -> Resolved
  -> Phase m Checked
checkedCore action env built resolved = do
  resolved.errors # failingWith Resolution
  let m = resolved.module
  -- a module resolved without error holds no invalid constant
  surface <- except (maybe (Left (pure (Backend SurfaceInterfaceMissing))) Right (surfaceInterface m resolved.exports))
  view <- viewFor (map _.module m.imports) env # orFailWith (pure <<< Environment <<< ViewRefused)
  signature <- compilationSignature env view m.name # orFailWith (pure <<< Environment <<< ImportsRefused)
  elaboratedModule <- lift (elaborateModuleM (action.synthesis built) signature (importedSurface env view) (importedCatalog env view) m resolved.exports)
  made <- elaboratedModule.result # orFailWith (map Elaboration)
  imports <- importsOf (Array.mapMaybe (\n -> lookupInterface n env) (Set.toUnfoldable (reachable view)))
    # orFailWith (pure <<< Environment <<< InterfacesRefused)
  pure { core: made.core, declared: made.declared, imports, decided: { surface, core: made.interface } }

-- | The checked Core handed to the host. What the module was resolved into is
-- | not in reach of what follows.
checked
  :: forall m
   . Monad m
  => CompilerAction m
  -> Array CompileWarning
  -> Checked
  -> Phase m Compiled
checked action warnings made = do
  lift (action.hooks.onElaborated made.core)
  translated action warnings made

-- | The checked Core translated to Mid IR.
translated
  :: forall m
   . Monad m
  => CompilerAction m
  -> Array CompileWarning
  -> Checked
  -> Phase m Compiled
translated action warnings made = do
  mid <- translate made.imports made.core made.declared # orFailWith (pure <<< Backend <<< TranslateFailed)
  lift (action.hooks.onTranslated mid.module)
  optimized action warnings made.decided mid

-- | The Mid IR optimized. No pass rewrites a module yet, so the optimizer stops
-- | before a first round.
optimized
  :: forall m
   . Monad m
  => CompilerAction m
  -> Array CompileWarning
  -> Decided
  -> { module :: MIR.Module, debug :: MIR.Debug Surface.Origin }
  -> Phase m Compiled
optimized action warnings decided mid = do
  lift (action.hooks.onEnterOptimizeIter mid.module)
  lift (action.hooks.onLeaveOptimizeIter mid.module)
  lowered warnings decided mid

-- | The Mid IR lowered to bytecode, and the interface assembled with the
-- | arities of what was lowered.
lowered
  :: forall m
   . Monad m
  => Array CompileWarning
  -> Decided
  -> { module :: MIR.Module, debug :: MIR.Debug Surface.Origin }
  -> Phase m Compiled
lowered warnings decided mid = do
  bytecode <- lower mid # orFailWith (pure <<< Backend <<< LowerFailed)
  interface <- assemble decided.surface decided.core arities # orFailWith (pure <<< Backend <<< InterfaceUnassembled)
  pure { dmo: bytecode.dmo, debug: bytecode.debug, interface, warnings }
  where
  -- an elaboration-only value is exported apart from the interface, which
  -- gives it no arity: a call to it from downstream is of an arity unknown
  arities = Map.filterKeys (not <<< isElaborationOnlyValue mid.module.name) (aritiesOf mid.module)

-- | What may fail, or what it failed with taken for the error given.
orFailWith :: forall m e e' a. Applicative m => (e -> e') -> Either e a -> ExceptT e' m a
orFailWith wrap = except <<< lmap wrap

-- | `orFailWith`, for what the host does.
orFailWithM :: forall m e e' a. Functor m => (e -> e') -> m (Either e a) -> ExceptT e' m a
orFailWithM wrap = ExceptT <<< map (lmap wrap)

-- | Stop at the errors a stage reports, where it reports any.
failingWith :: forall m e. Monad m => (e -> CompileError) -> Array e -> Phase m Unit
failingWith wrap errors = case NonEmptyArray.fromArray errors of
  Just es -> except (Left (map wrap es))
  Nothing -> pure unit
