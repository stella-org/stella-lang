-- | The build driver: the modules of a package compiled to bytecode, one at a
-- | time, in dependency order.
-- |
-- | **The driver is neutral about effects.** Reading a file, running a macro's
-- | parser, and taking what each phase makes — to show it or to write it — are
-- | the host's, handed in as a `CompilerAction` over a monad of its choosing; the
-- | driver asks for `Monad` alone, and a build that cannot go on is a returned
-- | `Left`. Which files to build, and what is done with the bytecode once
-- | written — code for a target — are the host's too.
-- |
-- | **A file's path names its module.** `src/A/B/C.stel` holds `A.B.C`, and
-- | `test/A/B/C.stel` holds `Test.A.B.C`; a module of `src` is never named under
-- | `Test`. The path is relative to the package's root.
-- |
-- | **A build holds one module at a time.** It reads every header first — the
-- | name and the imports, the declarations left unread — and orders the
-- | modules by their imports, the order they were given in deciding between
-- | modules neither of which imports the other; modules importing one another
-- | are reported before anything is compiled. Then each module is read again
-- | and compiled, and what a build keeps from one module to the next is the
-- | build environment alone, so that a module of the build is compiled against
-- | the modules of the build it imports.
-- |
-- | **Every stage of a module runs against one environment, which does not
-- | hold the module.** Its interface is added once the module is lowered
-- | and its interface assembled, for the modules after it alone; what a stage
-- | knows of the module itself comes from the module, never from the
-- | environment. An environment holding the module would let a stage take
-- | what the module published for what it is compiling — an optimizer inlining
-- | the module's own functions into themselves — so no module of the build may
-- | be named as one the environment holds already.
-- |
-- | **The driver is parts, and each entry composes the ones it needs**:
-- | reading the headers, ordering them by their imports, and compiling one
-- | module and committing its interface. An entry decides which modules of the
-- | build may share a name with one the environment holds; no part does.
-- |
-- | **An ordinary build (`build`) replaces nothing**: no module of the build is
-- | named as one the environment holds.
-- |
-- | **A seed build (`buildSeeds`) compiles modules of the environment anew
-- | from their sources**, every module it is given one of them; it is how the
-- | seed modules, which are loaded as the compiler bootstraps, are built. Each
-- | is compiled against the environment without it, and its new interface
-- | takes the old one's place. Until then the old one stays, for the modules
-- | the environment holds that import it; where any of them is kept, the new
-- | interface must be the old one, which is what they were compiled against.
-- | Which modules import it is read off the environment the build starts
-- | from, so that a module rebuilt earlier hides nothing.
-- |
-- | **Within a module, a phase's result is held no longer than the next phase
-- | reads it**: it is handed to the host as the phase ends, and what the next
-- | phase is given is what it reads, with what each stage decides of the
-- | module's interface.
-- |
-- | **A module's stages run in this order**: the text is lexed, laid out, and
-- | parsed; the syntax is checked for what no later stage reads; the module is
-- | resolved, its macro calls expanded; its imports are looked up in the build
-- | environment, and the signature and the catalog they give are made, with the
-- | types the ABI manifest supplies to the module itself; it is elaborated and
-- | its Core checked; the interfaces translation reads are gathered; it is
-- | translated to Mid IR, optimized, and lowered to bytecode; and its interface
-- | is assembled. **A stage that
-- | reports an error is the last that runs**, and every error it reports is
-- | returned; a module that does not compile is the last the build compiles.
module Stella.Compiler.Build
  ( PackageFile
  , defaultSourceRoots
  , Progress
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
import Data.String (Pattern(..), joinWith, stripSuffix)
import Data.String.CodeUnits as SCU
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Stella.Compiler.Build.Report (BackendProblem(..), BuildError(..), BuildMessage, SourceRoot, CompileError(..), CompileWarning, DiagnosticLocation, EnvironmentProblem(..), MessageLocation, SyntaxProblem(..), WrittenFile(..), WrittenLocation, WrittenSource(..), buildMessages, locationOf, locationsOf, originMessage, primaryLocationOf, printBuildMessage, printCompileError, printCompileWarning, warningLocationOf, warningMessage)
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

-- | A file of the package: the path the host reads it by, and its path from
-- | the package's root, one segment each.
type PackageFile = { path :: String, within :: Array String }

-- | The source directories of a package where it names none of its own: `src`,
-- | holding modules under no prefix, and `test`, holding those under `Test`.
defaultSourceRoots :: Array SourceRoot
defaultSourceRoots = [ { prefix: [], dir: [ "src" ] }, { prefix: [ "Test" ], dir: [ "test" ] } ]

-- | How far a build has gone: the module now compiled, counting from 1, of how
-- | many.
type Progress = { current :: Int, total :: Int }

-- | What the host does for a build: read a file, run a macro's parser, carry
-- | out the jobs of a module's elaboration, and take what each phase of a
-- | module makes as the phase ends — to show it, or to write it. A parser is run
-- | with the modules of the build compiled so far in hand, which a macro of the
-- | build is declared by. A job is carried out by the attempter made of those
-- | modules and the module's session, which runs a synthesis job by the
-- | synthesizers the host provides, one of the build among them; what that
-- | attempter stops with in `m` is the host's, and no diagnostic of the module.
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

-- | What an entry lets its build replace, as the build compiles each module:
-- | the environment the module is compiled against, made of the one the build
-- | has reached, and what refuses the interface it made.
type Replacing =
  { against :: ModuleName -> BuildEnvironment -> BuildEnvironment
  , refused :: Header -> ModuleInterface -> Maybe BuildError
  }

-- | An ordinary build's: nothing replaced, and no interface refused.
replacingNothing :: Replacing
replacingNothing = { against: \_ env -> env, refused: \_ _ -> Nothing }

-- | A seed build's, the environment it starts from and the modules it
-- | compiles anew given: each compiled against the environment without it, and
-- | its interface refused where it is not the old one while a module of that
-- | environment the build keeps reaches it.
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
-- | module's compiling begins; each phase hook as the phase ends, with what it
-- | made, which the build keeps no longer than the next phase needs it; the
-- | optimizer's three as its rounds go — once before the first, once after
-- | each round that changed the module, and once when it stops. `onLowered`
-- | comes with the module's bytecode and interface once the module is added to
-- | the build environment, and `onModuleDone`, with the warnings compiling the
-- | module gave, after it.
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

-- | What a header gives a build: the module's file and name, and the modules it
-- | imports, which are its dependencies, in the order written, each with where
-- | it is written; `Prim`, which an import adds no dependency on, is not among
-- | them.
type Header =
  { path :: String
  , name :: ModuleName
  , imports :: Array { module :: ModuleName, at :: DiagnosticLocation }
  }

-- | An ordinary build: the files given built against the environment given,
-- | in an order their imports allow, no module of them named as one the
-- | environment holds. The modules built, in the order built.
build
  :: forall m
   . MonadRec m
  => CompilerAction m
  -> ExpansionSettings
  -> BuildEnvironment
  -> Array SourceRoot
  -> Array PackageFile
  -> m (Either BuildError (Array { path :: String, name :: ModuleName }))
build action settings env roots files = runExceptT do
  except (rootsApart roots)
  named <- except (placed roots files)
  for_ (Array.find (\f -> Map.member f.name env.interfaces) named) (throwError <<< NameInEnvironment)
  let paths = Map.fromFoldable (map (\f -> Tuple f.name f.path) named)
  headers <- headersOf action.readSource paths named
  order <- except (ordered headers)
  compileAll action settings replacingNothing env paths order

-- | A seed build: the files given, each with the module it holds, every
-- | one a module of the environment given, `Prim` aside, compiled anew from
-- | its source, in an order their imports allow. The modules built, in the
-- | order built.
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

-- | The header of each file given, read as a build reads them before it orders
-- | anything: the source directories naming their modules apart, each file
-- | given its module's name off its path, and each header naming that module.
-- | Nothing past a header is read and nothing is compiled; the headers are in
-- | the order the files were given, and modules importing one another are not
-- | refused.
readHeaders
  :: forall m
   . MonadRec m
  => (String -> m (Either String String))
  -> Array SourceRoot
  -> Array PackageFile
  -> m (Either BuildError (Array Header))
readHeaders readSource roots files = runExceptT do
  except (rootsApart roots)
  named <- except (placed roots files)
  headersOf readSource (Map.fromFoldable (map (\f -> Tuple f.name f.path) named)) named

-- | Every file given its module's name, read off its path; no file given twice,
-- | and no module named twice.
placed :: Array SourceRoot -> Array PackageFile -> Either BuildError (Array { path :: String, name :: ModuleName })
placed roots files = do
  pathsOnce (map _.path files)
  named <- traverse (\f -> { path: f.path, name: _ } <$> moduleNameOf roots f) files
  namesOnce named
  pure named

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

-- | Source directories that name their modules apart: each prefix made of
-- | segments a module's name may hold, no two under one prefix, and none
-- | standing in another.
rootsApart :: Array SourceRoot -> Either BuildError Unit
rootsApart roots = do
  for_ roots \root ->
    when (Array.null root.dir || not (Array.all isProperName root.prefix)) do
      Left (SourceRootInvalid root)
  for_ (Array.mapWithIndex Tuple roots) \(Tuple i first) ->
    for_ (Array.drop (i + 1) roots) \second ->
      when (first.prefix == second.prefix || isPrefixOf first.dir second.dir || isPrefixOf second.dir first.dir) do
        Left (SourceRootsConflict { first, second })

-- | The module a file holds: the prefix of the source directory it stands in,
-- | then its path from there. The directory whose prefix the name falls under
-- | — the longest one it does — is the one it must stand in.
moduleNameOf :: Array SourceRoot -> PackageFile -> Either BuildError ModuleName
moduleNameOf roots f = case Array.find (\r -> isPrefixOf r.dir f.within) roots of
  Nothing -> Left (OutsidePackage f.path)
  Just root -> case Array.unsnoc (Array.drop (Array.length root.dir) f.within) of
    Just { init, last } | Just stem <- stripSuffix (Pattern ".stel") last ->
      let
        parts = Array.snoc init stem
        segments = root.prefix <> parts
        name = ModuleName (joinWith "." segments)
      in
        if not (Array.all isProperName parts) then Left (NotAModuleName f.path)
        else case ownerOf segments of
          Just owner | owner /= root -> Left (NameReserved { path: f.path, name, owner })
          _ -> Right name
    _ -> Left (OutsidePackage f.path)
  where
  ownerOf segments = Array.foldl longer Nothing (Array.filter (\r -> isPrefixOf r.prefix segments) roots)
  longer best r = case best of
    Just b | Array.length b.prefix >= Array.length r.prefix -> best
    _ -> Just r

isPrefixOf :: forall a. Eq a => Array a -> Array a -> Boolean
isPrefixOf prefix whole = Array.take (Array.length prefix) whole == prefix

-- | A name a segment of a module's name may be: an upper case letter, then
-- | letters, digits, `_`, and `'`.
isProperName :: String -> Boolean
isProperName segment = case SCU.uncons segment of
  Just { head, tail } -> isUpper head && Array.all isNameChar (SCU.toCharArray tail)
  Nothing -> false
  where
  isUpper c = c >= 'A' && c <= 'Z'
  isNameChar c = c >= 'a' && c <= 'z' || isUpper c || c >= '0' && c <= '9' || c == '_' || c == '\''

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

-- | A file's header, its declarations left unread; the header naming the module
-- | the file's path does.
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

-- | The headers in an order their imports allow: each after every module of
-- | the build it imports, the one given first taken first; or the first
-- | modules found importing one another.
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

-- | Every module in the order given, one at a time, each against the build
-- | environment with the modules before it committed, as the entry's
-- | replacing makes it, and its interface committed unless that refuses it.
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
-- | **Each phase is a function of what it reads alone**, so that what an
-- | earlier phase made and no later one reads is no longer held.
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
