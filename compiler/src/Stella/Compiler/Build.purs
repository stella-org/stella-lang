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
-- | build environment alone. **Within a module, a phase's result is held no
-- | longer than the next phase reads it**: it is handed to the host as the
-- | phase ends, and what the next phase is given is what it reads.
-- |
-- | **A module's stages run in this order**: the text is lexed, laid out, and
-- | parsed; the syntax is checked for what no later stage reads; the module is
-- | resolved, its macro calls expanded; its imports are looked up in the build
-- | environment, and the signature and the catalog they give are made, with the
-- | types the ABI manifest supplies to the module itself; it is elaborated and
-- | its Core checked; the interfaces translation reads are gathered; it is
-- | translated to Mid IR, optimized, and lowered to bytecode. **A stage that
-- | reports an error is the last that runs**, and every error it reports is
-- | returned; a module that does not compile is the last the build compiles.
module Stella.Compiler.Build
  ( PackageFile
  , Progress
  , CompilerAction
  , CompilerHooks
  , defaultHooks
  , build
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
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Set as Set
import Data.String (Pattern(..), joinWith, stripSuffix)
import Data.String.CodeUnits as SCU
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Stella.Compiler.Build.Report (BackendProblem(..), BuildError(..), BuildMessage, CompileError(..), CompileWarning, DiagnosticLocation, EnvironmentProblem(..), SyntaxProblem(..), buildMessages, locationsOf, primaryLocationOf, printCompileError, printCompileWarning, warningLocationOf)
import Stella.Compiler.Bytecode.Lower (lower)
import Stella.Compiler.Bytecode.Module (Debug, Dmo) as Bytecode
import Stella.Compiler.CST (parseHeader, parseModule)
import Stella.Compiler.CST.Check (checkModule)
import Stella.Compiler.CST.Types (Import(..), Item(..), Module(..), SourceRange)
import Stella.Compiler.Elaborate.Environment.Imported (compilationSignature, importedCatalog)
import Stella.Compiler.Elaborate.Surface.Group (groups)
import Stella.Compiler.Elaborate.Surface.Module (elaborateModule)
import Stella.Compiler.Interface (Imports, importsOf)
import Stella.Compiler.Interface.Environment (BuildEnvironment, lookupInterface, reachable, viewFor)
import Stella.Compiler.Macro.Run (ExpansionSettings, RunParser)
import Stella.Compiler.MiddleEnd.IR (Debug, Module) as MIR
import Stella.Compiler.MiddleEnd.Translate (translate)
import Stella.Compiler.Resolve.Module (Resolved, resolveModuleExpanding)
import Stella.Compiler.Surface.Origin (originOf, rangeOf)
import Stella.Compiler.Surface.Origin (Origin) as Surface
import Stella.Compiler.TypedCore (Declared, Module) as Core
import Stella.Compiler.TypedCore.Name (ModuleName(..))

-- | A file of the package: the path the host reads it by, and its path from
-- | the package's root, one segment each.
type PackageFile = { path :: String, within :: Array String }

-- | How far a build has gone: the module now compiled, counting from 1, of how
-- | many.
type Progress = { current :: Int, total :: Int }

-- | What the host does for a build: read a file, run a macro's parser, and
-- | take what each phase of a module makes as the phase ends — to show it, to
-- | write it, and to make what a module declares available to the parsers run
-- | after it.
type CompilerAction m =
  { readSource :: String -> m (Either String String)
  , runParser :: RunParser m
  , hooks :: CompilerHooks m
  }

-- | What the host is handed as a build goes. `onStartCompile` comes as a
-- | module's compiling begins; each phase hook as the phase ends, with what it
-- | made, which the build keeps no longer than the next phase needs it; the
-- | optimizer's three as its rounds go — once before the first, once after
-- | each round that changed the module, and once when it stops — and
-- | `onModuleDone`, with the warnings compiling the module gave, once its last
-- | phase has ended.
type CompilerHooks m =
  { onStartCompile :: Progress -> { path :: String, name :: ModuleName } -> m Unit
  , onElaborated :: Core.Module Surface.Origin -> m Unit
  , onTranslated :: MIR.Module -> m Unit
  , onEnterOptimizeIter :: MIR.Module -> m Unit
  , onContinueOptimizeIter :: Int -> MIR.Module -> m Unit
  , onLeaveOptimizeIter :: MIR.Module -> m Unit
  , onLowered :: { dmo :: Bytecode.Dmo, debug :: Bytecode.Debug Surface.Origin } -> m Unit
  , onModuleDone :: { path :: String, name :: ModuleName, warnings :: Array CompileWarning } -> m Unit
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

-- | What a header gives a build: the module's file and name, where its name is
-- | written, and what it imports, each with where it is written.
type Header =
  { path :: String
  , name :: ModuleName
  , imports :: Array { module :: ModuleName, at :: DiagnosticLocation }
  }

-- | Build the files given against the build environment, in an order their
-- | imports allow. The modules built, in the order built.
build
  :: forall m
   . MonadRec m
  => CompilerAction m
  -> ExpansionSettings
  -> BuildEnvironment
  -> Array PackageFile
  -> m (Either BuildError (Array { path :: String, name :: ModuleName }))
build action settings env files = runExceptT do
  named <- except (placed files)
  headers <- headersOf action named
  order <- except (ordered headers)
  compileAll action settings env (Set.fromFoldable (map _.name headers)) order

-- | Every file given its module's name, read off its path; no file given twice,
-- | and no module named twice.
placed :: Array PackageFile -> Either BuildError (Array { path :: String, name :: ModuleName })
placed files = do
  for_ (foldl seen { paths: Set.empty, twice: Nothing } files).twice (Left <<< ListedTwice)
  named <- traverse (\f -> { path: f.path, name: _ } <$> moduleNameOf f) files
  for_ (foldl once { names: Map.empty, twice: Nothing } named).twice (Left <<< NamedTwice)
  pure named
  where
  seen acc f
    | Just _ <- acc.twice = acc
    | Set.member f.path acc.paths = acc { twice = Just f.path }
    | otherwise = acc { paths = Set.insert f.path acc.paths }
  once acc f
    | Just _ <- acc.twice = acc
    | Just first <- Map.lookup f.name acc.names = acc { twice = Just { name: f.name, paths: [ first, f.path ] } }
    | otherwise = acc { names = Map.insert f.name f.path acc.names }

-- | The module a file holds, read off its path from the package's root.
moduleNameOf :: PackageFile -> Either BuildError ModuleName
moduleNameOf f = case Array.uncons f.within of
  Just { head: root, tail } | root == "src" || root == "test" -> case Array.unsnoc tail of
    Just { init, last } | Just stem <- stripSuffix (Pattern ".stel") last ->
      let
        parts = Array.snoc init stem
      in
        if not (Array.all isProperName parts) then Left (NotAModuleName f.path)
        else if root == "test" then Right (ModuleName (joinWith "." (Array.cons "Test" parts)))
        else if Array.head parts == Just "Test" then Left (NameReserved { path: f.path, name: ModuleName (joinWith "." parts) })
        else Right (ModuleName (joinWith "." parts))
    _ -> Left (OutsidePackage f.path)
  _ -> Left (OutsidePackage f.path)

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
  => CompilerAction m
  -> Array { path :: String, name :: ModuleName }
  -> ExceptT BuildError m (Array Header)
headersOf action named = tailRecM step { headers: [], i: 0 }
  where
  step { headers, i } = case Array.index named i of
    Nothing -> pure (Done headers)
    Just file -> do
      header <- headerOf action file
      pure (Loop { headers: Array.snoc headers header, i: i + 1 })

-- | A file's header, its declarations left unread; the header naming the module
-- | the file's path does.
headerOf
  :: forall m
   . Monad m
  => CompilerAction m
  -> { path :: String, name :: ModuleName }
  -> ExceptT BuildError m Header
headerOf action file = do
  text <- action.readSource file.path # orFailWithM (\detail -> Unreadable { path: file.path, detail })
  Module m <- parseHeader text # orFailWith (\err -> ModuleFailed { path: file.path, name: file.name, errors: pure (Syntax (Unparsed err)) })
  let written = ModuleName m.name.name
  when (written /= file.name) do
    throwError (NameMismatch { path: file.path, written, expected: file.name, at: inSource m.name.range })
  pure { path: file.path, name: file.name, imports: Array.mapMaybe importOf m.items }
  where
  importOf = case _ of
    ItemImport (Import r) -> Just { module: ModuleName r.module.name, at: inSource r.module.range }
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

-- | Every module in the order given, one at a time.
compileAll
  :: forall m
   . MonadRec m
  => CompilerAction m
  -> ExpansionSettings
  -> BuildEnvironment
  -> Set ModuleName
  -> Array Header
  -> ExceptT BuildError m (Array { path :: String, name :: ModuleName })
compileAll action settings env inBuild order = tailRecM step { built: [], i: 0 }
  where
  total = Array.length order
  step { built, i } = case Array.index order i of
    Nothing -> pure (Done built)
    Just header -> do
      compileOne action settings env inBuild { current: i + 1, total } header
      pure (Loop { built: Array.snoc built { path: header.path, name: header.name }, i: i + 1 })

-- | A module of the build read and compiled, against modules built before the
-- | build alone.
compileOne
  :: forall m
   . Monad m
  => CompilerAction m
  -> ExpansionSettings
  -> BuildEnvironment
  -> Set ModuleName
  -> Progress
  -> Header
  -> ExceptT BuildError m Unit
compileOne action settings env inBuild progress header = do
  for_ (Array.find (\i -> Set.member i.module inBuild) header.imports) \within ->
    throwError (ImportWithinBuild { path: header.path, imported: within.module, at: within.at })
  text <- action.readSource header.path # orFailWithM (\detail -> Unreadable { path: header.path, detail })
  lift (action.hooks.onStartCompile progress { path: header.path, name: header.name })
  warnings <- compileModule action settings env text # orFailWithM (\errors -> ModuleFailed { path: header.path, name: header.name, errors })
  lift (action.hooks.onModuleDone { path: header.path, name: header.name, warnings })

-- | Compile a module's source against the build environment, its macros'
-- | parsers run and what each phase makes handed over through the action
-- | given. The warnings compiling it gave.
-- |
-- | **Each phase is a function of what it reads alone**, so that what an
-- | earlier phase made and no later one reads is no longer held.
compileModule
  :: forall m
   . Monad m
  => CompilerAction m
  -> ExpansionSettings
  -> BuildEnvironment
  -> String
  -> m (Either (NonEmptyArray CompileError) (Array CompileWarning))
compileModule action settings env text = runExceptT do
  cst <- parseModule text # orFailWith (pure <<< Syntax <<< Unparsed)
  checkModule cst # failingWith (Syntax <<< IllFormed)
  resolved <- lift (resolveModuleExpanding action.runParser settings env cst)
  elaborated action env resolved

-- | What a phase of a module gives, or the errors it stops at.
type Phase m = ExceptT (NonEmptyArray CompileError) m

-- | The module resolved, elaborated, and checked, handed on with the warnings
-- | alone of what resolving it gave.
elaborated
  :: forall m
   . Monad m
  => CompilerAction m
  -> BuildEnvironment
  -> Resolved
  -> Phase m (Array CompileWarning)
elaborated action env resolved = checkedCore env resolved >>= checked action resolved.warnings

checkedCore
  :: forall m
   . Monad m
  => BuildEnvironment
  -> Resolved
  -> Phase m { core :: Core.Module Surface.Origin, declared :: Core.Declared Surface.Origin, imports :: Imports }
checkedCore env resolved = do
  resolved.errors # failingWith Resolution
  let m = resolved.module
  view <- viewFor (map _.module m.imports) env # orFailWith (pure <<< Environment <<< ViewRefused)
  signature <- compilationSignature env view m.name # orFailWith (pure <<< Environment <<< ImportsRefused)
  made <- (elaborateModule signature (importedCatalog env view) m resolved.exports).result # orFailWith (map Elaboration)
  imports <- importsOf (Array.mapMaybe (\n -> lookupInterface n env) (Set.toUnfoldable (reachable view)))
    # orFailWith (pure <<< Environment <<< InterfacesRefused)
  pure { core: made.core, declared: made.declared, imports }

-- | The checked Core handed to the host. What the module was resolved into is
-- | not in reach of what follows.
checked
  :: forall m
   . Monad m
  => CompilerAction m
  -> Array CompileWarning
  -> { core :: Core.Module Surface.Origin, declared :: Core.Declared Surface.Origin, imports :: Imports }
  -> Phase m (Array CompileWarning)
checked action warnings made = do
  lift (action.hooks.onElaborated made.core)
  translated action warnings made

-- | The checked Core translated to Mid IR.
translated
  :: forall m
   . Monad m
  => CompilerAction m
  -> Array CompileWarning
  -> { core :: Core.Module Surface.Origin, declared :: Core.Declared Surface.Origin, imports :: Imports }
  -> Phase m (Array CompileWarning)
translated action warnings made = do
  mid <- translate made.imports made.core made.declared # orFailWith (pure <<< Backend <<< TranslateFailed)
  lift (action.hooks.onTranslated mid.module)
  optimized action warnings mid

-- | The Mid IR optimized. No pass rewrites a module yet, so the optimizer stops
-- | before a first round.
optimized
  :: forall m
   . Monad m
  => CompilerAction m
  -> Array CompileWarning
  -> { module :: MIR.Module, debug :: MIR.Debug Surface.Origin }
  -> Phase m (Array CompileWarning)
optimized action warnings mid = do
  lift (action.hooks.onEnterOptimizeIter mid.module)
  lift (action.hooks.onLeaveOptimizeIter mid.module)
  lowered action warnings mid

-- | The Mid IR lowered to bytecode.
lowered
  :: forall m
   . Monad m
  => CompilerAction m
  -> Array CompileWarning
  -> { module :: MIR.Module, debug :: MIR.Debug Surface.Origin }
  -> Phase m (Array CompileWarning)
lowered action warnings mid = do
  bytecode <- lower mid # orFailWith (pure <<< Backend <<< LowerFailed)
  lift (action.hooks.onLowered bytecode)
  pure warnings

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

-- | A range of the source, as a diagnostic names it.
inSource :: SourceRange -> DiagnosticLocation
inSource r = let s = rangeOf (originOf r) in { start: s.start, end: s.end }
