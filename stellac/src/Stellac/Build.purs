-- | `stellac build`: the modules of a package compiled, each module's bytecode
-- | and interface written under `_build` ([Paths](Paths.purs)), where a package
-- | manager finds them.
-- |
-- | **The build is the compiler's driver, `Stella.Compiler.Build`, given what
-- | this command does for it**: the files the patterns name under the package's
-- | root, read as the driver asks; each macro's parser and each goal's
-- | synthesizer run on one compile-time session, opened at the first of them,
-- | a macro or a synthesizer of the package run from the bytecode written for
-- | its module; and what each phase makes written as the phase ends. The
-- | modules are built against `Prim`, the modules the compiler carries,
-- | `Base.Int`, `Stella.Syntax`, and `Stella.Elab`, which the session holds
-- | from its opening and is never sent, and the interfaces a dependency map
-- | names ([Dependencies](Dependencies.purs)).
-- | A macro or a synthesizer of a module the map lists runs from the bytecode
-- | the map names for it, after each module it reaches; a module the compiler
-- | carries that the map lists as well runs as the compiler carries it.
-- |
-- | **`--toolchain-rebuild` names modules the compiler carries that the package
-- | compiles anew**, which a build of no such name refuses to hold. The session
-- | still runs the ones the compiler carries; what the build writes of them is
-- | for a later toolchain.
-- |
-- | **A synthesizer that faults or uses up its budget fails the build where the
-- | goal it was solving stands**, against the synthesizer: it says nothing of
-- | whether the goal has a solution, so it is neither the program's error nor
-- | the compiler's.
-- |
-- | **A build succeeds only where everything it was to write was written**: a
-- | file a phase could not write fails the build once the modules are built, so
-- | that what an earlier build left under `_build` is never taken for what this
-- | one made. **A module's bytecode and interface are written as a pair**: a
-- | module whose pair could not be written in full leaves neither file of it,
-- | and its macros are not run. A session that did not close cleanly fails the
-- | build too.
module Stellac.Build (cmd) where

import Prelude

import Data.Array as Array
import Data.Array.NonEmpty as NonEmptyArray
import Data.Bifunctor (lmap)
import Data.Either (Either(..), either)
import Data.Foldable (foldM, for_)
import Data.Map as Map
import Data.Tuple (Tuple(..))
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Data.String (Pattern(..), joinWith, split)
import Data.Traversable (for)
import Effect.Aff (Milliseconds(..))
import Effect.Ref as Ref
import Fmt (fmt)
import Run (AFF, EFFECT, Run, expand, liftEffect)
import Run.Except (EXCEPT, throw)
import Run.Except as Except
import Stella.CLI.Effect.FS (FS)
import Stella.CLI.Effect.FS as FS
import Stella.CLI.Effect.Log (LOG)
import Stella.CLI.Effect.Log as Log
import Stella.CLI.Effect.Process (Output(..), PROCESS)
import Stella.CLI.Session.Broker (SessionHealth(..), newCancellation)
import Stella.CLI.Session.Client as Client
import Stella.CLI.Session.CompileTime (CompileTimeError(..))
import Stella.CLI.Session.RunParser (openingParser)
import Stella.CLI.Session.Synthesis (defaultSynthesisSettings, openingSynthesis)
import Stella.Compiler.Build (BuildError, BuildMessage, CompilerAction, build, buildMessages, defaultHooks, defaultSourceRoots, originMessage, printBuildMessage, warningMessage)
import Stella.Compiler.Bytecode (encode)
import Stella.Compiler.Bytecode.Bytes (Bytes)
import Stella.Compiler.Elaborate.CorePlus.Context (Origin(..))
import Stella.Compiler.Interface.Environment (addInterface, initialEnvironment, lookupInterface)
import Stella.Compiler.Interface.File as Interface
import Stella.Compiler.Macro.Compiled (compiled)
import Stella.Compiler.Macro.Run (defaultSettings)
import Stella.Compiler.TypedCore (Ident(..), ModuleName(..), Qualified(..))
import Stellac.Dependencies (printDependencyError)
import Stellac.Dependencies as Dependencies
import Stellac.Paths (buildDirectory, builtPath)
import Stellac.Options (BuildOptions)
import Type.Row (type (+))

-- | Where a build runs: the files, the log, and the session, a failure of the
-- | session thrown.
type Building = Run (EXCEPT CompileTimeError + FS + LOG + PROCESS + AFF + EFFECT + ())

cmd :: forall r. BuildOptions -> Run (FS + LOG + PROCESS + EXCEPT String + EFFECT + AFF + r) Unit
cmd opts = do
  syntax <- either (\why -> throw (internal ("the modules the compiler carries do not compile: " <> why))) pure compiled
  carried <- either (\err -> throw (internal ("the modules the compiler carries do not make an environment: " <> show err))) pure
    (foldM (flip addInterface) initialEnvironment syntax.moduleInterfaces)
  linked <- case opts.dependencies of
    Nothing -> pure { environment: carried, dependencies: [] }
    -- a relative map is under the package's root, as a relative output is
    Just given -> do
      absolute <- FS.isAbsolute given
      Dependencies.dependedOn (if absolute then given else underRoot given) carried
        >>= either (\errs -> for_ errs (Log.error <<< printDependencyError) *> throw "The build failed") pure
  let
    env = linked.environment
    -- the bytecode of each module the map lists, which the session loads it
    -- from; a module the compiler carries is never loaded from the map
    objects = Map.fromFoldable (map (\d -> Tuple d.module d.object) (Array.filter (\d -> not (Map.member d.module carried.interfaces)) linked.dependencies))
  for_ (Array.find (\name -> not (Array.any (\i -> i.name == name) syntax.moduleInterfaces)) opts.toolchainRebuild) \name ->
    throw (fmt @"`{name}` is not a module the compiler carries, and cannot be compiled anew" { name: moduleText name })
  found <- FS.glob opts.workdir patterns >>= either (\why -> throw (fmt @"The source files could not be listed: {why}" { why })) pure
  when (Array.null found) do
    throw (fmt @"No source file matches {patterns}" { patterns: joinWith ", " patterns })
  -- a relative output is under the package's root; what is absolute, the host says
  absolute <- FS.isAbsolute opts.output
  let
    output = if absolute then opts.output else underRoot opts.output
    buildDir = buildDirectory output
  FS.makeDirectory buildDir >>= either (\why -> throw (fmt @"`{dir}` could not be made: {why}" { dir: buildDir, why })) pure
  session <- liftEffect (Ref.new Nothing)
  trace <- liftEffect (Ref.new [])
  unwritten <- liftEffect (Ref.new [])
  -- the modules whose pair was written, and those the session loaded
  paired <- liftEffect (Ref.new Set.empty)
  loaded <- liftEffect (Ref.new Set.empty)
  -- the path of each module begun, which a failure of a synthesizer is reported in
  paths <- liftEffect (Ref.new Map.empty)
  -- what the synthesizers of the build run with, every one on the one session
  cancellation <- liftEffect (newCancellation (Milliseconds 1000.0))
  attempts <- liftEffect (Ref.new 0)
  health <- liftEffect (Ref.new Reusable)
  let
    files = map (\within -> { path: underRoot within, within: split (Pattern "/") within }) found

    -- what a phase could not write, kept to fail the build with once it ends
    failing :: String -> Building Unit
    failing why = liftEffect (Ref.modify_ (\ws -> Array.snoc ws why) unwritten)

    write :: String -> Either String Unit -> Building Boolean
    write path = case _ of
      Left why -> false <$ failing (fmt @"`{path}` could not be written: {why}" { path, why })
      Right _ -> pure true

    -- the bytecode, then the interface beside it; where either is not
    -- written, neither is left
    writePair :: ModuleName -> Either String { dmo :: Bytes, dmi :: Bytes } -> Building Unit
    writePair name encoded = do
      let
        dmo = builtPath output name "dmo"
        dmi = builtPath output name "dmi"
      both <- case encoded of
        Left why -> false <$ failing (internal why)
        Right bytes -> do
          wrote <- write dmo =<< FS.writeBytes dmo bytes.dmo
          if wrote then write dmi =<< FS.writeBytes dmi bytes.dmi else pure false
      if both then liftEffect (Ref.modify_ (Set.insert name) paired)
      else for_ [ dmo, dmi ] \path -> FS.remove path >>= case _ of
        Left why -> failing (fmt @"`{path}` could not be removed: {why}" { path, why })
        Right _ -> pure unit

    loading =
      { seed: syntax.preloaded
      , importsOf: \name -> if Map.member name objects then map _.imports (lookupInterface name env) else Nothing
      , loaded
      , locate: \name -> do
          written <- liftEffect (Ref.read paired)
          -- what this build wrote first, then what the map lists
          pure if Set.member name written then Just (builtPath output name "dmo") else Map.lookup name objects
      }

    action :: CompilerAction Building
    action =
      { readSource: FS.readText
      , runParser: openingParser session launch syntax.descriptor loading
      , synthesis: openingSynthesis
          { held: session
          , launch
          , descriptor: syntax.elaboration.descriptor
          , loading
          , budget: defaultSynthesisSettings.budget
          , cancellation
          , attempts
          , health
          }
      , hooks: defaultHooks
          { onStartCompile = \progress file -> do
              liftEffect (Ref.modify_ (Map.insert file.name file.path) paths)
              Log.info (fmt @"[{current}/{total}] Compiling {name} ({path})" { current: progress.current, total: progress.total, name: moduleText file.name, path: file.path })
          , onElaborated = \core -> do
              when opts.emitCore do
                Log.warn (fmt @"{name}: Core is not written as JSON by this version of the compiler" { name: moduleText core.name })
          , onEnterOptimizeIter = \mid -> traced mid.name "pre-optimised (fixpoint input)"
          , onContinueOptimizeIter = \round mid -> traced mid.name (fmt @"round {round}" { round })
          , onLeaveOptimizeIter = \mid -> traced mid.name "converged"
          , onLowered = \made -> do
              let name = moduleText made.dmo.name
              writePair made.dmo.name do
                dmo <- lmap (\err -> fmt @"the bytecode of {name} could not be encoded: {err}" { name, err: show err }) (encode made.dmo)
                dmi <- lmap (\err -> fmt @"the interface of {name} could not be encoded: {err}" { name, err: show err }) (Interface.encode { interface: made.interface, buildHash: Nothing })
                pure { dmo, dmi }
          , onModuleDone = \done -> do
              for_ done.warnings (Log.warn <<< printBuildMessage <<< warningMessage done.paths done.path)
              when (Just done.name == opts.traceOpt) do
                chunks <- liftEffect (Ref.read trace)
                let path = builtPath output done.name "mir"
                void (write path =<< FS.writeText path (traceText chunks))
          }
      }

    traced name label = when (Just name == opts.traceOpt) do
      liftEffect (Ref.modify_ (\chunks -> Array.snoc chunks (fmt @"=== {label} ===" { label })) trace)

  outcome <- expand (Except.runExcept (build action defaultSettings { environment: env, rebuilding: Set.fromFoldable opts.toolchainRebuild } defaultSourceRoots files))
  opened <- liftEffect (Ref.read session)
  closed <- for opened Client.close
  case outcome of
    Left failure -> do
      known <- liftEffect (Ref.read paths)
      case compileTimeFailure known failure of
        Just message -> do
          Log.error (printBuildMessage message)
          throw "The build failed"
        Nothing -> throw (internal (fmt @"the compile-time session failed: {failure}" { failure: show failure }))
    Right result -> do
      for_ closed case _ of
        Left failure -> Log.error (internal (fmt @"the compile-time session did not close cleanly: {failure}" { failure: show failure }))
        Right _ -> pure unit
      case result of
        Left err -> do
          reported err
          throw "The build failed"
        Right built -> do
          failures <- liftEffect (Ref.read unwritten)
          for_ failures Log.error
          when (not (Array.null failures) || closedBadly closed) do
            throw "The build failed"
          Log.info (fmt @"✓ Built {count} module(s) → {output}" { count: Array.length built, output })
  where
  patterns = if Array.null opts.src then [ "src/**/*.stel" ] else opts.src
  -- a path of the package, under its root
  underRoot path
    | opts.workdir == "." = path
    | otherwise = fmt @"{root}/{path}" { root: opts.workdir, path }

  steam = { command: opts.steamCmd, args: [ "session" ] }
  -- the session runs the build's parsers and synthesizers alike
  compileTime = { protocol: 1, profile: "elaboration", offers: [ "modules", "parse", "invoke", "kernel" ], requires: [] }
  launch = { command: steam.command, args: steam.args, output: Inherit, hello: compileTime }

  closedBadly = case _ of
    Just (Left _) -> true
    _ -> false

  traceText chunks
    | Array.length chunks <= 2 = joinWith "\n" chunks <> "\n(no optimizer rounds)\n"
    | otherwise = joinWith "\n" chunks <> "\n"

-- | A failure of compile-time execution that is neither the program's error
-- | nor the compiler's, said where it stands, the path of each module begun
-- | given: a synthesizer that faulted, or used up its budget, where the goal it
-- | was solving stands; and a module compiled anew that the session runs the
-- | carried one of in its place, with another interface.
compileTimeFailure :: Map.Map ModuleName String -> CompileTimeError -> Maybe BuildMessage
compileTimeFailure paths = case _ of
  SynthesizerFaulted r -> Just (at r.goal (fmt @"The synthesizer `{f}` faulted while solving this goal: {detail}" { f: qualifiedText r.synthesizer, detail: r.detail }))
  SynthesizerBudgetExhausted r -> Just (at r.goal (fmt @"The synthesizer `{f}` exhausted its execution budget of {budget} steps while solving this goal" { f: qualifiedText r.synthesizer, budget: grouped r.budget }))
  RebuiltDiffersFromSeed name -> Just { path: Map.lookup name paths, locations: [], message: fmt @"`{name}` is compiled anew with an interface that differs from the one of the module the compiler carries, which the macros and synthesizers of the build run on" { name: moduleText name } }
  _ -> Nothing
  where
  at goal message = case goal of
    AtSource { declaration: Qualified m _, origin } | Just path <- Map.lookup m paths -> originMessage paths path origin message
    InDeclaration (Qualified m _) | Just path <- Map.lookup m paths -> { path: Just path, locations: [], message }
    _ -> { path: Nothing, locations: [], message }

-- | A count with its digits grouped by threes: `1,000,000`.
grouped :: Int -> String
grouped n
  | n < 0 = "-" <> grouped (negate n)
  | n < 1000 = show n
  | otherwise = grouped (n / 1000) <> "," <> padded (n `mod` 1000)
      where
      padded k
        | k < 10 = "00" <> show k
        | k < 100 = "0" <> show k
        | otherwise = show k

qualifiedText :: Qualified Ident -> String
qualifiedText (Qualified (ModuleName m) (Ident n)) = m <> "." <> n

-- | A build's errors, each where it stands.
reported :: forall r. BuildError -> Run (LOG + r) Unit
reported err = for_ (NonEmptyArray.toArray (buildMessages err)) (Log.error <<< printBuildMessage)

internal :: String -> String
internal what = "Internal compiler error: " <> what

moduleText :: ModuleName -> String
moduleText (ModuleName m) = m
