-- | `stellac build`: the modules of a package compiled, each module's bytecode
-- | and interface written under `_build` ([Paths](Paths.purs)), where a package
-- | manager finds them.
-- |
-- | **The build is the compiler's driver, `Stella.Compiler.Build`, given what
-- | this command does for it**: the files the patterns name under the package's
-- | root, read as the driver asks; each macro's parser run on a compile-time
-- | session, opened at the first one, a macro of the package run from the
-- | bytecode written for its module; and what each phase makes written as the
-- | phase ends. The modules are built against `Prim` and the modules the
-- | compiler carries, `Base.Int` and `Stella.Syntax`.
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
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Data.String (Pattern(..), joinWith, split)
import Data.Traversable (for)
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
import Stella.CLI.Session.Client as Client
import Stella.CLI.Session.RunParser (ParserRunnerError, openingParser)
import Stella.Compiler.Build (BuildError, CompilerAction, build, buildMessages, defaultHooks, defaultSourceRoots, printBuildMessage, warningMessage)
import Stella.Compiler.Bytecode (encode)
import Stella.Compiler.Bytecode.Bytes (Bytes)
import Stella.Compiler.Interface.Environment (addInterface, initialEnvironment)
import Stella.Compiler.Interface.File as Interface
import Stella.Compiler.Macro.Compiled (compiled)
import Stella.Compiler.Macro.Run (defaultSettings)
import Stella.Compiler.TypedCore (ModuleName(..))
import Stellac.Paths (buildDirectory, builtPath)
import Stellac.Options (BuildOptions)
import Type.Row (type (+))

-- | Where a build runs: the files, the log, and the session, a failure of the
-- | session thrown.
type Building = Run (EXCEPT ParserRunnerError + FS + LOG + PROCESS + AFF + EFFECT + ())

cmd :: forall r. BuildOptions -> Run (FS + LOG + PROCESS + EXCEPT String + EFFECT + AFF + r) Unit
cmd opts = do
  syntax <- either (\why -> throw (internal ("the modules the compiler carries do not compile: " <> why))) pure compiled
  env <- either (\err -> throw (internal ("the modules the compiler carries do not make an environment: " <> show err))) pure
    (foldM (flip addInterface) initialEnvironment syntax.moduleInterfaces)
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
      { loaded
      , locate: \name -> do
          written <- liftEffect (Ref.read paired)
          pure if Set.member name written then Just (builtPath output name "dmo") else Nothing
      }

    action :: CompilerAction Building
    action =
      { readSource: FS.readText
      , runParser: openingParser session { command: steam.command, args: steam.args, output: Inherit, hello: parsing } syntax.descriptor loading
      , hooks: defaultHooks
          { onStartCompile = \progress file ->
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

  outcome <- expand (Except.runExcept (build action defaultSettings env defaultSourceRoots files))
  opened <- liftEffect (Ref.read session)
  closed <- for opened Client.close
  case outcome of
    Left failure -> throw (internal (fmt @"the compile-time session failed: {failure}" { failure: show failure }))
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
  parsing = { protocol: 1, profile: "elaboration", offers: [ "modules", "parse" ], requires: [] }

  closedBadly = case _ of
    Just (Left _) -> true
    _ -> false

  traceText chunks
    | Array.length chunks <= 2 = joinWith "\n" chunks <> "\n(no optimizer rounds)\n"
    | otherwise = joinWith "\n" chunks <> "\n"

-- | A build's errors, each where it stands.
reported :: forall r. BuildError -> Run (LOG + r) Unit
reported err = for_ (NonEmptyArray.toArray (buildMessages err)) (Log.error <<< printBuildMessage)

internal :: String -> String
internal what = "Internal compiler error: " <> what

moduleText :: ModuleName -> String
moduleText (ModuleName m) = m
