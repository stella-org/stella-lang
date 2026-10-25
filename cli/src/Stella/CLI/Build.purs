-- | A build on disk: an entry of the compiler's driver, run with what a command
-- | does around it.
-- |
-- | The host knows no kinds of build and decides nothing of what a build may
-- | replace. Its caller gives it the environment, the bytecode of modules
-- | outside the build that the session may load, where each written file goes,
-- | and the entry to run.
-- |
-- | For the driver, the host reads files as asked, runs every macro's parser
-- | and goal's synthesizer on one compile-time session opened at the first of
-- | them, runs a module of the build from the bytecode the build wrote, and
-- | writes what each phase makes as the phase ends. The session holds the seed
-- | modules from its opening and is never sent another module of their names.
-- | Where a module it runs reaches one the build compiled anew, the build fails
-- | unless the new interface is the one the session holds.
-- |
-- | A synthesizer that faults or uses up its budget fails the build where its
-- | goal stands. That says nothing of whether the goal has a solution, so it is
-- | neither the program's error nor the compiler's.
-- |
-- | A build succeeds only where everything it was to write was written, so
-- | what an earlier build left is never taken for this one's work; a file that
-- | could not be written fails the build once the modules are built. Bytecode
-- | and interface are written as a pair: where either fails, neither file is
-- | left and the module's macros are not run. A session that does not close
-- | cleanly fails the build too.
module Stella.CLI.Build
  ( Host
  , Building
  , Built
  , onDisk
  , internal
  ) where

import Prelude

import Data.Array as Array
import Data.Array.NonEmpty as NonEmptyArray
import Data.Bifunctor (lmap)
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Set as Set
import Data.String (joinWith)
import Data.Traversable (for)
import Effect.Aff (Milliseconds(..))
import Effect.Ref as Ref
import Fmt (fmt)
import Run (AFF, EFFECT, Run, expand, liftEffect)
import Run.Except (EXCEPT, throw)
import Run.Except as Except
import Stella.CLI.Effect.FS (FS, FilePath)
import Stella.CLI.Effect.FS as FS
import Stella.CLI.Effect.Log (LOG)
import Stella.CLI.Effect.Log as Log
import Stella.CLI.Effect.Process (Output(..), PROCESS)
import Stella.CLI.Session.Broker (SessionHealth(..), newCancellation)
import Stella.CLI.Session.Client as Client
import Stella.CLI.Session.CompileTime (CompileTimeError(..))
import Stella.CLI.Session.RunParser (openingParser)
import Stella.CLI.Session.Synthesis (defaultSynthesisSettings, openingSynthesis)
import Stella.Compiler.Build (BuildError, BuildMessage, CompilerAction, buildMessages, defaultHooks, originMessage, printBuildMessage, warningMessage)
import Stella.Compiler.Bytecode (encode)
import Stella.Compiler.Bytecode.Bytes (Bytes)
import Stella.Compiler.Elaborate.CorePlus.Context (Origin(..))
import Stella.Compiler.Interface.Environment (BuildEnvironment, lookupInterface)
import Stella.Compiler.Interface.File as Interface
import Stella.Compiler.Macro.Compiled (Compiled)
import Stella.Compiler.TypedCore (Ident(..), ModuleName(..), Qualified(..))
import Type.Row (type (+))

-- | What the caller gives the host. `seed` is what the session holds from its
-- | opening; `objects` are the bytecode of modules outside the build that the
-- | session may load, no seed module among them; `written` places a module's
-- | file by extension; `traced` names the modules whose optimizer rounds are
-- | traced; `finish` writes what the caller adds once every module is written,
-- | and answers why the build fails, nothing where it does not; `destination`
-- | is what the closing message names.
type Host =
  { seed :: Compiled
  , environment :: BuildEnvironment
  , objects :: Map ModuleName FilePath
  , written :: ModuleName -> String -> FilePath
  , steamCmd :: String
  , traced :: Array ModuleName
  , emitCore :: Boolean
  , finish :: Run (FS + ()) (Array String)
  , destination :: String
  }

-- | Where a build runs: the files, the log, and the session, whose failure is
-- | thrown.
type Building = Run (EXCEPT CompileTimeError + FS + LOG + PROCESS + AFF + EFFECT + ())

-- | What a successful build built, in order, and the modules the session
-- | loaded.
type Built = { modules :: Array { path :: String, name :: ModuleName }, loaded :: Set ModuleName }

-- | Runs the entry given with the host's action and environment. A build that
-- | fails says why and throws.
onDisk
  :: forall r
   . Host
  -> (CompilerAction Building -> BuildEnvironment -> Building (Either BuildError (Array { path :: String, name :: ModuleName })))
  -> Run (FS + LOG + PROCESS + EXCEPT String + EFFECT + AFF + r) Built
onDisk host entry = do
  session <- liftEffect (Ref.new Nothing)
  trace <- liftEffect (Ref.new [])
  unwritten <- liftEffect (Ref.new [])
  -- the modules whose pair was written, and those the session loaded
  paired <- liftEffect (Ref.new Set.empty)
  loaded <- liftEffect (Ref.new Set.empty)
  -- the path of each module begun, for reporting a synthesizer's failure
  paths <- liftEffect (Ref.new Map.empty)
  -- what the build's synthesizers share, all on the one session
  cancellation <- liftEffect (newCancellation (Milliseconds 1000.0))
  attempts <- liftEffect (Ref.new 0)
  health <- liftEffect (Ref.new Reusable)
  let
    -- what a phase could not write, to fail the build with at the end
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
        dmo = host.written name "dmo"
        dmi = host.written name "dmi"
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
      { seed: host.seed.preloaded
      , importsOf: \name -> if Map.member name host.objects then map _.imports (lookupInterface name host.environment) else Nothing
      , loaded
      , locate: \name -> do
          written <- liftEffect (Ref.read paired)
          -- what this build wrote first, then what the caller says is elsewhere
          pure if Set.member name written then Just (host.written name "dmo") else Map.lookup name host.objects
      }

    action :: CompilerAction Building
    action =
      { readSource: FS.readText
      , runParser: openingParser session launch host.seed.descriptor loading
      , synthesis: openingSynthesis
          { held: session
          , launch
          , descriptor: host.seed.elaboration.descriptor
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
              when host.emitCore do
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
              when (Array.elem done.name host.traced) do
                chunks <- liftEffect (Ref.read trace)
                liftEffect (Ref.write [] trace)
                let path = host.written done.name "mir"
                void (write path =<< FS.writeText path (traceText chunks))
          }
      }

    traced name label = when (Array.elem name host.traced) do
      liftEffect (Ref.modify_ (\chunks -> Array.snoc chunks (fmt @"=== {label} ===" { label })) trace)

  outcome <- expand (Except.runExcept (entry action host.environment))
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
          finishing <- expand host.finish
          for_ finishing Log.error
          when (not (Array.null finishing)) do
            throw "The build failed"
          Log.info (fmt @"✓ Built {count} module(s) → {destination}" { count: Array.length built, destination: host.destination })
          { modules: built, loaded: _ } <$> liftEffect (Ref.read loaded)
  where
  -- the session runs the build's parsers and synthesizers alike
  compileTime = { protocol: 1, profile: "elaboration", offers: [ "modules", "parse", "invoke", "kernel" ], requires: [] }
  launch = { command: host.steamCmd, args: [ "session" ], output: Inherit, hello: compileTime }

  closedBadly = case _ of
    Just (Left _) -> true
    _ -> false

  traceText chunks
    | Array.length chunks <= 2 = joinWith "\n" chunks <> "\n(no optimizer rounds)\n"
    | otherwise = joinWith "\n" chunks <> "\n"

-- | A failure of compile-time execution that is neither the program's error
-- | nor the compiler's, placed by the path of each module begun: a synthesizer
-- | that faulted or used up its budget, at its goal; and a seed module compiled
-- | anew with another interface than the one the session runs.
compileTimeFailure :: Map ModuleName String -> CompileTimeError -> Maybe BuildMessage
compileTimeFailure paths = case _ of
  SynthesizerFaulted r -> Just (at r.goal (fmt @"The synthesizer `{f}` faulted while solving this goal: {detail}" { f: qualifiedText r.synthesizer, detail: r.detail }))
  SynthesizerBudgetExhausted r -> Just (at r.goal (fmt @"The synthesizer `{f}` exhausted its execution budget of {budget} steps while solving this goal" { f: qualifiedText r.synthesizer, budget: grouped r.budget }))
  RebuiltDiffersFromSeed name -> Just { path: Map.lookup name paths, locations: [], message: fmt @"`{name}` is compiled anew with an interface that differs from the one of the seed module the macros and synthesizers of the build run on" { name: moduleText name } }
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

-- | What says a failure is the compiler's own.
internal :: String -> String
internal what = "Internal compiler error: " <> what

moduleText :: ModuleName -> String
moduleText (ModuleName m) = m
