-- | `stellac compile <stella.json>`: compiles the modules `stella.json` lists
-- | in the order listed, and writes each module's bytecode and interface to
-- | the output directory ([Paths](Paths.purs)).
-- |
-- | It runs the driver's ordinary build on the host `Stella.CLI.Build`, which
-- | reorders nothing and refuses a module listed before a module of the build
-- | it imports. Modules are compiled against `Prim`, the seed modules, and the
-- | interfaces in `dependencies` ([Dependencies](Dependencies.purs)). A macro
-- | or synthesizer of a module in `dependencies` runs from the bytecode listed
-- | for it, except a seed module, which runs as the session holds it. A seed
-- | module in `modules` is refused.
-- |
-- | `dependencies` is checked even when `modules` is empty; nothing is then
-- | written and the command succeeds.
module Stellac.Compile (cmd) where

import Prelude

import Data.Array as Array
import Data.Either (either)
import Data.Foldable (foldM, for_)
import Data.Map as Map
import Data.Tuple (Tuple(..))
import Fmt (fmt)
import Run (AFF, EFFECT, Run)
import Run.Except (EXCEPT, throw)
import Stella.CLI.Build (internal, onDisk)
import Stella.CLI.Effect.FS (FS)
import Stella.CLI.Effect.FS as FS
import Stella.CLI.Effect.Log (LOG)
import Stella.CLI.Effect.Log as Log
import Stella.CLI.Effect.Process (PROCESS)
import Stella.Compiler.Build (build)
import Stella.Compiler.Interface.Environment (addInterface, initialEnvironment)
import Stella.Compiler.Macro.Compiled (compiled)
import Stella.Compiler.Macro.Run (defaultSettings)
import Stellac.Config (Config)
import Stellac.Dependencies (printDependencyError)
import Stellac.Dependencies as Dependencies
import Stellac.Paths (builtPath)
import Type.Row (type (+))

cmd :: forall r. Config -> Run (FS + LOG + PROCESS + EXCEPT String + EFFECT + AFF + r) Unit
cmd config = do
  seed <- either (\why -> throw (internal ("the seed modules do not compile: " <> why))) pure compiled
  environment <- either (\err -> throw (internal ("the seed modules do not make an environment: " <> show err))) pure
    (foldM (flip addInterface) initialEnvironment seed.moduleInterfaces)
  linked <- Dependencies.dependedOn config.dependencies environment
    >>= either (\errs -> for_ errs (Log.error <<< printDependencyError) *> throw "The build failed") pure
  if Array.null config.modules then Log.info "Nothing to build"
  else do
    let output = config.options.output
    FS.makeDirectory output >>= either (\why -> throw (fmt @"`{dir}` could not be made: {why}" { dir: output, why })) pure
    void $ onDisk
      { seed
      , environment: linked
      -- where the session loads each module of `dependencies` from; a seed
      -- module never is
      , objects: Map.fromFoldable (map (\d -> Tuple d.module d.object) (Array.filter (\d -> not (Map.member d.module environment.interfaces)) config.dependencies))
      , written: builtPath output
      , steamCmd: config.options.steamCmd
      , traced: config.options.traceOptimizer
      , emitCore: config.options.emitCore
      , destination: output
      }
      \action env -> build action defaultSettings env (map (\m -> { path: m.path, name: m.module }) config.modules)
