-- | `stellac build`: the modules of a package compiled, each module's bytecode
-- | and interface written under `_build` ([Paths](Paths.purs)), where a package
-- | manager finds them.
-- |
-- | **The build is the driver's ordinary one, run on disk by the host
-- | `Stella.CLI.Build`**, given the files the patterns name under the
-- | package's root. The modules are built against `Prim`, the seed modules,
-- | `Base.Int`, `Stella.Syntax`, and `Stella.Elab`, which the session holds
-- | from its opening and is never sent, and the interfaces a dependency map
-- | names ([Dependencies](Dependencies.purs)). A macro or a synthesizer of a
-- | module the map lists runs from the bytecode the map names for it, after
-- | each module it reaches; a seed module the map lists as well runs as the
-- | session holds it. A file of the package holding a seed module is refused
-- | as any module the build is compiled against is.
module Stellac.Build (cmd) where

import Prelude

import Data.Array as Array
import Data.Either (either)
import Data.Foldable (foldM, for_)
import Data.Map as Map
import Data.Maybe (Maybe(..))
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
import Stella.Compiler.Build (build, defaultSourceRoots)
import Stella.Compiler.Interface.Environment (addInterface, initialEnvironment)
import Stella.Compiler.Macro.Compiled (compiled)
import Stella.Compiler.Macro.Run (defaultSettings)
import Stellac.Dependencies (printDependencyError)
import Stellac.Dependencies as Dependencies
import Stellac.Options (BuildOptions)
import Stellac.Paths (buildDirectory, builtPath)
import Stellac.Sources (sourceFiles)
import Stellac.Sources as Sources
import Type.Row (type (+))

cmd :: forall r. BuildOptions -> Run (FS + LOG + PROCESS + EXCEPT String + EFFECT + AFF + r) Unit
cmd opts = do
  seed <- either (\why -> throw (internal ("the seed modules do not compile: " <> why))) pure compiled
  environment <- either (\err -> throw (internal ("the seed modules do not make an environment: " <> show err))) pure
    (foldM (flip addInterface) initialEnvironment seed.moduleInterfaces)
  linked <- case opts.dependencies of
    Nothing -> pure { environment, dependencies: [] }
    -- a relative map is under the package's root, as a relative output is
    Just given -> do
      absolute <- FS.isAbsolute given
      Dependencies.dependedOn (if absolute then given else underRoot given) environment
        >>= either (\errs -> for_ errs (Log.error <<< printDependencyError) *> throw "The build failed") pure
  files <- sourceFiles opts.workdir opts.src
  -- a relative output is under the package's root; what is absolute, the host says
  absolute <- FS.isAbsolute opts.output
  let
    output = if absolute then opts.output else underRoot opts.output
    buildDir = buildDirectory output
  FS.makeDirectory buildDir >>= either (\why -> throw (fmt @"`{dir}` could not be made: {why}" { dir: buildDir, why })) pure
  void $ onDisk
    { seed
    , environment: linked.environment
    -- the bytecode of each module the map lists, which the session loads it
    -- from; a seed module is never loaded from the map
    , objects: Map.fromFoldable (map (\d -> Tuple d.module d.object) (Array.filter (\d -> not (Map.member d.module environment.interfaces)) linked.dependencies))
    , written: builtPath output
    , steamCmd: opts.steamCmd
    , traceOpt: opts.traceOpt
    , emitCore: opts.emitCore
    , destination: output
    }
    \action env -> build action defaultSettings env defaultSourceRoots files
  where
  underRoot = Sources.underRoot opts.workdir
