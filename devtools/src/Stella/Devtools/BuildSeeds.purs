-- | `stella-devtools build-seeds`: compiles the seed modules from the source,
-- | which are loaded during compiler bootstrap and serve as basis for elaborator
-- | on the steam compile-time session.
-- | Unlike `stellac compile`, it does not read `stella.json` so does not respect
-- | `workdir` or `dependencies`; it assumes to be run on the project root and
-- | reads the sources from `stella-packages` and every module is compiled anew from scratch.
-- |
-- | Note that during compile-time session the steam does not reload the seed modules
-- | with the new ones
module Stella.Devtools.BuildSeeds (seedModules, cmd) where

import Prelude

import Data.Array as Array
import Data.Either (either)
import Data.Foldable (foldM)
import Data.Map as Map
import Stella.Devtools.Options (BuildSeedsOptions)
import Fmt (fmt)
import Run (AFF, EFFECT, Run)
import Run.Except (EXCEPT, throw)
import Stella.CLI.Build (internal, onDisk)
import Stella.CLI.Effect.FS (FS, FilePath)
import Stella.CLI.Effect.FS as FS
import Stella.CLI.Effect.Log (LOG)
import Stella.CLI.Effect.Process (PROCESS)
import Stella.Compiler.Build (buildSeeds)
import Stella.Compiler.Interface.Environment (addInterface, initialEnvironment)
import Stella.Compiler.Macro.Compiled (compiled)
import Stella.Compiler.Macro.Run (defaultSettings)
import Stella.Compiler.TypedCore (ModuleName(..))
import Type.Row (type (+))

-- | Each seed module, with its source from the repository's root.
seedModules :: Array { path :: FilePath, name :: ModuleName }
seedModules =
  [ { path: "stella-packages/base/src/Base/Int.stel", name: ModuleName "Base.Int" }
  , { path: "stella-packages/compiler-lib/src/Stella/Syntax.stel", name: ModuleName "Stella.Syntax" }
  , { path: "stella-packages/compiler-lib/src/Stella/Elab.stel", name: ModuleName "Stella.Elab" }
  ]

cmd :: forall r. BuildSeedsOptions -> Run (FS + LOG + PROCESS + EXCEPT String + EFFECT + AFF + r) Unit
cmd opts = do
  seed <- either (\why -> throw (internal ("the seed modules do not compile: " <> why))) pure compiled
  environment <- either (\err -> throw (internal ("the seed modules do not make an environment: " <> show err))) pure
    (foldM (flip addInterface) initialEnvironment seed.moduleInterfaces)
  when (Array.sort (map _.name seedModules) /= Array.sort (map _.name seed.moduleInterfaces)) do
    throw (internal "the sources named are not those of the seed modules")
  FS.makeDirectory opts.output >>= either (\why -> throw (fmt @"`{dir}` could not be made: {why}" { dir: opts.output, why })) pure
  void $ onDisk
    { seed
    , environment
    , objects: Map.empty
    , written: \(ModuleName m) extension -> fmt @"{dir}/{m}.{extension}" { dir: opts.output, m, extension }
    , steamCmd: opts.steamCmd
    , traced: []
    , emitCore: false
    , destination: opts.output
    }
    \action env -> buildSeeds action defaultSettings env seedModules
