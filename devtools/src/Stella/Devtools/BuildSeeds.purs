-- | `stella-devtools build-seeds`: the seed modules, which are loaded as the
-- | compiler bootstraps, compiled anew from their sources by one seed build,
-- | each module's interface and bytecode written as `<output>/<M>.dmi` and
-- | `<output>/<M>.dmo`.
-- |
-- | **The sources are read where the repository keeps them**, from the
-- | directory this runs in, which is the repository's root. The build is the
-- | driver's seed build, run on disk by the host `Stella.CLI.Build`, against
-- | `Prim` and the seed modules and given no dependency map; every module it
-- | is given is compiled anew, so none is kept, and their interfaces may
-- | change.
-- |
-- | **It never changes the seed modules the compiler holds**: it builds with
-- | them as they stand, into the directory given, and taking what it wrote
-- | into the compiler is another step's. Its macros and synthesizers run on
-- | the seed modules as the session holds them, and the session is never sent
-- | what the build wrote of them.
module Stella.Devtools.BuildSeeds (seedModules, cmd) where

import Prelude

import Data.Array as Array
import Data.Either (either)
import Data.Foldable (foldM)
import Data.Map as Map
import Data.Maybe (Maybe(..))
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
    , traceOpt: Nothing
    , emitCore: false
    , destination: opts.output
    }
    \action env -> buildSeeds action defaultSettings env seedModules
