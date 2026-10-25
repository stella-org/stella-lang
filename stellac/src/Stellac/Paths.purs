-- | Where `stellac compile` writes, in the output directory `stella.json`
-- | names:
-- |
-- | ```text
-- | <output>/<M>.dmo         each module's bytecode
-- | <output>/<M>.dmi         each module's interface
-- | <output>/<M>.mir         the optimizer's trace of each module `traceOptimizer` names
-- | <output>/output.json     what the build states of the modules it built
-- | ```
module Stellac.Paths
  ( builtPath
  , outputPath
  ) where

import Fmt (fmt)
import Stella.CLI.Effect.FS (FilePath)
import Stella.Compiler.TypedCore (ModuleName(..))

-- | The file of a module in the output directory, with the extension given.
builtPath :: FilePath -> ModuleName -> String -> FilePath
builtPath output (ModuleName m) extension = fmt @"{output}/{m}.{extension}" { output, m, extension }

-- | `output.json` in the output directory.
outputPath :: FilePath -> FilePath
outputPath output = fmt @"{output}/output.json" { output }
