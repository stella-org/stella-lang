-- | Where a build writes, under the output directory:
-- |
-- | ```text
-- | <output>/_build/<M>.dmo   each module's bytecode
-- | <output>/_build/<M>.mir   the optimizer's trace of the module --trace-opt names
-- | ```
module Stellac.Paths
  ( buildDirectory
  , builtPath
  ) where

import Fmt (fmt)
import Stella.CLI.Effect.FS (FilePath)
import Stella.Compiler.TypedCore (ModuleName(..))

buildDirectory :: FilePath -> FilePath
buildDirectory output = fmt @"{output}/_build" { output }

-- | The file of a module under `_build`, with the extension given.
builtPath :: FilePath -> ModuleName -> String -> FilePath
builtPath output (ModuleName m) extension = fmt @"{dir}/{m}.{extension}" { dir: buildDirectory output, m, extension }
