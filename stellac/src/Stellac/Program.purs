module Stellac.Program (program, loaded) where

import Prelude

import Data.Either (either)
import Data.Foldable (for_)
import Fmt (fmt)
import Run (AFF, EFFECT, Run)
import Run.Except (EXCEPT, throw)
import Stella.CLI.Effect.FS (FS, FilePath)
import Stella.CLI.Effect.Log (LOG)
import Stella.CLI.Effect.Log as Log
import Stella.CLI.Effect.Process (PROCESS)
import Stellac.Compile as Compile
import Stellac.Config (Config, printConfigError)
import Stellac.Config as Config
import Stellac.Graph as Graph
import Stellac.Options (Command(..))
import Type.Row (type (+))

program :: Command -> Config -> Run (FS + LOG + PROCESS + EXCEPT String + EFFECT + AFF ()) Unit
program command config = case command of
  Compile _ -> Compile.cmd config
  Graph _ -> Graph.cmd config

-- | The `stella.json` at the path given; where it has errors, each is said and
-- | the file is refused.
loaded :: forall r. FilePath -> Run (FS + LOG + EXCEPT String + r) Config
loaded file = Config.load file >>= either refused pure
  where
  refused errors = do
    for_ errors (Log.error <<< printConfigError file)
    throw (fmt @"`{file}` was refused" { file })
