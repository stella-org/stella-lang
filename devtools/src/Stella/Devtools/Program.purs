module Stella.Devtools.Program (program) where

import Prelude

import Stella.Devtools.Options (Command(..), Options)
import Stella.Devtools.BuildSeeds as BuildSeeds
import Run (AFF, EFFECT, Run)
import Run.Except (EXCEPT)
import Stella.CLI.Effect.FS (FS)
import Stella.CLI.Effect.Log (LOG)
import Stella.CLI.Effect.Process (PROCESS)
import Type.Row (type (+))

program :: Options -> Run (FS + LOG + PROCESS + EXCEPT String + EFFECT + AFF ()) Unit
program { command } = case command of
  BuildSeeds opts -> BuildSeeds.cmd opts
