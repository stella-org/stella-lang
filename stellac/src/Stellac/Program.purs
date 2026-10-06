module Stellac.Program (program) where

import Prelude

import Run (AFF, EFFECT, Run)
import Run.Except (EXCEPT)
import Stella.CLI.Effect.FS (FS)
import Stella.CLI.Effect.Log (LOG)
import Stella.CLI.Effect.Process (PROCESS)
import Stellac.Build as Build
import Stellac.Options (Command(..), Options)
import Type.Row (type (+))

program :: Options -> Run (FS + LOG + PROCESS + EXCEPT String + EFFECT + AFF ()) Unit
program { command } = case command of
  Build opts -> Build.cmd opts
