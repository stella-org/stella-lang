module Stellac.Program where

import Prelude

import Run (AFF, EFFECT, Run)
import Run.Except (EXCEPT)
import Stella.CLI.Effect.FS (FS)
import Stella.CLI.Effect.Log (LOG)
import Stellac.Build as Build
import Stellac.Options (Options, Command(..))
import Type.Row (type (+))

program :: Options -> Run (FS + LOG + EXCEPT String + EFFECT + AFF ()) Unit
program { command } = case command of
  Build opts -> Build.cmd opts