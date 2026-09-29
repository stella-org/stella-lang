module Stellac.Build where

import Prelude

import Effect.Class.Console as Console
import Run (EFFECT, Run, AFF)
import Stella.CLI.Effect.FS (FS)
import Stellac.Options (BuildOptions)
import Type.Row (type (+))

cmd :: forall r. BuildOptions -> Run (FS + EFFECT + AFF + r) Unit
cmd opts = do
  Console.logShow opts