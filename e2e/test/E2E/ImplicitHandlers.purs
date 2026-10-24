-- | Modules written in source whose checking boundaries are met by implicit
-- | handlers the elaborator inserts, compiled and loaded, and each value read
-- | as the machine holds it once the module is initialized: the front end's
-- | insertion, run.
-- |
-- | `Lowering` declares `logAsTick`, a message logged a tick, and
-- | `verboseAsLog`, a thing said two messages logged; `Main` imports the
-- | effects alone by name. `logged` performs `Log` under a signature at
-- | `Tick`, and `chained` performs `Verbose`, which `verboseAsLog` lowers inside
-- | `logAsTick`. `quietly` performs `Quiet` under a signature at `()`, met by
-- | `silence`, which `Main` declares after it, and `quietId`, an η-expansion of
-- | `loudId`, performs it under the expansion's λ.
module Test.E2E.ImplicitHandlers (spec) where

import Prelude

import Prim as P

import Data.Map as Map
import Data.Tuple (Tuple(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import E2E.Build (Sources)
import Test.E2E.Running (running)

spec :: Sources -> Spec Unit
spec sources = describe "Stella source whose boundaries implicit handlers meet, run on Steam" do
  it "inserts an imported handler the header's import list does not name, each message logged a tick" do
    running sources [ "implicit-handlers" ] [ "counted" ] \values ->
      values `shouldEqual` Map.fromFoldable [ Tuple "counted" "12" ]

  it "inserts a chain of two, the inner one's targets handled by the outer one" do
    running sources [ "implicit-handlers" ] [ "lowered" ] \values ->
      values `shouldEqual` Map.fromFoldable [ Tuple "lowered" "14" ]

  it "inserts a handler the module declares after the boundary it meets" do
    running sources [ "implicit-handlers" ] [ "hushed" ] \values ->
      values `shouldEqual` Map.fromFoldable [ Tuple "hushed" "8" ]

  it "inserts a handler under the λ an η-expansion makes" do
    running sources [ "implicit-handlers" ] [ "echoed" ] \values ->
      values `shouldEqual` Map.fromFoldable [ Tuple "echoed" "5" ]
