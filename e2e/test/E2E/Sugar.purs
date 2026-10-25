module Test.E2E.Sugar (spec) where

import Prelude

import Data.Map as Map
import Data.Tuple (Tuple(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import E2E.Build (Sources)
import Test.E2E.Running (running)

spec :: Sources -> Spec Unit
spec sources = describe "Stella source written with sugar, run on Steam" do
  it "tells a value built with a constructor from one built with another, the constructor imported, qualified, or declared" do
    running sources [ "sugar" ] [ "justOne", "nothingQualified", "circle", "dot" ] \values ->
      values `shouldEqual` Map.fromFoldable [ Tuple "justOne" "true", Tuple "nothingQualified" "false", Tuple "circle" "false", Tuple "dot" "true" ]

  it "applies operators by their fixities, and operator, tuple, and cell-write sections to their arguments, a section inside a section among them" do
    running sources [ "sugar" ] [ "seven", "next", "both", "nested", "paired", "summed" ] \values ->
      values `shouldEqual` Map.fromFoldable [ Tuple "seven" "7", Tuple "next" "42", Tuple "both" "42", Tuple "nested" "7", Tuple "paired" "6", Tuple "summed" "5" ]
