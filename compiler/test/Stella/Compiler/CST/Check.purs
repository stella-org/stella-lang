-- | The checks on what the grammar reads widely, each reported where it fails.
module Test.Stella.Compiler.CST.Check (spec) where

import Prelude

import Data.Either (Either(..))
import Data.String (joinWith)
import Effect.Aff (Aff)
import Stella.Compiler.CST (parseModule, printSyntaxError)
import Stella.Compiler.CST.Check (CheckError(..), CheckReason(..), checkModule)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

-- | The reasons a module whose body is the lines given fails, each with the
-- | line and column it is reported at.
reports :: Array String -> Array { line :: Int, column :: Int, reason :: CheckReason } -> Aff Unit
reports body expected = case parseModule (joinWith "\n" ([ "module M where" ] <> body)) of
  Left e -> fail (printSyntaxError e)
  Right m -> map found (checkModule m) `shouldEqual` expected
  where
  found (CheckError r reason) = { line: r.start.line, column: r.start.column, reason }

spec :: Spec Unit
spec = describe "Stella.Compiler.CST.Check" do
  describe "the operation arrow" do
    it "admits one `->*` on the spine, under quantifiers and redundant parentheses, resuming with any type" do
      [ "effect E where"
      , "  writeAt :: Int -> String ->* Unit"
      , "  abort :: forall b. Unit ->* b"
      , "  op :: A ->* B -> C"
      , "  op2 :: A -> (B ->* C)"
      , "  op3 :: (A -> B ->* C)"
      ] `reports` []

    it "reports a second `->*` where it stands" do
      [ "effect E where", "  op :: A ->* B ->* C" ] `reports`
        [ { line: 3, column: 17, reason: OperationArrowMisplaced } ]

    it "reports `->*` inside an argument" do
      [ "effect E where", "  op :: (A ->* B) -> C" ] `reports`
        [ { line: 3, column: 12, reason: OperationArrowMisplaced } ]

    it "reports an operation with no `->*` at the operation" do
      [ "effect E where", "  op :: A -> B" ] `reports`
        [ { line: 3, column: 3, reason: OperationArrowMissing } ]

    it "reports an operation signature written through a type synonym, at both ends" do
      [ "type GetSignature s = Unit ->* s"
      , "effect State s where"
      , "  get :: GetSignature s"
      ] `reports`
        [ { line: 2, column: 28, reason: OperationArrowOutsideOperation }
        , { line: 4, column: 3, reason: OperationArrowMissing }
        ]

    it "reports `->*` outside an operation's signature, wherever the type stands" do
      [ "f :: Int ->* Int"
      , "g = (x :: A ->* B)"
      , "data T = T (A ->* B)"
      , "h = let y :: A ->* B"
      , "        y = 1 in y"
      ] `reports`
        [ { line: 2, column: 10, reason: OperationArrowOutsideOperation }
        , { line: 3, column: 13, reason: OperationArrowOutsideOperation }
        , { line: 4, column: 15, reason: OperationArrowOutsideOperation }
        , { line: 5, column: 16, reason: OperationArrowOutsideOperation }
        ]
