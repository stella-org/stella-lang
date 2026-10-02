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

  describe "computation types" do
    it "admits one at the top of a top-level signature, under quantifiers, constraints, and parentheses" do
      [ "x :: Int / {| Random |}"
      , "y :: forall a. a / {| Random |}"
      , "z :: forall a. Show a => a / {| Random |}"
      , "w :: (Int -> Int) / {| Random |}"
      , "p :: (Int / {| Random |})"
      , "q :: forall a. ((a / {| Random |}))"
      ] `reports` []

    it "admits `/` on the arrow it follows" do
      [ "f :: Int -> String / {| Console |}"
      , "handler h :: forall a. (Unit -> a / {| E |}) -> a where"
      , "  fast | op _ -> 0"
      ] `reports` []

    it "reports one in an argument, and in a parenthesized result" do
      [ "f :: (Int / {| E |}) -> Int"
      , "g :: Int -> (Int / {| E |})"
      ] `reports`
        [ { line: 2, column: 11, reason: ComputationTypeMisplaced }
        , { line: 3, column: 18, reason: ComputationTypeMisplaced }
        ]

    it "reports one wherever a type stands that is not a top-level signature" do
      [ "x :: { a :: Int / {| E |} }"
      , "y = (1 :: Int / {| E |})"
      , "foreign f :: Int / {| E |}"
      , "data T = T (Int / {| E |})"
      , "effect E where"
      , "  op :: Unit ->* Int / {| F |}"
      ] `reports`
        [ { line: 2, column: 17, reason: ComputationTypeMisplaced }
        , { line: 3, column: 15, reason: ComputationTypeMisplaced }
        , { line: 4, column: 18, reason: ComputationTypeMisplaced }
        , { line: 5, column: 17, reason: ComputationTypeMisplaced }
        , { line: 7, column: 22, reason: ComputationTypeMisplaced }
        ]

  describe "directives" do
    it "admit `#observ(none)`, whatever it stands with" do
      [ "#observ(none) foreign f :: Int -> Int" ] `reports` []

    it "report one this version does not have, before a declaration and in a type" do
      [ "#inline(arity=2)"
      , "f x y = x"
      , "data P = P (#unbox Int)"
      ] `reports`
        [ { line: 2, column: 1, reason: DirectiveUnsupported }
        , { line: 4, column: 13, reason: DirectiveUnsupported }
        ]

    it "report `#observ(none)` in a type" do
      [ "data P = P (#observ(none) Int)"
      , "x :: (#observ(none) Int)"
      ] `reports`
        [ { line: 2, column: 13, reason: DirectiveInType }
        , { line: 3, column: 7, reason: DirectiveInType }
        ]

    it "report `#observ` with an argument other than `none`" do
      [ "#observ(all) foreign f :: Int -> Int"
      , "#observ foreign g :: Int -> Int"
      ] `reports`
        [ { line: 2, column: 1, reason: DirectiveArgumentsInvalid }
        , { line: 3, column: 1, reason: DirectiveArgumentsInvalid }
        ]

  describe "imports" do
    it "report `hiding` on an import with a list, an alias, or `lazy`, each on its own, where the word stands" do
      [ "import A hiding (x)"
      , "import B (y) hiding (x)"
      , "import C hiding (x) as C"
      , "import lazy D hiding (x)"
      , "import E hiding ()"
      , "import F (y) hiding ()"
      ] `reports`
        [ { line: 3, column: 14, reason: HidingNotOnPlainImport }
        , { line: 4, column: 10, reason: HidingNotOnPlainImport }
        , { line: 5, column: 15, reason: HidingNotOnPlainImport }
        , { line: 7, column: 14, reason: HidingNotOnPlainImport }
        ]

  describe "type operators" do
    it "report `/` named as a type operator, and not as a term operator" do
      [ "infixl 7 type Quotient as /"
      , "infixl 7 div as /"
      , "infixr 6 type Tuple as /\\"
      ] `reports`
        [ { line: 2, column: 27, reason: TypeOperatorReserved } ]
