-- | The range a node of the concrete syntax tree covers, and the origin a node
-- | of the Surface AST built from two others takes.
module Test.Stella.Compiler.CST.Range (spec) where

import Prelude
import Prim hiding (Type)

import Data.Either (Either(..))
import Effect.Aff (Aff)
import Stella.Compiler.Surface.Origin (Origin(..), spanning)
import Stella.Compiler.CST (parseExpr, parseType, printSyntaxError)
import Stella.Compiler.CST.Range (binderRange, covering, exprRange, typeRange)
import Stella.Compiler.CST.Types (Binder, Expr(..), SourceRange)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

-- | A range on one line, from the first column to the one just after the last.
on :: Int -> Int -> Int -> SourceRange
on line from to = { start: { line, column: from }, end: { line, column: to } }

expr :: String -> (Expr -> Aff Unit) -> Aff Unit
expr src k = case parseExpr src of
  Left e -> fail (printSyntaxError e)
  Right e -> k e

expectExpr :: String -> SourceRange -> Aff Unit
expectExpr src r = expr src \e -> exprRange e `shouldEqual` r

expectType :: String -> SourceRange -> Aff Unit
expectType src r = case parseType src of
  Left e -> fail (printSyntaxError e)
  Right t -> typeRange t `shouldEqual` r

-- | The pattern a lambda binds first, `\p -> …`.
lambdaBinder :: String -> (Binder -> Aff Unit) -> Aff Unit
lambdaBinder src k = expr src case _ of
  ExprLambda [ b ] _ -> k b
  e -> fail ("not a lambda of one pattern: " <> show e)

spec :: Spec Unit
spec = describe "CST.Range" do
  describe "covering" do
    it "spans from the earlier start to the later end, in either order" do
      covering (on 1 1 3) (on 2 4 6) `shouldEqual` { start: { line: 1, column: 1 }, end: { line: 2, column: 6 } }
      covering (on 2 4 6) (on 1 1 3) `shouldEqual` { start: { line: 1, column: 1 }, end: { line: 2, column: 6 } }

    it "keeps a range that holds the other" do
      covering (on 1 1 9) (on 1 3 5) `shouldEqual` on 1 1 9

    it "orders columns within a line and lines before columns" do
      covering (on 1 5 7) (on 1 2 3) `shouldEqual` on 1 2 7
      covering (on 2 1 2) (on 1 9 10) `shouldEqual` { start: { line: 1, column: 9 }, end: { line: 2, column: 2 } }

  describe "spanning" do
    it "covers the ranges of both origins" do
      spanning (FromSource (on 1 5 7)) (FromSource (on 1 1 2)) `shouldEqual` FromSource (on 1 1 7)

  describe "exprRange" do
    it "is a leaf's own range" do
      expectExpr "foo" (on 1 1 4)
      expectExpr "\"ab\"" (on 1 1 5)

    it "covers an application from its head to its last argument" do
      expectExpr "f x  yy" (on 1 1 8)

    it "takes the operator in, where it stands between its operands" do
      expectExpr "a + b" (on 1 1 6)

    it "reaches across lines" do
      expectExpr "f\n  x" { start: { line: 1, column: 1 }, end: { line: 2, column: 4 } }

    it "does not reach a keyword or a parenthesis" do
      expectExpr "\\x -> y" (on 1 2 8)
      expectExpr "(f x)" (on 1 2 5)

    it "covers a record with its braces, empty or not" do
      expectExpr "{ a: 1, b }" (on 1 1 12)
      expectExpr "{}" (on 1 1 3)

    it "reaches the braces of a record that stands last" do
      expectExpr "f x {}" (on 1 1 7)

    it "covers `()` with both its parentheses, which group nothing" do
      expectExpr "f ()" (on 1 1 5)
      expectType "Unit -> ()" (on 1 1 11)

  describe "typeRange" do
    it "covers an effectful arrow from its argument to its row" do
      expectType "Int -> Unit / e" (on 1 1 16)

    it "covers a row with its brackets, empty or not" do
      expectType "{||}" (on 1 1 5)
      expectType "{| Console |}" (on 1 1 14)
      expectType "[]" (on 1 1 3)
      expectType "{}" (on 1 1 3)

  describe "binderRange" do
    it "covers a constructor pattern and its fields" do
      lambdaBinder "\\(Just x) -> x" \b -> binderRange b `shouldEqual` on 1 3 9

    it "covers a record pattern with its braces, empty or not" do
      lambdaBinder "\\{ a, ...r } -> a" \b -> binderRange b `shouldEqual` on 1 2 13
      lambdaBinder "\\{} -> 0" \b -> binderRange b `shouldEqual` on 1 2 4
