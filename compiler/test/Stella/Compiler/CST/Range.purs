-- | The range a node of the concrete syntax tree covers, and the origin a node
-- | of the Surface AST built from two others takes.
module Test.Stella.Compiler.CST.Range (spec) where

import Prelude
import Prim hiding (Type)

import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Effect.Aff (Aff)
import Stella.Compiler.Surface.Origin (Origin(..), originOf, rangeOf, spanning)
import Stella.Compiler.CST (parseExpr, parseType, printSyntaxError)
import Stella.Compiler.CST.Range (binderRange, covering, exprRange, typeRange)
import Stella.Compiler.CST.Types (Binder, Expr(..), ExpansionId(..), RangeSpace(..), SourceRange, inSource)
import Stella.Compiler.TypedCore.Name (Ident(..), ModuleName(..), Qualified(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

-- | A range on one line, from the first column to the one just after the last.
on :: Int -> Int -> Int -> SourceRange
on line from to = inSource { line, column: from } { line, column: to }

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

-- | An expansion of `A.m`, called at line 9 on the input `a b`, which produced
-- | `a b a`; and one of `A.n`, called by the first token it produced on the
-- | second, which produced the one token it read.
expansion :: RangeSpace
expansion = Expansion
  { id: ExpansionId 0
  , macro: Qualified (ModuleName "A") (Ident "m")
  , call: on 9 5 12
  , written: [ on 9 8 9, on 9 10 11, on 9 8 9 ]
  }

inExpansion :: Int -> Int -> Int -> SourceRange
inExpansion line from to = { space: expansion, start: { line, column: from }, end: { line, column: to } }

inner :: RangeSpace
inner = Expansion
  { id: ExpansionId 1
  , macro: Qualified (ModuleName "A") (Ident "n")
  , call: inExpansion 1 1 2
  , written: [ inExpansion 1 2 3 ]
  }

spec :: Spec Unit
spec = describe "CST.Range" do
  describe "covering" do
    it "spans from the earlier start to the later end, in either order" do
      covering (on 1 1 3) (on 2 4 6) `shouldEqual` (inSource { line: 1, column: 1 } { line: 2, column: 6 })
      covering (on 2 4 6) (on 1 1 3) `shouldEqual` (inSource { line: 1, column: 1 } { line: 2, column: 6 })

    it "keeps a range that holds the other" do
      covering (on 1 1 9) (on 1 3 5) `shouldEqual` on 1 1 9

    it "joins no range of another text" do
      covering (on 1 1 3) (inExpansion 2 4 6) `shouldEqual` on 1 1 3
      covering (inExpansion 2 4 6) (on 1 1 3) `shouldEqual` inExpansion 2 4 6
      covering (inExpansion 1 1 3) (inExpansion 2 4 6) `shouldEqual` { space: expansion, start: { line: 1, column: 1 }, end: { line: 2, column: 6 } }
      -- an expansion is told by its number, whatever else it holds
      let
        numbered n = { space: Expansion { id: ExpansionId n, macro: Qualified (ModuleName "A") (Ident "m"), call: on 9 5 12, written: [] }, start: { line: 1, column: 4 }, end: { line: 1, column: 5 } }
      covering (inExpansion 1 1 2) (numbered 1) `shouldEqual` inExpansion 1 1 2
      covering (inExpansion 1 1 2) (numbered 0) `shouldEqual` inExpansion 1 1 5

    it "orders columns within a line and lines before columns" do
      covering (on 1 5 7) (on 1 2 3) `shouldEqual` on 1 2 7
      covering (on 2 1 2) (on 1 9 10) `shouldEqual` (inSource { line: 1, column: 9 } { line: 2, column: 2 })

  describe "spanning" do
    it "covers the ranges of both origins" do
      spanning (FromSource (on 1 5 7)) (FromSource (on 1 1 2)) `shouldEqual` FromSource (on 1 1 7)

    it "joins two origins of one expansion, and keeps the first of two texts" do
      spanning (originOf (inExpansion 1 5 7)) (originOf (inExpansion 1 1 2)) `shouldEqual` originOf (inExpansion 1 1 7)
      spanning (FromSource (on 1 5 7)) (originOf (inExpansion 1 1 2)) `shouldEqual` FromSource (on 1 5 7)

  describe "originOf" do
    it "reads an origin off the text a range is in, through every call to the source" do
      originOf (on 1 1 2) `shouldEqual` FromSource (on 1 1 2)
      let
        deep = { space: inner, start: { line: 1, column: 1 }, end: { line: 1, column: 2 } }
        m = Qualified (ModuleName "A") (Ident "m")
      originOf deep `shouldEqual`
        FromExpansion
          { range: deep
          , macro: Qualified (ModuleName "A") (Ident "n")
          , call: FromExpansion { range: inExpansion 1 1 2, macro: m, call: FromSource (on 9 5 12), written: FromSource (on 9 8 9) }
          , written: FromExpansion { range: inExpansion 1 2 3, macro: m, call: FromSource (on 9 5 12), written: FromSource (on 9 10 11) }
          }
      -- a diagnostic is located at the call written in source
      rangeOf (originOf deep) `shouldEqual` on 9 5 12

    it "reads what a run of an expansion's tokens was written as, or the call where it covers none" do
      let
        written r = case originOf r of
          FromExpansion e -> Just e.written
          _ -> Nothing
      written (inExpansion 1 2 3) `shouldEqual` Just (FromSource (on 9 10 11))
      written (inExpansion 1 1 3) `shouldEqual` Just (FromSource (on 9 8 11))
      written (inExpansion 1 2 2) `shouldEqual` Just (FromSource (on 9 5 12))

  describe "exprRange" do
    it "is a leaf's own range" do
      expectExpr "foo" (on 1 1 4)
      expectExpr "\"ab\"" (on 1 1 5)

    it "covers an application from its head to its last argument" do
      expectExpr "f x  yy" (on 1 1 8)

    it "takes the operator in, where it stands between its operands" do
      expectExpr "a + b" (on 1 1 6)

    it "reaches across lines" do
      expectExpr "f\n  x" (inSource { line: 1, column: 1 } { line: 2, column: 4 })

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

    it "covers a type operator from its left operand to its right" do
      expectType "f a /\\ b" (on 1 1 9)

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
