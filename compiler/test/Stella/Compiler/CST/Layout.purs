-- | The offside rule, shown by writing the blocks it inserts as `{`, `;` and
-- | `}`.
module Test.Stella.Compiler.CST.Layout (spec) where

import Prelude

import Data.Either (Either(..))
import Data.String (joinWith)
import Effect.Aff (Aff)
import Stella.Compiler.CST.Layout (insertLayout)
import Stella.Compiler.CST.Lexer (lex)
import Stella.Compiler.CST.Types (Token(..), printToken)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

blocks :: String -> String
blocks src = case lex src of
  Left e -> show e
  Right lexed -> joinWith " " (map (render <<< _.value) (insertLayout lexed.tokens))
  where
  render = case _ of
    TokLayoutStart _ -> "{"
    TokLayoutSep _ -> ";"
    TokLayoutEnd _ -> "}"
    tok -> printToken tok

laysOut :: String -> String -> Aff Unit
laysOut src expected = blocks src `shouldEqual` expected

spec :: Spec Unit
spec = describe "Stella.Compiler.CST.Layout" do
  it "separates the declarations of a module" do
    "module M where\nimport A\nx = 1\ny = 2" `laysOut`
      "module M where { import A ; x = 1 ; y = 2 }"

  it "continues a declaration on an indented line" do
    "module M where\nx =\n  f 1\n    2\ny = 2" `laysOut`
      "module M where { x = f 1 2 ; y = 2 }"

  it "opens a block for `let` and closes it at `in`" do
    "module M where\nx = let a = 1 in a" `laysOut`
      "module M where { x = let { a = 1 } in a }"
    "module M where\nx =\n  let\n    a = 1\n    b = 2\n  in\n    a" `laysOut`
      "module M where { x = let { a = 1 ; b = 2 } in a }"

  it "separates case alternatives" do
    "module M where\nf = case _ of\n  Just x -> x\n  Nothing -> 0" `laysOut`
      "module M where { f = case _ of { Just x -> x ; Nothing -> 0 } }"

  it "keeps commas of a case head and of its alternatives inside the alternative" do
    "module M where\nf = case _, _ of\n  _, Just a -> a\n  a, _ -> a" `laysOut`
      "module M where { f = case _ , _ of { _ , Just a -> a ; a , _ -> a } }"

  it "opens a guard block for `where` after the patterns of an alternative" do
    "module M where\nf = case _ of\n  n where\n      m = n\n      m -> 1\n  n -> 0" `laysOut`
      "module M where { f = case _ of { n where { m = n ; m -> 1 } ; n -> 0 } }"

  it "opens a block for a declaration's `where`" do
    "module M where\nf x = g x\n  where\n  g y = y\nh = 1" `laysOut`
      "module M where { f x = g x where { g y = y } ; h = 1 }"

  it "separates handler items, a clause standing at the block's column" do
    "module M where\nhandler h :: E ~> () where\n  var n := 0\n  | return x -> x\n  | full op _ -> 1" `laysOut`
      "module M where { handler h :: E ~> ( ) where { var n := 0 ; | return x -> x ; | full op _ -> 1 } }"

  it "continues a group whose clauses are indented under its first" do
    "module M where\nx = handle w with\n  State full | get _ -> 0\n             | set _ -> 1\n  runA" `laysOut`
      "module M where { x = handle w with { State full | get _ -> 0 | set _ -> 1 ; runA } }"

  it "closes a `using` block at `handle`" do
    "module M where\nx = using runA handle w" `laysOut`
      "module M where { x = using { runA } handle w }"
    "module M where\nx =\n  using\n    runA\n    runB\n  handle\n    w" `laysOut`
      "module M where { x = using { runA ; runB } handle w }"

  it "reads a keyword as a record label" do
    "module M where\nx = { type: 1, where: 2 }.where" `laysOut`
      "module M where { x = { type : 1 , where : 2 } . where }"

  it "passes a macro's bracket through untouched" do
    "module M where\nclass%{\n  Show a where\n    show :: a -> String\n}\ny = 1" `laysOut`
      "module M where { class% { Show a where show :: a -> String } ; y = 1 }"

  it "opens blocks inside a quotation as in an expression, and closes them at its `}`" do
    "module M where\nq = %term{ let a = 1\n               b = a in b }\ny = 1" `laysOut`
      "module M where { q = %term{ let { a = 1 ; b = a } in b } ; y = 1 }"
    "module M where\nq = %term{ case x of\n  A -> 1 }\ny = 1" `laysOut`
      "module M where { q = %term{ case x of { A -> 1 } } ; y = 1 }"

  it "closes every open block at the end" do
    "module M where\nf = case x of\n  A -> let y = 1" `laysOut`
      "module M where { f = case x of { A -> let { y = 1 } } }"
