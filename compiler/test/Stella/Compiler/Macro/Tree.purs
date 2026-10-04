-- | The token tree of a macro call: nested by delimiter, every token with its
-- | kind, its text, its range, its trivia, and an origin the host issued.
module Test.Stella.Compiler.Macro.Tree (spec) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Either (Either(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Effect.Aff (Aff)
import Stella.Compiler.CST (parseExpr, printSyntaxError)
import Stella.Compiler.CST.Types (Expr(..), SourceRange, inSource)
import Stella.Compiler.Macro.Tree (Delimiter(..), OriginRef(..), Position(..), Range(..), Token(..), TokenKind(..), TokenTree(..), Trivia(..), treeOf)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

-- | The tree of the macro call the text is, its origins numbered from 0.
treeOfCall :: P.String -> ({ trees :: P.Array TokenTree, origins :: Map.Map P.Int SourceRange, next :: P.Int } -> Aff Unit) -> Aff Unit
treeOfCall src k = case parseExpr src of
  Left e -> fail (printSyntaxError e)
  Right (ExprMacro m) -> k (treeOf 0 m.body)
  Right _ -> fail "not a macro call"

-- | A tree with what is incidental dropped: its kinds and nesting.
shape :: TokenTree -> P.String
shape = case _ of
  Leaf (Token kind _ _ _ _) -> show kind
  Group d _ inner closes -> show d <> "[" <> Array.intercalate " " (map shape inner) <> "]" <> show (Array.length closes)

spec :: Spec Unit
spec = describe "Stella.Compiler.Macro.Tree" do
  it "nests the call's tokens by delimiter, its brackets included, each kind as the lexer told it" do
    treeOfCall "m%{ a, (b C) }" \r ->
      map shape r.trees `shouldEqual`
        [ "Brace[(LowerName Nothing \"a\") Comma Paren[(LowerName Nothing \"b\") (UpperName Nothing \"C\")]1]1" ]
    treeOfCall "m%{{ x } }" \r ->
      map shape r.trees `shouldEqual` [ "Synthesized[(LowerName Nothing \"x\")]2" ]
    treeOfCall "m%\"s\"" \r ->
      map shape r.trees `shouldEqual` [ "(StringLiteral \"s\")" ]

  it "keeps each token's text, range, and trivia, and issues an origin for each, standing for its range" do
    treeOfCall "m%[ x -- note\n  ]" \r -> do
      case r.trees of
        [ Group Bracket open [ Leaf x ] [ close ] ] -> do
          open `shouldEqual` Token GroupBracket "[" (Range (Position 1 3) (Position 1 4)) [] (OriginRef 0)
          x `shouldEqual` Token (LowerName Nothing "x") "x" (Range (Position 1 5) (Position 1 6)) [ Spaces " " (Range (Position 1 4) (Position 1 5)) ] (OriginRef 1)
          case close of
            Token _ text _ leading origin -> do
              text `shouldEqual` "]"
              leading `shouldEqual`
                [ Spaces " " (Range (Position 1 6) (Position 1 7))
                , LineComment "-- note" (Range (Position 1 7) (Position 1 14))
                , Newline "\n" (Range (Position 1 14) (Position 2 1))
                , Spaces "  " (Range (Position 2 1) (Position 2 3))
                ]
              origin `shouldEqual` OriginRef 2
          r.next `shouldEqual` 3
          Map.lookup 1 r.origins `shouldEqual` Just (inSource { line: 1, column: 5 } { line: 1, column: 6 })
        _ -> fail "not one bracket of one name"
