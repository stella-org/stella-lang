-- | Source text in, concrete syntax tree out.
-- |
-- | Three passes: the lexer turns text into tokens, the offside rule inserts
-- | the block tokens indentation calls for, and the generated parser builds
-- | the tree.
module Stella.Compiler.CST
  ( SyntaxError(..)
  , parseModule
  , parseType
  , parseExpr
  , printSyntaxError
  ) where

import Prelude
import Prim hiding (Type)

import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.String (joinWith)
import Puppy.Runtime (ParseError)
import Stella.Compiler.CST.Layout (insertLayout)
import Stella.Compiler.CST.Lexer (LexError(..), lex, printLexErrorReason)
import Stella.Compiler.CST.Parser as P
import Stella.Compiler.CST.Types (Expr, Module, SourcePos, SourceToken, Type, printToken)

data SyntaxError
  = LexFailure LexError
  -- | The token the parser could not use, or `Nothing` at the end of the
  -- | input, and the tokens it could have used there.
  | ParseFailure SourcePos (Maybe SourceToken) (Array String)

derive instance Eq SyntaxError

instance Show SyntaxError where
  show = printSyntaxError

-- | How many tokens a message lists as expected. Beyond that the list says less
-- | than the token found does, and is left out.
listedExpected :: Int
listedExpected = 8

printSyntaxError :: SyntaxError -> String
printSyntaxError = case _ of
  LexFailure (LexError pos reason) -> at pos <> printLexErrorReason reason
  ParseFailure pos found expected ->
    at pos <> "unexpected " <> maybe "end of input" (\t -> printToken t.value) found
      <>
        if Array.null expected || Array.length expected > listedExpected then ""
        else "; expected " <> joinWith ", " expected
  where
  at pos = show pos.line <> ":" <> show pos.column <> ": "
  maybe d f = case _ of
    Nothing -> d
    Just x -> f x

parseModule :: String -> Either SyntaxError Module
parseModule = run P.parseModule

parseType :: String -> Either SyntaxError Type
parseType = run P.parseType

parseExpr :: String -> Either SyntaxError Expr
parseExpr = run P.parseExpr

run
  :: forall a
   . (Array SourceToken -> Either (ParseError SourceToken) a)
  -> String
  -> Either SyntaxError a
run parser src = case lex src of
  Left e -> Left (LexFailure e)
  Right toks ->
    let
      laidOut = insertLayout toks
    in
      case parser laidOut of
        Right a -> Right a
        Left e -> Left (ParseFailure (positionOf laidOut e) e.found e.expected)

-- | Where a parse stopped: at the token it could not use, or just after the
-- | last token at the end of the input.
positionOf :: Array SourceToken -> ParseError SourceToken -> SourcePos
positionOf toks e = case e.found of
  Just tok -> tok.range.start
  Nothing -> case Array.last toks of
    Just tok -> tok.range.end
    Nothing -> { line: 1, column: 1 }
