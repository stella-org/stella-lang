-- | Source text in, concrete syntax tree out.
-- |
-- | Three passes: the lexer turns text into tokens, the offside rule inserts
-- | the block tokens indentation calls for, and the generated parser builds
-- | the tree.
module Stella.Compiler.CST
  ( SyntaxError(..)
  , parseModule
  , parseHeader
  , parseType
  , parseExpr
  , printSyntaxError
  , syntaxErrorPosition
  , syntaxErrorMessage
  ) where

import Prelude
import Prim hiding (Type)

import Fmt (fmt)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.String (joinWith)
import Puppy.Runtime (ParseError)
import Stella.Compiler.CST.Layout (insertLayout)
import Stella.Compiler.CST.Lexer (Ahead, LexError(..), Lexed, lex, lexWhile, printLexErrorReason)
import Stella.Compiler.CST.Parser as P
import Stella.Compiler.CST.Types (Expr, Module, SourcePos, SourceToken, Token(..), Type, printToken)

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
printSyntaxError e = at (syntaxErrorPosition e) <> syntaxErrorMessage e
  where
  at pos = fmt @"{line}:{column}: " { line: pos.line, column: pos.column }

-- | Where a syntax error stands.
syntaxErrorPosition :: SyntaxError -> SourcePos
syntaxErrorPosition = case _ of
  LexFailure (LexError pos _) -> pos
  ParseFailure pos _ _ -> pos

-- | What a syntax error says, without where it stands.
syntaxErrorMessage :: SyntaxError -> String
syntaxErrorMessage = case _ of
  LexFailure (LexError _ reason) -> printLexErrorReason reason
  ParseFailure _ found expected ->
    fmt @"unexpected {found}{expected}"
      { found: maybe "end of input" (\t -> printToken t.value) found
      , expected:
          if Array.null expected || Array.length expected > listedExpected then ""
          else "; expected " <> joinWith ", " expected
      }
  where
  maybe d f = case _ of
    Nothing -> d
    Just x -> f x

parseModule :: String -> Either SyntaxError Module
parseModule = run P.parseModule

-- | A module's header: its name, its exports, and its imports, read without
-- | its declarations.
-- |
-- | **The text is lexed up to the first item of the module's block that is no
-- | import, and no further**: the imports come before every declaration, so
-- | what follows decides nothing of what the module imports, and nothing in it
-- | — a string or a comment left open among them — keeps the header from being
-- | read. What is lexed is laid out and parsed by the grammar a whole module is
-- | parsed by, its block closed where the text read ends.
parseHeader :: String -> Either SyntaxError Module
parseHeader src = case lexWhile Nothing headerItem src of
  Left e -> Left (LexFailure e)
  Right lexed -> parseLexed P.parseModule lexed

-- | Whether to lex the token ahead of a header: every token up to the module's
-- | block, and in it every token up to an item that is no import. The state is
-- | the column the block's items stand at, once its first item is seen.
headerItem :: Maybe Int -> Ahead -> Maybe (Maybe Int)
headerItem block ahead = case block of
  Nothing
    | ahead.previous == Just (TokLowerName Nothing "where") ->
        if ahead.startsWithWord "import" then Just (Just ahead.at.column) else Nothing
    | otherwise -> Just Nothing
  Just column
    | ahead.onNewLine && ahead.at.column <= column && not (ahead.startsWithWord "import") -> Nothing
    | otherwise -> Just block

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
  Right lexed -> parseLexed parser lexed

parseLexed
  :: forall a
   . (Array SourceToken -> Either (ParseError SourceToken) a)
  -> Lexed
  -> Either SyntaxError a
parseLexed parser lexed =
  let
    laidOut = insertLayout lexed.tokens
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
