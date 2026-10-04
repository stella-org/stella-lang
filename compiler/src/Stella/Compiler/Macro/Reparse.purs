-- | Syntax a parser returned, read back by the fixed grammar as an expression
-- | written in the text of one expansion
-- | ([Syntax Extensions and Parsers](../../../../docs/proposals/09-Syntax-Extensions-and-Parsers.md)).
-- |
-- | **What a parser returns is checked before it is read.** Every group opens
-- | and closes as its delimiter does, a bracket stands at the edge of a group and
-- | nowhere else, the tokens and their trivia, written as they are, are what the
-- | lexer reads them as, and every origin is one the host issued for the call;
-- | a parser cannot make one, and can only pass on those its input carried.
-- |
-- | **The tokens become tokens of the expansion's text.** Each stands at its
-- | place in what was produced, the `n`th covering column `n` of line 1, and
-- | the expansion records, for each, the range of the token it came from, so an
-- | origin read off any range of the expansion reaches what its tokens were
-- | written as. A layout group becomes the virtual tokens the host's own layout
-- | inserts — one opening the block, one between two items, one closing it —
-- | standing where the group and its items do.
module Stella.Compiler.Macro.Reparse
  ( Call
  , SyntaxProblem(..)
  , reparse
  ) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.String (Pattern(..), stripPrefix)
import Data.Foldable (foldMap)
import Data.List (List(..), (:))
import Data.Traversable (sequence, traverse)
import Data.Tuple (Tuple(..))
import Stella.Compiler.CST.Lexer (lex)
import Stella.Compiler.CST.Parser as P
import Stella.Compiler.CST.Types (Expr, RangeSpace(..), SourceRange, SourceToken, StringStyle(..), printToken)
import Stella.Compiler.CST.Types as CST
import Stella.Compiler.Macro.Tree (Delimiter(..), OriginRef(..), Syntax(..), SyntaxItem(..), SyntaxNode(..), Term, Token(..), TokenKind(..), Trivia(..))
import Stella.Compiler.TypedCore.Name (Ident, Qualified)

-- | The call a syntax was returned for: the expansion it is read into, the
-- | macro, the call's range in the text it stands in, and the origins the host
-- | issued for its input, each standing for the range of an input token.
type Call =
  { id :: CST.ExpansionId
  , macro :: Qualified Ident
  , call :: SourceRange
  , issued :: Map Int SourceRange
  }

-- | Why a returned syntax is not read.
data SyntaxProblem
  -- | An origin the host did not issue for the call.
  = OriginNotIssued Int
  -- | A bracket standing where no group opens or closes.
  | BracketOutsideGroup String
  -- | A group whose opening or closing tokens are not its delimiter's.
  | GroupMismatched String
  -- | Tokens that, written as they are, the lexer reads otherwise: the text of
  -- | the first, or the whole where it reads none.
  | NotAsLexed String
  -- | What the tokens are is no expression: the token the grammar could not
  -- | take, as written, where there was one, and what it expected.
  | NotAnExpression (Maybe String) (Array String)

-- | One token of the output, before it is placed: what it is, its trivia, where
-- | it came from, and its text as written, which a virtual token has none of.
type Placed = { value :: CST.Token, leading :: Array Trivia, origin :: OriginRef, text :: Maybe String }

reparse :: Call -> Syntax Term -> Either SyntaxProblem Expr
reparse call (Syntax nodes) = do
  placed <- directives <<< Array.concat <$> traverse node nodes
  written <- traverse (\p -> issuedFor p.origin) placed
  asLexed placed
  let
    space = Expansion { id: call.id, macro: call.macro, call: call.call, written }
    tokens = Array.mapWithIndex (sourceToken space) placed
  case P.parseExpr tokens of
    Right e -> Right e
    Left e -> Left (NotAnExpression (map (\t -> printToken t.value) e.found) e.expected)
  where
  issuedFor (OriginRef n) = case Map.lookup n call.issued of
    Just r -> Right r
    Nothing -> Left (OriginNotIssued n)

  node :: SyntaxNode -> Either SyntaxProblem (Array Placed)
  node = case _ of
    SyntaxToken t -> Array.singleton <$> token t
    SyntaxGroup origin d open inner closes -> do
      _ <- issuedFor origin
      o <- bracket (opening d) open
      i <- Array.concat <$> traverse node inner
      c <-
        if Array.length closes == Array.length (closing d) then sequence (Array.zipWith bracket (closing d) closes)
        else Left (GroupMismatched (show d))
      pure ([ o ] <> i <> c)
    SyntaxLayout origin items -> do
      _ <- issuedFor origin
      inside <- traverse item items
      let
        between = Array.concat (Array.mapWithIndex (\i x -> if i == 0 then x.nodes else [ virtual (CST.TokLayoutSep 0) x.origin ] <> x.nodes) inside)
      pure ([ virtual (CST.TokLayoutStart 0) origin ] <> between <> [ virtual (CST.TokLayoutEnd 0) origin ])

  item (SyntaxItem origin held) = do
    _ <- issuedFor origin
    placed <- Array.concat <$> traverse node held
    pure { origin, nodes: placed }

  virtual value origin = { value, leading: [], origin, text: Nothing }

  -- a bracket of a group is the one its delimiter opens or closes with
  bracket expected (Token kind text _ before origin) = case kind of
    GroupBracket
      | text == printToken expected -> Right { value: expected, leading: before, origin, text: Just text }
    _ -> Left (GroupMismatched text)

  token (Token kind text _ before origin) = case kind of
    GroupBracket -> Left (BracketOutsideGroup text)
    _ -> do
      value <- tokenOf kind text
      pure { value, leading: before, origin, text: Just text }

  -- **the tokens written as they are, their trivia among them, are what the
  -- lexer reads them as**: one token is read where one stands, of the kind and
  -- the text given, and with the trivia given before it. What a token is can
  -- depend on what stands around it, so each run of tokens between two virtual
  -- ones is read at once; a virtual token stands between the two it separates,
  -- and nothing is read across it.
  asLexed placed = void (traverse asLexedRun (runs placed))

  runs placed = Array.filter (not <<< Array.null) (go [] [] (Array.toUnfoldable placed))
    where
    go acc current = case _ of
      Nil -> Array.snoc acc current
      p : rest -> case p.text of
        Just text -> go acc (Array.snoc current { p, text }) rest
        Nothing -> go (Array.snoc acc current) [] rest

  asLexedRun written =
    let
      source = foldMap (\w -> foldMap triviaText w.p.leading <> w.text) written
      differing lexed = Array.find (\(Tuple t w) -> t.value /= w.p.value || map triviaOf t.leading /= map treeTrivia w.p.leading) (Array.zip lexed written)
    in
      case lex source of
        Right lexed
          | Array.null lexed.trailing
          , Array.length lexed.tokens == Array.length written ->
              case differing lexed.tokens of
                Nothing -> Right unit
                Just (Tuple _ w) -> Left (NotAsLexed w.text)
        _ -> Left (NotAsLexed source)

  triviaText = case _ of
    Spaces s _ -> s
    Newline s _ -> s
    LineComment s _ -> s
    BlockComment s _ -> s

  treeTrivia = case _ of
    Spaces s _ -> Tuple 0 s
    Newline s _ -> Tuple 1 s
    LineComment s _ -> Tuple 2 s
    BlockComment s _ -> Tuple 3 s

  triviaOf = case _ of
    CST.Spaces s _ -> Tuple 0 s
    CST.Newline s _ -> Tuple 1 s
    CST.LineComment s _ -> Tuple 2 s
    CST.BlockComment s _ -> Tuple 3 s

  -- whether a directive takes an argument list is read off what follows it,
  -- as the lexer reads it
  directives placed = Array.mapWithIndex
    ( \i p -> case p.value of
        CST.TokDirective name _ -> p { value = CST.TokDirective name (argumentsFollow (Array.index placed (i + 1))) }
        _ -> p
    )
    placed

  argumentsFollow = case _ of
    Just next | CST.TokLeftParen <- next.value -> Array.null next.leading
    _ -> false

  sourceToken :: RangeSpace -> Int -> Placed -> SourceToken
  sourceToken space i p =
    let
      range = { space, start: { line: 1, column: i + 1 }, end: { line: 1, column: i + 2 } }
    in
      { range, leading: map (triviaAt range) p.leading, value: p.value }

  triviaAt range = case _ of
    Spaces s _ -> CST.Spaces s (atStart range)
    Newline s _ -> CST.Newline s (atStart range)
    LineComment s _ -> CST.LineComment s (atStart range)
    BlockComment s _ -> CST.BlockComment s (atStart range)

  atStart range = range { end = range.start }

-- | The token a kind and a text say, a literal carrying the text it was written
-- | as.
tokenOf :: TokenKind -> String -> Either SyntaxProblem CST.Token
tokenOf kind text = case kind of
  GroupBracket -> Left (BracketOutsideGroup text)
  Comma -> Right CST.TokComma
  Backslash -> Right CST.TokBackslash
  Underscore -> Right CST.TokUnderscore
  LowerName q n -> Right (CST.TokLowerName q n)
  UpperName q n -> Right (CST.TokUpperName q n)
  DiscriminatorName q n -> Right (CST.TokDiscriminator q n)
  OperatorName q n -> Right (CST.TokOperator q n)
  OperatorValue q n -> Right (CST.TokOperatorValue q n)
  InfixName q n -> Right (CST.TokInfixName q n)
  HoleName n -> Right (CST.TokHole n)
  TagName n -> Right (CST.TokTag n)
  DirectiveName n -> Right (CST.TokDirective n false)
  MacroName q n -> Right (CST.TokMacro q n)
  IntLiteral n -> Right (CST.TokInt text n)
  NumberLiteral n -> Right (CST.TokNumber text n)
  CharLiteral v -> Right (CST.TokChar text v)
  StringLiteral v -> Right (CST.TokString (styleOf text) text v)
  where
  styleOf t = case stripPrefix (Pattern "\"\"\"") t of
    Just _ -> Block
    Nothing -> Quoted

opening :: Delimiter -> CST.Token
opening = case _ of
  Paren -> CST.TokLeftParen
  Bracket -> CST.TokLeftSquare
  Brace -> CST.TokLeftBrace
  EffectRow -> CST.TokLeftBar
  Synthesized -> CST.TokLeftSynth
  AttributeBracket -> CST.TokLeftAttribute
  LocalOpen m -> CST.TokLocalOpen m

closing :: Delimiter -> Array CST.Token
closing = case _ of
  Paren -> [ CST.TokRightParen ]
  Bracket -> [ CST.TokRightSquare ]
  Brace -> [ CST.TokRightBrace ]
  EffectRow -> [ CST.TokRightBar ]
  Synthesized -> [ CST.TokRightBrace, CST.TokRightBrace ]
  AttributeBracket -> [ CST.TokRightSquare ]
  LocalOpen _ -> [ CST.TokRightParen ]

derive instance Eq SyntaxProblem

instance Show SyntaxProblem where
  show = case _ of
    OriginNotIssued n -> "OriginNotIssued " <> show n
    BracketOutsideGroup t -> "BracketOutsideGroup " <> show t
    GroupMismatched t -> "GroupMismatched " <> show t
    NotAsLexed t -> "NotAsLexed " <> show t
    NotAnExpression found expected -> "NotAnExpression " <> show found <> " " <> show expected
