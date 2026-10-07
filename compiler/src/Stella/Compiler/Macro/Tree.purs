-- | What a macro reads and what it produces, as the host holds them
-- | ([Syntax Extensions and Parsers](../../../../docs/proposals/09-Syntax-Extensions-and-Parsers.md)).
-- |
-- | **A macro reads a token tree**: the tokens of its call, nested by
-- | delimiter, each with its kind, its text as written, its range, the trivia
-- | before it, and an origin. **It produces syntax**: tokens, groups, and
-- | layout groups, each carrying an origin. These types mirror those of the
-- | guest module `Stella.Syntax` constructor for constructor, which is how a
-- | value crosses to a parser running as guest code and back.
-- |
-- | **An origin says where a token or a node came from, for diagnostics
-- | alone**: nothing resolves a name, or decides what a program means, by it.
-- | A token of the call's input carries a reference the host issued, which a
-- | parser cannot make, and which stands for a range the host's table keys by
-- | the reference. A token of a quotation carries the module and the range its
-- | origin declares — where a quotation compiled from source stands, which the
-- | compiler writes — and the host checks the module is one the macro's
-- | reaches and the range a range, and no more.
module Stella.Compiler.Macro.Tree
  ( OriginRef(..)
  , IssuedOrigin(..)
  , Position(..)
  , Range(..)
  , Trivia(..)
  , TokenKind(..)
  , Token(..)
  , Delimiter(..)
  , TokenTree(..)
  , SyntaxNode(..)
  , SyntaxItem(..)
  , Syntax(..)
  , Term
  , Failure(..)
  , Result(..)
  , Origins
  , treeOf
  , opening
  , kindOf
  , textOf
  , rangeOf
  , triviaOf
  ) where

import Prelude

import Data.Array as Array
import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Show.Generic (genericShow)
import Data.Tuple (Tuple(..))
import Data.List (List(..))
import Data.List as List
import Stella.Compiler.CST.Types (SourcePos, SourceRange, SourceToken, Token(..), printToken) as CST
import Stella.Compiler.CST.Types (Trivia(..)) as CSTTrivia

-- | Where a token or a node came from: a token of the call's input, by the
-- | reference the host issued for it, or a quotation, by the module and the
-- | range it declares. `QuotedOrigin` is `Stella.Syntax.$QuotedOrigin`.
data OriginRef
  = InputOrigin IssuedOrigin
  | QuotedOrigin String Position Position

-- | A reference the host issued for a token of a call's input, which stands
-- | for the token's range in the host's table.
newtype IssuedOrigin = IssuedOrigin Int

data Position = Position Int Int

data Range = Range Position Position

data Trivia
  = Spaces String Range
  | Newline String Range
  | LineComment String Range
  | BlockComment String Range

-- | What a token is, as the lexer told it apart. A keyword is a lower name, a
-- | syntax in scope being what makes it one. A name or an operator carries its
-- | qualifier where it has one. A bracket opening or closing a group is a
-- | `GroupBracket`, the group saying which delimiter it is.
data TokenKind
  = GroupBracket
  | Comma
  | Backslash
  | Underscore
  | LowerName (Maybe String) String
  | UpperName (Maybe String) String
  | DiscriminatorName (Maybe String) String
  | OperatorName (Maybe String) String
  | OperatorValue (Maybe String) String
  | InfixName (Maybe String) String
  | HoleName String
  | TagName String
  | DirectiveName String
  | MacroName (Maybe String) String
  | IntLiteral Int
  | NumberLiteral Number
  | CharLiteral String
  | StringLiteral String

-- | A token: what it is, its text as written, where it stands, the trivia
-- | before it, and where it came from.
data Token = Token TokenKind String Range (Array Trivia) OriginRef

-- | What a group is opened by. `{{` is closed by two tokens, every other by one.
data Delimiter
  = Paren
  | Bracket
  | Brace
  | EffectRow
  | Synthesized
  | AttributeBracket
  | LocalOpen String

-- | A token, or a group: its delimiter, the opening token, what it holds, and
-- | the closing tokens.
data TokenTree
  = Leaf Token
  | Group Delimiter Token (Array TokenTree) (Array Token)

-- | Syntax a parser produces: a token, a group, or a layout group — a block
-- | whose items the host separates and encloses as its own layout does. A
-- | group and a layout group carry an origin of their own, which places them
-- | where they have no token to stand at.
data SyntaxNode
  = SyntaxToken Token
  | SyntaxGroup OriginRef Delimiter Token (Array SyntaxNode) (Array Token)
  | SyntaxLayout OriginRef (Array SyntaxItem)

-- | An item of a layout group, with the origin of where it begins.
data SyntaxItem = SyntaxItem OriginRef (Array SyntaxNode)

-- | Syntax of the category `c`, which is no more than a type tells.
data Syntax :: Type -> Type
data Syntax c = Syntax (Array SyntaxNode)

-- | The category of expressions.
data Term

-- | Why a parser failed: the farthest position it reached, what it expected
-- | there, and the labels of the contexts it was in. A parser may name one
-- | expectation more than once, and the host takes them as a set.
data Failure = Failure Position (Array String) (Array String)

-- | How a parser came out.
data Result a
  = Parsed a
  | Failed Failure

-- | What each origin a host issued stands for.
type Origins = Map Int CST.SourceRange

-- | The token tree of a macro call's body, the brackets included, with an
-- | origin issued for each token, numbered from the number given. The body is
-- | well bracketed, the grammar having read it as one bracket or one string.
treeOf :: Int -> Array CST.SourceToken -> { trees :: Array TokenTree, origins :: Origins, next :: Int }
treeOf first body =
  { trees: (items (List.fromFoldable numbered)).trees
  , origins: Map.fromFoldable (map (\n -> Tuple n.number n.token.range) numbered)
  , next: first + Array.length body
  }
  where
  numbered = Array.mapWithIndex (\i token -> { number: first + i, token }) body

  -- The trees up to a closing token or the end, and what follows them.
  items :: List Numbered -> { trees :: Array TokenTree, rest :: List Numbered }
  items = go []
    where
    go acc = case _ of
      Cons n rest
        | closing n.token.value -> { trees: acc, rest: Cons n rest }
        | Just delimiter <- opening n.token.value ->
            let
              inner = items rest
              closed = closes delimiter inner.rest
            in
              go (Array.snoc acc (Group delimiter (tokenOf n) inner.trees closed.tokens)) closed.rest
        | otherwise -> go (Array.snoc acc (Leaf (tokenOf n))) rest
      Nil -> { trees: acc, rest: Nil }

  -- `{{` is closed by two `}`, every other delimiter by one token.
  closes delimiter = case delimiter, _ of
    Synthesized, Cons a (Cons b rest) -> { tokens: [ tokenOf a, tokenOf b ], rest }
    _, Cons a rest -> { tokens: [ tokenOf a ], rest }
    _, Nil -> { tokens: [], rest: Nil }

type Numbered = { number :: Int, token :: CST.SourceToken }

tokenOf :: Numbered -> Token
tokenOf n = Token (kindOf n.token.value) (textOf n.token.value) (rangeOf n.token.range) (map triviaOf n.token.leading) (InputOrigin (IssuedOrigin n.number))

-- | The delimiter a token opens a group of, where it opens one.
opening :: CST.Token -> Maybe Delimiter
opening = case _ of
  CST.TokLeftParen -> Just Paren
  CST.TokLeftSquare -> Just Bracket
  CST.TokLeftBrace -> Just Brace
  CST.TokLeftBar -> Just EffectRow
  CST.TokLeftSynth -> Just Synthesized
  CST.TokLeftAttribute -> Just AttributeBracket
  CST.TokLocalOpen m -> Just (LocalOpen m)
  _ -> Nothing

closing :: CST.Token -> Boolean
closing = case _ of
  CST.TokRightParen -> true
  CST.TokRightSquare -> true
  CST.TokRightBrace -> true
  CST.TokRightBar -> true
  _ -> false

-- | What a token is. A bracket opens or closes a group; no token layout
-- | inserts stands in a macro's body.
kindOf :: CST.Token -> TokenKind
kindOf = case _ of
  CST.TokComma -> Comma
  CST.TokBackslash -> Backslash
  CST.TokUnderscore -> Underscore
  CST.TokLowerName q n -> LowerName q n
  CST.TokUpperName q n -> UpperName q n
  CST.TokDiscriminator q n -> DiscriminatorName q n
  CST.TokOperator q n -> OperatorName q n
  CST.TokOperatorValue q n -> OperatorValue q n
  CST.TokInfixName q n -> InfixName q n
  CST.TokHole n -> HoleName n
  CST.TokTag n -> TagName n
  CST.TokDirective n _ -> DirectiveName n
  CST.TokMacro q n -> MacroName q n
  CST.TokInt _ n -> IntLiteral n
  CST.TokNumber _ n -> NumberLiteral n
  CST.TokChar _ v -> CharLiteral v
  CST.TokString _ _ v -> StringLiteral v
  _ -> GroupBracket

-- | A token's text as written.
textOf :: CST.Token -> String
textOf = CST.printToken

rangeOf :: CST.SourceRange -> Range
rangeOf r = Range (position r.start) (position r.end)

position :: CST.SourcePos -> Position
position p = Position p.line p.column

triviaOf :: CSTTrivia.Trivia -> Trivia
triviaOf = case _ of
  CSTTrivia.Spaces s r -> Spaces s (rangeOf r)
  CSTTrivia.Newline s r -> Newline s (rangeOf r)
  CSTTrivia.LineComment s r -> LineComment s (rangeOf r)
  CSTTrivia.BlockComment s r -> BlockComment s (rangeOf r)

derive instance Eq IssuedOrigin
derive instance Ord IssuedOrigin
derive instance Generic IssuedOrigin _
instance Show IssuedOrigin where
  show = genericShow

derive instance Eq OriginRef
derive instance Ord OriginRef
derive instance Generic OriginRef _
instance Show OriginRef where
  show = genericShow

derive instance Eq Position
derive instance Ord Position
derive instance Generic Position _
instance Show Position where
  show = genericShow

derive instance Eq Range
derive instance Generic Range _
instance Show Range where
  show = genericShow

derive instance Eq Trivia
derive instance Generic Trivia _
instance Show Trivia where
  show = genericShow

derive instance Eq TokenKind
derive instance Generic TokenKind _
instance Show TokenKind where
  show = genericShow

derive instance Eq Token
derive instance Generic Token _
instance Show Token where
  show = genericShow

derive instance Eq Delimiter
derive instance Generic Delimiter _
instance Show Delimiter where
  show = genericShow

derive instance Eq TokenTree
derive instance Generic TokenTree _
instance Show TokenTree where
  show x = genericShow x

derive instance Eq SyntaxNode
derive instance Generic SyntaxNode _
instance Show SyntaxNode where
  show x = genericShow x

derive instance Eq (Syntax c)
derive instance Generic (Syntax c) _
instance Show (Syntax c) where
  show x = genericShow x

derive instance Eq Failure
derive instance Generic Failure _
instance Show Failure where
  show = genericShow

derive instance Eq a => Eq (Result a)
derive instance Generic (Result a) _
instance Show a => Show (Result a) where
  show = genericShow

derive instance Eq SyntaxItem
derive instance Generic SyntaxItem _
instance Show SyntaxItem where
  show x = genericShow x
