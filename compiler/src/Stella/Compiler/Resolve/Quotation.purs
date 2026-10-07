-- | A quotation resolved into the expression building the syntax it quotes
-- | ([Syntax Extensions and Parsers](../../../../docs/proposals/09-Syntax-Extensions-and-Parsers.md)).
-- |
-- | **A quotation is the `Stella.Syntax.Syntax Stella.Syntax.Term` its tokens
-- | are**, written as an application of `Stella.Syntax`'s constructors: each
-- | token as it is written, its kind, its text, and the trivia before it; each
-- | bracket and what it holds a group; each block the layout opened a layout
-- | group, its items as the layout separated them. The braces of the quotation
-- | are none of it. Nothing quoted is resolved: a name in it is resolved where
-- | the syntax is read.
-- |
-- | **An antiquotation is resolved where it stands**, and what it splices in
-- | stands in parentheses, so that it is one operand whatever it holds.
-- |
-- | **Every token and node carries the origin of a quotation**: this module,
-- | and the range in its source it was written at, for diagnostics alone. Its
-- | constructor and the splicing are `Stella.Syntax`'s elaboration-only
-- | entries, which no source names.
module Stella.Compiler.Resolve.Quotation
  ( quotation
  ) where

import Prelude
import Prim hiding (Type)

import Data.Array as Array
import Data.List (List(..), (:))
import Data.List as List
import Data.Maybe (Maybe(..))
import Data.Traversable (traverse)
import Stella.Compiler.CST.Types (Expr, QuotePart(..), Quotation, SourceRange, SourceToken, Token(..)) as CST
import Stella.Compiler.Macro.Bundle (syntaxModuleName)
import Stella.Compiler.Macro.Tree (Delimiter(..), Position(..), Range(..), TokenKind(..), Trivia(..), kindOf, opening, textOf, triviaOf)
import Stella.Compiler.Macro.Tree (rangeOf) as Tree
import Stella.Compiler.Surface.Expr (Expr(..))
import Stella.Compiler.Surface.Origin (Origin, originOf, rangeOf)
import Stella.Compiler.Surface.Type (Type(..))
import Stella.Compiler.TypedCore.Domain (scalarString)
import Stella.Compiler.TypedCore.Name (Ident(..), ModuleName(..), Qualified(..), TyName(..))
import Stella.Compiler.TypedCore.Term (Literal(..))

-- | What a quotation holds, its antiquotations resolved: a token as written, or
-- | an expression spliced in where an antiquotation stands.
data Item
  = Quoted CST.SourceToken
  | Spliced { range :: CST.SourceRange, leading :: Array Trivia, expr :: Expr }

-- | The expression a quotation written in the module given builds, its
-- | antiquotations resolved by the function given.
quotation :: forall m. Monad m => ModuleName -> (CST.Expr -> m Expr) -> Origin -> CST.Quotation -> m Expr
quotation self resolve o q = do
  items <- Array.concat <$> traverse item q.parts
  let built = sequenceOf (List.fromFoldable items)
  pure (ExprTyped o (ctor "Syntax" [ list built.nodes ]) syntaxTerm)
  where
  item = case _ of
    CST.QuotedTokens ts -> pure (map Quoted ts)
    CST.QuotedAntiquote a -> resolve a.expr <#> \e ->
      [ Spliced { range: a.range, leading: map triviaOf a.leading, expr: e } ]

  -- the nodes up to a closing bracket, a separator, or the end of a block,
  -- which is left for what encloses them
  sequenceOf :: List Item -> { nodes :: Array Expr, rest :: List Item }
  sequenceOf = go []
    where
    go acc items = case items of
      Nil -> { nodes: acc, rest: Nil }
      Spliced s : rest -> go (Array.snoc acc (spliced s)) rest
      Quoted t : rest
        | ends t.value -> { nodes: acc, rest: items }
        | Just d <- opening t.value ->
            let
              inner = sequenceOf rest
              closed = closers d inner.rest
            in
              go (Array.snoc acc (group t d inner.nodes closed.tokens)) closed.rest
        | CST.TokLayoutStart _ <- t.value ->
            let
              block = itemsOf t rest
            in
              go (Array.snoc acc (ctor "SyntaxLayout" [ origin t.range, list block.items ])) block.rest
        | otherwise -> go (Array.snoc acc (ctor "SyntaxToken" [ token t ])) rest

  -- the items of a block opened by the token given, each beginning where the
  -- layout separated it from the one before
  itemsOf :: CST.SourceToken -> List Item -> { items :: Array Expr, rest :: List Item }
  itemsOf start = go [] start
    where
    go acc at items =
      let
        one = sequenceOf items
        acc' = Array.snoc acc (ctor "SyntaxItem" [ origin (firstRange at one.rest items), list one.nodes ])
      in
        case one.rest of
          Quoted t : rest | CST.TokLayoutSep _ <- t.value -> go acc' t rest
          Quoted t : rest | CST.TokLayoutEnd _ <- t.value -> { items: acc', rest }
          rest -> { items: acc', rest }

  -- where an item stands: its first token, or the token beginning it where it
  -- holds none
  firstRange at _ items = case items of
    Quoted t : _ | not (ends t.value) -> t.range
    Spliced s : _ -> s.range
    _ -> at.range

  -- the tokens closing a group: two `}` for `{{`, one token otherwise
  closers d items = case d, items of
    Synthesized, Quoted a : Quoted b : rest -> { tokens: [ token a, token b ], rest }
    _, Quoted a : rest -> { tokens: [ token a ], rest }
    _, rest -> { tokens: [], rest }

  group open d inner closes =
    ctor "SyntaxGroup" [ origin open.range, delimiter d, token open, list inner, list closes ]

  -- what an antiquotation splices in is syntax of a term, as the place it
  -- stands in is
  spliced s = ap (value "$spliced") [ origin s.range, list (map trivia s.leading), ExprTyped o s.expr syntaxTerm ]

  token t = ctor "Token"
    [ kind (kindOf t.value), string (textOf t.value), rangeExpr (Tree.rangeOf t.range), list (map (trivia <<< triviaOf) t.leading), origin t.range ]

  -- the origin of a quotation: this module, and where in its source the range
  -- given stands
  origin r =
    let
      at = rangeOf (originOf r)
    in
      ctor "$QuotedOrigin" [ string (moduleText self), position at.start.line at.start.column, position at.end.line at.end.column ]

  ends = case _ of
    CST.TokRightParen -> true
    CST.TokRightSquare -> true
    CST.TokRightBrace -> true
    CST.TokRightBar -> true
    CST.TokLayoutSep _ -> true
    CST.TokLayoutEnd _ -> true
    _ -> false

  -- the expressions of `Stella.Syntax`'s values
  ap = Array.foldl (ExprApp o)
  ctor n args = ap (ExprConstructor o (syntaxName n)) args
  value n = ExprValue o (syntaxName n)
  list = Array.foldr (\x rest -> ctor "Cons" [ x, rest ]) (ctor "Nil" [])
  literal = ExprLiteral o
  int n = literal (LitInt n)
  -- the text of a token of the source, which is always a sequence of scalar
  -- values
  string s = case scalarString s of
    Just text -> literal (LitString text)
    Nothing -> ExprInvalid o
  maybeString = case _ of
    Just s -> ctor "Just" [ string s ]
    Nothing -> ctor "Nothing" []
  position line column = ctor "Position" [ int line, int column ]
  rangeExpr (Range (Position l1 c1) (Position l2 c2)) = ctor "Range" [ position l1 c1, position l2 c2 ]

  trivia = case _ of
    Spaces s r -> ctor "Spaces" [ string s, rangeExpr r ]
    Newline s r -> ctor "Newline" [ string s, rangeExpr r ]
    LineComment s r -> ctor "LineComment" [ string s, rangeExpr r ]
    BlockComment s r -> ctor "BlockComment" [ string s, rangeExpr r ]

  delimiter = case _ of
    Paren -> ctor "Paren" []
    Bracket -> ctor "Bracket" []
    Brace -> ctor "Brace" []
    EffectRow -> ctor "EffectRow" []
    Synthesized -> ctor "Synthesized" []
    AttributeBracket -> ctor "AttributeBracket" []
    LocalOpen m -> ctor "LocalOpen" [ string m ]

  kind = case _ of
    GroupBracket -> ctor "GroupBracket" []
    Comma -> ctor "Comma" []
    Backslash -> ctor "Backslash" []
    Underscore -> ctor "Underscore" []
    LowerName qualifier n -> ctor "LowerName" [ maybeString qualifier, string n ]
    UpperName qualifier n -> ctor "UpperName" [ maybeString qualifier, string n ]
    DiscriminatorName qualifier n -> ctor "DiscriminatorName" [ maybeString qualifier, string n ]
    OperatorName qualifier n -> ctor "OperatorName" [ maybeString qualifier, string n ]
    OperatorValue qualifier n -> ctor "OperatorValue" [ maybeString qualifier, string n ]
    InfixName qualifier n -> ctor "InfixName" [ maybeString qualifier, string n ]
    HoleName n -> ctor "HoleName" [ string n ]
    TagName n -> ctor "TagName" [ string n ]
    DirectiveName n -> ctor "DirectiveName" [ string n ]
    MacroName qualifier n -> ctor "MacroName" [ maybeString qualifier, string n ]
    IntLiteral n -> ctor "IntLiteral" [ int n ]
    NumberLiteral n -> ctor "NumberLiteral" [ literal (LitNumber n) ]
    CharLiteral s -> ctor "CharLiteral" [ string s ]
    StringLiteral s -> ctor "StringLiteral" [ string s ]

  syntaxTerm = TypeApp o (TypeConstructor o (Qualified syntaxModuleName (TyName "Syntax"))) (TypeConstructor o (Qualified syntaxModuleName (TyName "Term")))

syntaxName :: String -> Qualified Ident
syntaxName = Qualified syntaxModuleName <<< Ident

moduleText :: ModuleName -> String
moduleText (ModuleName m) = m
