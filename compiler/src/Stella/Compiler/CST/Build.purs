-- | What the grammar's semantic actions build with.
-- |
-- | Every terminal of the grammar carries its whole token; these read a name,
-- | a literal, or a range out of one, and reinterpret what the grammar reads
-- | widely — atoms side by side, an expression standing where a pattern is
-- | meant — once it has been read.
module Stella.Compiler.CST.Build
  ( name
  , moduleName
  , range
  , intLiteral
  , numberLiteral
  , charLiteral
  , stringLiteral
  , binderApp
  , letBinding
  , toBinder
  , directive
  ) where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Stella.Compiler.CST.Types (Argument, Binder(..), Directive, Expr(..), LetBinding(..), Literal, Name, RecordBinder(..), RecordField(..), SourceRange, SourceToken, Token(..))

range :: SourceToken -> SourceRange
range = _.range

-- | The name a token carries. Only a token carrying one reaches here.
name :: SourceToken -> Name
name tok = case tok.value of
  TokLowerName q n -> { range: tok.range, qualifier: q, name: n }
  TokUpperName q n -> { range: tok.range, qualifier: q, name: n }
  TokDiscriminator q n -> { range: tok.range, qualifier: q, name: n }
  TokOperator q n -> { range: tok.range, qualifier: q, name: n }
  TokOperatorValue q n -> { range: tok.range, qualifier: q, name: n }
  TokInfixName q n -> { range: tok.range, qualifier: q, name: n }
  TokMacro q n -> { range: tok.range, qualifier: q, name: n }
  TokHole n -> { range: tok.range, qualifier: Nothing, name: n }
  TokTag n -> { range: tok.range, qualifier: Nothing, name: n }
  TokDirective n _ -> { range: tok.range, qualifier: Nothing, name: n }
  TokLocalOpen q -> { range: tok.range, qualifier: Nothing, name: q }
  _ -> { range: tok.range, qualifier: Nothing, name: "" }

-- | A module name, which the lexer reads as a qualified upper case name.
moduleName :: SourceToken -> Name
moduleName tok = case tok.value of
  TokUpperName (Just q) n -> { range: tok.range, qualifier: Nothing, name: q <> "." <> n }
  _ -> name tok

intLiteral :: SourceToken -> Literal Int
intLiteral tok = case tok.value of
  TokInt raw value -> { range: tok.range, raw, value }
  _ -> { range: tok.range, raw: "", value: 0 }

numberLiteral :: SourceToken -> Literal Number
numberLiteral tok = case tok.value of
  TokNumber raw value -> { range: tok.range, raw, value }
  _ -> { range: tok.range, raw: "", value: 0.0 }

charLiteral :: SourceToken -> Literal String
charLiteral tok = case tok.value of
  TokChar raw value -> { range: tok.range, raw, value }
  _ -> { range: tok.range, raw: "", value: "" }

stringLiteral :: SourceToken -> Literal String
stringLiteral tok = case tok.value of
  TokString _ raw value -> { range: tok.range, raw, value }
  _ -> { range: tok.range, raw: "", value: "" }

directive :: SourceToken -> Maybe (Array Argument) -> Directive
directive tok args = { name: name tok, args }

-- | Atoms side by side. A constructor or a tag at the head takes the rest as
-- | its arguments; anything else is kept as it was written.
binderApp :: Array Binder -> Binder
binderApp atoms = case Array.uncons atoms of
  Just { head, tail: [] } -> head
  Just { head: BinderConstructor n [], tail } -> BinderConstructor n tail
  Just { head: BinderTag n [], tail } -> BinderTag n tail
  Just { head, tail } -> BinderApp head tail
  Nothing -> BinderInvalid (ExprTuple [])

-- | The left of a `let` binding, read as a pattern and told apart here: a name
-- | followed by patterns binds a local function, a name alone a value, and
-- | anything else is a pattern binding.
letBinding :: Binder -> Expr -> LetBinding
letBinding left right = case left of
  BinderApp (BinderVar n) args -> LetValue n args right
  BinderVar n -> LetValue n [] right
  _ -> LetPattern left right

-- | The left of a binding in a guard block, which the grammar reads as an
-- | expression because a guard line may begin the same way.
toBinder :: Expr -> Binder
toBinder = case _ of
  ExprVar n | n.qualifier == Nothing -> BinderVar n
  ExprSection r -> BinderWildcard r
  ExprConstructor n -> BinderConstructor n []
  ExprTag n -> BinderTag n []
  ExprBoolean r b -> BinderBoolean r b
  ExprInt l -> BinderInt l
  ExprNumber l -> BinderNumber l
  ExprChar l -> BinderChar l
  ExprString l -> BinderString l
  ExprUnit r -> BinderUnit r
  ExprParens e -> BinderParens (toBinder e)
  ExprTuple es -> BinderTuple (map toBinder es)
  ExprTyped e t -> BinderTyped (toBinder e) t
  ExprAt n e -> BinderAs n (toBinder e)
  ExprRecord fs -> BinderRecord (map field fs)
  e@(ExprApp _ _) -> case spine e [] of
    { head: ExprConstructor n, args } -> BinderConstructor n (map toBinder args)
    { head: ExprTag n, args } -> BinderTag n (map toBinder args)
    _ -> BinderInvalid e
  e -> BinderInvalid e
  where
  field = case _ of
    FieldValue l e -> RecordBinderField l (toBinder e)
    FieldPun l -> RecordBinderPun l
    FieldUpdate l e -> RecordBinderField l (BinderInvalid e)
    FieldSpread (ExprVar n) -> RecordBinderRest n.range (Just n)
    FieldSpread e -> RecordBinderField { range: { start: { line: 0, column: 0 }, end: { line: 0, column: 0 } }, qualifier: Nothing, name: "" } (BinderInvalid e)

  spine = case _, _ of
    ExprApp f a, args -> spine f (Array.cons a args)
    head, args -> { head, args }
