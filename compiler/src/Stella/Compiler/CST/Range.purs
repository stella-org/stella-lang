-- | The source range a node of the concrete syntax tree covers, composed from
-- | the ranges it holds.
-- |
-- | A leaf carries a range — a name, a literal, a written symbol such as `_` or
-- | `->*` — and so does a form made by its brackets: `()`, a record, a row, a
-- | variant, and a record pattern, whose range covers the brackets themselves.
-- | Every other node covers the smallest range holding everything beneath it,
-- | so its range begins at its first part and ends at its last. A keyword and a
-- | grouping parenthesis are no part of it: `\x -> e` covers `x -> e`, and
-- | `(f x)` covers `f x`.
-- |
-- | Every node holds at least one range, so every node has one.
module Stella.Compiler.CST.Range
  ( covering
  , exprRange
  , typeRange
  , kindRange
  , binderRange
  , letBindingRange
  , nonEmpty
  ) where

import Prelude
import Prim hiding (Type)

import Data.Array.NonEmpty (NonEmptyArray)
import Data.Array.NonEmpty as NonEmptyArray
import Data.Foldable (foldMap, foldl)
import Data.Maybe (Maybe(..))
import Data.Semigroup.Foldable (foldl1)
import Stella.Compiler.CST.Types (Binder(..), CaseBody(..), Clause(..), Expr(..), GuardLine(..), HandlerListItem(..), Kind(..), LetBinding(..), SourcePos, SourceRange, Type(..), TypeVarBinding(..), inSource, sameSpace)

-- | The smallest range covering both, whichever order they stand in. **Two
-- | ranges are joined only where they are in one text**: a range of another is
-- | left out, the first standing as it is. A node a parse of an expansion
-- | produced stands under one the enclosing text holds, whose range is the
-- | call's, so a well-formed tree never asks for the two to be joined.
covering :: SourceRange -> SourceRange -> SourceRange
covering a b
  | not (sameSpace a.space b.space) = a
  | otherwise = { space: a.space, start: earlier a.start b.start, end: later a.end b.end }
      where
      earlier p q = if before q p then q else p
      later p q = if before p q then q else p

before :: SourcePos -> SourcePos -> Boolean
before p q = p.line < q.line || (p.line == q.line && p.column < q.column)

-- | The range covering a first range and every one after it.
cover :: SourceRange -> Array SourceRange -> SourceRange
cover = foldl covering

-- | The range covering every range of a sequence that is never empty.
coverAll :: NonEmptyArray SourceRange -> SourceRange
coverAll = foldl1 covering

-- | The range covering a sequence the grammar never reads empty: the components
-- | of a tuple, the choices of an or-pattern, the scrutinees of a `case`, the
-- | lines of a guard block. Read empty, it is `nowhere`.
nonEmpty :: Array SourceRange -> SourceRange
nonEmpty rs = case NonEmptyArray.fromArray rs of
  Just ne -> coverAll ne
  Nothing -> nowhere

-- | Line 0, which is no position of a source text.
nowhere :: SourceRange
nowhere = inSource { line: 0, column: 0 } { line: 0, column: 0 }

kindRange :: Kind -> SourceRange
kindRange = case _ of
  KindName n -> n.range
  KindVar n -> n.range
  KindApp f a -> covering (kindRange f) (kindRange a)
  KindArrow a b -> covering (kindRange a) (kindRange b)
  KindParens k -> kindRange k

typeVarBindingRange :: TypeVarBinding -> SourceRange
typeVarBindingRange = case _ of
  BindName n -> n.range
  BindKinded n k -> covering n.range (kindRange k)

typeRange :: Type -> SourceRange
typeRange = case _ of
  TypeVar n -> n.range
  TypeConstructor n -> n.range
  TypeWildcard r -> r
  TypeHole n -> n.range
  TypeUnit r -> r
  TypeApp f a -> covering (typeRange f) (typeRange a)
  TypeOp a _ b -> covering (typeRange a) (typeRange b)
  TypeArrow a b -> covering (typeRange a) (typeRange b)
  TypeOperationArrow a _ b -> covering (typeRange a) (typeRange b)
  TypeEffect t _ e -> covering (typeRange t) (typeRange e)
  TypeCapability a b -> covering (typeRange a) (typeRange b)
  TypeForall bs t -> cover (typeRange t) (map typeVarBindingRange bs)
  TypeConstrained c t -> covering (typeRange c) (typeRange t)
  TypeKinded t k -> covering (typeRange t) (kindRange k)
  TypeParens t -> typeRange t
  TypeTuple ts -> nonEmpty (map typeRange ts)
  TypeRecord r _ -> r
  TypeEffectRow r _ -> r
  TypeVariant r _ -> r
  TypeSynthesized n t f -> cover (typeRange t) ([ f.range ] <> foldMap (pure <<< _.range) n)
  TypeDirective d t -> covering d.name.range (typeRange t)

exprRange :: Expr -> SourceRange
exprRange = case _ of
  ExprVar n -> n.range
  ExprConstructor n -> n.range
  ExprDiscriminator n -> n.range
  ExprOperatorValue n -> n.range
  ExprTag n -> n.range
  ExprHole n -> n.range
  ExprSection r -> r
  ExprBoolean r _ -> r
  ExprInt l -> l.range
  ExprNumber l -> l.range
  ExprChar l -> l.range
  ExprString l -> l.range
  ExprUnit r -> r
  ExprParens e -> exprRange e
  ExprTuple es -> nonEmpty (map exprRange es)
  ExprRecord r _ -> r
  ExprApp f a -> covering (exprRange f) (exprRange a)
  ExprOp a _ b -> covering (exprRange a) (exprRange b)
  ExprTyped e t -> covering (exprRange e) (typeRange t)
  ExprAccess e ls -> cover (exprRange e) (map _.range ls)
  ExprLambda bs e -> cover (exprRange e) (map binderRange bs)
  ExprLet ls e -> cover (exprRange e) (map letBindingRange ls)
  ExprCase es as -> cover (nonEmpty (map exprRange es)) (map alternativeRange as)
  ExprHandle e is -> cover (exprRange e) (map listItemRange is)
  ExprUsing is e -> cover (exprRange e) (map listItemRange is)
  ExprLocalOpen n e -> covering n.range (exprRange e)
  ExprImportIn n e -> covering n.range (exprRange e)
  ExprMacro m -> cover m.name.range (map _.range m.body)
  ExprQuote q -> q.range
  ExprAntiquote a -> a.range
  ExprExpanded e -> e.call
  ExprInvalid r -> r
  ExprAt n e -> covering n.range (exprRange e)
  ExprCellRead n -> n.range
  ExprCellWrite n e -> covering n.range (exprRange e)
  ExprResume r -> r
  where
  alternativeRange a = cover (bodyRange a.body) (map binderRange (join a.patterns))
  bodyRange = case _ of
    Unconditional e -> exprRange e
    GuardBlock gs -> nonEmpty (map guardRange gs)
  guardRange = case _ of
    GuardBinding b e -> covering (binderRange b) (exprRange e)
    Guard g e -> covering (exprRange g) (exprRange e)

letBindingRange :: LetBinding -> SourceRange
letBindingRange = case _ of
  LetSignature n t -> covering n.range (typeRange t)
  LetValue n bs e -> cover n.range (map binderRange bs <> [ exprRange e ])
  LetPattern b e -> covering (binderRange b) (exprRange e)

listItemRange :: HandlerListItem -> SourceRange
listItemRange = case _ of
  ListGroup g ->
    cover g.head.range
      (map (\c -> covering c.name.range (exprRange c.value)) g.cells <> map clauseRange g.clauses)
  ListHandler e -> exprRange e

clauseRange :: Clause -> SourceRange
clauseRange = case _ of
  ClauseOperation _ n bs e -> cover n.range (map binderRange bs <> [ exprRange e ])
  ClauseReturn b e -> covering (binderRange b) (exprRange e)

binderRange :: Binder -> SourceRange
binderRange = case _ of
  BinderWildcard r -> r
  BinderVar n -> n.range
  BinderAs n b -> covering n.range (binderRange b)
  BinderConstructor n bs -> cover n.range (map binderRange bs)
  BinderTag n bs -> cover n.range (map binderRange bs)
  BinderBoolean r _ -> r
  BinderInt l -> l.range
  BinderNumber l -> l.range
  BinderChar l -> l.range
  BinderString l -> l.range
  BinderUnit r -> r
  BinderParens b -> binderRange b
  BinderTuple bs -> nonEmpty (map binderRange bs)
  BinderOr bs -> nonEmpty (map binderRange bs)
  BinderRecord r _ -> r
  BinderTyped b t -> covering (binderRange b) (typeRange t)
  BinderApp f as -> cover (binderRange f) (map binderRange as)
  BinderInvalid e -> exprRange e
