-- | Resolving expressions and the local scopes they open into the Surface AST.
-- |
-- | A name of the value namespace is looked up in the innermost frame holding
-- | it — a binding group around it, or a local open — and then in the module's
-- | scope, and becomes the node of what it is: a local value, a value, a
-- | computation, a constructor, or an operation. A chain of operators is
-- | rebracketed by fixity; a name used infix, `` `f` ``, binds as `infixl 9`.
-- |
-- | **A `let` block and a `where` are recursive**: the block is one binding
-- | group, and everything it binds is in scope in every right-hand side and in
-- | the body. Which references may form a cycle is decided where the block is
-- | elaborated. A lambda, a `let` pattern binding, and a binding of a guard
-- | block take irrefutable patterns, and a binding of a guard block is in scope
-- | in the lines after it.
-- |
-- | The forms whose resolution belongs to a later part are reported as not
-- | supported yet: the anonymous argument `_` and the sections and `case _ of`
-- | it makes, a macro call, and in a handling expression a group written in
-- | place, a cell, and `resume`.
module Stella.Compiler.Resolve.Expr
  ( resolveExpr
  , resolveLet
  , resolveDefinition
  ) where

import Prelude
import Prim hiding (Type)

import Data.Array as Array
import Data.Either (Either(..))
import Data.Enum (fromEnum)
import Data.Foldable (foldl, traverse_)
import Data.Maybe (Maybe(..), maybe)
import Data.String.CodePoints (toCodePointArray)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Stella.Compiler.CST.Range (binderRange, covering, exprRange, letBindingRange, nonEmpty)
import Stella.Compiler.CST.Types as CST
import Stella.Compiler.Resolve.Binder (Member(..), ResolvedMember(..), requireIrrefutable, resolveAlternative, resolveBinders, resolveGroup)
import Stella.Compiler.Resolve.Fixity (rebracket)
import Stella.Compiler.Resolve.Group (GroupError(..), LocalBinding(..), groupBindings)
import Stella.Compiler.Resolve.Label (reportLabelsTwice)
import Stella.Compiler.Resolve.Monad (Found(..), Resolve, ResolveReason(..), ValueKind(..), ValueReference(..), lookupOperator, lookupValue, lookupValueReference, openedBy, report, valueKind, withOpened, withTypeVariables, withValues)
import Stella.Compiler.Resolve.Type (resolveSignature, resolveType, signatureScope)
import Stella.Compiler.Surface.Decl (Associativity(..))
import Stella.Compiler.Surface.Expr (AlternativeBody(..), Binder, Expr(..), GuardLine(..), HandlerItem(..), LetBinding(..), RecordField(..), exprOrigin)
import Stella.Compiler.Surface.Origin (Origin(..), spanning)
import Stella.Compiler.TypedCore.Domain (scalarString, scalarValue)
import Stella.Compiler.TypedCore.Name (Ident, Qualified, Symbol(..), Tag(..))
import Stella.Compiler.TypedCore.Prim (unitCtor)
import Stella.Compiler.TypedCore.Term (Literal(..))

resolveExpr :: CST.Expr -> Resolve Expr
resolveExpr e = case e of
  CST.ExprVar n -> reference o n
  CST.ExprConstructor n -> constructor ExprConstructor n
  CST.ExprDiscriminator n -> constructor ExprDiscriminator n
  CST.ExprOperatorValue n -> lookupOperator n >>= case _ of
    Found f -> maybe (pure (ExprInvalid o)) (global o) f.target
    NotFound -> invalid (UnknownOperator (written n))
    Ambiguous -> invalid (AmbiguousOperator (written n))
  CST.ExprTag n -> pure (ExprTag o (Tag n.name))
  CST.ExprHole n -> pure (ExprHole o n.name)
  CST.ExprSection _ -> invalid (NotYetSupported "The anonymous argument `_`")
  CST.ExprBoolean _ b -> pure (ExprLiteral o (LitBoolean b))
  CST.ExprInt l -> pure (ExprLiteral o (LitInt l.value))
  CST.ExprNumber l -> pure (ExprLiteral o (LitNumber l.value))
  CST.ExprChar l -> case toCodePointArray l.value of
    [ c ] | Just v <- scalarValue (fromEnum c) -> pure (ExprLiteral o (LitChar v))
    _ -> invalid LiteralNotScalar
  CST.ExprString l -> case scalarString l.value of
    Just s -> pure (ExprLiteral o (LitString s))
    Nothing -> invalid LiteralNotScalar
  CST.ExprUnit _ -> pure (ExprConstructor o unitCtor)
  CST.ExprParens inner -> resolveExpr inner
  CST.ExprTuple es -> ExprTuple o <$> traverse resolveExpr es
  CST.ExprRecord _ fields -> ExprRecord o <$> recordFields fields
  CST.ExprApp f a -> ExprApp o <$> resolveExpr f <*> resolveExpr a
  CST.ExprOp _ _ _ -> operatorChain e
  CST.ExprTyped inner t -> ExprTyped o <$> resolveExpr inner <*> resolveType t
  CST.ExprAccess inner labels -> do
    inner' <- resolveExpr inner
    pure (foldl (\acc l -> ExprSelect (spanning (exprOrigin acc) (FromSource l.range)) acc (Symbol l.name)) inner' labels)
  CST.ExprLambda bs body -> do
    r <- resolveBinders bs
    traverse_ requireIrrefutable r.binders
    ExprLambda o r.binders <$> withValues r.bound (resolveExpr body)
  CST.ExprLet items body -> resolveLet o items (resolveExpr body)
  CST.ExprCase scrutinees alternatives -> do
    scrutinees' <- traverse scrutinee scrutinees
    ExprCase o scrutinees' <$> traverse alternative alternatives
  CST.ExprHandle inner items -> handling items inner
  CST.ExprUsing items inner -> handling items inner
  CST.ExprLocalOpen alias inner -> open alias inner
  CST.ExprImportIn alias inner -> open alias inner
  CST.ExprMacro _ -> invalid (NotYetSupported "A macro call")
  CST.ExprAt n label -> operationAt n label
  CST.ExprCellRead _ -> invalid (NotYetSupported "A cell")
  CST.ExprCellWrite _ _ -> invalid (NotYetSupported "A cell")
  CST.ExprResume _ -> invalid (NotYetSupported "`resume`")
  where
  o = FromSource (exprRange e)
  invalid reason = report (exprRange e) reason $> ExprInvalid o

  constructor k n = lookupValue n >>= case _ of
    Found q -> valueKind q >>= case _ of
      ConstructorValue -> pure (k o q)
      _ -> invalid (NotAConstructor (written n))
    NotFound -> invalid (UnknownConstructor (written n))
    Ambiguous -> invalid (AmbiguousValue (written n))

  scrutinee = case _ of
    CST.ExprSection r -> report r (NotYetSupported "`case _ of`") $> ExprInvalid (FromSource r)
    s -> resolveExpr s

  handling items inner = do
    items' <- Array.catMaybes <$> traverse handlerItem items
    ExprHandle o items' <$> resolveExpr inner
  handlerItem = case _ of
    CST.ListHandler h -> Just <<< HandlerApplied <$> resolveExpr h
    CST.ListGroup g -> report g.head.range (NotYetSupported "A handler group written in place") $> Nothing

  open alias inner = openedBy (written alias) >>= case _ of
    Just names -> withOpened names (resolveExpr inner)
    Nothing -> report alias.range (UnknownAlias (written alias)) $> ExprInvalid o

  operationAt n label = case label of
    CST.ExprVar l | l.qualifier == Nothing -> lookupValueReference n >>= case _ of
      Found (GlobalReference q) -> valueKind q >>= case _ of
        OperationValue -> pure (ExprOperation o q (Just (Symbol l.name)))
        _ -> report n.range (NotAnOperation (written n)) $> ExprInvalid o
      Found (LocalReference _) -> report n.range (NotAnOperation (written n)) $> ExprInvalid o
      NotFound -> report n.range (UnknownValue (written n)) $> ExprInvalid o
      Ambiguous -> report n.range (AmbiguousValue (written n)) $> ExprInvalid o
    _ -> report (exprRange label) LabelExpected $> ExprInvalid o

-- | A reference to a name of the value namespace.
reference :: Origin -> CST.Name -> Resolve Expr
reference o n = lookupValueReference n >>= case _ of
  Found (LocalReference v) -> pure (ExprLocal o v)
  Found (GlobalReference q) -> global o q
  NotFound -> report n.range (UnknownValue (written n)) $> ExprInvalid o
  Ambiguous -> report n.range (AmbiguousValue (written n)) $> ExprInvalid o

-- | The node a reference to a global is: what the entity is decides it.
global :: Origin -> Qualified Ident -> Resolve Expr
global o q = valueKind q <#> case _ of
  PlainValue -> ExprValue o q
  ComputationValue -> ExprComputation o q
  ConstructorValue -> ExprConstructor o q
  OperationValue -> ExprOperation o q Nothing

-- | A chain of operators, rebracketed by fixity. An operator nothing in scope
-- | stands for, or two that cannot be chained, leave the chain invalid.
operatorChain :: CST.Expr -> Resolve Expr
operatorChain e = do
  let chain = flatten e
  first <- resolveExpr chain.first
  rest <- traverse (\(Tuple op operand) -> Tuple <$> operator op <*> resolveExpr operand) chain.rest
  case traverse (\(Tuple op operand) -> map (\op' -> Tuple op' operand) op) rest of
    Nothing -> pure (ExprInvalid o)
    Just ops -> case rebracket _.fixity apply first ops of
      Right result -> pure result
      Left { first: a, second: b } -> report b.name.range (OperatorsUnordered (written b.name) (written a.name)) $> ExprInvalid o
  where
  o = FromSource (exprRange e)
  flatten = case _ of
    CST.ExprOp a op b -> let c = flatten a in c { rest = Array.snoc c.rest (Tuple op b) }
    x -> { first: x, rest: [] }
  operator = case _ of
    CST.OperatorSymbol n -> lookupOperator n >>= case _ of
      -- An operator whose target does not resolve is reported where it is
      -- declared, and leaves the chain invalid here.
      Found f -> case f.target of
        Just q -> do
          target <- global (FromSource n.range) q
          pure (Just { name: n, fixity: { associativity: f.associativity, precedence: f.precedence }, target })
        Nothing -> pure Nothing
      NotFound -> report n.range (UnknownOperator (written n)) $> Nothing
      Ambiguous -> report n.range (AmbiguousOperator (written n)) $> Nothing
    CST.OperatorName n -> reference (FromSource n.range) n <#> case _ of
      ExprInvalid _ -> Nothing
      target -> Just { name: n, fixity: { associativity: AssociateLeft, precedence: 9 }, target }
  apply op l r = ExprOperator (spanning (exprOrigin l) (exprOrigin r)) op.target l r

recordFields :: Array CST.RecordField -> Resolve (Array RecordField)
recordFields fields = do
  reportLabelsTwice (Array.mapMaybe labelOf fields)
  traverse field fields
  where
  labelOf = case _ of
    CST.FieldValue n _ -> Just n
    CST.FieldPun n -> Just n
    CST.FieldUpdate n _ -> Just n
    CST.FieldSpread _ -> Nothing
  field = case _ of
    CST.FieldValue n v -> FieldValue (FromSource (covering n.range (exprRange v))) (Symbol n.name) <$> resolveExpr v
    CST.FieldPun n -> FieldValue (FromSource n.range) (Symbol n.name) <$> reference (FromSource n.range) n
    CST.FieldUpdate n v -> FieldUpdate (FromSource (covering n.range (exprRange v))) (Symbol n.name) <$> resolveExpr v
    CST.FieldSpread v -> FieldSpread (FromSource (exprRange v)) <$> resolveExpr v

alternative :: CST.CaseAlternative -> Resolve { origin :: Origin, patterns :: Array (Array Binder), body :: AlternativeBody }
alternative alt = do
  r <- resolveAlternative alt.patterns
  body <- withValues r.bound case alt.body of
    CST.Unconditional b -> Unconditional <$> resolveExpr b
    CST.GuardBlock lines -> Guarded <$> guardLines lines
  pure { origin: FromSource (nonEmpty (map binderRange (Array.concat alt.patterns) <> bodyRanges)), patterns: r.patterns, body }
  where
  bodyRanges = case alt.body of
    CST.Unconditional b -> [ exprRange b ]
    CST.GuardBlock lines -> map lineRange lines
  lineRange = case _ of
    CST.GuardBinding b v -> covering (binderRange b) (exprRange v)
    CST.Guard c v -> covering (exprRange c) (exprRange v)

-- | The lines of a guard block, each binding in scope in the lines after it.
guardLines :: Array CST.GuardLine -> Resolve (Array GuardLine)
guardLines lines = case Array.uncons lines of
  Nothing -> pure []
  Just { head, tail } -> case head of
    CST.GuardBinding b v -> do
      v' <- resolveExpr v
      r <- resolveBinders [ b ]
      traverse_ requireIrrefutable r.binders
      rest <- withValues r.bound (guardLines tail)
      pure (Array.fromFoldable (Array.head r.binders <#> \b' -> GuardBinding (FromSource (covering (binderRange b) (exprRange v))) b' v') <> rest)
    CST.Guard condition body -> do
      let o = FromSource (covering (exprRange condition) (exprRange body))
      line <- case condition of
        CST.ExprVar n | n.qualifier == Nothing && n.name == "otherwise" -> GuardOtherwise o <$> resolveExpr body
        _ -> GuardWhen o <$> resolveExpr condition <*> resolveExpr body
      rest <- guardLines tail
      pure ([ line ] <> rest)

-- | A `let` block or a `where` around what the body resolves to: one binding
-- | group, in scope in every right-hand side and in the body.
resolveLet :: Origin -> Array CST.LetBinding -> Resolve Expr -> Resolve Expr
resolveLet o items body = do
  let grouped = groupBindings items
  traverse_ (\(GroupError r reason) -> report r (LetGrouping reason)) grouped.errors
  g <- resolveGroup (map member grouped.bindings)
  withValues g.bound do
    bindings <- Array.catMaybes <$> traverse binding (Array.zip grouped.bindings g.members)
    ExprLet o bindings <$> body
  where
  member = case _ of
    LocalValue v -> MemberName v.name
    LocalPattern b _ -> MemberPattern b
  binding = case _ of
    Tuple (LocalValue v) (ResolvedName var) -> do
      signature <- traverse resolveSignature v.signature
      withTypeVariables (maybe [] signatureScope signature) do
        d <- resolveDefinition v.binders v.body Nothing
        pure (Just (LetValue { origin: FromSource (covering v.name.range (exprRange v.body)), var, signature, params: d.params, body: d.body }))
    Tuple (LocalPattern b v) (ResolvedPattern b') -> do
      requireIrrefutable b'
      v' <- resolveExpr v
      pure (Just (LetPattern { origin: FromSource (covering (binderRange b) (exprRange v)), binder: b', body: v' }))
    _ -> pure Nothing

-- | A definition: its parameters, one binding group of irrefutable patterns,
-- | and its body, under its `where` where it has one.
resolveDefinition
  :: Array CST.Binder
  -> CST.Expr
  -> Maybe (Array CST.LetBinding)
  -> Resolve { params :: Array Binder, body :: Expr }
resolveDefinition params body local = do
  r <- resolveBinders params
  traverse_ requireIrrefutable r.binders
  body' <- withValues r.bound case local of
    Nothing -> resolveExpr body
    Just items -> resolveLet (FromSource (nonEmpty ([ exprRange body ] <> map letBindingRange items))) items (resolveExpr body)
  pure { params: r.binders, body: body' }

written :: CST.Name -> String
written n = maybe n.name (\q -> q <> "." <> n.name) n.qualifier
