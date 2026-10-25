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
-- | **The cells of a handling expression are in scope in the operation clauses
-- | of its groups**, every group alike, and closed in the rest of the
-- | expression — its initial values, its return clauses, the computation it
-- | handles, and the handlers applied as its items — where a reference to one is
-- | reported as such. A handler declaration's cells are in scope in its
-- | operation clauses in the same way. A cell hides one of its name outside its
-- | expression throughout it. A clause names an operation of the effect its handler
-- | handles, looked up among that effect's operations whatever the imports
-- | bring; a group headed by a label handles the effect of the operations in
-- | scope its clauses name.
-- |
-- | **`resume` stands applied, in the immediate body of a `full` clause**: not
-- | inside a lambda, a local function, a `case _ of`, or a handling expression
-- | there, each of which could keep it beyond the clause
-- | ([Effect Handlers](../../../../docs/technical-references/02-Surface-Language/02-Effect-Handlers.md)).
-- |
-- | **`case _ of` is a function**: each anonymous scrutinee, from the left, is a
-- | parameter of a λ around the `case`, named apart from every name source can
-- | write.
-- |
-- | The forms whose resolution belongs to a later part are reported as not
-- | supported yet: the anonymous argument `_` elsewhere, and the sections it
-- | makes, and a macro call.
module Stella.Compiler.Resolve.Expr
  ( resolveExpr
  , resolveLet
  , resolveDefinition
  , resolveTopDefinition
  , resolveHandler
  ) where

import Prelude
import Prim hiding (Type)

import Data.Array as Array
import Data.Either (Either(..))
import Data.Enum (fromEnum)
import Data.Foldable (foldM, foldl, for_, traverse_)
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.String.CodeUnits as CodeUnits
import Data.String.CodePoints (toCodePointArray)
import Data.Set (Set)
import Data.Set as Set
import Data.Traversable (for, sequence, traverse)
import Data.TraversableWithIndex (traverseWithIndex)
import Data.Tuple (Tuple(..))
import Stella.Compiler.CST.Range (binderRange, covering, exprRange, letBindingRange, nonEmpty, typeRange)
import Stella.Compiler.CST.Types as CST
import Stella.Compiler.CST.Types (sameSpace)
import Stella.Compiler.Resolve.Binder (Member(..), ResolvedMember(..), requireIrrefutable, resolveAlternative, resolveBinders, resolveCells, resolveGroup, resolveScopedBinders)
import Stella.Compiler.Resolve.Fixity (rebracket)
import Stella.Compiler.Resolve.Group (GroupError(..), LocalBinding(..), groupBindings)
import Stella.Compiler.Resolve.Label (reportLabelsTwice)
import Stella.Compiler.Interface.Environment (reachable)
import Stella.Compiler.Macro.Bundle (syntaxModuleName)
import Stella.Compiler.Resolve.Quotation (quotation)
import Stella.Compiler.Resolve.Monad (Cell(..), CellClosure(..), Found(..), HandledEffectProblem(..), Resolve, SynonymBody(..), ResolveReason(..), ResumeBlock(..), ResumeState(..), TypeReference(..), ValueKind(..), ValueReference(..), blockResume, context, constructorOf, declaresNoOperations, freshBinding, lookupCell, lookupOperator, lookupType, lookupValue, lookupValueReference, openedBy, operationOf, operationsOf, report, resumeState, speculatively, synonymBody, valueKind, withCells, withCellsClosed, withOpened, withResume, withTypeVariables, withValues)
import Stella.Compiler.Resolve.Type (resolveSignature, resolveType, scopeOf, signatureScope)
import Stella.Compiler.Surface.Decl (Associativity(..))
import Stella.Compiler.Surface.Expr (AlternativeBody(..), Binder(..), CellDeclaration, ClauseForm(..), Expr(..), Group, GuardLine(..), HandlerBody, HandlerItem(..), LetBinding(..), OperationClause, RecordField(..), exprOrigin)
import Stella.Compiler.Surface.Name (BindingId(..), CellVar, LocalVar(..), TypeVar)
import Stella.Compiler.Surface.Origin (Origin, originOf, spanning)
import Stella.Compiler.Surface.Type (EffectApplication, EffectRowItem(..), Signature, Type(..))
import Stella.Compiler.TypedCore.Domain (scalarString, scalarValue)
import Stella.Compiler.TypedCore.Name (EffName(..), Ident(..), Qualified(..), Symbol(..), Tag(..), TyName)
import Stella.Compiler.TypedCore.Prim (functionTy, unitCtor, unitTy)
import Stella.Compiler.TypedCore.Term (Literal(..))
import Stella.Compiler.TypedCore.Type as Core

resolveExpr :: CST.Expr -> Resolve Expr
resolveExpr e = case e of
  CST.ExprVar n -> reference o n
  CST.ExprConstructor n -> constructor ExprConstructor n
  CST.ExprDiscriminator n -> discriminator n
  CST.ExprOperatorValue n -> lookupOperator n >>= case _ of
    Found f -> maybe (pure (ExprInvalid o)) (global o) f.target
    NotFound -> invalid (UnknownOperator (written n))
    Ambiguous -> invalid (AmbiguousOperator (written n))
  CST.ExprTag n -> pure (ExprTag o (originOf n.range) (Tag n.name) Nothing)
  CST.ExprHole n -> pure (ExprHole o n.name)
  CST.ExprSection r
    | writtenInMacroInput r -> invalid AnonymousArgumentInMacroInput
    | otherwise -> invalid AnonymousArgumentMisplaced
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
  CST.ExprParens bounds inner
    | anonymousOperands bounds inner -> section bounds (operands inner) \at -> operatorChain at inner
    | otherwise -> resolveExpr inner
  CST.ExprTuple bounds es
    | Array.any (isAnonymous bounds) es -> section bounds es \at -> ExprTuple o <$> traverseWithIndex at es
    | otherwise -> ExprTuple o <$> traverse resolveExpr es
  CST.ExprRecord _ fields -> ExprRecord o <$> recordFields fields
  CST.ExprApp f a
    | Just applied <- tagApplied f [ a ] -> case applied.payloads of
        [ payload ] -> ExprTag o (originOf applied.tag.range) (Tag applied.tag.name) <<< Just <$> resolveExpr payload
        _ -> invalid TagPayloadMany
    | otherwise -> case unparenthesized f of
        CST.ExprResume r -> ExprApp o <$> resumeAt r <*> resolveExpr a
        _ -> ExprApp o <$> resolveExpr f <*> resolveExpr a
  CST.ExprOp _ _ _ -> operatorChain (const resolveExpr) e
  CST.ExprTyped inner t -> ExprTyped o <$> resolveExpr inner <*> resolveType t
  CST.ExprAccess inner labels -> do
    inner' <- resolveExpr inner
    pure (foldl (\acc l -> ExprSelect (spanning (exprOrigin acc) (originOf l.range)) acc (originOf l.range) (Symbol l.name)) inner' labels)
  CST.ExprLambda bs body -> blockResume InsideLambda do
    r <- resolveBinders bs
    traverse_ requireIrrefutable r.binders
    ExprLambda o r.binders <$> withValues r.bound (resolveExpr body)
  CST.ExprLet items body -> resolveLet o items (resolveExpr body)
  CST.ExprCase bounds scrutinees alternatives -> do
    anonymous <- traverse (anonymousScrutinee bounds) scrutinees
    let
      params = Array.catMaybes anonymous
      matching = do
        scrutinees' <- traverse (\(Tuple s a) -> maybe (resolveExpr s) (\p -> pure (ExprLocal p.origin p.var)) a) (Array.zip scrutinees anonymous)
        ExprCase o scrutinees' <$> traverse (alternative (Array.length scrutinees)) alternatives
    if Array.null params then matching
    else blockResume InsideAnonymousCase (ExprLambda o (map (\p -> BinderVar p.origin p.var) params) <$> matching)
  CST.ExprHandle inner items -> blockResume InsideHandling (handling items inner)
  CST.ExprUsing items inner -> blockResume InsideHandling (handling items inner)
  CST.ExprLocalOpen alias inner -> open alias inner
  CST.ExprImportIn alias inner -> open alias inner
  CST.ExprMacro _ -> invalid (NotYetSupported "A macro call")
  CST.ExprQuote q -> context >>= \ctx ->
    if maybe false (Set.member syntaxModuleName <<< reachable) ctx.view then quotation ctx.module resolveExpr o q
    else invalid QuotationWithoutSyntax
  -- an antiquotation outside a quotation is reported where the syntax is checked
  CST.ExprAntiquote _ -> pure (ExprInvalid o)
  CST.ExprExpanded expanded -> resolveExpr expanded.expr
  -- the expansion that failed was reported where it failed
  CST.ExprInvalid _ -> pure (ExprInvalid o)
  CST.ExprAt n label -> operationAt n label
  CST.ExprCellRead n -> cell n <#> maybe (ExprInvalid o) (ExprCellRead o)
  CST.ExprCellWrite n v
    | isAnonymous (cellWriteRange n v) v -> section (cellWriteRange n v) [ v ] (cellWrite n v)
    | otherwise -> cellWrite n v (const resolveExpr)
  CST.ExprResume _ -> resumeState >>= case _ of
    ResumeAvailable -> invalid ResumeNotApplied
    ResumeBlocked why -> invalid (ResumeMisplaced why)
  where
  o = originOf (exprRange e)
  invalid reason = report (exprRange e) reason $> ExprInvalid o

  constructor k n = lookupValue n >>= case _ of
    Found q -> valueKind q >>= case _ of
      ConstructorValue -> pure (k o q)
      _ -> invalid (NotAConstructor (written n))
    NotFound -> invalid (UnknownConstructor (written n))
    Ambiguous -> invalid (AmbiguousValue (written n))

  discriminator n = lookupValue n >>= case _ of
    Found q -> constructorOf q >>= case _ of
      Just c -> do
        id@(BindingId k) <- freshBinding
        let
          x = LocalVar { id, name: Ident ("discriminator#" <> show k) }
          answering b holds = { origin: o, patterns: [ [ b ] ], body: Unconditional (ExprLiteral o (LitBoolean holds)) }
          built = answering (BinderConstructor o q (Array.replicate c.arity (BinderWildcard o))) true
        pure (ExprLambda o [ BinderVar o x ] (ExprCase o [ ExprLocal o x ] (if c.siblings == 1 then [ built ] else [ built, answering (BinderWildcard o) false ])))
      Nothing -> invalid (NotAConstructor (written n))
    NotFound -> invalid (UnknownConstructor (written n))
    Ambiguous -> invalid (AmbiguousValue (written n))

  cellWrite n v resolveValue = do
    c <- cell n
    v' <- resolveValue 0 v
    pure (maybe (ExprInvalid o) (\c' -> ExprCellWrite o c' v') c)

  -- what a section holds is inside the λ it stands for, so a `resume` in it
  -- would be kept beyond its clause
  section bounds slots build = blockResume InsideLambda do
    params <- traverse
      ( \x -> case unparenthesized x of
          CST.ExprSection r | isAnonymous bounds x -> do
            id@(BindingId k) <- freshBinding
            pure (Just { origin: originOf r, var: LocalVar { id, name: Ident ("section#" <> show k) } })
          _ -> pure Nothing
      )
      slots
    body <- build (\i x -> maybe (resolveExpr x) (\p -> pure (ExprLocal p.origin p.var)) (join (Array.index params i)))
    pure (ExprLambda o (map (\p -> BinderVar p.origin p.var) (Array.catMaybes params)) body)

  -- an anonymous scrutinee, parenthesized or not, is a parameter of a λ
  -- around the `case`, named apart from every name source can write
  anonymousScrutinee bounds s = case unparenthesized s of
    CST.ExprSection r | isAnonymous bounds s -> do
      id@(BindingId n) <- freshBinding
      pure (Just { origin: originOf r, var: LocalVar { id, name: Ident ("case#" <> show n) } })
    _ -> pure Nothing

  handling items inner = do
    source <- foldM handlingItem { cells: [], items: [] } items
    c <- resolveCells (map _.name source.cells)
    initials <- withCellsClosed InInitialValue c.bound (traverse (resolveExpr <<< _.value) source.cells)
    items' <- Array.catMaybes <$> traverse (handlerItem c.bound) source.items
    handled <- withCellsClosed InHandledComputation c.bound (resolveExpr inner)
    pure (ExprHandle o (cellDeclarations source.cells initials c.cells) items' handled)

  -- Every `var` stands ahead of the groups and handlers; one after them is
  -- reported and left out.
  handlingItem acc = case _ of
    CST.ListCell n v
      | Array.null acc.items -> pure acc { cells = Array.snoc acc.cells { name: n, value: v } }
      | otherwise -> report n.range (CellAfterItem n.name) $> acc
    item -> pure acc { items = Array.snoc acc.items item }

  handlerItem cells = case _ of
    CST.ListCell _ _ -> pure Nothing
    CST.ListHandler h -> Just <<< HandlerApplied <$> withCellsClosed InHandlerApplied cells (resolveExpr h)
    CST.ListGroup g -> map HandlerGroup <$> group cells g

  open alias inner = openedBy (written alias) >>= case _ of
    Just names -> withOpened names (resolveExpr inner)
    Nothing -> report alias.range (UnknownAlias (written alias)) $> ExprInvalid o

  operationAt n label = case label of
    CST.ExprVar l | l.qualifier == Nothing -> lookupValueReference n >>= case _ of
      Found (GlobalReference q) -> valueKind q >>= case _ of
        OperationValue -> pure (ExprOperation o (originOf n.range) q (Just { origin: originOf l.range, label: Symbol l.name }))
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
  OperationValue -> ExprOperation o o q Nothing

-- | A chain of operators, rebracketed by fixity. An operator nothing in scope
-- | stands for, or two that cannot be chained, leave the chain invalid.
operatorChain :: (Int -> CST.Expr -> Resolve Expr) -> CST.Expr -> Resolve Expr
operatorChain resolveOperand e = do
  let chain = flatten e
  first <- resolveOperand 0 chain.first
  rest <- traverseWithIndex (\i (Tuple op operand) -> Tuple <$> operator op <*> resolveOperand (i + 1) operand) chain.rest
  case traverse (\(Tuple op operand) -> map (\op' -> Tuple op' operand) op) rest of
    Nothing -> pure (ExprInvalid o)
    Just ops -> case rebracket _.fixity apply first ops of
      Right result -> pure result
      Left { first: a, second: b } -> report b.name.range (OperatorsUnordered (written b.name) (written a.name)) $> ExprInvalid o
  where
  o = originOf (exprRange e)
  flatten = case _ of
    CST.ExprOp a op b -> let c = flatten a in c { rest = Array.snoc c.rest (Tuple op b) }
    x -> { first: x, rest: [] }
  operator = case _ of
    CST.OperatorSymbol n -> lookupOperator n >>= case _ of
      -- An operator whose target does not resolve is reported where it is
      -- declared, and leaves the chain invalid here.
      Found f -> case f.target of
        Just q -> do
          target <- global (originOf n.range) q
          pure (Just { name: n, fixity: { associativity: f.associativity, precedence: f.precedence }, target })
        Nothing -> pure Nothing
      NotFound -> report n.range (UnknownOperator (written n)) $> Nothing
      Ambiguous -> report n.range (AmbiguousOperator (written n)) $> Nothing
    CST.OperatorName n -> reference (originOf n.range) n <#> case _ of
      ExprInvalid _ -> Nothing
      target -> Just { name: n, fixity: { associativity: AssociateLeft, precedence: 9 }, target }
  apply op l r = ExprOperator (spanning (exprOrigin l) (exprOrigin r)) op.target l r

recordFields :: Array CST.RecordField -> Resolve (Array RecordField)
recordFields fields = do
  reportLabelsTwice (Array.mapMaybe labelOf fields)
  -- a replacement replaces a field of the record spread
  unless (Array.any spread fields) $ for_ fields case _ of
    CST.FieldUpdate n v -> report (covering n.range (exprRange v)) (ReplacementWithoutSpread n.name)
    _ -> pure unit
  traverse field fields
  where
  spread = case _ of
    CST.FieldSpread _ -> true
    _ -> false
  labelOf = case _ of
    CST.FieldValue n _ -> Just n
    CST.FieldPun n -> Just n
    CST.FieldUpdate n _ -> Just n
    CST.FieldSpread _ -> Nothing
  field = case _ of
    CST.FieldValue n v -> FieldValue (originOf (covering n.range (exprRange v))) (originOf n.range) (Symbol n.name) <$> resolveExpr v
    CST.FieldPun n -> FieldValue (originOf n.range) (originOf n.range) (Symbol n.name) <$> reference (originOf n.range) n
    CST.FieldUpdate n v -> FieldUpdate (originOf (covering n.range (exprRange v))) (originOf n.range) (Symbol n.name) <$> resolveExpr v
    CST.FieldSpread v -> FieldSpread (originOf (exprRange v)) <$> resolveExpr v

-- | An alternative of a `case` matching the number of values given: each row of
-- | it writes one pattern per value.
alternative :: Int -> CST.CaseAlternative -> Resolve { origin :: Origin, patterns :: Array (Array Binder), body :: AlternativeBody }
alternative scrutinees alt = do
  for_ alt.patterns \row -> case Array.uncons row of
    Just { head } | Array.length row /= scrutinees ->
      report (covering (binderRange head) (maybe (binderRange head) binderRange (Array.last row))) (PatternCount (Array.length row) scrutinees)
    _ -> pure unit
  r <- resolveAlternative alt.patterns
  body <- withValues r.bound case alt.body of
    CST.Unconditional b -> Unconditional <$> resolveExpr b
    CST.GuardBlock lines -> Guarded <$> guardLines lines
  pure { origin: originOf (nonEmpty (map binderRange (Array.concat alt.patterns) <> bodyRanges)), patterns: r.patterns, body }
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
      pure (Array.fromFoldable (Array.head r.binders <#> \b' -> GuardBinding (originOf (covering (binderRange b) (exprRange v))) b' v') <> rest)
    CST.Guard condition body -> do
      let o = originOf (covering (exprRange condition) (exprRange body))
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
  localBlock o grouped.bindings body

-- | A block of bindings grouped already, around what the body resolves to.
localBlock :: Origin -> Array LocalBinding -> Resolve Expr -> Resolve Expr
localBlock o bindings body = do
  g <- resolveGroup (map member bindings)
  withValues g.bound do
    bindings' <- Array.catMaybes <$> traverse binding (Array.zip bindings g.members)
    ExprLet o bindings' <$> body
  where
  member = case _ of
    LocalValue v -> MemberName v.name
    LocalPattern b _ -> MemberPattern b
  binding = case _ of
    Tuple (LocalValue v) (ResolvedName var) -> do
      signature <- traverse resolveSignature v.signature
      withTypeVariables (maybe [] signatureScope signature) do
        d <- (if Array.null v.binders then identity else blockResume InsideLocalFunction)
          (resolveDefinition v.binders v.body Nothing)
        pure (Just (LetValue { origin: originOf (covering v.name.range (exprRange v.body)), var, signature, params: d.params, body: d.body }))
    Tuple (LocalPattern b v) (ResolvedPattern b') -> do
      requireIrrefutable b'
      v' <- resolveExpr v
      pure (Just (LetPattern { origin: originOf (covering (binderRange b) (exprRange v)), binder: b', body: v' }))
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
    Just items -> resolveLet (originOf (nonEmpty ([ exprRange body ] <> map letBindingRange items))) items (resolveExpr body)
  pure { params: r.binders, body: body' }

-- | A top-level definition: its parameters and its body, under the bindings of
-- | its `where`, which were grouped with the module's declarations.
resolveTopDefinition
  :: Array CST.Binder
  -> CST.Expr
  -> Array LocalBinding
  -> Resolve { params :: Array Binder, body :: Expr }
resolveTopDefinition params body local = do
  r <- resolveBinders params
  traverse_ requireIrrefutable r.binders
  body' <- withValues r.bound
    if Array.null local then resolveExpr body
    else localBlock (originOf (nonEmpty ([ exprRange body ] <> map localRange local))) local (resolveExpr body)
  pure { params: r.binders, body: body' }
  where
  localRange = case _ of
    LocalValue v -> covering v.name.range (exprRange v.body)
    LocalPattern b v -> covering (binderRange b) (exprRange v)

operands :: CST.Expr -> Array CST.Expr
operands = case _ of
  CST.ExprOp a _ b -> Array.snoc (operands a) b
  x -> [ x ]

anonymousOperands :: CST.SourceRange -> CST.Expr -> Boolean
anonymousOperands bounds e = case e of
  CST.ExprOp _ _ _ -> Array.any (isAnonymous bounds) (operands e)
  _ -> false

-- | A macro may copy, drop, or move what its input holds, so a `_` is an
-- | argument only where every token from the first bound of what it is an
-- | argument of through the last was written in the text the `_` was.
isAnonymous :: CST.SourceRange -> CST.Expr -> Boolean
isAnonymous bounds e = case unparenthesized e of
  CST.ExprSection r -> case r.space of
    CST.Expansion x
      | sameSpace bounds.space r.space ->
          let
            writtenIn c = map _.space (Array.index x.written (c - 1))
            together c = case writtenIn c, writtenIn r.start.column of
              Just a, Just b -> sameSpace a b
              _, _ -> false
          in
            Array.all together (Array.range bounds.start.column (bounds.end.column - 1))
      | otherwise -> false
    _ -> true
  _ -> false

-- | A cell write, its value's parentheses among it.
cellWriteRange :: CST.Name -> CST.Expr -> CST.SourceRange
cellWriteRange n v = covering n.range case v of
  CST.ExprParens r _ -> r
  _ -> exprRange v

writtenInMacroInput :: CST.SourceRange -> Boolean
writtenInMacroInput r = case r.space of
  CST.Expansion e -> case Array.index e.written (r.start.column - 1) of
    Just { space: CST.Quotation _ } -> false
    Just _ -> true
    Nothing -> false
  _ -> false

unparenthesized :: CST.Expr -> CST.Expr
unparenthesized = case _ of
  CST.ExprParens _ inner -> unparenthesized inner
  e -> e

-- | A tag at the head of an application, and the payloads it is applied to,
-- | from the first. A tag is applied to its payload where it is written, so
-- | the spine is read through applications alone, and parentheses only around
-- | the tag itself.
tagApplied :: CST.Expr -> Array CST.Expr -> Maybe { tag :: CST.Name, payloads :: Array CST.Expr }
tagApplied f payloads = case f of
  CST.ExprApp g a -> tagApplied g (Array.cons a payloads)
  _ -> case unparenthesized f of
    CST.ExprTag tag -> Just { tag, payloads }
    _ -> Nothing

-- | `resume` applied to an argument, where it stands.
resumeAt :: CST.SourceRange -> Resolve Expr
resumeAt r = resumeState >>= case _ of
  ResumeAvailable -> pure (ExprResume (originOf r))
  ResumeBlocked why -> report r (ResumeMisplaced why) $> ExprInvalid (originOf r)

-- | The cell `x!` or `x := e` names, where it is open.
cell :: CST.Name -> Resolve (Maybe CellVar)
cell n = lookupCell n.name >>= case _ of
  Just (CellOpen v) -> pure (Just v)
  Just (CellClosed _ why) -> report n.range (CellClosedHere n.name why) $> Nothing
  Nothing -> report n.range (UnknownCell n.name) $> Nothing

-- | What a handler's clauses are read against: the effect it handles where
-- | that is known before them, the label heading a group, or nothing where
-- | neither resolved.
data Handles
  = HandlesEffect (Qualified EffName)
  | HandlesLabel CST.Name
  | HandlesUnknown

-- | A handler's clauses as written, each with the marker of the block it stands
-- | in.
type HandlerSource = Array { block :: Maybe CST.Marker, clause :: CST.Clause }

-- | A cell as written.
type CellSource = { name :: CST.Name, value :: CST.Expr }

-- | The cells as written, with their initial values and the variables they bind.
cellDeclarations :: Array CellSource -> Array Expr -> Array CellVar -> Array CellDeclaration
cellDeclarations sources initials vars =
  Array.zipWith (\(Tuple d initial) var -> { origin: originOf (cellRange d), cell: var, initial })
    (Array.zip sources initials)
    vars

-- | A group written in place, over the cells of the expression it is an item
-- | of. A head written as a type name is the effect it handles, and one written
-- | as a value name is a label; a group headed by a label handles the effect its
-- | operations belong to. A group whose effect is not decided is left out, what
-- | decided it not being reported again.
group
  :: Array CellVar
  -> { head :: CST.Name, marker :: Maybe CST.Marker, clauses :: Array CST.Clause }
  -> Resolve (Maybe Group)
group cells g = do
  handles <-
    if isLabel g.head then pure (HandlesLabel g.head)
    else lookupType g.head >>= case _ of
      Found (EffectReference e) -> pure (HandlesEffect e)
      Found _ -> report g.head.range (NotAnEffect (written g.head)) $> HandlesUnknown
      NotFound -> report g.head.range (UnknownType (written g.head)) $> HandlesUnknown
      Ambiguous -> report g.head.range (AmbiguousType (written g.head)) $> HandlesUnknown
  r <- handlerBody handles g.head.range cells (map { block: g.marker, clause: _ } g.clauses)
  pure $ r.effect <#> \effect ->
    { origin: originOf (nonEmpty ([ g.head.range ] <> map clauseRange g.clauses))
    , head: originOf g.head.range
    , label: if isLabel g.head then Just (Symbol g.head.name) else Nothing
    , effect
    , body: r.body
    }
  where
  isLabel n = n.qualifier == Nothing && case CodeUnits.charAt 0 n.name of
    Just c -> not (c >= 'A' && c <= 'Z')
    Nothing -> false

-- | A handler declaration's parts: its parameters, its signature, the effect
-- | it handles, the targets of the `~>` its signature writes, its cells, and
-- | its body. The signature's spine gives a pure arrow to each parameter, and
-- | what follows them is the handler's type. The type variables the signature
-- | quantifies implicitly are in scope in every parameter and the body, and
-- | those a `forall` on its spine binds in the parameters after it and the
-- | body. The parameters, one binding group of irrefutable patterns, are in
-- | scope in every initial value and clause.
resolveHandler
  :: Array CST.Binder
  -> CST.Type
  -> Array CST.HandlerItem
  -> Resolve
       { params :: Array Binder
       , signature :: Signature Type
       , handled :: Maybe (Qualified EffName)
       , capabilityTargets :: Maybe (Array EffectApplication)
       , cells :: Array CellDeclaration
       , body :: HandlerBody
       }
resolveHandler params t items = do
  signature <- resolveSignature t
  positions <- spinePositions signature.body
  let
    arity = Array.length params
    scopeAt i = signature.implicit <> maybe [] _.scope (Array.index positions (min i (Array.length positions - 1)))
  shape <- handlerShape arity positions
  r <- resolveScopedBinders (Array.mapWithIndex (\i p -> Tuple (scopeAt i) p) params)
  traverse_ requireIrrefutable r.binders
  source <- declared items
  withTypeVariables (scopeAt arity) $ withValues r.bound do
    c <- resolveCells (map _.name source.cells)
    initials <- withCellsClosed InInitialValue c.bound (traverse (resolveExpr <<< _.value) source.cells)
    body <- handlerBody (maybe HandlesUnknown HandlesEffect (map _.handled shape)) (typeRange t) c.bound source.clauses
    pure
      { params: r.binders
      , signature
      , handled: body.effect
      , capabilityTargets: shape >>= _.targets
      , cells: cellDeclarations source.cells initials c.cells
      , body: body.body
      }
  where
  -- Every `var` stands ahead of the clauses; one after them is reported and
  -- left out.
  declared = foldM step { cells: [], clauses: [] }
  step acc = case _ of
    CST.HandlerCell n v
      | Array.null acc.clauses -> pure acc { cells = Array.snoc acc.cells { name: n, value: v } }
      | otherwise -> report n.range (CellAfterClause n.name) $> acc
    CST.HandlerClauses m cs -> pure acc { clauses = acc.clauses <> map { block: m, clause: _ } cs }
  -- The handler's type stands after an arrow for each parameter. Where it
  -- does not, the arrows after which it stands, the fewest, are reported with
  -- the parameters. A spine reaching a type reported invalid is reported no
  -- further.
  handlerShape arity positions
    | Array.any invalid positions = pure Nothing
    | otherwise = do
        atArity <- maybe (pure NotShaped) shapeAt (Array.index positions arity)
        case atArity of
          Shaped (Right s) -> pure (Just s)
          Shaped (Left p) -> problem p
          NotShaped -> do
            shapes <- traverse shapeAt positions
            problem case Array.findIndex isShaped shapes of
              Just k -> HandlerParameters arity k
              Nothing -> HandlerShape
  problem p = report (typeRange t) (HandledEffect p) $> Nothing
  isShaped = case _ of
    Shaped _ -> true
    NotShaped -> false
  invalid p = case p.at of
    SurfaceAt (TypeInvalid _) -> true
    _ -> false

-- | A position on the spine of a handler declaration's signature: the type
-- | there, and the type variables the quantifiers before it bind. Past a
-- | synonym, the type is its body, read in the surface or, for an imported
-- | one, in Core, and the quantifiers in it bind nothing the declaration sees.
type SpinePosition = { at :: SpineType, scope :: Array TypeVar, throughSynonym :: Boolean }

data SpineType
  = SurfaceAt Type
  | CoreAt Core.Type

-- | The positions of a signature's spine: the type at its top, then the one
-- | after each pure arrow but that of a synthesized parameter, each past its
-- | quantifiers, constraints, synthesized parameters, and kind annotations,
-- | and with a synonym without parameters standing there read as its body.
spinePositions :: Type -> Resolve (Array SpinePosition)
spinePositions t = go [] Set.empty { at: SurfaceAt t, scope: [], throughSynonym: false }
  where
  go acc expanding p = settle expanding p >>= \s -> do
    let acc' = Array.snoc acc s.position
    case s.position.at of
      SurfaceAt (TypeFunction _ _ rest Nothing) -> go acc' s.expanding s.position { at = SurfaceAt rest }
      CoreAt ct | Just f <- coreFunction ct, f.row == Core.TRowEmpty -> go acc' s.expanding s.position { at = CoreAt f.result }
      _ -> pure acc'
  settle expanding p = case p.at of
    SurfaceAt (TypeForall _ bs body) ->
      settle expanding p { at = SurfaceAt body, scope = if p.throughSynonym then p.scope else p.scope <> scopeOf bs }
    SurfaceAt (TypeConstrained _ _ body) -> settle expanding p { at = SurfaceAt body }
    SurfaceAt (TypeKinded _ body _) -> settle expanding p { at = SurfaceAt body }
    SurfaceAt (TypeFunction _ (TypeSynthesized _ _ _ _ _) body Nothing) -> settle expanding p { at = SurfaceAt body }
    SurfaceAt (TypeSynonym _ q) | not (Set.member q expanding) ->
      synonymBody q >>= case _ of
        Just (OwnSynonym body) -> do
          b <- speculatively (resolveType body)
          settle (Set.insert q expanding) p { at = SurfaceAt b, throughSynonym = true }
        Just (ImportedSynonym body) -> settle (Set.insert q expanding) p { at = CoreAt body, throughSynonym = true }
        Nothing -> pure { position: p, expanding }
    CoreAt (Core.TForall _ _ body) -> settle expanding p { at = CoreAt body }
    CoreAt (Core.TConstrained _ body) -> settle expanding p { at = CoreAt body }
    _ -> pure { position: p, expanding }

-- | What stands at a position of the spine: a handler's type, with the effect
-- | it handles and its targets or why neither is read, or something else.
data SpineShape
  = NotShaped
  | Shaped (Either HandledEffectProblem { handled :: Qualified EffName, targets :: Maybe (Array EffectApplication) })

-- | Whether the type at a position of the spine is a handler's: `E ~> ( t̄ )`,
-- | or a function from a thunk `Unit -> α / ρ` to a result, under `/ ρ'` or
-- | pure. A handler's handles `E`, or the one element `ρ` holds and `ρ'` does
-- | not, and its targets are those of a `~>` the signature writes itself.
-- |
-- | A row is read as written, `{| … |}`, or as a type synonym without
-- | parameters names it, a kind annotation around either aside, and a spread
-- | contributes what the row it names holds: a synonym's, or none where it is
-- | a variable or left open. Elements are told apart by their keys, the effect
-- | or the label.
shapeAt :: SpinePosition -> Resolve SpineShape
shapeAt p = case p.at of
  SurfaceAt (TypeCapability _ source targets) ->
    pure (Shaped (Right { handled: source.effect, targets: if p.throughSynonym then Nothing else Just targets }))
  SurfaceAt (TypeFunction _ (TypeFunction _ (TypeConstructor _ u) _ (Just thunk)) _ residual) | u == unitTy -> do
    source <- rowKeys Set.empty thunk
    result <- maybe (pure (Just [])) (rowKeys Set.empty) residual
    pure (Shaped (removed source result))
  CoreAt ct
    | Just f <- coreFunction ct
    , Just thunk <- coreFunction f.argument
    , Core.TCon u _ <- thunk.argument
    , u == unitTy -> pure (Shaped (removed (coreKeys thunk.row) (coreKeys f.row)))
  _ -> pure NotShaped
  where
  removed source result = case source, result of
    Just s, Just res -> case Array.difference (Array.nub s) res of
      [ Left e ] -> Right { handled: e, targets: Nothing }
      [ Right l ] -> Left (HandlesInstance l)
      [] -> Left HandlesNothing
      _ -> Left HandlesSeveral
    _, _ -> Left HandlerShape

-- | A function type of Core, `τ -{ρ}-> τ'`, taken apart.
coreFunction :: Core.Type -> Maybe { argument :: Core.Type, row :: Core.Type, result :: Core.Type }
coreFunction = case _ of
  Core.TApp (Core.TApp (Core.TApp (Core.TCon f _) argument) row) result
    | f == functionTy -> Just { argument, row, result }
  _ -> Nothing

-- | The key of an element of an effect row: the effect, or the label of an
-- | instance.
type RowKey = Either (Qualified EffName) String

-- | The keys a row holds, where it is read: a row written out, or one a
-- | synonym without parameters names. The synonyms being expanded are
-- | carried, and one naming itself is not read.
rowKeys :: Set (Qualified TyName) -> Type -> Resolve (Maybe (Array RowKey))
rowKeys expanding = case _ of
  TypeEffectRow _ items -> map Array.concat <<< sequence <$> traverse item items
  TypeSynonym _ q -> synonymKeys expanding q
  TypeKinded _ inner _ -> rowKeys expanding inner
  _ -> pure Nothing
  where
  item = case _ of
    EffectElement a -> pure (Just [ Left a.effect ])
    EffectInstance _ (Symbol l) _ -> pure (Just [ Right l ])
    EffectSpread _ Nothing -> pure (Just [])
    EffectSpread _ (Just s) -> case s of
      TypeVariable _ _ -> pure (Just [])
      TypeWildcard _ -> pure (Just [])
      _ -> rowKeys expanding s

synonymKeys :: Set (Qualified TyName) -> Qualified TyName -> Resolve (Maybe (Array RowKey))
synonymKeys expanding q
  | Set.member q expanding = pure Nothing
  | otherwise =
      synonymBody q >>= case _ of
        Just (OwnSynonym body) -> speculatively (resolveType body) >>= rowKeys (Set.insert q expanding)
        Just (ImportedSynonym body) -> pure (coreKeys body)
        Nothing -> pure Nothing

-- | The keys a row of Core holds.
coreKeys :: Core.Type -> Maybe (Array RowKey)
coreKeys = case _ of
  Core.TRowEmpty -> Just []
  Core.TRowExtend entry rest -> Array.cons <$> entryKey entry <*> coreKeys rest
  Core.TRowUnion a b -> (<>) <$> coreKeys a <*> coreKeys b
  Core.TVar _ -> Just []
  _ -> Nothing
  where
  entryKey = case _ of
    Core.RowEffectEntry e _ -> Just (Left e)
    Core.RowLabelledEffectEntry (Symbol l) _ _ -> Just (Right l)
    _ -> Nothing

-- | A handler's body: its clauses in the order written, over the cells of the
-- | handling expression or handler declaration it belongs to. An operation
-- | clause sees those cells open and the return clause sees them closed.
-- |
-- | A clause names an operation of the effect handled where that is known,
-- | and otherwise one in scope, which decides the effect. A clause whose
-- | operation is not decided, one with other than a pattern per argument, and
-- | a second clause for one operation or a second return clause are reported
-- | where the problem is not reported already, and left out.
-- | The operations of the effect no clause names, a clause left out above still
-- | naming its operation, are reported together at the range given: a group's
-- | head, or a declaration's signature.
-- |
-- | An effect that declares no operations has no handler: it is reported at
-- | that range ahead of the clauses, which are then read as against an effect
-- | not known.
handlerBody :: Handles -> CST.SourceRange -> Array CellVar -> HandlerSource -> Resolve { effect :: Maybe (Qualified EffName), body :: HandlerBody }
handlerBody handles missingAt cells h = case handles of
  HandlesEffect e -> declaresNoOperations e >>= case _ of
    true -> do
      report missingAt (EffectWithoutOperations (effectWord e))
      clausesAgainst HandlesUnknown missingAt cells h
    false -> clausesAgainst handles missingAt cells h
  _ -> clausesAgainst handles missingAt cells h

-- | A handler's body read against what it handles, as `handlerBody` reads one.
clausesAgainst :: Handles -> CST.SourceRange -> Array CellVar -> HandlerSource -> Resolve { effect :: Maybe (Qualified EffName), body :: HandlerBody }
clausesAgainst handles missingAt cells h = do
  heads <- traverse (operationHead <<< _.clause) h
  let
    resolvedHeads = Array.catMaybes heads
    effect = case handles of
      HandlesEffect e -> Just e
      HandlesLabel _ -> map _.op.effect (Array.head resolvedHeads)
      HandlesUnknown -> Nothing
  case handles of
    HandlesLabel l | Array.null (Array.mapMaybe operationName h) -> report l.range (LabelledGroupEmpty l.name)
    _ -> pure unit
  -- A group headed by a label handles the effect of its first operation, and
  -- a clause for another is reported and left out.
  checked <- for heads case _ of
    Just hd | Just e <- effect, hd.op.effect /= e -> do
      report hd.at (OperationOfOtherEffect hd.written (effectWord hd.op.effect) (effectWord e))
      pure Nothing
    other -> pure other
  -- every operation of the effect has a clause naming it, whatever else is
  -- wrong with the clause
  for_ effect \e -> do
    ops <- operationsOf e
    let
      named = map _.name (Array.catMaybes checked)
      missing = Array.filter (\op -> not (Array.elem (qualifiedLike e op.name) named)) ops
    unless (Array.null missing) (report missingAt (ClauseMissing (effectWord e) (map (\{ name: Ident n } -> n) missing)))
  ctx <- context
  acc <- foldM (clause ctx cells) { operations: [], seen: [], return: Nothing }
    (Array.zip h checked)
  pure
    { effect
    , body:
        { operations: acc.operations
        , return: acc.return
        }
    }
  where
  operationName = case _ of
    { clause: CST.ClauseOperation _ n _ _ } -> Just n
    _ -> Nothing

  operationHead = case _ of
    CST.ClauseOperation _ n _ _ -> case handles of
      HandlesEffect e | n.qualifier == Nothing -> do
        ops <- operationsOf e
        case Array.find (\op -> op.name == Ident n.name) ops of
          Just op -> pure (Just { at: n.range, written: written n, name: qualifiedLike e op.name, op: { effect: e, arity: op.arity } })
          Nothing -> report n.range (NotAnOperationOf n.name (effectWord e)) $> Nothing
      HandlesUnknown -> pure Nothing
      _ -> inScope n
    CST.ClauseReturn _ _ -> pure Nothing

  -- An operation in scope, a global named by the clause; for a group whose
  -- effect is known, one of that effect.
  inScope n = lookupValue n >>= case _ of
    Found q -> operationOf q >>= case _ of
      Just op -> case handles of
        HandlesEffect e | op.effect /= e -> report n.range (NotAnOperationOf (written n) (effectWord e)) $> Nothing
        _ -> pure (Just { at: n.range, written: written n, name: q, op })
      Nothing -> unknown
    NotFound -> unknown
    Ambiguous -> report n.range (AmbiguousValue (written n)) $> Nothing
    where
    unknown = case handles of
      HandlesEffect e -> report n.range (NotAnOperationOf (written n) (effectWord e)) $> Nothing
      _ -> report n.range (UnknownOperation (written n)) $> Nothing

  clause ctx opened acc (Tuple { block, clause: written' } hd) = case written' of
    CST.ClauseOperation m n bs body -> do
      let marker = fromMaybe CST.Full (maybe block Just m)
      when (marker == CST.ReifiableFull && not ctx.continuation) (report n.range ContinuationNotImported)
      r <- resolveBinders bs
      traverse_ requireIrrefutable r.binders
      body' <- withValues r.bound (withCells opened (withResume (resumeIn marker) (resolveExpr body)))
      let continuation = marker == CST.ReifiableFull
      case hd of
        Nothing -> pure acc
        Just h'
          | Array.length bs /= h'.op.arity + (if continuation then 1 else 0) -> do
              report n.range (ClauseArity h'.written h'.op.arity (Array.length bs) continuation)
              pure acc
          | Array.elem h'.name acc.seen -> report n.range (ClauseTwice h'.written) $> acc
          | otherwise -> do
              let
                form = case marker of
                  CST.Full -> ClauseFull
                  CST.Fast -> ClauseFast
                  CST.ReifiableFull -> maybe ClauseFull ClauseReifiable (Array.last r.binders)
                arguments = if continuation then fromMaybe [] (Array.init r.binders) else r.binders

                operation :: OperationClause
                operation = { origin: originOf (covering n.range (exprRange body)), operation: h'.name, form, arguments, body: body' }
              pure acc { operations = Array.snoc acc.operations operation, seen = Array.snoc acc.seen h'.name }
    CST.ClauseReturn b body -> do
      r <- resolveBinders [ b ]
      traverse_ requireIrrefutable r.binders
      body' <- withValues r.bound (withCellsClosed InReturnClause opened (resolveExpr body))
      case acc.return, Array.head r.binders of
        Just _, _ -> report (binderRange b) ReturnTwice $> acc
        Nothing, Just b' -> pure acc { return = Just { origin: originOf (covering (binderRange b) (exprRange body)), binder: b', body: body' } }
        Nothing, Nothing -> pure acc

  resumeIn = case _ of
    CST.Full -> ResumeAvailable
    CST.Fast -> ResumeBlocked InFastClause
    CST.ReifiableFull -> ResumeBlocked InReifiableClause

  qualifiedLike (Qualified owner _) i = Qualified owner i

effectWord :: Qualified EffName -> String
effectWord (Qualified _ (EffName e)) = e

cellRange :: CellSource -> CST.SourceRange
cellRange d = covering d.name.range (exprRange d.value)

clauseRange :: CST.Clause -> CST.SourceRange
clauseRange = case _ of
  CST.ClauseOperation _ n _ body -> covering n.range (exprRange body)
  CST.ClauseReturn b body -> covering (binderRange b) (exprRange body)

written :: CST.Name -> String
written n = maybe n.name (\q -> q <> "." <> n.name) n.qualifier
