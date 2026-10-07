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
-- | **A handler's cells are in scope in its operation clauses**, and closed in
-- | its initial values and its return clause, where a reference to one is
-- | reported as such. A clause names an operation of the effect its handler
-- | handles, looked up among that effect's operations whatever the imports
-- | bring; a group headed by a label handles the effect of the operations in
-- | scope its clauses name.
-- |
-- | **`resume` stands applied, in the immediate body of a `full` clause**: not
-- | inside a lambda, a local function, or a handling expression there, each of
-- | which could keep it beyond the clause
-- | ([Effect Handlers](../../../../docs/technical-references/02-Surface-Language/02-Effect-Handlers.md)).
-- |
-- | The forms whose resolution belongs to a later part are reported as not
-- | supported yet: the anonymous argument `_` and the sections and `case _ of`
-- | it makes, and a macro call.
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
import Data.Foldable (foldM, foldl, traverse_)
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.String.CodeUnits as CodeUnits
import Data.String.CodePoints (toCodePointArray)
import Data.Set (Set)
import Data.Set as Set
import Data.Traversable (for, sequence, traverse)
import Data.Tuple (Tuple(..))
import Stella.Compiler.CST.Range (binderRange, covering, exprRange, letBindingRange, nonEmpty, typeRange)
import Stella.Compiler.CST.Types as CST
import Stella.Compiler.Resolve.Binder (Member(..), ResolvedMember(..), requireIrrefutable, resolveAlternative, resolveBinders, resolveCells, resolveGroup)
import Stella.Compiler.Resolve.Fixity (rebracket)
import Stella.Compiler.Resolve.Group (GroupError(..), LocalBinding(..), groupBindings)
import Stella.Compiler.Resolve.Label (reportLabelsTwice)
import Stella.Compiler.Interface.Environment (reachable)
import Stella.Compiler.Macro.Bundle (syntaxModuleName)
import Stella.Compiler.Resolve.Quotation (quotation)
import Stella.Compiler.Resolve.Monad (Cell(..), CellClosure(..), Found(..), HandledEffectProblem(..), Resolve, SynonymBody(..), ResolveReason(..), ResumeBlock(..), ResumeState(..), TypeReference(..), ValueKind(..), ValueReference(..), blockResume, context, lookupCell, lookupOperator, lookupType, lookupValue, lookupValueReference, openedBy, operationOf, operationsOf, report, resumeState, speculatively, synonymBody, valueKind, withCells, withCellsClosed, withOpened, withResume, withTypeVariables, withValues)
import Stella.Compiler.Resolve.Type (handlerScope, resolveHandlerSignature, resolveSignature, resolveType, signatureScope)
import Stella.Compiler.Surface.Decl (Associativity(..))
import Stella.Compiler.Surface.Expr (AlternativeBody(..), Binder, ClauseForm(..), Expr(..), Group, GuardLine(..), HandlerBody, HandlerItem(..), LetBinding(..), OperationClause, RecordField(..), exprOrigin)
import Stella.Compiler.Surface.Name (CellVar)
import Stella.Compiler.Surface.Origin (Origin, originOf, spanning)
import Stella.Compiler.Surface.Type (EffectRowItem(..), HandlerSignature(..), Signature, Type(..))
import Stella.Compiler.TypedCore.Domain (scalarString, scalarValue)
import Stella.Compiler.TypedCore.Name (EffName(..), Ident(..), Qualified(..), Symbol(..), Tag(..), TyName)
import Stella.Compiler.TypedCore.Prim (unitCtor, unitTy)
import Stella.Compiler.TypedCore.Term (Literal(..))
import Stella.Compiler.TypedCore.Type as Core

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
  CST.ExprApp f a -> case unparenthesized f of
    CST.ExprResume r -> ExprApp o <$> resumeAt r <*> resolveExpr a
    _ -> ExprApp o <$> resolveExpr f <*> resolveExpr a
  CST.ExprOp _ _ _ -> operatorChain e
  CST.ExprTyped inner t -> ExprTyped o <$> resolveExpr inner <*> resolveType t
  CST.ExprAccess inner labels -> do
    inner' <- resolveExpr inner
    pure (foldl (\acc l -> ExprSelect (spanning (exprOrigin acc) (originOf l.range)) acc (Symbol l.name)) inner' labels)
  CST.ExprLambda bs body -> blockResume InsideLambda do
    r <- resolveBinders bs
    traverse_ requireIrrefutable r.binders
    ExprLambda o r.binders <$> withValues r.bound (resolveExpr body)
  CST.ExprLet items body -> resolveLet o items (resolveExpr body)
  CST.ExprCase scrutinees alternatives -> do
    scrutinees' <- traverse scrutinee scrutinees
    ExprCase o scrutinees' <$> traverse alternative alternatives
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
  CST.ExprCellWrite n v -> do
    c <- cell n
    v' <- resolveExpr v
    pure (maybe (ExprInvalid o) (\c' -> ExprCellWrite o c' v') c)
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

  scrutinee = case _ of
    CST.ExprSection r -> report r (NotYetSupported "`case _ of`") $> ExprInvalid (originOf r)
    s -> resolveExpr s

  handling items inner = do
    items' <- Array.catMaybes <$> traverse handlerItem items
    ExprHandle o items' <$> resolveExpr inner
  handlerItem = case _ of
    CST.ListHandler h -> Just <<< HandlerApplied <$> resolveExpr h
    CST.ListGroup g -> map HandlerGroup <$> group g

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
  traverse field fields
  where
  labelOf = case _ of
    CST.FieldValue n _ -> Just n
    CST.FieldPun n -> Just n
    CST.FieldUpdate n _ -> Just n
    CST.FieldSpread _ -> Nothing
  field = case _ of
    CST.FieldValue n v -> FieldValue (originOf (covering n.range (exprRange v))) (Symbol n.name) <$> resolveExpr v
    CST.FieldPun n -> FieldValue (originOf n.range) (Symbol n.name) <$> reference (originOf n.range) n
    CST.FieldUpdate n v -> FieldUpdate (originOf (covering n.range (exprRange v))) (Symbol n.name) <$> resolveExpr v
    CST.FieldSpread v -> FieldSpread (originOf (exprRange v)) <$> resolveExpr v

alternative :: CST.CaseAlternative -> Resolve { origin :: Origin, patterns :: Array (Array Binder), body :: AlternativeBody }
alternative alt = do
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

unparenthesized :: CST.Expr -> CST.Expr
unparenthesized = case _ of
  CST.ExprParens inner -> unparenthesized inner
  e -> e

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

-- | A handler's cells and clauses as written, each clause with the marker of
-- | the block it stands in.
type HandlerSource =
  { cells :: Array { name :: CST.Name, value :: CST.Expr }
  , clauses :: Array { block :: Maybe CST.Marker, clause :: CST.Clause }
  }

-- | A group written in place. A head written as a type name is the effect it
-- | handles, and one written as a value name is a label; a group headed by a
-- | label handles the effect its operations belong to. A group whose effect
-- | is not decided is left out, what decided it not being reported again.
group
  :: { head :: CST.Name, marker :: Maybe CST.Marker, cells :: Array { name :: CST.Name, value :: CST.Expr }, clauses :: Array CST.Clause }
  -> Resolve (Maybe Group)
group g = do
  handles <-
    if isLabel g.head then pure (HandlesLabel g.head)
    else lookupType g.head >>= case _ of
      Found (EffectReference e) -> pure (HandlesEffect e)
      Found _ -> report g.head.range (NotAnEffect (written g.head)) $> HandlesUnknown
      NotFound -> report g.head.range (UnknownType (written g.head)) $> HandlesUnknown
      Ambiguous -> report g.head.range (AmbiguousType (written g.head)) $> HandlesUnknown
  r <- handlerBody handles { cells: g.cells, clauses: map { block: g.marker, clause: _ } g.clauses }
  pure $ r.effect <#> \effect ->
    { origin: originOf (nonEmpty ([ g.head.range ] <> map cellRange g.cells <> map clauseRange g.clauses))
    , label: if isLabel g.head then Just (Symbol g.head.name) else Nothing
    , effect
    , body: r.body
    }
  where
  isLabel n = n.qualifier == Nothing && case CodeUnits.charAt 0 n.name of
    Just c -> not (c >= 'A' && c <= 'Z')
    Nothing -> false

-- | A handler declaration's parts: its parameters, its signature, the effect
-- | it handles, and its body. The type variables of the signature are in
-- | scope in the parameters and the body, and the parameters, one binding
-- | group of irrefutable patterns, in every initial value and clause.
resolveHandler
  :: Array CST.Binder
  -> CST.Type
  -> Array CST.HandlerItem
  -> Resolve
       { params :: Array Binder
       , signature :: Signature HandlerSignature
       , effect :: Maybe (Qualified EffName)
       , body :: HandlerBody
       }
resolveHandler params t items = do
  signature <- resolveHandlerSignature t
  withTypeVariables (handlerScope signature) do
    effect <- case signature.body of
      Capability c -> pure (Just c.source.effect)
      General g -> handledBy (typeRange t) g
    r <- resolveBinders params
    traverse_ requireIrrefutable r.binders
    source <- declared items
    body <- withValues r.bound (handlerBody (maybe HandlesUnknown HandlesEffect effect) source)
    pure { params: r.binders, signature, effect, body: body.body }
  where
  -- Every `var` stands ahead of the clauses; one after them is reported and
  -- left out.
  declared = foldM step { cells: [], clauses: [] }
  step acc = case _ of
    CST.HandlerCell n v
      | Array.null acc.clauses -> pure acc { cells = Array.snoc acc.cells { name: n, value: v } }
      | otherwise -> report n.range (CellAfterClause n.name) $> acc
    CST.HandlerClauses m cs -> pure acc { clauses = acc.clauses <> map { block: m, clause: _ } cs }

-- | The effect a signature written in full handles: past its quantifiers,
-- | constraints, and synthesized arguments, it is a function from a thunk
-- | `Unit -> α / ρ` to a result, under `/ ρ'` or pure, and the effect is the
-- | one element `ρ` holds and `ρ'` does not.
-- |
-- | A row is read as written, `{| … |}`, or as a type synonym without
-- | parameters names it, a kind annotation around either aside, and a spread contributes what the row it names holds:
-- | a synonym's, or none where it is a variable or left open. Elements are
-- | told apart by their keys, the effect or the label.
handledBy :: CST.SourceRange -> Type -> Resolve (Maybe (Qualified EffName))
handledBy r t = case afterSpine t of
  TypeInvalid _ -> pure Nothing
  TypeFunction _ (TypeFunction _ (TypeConstructor _ u) _ (Just thunk)) _ residual | u == unitTy -> do
    source <- rowKeys Set.empty thunk
    result <- maybe (pure (Just [])) (rowKeys Set.empty) residual
    case source, result of
      Just s, Just res -> case Array.difference (Array.nub s) res of
        [ Left e ] -> pure (Just e)
        [ Right l ] -> problem (HandlesInstance l)
        [] -> problem HandlesNothing
        _ -> problem HandlesSeveral
      _, _ -> problem HandlerShape
  _ -> problem HandlerShape
  where
  problem p = report r (HandledEffect p) $> Nothing
  afterSpine = case _ of
    TypeForall _ _ body -> afterSpine body
    TypeConstrained _ _ body -> afterSpine body
    TypeFunction _ (TypeSynthesized _ _ _ _) body Nothing -> afterSpine body
    other -> other

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
      where
      coreKeys = case _ of
        Core.TRowEmpty -> Just []
        Core.TRowExtend entry rest -> Array.cons <$> entryKey entry <*> coreKeys rest
        Core.TRowUnion a b -> (<>) <$> coreKeys a <*> coreKeys b
        Core.TVar _ -> Just []
        _ -> Nothing
      entryKey = case _ of
        Core.RowEffectEntry e _ -> Just (Left e)
        Core.RowLabelledEffectEntry (Symbol l) _ _ -> Just (Right l)
        _ -> Nothing

-- | A handler's body: its cells, one binding group, then its clauses in the
-- | order written. An initial value and the return clause see the handler's
-- | cells closed, and an operation clause sees them open; a cell of the
-- | handler hides one of its name outside it either way.
-- |
-- | A clause names an operation of the effect handled where that is known,
-- | and otherwise one in scope, which decides the effect. A clause whose
-- | operation is not decided, one with other than a pattern per argument, and
-- | a second clause for one operation or a second return clause are reported
-- | where the problem is not reported already, and left out.
handlerBody :: Handles -> HandlerSource -> Resolve { effect :: Maybe (Qualified EffName), body :: HandlerBody }
handlerBody handles h = do
  c <- resolveCells (map _.name h.cells)
  initials <- withCellsClosed InInitialValue c.bound (traverse (resolveExpr <<< _.value) h.cells)
  heads <- traverse (operationHead <<< _.clause) h.clauses
  let
    resolvedHeads = Array.catMaybes heads
    effect = case handles of
      HandlesEffect e -> Just e
      HandlesLabel _ -> map _.op.effect (Array.head resolvedHeads)
      HandlesUnknown -> Nothing
  case handles of
    HandlesLabel l | Array.null (Array.mapMaybe operationName h.clauses) -> report l.range (LabelledGroupEmpty l.name)
    _ -> pure unit
  -- A group headed by a label handles the effect of its first operation, and
  -- a clause for another is reported and left out.
  checked <- for heads case _ of
    Just hd | Just e <- effect, hd.op.effect /= e -> do
      report hd.at (OperationOfOtherEffect hd.written (effectWord hd.op.effect) (effectWord e))
      pure Nothing
    other -> pure other
  ctx <- context
  acc <- foldM (clause ctx c.bound) { operations: [], seen: [], return: Nothing }
    (Array.zip h.clauses checked)
  pure
    { effect
    , body:
        { cells: Array.zipWith (\(Tuple d initial) var -> { origin: originOf (cellRange d), cell: var, initial }) (Array.zip h.cells initials) c.cells
        , operations: acc.operations
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

  clause ctx cells acc (Tuple { block, clause: written' } hd) = case written' of
    CST.ClauseOperation m n bs body -> do
      let marker = fromMaybe CST.Full (maybe block Just m)
      when (marker == CST.ReifiableFull && not ctx.continuation) (report n.range ContinuationNotImported)
      r <- resolveBinders bs
      traverse_ requireIrrefutable r.binders
      body' <- withValues r.bound (withCells cells (withResume (resumeIn marker) (resolveExpr body)))
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
      body' <- withValues r.bound (withCellsClosed InReturnClause cells (resolveExpr body))
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

cellRange :: { name :: CST.Name, value :: CST.Expr } -> CST.SourceRange
cellRange d = covering d.name.range (exprRange d.value)

clauseRange :: CST.Clause -> CST.SourceRange
clauseRange = case _ of
  CST.ClauseOperation _ n _ body -> covering n.range (exprRange body)
  CST.ClauseReturn b body -> covering (binderRange b) (exprRange body)

written :: CST.Name -> String
written n = maybe n.name (\q -> q <> "." <> n.name) n.qualifier
