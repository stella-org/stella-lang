-- | The kernel's builders of `perform`, `handle`, `region`, and cells.
-- |
-- | **The kernel does not follow the ambient row.** A `perform` is given the
-- | element it performs on — its key and its payload, `E τ̄` — as a protocol
-- | annotation from which the operation's types are read, and a handler is given
-- | its answer type and its residual row where it is opened, which the types of
-- | its continuations need before any clause is built. Every one of these is
-- | judged well-formed and checked against the effect's declaration; that the
-- | element is in the row the term stands at is the Core type checker's.
-- |
-- | **A handler's clauses are opened together and closed together**, under one
-- | binder, in the order given: the return clause's scope binds the result of the
-- | handled computation, and each operation clause's binds the operation's type
-- | variables, its argument, and, for a `full` clause, its continuation. All of
-- | them jump to no join point outside, as an abstraction's body does not; and
-- | the handled computation, which runs inside the handler, jumps to none either.
-- |
-- | **A region is a binder** (D36). Its body scope binds a fresh region name with
-- | the layout given, and `readCell` and `writeCell` name the region by its
-- | binder, so a cell is reached in any scope the region stands around and in no
-- | other. That the region is in the row the term stands at is the Core type
-- | checker's.
module Stella.Compiler.Elaborate.Kernel.Builder.Handler
  ( perform
  , openHandle
  , closeHandle
  , openRegion
  , closeRegion
  , readCell
  , writeCell
  ) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.Kernel.Builder.Common (abstractedChild, built, childWith, closedOver, closedOverParts, inheritingChild, issueTerm, kinded, rejected, substitutedAt, usableIn, usableTermIn, valueType)
import Stella.Compiler.Elaborate.CorePlus.Context (XContext, bindRegion, bindTyVar, bindVar)
import Stella.Compiler.Elaborate.Vocabulary.Diagnostic (BuildError(..), Defect(..))
import Stella.Compiler.Elaborate.Environment.Effects (EffectShape, OperationShape, lookupEffect)
import Stella.Compiler.Elaborate.Kernel.Elab (Elab, askEnv, break, currentMetas, freshBinderName, freshIdent, freshRegionName, holdOpen, issue, resolveBinder, resolveExpr, resolveScope)
import Stella.Compiler.Elaborate.Vocabulary.Handle (BinderObject(..), Handle, HandleObject(..), ScopeId, ScopeObject)
import Stella.Compiler.Elaborate.CorePlus.Kind (XKind(..))
import Stella.Compiler.Elaborate.Mechanism.Kinding (KindEvidence(..), checkKind, wellFormedKey)
import Stella.Compiler.Elaborate.CorePlus.Term (XCell, XExpr(..), XOpClause(..), freeVarsOf)
import Stella.Compiler.Elaborate.CorePlus.Type (XRowEntry(..), XType(..), freeRegions)
import Stella.Compiler.Elaborate.Mechanism.Unify (substitute)
import Stella.Compiler.Elaborate.Vocabulary.View (PayloadView(..))
import Stella.Compiler.TypedCore (EffName, Ident, OpName, Qualified, RegionName, RowElemKind(..), RowKey(..), TyVar(..))
import Stella.Compiler.TypedCore.Prim (functionTy, unitTy)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))

-- | `perform k.op [σ̄] e`, claimed at what the operation resumes with, its
-- | effect's parameters and its own type binders instantiated.
-- |
-- | The key and the payload are the element the term performs on, `E τ̄`,
-- | related as a row element's are: `EffectKey E` over an unlabelled `E τ̄`, a
-- | `SymbolKey` over a labelled one. The element is kinded, the operation must be
-- | one `E` declares, and `σ̄` as many as it binds, each at its kind; what `e` is
-- | claimed at is the Core type checker's.
perform :: Handle -> RowKey -> PayloadView -> OpName -> P.Array Handle -> Handle -> Elab Handle
perform scopeHandle key payload op typeArgHandles argumentHandle = do
  scope <- resolveScope scopeHandle
  element <- elementIn scope key payload
  effect <- effectShape element.effect
  operation <- operationOf element.effect effect op
  when (Array.length typeArgHandles /= Array.length operation.tyBinders)
    (rejected (OperationArity op (Array.length operation.tyBinders) (Array.length typeArgHandles)))
  typeArgs <- traverse (usableIn scope) typeArgHandles
  env <- askEnv
  metas <- currentMetas
  for_ (Array.zip operation.tyBinders typeArgs) \(Tuple b arg) ->
    case checkKind env.session.kinding { kindVars: scope.context.kindVars, tyVars: scope.context.tyVars, regions: Map.keys scope.context.regions } metas b.kind arg.type of
      Left fault -> rejected (IllKinded fault)
      Right _ -> pure unit
  argument <- usableTermIn scope argumentHandle
  let
    typeArgTypes = map (substitute metas <<< _.type) typeArgs
  resumes <- substitutedAt scope
    ( Map.fromFoldable
        (Array.zip (map _.name effect.params) element.args <> Array.zip (map _.name operation.tyBinders) typeArgTypes)
    )
    operation.resumesWith
  issueTerm scope (EPerform unit key op typeArgTypes argument.term) resumes

-- | Open `handle e with h`: a binder, the return clause's scope and the variable
-- | it binds, and for each operation, in the order given, its clause's scope and
-- | what it binds.
-- |
-- | `e` is a term the scope may use, jumping to no join point. The element is
-- | judged as `perform` judges one; the clauses name every operation its effect
-- | declares, once each, and `full` ones bind a continuation. `β` is a type the
-- | scope may use at `Type`, and `ρ` one at `Row Effect`, which every clause
-- | stands at. The names are the host's, fresh where they are bound.
openHandle
  :: Handle
  -> Handle
  -> RowKey
  -> PayloadView
  -> Handle
  -> Handle
  -> P.Array { op :: OpName, full :: P.Boolean }
  -> Elab
       { binder :: Handle
       , returnClause :: { variable :: Handle, scope :: Handle }
       , clauses ::
           P.Array
             { typeVariables :: P.Array Handle
             , argument :: Handle
             , continuation :: Maybe Handle
             , scope :: Handle
             }
       }
openHandle scopeHandle computationHandle key payload answerHandle residualHandle clausesGiven = do
  scope <- resolveScope scopeHandle
  computation <- usableTermIn scope computationHandle
  unless (Set.isEmpty (freeVarsOf computation.term).joins) (rejected (JoinOutOfScope computationHandle))
  element <- elementIn scope key payload
  effect <- effectShape element.effect
  answer <- valueType scope answerHandle
  residualObject <- usableIn scope residualHandle
  case residualObject.kind of
    ExactKind (XKRow RowEffect) -> pure unit
    AnyRow -> pure unit
    _ -> rejected (NotAnEffectRow residualHandle)
  let
    residual = residualObject.type
    ops = map _.op clausesGiven
  for_ (Array.findIndex (\op -> Array.length (Array.filter (_ == op) ops) > 1) ops) \i ->
    for_ (Array.index ops i) \op -> rejected (DuplicateClause op)
  operations <- traverse (\c -> operationOf element.effect effect c.op) clausesGiven
  for_ (Map.keys effect.operations) \op ->
    unless (Array.elem op ops) (rejected (MissingClause op))
  hub <- inheritingChild scope scope.context
  returnName <- freshIdent (Map.keys scope.context.vars) "x"
  returnScope <- childWith hub (bindVar scope.context returnName computation.claimed) Map.empty Nothing
  clauses <- traverse
    (\(Tuple given operation) -> openClause scope hub scope.context residual answer element.args effect given operation)
    (Array.zip clausesGiven operations)
  binder <- issue
    ( BinderObject
        ( HandleBinder
            { computation: computation.term
            , element: element.entry
            , answer
            , residual
            , returnClause: { name: returnName, type: computation.claimed, scope: returnScope.id }
            , clauses: map _.record clauses
            , parent: scope.id
            , body: hub.id
            }
        )
    )
  holdOpen hub.id hub.ancestors
  returnVariable <- issueTerm returnScope (EVar unit returnName) computation.claimed
  returnScopeHandle <- issue (ScopeObject returnScope)
  handles <- traverse issueClause clauses
  pure { binder, returnClause: { variable: returnVariable, scope: returnScopeHandle }, clauses: handles }

-- | Close a handler opened in this scope with the return clause's body and one
-- | body for each operation clause in the order opened, claimed at the answer
-- | type.
-- |
-- | Each body is visible under its own clause and jumps to no join point.
closeHandle :: Handle -> Handle -> Handle -> P.Array Handle -> Elab Handle
closeHandle scopeHandle binderHandle returnHandle clauseHandles = do
  scope <- resolveScope scopeHandle
  resolveBinder binderHandle >>= case _ of
    HandleBinder b -> do
      when (Array.length clauseHandles /= Array.length b.clauses)
        (rejected (ClauseCount binderHandle (Array.length b.clauses) (Array.length clauseHandles)))
      returnBody <- resolveExpr returnHandle
      clauseBodies <- traverse resolveExpr clauseHandles
      closedOverParts scope binderHandle b
        ( [ { within: b.returnClause.scope, builtIn: returnBody.builtIn, handle: returnHandle } ]
            <> Array.zipWith (\c (Tuple h body) -> { within: c.scope, builtIn: body.builtIn, handle: h }) b.clauses (Array.zip clauseHandles clauseBodies)
        )
      for_ (Array.zip ([ returnHandle ] <> clauseHandles) ([ returnBody ] <> clauseBodies)) \(Tuple h body) ->
        unless (Set.isEmpty (freeVarsOf body.term).joins) (rejected (JoinOutOfScope h))
      let
        handler =
          { element: b.element
          , returnClause: { binder: b.returnClause.name, ty: b.returnClause.type, body: returnBody.term }
          , opClauses: Array.zipWith clauseOf b.clauses clauseBodies
          }
      issueTerm scope (EHandle unit b.computation handler) b.answer
    RegionBinder _ -> misuse binderHandle
    ForallBinder _ -> misuse binderHandle
    AssumedConstraint _ -> misuse binderHandle
    LambdaBinder _ -> misuse binderHandle
    TypeAbsBinder _ -> misuse binderHandle
    ConstraintAbsBinder _ -> misuse binderHandle
    LetBinder _ -> misuse binderHandle
    LetRecGroup _ -> misuse binderHandle
    JoinBinder _ -> misuse binderHandle
    CaseBinder _ -> misuse binderHandle
    BindBinder _ -> misuse binderHandle
    SwitchBinder _ -> misuse binderHandle
  where
  clauseOf c body = case c.continuation of
    Just k -> XFullClause { op: c.op, tyBinders: c.tyBinders, argBinder: c.argument, contBinder: k, body: body.term }
    Nothing -> XFastClause { op: c.op, tyBinders: c.tyBinders, argBinder: c.argument, body: body.term }

-- | Open `region [ℓ] ( k̄ : σ̄ ) @ ( … ) in …`: a binder, the fresh region name it
-- | binds, and the scope its body is built in, which binds that name with the
-- | layout given and jumps to no join point outside, as Core discards the join
-- | points at a region's body. The name is what a row element and a key of the
-- | region are written with.
-- |
-- | A layout's keys are distinct and well-formed for a `Row Type`, and its types
-- | ones the scope may use at `Type`.
openRegion :: Handle -> P.Array { key :: RowKey, type :: Handle } -> Elab { binder :: Handle, name :: RegionName, bodyScope :: Handle }
openRegion scopeHandle layoutGiven = do
  scope <- resolveScope scopeHandle
  cells <- layoutIn scope layoutGiven
  name <- freshRegionName (Map.keys scope.context.regions) "r"
  body <- abstractedChild scope
    (bindRegion scope.context name (Map.fromFoldable (map (\c -> Tuple c.key c.ty) cells)))
  binder <- issue (BinderObject (RegionBinder { name, cells, parent: scope.id, body: body.id }))
  holdOpen body.id body.ancestors
  bodyHandle <- issue (ScopeObject body)
  pure { binder, name, bodyScope: bodyHandle }

-- | Close a region opened in this scope with its body and one initial value for
-- | each cell, claimed at the type the body is claimed at.
-- |
-- | The body is visible under the binder and jumps to no join point; the initial
-- | values are terms this scope may use, outside the region. What the initial values are claimed at is
-- | the Core type checker's. A body claimed at a type mentioning the region would
-- | let a reference into it outlive it, and is refused.
closeRegion :: Handle -> Handle -> Handle -> P.Array Handle -> Elab Handle
closeRegion scopeHandle binderHandle bodyHandle initialHandles = do
  scope <- resolveScope scopeHandle
  resolveBinder binderHandle >>= case _ of
    RegionBinder b -> do
      when (Array.length initialHandles /= Array.length b.cells)
        (rejected (InitialValueCount binderHandle (Array.length b.cells) (Array.length initialHandles)))
      body <- resolveExpr bodyHandle
      closedOver scope binderHandle b body.builtIn bodyHandle
      unless (Set.isEmpty (freeVarsOf body.term).joins) (rejected (JoinOutOfScope bodyHandle))
      initials <- traverse (usableTermIn scope) initialHandles
      metas <- currentMetas
      let
        claimed = substitute metas body.claimed
      when (Set.member b.name (freeRegions claimed)) (rejected (RegionEscapes b.name))
      issueTerm scope (ERegion unit b.name b.cells (map _.term initials) body.term) claimed
    HandleBinder _ -> misuse binderHandle
    ForallBinder _ -> misuse binderHandle
    AssumedConstraint _ -> misuse binderHandle
    LambdaBinder _ -> misuse binderHandle
    TypeAbsBinder _ -> misuse binderHandle
    ConstraintAbsBinder _ -> misuse binderHandle
    LetBinder _ -> misuse binderHandle
    LetRecGroup _ -> misuse binderHandle
    JoinBinder _ -> misuse binderHandle
    CaseBinder _ -> misuse binderHandle
    BindBinder _ -> misuse binderHandle
    SwitchBinder _ -> misuse binderHandle

-- | `readCell ℓ.k`, claimed at the type the region's layout gives `k`. The
-- | region is named by its binder, and the scope must stand inside it.
readCell :: Handle -> Handle -> RowKey -> Elab Handle
readCell scopeHandle binderHandle key = do
  scope <- resolveScope scopeHandle
  cell <- cellIn scopeHandle scope binderHandle key
  issueTerm scope (EReadCell unit cell.region key) cell.ty

-- | `writeCell ℓ.k e`, claimed at `Unit`. What `e` is claimed at is the Core type
-- | checker's.
writeCell :: Handle -> Handle -> RowKey -> Handle -> Elab Handle
writeCell scopeHandle binderHandle key valueHandle = do
  scope <- resolveScope scopeHandle
  cell <- cellIn scopeHandle scope binderHandle key
  value <- usableTermIn scope valueHandle
  issueTerm scope (EWriteCell unit cell.region key value.term) (XCon unitTy [])

-- The region a binder opens and the type its layout gives a cell, where the
-- scope stands inside that region.
cellIn :: Handle -> ScopeObject -> Handle -> RowKey -> Elab { region :: RegionName, ty :: XType }
cellIn scopeHandle scope binderHandle key =
  resolveBinder binderHandle >>= case _ of
    RegionBinder b -> case Map.lookup b.name scope.context.regions of
      Nothing -> rejected (NoRegion scopeHandle)
      Just region -> case Map.lookup key region.layout of
        Just ty -> pure { region: b.name, ty }
        Nothing -> rejected (CellAbsent key)
    _ -> misuse binderHandle

misuse :: forall a. Handle -> Elab a
misuse binderHandle = rejected (BinderMisuse binderHandle)

-- The effect element a key and a payload make, kinded: a region is refused, and
-- a type payload is not an effect.
elementIn
  :: ScopeObject
  -> RowKey
  -> PayloadView
  -> Elab { entry :: XRowEntry, effect :: Qualified EffName, args :: P.Array XType }
elementIn scope key = case _ of
  RegionPayload _ -> rejected RegionEntryForbidden
  TypePayload _ -> rejected (EntryMismatch key)
  EffectPayload e argHandles -> do
    args <- traverse (map _.type <<< usableIn scope) argHandles
    entry <- case key of
      EffectKey e' | e' == e -> pure (XRowEffectEntry e args)
      SymbolKey s -> pure (XRowLabelledEffectEntry s e args)
      _ -> rejected (EntryMismatch key)
    _ <- kinded scope (XRowExtend entry XRowEmpty)
    metas <- currentMetas
    pure { entry, effect: e, args: map (substitute metas) args }

-- The declaration of an effect the kinding environment declares; the table
-- lacking it is the host's own inconsistency, the two coming from one signature.
effectShape :: Qualified EffName -> Elab EffectShape
effectShape name = do
  env <- askEnv
  case lookupEffect env.session.effects name of
    Just shape -> pure shape
    Nothing -> break (EffectTableMismatch name)

operationOf :: Qualified EffName -> EffectShape -> OpName -> Elab OperationShape
operationOf name effect op = case Map.lookup op effect.operations of
  Just operation -> pure operation
  Nothing -> rejected (UnknownOperation name op)

-- A layout's cells: distinct keys, well-formed for a `Row Type`, at types the
-- scope may use.
layoutIn :: ScopeObject -> P.Array { key :: RowKey, type :: Handle } -> Elab (P.Array XCell)
layoutIn scope given = do
  env <- askEnv
  let
    keys = map _.key given
  for_ (Array.findIndex (\k -> Array.length (Array.filter (_ == k) keys) > 1) keys) \i ->
    for_ (Array.index keys i) \k -> rejected (DuplicateCell k)
  for_ keys \k -> case wellFormedKey env.session.kinding (Map.keys scope.context.regions) k (Just RowType) of
    Left fault -> rejected (IllKinded fault)
    Right _ -> pure unit
  traverse (\c -> valueType scope c.type <#> \ty -> { key: c.key, ty }) given

-- What the binder records of an operation clause.
type ClauseRecord =
  { op :: OpName
  , tyBinders :: P.Array { name :: TyVar, kind :: XKind }
  , argument :: { name :: Ident, ty :: XType }
  , continuation :: Maybe { name :: Ident, ty :: XType }
  , scope :: ScopeId
  }

-- One operation clause's scope: the operation's type variables, fresh, its
-- argument at the argument type, and for a `full` clause its continuation at
-- `τ -{ρ}-> β`, the row being the clauses' own.
openClause
  :: ScopeObject
  -> ScopeObject
  -> XContext
  -> XType
  -> XType
  -> P.Array XType
  -> EffectShape
  -> { op :: OpName, full :: P.Boolean }
  -> OperationShape
  -> Elab { record :: ClauseRecord, scope :: ScopeObject }
openClause scope hub clauseContext clauseRow answer args effect given operation = do
  names <- traverse (\b -> freshBinderName (Map.keys clauseContext.tyVars) (hintOf b.name)) operation.tyBinders
  let
    tyBinders = Array.zipWith (\b name -> { name, kind: b.kind }) operation.tyBinders names
    substitution =
      Map.fromFoldable
        ( Array.zip (map _.name effect.params) args
            <> Array.zip (map _.name operation.tyBinders) (map XVar names)
        )
    bound = Array.foldl (\ctx b -> bindTyVar ctx b.name b.kind) clauseContext tyBinders
  -- The substitution reads the clause's own variables, which the scope does not
  -- bind, so it is made in a scope that does.
  inner <- childWith hub bound Map.empty Nothing
  argumentType <- substitutedAt inner substitution operation.argument
  resumesType <- substitutedAt inner substitution operation.resumesWith
  argumentName <- freshIdent (Map.keys scope.context.vars) "x"
  continuation <-
    if given.full then do
      k <- freshIdent (Map.keys scope.context.vars) "k"
      pure (Just { name: k, ty: XApp (XApp (XApp (XCon functionTy []) resumesType) clauseRow) answer })
    else pure Nothing
  let
    context = Array.foldl (\ctx p -> bindVar ctx p.name p.ty)
      (bindVar bound argumentName argumentType)
      (Array.fromFoldable continuation)
    clauseScope = inner { context = context }
  pure
    { record:
        { op: given.op
        , tyBinders
        , argument: { name: argumentName, ty: argumentType }
        , continuation
        , scope: clauseScope.id
        }
    , scope: clauseScope
    }
  where
  hintOf (TyVar name) = name

-- Issue what an operation clause binds, built in its scope.
issueClause
  :: { record :: ClauseRecord, scope :: ScopeObject }
  -> Elab { typeVariables :: P.Array Handle, argument :: Handle, continuation :: Maybe Handle, scope :: Handle }
issueClause clause = do
  typeVariables <- traverse (\b -> built clause.scope (XVar b.name)) clause.record.tyBinders
  argument <- issueTerm clause.scope (EVar unit clause.record.argument.name) clause.record.argument.ty
  continuation <- traverse (\k -> issueTerm clause.scope (EVar unit k.name) k.ty) clause.record.continuation
  scope <- issue (ScopeObject clause.scope)
  pure { typeVariables, argument, continuation, scope }
