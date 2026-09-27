-- | The kernel's term builders: how a synthesizer assembles a Core⁺ term from
-- | the handles it holds.
-- |
-- | **A term is built in a build scope, as a type is**, and carries it: a
-- | builder uses a term only where it was built in the scope given or in one of
-- | its ancestors. A term built under a binder mentions what the binder binds or
-- | assumes, so it may stand only under the term binder that corresponds.
-- |
-- | **A builder is not a type checker.** Each term holds the type it is claimed
-- | at; what the kernel checks is the scope, the class of each handle, and how a
-- | binder is used. Whether a claim is borne out is the Core type checker's to
-- | decide once the term is zonked. For a leaf the claim is the host's own,
-- | there being one type a leaf can be claimed at.
-- |
-- | Two forms have no builder. `?m` is made by `subgoal` alone, which creates the
-- | job that fills it; and a typed hole is the Surface elaborator's, for
-- | reporting and recovery. A synthesizer that cannot build a candidate throws
-- | rather than returning a hole, which would succeed here and fail only at the
-- | Core boundary, after the search had stopped.
module Stella.Compiler.Elaborate.BuildTerm
  ( localVariable
  , globalRef
  , literal
  , termApply
  , typeApply
  , constraintApply
  , openLambda
  , closeLambda
  , openTypeAbs
  , closeTypeAbs
  , openConstraintAbs
  , closeConstraintAbs
  , openLet
  , closeLet
  , openLetRec
  , closeLetRec
  , openJoin
  , closeJoin
  , jump
  ) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.BuildScope (Shape(..), abstractedChild, built, childWith, closedOver, closedOverParts, constrainedShape, constraintIn, forallShape, functionShape, inheritingChild, instantiatedAt, issueTerm, kindIn, rejected, requiredIn, schemeAt, siteOf, usableIn, usableTermIn, visibleUnder)
import Stella.Compiler.Elaborate.Context (bindTyVar, bindVar)
import Stella.Compiler.Elaborate.Context as Context
import Stella.Compiler.Elaborate.Diagnostic (BuildError(..))
import Stella.Compiler.Elaborate.Elab (Elab, assume, currentMetas, freshBinderName, freshIdent, freshJoin, holdOpen, issue, postpone, resolveBinder, resolveExpr, resolveJoin, resolveScope)
import Stella.Compiler.Elaborate.Handle (BinderObject(..), ExprObject, Handle, HandleObject(..), ScopeId, ScopeObject)
import Stella.Compiler.Elaborate.Kind (XKind(..))
import Stella.Compiler.Elaborate.Kinding (KindEvidence(..), quantifiable)
import Stella.Compiler.Elaborate.Term (XExpr(..), freeVarsOf)
import Stella.Compiler.Elaborate.Type (XType(..), fromCore)
import Stella.Compiler.Elaborate.Unify (substitute)
import Stella.Compiler.Elaborate.View (ConstraintView, KindView)
import Stella.Compiler.TypedCore (Ident, Literal, Qualified, RowElemKind(..))
import Stella.Compiler.TypedCore.Prim (functionTy, litType)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Data.Traversable (traverse)

-- | A value variable the scope binds, at the type it is bound at.
-- |
-- | Only a name the scope binds is accepted: the site's bindings, and those of
-- | the binders opened around the scope. No other name can be written, so none
-- | is made up.
localVariable :: Handle -> Ident -> Elab Handle
localVariable scopeHandle name = do
  scope <- resolveScope scopeHandle
  case Map.lookup name scope.context.vars of
    Nothing -> rejected (UnboundVariable name)
    Just ty -> issueTerm scope (EVar unit name) ty

-- | A reference to a catalog entry at the kinds given, at its scheme so
-- | instantiated. The entry is judged as `instantiateScheme` judges it.
globalRef :: Handle -> Qualified Ident -> P.Array KindView -> Elab Handle
globalRef scopeHandle name kinds = do
  scope <- resolveScope scopeHandle
  instantiated <- schemeAt scope name kinds
  issueTerm scope (EGlobal unit name instantiated.kinds) instantiated.type

-- | A literal, at the type of its kind of literal.
literal :: Handle -> Literal -> Elab Handle
literal scopeHandle lit = do
  scope <- resolveScope scopeHandle
  issueTerm scope (ELit unit lit) (fromCore (litType lit))

-- | `f x`, claimed at the result of the function type `f` is claimed at.
-- |
-- | What `x` is claimed at is not compared with the function's parameter: that
-- | is the Core type checker's. A claim for `f` whose head is still an unsolved
-- | metavariable waits on it; one that can never be a function type is a misuse.
termApply :: Handle -> Handle -> Handle -> Elab Handle
termApply scopeHandle functionHandle argumentHandle = do
  scope <- resolveScope scopeHandle
  function <- usableTermIn scope functionHandle
  argument <- usableTermIn scope argumentHandle
  metas <- currentMetas
  case functionShape metas function.claimed of
    Seen fn -> issueTerm scope (EApp unit function.term argument.term) fn.result
    Blocked ms -> postpone ms
    Otherwise -> rejected (NotAFunction functionHandle)

-- | `e [σ]`, claimed at `τ[a := σ]` where `e` is claimed at `forall (a : κ). τ`,
-- | by the substitution `instantiateForall` makes. `σ` must stand at `κ`.
typeApply :: Handle -> Handle -> Handle -> Elab Handle
typeApply scopeHandle termHandle argumentHandle = do
  scope <- resolveScope scopeHandle
  term <- usableTermIn scope termHandle
  argument <- usableIn scope argumentHandle
  metas <- currentMetas
  case forallShape metas term.claimed of
    Seen whole -> do
      let
        σ = substitute metas argument.type
      instantiatedAt scope whole.binder whole.kind whole.body σ
        >>= issueTerm scope (ETyApp unit term.term σ)
    Blocked ms -> postpone ms
    Otherwise -> rejected (NotAForall termHandle)

-- | `e [•]`, claimed at `τ` where `e` is claimed at `C => τ`, requiring `C` of
-- | the scope together with the term: proved now, watched where a flexible tail
-- | leaves it open, and a failure where it is already broken.
constraintApply :: Handle -> Handle -> Elab Handle
constraintApply scopeHandle termHandle = do
  scope <- resolveScope scopeHandle
  term <- usableTermIn scope termHandle
  metas <- currentMetas
  case constrainedShape metas term.claimed of
    Seen constrained -> do
      requiredIn scope constrained.constraint
      issueTerm scope (EConstraintApp unit term.term) constrained.body
    Blocked ms -> postpone ms
    Otherwise -> rejected (NotConstrained termHandle)

-- | Open `λ(x : τ)`: a binder, the variable it binds as a term built in the
-- | body's scope, and that scope. `τ` must be a type the scope may use, at
-- | `Type`; the name is the host's, fresh where it is bound.
openLambda
  :: Handle
  -> P.String
  -> Handle
  -> Elab { binder :: Handle, variable :: Handle, bodyScope :: Handle }
openLambda scopeHandle hint typeHandle = do
  scope <- resolveScope scopeHandle
  ty <- valueType scope typeHandle
  name <- freshIdent (Map.keys scope.context.vars) hint
  child <- abstractedChild scope (bindVar scope.context name ty)
  binder <- issue (BinderObject (LambdaBinder { name, type: ty, parent: scope.id, body: child.id }))
  holdOpen child.id child.ancestors
  variable <- issueTerm child (EVar unit name) ty
  bodyScope <- issue (ScopeObject child)
  pure { binder, variable, bodyScope }

-- | Close a lambda opened in this scope over a body visible under it, claimed at
-- | `τ -{ρ}-> σ` where `σ` is what the body is claimed at.
-- |
-- | `ρ` is the row the body's effects go on, which no claim records and the
-- | synthesizer gives: a type this scope may use, standing at `Row Effect`. A
-- | row built inside the body's scope does not leave it this way; an effect
-- | metavariable the row needs is created here before the lambda is opened.
closeLambda :: Handle -> Handle -> Handle -> Handle -> Elab Handle
closeLambda scopeHandle binderHandle bodyHandle rowHandle = do
  scope <- resolveScope scopeHandle
  resolveBinder binderHandle >>= case _ of
    LambdaBinder b -> do
      body <- abstractedBody scope binderHandle b bodyHandle
      row <- usableIn scope rowHandle
      case row.kind of
        ExactKind (XKRow RowEffect) -> pure unit
        AnyRow -> pure unit
        _ -> rejected (NotAnEffectRow rowHandle)
      issueTerm scope (ELam unit b.name b.type body.term) (functionType b.type row.type body.claimed)
    ForallBinder _ -> misuse
    AssumedConstraint _ -> misuse
    TypeAbsBinder _ -> misuse
    ConstraintAbsBinder _ -> misuse
    LetBinder _ -> misuse
    LetRecGroup _ -> misuse
    JoinBinder _ -> misuse
  where
  misuse = rejected (BinderMisuse binderHandle)

-- | Open `Λ(a : κ)`: a binder, the variable it binds as a type built in the
-- | body's scope, and that scope. `κ` must be quantifiable.
openTypeAbs
  :: Handle
  -> P.String
  -> KindView
  -> Elab { binder :: Handle, variable :: Handle, bodyScope :: Handle }
openTypeAbs scopeHandle hint kindView = do
  scope <- resolveScope scopeHandle
  kind <- kindIn scope kindView
  case quantifiable kind of
    Left fault -> rejected (IllKinded fault)
    Right _ -> pure unit
  name <- freshBinderName (Map.keys scope.context.tyVars) hint
  child <- abstractedChild scope (bindTyVar scope.context name kind)
  binder <- issue (BinderObject (TypeAbsBinder { name, kind, parent: scope.id, body: child.id }))
  holdOpen child.id child.ancestors
  variable <- built child (XVar name)
  bodyScope <- issue (ScopeObject child)
  pure { binder, variable, bodyScope }

-- | Close a type abstraction opened in this scope over a body visible under it,
-- | claimed at `forall (a : κ). σ` where `σ` is what the body is claimed at.
closeTypeAbs :: Handle -> Handle -> Handle -> Elab Handle
closeTypeAbs scopeHandle binderHandle bodyHandle = do
  scope <- resolveScope scopeHandle
  resolveBinder binderHandle >>= case _ of
    TypeAbsBinder b -> do
      body <- abstractedBody scope binderHandle b bodyHandle
      issueTerm scope (ETyLam unit b.name b.kind body.term) (XForall b.name b.kind body.claimed)
    ForallBinder _ -> misuse
    AssumedConstraint _ -> misuse
    LambdaBinder _ -> misuse
    ConstraintAbsBinder _ -> misuse
    LetBinder _ -> misuse
    LetRecGroup _ -> misuse
    JoinBinder _ -> misuse
  where
  misuse = rejected (BinderMisuse binderHandle)

-- | Open `Λ(_ : C)`: a binder, and the scope its body is built in, which assumes
-- | `C`. The constraint is judged well-formed here; whether it can hold is
-- | decided where the abstraction is closed, as for `openConstraint`.
openConstraintAbs :: Handle -> ConstraintView -> Elab { binder :: Handle, bodyScope :: Handle }
openConstraintAbs scopeHandle view = do
  scope <- resolveScope scopeHandle
  constraint <- constraintIn scope view
  child <- abstractedChild scope (Context.assume scope.context constraint)
  binder <- issue (BinderObject (ConstraintAbsBinder { constraint, parent: scope.id, body: child.id }))
  holdOpen child.id child.ancestors
  bodyScope <- issue (ScopeObject child)
  pure { binder, bodyScope }

-- | Close a constraint abstraction opened in this scope over a body visible
-- | under it, claimed at `C => σ` where `σ` is what the body is claimed at, and
-- | holding `C` as an assumption from here on.
closeConstraintAbs :: Handle -> Handle -> Handle -> Elab Handle
closeConstraintAbs scopeHandle binderHandle bodyHandle = do
  scope <- resolveScope scopeHandle
  resolveBinder binderHandle >>= case _ of
    ConstraintAbsBinder b -> do
      body <- abstractedBody scope binderHandle b bodyHandle
      site <- siteOf scope
      _ <- assume site b.constraint
      issueTerm scope (EConstraintLam unit b.constraint body.term) (XConstrained b.constraint body.claimed)
    ForallBinder _ -> misuse
    AssumedConstraint _ -> misuse
    LambdaBinder _ -> misuse
    TypeAbsBinder _ -> misuse
    LetBinder _ -> misuse
    LetRecGroup _ -> misuse
    JoinBinder _ -> misuse
  where
  misuse = rejected (BinderMisuse binderHandle)

-- | Open `let x = rhs in`: a binder, the variable it binds as a term built in
-- | the body's scope, and that scope. The right-hand side is a term this scope
-- | may use, and `x` is bound at what it is claimed at; a right-hand side built
-- | in the body's scope cannot be given, so none refers to `x`.
openLet
  :: Handle
  -> P.String
  -> Handle
  -> Elab { binder :: Handle, variable :: Handle, bodyScope :: Handle }
openLet scopeHandle hint rhsHandle = do
  scope <- resolveScope scopeHandle
  rhs <- usableTermIn scope rhsHandle
  name <- freshIdent (Map.keys scope.context.vars) hint
  child <- inheritingChild scope (bindVar scope.context name rhs.claimed)
  binder <- issue (BinderObject (LetBinder { name, type: rhs.claimed, rhs: rhs.term, parent: scope.id, body: child.id }))
  holdOpen child.id child.ancestors
  variable <- issueTerm child (EVar unit name) rhs.claimed
  bodyScope <- issue (ScopeObject child)
  pure { binder, variable, bodyScope }

-- | Close a `let` opened in this scope over a body visible under it, claimed at
-- | what the body is claimed at.
closeLet :: Handle -> Handle -> Handle -> Elab Handle
closeLet scopeHandle binderHandle bodyHandle = do
  scope <- resolveScope scopeHandle
  resolveBinder binderHandle >>= case _ of
    LetBinder b -> do
      body <- resolveExpr bodyHandle
      closedOver scope binderHandle b body.builtIn bodyHandle
      issueTerm scope (ELet unit b.name b.type b.rhs body.term) body.claimed
    ForallBinder _ -> misuse
    AssumedConstraint _ -> misuse
    LambdaBinder _ -> misuse
    TypeAbsBinder _ -> misuse
    ConstraintAbsBinder _ -> misuse
    LetRecGroup _ -> misuse
    JoinBinder _ -> misuse
  where
  misuse = rejected (BinderMisuse binderHandle)

-- | Open a `letrec` group: a binder, each variable it binds as a term built in
-- | the body's scope, and that scope, which binds them all. Each declared type
-- | must be one this scope may use, at `Type`.
openLetRec
  :: Handle
  -> P.Array { hint :: P.String, type :: Handle }
  -> Elab { binder :: Handle, variables :: P.Array Handle, bodyScope :: Handle }
openLetRec scopeHandle declared = do
  scope <- resolveScope scopeHandle
  types <- traverse (valueType scope <<< _.type) declared
  names <- traverse (\d -> freshIdent (Map.keys scope.context.vars) d.hint) declared
  let
    bindings = Array.zipWith { name: _, type: _ } names types
  child <- inheritingChild scope (Array.foldl (\ctx b -> bindVar ctx b.name b.type) scope.context bindings)
  binder <- issue (BinderObject (LetRecGroup { bindings, parent: scope.id, body: child.id }))
  holdOpen child.id child.ancestors
  variables <- traverse (\b -> issueTerm child (EVar unit b.name) b.type) bindings
  bodyScope <- issue (ScopeObject child)
  pure { binder, variables, bodyScope }

-- | Close a `letrec` group opened in this scope, with one right-hand side for
-- | each name it binds, in order, and a body; each is visible under the group.
-- | Claimed at what the body is claimed at.
closeLetRec :: Handle -> Handle -> P.Array Handle -> Handle -> Elab Handle
closeLetRec scopeHandle binderHandle rhsHandles bodyHandle = do
  scope <- resolveScope scopeHandle
  resolveBinder binderHandle >>= case _ of
    LetRecGroup g -> do
      when (g.parent /= scope.id) misuse
      when (Array.length rhsHandles /= Array.length g.bindings)
        (rejected (LetRecArity binderHandle (Array.length g.bindings) (Array.length rhsHandles)))
      rhss <- traverse (visibleUnderGroup scope g) rhsHandles
      body <- resolveExpr bodyHandle
      closedOver scope binderHandle g body.builtIn bodyHandle
      let
        values = Array.zipWith (\b rhs -> { name: b.name, ty: b.type, value: rhs.term }) g.bindings rhss
      issueTerm scope (ELetRec unit values body.term) body.claimed
    ForallBinder _ -> misuse
    AssumedConstraint _ -> misuse
    LambdaBinder _ -> misuse
    TypeAbsBinder _ -> misuse
    ConstraintAbsBinder _ -> misuse
    LetBinder _ -> misuse
    JoinBinder _ -> misuse
  where
  misuse :: forall a. Elab a
  misuse = rejected (BinderMisuse binderHandle)

  visibleUnderGroup scope g handle = do
    rhs <- resolveExpr handle
    if visibleUnder scope g rhs.builtIn then pure rhs
    else rejected (ScopeViolation handle)

-- A type a value may be bound at: one the scope may use, standing at `Type`.
valueType :: ScopeObject -> Handle -> Elab XType
valueType scope handle = do
  ty <- usableIn scope handle
  case ty.kind of
    ExactKind XKType -> pure ty.type
    _ -> rejected (NotAType handle)

-- `argument -{row}-> result`.
functionType :: XType -> XType -> XType -> XType
functionType argument row result =
  XApp (XApp (XApp (XCon functionTy []) argument) row) result

-- An abstraction's body: visible under its binder, and jumping to no join
-- point, the body's scope having none.
abstractedBody
  :: forall r
   . ScopeObject
  -> Handle
  -> { parent :: ScopeId, body :: ScopeId | r }
  -> Handle
  -> Elab ExprObject
abstractedBody scope binderHandle binder bodyHandle = do
  body <- resolveExpr bodyHandle
  closedOver scope binderHandle binder body.builtIn bodyHandle
  unless (Set.isEmpty (freeVarsOf body.term).joins) (rejected (JoinOutOfScope bodyHandle))
  pure body

-- | Open `letjoin j (x̄ : τ̄) : τ`: a binder, the join point as a handle, the
-- | parameters as terms built in the definition's scope, and two scopes — the
-- | definition's, binding the parameters and `j`, and the continuation's,
-- | binding `j` alone.
-- |
-- | Each type is one the scope may use, at `Type`. The names are the host's,
-- | fresh where they are bound, `j` in a namespace of join points apart from
-- | values.
openJoin
  :: Handle
  -> P.String
  -> P.Array { hint :: P.String, type :: Handle }
  -> Handle
  -> Elab
       { binder :: Handle
       , join :: Handle
       , params :: P.Array Handle
       , definitionScope :: Handle
       , bodyScope :: Handle
       }
openJoin scopeHandle hint declared resultHandle = do
  scope <- resolveScope scopeHandle
  types <- traverse (valueType scope <<< _.type) declared
  result <- valueType scope resultHandle
  name <- freshJoin (Map.keys scope.joins) hint
  names <- traverse (\d -> freshIdent (Map.keys scope.context.vars) d.hint) declared
  let
    params = Array.zipWith { name: _, type: _ } names types
    signature = { params: types, result }
    joins = Map.insert name signature scope.joins
  hub <- inheritingChild scope scope.context
  definition <- childWith hub (Array.foldl (\ctx p -> bindVar ctx p.name p.type) scope.context params) joins
  continuation <- childWith hub scope.context joins
  binder <- issue
    ( BinderObject
        ( JoinBinder
            { name, params, result, parent: scope.id, body: hub.id, definition: definition.id, continuation: continuation.id }
        )
    )
  holdOpen hub.id hub.ancestors
  join <- issue (JoinObject { name, signature, hub: hub.id })
  paramTerms <- traverse (\p -> issueTerm definition (EVar unit p.name) p.type) params
  definitionScope <- issue (ScopeObject definition)
  bodyScope <- issue (ScopeObject continuation)
  pure { binder, join, params: paramTerms, definitionScope, bodyScope }

-- | Close a `letjoin` opened in this scope, over a definition visible under the
-- | definition's scope and a body visible under the continuation's, claimed at
-- | the join point's result.
closeJoin :: Handle -> Handle -> Handle -> Handle -> Elab Handle
closeJoin scopeHandle binderHandle definitionHandle bodyHandle = do
  scope <- resolveScope scopeHandle
  resolveBinder binderHandle >>= case _ of
    JoinBinder b -> do
      definition <- resolveExpr definitionHandle
      body <- resolveExpr bodyHandle
      closedOverParts scope binderHandle b
        [ { within: b.definition, builtIn: definition.builtIn, handle: definitionHandle }
        , { within: b.continuation, builtIn: body.builtIn, handle: bodyHandle }
        ]
      let
        params = map (\p -> { name: p.name, ty: p.type }) b.params
      issueTerm scope (ELetJoin unit b.name params b.result definition.term body.term) b.result
    ForallBinder _ -> misuse
    AssumedConstraint _ -> misuse
    LambdaBinder _ -> misuse
    TypeAbsBinder _ -> misuse
    ConstraintAbsBinder _ -> misuse
    LetBinder _ -> misuse
    LetRecGroup _ -> misuse
  where
  misuse = rejected (BinderMisuse binderHandle)

-- | `jump j (ē)`, claimed at `j`'s result.
-- |
-- | `j` must be in scope: this scope must stand under the `letjoin` that binds
-- | it, and no abstraction may stand between. The arguments are as many as `j`
-- | takes; what they are claimed at, and whether the jump is in tail position,
-- | are the Core type checker's.
jump :: Handle -> Handle -> P.Array Handle -> Elab Handle
jump scopeHandle joinHandle argumentHandles = do
  scope <- resolveScope scopeHandle
  join <- resolveJoin joinHandle
  unless (Set.member join.hub scope.ancestors && Map.lookup join.name scope.joins == Just join.signature)
    (rejected (JoinOutOfScope joinHandle))
  when (Array.length argumentHandles /= Array.length join.signature.params)
    (rejected (JumpArity joinHandle (Array.length join.signature.params) (Array.length argumentHandles)))
  arguments <- traverse (usableTermIn scope) argumentHandles
  issueTerm scope (EJump unit join.name (map _.term arguments)) join.signature.result
