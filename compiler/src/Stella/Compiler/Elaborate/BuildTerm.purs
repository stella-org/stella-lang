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
  ) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.BuildScope (issueTerm, rejected, schemeAt)
import Stella.Compiler.Elaborate.Diagnostic (BuildError(..))
import Stella.Compiler.Elaborate.Elab (Elab, resolveScope)
import Stella.Compiler.Elaborate.Handle (Handle)
import Stella.Compiler.Elaborate.Term (XExpr(..))
import Stella.Compiler.Elaborate.Type (fromCore)
import Stella.Compiler.Elaborate.View (KindView)
import Stella.Compiler.TypedCore (Ident, Literal, Qualified)
import Stella.Compiler.TypedCore.Prim (litType)
import Data.Map as Map
import Data.Maybe (Maybe(..))

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
