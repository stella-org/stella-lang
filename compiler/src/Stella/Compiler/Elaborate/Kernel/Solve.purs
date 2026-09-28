-- | The kernel's requests over metavariables and constraints: what a synthesizer
-- | asks of the solver, as opposed to what it observes or builds.
-- |
-- | **Each takes a build scope, and reads what it decides against from there.**
-- | A metavariable is created under the scope's variables, an equation stands at
-- | the scope's context, and a constraint is entailed from, or required with, the
-- | scope's assumptions — the site's, with every one opened around it. The types
-- | it is given are ones the scope may use, so nothing observed in no build scope
-- | reaches the solver through these, and no caller states a context or a scope
-- | wider than the one it stands in.
-- |
-- | Every one goes through the mechanism's own operation, so an assignment is
-- | never made except where its obligations are rechecked, its wakes queued, and
-- | its write recorded.
module Stella.Compiler.Elaborate.Kernel.Solve
  ( freshMetaType
  , isAssigned
  , unify
  , entails
  , require
  , subgoal
  ) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.Kernel.Builder.Common (built, constraintIn, kindIn, kindingScopeOf, rejected, requiredIn, siteOf, usableIn)
import Stella.Compiler.Elaborate.CorePlus.Context (FactsError(..), facts)
import Stella.Compiler.Elaborate.Vocabulary.Diagnostic (BuildError(..), Defect(..))
import Stella.Compiler.Elaborate.Kernel.Elab (Elab, break, createSynthesis, currentMetas, freshTypeMeta, issue, resolveMeta, resolveScope)
import Stella.Compiler.Elaborate.Kernel.Elab as Elab
import Stella.Compiler.Elaborate.Vocabulary.Handle (Handle, HandleObject(..))
import Stella.Compiler.Elaborate.CorePlus.Kind (XKind(..))
import Stella.Compiler.Elaborate.Mechanism.Kinding (KindEvidence(..), quantifiable)
import Stella.Compiler.Elaborate.Mechanism.Obligation (Basis(..), Breach(..), Standing(..), standing)
import Stella.Compiler.Elaborate.Mechanism.Pending (SynthRef)
import Stella.Compiler.Elaborate.CorePlus.Term (XExpr(..))
import Stella.Compiler.Elaborate.Mechanism.Unify (MetaBinding(..), lookupMeta, substitute)
import Stella.Compiler.Elaborate.Vocabulary.View (ConstraintView, KindView)
import Stella.Compiler.TypedCore (RowElemKind(..))
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))

-- | A type metavariable at the kind given, created under the scope's variables.
-- |
-- | **The kind must be one a type variable could stand at**: settled, well-formed
-- | in the scope, and quantifiable. A metavariable a synthesizer holds stands
-- | where a type variable would, so `Effect`, and an arrow whose final result is
-- | a row, such as `Type -> Row Type`, are refused, as `openForall` refuses them;
-- | a row kind itself is not. The metavariables the mechanism creates for itself,
-- | through `Elab.freshTypeMeta`, are not held to this: a synthesizer cannot
-- | create one, but may observe one — in a goal's type, as a row's flexible
-- | tail — and wait on it.
freshMetaType :: Handle -> KindView -> Elab Handle
freshMetaType scopeHandle kindView = do
  scope <- resolveScope scopeHandle
  kind <- kindIn scope kindView
  case quantifiable kind of
    Left fault -> rejected (IllKinded fault)
    Right _ -> pure unit
  freshTypeMeta scope.context kind >>= built scope

-- | Whether a metavariable is solved in the current `Ψ`.
isAssigned :: Handle -> Elab P.Boolean
isAssigned handle = do
  m <- resolveMeta handle
  metas <- currentMetas
  case lookupMeta metas m of
    Just (Assigned _) -> pure true
    Just (Unsolved _) -> pure false
    Nothing -> break (MetaAbsent m)

-- | `τ1 ≡ τ2`, at the kind the two handles' evidence gives, standing at the
-- | scope's context.
-- |
-- | Two exact kinds must agree; a row standing at any row kind meets a row at an
-- | exact one at that one; and two rows standing at any row kind — closed and
-- | empty, with no element and no tail — are equated at `Row Type`, a choice no
-- | substitution can observe. Evidence that cannot meet is a misuse and not a
-- | candidate that does not fit, every kind a handle holds being settled.
unify :: Handle -> Handle -> Handle -> Elab Unit
unify scopeHandle leftHandle rightHandle = do
  scope <- resolveScope scopeHandle
  left <- usableIn scope leftHandle
  right <- usableIn scope rightHandle
  kind <- case left.kind, right.kind of
    ExactKind a, ExactKind b | a == b -> pure a
    ExactKind k@(XKRow _), AnyRow -> pure k
    AnyRow, ExactKind k@(XKRow _) -> pure k
    AnyRow, AnyRow -> pure (XKRow RowType)
    _, _ -> rejected (KindsDiffer leftHandle rightHandle)
  site <- siteOf scope
  Elab.unify site { kind, left: left.type, right: right.type }

-- | Whether the scope's assumptions prove the constraint, against the current
-- | `Ψ`. It reads and changes nothing.
-- |
-- | **Only a proof is an answer of `true`.** A constraint left waiting on a
-- | flexible tail is not proved, and neither is one the facts refute or fail to
-- | prove; a flexible tail is never taken for a fact. A synthesizer that would
-- | rather wait reads the row's flexible tails from its view and postpones on
-- | them. **Assumptions that contradict each other prove nothing here**: answering
-- | `true` from a contradiction would be sound and useless, and closing the
-- | constraint that opened one fails anyway.
-- |
-- | A row with no normal form is a broken invariant of the solver, the
-- | constraint having been judged well-formed, and is a defect rather than an
-- | answer.
entails :: Handle -> ConstraintView -> Elab P.Boolean
entails scopeHandle view = do
  scope <- resolveScope scopeHandle
  constraint <- constraintIn scope view
  metas <- currentMetas
  site <- siteOf scope
  let
    zonk = substitute metas
  case facts zonk scope.context of
    Left (FactsRowError err) -> break (ObligationSubjectNotARow site.origin err)
    Left (LacksContradiction _) -> pure false
    Left (DisjointContradiction _) -> pure false
    Right sitefacts -> case standing Required sitefacts zonk constraint of
      Right Discharged -> pure true
      Right (Watching _) -> pure false
      Left breach -> case breach of
        SolutionCarriesKey _ -> pure false
        LacksUnprovenAtSite _ _ -> pure false
        SidesShareKey _ -> pure false
        DisjointUnprovenAtSite _ _ -> pure false
        SiteFactsFailed (FactsRowError err) -> break (ObligationSubjectNotARow site.origin err)
        SiteFactsFailed (LacksContradiction _) -> pure false
        SiteFactsFailed (DisjointContradiction _) -> pure false
        ObligationNotARow err -> break (ObligationSubjectNotARow site.origin err)

-- | Require a constraint of what is built in the scope: a `Required` obligation
-- | carrying the scope's context and the running job's origin. One already
-- | broken is a failure now.
require :: Handle -> ConstraintView -> Elab Unit
require scopeHandle view = do
  scope <- resolveScope scopeHandle
  constraintIn scope view >>= requiredIn scope

-- | `⟨ τ by f ⟩`, asked from inside an attempt: a term metavariable at `τ` under
-- | the scope's context and a synthesis job at the scope's site that fills it,
-- | queued for its first attempt. The term is built in the scope, which is where
-- | it may be placed.
subgoal :: Handle -> Handle -> SynthRef -> Elab Handle
subgoal scopeHandle typeHandle synthesizer = do
  scope <- resolveScope scopeHandle
  expected <- usableIn scope typeHandle
  case expected.kind of
    ExactKind XKType -> pure unit
    _ -> rejected (NotAType typeHandle)
  site <- siteOf scope
  Tuple _ target <- createSynthesis site expected.type synthesizer scope.region
  issue
    ( ExprObject
        { term: ETermMeta unit target
        , claimed: expected.type
        , scope: kindingScopeOf scope
        , builtIn: Just scope.id
        , region: scope.region
        }
    )
