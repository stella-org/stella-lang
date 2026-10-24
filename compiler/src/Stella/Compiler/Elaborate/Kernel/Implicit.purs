-- | A checking boundary settled by the implicit handlers of `Ξ`
-- | ([Effect Handlers](../../../../../docs/technical-references/02-Surface-Language/02-Effect-Handlers.md#the-plan)).
-- |
-- | **The body is fixed at its own row `U`**, and the handlers the keys it
-- | performs call for are read off the keys alone, in the one order their
-- | dependencies give. **The thunk of the body is widened** by every target and
-- | every element of the row expected that it lacks. A key carried more than
-- | once carries one payload, and each handler's source the payload of the
-- | element it was chosen for. **Each handler is then instantiated**, its
-- | scheme's kind and type quantifiers at fresh metavariables and its
-- | constraints required at the boundary, and applied to the thunk below it;
-- | the row the last one leaves is equated with the row expected. What was opened and applied is
-- | recorded for the boundary's term to be lowered by, and nothing else
-- | decides it again.
module Stella.Compiler.Elaborate.Kernel.Implicit
  ( insertImplicit
  ) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldM, for_)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Stella.Compiler.Elaborate.CorePlus.Kind (XKind(..))
import Stella.Compiler.Elaborate.CorePlus.Row (rebuild)
import Stella.Compiler.Elaborate.CorePlus.Type (XRowEntry, XType(..), fromCore, fromCoreEntry, xRowEntryKey)
import Stella.Compiler.Elaborate.Kernel.Builder.Common (substituteKindVars, substituteTyVars)
import Stella.Compiler.Elaborate.Kernel.Elab (Elab, askEnv, freshKindMeta, freshTypeMeta, raiseDiagnostic, recordPlan, releaseBoundary, require, transact, unify)
import Stella.Compiler.Elaborate.Mechanism.Fit (Remainders)
import Stella.Compiler.Elaborate.Mechanism.Pending (HandlerGoal, Site)
import Stella.Compiler.Elaborate.Mechanism.Plan (PlanFailure(..), SpineStep(..), searchPlan)
import Stella.Compiler.Elaborate.Mechanism.Unify (KindRequirement(..))
import Stella.Compiler.Elaborate.Vocabulary.Diagnostic (Diagnostic(..))
import Stella.Compiler.TypedCore.Kind (RowElemKind(..))
import Stella.Compiler.TypedCore.Prim (functionTy, unitTy)
import Stella.Compiler.TypedCore.Type (compareRowKeys)

-- | Settle the boundary given, whose body performs a key the row expected
-- | lacks, by implicit handlers: given the body's row `U` and the row
-- | expected, and what is left of each once what they share has cancelled.
insertImplicit :: Site -> HandlerGoal -> Remainders -> Remainders -> Elab Unit
insertImplicit site goal settled remainders = do
  env <- askEnv
  releaseBoundary goal.boundary
  unify site { kind: rowEffect, left: XMeta goal.boundary, right: rebuild settled.source }
  plan <- case searchPlan env.session.implicits (Map.keys remainders.source.known) (Map.keys settled.target.known) of
    Right plan -> pure plan
    Left (PlanMissing k) -> raiseDiagnostic (ImplicitHandlerMissing site.origin k remainders.source)
    Left (PlanSeveral k handlers) -> raiseDiagnostic (ImplicitHandlerAmbiguous site.origin k handlers)
    Left (PlanUnordered handlers) -> raiseDiagnostic (ImplicitOrderAmbiguous site.origin handlers)
  -- the row expected's elements and every target, each key with one payload
  carried <- foldM join settled.target.known (map fromCoreEntry (Array.concatMap _.targets plan))
  for_ (Map.toUnfoldable (Map.intersectionWith Tuple settled.source.known carried) :: P.Array _) \(Tuple k (Tuple a b)) ->
    samePayload k a b
  -- each handler's source against the element it was chosen for: the body's,
  -- or a target of a handler inside it
  for_ plan \h -> do
    let
      source = fromCoreEntry h.source
      k = xRowEntryKey source
    for_ (Map.lookup k (Map.union settled.source.known carried)) (samePayload k source)
  let
    widening = Array.sortBy (\a b -> compareRowKeys (xRowEntryKey a) (xRowEntryKey b))
      (Array.fromFoldable (Map.values (Map.filterKeys (\k -> not (Map.member k settled.source.known)) carried)))
    start = rebuild settled.source { known = Map.union settled.source.known (Map.fromFoldable (map (\e -> Tuple (xRowEntryKey e) e) widening)) }
  applied <- foldM apply { row: start, steps: [] } plan
  unify site { kind: rowEffect, left: applied.row, right: goal.expected }
  recordPlan goal.boundary { source: rebuild settled.source, widening, answer: goal.answer, steps: applied.steps }
  where
  rowEffect = XKRow RowEffect

  join acc e = case Map.lookup (xRowEntryKey e) acc of
    Just e' -> samePayload (xRowEntryKey e) e' e $> acc
    Nothing -> pure (Map.insert (xRowEntryKey e) e acc)

  samePayload k a b = transact (unify site { kind: rowEffect, left: single a, right: single b }) >>= case _ of
    Right _ -> pure unit
    Left _ -> raiseDiagnostic (ImplicitPayloadConflict site.origin k)

  single :: XRowEntry -> XType
  single e = XRowExtend e XRowEmpty

  -- each handler applied to the thunk of what the one below it left, at the
  -- type the body answers with
  apply acc h = do
    kinds <- traverse (\_ -> freshKindMeta site.context.kindVars (Set.singleton Quantifiable)) h.scheme.kindVars
    opened <- instantiated [] (substituteKindVars (Map.fromFoldable (Array.zip h.scheme.kindVars kinds)) (fromCore h.scheme.body))
    output <- freshTypeMeta site.context rowEffect
    unify site { kind: XKType, left: opened.type, right: arrow (arrow unit acc.row goal.answer) output goal.answer }
    pure { row: output, steps: Array.snoc acc.steps { handler: h.handler, kinds, spine: opened.spine, input: acc.row, output } }

  instantiated spine = case _ of
    XForall a k rest -> do
      m <- freshTypeMeta site.context k
      instantiated (Array.snoc spine (SpineType m)) (substituteTyVars (Map.singleton a m) Map.empty rest)
    XConstrained c rest -> do
      require site c
      instantiated (Array.snoc spine SpineConstraint) rest
    t -> pure { type: t, spine }

  unit = XCon unitTy []
  arrow argument row result = XApp (XApp (XApp (XCon functionTy []) argument) row) result
