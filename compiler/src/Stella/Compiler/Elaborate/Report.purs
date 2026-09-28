-- | How a synthesizer reports and waits: `throw` to fail, `warn` to say something
-- | and go on, and `postpone` to wait on a metavariable.
-- |
-- | **The synthesizer builds the message, and the host makes the report.** A
-- | message is text and the handles the synthesizer holds; the host freezes it
-- | where it is said, and adds the goal the running job is about. What the
-- | synthesizer cannot do is build the host's report itself, which names a site
-- | and holds Core⁺.
-- |
-- | A handle in a message is shown, not built with, so the scope rules do not
-- | apply to it: a type a sibling candidate built, or one observed under a
-- | binder, may be named. It must still be a valid handle of the running
-- | session.
module Stella.Compiler.Elaborate.Report
  ( throw
  , warn
  , postpone
  ) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.Diagnostic (Defect(..), Diagnostic(..))
import Stella.Compiler.Elaborate.Elab (Elab, askEnv, break, currentMetas, raiseDiagnostic, recordWarning, resolveExpr, resolveMeta, resolveType)
import Stella.Compiler.Elaborate.Elab as Elab
import Stella.Compiler.Elaborate.Handle (Handle)
import Stella.Compiler.Elaborate.Message (FrozenMessagePart(..), GoalSummary, MessagePart(..))
import Stella.Compiler.Elaborate.Pending (goalOf)
import Stella.Compiler.Elaborate.TermMeta (zonkExpr)
import Stella.Compiler.Elaborate.Unify (substitute)
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Data.Traversable (traverse)

-- | Fail the attempt with the message given, a failure `transact` catches: this
-- | candidate, or this goal, does not hold.
throw :: forall a. P.Array MessagePart -> Elab a
throw message = do
  goal <- runningGoal
  frozen <- traverse freeze message
  raiseDiagnostic (SynthesisFailed { goal, message: frozen })

-- | Warn with the message given, and go on. The warning is kept only where the
-- | attempt, and every `transact` around the warning, commits.
warn :: P.Array MessagePart -> Elab Unit
warn message = do
  goal <- runningGoal
  frozen <- traverse freeze message
  recordWarning { goal, message: frozen }

-- | Wait until one of the metavariables named is solved: the attempt ends, and
-- | the goal is run again from its beginning once one is.
-- |
-- | **Whether each can wake the goal is decided where the attempt ends, against
-- | `Ψ` as its rollback leaves it**, and not here: a metavariable this attempt
-- | solved is unsolved again once it is rolled back, and is then as good a thing
-- | to wait on as any. One the attempt created, one solved before it, and an
-- | empty set are defects then, as every postponement's are.
postpone :: forall a. P.Array Handle -> Elab a
postpone metas = traverse resolveMeta metas >>= \ms -> Elab.postpone (Set.fromFoldable ms)

-- A part of a message as it stands now: a handle resolved and what it holds
-- zonked, so that the report does not change as `Ψ` does.
freeze :: MessagePart -> Elab FrozenMessagePart
freeze part = do
  metas <- currentMetas
  case part of
    TextPart text -> pure (FrozenText text)
    NamePart name -> pure (FrozenName name)
    TypePart handle -> resolveType handle <#> \o -> FrozenType { type: substitute metas o.type, kind: o.kind }
    TermPart handle -> resolveExpr handle <#> \o -> FrozenTerm { term: zonkExpr metas o.term, claimed: substitute metas o.claimed }

-- The goal the frame is running, summed up for a report. A report is a
-- synthesizer's, so a frame running no goal is a defect of whoever reported.
runningGoal :: Elab GoalSummary
runningGoal = do
  env <- askEnv
  metas <- currentMetas
  case env.frame of
    Nothing -> break NoFrame
    Just frame -> case frame.goal of
      Nothing -> break NoGoal
      Just running ->
        let
          goal = goalOf running.goal
        in
          pure
            { origin: frame.site.origin
            , pending: running.id
            , synthesizer: goal.synthesizer
            , expectedType: substitute metas goal.expectedType
            }
