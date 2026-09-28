-- | Accepting a synthesizer's result as the solution of its goal.
-- |
-- | **Acceptance runs inside the attempt, before it commits**, so a result that
-- | fails it fails the attempt, rolled back with everything the synthesizer
-- | did. It is run where no transaction and no binder is open.
module Stella.Compiler.Elaborate.Accept
  ( acceptResult
  ) where

import Prelude

import Stella.Compiler.Elaborate.Diagnostic (Defect(..))
import Stella.Compiler.Elaborate.Elab (Elab, askEnv, assignTerm, break, resolveExpr, unify)
import Stella.Compiler.Elaborate.Handle (Handle, rootScopeId)
import Stella.Compiler.Elaborate.Kind (XKind(..))
import Stella.Compiler.Elaborate.Pending (goalOf)
import Data.Maybe (Maybe(..))

-- | Accept the Expr handle given as the running goal's result.
-- |
-- | The term must be built in the goal's root scope: only there does what it
-- | may mention agree with where the goal stands, and one built anywhere else is
-- | a defect of the synthesizer. **Its claim is unified with the goal's type
-- | before the term is assigned**, which is what lets the goal's type be learned
-- | from the result, and what refuses a result claiming a type the goal does not
-- | have: a failure, or a postponement where the equation waits. The term is
-- | then assigned to the goal's target.
acceptResult :: Handle -> Elab Unit
acceptResult result = do
  env <- askEnv
  case env.frame of
    Nothing -> break NoFrame
    Just frame -> case frame.goal of
      Nothing -> break NoGoal
      Just running -> do
        e <- resolveExpr result
        when (e.builtIn /= Just rootScopeId) (break (ResultNotAtRoot result))
        let
          goal = goalOf running.goal
        unify frame.site { kind: XKType, left: e.claimed, right: goal.expectedType }
        assignTerm frame.site goal.target e.term
