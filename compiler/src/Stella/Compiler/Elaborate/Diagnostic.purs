-- | What a failure reports, in the two kinds there are.
-- |
-- | A **diagnostic** is a statement about the program being compiled. It is what
-- | `throw` carries and what a `Failed` attempt holds, and it is one of the three
-- | outcomes a goal has: one says the goal cannot be decided yet, this one that
-- | it cannot be decided at all.
-- |
-- | A **defect** is a statement about the mechanism, or about what drove it, and
-- | it is no outcome of a goal. The two are kept apart because what may be caught
-- | differs: a search tries a candidate and reads a failure as "not this one",
-- | which is right for a diagnostic and hides a defect.
module Stella.Compiler.Elaborate.Diagnostic
  ( Diagnostic(..)
  , Defect(..)
  ) where

import Prelude

import Stella.Compiler.Elaborate.Context (Origin)
import Stella.Compiler.Elaborate.Obligation (Basis, Breach)
import Stella.Compiler.Elaborate.Row (XRowError)
import Stella.Compiler.Elaborate.Unify (UnifyError)
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

data Diagnostic
  -- | An equation no substitution satisfies, reported at the site it stands at.
  = EquationFailed Origin UnifyError
  -- | An assignment that broke a row constraint.
  -- |
  -- | **Two places are named because two are involved.** `equation` is where the
  -- | assignment was made, and `obligation` is the site the constraint came
  -- | from, whose facts are what decided it; the two are one site only by
  -- | coincidence. `basis` says which of the two it was — an assumption the
  -- | assignment made unsatisfiable, or a requirement it left unproved.
  | ObligationBroken
      { equation :: Origin
      , obligation :: Origin
      , basis :: Basis
      , breach :: Breach
      }

-- | Something the mechanism, or whoever drove it, got wrong.
-- |
-- | **Nothing catches one, and that is the whole of why it is not a diagnostic.**
-- | A checkpoint is for trying a candidate that may not work out, and what says a
-- | candidate did not is a diagnostic; a defect says the solver was driven
-- | against its contract or has broken an invariant of its own. Caught as a
-- | failure, it would send a search on to the next candidate with the defect
-- | reported nowhere — or reported to the author as a type error, about a program
-- | nothing is wrong with.
data Defect
  -- | What a unification reports about **its caller**: a metavariable `Ψ` does
  -- | not hold or holds solved already, a kind metavariable it does not hold, or
  -- | a journal of assignments nobody has acted on. Another candidate repairs
  -- | none of them.
  = UnifierMisuse Origin UnifyError
  -- | The subject of a row constraint zonked to something with no row normal
  -- | form. Only a row metavariable is named by a row constraint, so this is an
  -- | invariant of the solver rather than a property of the program. The origin
  -- | is the site the obligation came from, that being where the constraint was
  -- | taken on.
  | ObligationSubjectNotARow Origin XRowError

derive instance Eq Diagnostic
derive instance Generic Diagnostic _

instance Show Diagnostic where
  show x = genericShow x

derive instance Eq Defect
derive instance Generic Defect _

instance Show Defect where
  show x = genericShow x
