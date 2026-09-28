-- | What attempting a pending job came to.
module Stella.Compiler.Elaborate.Attempt
  ( Attempt(..)
  ) where

import Prelude

import Stella.Compiler.Elaborate.Diagnostic (Defect, Diagnostic)
import Stella.Compiler.Elaborate.Type (MetaVar)
import Data.Generic.Rep (class Generic)
import Data.Set (Set)
import Data.Show.Generic (genericShow)

-- | What attempting a pending job came to, once the scheduler has acted on it.
data Attempt
  -- | Solved and committed; the job is gone from every table.
  = Committed
  -- | Postponed, and registered under the metavariables admitted.
  | Registered (Set MetaVar)
  -- | Failed; the job is gone from every table, and the diagnostic is what to
  -- | report.
  | Rejected Diagnostic
  -- | A defect. Nothing further is attempted.
  | Halted Defect

derive instance Eq Attempt
derive instance Generic Attempt _

instance Show Attempt where
  show x = genericShow x
