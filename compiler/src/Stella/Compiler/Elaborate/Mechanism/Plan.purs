-- | Which implicit handlers a checking boundary inserts, and in what order
-- | ([Effect Handlers](../../../../../docs/technical-references/02-Surface-Language/02-Effect-Handlers.md#the-plan)):
-- | the part of the plan read off keys alone.
-- |
-- | **The handlers are found by a worklist** over the keys the body performs
-- | and the row expected lacks, each key taken least first in the canonical
-- | order of keys: the one candidate of `Ξ` whose source has that key, then
-- | the keys its targets add that the row expected lacks and no handler has
-- | been sought for. A key no candidate handles, or several do, ends the
-- | search. **The order is the one the handlers' dependencies give**, a
-- | handler inside every one that handles what it performs. It must be total;
-- | where it is not, the handlers it leaves unordered are reported.
module Stella.Compiler.Elaborate.Mechanism.Plan
  ( PlanFailure(..)
  , ImplicitPlan
  , PlanStep
  , SpineStep(..)
  , searchPlan
  ) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Set as Set
import Data.Show.Generic (genericShow)
import Stella.Compiler.Elaborate.CorePlus.Kind (XKind)
import Stella.Compiler.Elaborate.CorePlus.Type (XRowEntry, XType)
import Stella.Compiler.Elaborate.Environment.Implicit (ImplicitCandidate, compareIdentity)
import Stella.Compiler.TypedCore.Name (Ident, Qualified)
import Stella.Compiler.TypedCore.Type (RowKey, compareRowKeys, rowEntryKey)

-- | A plan a boundary settled, as its lowering reads it: the body's row `ρ1`,
-- | the elements the thunk of the body is widened by, the type the body
-- | answers with, and each handler, innermost first, with what applying it
-- | took.
type ImplicitPlan =
  { source :: XType
  , widening :: Array XRowEntry
  , answer :: XType
  , steps :: Array PlanStep
  }

-- | A handler of a plan: the global, the kinds its scheme's kind quantifiers
-- | were opened at, its scheme's spine as it was opened, the row of the thunk
-- | it is applied to, and the row it leaves.
type PlanStep =
  { handler :: Qualified Ident
  , kinds :: Array XKind
  , spine :: Array SpineStep
  , input :: XType
  , output :: XType
  }

-- | A quantifier opened at the type given, or a constraint required.
data SpineStep
  = SpineType XType
  | SpineConstraint

-- | Why no plan is read off the keys.
data PlanFailure
  -- | A key no candidate handles.
  = PlanMissing RowKey
  -- | A key several candidates handle, those in the order of their identities.
  | PlanSeveral RowKey (Array (Qualified Ident))
  -- | Handlers the dependencies leave unordered, in the order of their
  -- | identities.
  | PlanUnordered (Array (Qualified Ident))

-- | The handlers a boundary inserts, innermost first, given the candidates,
-- | the keys the body performs that the row expected lacks, and the keys the
-- | row expected holds.
searchPlan :: Array ImplicitCandidate -> Set RowKey -> Set RowKey -> Either PlanFailure (Array ImplicitCandidate)
searchPlan candidates removed expected = found [] Set.empty (Array.fromFoldable removed) >>= ordered
  where
  found plan processed worklist = case Array.head (Array.sortBy compareRowKeys worklist) of
    Nothing -> Right plan
    Just k -> case Array.sortBy (\a b -> compareIdentity a.handler b.handler) (Array.filter (\c -> rowEntryKey c.source == k) candidates) of
      [] -> Left (PlanMissing k)
      [ h ] ->
        let
          done = Set.insert k processed
          added = Array.filter (\t -> not (Set.member t expected || Set.member t done || Array.elem t worklist)) (map rowEntryKey h.targets)
        in
          found (Array.snoc plan h) done (Array.delete k worklist <> added)
      several -> Left (PlanSeveral k (map _.handler several))

  -- `h` stands inside `h'` where `h'` handles what `h` performs; the order is
  -- the one topological order there is, innermost first
  ordered plan = go [] plan
    where
    inside h h' = Array.elem (rowEntryKey h'.source) (map rowEntryKey h.targets)
    go acc left = case Array.filter (\h -> not (Array.any (\h' -> inside h' h) left)) left of
      [] | Array.null left -> Right acc
      [] -> Left (PlanUnordered (map _.handler (Array.sortBy (\a b -> compareIdentity a.handler b.handler) left)))
      [ h ] -> go (Array.snoc acc h) (Array.filter (\h' -> h'.handler /= h.handler) left)
      ready -> Left (PlanUnordered (map _.handler (Array.sortBy (\a b -> compareIdentity a.handler b.handler) ready)))

derive instance Eq SpineStep
derive instance Generic SpineStep _

instance Show SpineStep where
  show x = genericShow x
