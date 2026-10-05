-- | A module's values grouped by what they refer to: each strongly connected
-- | component of the reference graph a group, the groups in dependency order.
-- |
-- | **The order is a stable topological order.** A group stands after every
-- | group it refers to; among the groups that may stand next, the one holding
-- | the declaration written first does. Declarations are told apart by their
-- | ordinal, their place in the module's list of declarations, which two never
-- | share. A group lists its members in that order too.
module Stella.Compiler.Elaborate.Surface.Group
  ( Group
  , groups
  ) where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl)
import Data.List (List(..), (:))
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Set (Set)
import Data.Set as Set
import Data.Tuple (Tuple(..))

-- | A strongly connected component: its members' ordinals, ascending, and
-- | whether it is recursive — more than one member, or one referring to itself.
type Group = { members :: Array Int, recursive :: Boolean }

-- | The groups of the nodes `0 .. n - 1`, the node at index `i` referring to
-- | the nodes `refers !! i` names. A reference to no node is ignored.
groups :: Array (Set Int) -> Array Group
groups refers = ordered
  where
  n = Array.length refers
  successors v = Array.filter (\w -> w >= 0 && w < n) (Array.fromFoldable (fromMaybe Set.empty (Array.index refers v)))

  components = map Array.sort (strongComponents n successors)
  componentOf = Map.fromFoldable (Array.concat (Array.mapWithIndex (\c ms -> map (\m -> Tuple m c) ms) components))
  component v = fromMaybe 0 (Map.lookup v componentOf)

  -- the components each one refers to, itself aside
  needs = Array.mapWithIndex (\c ms -> Set.delete c (Set.fromFoldable (map component (Array.concatMap successors ms)))) components
  neededBy = foldl
    (\acc (Tuple c ds) -> foldl (\a d -> Map.insertWith (<>) d [ c ] a) acc (Array.fromFoldable ds))
    Map.empty
    (Array.mapWithIndex Tuple needs)

  -- a component is keyed by its first member, the ready ones taken least first
  key c = case Array.index components c >>= Array.head of
    Just m -> m
    Nothing -> 0
  initial = Set.fromFoldable (Array.mapMaybe (\(Tuple c ds) -> if Set.isEmpty ds then Just (Tuple (key c) c) else Nothing) (Array.mapWithIndex Tuple needs))
  waiting = Map.fromFoldable (Array.mapWithIndex (\c ds -> Tuple c (Set.size ds)) needs)

  ordered = emit initial waiting []
  emit ready left acc = case Set.findMin ready of
    Nothing -> acc
    Just next@(Tuple _ c) ->
      let
        released = fromMaybe [] (Map.lookup c neededBy)
        left' = foldl (\m d -> Map.update (\k -> Just (k - 1)) d m) left released
        newlyReady = Array.filter (\d -> Map.lookup d left' == Just 0) released
        ready' = foldl (\s d -> Set.insert (Tuple (key d) d) s) (Set.delete next ready) newlyReady
        members = fromMaybe [] (Array.index components c)
      in
        emit ready' left' (Array.snoc acc { members, recursive: Array.length members > 1 || Array.any (\m -> Array.elem m (successors m)) members })

type Tarjan =
  { index :: Map Int Int
  , low :: Map Int Int
  , stack :: List Int
  , onStack :: Set Int
  , next :: Int
  , found :: Array (Array Int)
  }

-- | The strongly connected components of the nodes `0 .. n - 1` (Tarjan).
strongComponents :: Int -> (Int -> Array Int) -> Array (Array Int)
strongComponents n successors
  | n <= 0 = []
  | otherwise = (foldl start empty (Array.range 0 (n - 1))).found
      where
      empty = { index: Map.empty, low: Map.empty, stack: Nil, onStack: Set.empty, next: 0, found: [] }
      start s v = if Map.member v s.index then s else visit v s

      visit v s0 =
        let
          s1 = s0
            { index = Map.insert v s0.next s0.index
            , low = Map.insert v s0.next s0.low
            , stack = v : s0.stack
            , onStack = Set.insert v s0.onStack
            , next = s0.next + 1
            }
          s2 = foldl (edge v) s1 (successors v)
        in
          if Map.lookup v s2.low == Map.lookup v s2.index then pop v [] s2 else s2

      edge v s w
        | not (Map.member w s.index) = let s' = visit w s in lower v (at w s'.low) s'
        | Set.member w s.onStack = lower v (at w s.index) s
        | otherwise = s

      lower v x s = s { low = Map.insert v (min x (at v s.low)) s.low }
      at v m = fromMaybe 0 (Map.lookup v m)

      pop v acc s = case s.stack of
        w : rest ->
          let
            s' = s { stack = rest, onStack = Set.delete w s.onStack }
          in
            if w == v then s' { found = Array.snoc s.found (Array.cons w acc) } else pop v (Array.cons w acc) s'
        Nil -> s
