-- | The labels of a record: a record type, a record literal or its update, and
-- | a record pattern each write a label once.
module Stella.Compiler.Resolve.Label
  ( reportLabelsTwice
  ) where

import Prelude

import Data.Array as Array
import Data.Foldable (foldM)
import Stella.Compiler.CST.Types (Name)
import Stella.Compiler.Resolve.Monad (Resolve, ResolveReason(..), report)

-- | Reports each label written after one of its spelling, in the order
-- | written. A pun is a label, and a spread or a rest is none.
reportLabelsTwice :: Array Name -> Resolve Unit
reportLabelsTwice labels = void (foldM step [] labels)
  where
  step seen l
    | Array.elem l.name seen = report l.range (LabelTwice l.name) $> seen
    | otherwise = pure (Array.snoc seen l.name)
