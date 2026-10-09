-- | The labels and tags of a row: a record type, a record literal or its
-- | update, a record pattern, a variant's row, and an effect row each write a
-- | label once, and a variant's row a tag once.
module Stella.Compiler.Resolve.Label
  ( reportLabelsTwice
  , reportTagsTwice
  ) where

import Prelude

import Data.Array as Array
import Data.Foldable (foldM)
import Stella.Compiler.CST.Types (Name)
import Stella.Compiler.Resolve.Monad (Resolve, ResolveReason(..), report)

-- | Reports each label written after one of its spelling, in the order
-- | written. A pun is a label, and a spread or a rest is none.
reportLabelsTwice :: Array Name -> Resolve Unit
reportLabelsTwice = reportTwice LabelTwice

-- | Reports each tag written after one of its spelling, in the order written.
reportTagsTwice :: Array Name -> Resolve Unit
reportTagsTwice = reportTwice TagTwice

reportTwice :: (String -> ResolveReason) -> Array Name -> Resolve Unit
reportTwice reason names = void (foldM step [] names)
  where
  step seen n
    | Array.elem n.name seen = report n.range (reason n.name) $> seen
    | otherwise = pure (Array.snoc seen n.name)
