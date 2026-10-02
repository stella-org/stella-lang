-- | Where a node of the Surface AST came from.
-- |
-- | Every node carries an origin, which is what a diagnostic about the node is
-- | located by. A node built from source carries the range of the source it was
-- | built from; a node an expansion or a desugaring produces carries what it
-- | was produced from instead.
module Stella.Compiler.Surface.Origin
  ( Origin(..)
  , rangeOf
  , spanning
  ) where

import Prelude

import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Stella.Compiler.CST.Range (covering)
import Stella.Compiler.CST.Types (SourceRange)

data Origin
  -- | Built from the source text the range covers.
  = FromSource SourceRange

-- | The source range an origin stands for.
rangeOf :: Origin -> SourceRange
rangeOf = case _ of
  FromSource r -> r

-- | The origin of a node built from two others, covering both.
spanning :: Origin -> Origin -> Origin
spanning a b = FromSource (covering (rangeOf a) (rangeOf b))

derive instance Eq Origin
derive instance Generic Origin _

instance Show Origin where
  show = genericShow
