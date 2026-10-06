-- | Where a node of the Surface AST came from.
-- |
-- | Every node carries an origin, which is what a diagnostic about the node is
-- | located by. A node built from source carries the range of the source it was
-- | built from. A node built from what an expansion of a macro produced carries
-- | its range in that expansion, the macro, the origin of the call, and the
-- | origin of what its tokens were written as: the call's input, or a
-- | quotation. Either of the two is in an expansion in turn where one wrote it.
module Stella.Compiler.Surface.Origin
  ( Origin(..)
  , originOf
  , rangeOf
  , spanning
  ) where

import Prelude

import Data.Array as Array
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..))
import Data.Show.Generic (genericShow)
import Stella.Compiler.CST.Range (covering)
import Stella.Compiler.CST.Types (RangeSpace(..), SourceRange)
import Stella.Compiler.TypedCore.Name (Ident, Qualified)

data Origin
  -- | Built from the source text the range covers: the module's, or that of
  -- | the module a quotation is written in, which only what a token of an
  -- | expansion was written as is.
  = FromSource SourceRange
  -- | Built from what an expansion produced: the range in it, the macro
  -- | expanded, where its call stands, and where its tokens were written.
  | FromExpansion
      { range :: SourceRange
      , macro :: Qualified Ident
      , call :: Origin
      , written :: Origin
      }

-- | The origin of what a range covers, read from the text the range is in. In
-- | an expansion, what its tokens were written as is read from the expansion's
-- | record of them, by their places in what it produced; a range covering no
-- | token was written nowhere but at the call.
originOf :: SourceRange -> Origin
originOf range = case range.space of
  SourceFile -> FromSource range
  Quotation _ -> FromSource range
  Expansion e ->
    let
      call = originOf e.call
      covered = Array.slice (range.start.column - 1) (range.end.column - 1) e.written
      written = case Array.uncons covered of
        Just { head, tail } -> originOf (Array.foldl covering head tail)
        Nothing -> call
    in
      FromExpansion { range, macro: e.macro, call, written }

-- | The range of the source an origin is located by: its own, or that of the
-- | call written in source that the expansions it came through began at.
rangeOf :: Origin -> SourceRange
rangeOf = case _ of
  FromSource r -> r
  FromExpansion e -> rangeOf e.call

-- | The origin of a node built from two others, covering both. Two origins of
-- | one text are joined; otherwise the first stands.
spanning :: Origin -> Origin -> Origin
spanning a b = originOf (covering (rangeIn a) (rangeIn b))
  where
  rangeIn = case _ of
    FromSource r -> r
    FromExpansion e -> e.range

derive instance Eq Origin
derive instance Generic Origin _

instance Show Origin where
  show x = genericShow x
