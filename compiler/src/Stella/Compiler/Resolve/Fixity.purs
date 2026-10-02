-- | Rebracketing a chain of operators by their fixities, for expressions and
-- | types alike.
-- |
-- | The parser reads a chain in the order written, every operator at one
-- | precedence. Here the higher precedence binds tighter, and two operators of
-- | one precedence associate as both declare: to the left where both are
-- | `infixl`, to the right where both are `infixr`. Any other pair of one
-- | precedence — an `infixl` beside an `infixr`, or an `infix` beside anything —
-- | is unordered, and the chain needs parentheses.
module Stella.Compiler.Resolve.Fixity
  ( Fixity
  , Unordered
  , rebracket
  ) where

import Prelude

import Data.Either (Either(..))
import Data.Foldable (foldM)
import Data.List (List(..), (:))
import Data.Tuple (Tuple(..))
import Stella.Compiler.Surface.Decl (Associativity(..))

type Fixity = { associativity :: Associativity, precedence :: Int }

-- | Two operators of one precedence that cannot be chained: the one standing
-- | first, and the one after it.
type Unordered op = { first :: op, second :: op }

type Stacks op a = { operands :: List a, operators :: List op }

-- | Rebrackets a chain: its first operand, then each operator with the operand
-- | after it.
rebracket
  :: forall op a
   . (op -> Fixity)
  -> (op -> a -> a -> a)
  -> a
  -> Array (Tuple op a)
  -> Either (Unordered op) a
rebracket fixity combine first rest = do
  stacks <- foldM push { operands: first : Nil, operators: Nil } rest
  pure (finish (reduceWhile (const true) stacks))
  where
  push stacks (Tuple op operand) = do
    reduced <- reduceBefore op stacks
    pure { operands: operand : reduced.operands, operators: op : reduced.operators }

  -- Applies every operator on the stack that binds tighter than the one coming.
  reduceBefore op stacks = case stacks.operators of
    top : _ -> case tighter top op of
      Right true -> reduceBefore op (reduceOne stacks)
      Right false -> Right stacks
      Left unordered -> Left unordered
    Nil -> Right stacks

  tighter earlier later =
    let
      e = fixity earlier
      l = fixity later
    in
      case compare e.precedence l.precedence of
        GT -> Right true
        LT -> Right false
        EQ -> case e.associativity, l.associativity of
          AssociateLeft, AssociateLeft -> Right true
          AssociateRight, AssociateRight -> Right false
          _, _ -> Left { first: earlier, second: later }

  reduceWhile p stacks = case stacks.operators of
    top : _ | p top -> reduceWhile p (reduceOne stacks)
    _ -> stacks

  reduceOne stacks = case stacks.operators, stacks.operands of
    op : ops, r : l : ands -> { operands: combine op l r : ands, operators: ops }
    _, _ -> stacks

  finish stacks = case stacks.operands of
    a : _ -> a
    Nil -> first
