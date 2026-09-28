-- | The `Base` operations as JavaScript expressions.
-- |
-- | An operation is carried out where it stands rather than called through
-- | anything supplied beside the program, and what each one means is the ABI's
-- | ([Prim and Base](../../../../../docs/technical-references/06-Modules/02-Prim-and-Base.md)).
-- | Where the host's operator and that meaning part, the expression implements the
-- | meaning: `Base.Int.mul` is `Math.imul` and not `(a * b) | 0`, which loses the
-- | low bits of a product wider than 53.
module Stella.Compiler.JavaScript.Operation
  ( inline
  ) where

import Prim as P

import Data.Maybe (Maybe(..))
import Stella.Compiler.JavaScript.Syntax (Expr(..))
import Stella.Compiler.Primitive (PrimOp(..))

-- | The expression carrying the operation out over operands already evaluated,
-- | or nothing for an operation this backend does not carry out yet.
inline :: PrimOp -> Maybe (P.Array Expr -> Expr)
inline = case _ of
  IntAdd -> Just (binary \a b -> wrap (Binary "+" a b))
  IntSub -> Just (binary \a b -> wrap (Binary "-" a b))
  IntMul -> Just (binary \a b -> Call (Member (Ident "Math") "imul") [ a, b ])
  IntEq -> Just (binary (Binary "==="))
  IntLt -> Just (binary (Binary "<"))
  _ -> Nothing

-- | The result read as a 32-bit signed integer, which is what wrapping modulo
-- | 2³² gives (D37).
wrap :: Expr -> Expr
wrap e = Binary "|" e (Number "0")

binary :: (Expr -> Expr -> Expr) -> P.Array Expr -> Expr
binary f = case _ of
  [ a, b ] -> f a b
  -- the count was checked against the operation's arity before code is generated
  _ -> Call (Member (Ident "rt") "unreachable") [ String "an operation given another count" ]
