-- | The `Base` operations as JavaScript expressions.
-- |
-- | An operation is carried out where it stands rather than called through
-- | anything supplied beside the program, and what each one means is the ABI's
-- | ([Prim and Base](../../../../../docs/technical-references/06-Modules/02-Prim-and-Base.md)).
-- | Where the host's operator and that meaning part, the expression implements the
-- | meaning:
-- |
-- | | Operation | Not the host's | Because |
-- | | --- | --- | --- |
-- | | `Base.Int.mul` | `(a * b) \| 0` | a product wider than 53 bits loses its low bits in binary64; `Math.imul` does not |
-- | | `Base.Int.quot`, `rem` | `/`, `%` alone | a zero divisor faults |
-- | | `Base.Number.toInt` | `\| 0` | the ABI saturates; `\| 0` wraps |
-- | | `Base.String.length`, `codePointAt`, `slice` | `.length`, indexing, `.slice` | they count scalar values, not UTF-16 code units (D27) |
-- | | `Base.String.lt` | `<` | the order is by scalar value; `<` compares code units, which puts an astral character below `U+E000` |
-- |
-- | What cannot be one expression — a check that faults, a count of scalar values —
-- | calls the runtime, bound as `rt` in every generated module. **Every operation of
-- | the version has an expression**, so this is total and no operation a module
-- | names is left without one.
module Stella.Backend.JavaScript.Operation
  ( inline
  ) where

import Prim as P

import Stella.Backend.JavaScript.Syntax (Expr(..))
import Stella.Compiler.Primitive (PrimOp(..))

-- | The expression carrying the operation out over operands already evaluated.
inline :: PrimOp -> P.Array Expr -> Expr
inline = case _ of
  IntAdd -> binary \a b -> wrap (Binary "+" a b)
  IntSub -> binary \a b -> wrap (Binary "-" a b)
  IntMul -> binary \a b -> Call (Member (Ident "Math") "imul") [ a, b ]
  IntQuot -> runtime "quot"
  IntRem -> runtime "rem"
  IntEq -> binary (Binary "===")
  IntLt -> binary (Binary "<")
  -- an `Int` is a number already, and every one is exact in binary64
  IntToNumber -> unary \a -> a
  IntToString -> unary \a -> Call (Ident "String") [ a ]
  NumberAdd -> binary (Binary "+")
  NumberSub -> binary (Binary "-")
  NumberMul -> binary (Binary "*")
  NumberDivide -> binary (Binary "/")
  -- the sign flipped, so `0.0` gives `-0.0`, which `0.0 - x` would not
  NumberNegate -> unary (Unary "-")
  -- IEEE equality and less-than: false wherever NaN takes part, and the two
  -- zeros equal
  NumberEq -> binary (Binary "===")
  NumberLt -> binary (Binary "<")
  NumberFloor -> unary \a -> Call (Member (Ident "Math") "floor") [ a ]
  NumberCeil -> unary \a -> Call (Member (Ident "Math") "ceil") [ a ]
  NumberTrunc -> unary \a -> Call (Member (Ident "Math") "trunc") [ a ]
  NumberToInt -> runtime "numberToInt"
  -- `Number::toString(x, 10)` of ECMA-262, 15th edition, is what `String` gives
  NumberToString -> unary \a -> Call (Ident "String") [ a ]
  StringLength -> runtime "stringLength"
  StringCodePointAt -> runtime "codePointAt"
  StringAppend -> binary (Binary "+")
  StringSlice -> runtime "slice"
  StringSingleton -> unary \a -> Call (Member (Ident "String") "fromCodePoint") [ a ]
  -- a `String` holds scalar values only, so equal code units are equal scalars
  StringEq -> binary (Binary "===")
  StringLt -> runtime "stringLt"
  -- a `Char` is held as the number of its scalar value
  CharToCodePoint -> unary \a -> a
  CharFromCodePoint -> runtime "fromCodePoint"
  ArrayLength -> unary \a -> Member a "length"
  ArrayUnsafeNew -> runtime "arrayNew"
  ArrayUnsafeSet -> runtime "arraySet"
  ArrayUnsafeIndex -> runtime "arrayIndex"

-- | The result read as a 32-bit signed integer, which is what wrapping modulo
-- | 2³² gives (D37).
wrap :: Expr -> Expr
wrap e = Binary "|" e (Number "0")

runtime :: P.String -> P.Array Expr -> Expr
runtime name = Call (Member (Ident "rt") name)

unary :: (Expr -> Expr) -> P.Array Expr -> Expr
unary f = case _ of
  [ a ] -> f a
  _ -> miscounted

binary :: (Expr -> Expr -> Expr) -> P.Array Expr -> Expr
binary f = case _ of
  [ a, b ] -> f a b
  _ -> miscounted

-- | The count is checked against the operation's arity before code is generated.
miscounted :: Expr
miscounted = Call (Member (Ident "rt") "unreachable") [ String "an operation given another count" ]
