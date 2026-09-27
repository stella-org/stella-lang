-- | The primitive operations of the `Base` ABI surface.
-- |
-- | A `Base` ABI entry whose meaning the ABI fixes is an **operation**, not an
-- | implementation: every consumer carries it out directly rather than calling
-- | something a backend supplied separately. Naming the operation is what lets a
-- | machine add two integers in its dispatch loop and a JavaScript backend emit
-- | `a + b`, neither of them recognizing a qualified name to find out.
-- |
-- | **This table stands in for the ABI manifest**, which defines the surface and
-- | is implemented by a compiler and its backends together
-- | ([Prim and Base](../../../../docs/technical-references/06-Modules/02-Prim-and-Base.md)).
-- | It is keyed to one ABI version, and it grows as the content of that version
-- | is settled. Until the manifest exists, this is where a compiler reads it.
module Stella.Compiler.Primitive
  ( PrimOp(..)
  , PrimEntry
  , primTable
  , lookupPrim
  , entryOfOp
  , codeOfOp
  , opOfCode
  , arityOfOp
  ) where

import Prelude

import Prim as P

import Stella.Compiler.TypedCore.Name (Ident(..), ModuleName(..), Qualified(..))
import Data.Array as Array
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe)
import Data.Show.Generic (genericShow)

-- | The operations `stella-base-0.1` fixes.
-- |
-- | Each is a `Base` entry that returns no `IO`: a native leaf action names an
-- | implementation and stays a `foreign`, as does anything of a target
-- | namespace, whose meaning is one target's rather than the ABI's.
data PrimOp
  = IntAdd
  | IntSub
  | IntMul
  | IntQuot
  | IntRem
  | IntEq
  | IntLt
  | IntToNumber
  | IntToString
  | NumberAdd
  | NumberSub
  | NumberMul
  | NumberDivide
  | NumberNegate
  | NumberEq
  | NumberLt
  | NumberFloor
  | NumberCeil
  | NumberTrunc
  | NumberToInt
  | NumberToString
  | StringLength
  | StringCodePointAt
  | StringAppend
  | StringSlice
  | StringSingleton
  | StringEq
  | StringLt
  | CharToCodePoint
  | CharFromCodePoint
  | ArrayLength
  | ArrayUnsafeNew
  | ArrayUnsafeSet
  | ArrayUnsafeIndex

-- | What an operation realizes, and what a consumer owes it.
-- |
-- | `entry` is the `Base` name, which is what target validation reads: an
-- | operation is how the entry is carried out and not a way of not using it, so
-- | a backend still owes the entry at the profile that holds it.
-- |
-- | **The mapping between an operation and its entry has one definition**, in
-- | `entryOfOp`. Carrying the two independently anywhere would let a reader
-- | check one entry while a machine ran another operation.
-- |
-- | **What an operation means, and whether it may fault, is not here and is not
-- | the compiler's to say.** The ABI specification fixes it, which is what obliges
-- | every backend to one observable meaning: `stella-base-0.1` has `Base.Int.add`
-- | and `Base.Int.sub` wrap, so a backend on a host that traps on overflow owes the
-- | wrapping form, and it has `Base.String.codePointAt` and `Base.Array.unsafeIndex`
-- | fault outside their range
-- | ([Prim and Base](../../../../docs/technical-references/06-Modules/02-Prim-and-Base.md)).
type PrimEntry =
  { op :: PrimOp
  , entry :: Qualified Ident
  , arity :: P.Int
  }

-- | The `Base` entry an operation realizes. Total, and the one place the
-- | correspondence is written.
entryOfOp :: PrimOp -> Qualified Ident
entryOfOp = case _ of
  IntAdd -> base "Base.Int" "add"
  IntSub -> base "Base.Int" "sub"
  IntMul -> base "Base.Int" "mul"
  IntQuot -> base "Base.Int" "quot"
  IntRem -> base "Base.Int" "rem"
  IntEq -> base "Base.Int" "eq"
  IntLt -> base "Base.Int" "lt"
  IntToNumber -> base "Base.Int" "toNumber"
  IntToString -> base "Base.Int" "toString"
  NumberAdd -> base "Base.Number" "add"
  NumberSub -> base "Base.Number" "sub"
  NumberMul -> base "Base.Number" "mul"
  NumberDivide -> base "Base.Number" "divide"
  NumberNegate -> base "Base.Number" "negate"
  NumberEq -> base "Base.Number" "eq"
  NumberLt -> base "Base.Number" "lt"
  NumberFloor -> base "Base.Number" "floor"
  NumberCeil -> base "Base.Number" "ceil"
  NumberTrunc -> base "Base.Number" "trunc"
  NumberToInt -> base "Base.Number" "toInt"
  NumberToString -> base "Base.Number" "toString"
  StringLength -> base "Base.String" "length"
  StringCodePointAt -> base "Base.String" "codePointAt"
  StringAppend -> base "Base.String" "append"
  StringSlice -> base "Base.String" "slice"
  StringSingleton -> base "Base.String" "singleton"
  StringEq -> base "Base.String" "eq"
  StringLt -> base "Base.String" "lt"
  CharToCodePoint -> base "Base.Char" "toCodePoint"
  CharFromCodePoint -> base "Base.Char" "fromCodePoint"
  ArrayLength -> base "Base.Array" "length"
  ArrayUnsafeNew -> base "Base.Array" "unsafeNew"
  ArrayUnsafeSet -> base "Base.Array" "unsafeSet"
  ArrayUnsafeIndex -> base "Base.Array" "unsafeIndex"
  where
  base moduleName name = Qualified (ModuleName moduleName) (Ident name)

-- | The code an operation carries in a `.dmo`. Total, and the one place the
-- | code is written.
-- |
-- | **A code is written rather than derived**: a position in this table, or an
-- | alphabetical rank, would change a published file's meaning as soon as an
-- | operation were added. It is fixed for the life of an ABI version, and the
-- | code of an operation a later version drops is not reused
-- | ([Encoding](../../../../docs/technical-references/05-Backend/02-Encoding.md)).
codeOfOp :: PrimOp -> P.Int
codeOfOp = case _ of
  IntAdd -> 0x01
  IntSub -> 0x02
  IntMul -> 0x03
  IntQuot -> 0x04
  IntRem -> 0x05
  IntEq -> 0x06
  IntLt -> 0x07
  IntToNumber -> 0x08
  IntToString -> 0x09
  StringLength -> 0x10
  StringCodePointAt -> 0x11
  StringAppend -> 0x12
  StringSlice -> 0x13
  StringSingleton -> 0x14
  StringEq -> 0x15
  StringLt -> 0x16
  ArrayUnsafeIndex -> 0x20
  ArrayUnsafeNew -> 0x21
  ArrayUnsafeSet -> 0x22
  ArrayLength -> 0x23
  NumberAdd -> 0x30
  NumberSub -> 0x31
  NumberMul -> 0x32
  NumberDivide -> 0x33
  NumberNegate -> 0x34
  NumberEq -> 0x35
  NumberLt -> 0x36
  NumberFloor -> 0x37
  NumberCeil -> 0x38
  NumberTrunc -> 0x39
  NumberToInt -> 0x3A
  NumberToString -> 0x3B
  CharToCodePoint -> 0x40
  CharFromCodePoint -> 0x41

-- | The operation a code names, where this ABI version names one. A reader of a
-- | code it does not hold rejects the file: what an operation realizes is not
-- | derivable from the file.
opOfCode :: P.Int -> Maybe PrimOp
opOfCode code = map _.op (Array.find (\e -> codeOfOp e.op == code) primTable)

-- | How many arguments saturate an operation. Total, and the one place the
-- | arity is written.
arityOfOp :: PrimOp -> P.Int
arityOfOp = case _ of
  IntAdd -> 2
  IntSub -> 2
  IntMul -> 2
  IntQuot -> 2
  IntRem -> 2
  IntEq -> 2
  IntLt -> 2
  IntToNumber -> 1
  IntToString -> 1
  NumberAdd -> 2
  NumberSub -> 2
  NumberMul -> 2
  NumberDivide -> 2
  NumberNegate -> 1
  NumberEq -> 2
  NumberLt -> 2
  NumberFloor -> 1
  NumberCeil -> 1
  NumberTrunc -> 1
  NumberToInt -> 1
  NumberToString -> 1
  StringLength -> 1
  StringCodePointAt -> 2
  StringAppend -> 2
  StringSlice -> 3
  StringSingleton -> 1
  StringEq -> 2
  StringLt -> 2
  CharToCodePoint -> 1
  CharFromCodePoint -> 1
  ArrayUnsafeIndex -> 2
  ArrayUnsafeNew -> 1
  ArrayUnsafeSet -> 3
  ArrayLength -> 1

primTable :: P.Array PrimEntry
primTable = map (\op -> { op, entry: entryOfOp op, arity: arityOfOp op })
  [ IntAdd
  , IntSub
  , IntMul
  , IntQuot
  , IntRem
  , IntEq
  , IntLt
  , IntToNumber
  , IntToString
  , NumberAdd
  , NumberSub
  , NumberMul
  , NumberDivide
  , NumberNegate
  , NumberEq
  , NumberLt
  , NumberFloor
  , NumberCeil
  , NumberTrunc
  , NumberToInt
  , NumberToString
  , StringLength
  , StringCodePointAt
  , StringAppend
  , StringSlice
  , StringSingleton
  , StringEq
  , StringLt
  , CharToCodePoint
  , CharFromCodePoint
  , ArrayUnsafeIndex
  , ArrayUnsafeNew
  , ArrayUnsafeSet
  , ArrayLength
  ]

-- | The operation a `Base` entry is, where it is one.
lookupPrim :: Qualified Ident -> Maybe PrimEntry
lookupPrim name = Array.find (\e -> e.entry == name) primTable

derive instance Eq PrimOp
derive instance Ord PrimOp
derive instance Generic PrimOp _

instance Show PrimOp where
  show = genericShow
