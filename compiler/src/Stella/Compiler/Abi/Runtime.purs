-- | The runtime-facing ABI catalog: the `Base` entries of `stella-base-0.1` a
-- | runtime carries out itself, as a runtime or a backend reads them — each
-- | entry's name, arity, runtime class, and profile, and the code of each
-- | operation.
-- |
-- | **Nothing here is a compiler's representation.** A name is text and no type
-- | is written: what an entry is declared at is the compiler's, keyed by the
-- | entry's identity ([Primitive](../Primitive.purs)). The catalog stands in for
-- | the ABI manifest, which a compiler and its backends implement together
-- | ([Prim and Base](../../../../../docs/technical-references/06-Modules/02-Prim-and-Base.md)).
-- |
-- | **An entry's name and arity are written once, here**, and so is an
-- | operation's code: a runtime classifies a foreign by its name against this
-- | table, and checks the arity it is declared at against the one given here.
module Stella.Compiler.Abi.Runtime
  ( PrimOp(..)
  , RuntimeEntryId(..)
  , RuntimeClass(..)
  , Profile(..)
  , includes
  , EntryName
  , RuntimeEntry
  , operations
  , runtimeEntries
  , runtimeEntryOf
  , lookupRuntimeEntry
  , nameOfOp
  , arityOfOp
  , codeOfOp
  , opOfCode
  , InClosedRun(..)
  , inClosedRunOf
  ) where

import Prelude

import Prim as P

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

-- | An entry the runtime carries out itself: an operation, or one of the two
-- | `Base.IO` entries.
data RuntimeEntryId
  = Operation PrimOp
  | IOPure
  | IOBind

-- | How the runtime carries an entry out. An **operation** is carried out as
-- | the operation it is, a call to it lowered to the operation in bytecode. An
-- | **IO entry** builds an `IO` value the runtime runs: it returns `IO`, so no
-- | code stands for it, and a call to it stays a call to a foreign, which the
-- | runtime binds to its own implementation by the entry's name.
data RuntimeClass
  = RuntimeOperation
  | RuntimeIO

-- | A named set of entries a backend undertakes to implement: `core-runtime`,
-- | the two `Base.IO` entries, and `standard`, which holds `core-runtime`.
data Profile
  = CoreRuntime
  | Standard

-- | Whether a backend claiming the first profile owes what the second holds.
includes :: Profile -> Profile -> P.Boolean
includes claimed held = case claimed, held of
  Standard, _ -> true
  CoreRuntime, CoreRuntime -> true
  CoreRuntime, Standard -> false

-- | An entry's name: its module's, and its own within the module.
type EntryName = { module :: P.String, value :: P.String }

type RuntimeEntry =
  { id :: RuntimeEntryId
  , name :: EntryName
  , arity :: P.Int
  , runtimeClass :: RuntimeClass
  , profile :: Profile
  }

-- | The operations, in the order the catalog lists them.
operations :: P.Array PrimOp
operations =
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

-- | Every entry, the operations first, in the order of `operations`.
runtimeEntries :: P.Array RuntimeEntry
runtimeEntries = map runtimeEntryOf (map Operation operations <> [ IOPure, IOBind ])

-- | The entry of an identity. Total.
runtimeEntryOf :: RuntimeEntryId -> RuntimeEntry
runtimeEntryOf id = case id of
  Operation op -> { id, name: nameOfOp op, arity: arityOfOp op, runtimeClass: RuntimeOperation, profile: Standard }
  IOPure -> { id, name: { module: "Base.IO", value: "pure" }, arity: 1, runtimeClass: RuntimeIO, profile: CoreRuntime }
  IOBind -> { id, name: { module: "Base.IO", value: "bind" }, arity: 2, runtimeClass: RuntimeIO, profile: CoreRuntime }

-- | The entry of a name, where the catalog holds one.
lookupRuntimeEntry :: EntryName -> Maybe RuntimeEntry
lookupRuntimeEntry name = Array.find (\e -> e.name.module == name.module && e.name.value == name.value) runtimeEntries

-- | The `Base` entry an operation realizes. Total, and the one place the
-- | correspondence is written.
nameOfOp :: PrimOp -> EntryName
nameOfOp = case _ of
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
  base module' value = { module: module', value }

-- | How many arguments saturate an operation. Total, and the one place the
-- | count is written.
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
  ArrayLength -> 1
  ArrayUnsafeNew -> 1
  ArrayUnsafeSet -> 3
  ArrayUnsafeIndex -> 2

-- | The code an operation carries in a `.dmo`. Total, and the one place the
-- | code is written.
-- |
-- | **A code is written rather than derived**: a position in this table, or an
-- | alphabetical rank, would change a published file's meaning as soon as an
-- | operation were added. It is fixed for the life of an ABI version, and the
-- | code of an operation a later version drops is not reused
-- | ([Encoding](../../../../../docs/technical-references/05-Backend/02-Encoding.md)).
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
opOfCode code = Array.find (\op -> codeOfOp op == code) operations

-- | What an operation is to a closed run, one that reaches no observable state
-- | outside it: carried out as it is, carried out on state the run itself made,
-- | or not carried out at all.
data InClosedRun
  = Admitted
  -- | Its state operands are the run's own, and state it makes becomes the run's.
  | RunLocalState
  | Withheld

-- | Total, and the one place an operation is classified, so an operation added
-- | to the table is classified where it is added.
inClosedRunOf :: PrimOp -> InClosedRun
inClosedRunOf = case _ of
  IntAdd -> Admitted
  IntSub -> Admitted
  IntMul -> Admitted
  IntQuot -> Admitted
  IntRem -> Admitted
  IntEq -> Admitted
  IntLt -> Admitted
  IntToNumber -> Admitted
  IntToString -> Admitted
  NumberAdd -> Admitted
  NumberSub -> Admitted
  NumberMul -> Admitted
  NumberDivide -> Admitted
  NumberNegate -> Admitted
  NumberEq -> Admitted
  NumberLt -> Admitted
  NumberFloor -> Admitted
  NumberCeil -> Admitted
  NumberTrunc -> Admitted
  NumberToInt -> Admitted
  NumberToString -> Admitted
  StringLength -> Admitted
  StringCodePointAt -> Admitted
  StringAppend -> Admitted
  StringSlice -> Admitted
  StringSingleton -> Admitted
  StringEq -> Admitted
  StringLt -> Admitted
  CharToCodePoint -> Admitted
  CharFromCodePoint -> Admitted
  ArrayLength -> RunLocalState
  ArrayUnsafeNew -> RunLocalState
  ArrayUnsafeSet -> RunLocalState
  ArrayUnsafeIndex -> RunLocalState

derive instance Eq InClosedRun
derive instance Generic InClosedRun _
instance Show InClosedRun where
  show = genericShow

derive instance Eq PrimOp
derive instance Ord PrimOp
derive instance Generic PrimOp _

instance Show PrimOp where
  show = genericShow

derive instance Eq RuntimeEntryId
derive instance Ord RuntimeEntryId
derive instance Generic RuntimeEntryId _

instance Show RuntimeEntryId where
  show = genericShow

derive instance Eq RuntimeClass
derive instance Generic RuntimeClass _

instance Show RuntimeClass where
  show = genericShow

derive instance Eq Profile
derive instance Generic Profile _

instance Show Profile where
  show = genericShow
