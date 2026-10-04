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
  , InClosedRun(..)
  , inClosedRunOf
  , typeOfOp
  , schemeOfOp
  , arrayTy
  , withBaseTypes
  , baseModuleNames
  , baseModule
  ) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Map as Map
import Stella.Compiler.TypedCore.Decl (Decl(..), Export(..), Module)
import Stella.Compiler.TypedCore.Kind (Kind(..), monoScheme)
import Stella.Compiler.TypedCore.Name (Ident(..), ModuleName(..), Qualified(..), TyName(..), TyVar(..))
import Stella.Compiler.TypedCore.Prim (asFunction, booleanTy, charTy, intTy, numberTy, pureFn, stringTy, unitTy)
import Stella.Compiler.TypedCore.Signature (CanonicalClass(..), Signature, TyConInfo(..))
import Stella.Compiler.TypedCore.Type (Type(..), TypeScheme)
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..))
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
-- | `scheme` is what the entry is declared at, and `arity` the arrows of it: the
-- | two are read off one type, `typeOfOp`, so a declaration and a call site agree
-- | by construction.
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
  , scheme :: TypeScheme
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

-- | What an operation is to a closed run, one whose result is to depend on its
-- | input alone: carried out as it is, carried out on state the run itself made,
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

-- | The type an operation's entry is declared at. Total, and the one place the
-- | type is written. `Base.Array`'s entries quantify their element type in the
-- | type itself, a kind scheme binding kind variables only.
typeOfOp :: PrimOp -> Type
typeOfOp = case _ of
  IntAdd -> fn2 int int int
  IntSub -> fn2 int int int
  IntMul -> fn2 int int int
  IntQuot -> fn2 int int int
  IntRem -> fn2 int int int
  IntEq -> fn2 int int boolean
  IntLt -> fn2 int int boolean
  IntToNumber -> pureFn int number
  IntToString -> pureFn int string
  NumberAdd -> fn2 number number number
  NumberSub -> fn2 number number number
  NumberMul -> fn2 number number number
  NumberDivide -> fn2 number number number
  NumberNegate -> pureFn number number
  NumberEq -> fn2 number number boolean
  NumberLt -> fn2 number number boolean
  NumberFloor -> pureFn number number
  NumberCeil -> pureFn number number
  NumberTrunc -> pureFn number number
  NumberToInt -> pureFn number int
  NumberToString -> pureFn number string
  StringLength -> pureFn string int
  StringCodePointAt -> fn2 int string char
  StringAppend -> fn2 string string string
  StringSlice -> pureFn int (fn2 int string string)
  StringSingleton -> pureFn char string
  StringEq -> fn2 string string boolean
  StringLt -> fn2 string string boolean
  CharToCodePoint -> pureFn char int
  CharFromCodePoint -> pureFn int char
  ArrayLength -> forallA (pureFn (arrayOf a) int)
  ArrayUnsafeNew -> forallA (pureFn int (arrayOf a))
  ArrayUnsafeSet -> forallA (pureFn int (fn2 a (arrayOf a) unit))
  ArrayUnsafeIndex -> forallA (fn2 (arrayOf a) int a)
  where
  con name = TCon name []
  int = con intTy
  number = con numberTy
  string = con stringTy
  char = con charTy
  boolean = con booleanTy
  unit = con unitTy
  fn2 x y r = pureFn x (pureFn y r)
  a = TVar (TyVar "a")
  forallA = TForall (TyVar "a") KType
  arrayOf = TApp (con arrayTy)

-- | The scheme an operation's entry is declared at.
schemeOfOp :: PrimOp -> TypeScheme
schemeOfOp = monoScheme <<< typeOfOp

-- | How many arguments saturate an operation: the arrows of its type, beneath
-- | its quantifiers.
arityOfOp :: PrimOp -> P.Int
arityOfOp = arrows <<< typeOfOp
  where
  arrows = case _ of
    TForall _ _ body -> arrows body
    ty -> case asFunction ty of
      Just f -> 1 + arrows f.result
      Nothing -> 0

-- | `Base.Array.Array`, the type constructor the ABI supplies to `Base.Array`.
arrayTy :: Qualified TyName
arrayTy = Qualified (ModuleName "Base.Array") (TyName "Array")

-- | A signature with the types the ABI supplies and no declaration produces:
-- | `Base.Array.Array`, an intrinsic of the opaque class
-- | ([Prim and Base](../../../../docs/technical-references/06-Modules/02-Prim-and-Base.md)).
withBaseTypes :: Signature -> Signature
withBaseTypes sig = sig
  { types = Map.insert arrayTy (IntrinsicTyCon (monoScheme (KFun KType KType)) CanonicalOpaque) sig.types }

-- | The `Base` modules whose entries are operations, in the order of the table.
baseModuleNames :: P.Array ModuleName
baseModuleNames = Array.nub (map (\e -> moduleOf e.entry) primTable)
  where
  moduleOf (Qualified m _) = m

-- | The `Base` module of that name as Core: a `foreign` declaration of each
-- | operation's entry, at its scheme, in the order of the table, all exported,
-- | every annotation the one given. Such a module is compiled and loaded as any
-- | other, and a consumer carries out each entry as the operation it is.
baseModule :: forall a. a -> ModuleName -> Module a
baseModule annotation name =
  { annotation
  , name
  , imports: []
  , exports: map (ExportValue <<< _.name) entries
  , decls: map (\e -> DeclForeign annotation { name: e.name, scheme: e.scheme, attributes: [] }) entries
  }
  where
  entries = Array.mapMaybe ownEntry primTable
  ownEntry e = case e.entry of
    Qualified m x | m == name -> Just { name: x, scheme: e.scheme }
    _ -> Nothing

primTable :: P.Array PrimEntry
primTable = map (\op -> { op, entry: entryOfOp op, arity: arityOfOp op, scheme: schemeOfOp op })
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

derive instance Eq InClosedRun
derive instance Generic InClosedRun _
instance Show InClosedRun where
  show = genericShow

derive instance Eq PrimOp
derive instance Ord PrimOp
derive instance Generic PrimOp _

instance Show PrimOp where
  show = genericShow
