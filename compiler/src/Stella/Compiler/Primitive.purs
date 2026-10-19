-- | The compiler-facing side of the ABI catalog: what each `Base` entry the
-- | runtime carries out is declared at, the type constructors the ABI supplies,
-- | and the `Base` names as the compiler writes them.
-- |
-- | A `Base` ABI entry whose meaning the ABI fixes is an **operation**, not an
-- | implementation: every consumer carries it out directly rather than calling
-- | something a backend supplied separately. Naming the operation is what lets a
-- | machine add two integers in its dispatch loop and a JavaScript backend emit
-- | `a + b`, neither of them recognizing a qualified name to find out.
-- |
-- | **The catalog has two sides.** What a runtime reads of an entry — its name,
-- | arity, runtime class, and profile — is the runtime-facing side
-- | ([Runtime](Abi/Runtime.purs)), written there once and holding nothing of the
-- | compiler's representation. What the compiler reads besides is here, keyed by
-- | the entry's identity: the scheme it is declared at, which a surface
-- | declaration of the entry must be at, and the arity of that scheme must be
-- | the one the runtime-facing side gives. The two stand in for the ABI
-- | manifest, which a compiler and its backends implement together
-- | ([Prim and Base](../../../../docs/technical-references/06-Modules/02-Prim-and-Base.md)).
-- | It is keyed to one ABI version, and it grows as the content of that version
-- | is settled.
module Stella.Compiler.Primitive
  ( module Runtime
  , PrimEntry
  , primTable
  , lookupPrim
  , entryOfOp
  , qualifiedOf
  , runtimeEntryNamed
  , schemeOfRuntimeEntry
  , typeOfOp
  , schemeOfOp
  , AbiType
  , abiTypeDescriptors
  , abiTypes
  , arrayTy
  , withBaseTypes
  , baseModuleNames
  , baseModule
  ) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Stella.Compiler.Abi.Runtime (EntryName, InClosedRun(..), PrimOp(..), Profile(..), RuntimeClass(..), RuntimeEntry, RuntimeEntryId(..), arityOfOp, codeOfOp, includes, inClosedRunOf, lookupRuntimeEntry, nameOfOp, opOfCode, operations, runtimeEntries, runtimeEntryOf) as Runtime
import Stella.Compiler.Abi.Runtime (EntryName, PrimOp(..), Profile(..), RuntimeEntry, RuntimeEntryId(..), arityOfOp, includes, lookupRuntimeEntry, nameOfOp, operations)
import Stella.Compiler.Interface.Module (TypeEntry, TypeSort(..))
import Stella.Compiler.TypedCore.Decl (Decl(..), Export(..), Module)
import Stella.Compiler.TypedCore.Kind (Kind(..), KindScheme, monoScheme)
import Stella.Compiler.TypedCore.Name (Ident(..), ModuleName(..), Qualified(..), TyName(..), TyVar(..))
import Stella.Compiler.TypedCore.Prim (booleanTy, charTy, intTy, ioTy, numberTy, pureFn, stringTy, unitTy)
import Stella.Compiler.TypedCore.Signature (CanonicalClass(..), Signature, TyConInfo(..))
import Stella.Compiler.TypedCore.Type (Type(..), TypeScheme)

-- | What an operation realizes, and what a consumer owes it.
-- |
-- | `entry` is the `Base` name, which is what target validation reads: an
-- | operation is how the entry is carried out and not a way of not using it, so
-- | a backend still owes the entry at the profile that holds it.
-- |
-- | **The mapping between an operation and its entry has one definition**, in
-- | the runtime-facing catalog. Carrying the two independently anywhere would
-- | let a reader check one entry while a machine ran another operation.
-- |
-- | `scheme` is what the entry is declared at, and `arity` the one the catalog
-- | gives, which is the arrows of the scheme.
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

-- | The `Base` entry an operation realizes, as the compiler names it.
entryOfOp :: PrimOp -> Qualified Ident
entryOfOp = qualifiedOf <<< nameOfOp

-- | A name of the catalog as the compiler writes it.
qualifiedOf :: EntryName -> Qualified Ident
qualifiedOf name = Qualified (ModuleName name.module) (Ident name.value)

-- | The entry the runtime carries out that a foreign of this name is, where
-- | the catalog holds one.
runtimeEntryNamed :: Qualified Ident -> Maybe RuntimeEntry
runtimeEntryNamed (Qualified (ModuleName m) (Ident x)) = lookupRuntimeEntry { module: m, value: x }

-- | The scheme an entry is declared at. Total, and the one place it is
-- | written: an operation's from its type, and each `Base.IO` entry's here.
schemeOfRuntimeEntry :: RuntimeEntryId -> TypeScheme
schemeOfRuntimeEntry = case _ of
  Operation op -> schemeOfOp op
  IOPure -> monoScheme (TForall a KType (pureFn (TVar a) (io (TVar a))))
  IOBind -> monoScheme (TForall a KType (TForall b KType (pureFn (io (TVar a)) (pureFn (pureFn (TVar a) (io (TVar b))) (io (TVar b))))))
  where
  a = TyVar "a"
  b = TyVar "b"
  io = TApp (TCon ioTy [])

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

-- | A type constructor the ABI supplies to a `Base` module, which no
-- | declaration produces: its kind, the class of its values, and the profile
-- | holding it. The one description both the interface's entry and the Core
-- | signature's are made from.
type AbiType =
  { name :: Qualified TyName
  , kind :: KindScheme
  , canonical :: CanonicalClass
  , profile :: Profile
  }

-- | Every type constructor the ABI supplies.
abiTypeDescriptors :: P.Array AbiType
abiTypeDescriptors =
  [ { name: arrayTy, kind: monoScheme (KFun KType KType), canonical: CanonicalOpaque, profile: Standard } ]

-- | The type constructors the ABI supplies to each module, as a build
-- | environment holds them, of those a backend claiming the profile given owes.
-- | Which profile a build is for is the host's to say.
abiTypes :: Profile -> Map ModuleName (Map TyName TypeEntry)
abiTypes profile = Map.fromFoldableWith Map.union (map entry (Array.filter (includes profile <<< _.profile) abiTypeDescriptors))
  where
  entry t = case t.name of
    Qualified m n -> Tuple m (Map.singleton n { kind: t.kind, sort: Intrinsic t.canonical, attributes: [] })

-- | `Base.Array.Array`, the type constructor the ABI supplies to `Base.Array`.
arrayTy :: Qualified TyName
arrayTy = Qualified (ModuleName "Base.Array") (TyName "Array")

-- | A signature with every type the ABI supplies and no declaration produces
-- | ([Prim and Base](../../../../docs/technical-references/06-Modules/02-Prim-and-Base.md)).
withBaseTypes :: Signature -> Signature
withBaseTypes sig = sig { types = Array.foldl (\ts t -> Map.insert t.name (IntrinsicTyCon t.kind t.canonical) ts) sig.types abiTypeDescriptors }

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

-- | The operations, each with its entry, arity, and scheme, in the order of the
-- | catalog. The `Base.IO` entries are none of them.
primTable :: P.Array PrimEntry
primTable = map (\op -> { op, entry: entryOfOp op, arity: arityOfOp op, scheme: schemeOfOp op }) operations

-- | The operation a `Base` entry is, where it is one.
lookupPrim :: Qualified Ident -> Maybe PrimEntry
lookupPrim name = Array.find (\e -> e.entry == name) primTable
