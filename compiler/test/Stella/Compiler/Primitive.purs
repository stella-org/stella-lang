-- | The primitive operations of the `Base` surface, through translation and
-- | lowering.
-- |
-- | An operation is a `Base` ABI entry a consumer carries out directly. What is
-- | asserted here is that the entry is recognized as one **wherever it is
-- | named** — saturated, partially applied, or referred to bare — and that a
-- | declaration disagreeing with the manifest is rejected rather than quietly
-- | read as an ordinary foreign.
module Test.Stella.Compiler.Primitive (spec) where

import Prelude

import Prim as P

import Stella.Compiler.Primitive (InClosedRun(..), PrimOp(..), Profile(..), RuntimeClass(..), RuntimeEntryId(..), abiTypes, arityOfOp, arrayTy, inClosedRunOf, baseModule, baseModuleNames, codeOfOp, entryOfOp, lookupRuntimeEntry, opOfCode, operations, primTable, qualifiedOf, runtimeEntries, runtimeEntryNamed, schemeOfOp, schemeOfRuntimeEntry, withBaseTypes)
import Stella.Compiler.TypedCore.Equality (schemeEquiv)
import Stella.Compiler.TypedCore.Kind (Kind(..))
import Stella.Compiler.TypedCore.Name (KindVar(..), TyName(..), TyVar(..))
import Stella.Compiler.TypedCore.Prim (foreignArity)
import Stella.Compiler.TypedCore.Signature (CanonicalClass(..), TyConInfo(..))
import Stella.Compiler.TypedCore.Type (substituteType)
import Data.Map as Map
import Data.Set as Set
import Data.Tuple (Tuple(..))
import Stella.Compiler.Bytecode (CalleeEntry(..), Dmo, LowerError, lower)
import Stella.Compiler.Interface (noImports)
import Stella.Compiler.MiddleEnd (TranslateError(..), translate)
import Stella.Compiler.MiddleEnd as M
import Stella.Compiler.TypedCore (Decl(..), Export(..), Expr(..), Ident(..), Literal(..), Module, ModuleName(..), Qualified(..), TypeScheme, declare, declareAnnotated, intTy, monoScheme, primSignature, pureFn, Type(..))
import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

int :: Type
int = TCon intTy []

intModuleName :: ModuleName
intModuleName = ModuleName "Base.Int"

mainModuleName :: ModuleName
mainModuleName = ModuleName "Main"

intAdd :: Qualified Ident
intAdd = Qualified intModuleName (Ident "add")

value :: P.String -> Qualified Ident
value name = Qualified mainModuleName (Ident name)

-- | `Base.Int`, declaring `add` at whatever arity the case calls for. The
-- | manifest fixes 2, so anything else is a disagreement the compiler must
-- | report.
intModuleOf :: TypeScheme -> Module P.Int
intModuleOf scheme =
  { annotation: 0
  , name: intModuleName
  , imports: []
  , exports: [ ExportValue (Ident "add"), ExportValue (Ident "zero") ]
  , decls:
      [ DeclForeign 1 { name: Ident "add", scheme, attributes: [] }
      -- an entry the manifest does not hold, which no arity makes an operation
      , DeclForeign 2 { name: Ident "zero", scheme: monoScheme int, attributes: [] }
      ]
  }

mainOf :: P.Array (Decl P.Int) -> Module P.Int
mainOf decls =
  { annotation: 0
  , name: mainModuleName
  , imports: [ intModuleName ]
  , exports: []
  , decls
  }

type Mid = { module :: M.Module, debug :: M.Debug P.Int }

-- | Declare both modules and translate `Main`. The outer `Either` is the
-- | fixture's own health and the inner one the translation's answer, which is
-- | what several of these cases assert.
midOf :: TypeScheme -> P.Array (Decl P.Int) -> Either P.String (Either TranslateError Mid)
midOf scheme decls = case declare primSignature (intModuleOf scheme) of
  Left _ -> Left "Base.Int did not declare"
  Right signature -> case declareAnnotated signature (mainOf decls) of
    Left _ -> Left "Main did not declare"
    Right declared -> Right (translate noImports (mainOf decls) declared)

dmoOf :: TypeScheme -> P.Array (Decl P.Int) -> Either P.String Dmo
dmoOf scheme decls = case midOf scheme decls of
  Left err -> Left err
  Right (Left err) -> Left (show err)
  Right (Right mid) -> case lower mid of
    Left err -> Left (show (err :: LowerError))
    Right out -> Right out.dmo

bodyOf :: TypeScheme -> P.Array (Decl P.Int) -> P.Int -> Either P.String M.Expr
bodyOf scheme decls i = case midOf scheme decls of
  Left err -> Left err
  Right (Left err) -> Left (show err)
  Right (Right mid) -> case Array.find (\f -> f.id == M.FuncId i) mid.module.functions of
    Just f -> Right f.body
    Nothing -> Left ("no function #" <> show i)

-- The declarations -------------------------------------------------------------

binary :: TypeScheme
binary = monoScheme (pureFn int (pureFn int int))

ternary :: TypeScheme
ternary = monoScheme (pureFn int (pureFn int (pureFn int int)))

nullary :: TypeScheme
nullary = monoScheme int

-- | `nonrec Main.addTwo : Int -{()}-> Int = Base.Int.add 2`, one argument short.
addTwoDecl :: Decl P.Int
addTwoDecl = DeclNonRec 1
  { name: Ident "addTwo"
  , scheme: monoScheme (pureFn int int)
  , value: App 0 (Global 0 intAdd []) (Lit 0 (LitInt 2))
  , attributes: []
  }

-- | `nonrec Main.three : Int = Main.addTwo 1`, which saturates that.
threeDecl :: Decl P.Int
threeDecl = DeclNonRec 2
  { name: Ident "three"
  , scheme: nullary
  , value: App 0 (Global 0 (value "addTwo") []) (Lit 0 (LitInt 1))
  , attributes: []
  }

-- | `nonrec Main.plain : Int = Base.Int.zero`, an entry of no arity that the
-- | manifest does not hold.
plainDecl :: Decl P.Int
plainDecl = DeclNonRec 1
  { name: Ident "plain"
  , scheme: nullary
  , value: Global 0 (Qualified intModuleName (Ident "zero")) []
  , attributes: []
  }

-- | `nonrec Main.bare : … = Base.Int.add`, referring to the entry and applying
-- | nothing. The type follows whatever arity the declaration was given.
bareDecl :: TypeScheme -> Decl P.Int
bareDecl scheme = DeclNonRec 1
  { name: Ident "bare"
  , scheme
  , value: Global 0 intAdd []
  , attributes: []
  }

-- | The manifest of `stella-base-0.1`, written out.
-- |
-- | **A second copy is the point of it.** `codeOfOp`, `arityOfOp`, and
-- | `entryOfOp` are one definition each, and an encode followed by a decode reads
-- | that same definition from both sides, so a wrong code round-trips perfectly. A
-- | published table is fixed for the life of a version
-- | ([Encoding](../../../../docs/technical-references/05-Backend/02-Encoding.md)),
-- | which is what makes writing it twice worth the duplication rather than a smell.
manifestOf01 :: P.Array { code :: P.Int, entry :: Qualified Ident, arity :: P.Int }
manifestOf01 =
  [ { code: 0x01, entry: base "Base.Int" "add", arity: 2 }
  , { code: 0x02, entry: base "Base.Int" "sub", arity: 2 }
  , { code: 0x03, entry: base "Base.Int" "mul", arity: 2 }
  , { code: 0x04, entry: base "Base.Int" "quot", arity: 2 }
  , { code: 0x05, entry: base "Base.Int" "rem", arity: 2 }
  , { code: 0x06, entry: base "Base.Int" "eq", arity: 2 }
  , { code: 0x07, entry: base "Base.Int" "lt", arity: 2 }
  , { code: 0x08, entry: base "Base.Int" "toNumber", arity: 1 }
  , { code: 0x09, entry: base "Base.Int" "toString", arity: 1 }
  , { code: 0x30, entry: base "Base.Number" "add", arity: 2 }
  , { code: 0x31, entry: base "Base.Number" "sub", arity: 2 }
  , { code: 0x32, entry: base "Base.Number" "mul", arity: 2 }
  , { code: 0x33, entry: base "Base.Number" "divide", arity: 2 }
  , { code: 0x34, entry: base "Base.Number" "negate", arity: 1 }
  , { code: 0x35, entry: base "Base.Number" "eq", arity: 2 }
  , { code: 0x36, entry: base "Base.Number" "lt", arity: 2 }
  , { code: 0x37, entry: base "Base.Number" "floor", arity: 1 }
  , { code: 0x38, entry: base "Base.Number" "ceil", arity: 1 }
  , { code: 0x39, entry: base "Base.Number" "trunc", arity: 1 }
  , { code: 0x3A, entry: base "Base.Number" "toInt", arity: 1 }
  , { code: 0x3B, entry: base "Base.Number" "toString", arity: 1 }
  , { code: 0x10, entry: base "Base.String" "length", arity: 1 }
  , { code: 0x11, entry: base "Base.String" "codePointAt", arity: 2 }
  , { code: 0x12, entry: base "Base.String" "append", arity: 2 }
  , { code: 0x13, entry: base "Base.String" "slice", arity: 3 }
  , { code: 0x14, entry: base "Base.String" "singleton", arity: 1 }
  , { code: 0x15, entry: base "Base.String" "eq", arity: 2 }
  , { code: 0x16, entry: base "Base.String" "lt", arity: 2 }
  , { code: 0x40, entry: base "Base.Char" "toCodePoint", arity: 1 }
  , { code: 0x41, entry: base "Base.Char" "fromCodePoint", arity: 1 }
  , { code: 0x20, entry: base "Base.Array" "unsafeIndex", arity: 2 }
  , { code: 0x21, entry: base "Base.Array" "unsafeNew", arity: 1 }
  , { code: 0x22, entry: base "Base.Array" "unsafeSet", arity: 3 }
  , { code: 0x23, entry: base "Base.Array" "length", arity: 1 }
  ]
  where
  base m n = Qualified (ModuleName m) (Ident n)

spec :: Spec Unit
spec = describe "Stella.Compiler.Abi » operations of the Base surface" do

  describe "the manifest of stella-base-0.1" do

    it "holds these operations and no others" do
      Array.length primTable `shouldEqual` Array.length manifestOf01
      map _.entry primTable `shouldEqual` map _.entry manifestOf01

    it "gives each the code, the entry, and the arity the version fixes" do
      let
        written = map
          (\op -> { code: codeOfOp op, entry: entryOfOp op, arity: arityOfOp op })
          (map _.op primTable)
      written `shouldEqual` manifestOf01

    -- a code is written rather than derived, and a version that reused one would
    -- leave a published file with two readings
    it "gives no two operations one code" do
      let codes = map (\op -> codeOfOp op) (map _.op primTable)
      Array.length (Array.nub codes) `shouldEqual` Array.length codes

    it "reads each code back as the operation it names" do
      let ops = map _.op primTable
      map (\op -> opOfCode (codeOfOp op)) ops `shouldEqual` map Just ops
      opOfCode 0x7F `shouldEqual` Nothing

    -- a `Base` module is compiled from the table, so what it declares is what the
    -- table holds, one entry at a time
    -- what a closed run admits is the table's to say, so an operation added is
    -- classified where it is added
    it "gives the operations on arrays to a closed run as state of its own, and admits the rest" do
      map _.op (Array.filter (\e -> inClosedRunOf e.op /= Admitted) primTable)
        `shouldEqual` [ ArrayUnsafeIndex, ArrayUnsafeNew, ArrayUnsafeSet, ArrayLength ]
      Array.all (\e -> inClosedRunOf e.op == RunLocalState || inClosedRunOf e.op == Admitted) primTable `shouldEqual` true

    it "gives each Base module its operations as foreign declarations, at their schemes" do
      baseModuleNames `shouldEqual` map ModuleName [ "Base.Int", "Base.Number", "Base.String", "Base.Char", "Base.Array" ]
      Array.concatMap (foreignsOf <<< baseModule 0) baseModuleNames
        `shouldEqual` map (\e -> { name: e.entry, scheme: schemeOfOp e.op }) primTable
      Array.foldM
        ( \_ name -> case declareAnnotated (withBaseTypes primSignature) (baseModule 0 name) of
            Left err -> fail (show name <> " does not declare: " <> show err.error)
            Right _ -> pure unit
        )
        unit
        baseModuleNames

  describe "an operation short of its arguments" do

    it "waits as an operation rather than as the name of an implementation" do
      -- were the callee the qualified name, saturating this would call whatever
      -- a backend supplied under it instead of running the operation
      bodyOf binary [ addTwoDecl, threeDecl ] 0 `shouldEqual` Right
        (M.ETail (M.CPap (M.CalleePrim IntAdd) [ M.ALit (LitInt 2) ]))

    it "is saturated through the value it was bound to, which calls unknown" do
      -- `addTwo`'s right-hand side is not a lambda, so it has no definitional
      -- arity and nothing may assume one
      bodyOf binary [ addTwoDecl, threeDecl ] 1 `shouldEqual` Right
        (M.ETail (M.CCallUnknown (M.AGlobal (value "addTwo")) [ M.ALit (LitInt 1) ]))

    it "reaches the callee table as an operation, and the operation table too" do
      -- a machine reads the callee to know what saturating the partial
      -- application runs; target validation reads `prims` to know what the
      -- module owes. Both must name the operation
      let
        tables = do
          dmo <- dmoOf binary [ addTwoDecl, threeDecl ]
          Right { callees: dmo.callees, prims: dmo.prims }
      tables `shouldEqual` Right
        { callees: [ CalleePrim IntAdd ]
        , prims: [ IntAdd ]
        }

    it "derives the entry it realizes from the operation and nowhere else" do
      map entryOfOp [ IntAdd ] `shouldEqual` [ intAdd ]

  describe "an entry of no arity" do

    it "runs where it is named, and is classified on the same path" do
      -- a foreign of no arity saturates as soon as its spine is formed, so
      -- referring to it runs it. The reference consults the manifest exactly as
      -- a call does, and `Base.Int.zero` is in neither
      bodyOf binary [ plainDecl ] 0 `shouldEqual` Right
        (M.ETail (M.CForeign (Qualified intModuleName (Ident "zero")) []))

  describe "a declaration disagreeing with the manifest" do

    it "is reported where the entry is called" do
      midOf ternary [ bareDecl ternary ] `shouldEqual`
        Right (Left (AbiArityMismatch intAdd 2 3))

    it "is reported where it is referred to bare at no arity" do
      -- nothing here may fall through to an ordinary foreign: an operation of
      -- the wrong arity would run with the wrong number of operands
      midOf nullary [ bareDecl nullary ] `shouldEqual`
        Right (Left (AbiArityMismatch intAdd 2 0))

  describe "the ABI catalog" do

    it "names each entry once, every operation and both `Base.IO` entries among them" do
      let names = map (\e -> e.name.module <> "." <> e.name.value) runtimeEntries
      Array.length (Array.nub names) `shouldEqual` Array.length names
      map _.id runtimeEntries `shouldEqual` (map Operation operations <> [ IOPure, IOBind ])
      Array.length (Array.nub operations) `shouldEqual` 34
      map (opOfCode <<< codeOfOp) operations `shouldEqual` map Just operations

    it "gives each entry the arity of the scheme it is declared at" do
      Array.filter (\e -> e.arity /= foreignArity (schemeOfRuntimeEntry e.id)) runtimeEntries `shouldEqual` []

    it "finds each entry by its name, and the compiler's name of it" do
      Array.filter (\e -> map _.id (lookupRuntimeEntry e.name) /= Just e.id || map _.id (runtimeEntryNamed (qualifiedOf e.name)) /= Just e.id) runtimeEntries `shouldEqual` []
      map _.id (runtimeEntryNamed (Qualified (ModuleName "Base.Int") (Ident "zero"))) `shouldEqual` Nothing

    it "classes the `Base.IO` entries as the runtime's IO, at `core-runtime`, and leaves them out of the operations" do
      map (\e -> { id: e.id, runtimeClass: e.runtimeClass, profile: e.profile }) (Array.filter (\e -> e.name.module == "Base.IO") runtimeEntries) `shouldEqual`
        [ { id: IOPure, runtimeClass: RuntimeIO, profile: CoreRuntime }, { id: IOBind, runtimeClass: RuntimeIO, profile: CoreRuntime } ]
      Array.length primTable `shouldEqual` 34
      Array.elem (ModuleName "Base.IO") baseModuleNames `shouldEqual` false

    it "compares schemes up to the names of their kind and type variables, and no further" do
      let
        k = KindVar "k"
        j = KindVar "j"
        poly v kv = { kindVars: [ kv ], body: TForall (TyVar v) (KVar kv) (pureFn (TVar (TyVar v)) (TVar (TyVar v))) }
        bound = schemeOfRuntimeEntry IOBind
        renamed = case bound.body of
          TForall _ ka (TForall _ kb body) -> bound { body = TForall (TyVar "x") ka (TForall (TyVar "y") kb (swap body)) }
          other -> bound { body = other }
        swap = substituteType (Map.fromFoldable [ Tuple (TyVar "a") (TVar (TyVar "x")), Tuple (TyVar "b") (TVar (TyVar "y")) ])
      schemeEquiv bound renamed `shouldEqual` Right true
      schemeEquiv (poly "a" k) (poly "b" j) `shouldEqual` Right true
      schemeEquiv (poly "a" k) { kindVars: [], body: TForall (TyVar "a") KType (pureFn (TVar (TyVar "a")) (TVar (TyVar "a"))) } `shouldEqual` Right false
      schemeEquiv (poly "a" k) { kindVars: [ k, j ], body: (poly "a" k).body } `shouldEqual` Right false
      schemeEquiv bound (schemeOfRuntimeEntry IOPure) `shouldEqual` Right false

    it "supplies `Base.Array.Array` at `standard` and none at `core-runtime`, as Core and as the interface read it" do
      map (map Map.keys) (Map.toUnfoldable (abiTypes Standard) :: P.Array _) `shouldEqual` [ Tuple (ModuleName "Base.Array") (Set.singleton (TyName "Array")) ]
      Map.isEmpty (abiTypes CoreRuntime) `shouldEqual` true
      Map.lookup arrayTy (withBaseTypes primSignature).types `shouldEqual` Just (IntrinsicTyCon (monoScheme (KFun KType KType)) CanonicalOpaque)

-- | What a module declares, as foreigns of its name.
foreignsOf :: Module P.Int -> P.Array { name :: Qualified Ident, scheme :: TypeScheme }
foreignsOf m = Array.mapMaybe
  ( case _ of
      DeclForeign _ f -> Just { name: Qualified m.name f.name, scheme: f.scheme }
      _ -> Nothing
  )
  m.decls
