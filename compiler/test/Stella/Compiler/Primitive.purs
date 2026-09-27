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

import Stella.Compiler.Primitive (PrimOp(..), arityOfOp, codeOfOp, entryOfOp, opOfCode, primTable)
import Stella.Compiler.Bytecode (CalleeEntry(..), Dmo, LowerError, lower)
import Stella.Compiler.Interface (noImports)
import Stella.Compiler.MiddleEnd (TranslateError(..), translate)
import Stella.Compiler.MiddleEnd as M
import Stella.Compiler.TypedCore (Decl(..), Export(..), Expr(..), Ident(..), Literal(..), Module, ModuleName(..), Qualified(..), TypeScheme, declare, declareAnnotated, intTy, monoScheme, primSignature, pureFn, Type(..))
import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

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
  , { code: 0x10, entry: base "Base.String" "length", arity: 1 }
  , { code: 0x11, entry: base "Base.String" "codePointAt", arity: 2 }
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
