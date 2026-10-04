-- | Attributes in Core: a declaration's parameters, and the arguments of one
-- | attached to a declaration, each checked against the closed type its
-- | parameter declares.
module Test.Stella.Compiler.TypedCore.AttributeCheck (spec) where

import Prelude

import Prim as P

import Data.Either (Either(..), isLeft, isRight)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Stella.Compiler.TypedCore (Attribute, Constant(..), Constraint(..), Decl(..), DeclError(..), Expr(..), Ident(..), Kind(..), Literal(..), Module, ModuleName(..), Qualified(..), RowElemKind(..), RowEntry(..), RowKey(..), Signature, Symbol(..), TyName(..), TyVar(..), Type(..), declare, initialSignature, monoScheme, primSignature, pureFn, scalarString)
import Stella.Compiler.TypedCore.AttributeCheck (AttributeError(..), checkAttribute, checkAttributeDecl, checkConstant)
import Stella.Compiler.TypedCore.Prim (intTy, recordTy, stringTy)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, shouldSatisfy)

main :: ModuleName
main = ModuleName "Main"

inMain :: forall a. a -> Qualified a
inMain = Qualified main

int :: Type
int = TCon intTy []

string :: Type
string = TCon stringTy []

maybeOf :: Type -> Type
maybeOf = TApp (TCon (inMain (TyName "Maybe")) [])

-- | `{ name : String, level : Int }`.
nameLevel :: Type
nameLevel = TApp (TCon recordTy [])
  (TRowExtend (RowTypeEntry (SymbolKey (Symbol "name")) string) (TRowExtend (RowTypeEntry (SymbolKey (Symbol "level")) int) TRowEmpty))

-- | `data Maybe a = Nothing | Just a`, `one : Int`, `id : forall a. a -> a`,
-- | and `lacking : forall (r : Row Type). (x ∉ r) => Int`.
fixture :: Module P.Int
fixture =
  { annotation: 0
  , name: main
  , imports: []
  , exports: []
  , decls:
      [ DeclData 1
          { name: TyName "Maybe"
          , kindVars: []
          , params: [ { name: a, kind: KType } ]
          , constructors: [ { name: Ident "Nothing", tag: 0, fields: [] }, { name: Ident "Just", tag: 1, fields: [ TVar a ] } ]
          , isNewtype: false
          , attributes: []
          }
      , DeclNonRec 2 { name: Ident "one", scheme: monoScheme int, value: Lit 2 (LitInt 1), attributes: [] }
      , DeclNonRec 3
          { name: Ident "id"
          , scheme: monoScheme (TForall a KType (pureFn (TVar a) (TVar a)))
          , value: TyLam 3 a KType (Lam 3 (Ident "x") (TVar a) (Var 3 (Ident "x")))
          , attributes: []
          }
      , DeclNonRec 4
          { name: Ident "lacking"
          , scheme: monoScheme (TForall r (KRow RowType) (TConstrained (Lacks (SymbolKey (Symbol "x")) (TVar r)) int))
          , value: TyLam 4 r (KRow RowType) (ConstraintLam 4 (Lacks (SymbolKey (Symbol "x")) (TVar r)) (Lit 4 (LitInt 0)))
          , attributes: []
          }
      ]
  }
  where
  a = TyVar "a"
  r = TyVar "r"

signature :: Signature
signature = case declare primSignature fixture of
  Right sig -> sig
  Left _ -> primSignature

-- | `json` takes a `String` and keyword `(level :: Int = 3)`.
withJson :: Signature
withJson = signature
  { attributes = Map.insert (inMain (Ident "json"))
      { positional: [ string ], keyword: [ { label: "level", type: int, default: Just (ConstantLiteral (LitInt 3)) } ] }
      signature.attributes
  }

json :: P.Array Constant -> P.Array { label :: P.String, value :: Constant } -> Attribute
json positional keyword = { name: inMain (Ident "json"), positional, keyword }

text :: P.String -> Constant
text s = case scalarString s of
  Just v -> ConstantLiteral (LitString v)
  Nothing -> ConstantLiteral (LitInt 0)

spec :: Spec Unit
spec = describe "Stella.Compiler.TypedCore.AttributeCheck" do
  describe "a declaration" do
    it "takes closed parameter types of kind Type, and defaults of their types" do
      checkAttributeDecl signature { positional: [ int, maybeOf int ], keyword: [] } `shouldEqual` Right unit
      isLeft (checkAttributeDecl signature { positional: [ TVar (TyVar "a") ], keyword: [] }) `shouldEqual` true
      isLeft (checkAttributeDecl signature { positional: [ TRowEmpty ], keyword: [] }) `shouldEqual` true
      checkAttributeDecl signature { positional: [], keyword: [ { label: "level", type: int, default: Just (ConstantLiteral (LitBoolean true)) } ] }
        `shouldEqual` Left (ConstantNotOfType (ConstantLiteral (LitBoolean true)) int)

  describe "an attached attribute" do
    it "is declared, and normalized: as many positional arguments as parameters, every keyword in the order declared" do
      checkAttribute withJson (json [ text "u" ] [ { label: "level", value: ConstantLiteral (LitInt 1) } ]) `shouldEqual` Right unit
      checkAttribute withJson { name: inMain (Ident "nope"), positional: [], keyword: [] } `shouldEqual` Left (UndeclaredAttribute (inMain (Ident "nope")))
      checkAttribute withJson (json [] [ { label: "level", value: ConstantLiteral (LitInt 1) } ]) `shouldEqual` Left (PositionalCount (inMain (Ident "json")) 1 0)
      checkAttribute withJson (json [ text "u" ] []) `shouldEqual` Left (KeywordsNotNormalized (inMain (Ident "json")) [ "level" ] [])

  describe "a constant" do
    it "of a literal has the Prim type of its kind" do
      checkConstant signature int (ConstantLiteral (LitInt 1)) `shouldEqual` Right unit
      checkConstant signature string (ConstantLiteral (LitInt 1)) `shouldEqual` Left (ConstantNotOfType (ConstantLiteral (LitInt 1)) string)

    it "of a value has the type its outer quantifiers instantiate to, and discharges no constraint" do
      checkConstant signature int (ConstantValue (inMain (Ident "one"))) `shouldEqual` Right unit
      checkConstant signature (pureFn int int) (ConstantValue (inMain (Ident "id"))) `shouldEqual` Right unit
      isLeft (checkConstant signature (pureFn int string) (ConstantValue (inMain (Ident "id")))) `shouldEqual` true
      isLeft (checkConstant signature int (ConstantValue (inMain (Ident "lacking")))) `shouldEqual` true
      checkConstant signature int (ConstantValue (inMain (Ident "absent"))) `shouldEqual` Left (UndeclaredGlobal (inMain (Ident "absent")))

    it "of a constructor builds the type expected, each argument checked against its field" do
      let just c = ConstantConstructor (inMain (Ident "Just")) [ c ]
      checkConstant signature (maybeOf int) (ConstantConstructor (inMain (Ident "Nothing")) []) `shouldEqual` Right unit
      checkConstant signature (pureFn int (maybeOf int)) (ConstantValue (inMain (Ident "Just")))
        `shouldEqual` Left (UndeclaredGlobal (inMain (Ident "Just")))
      checkConstant signature (maybeOf int) (just (ConstantLiteral (LitInt 1))) `shouldEqual` Right unit
      checkConstant signature (maybeOf (maybeOf int)) (just (ConstantConstructor (inMain (Ident "Nothing")) [])) `shouldEqual` Right unit
      isLeft (checkConstant signature (maybeOf string) (just (ConstantLiteral (LitInt 1)))) `shouldEqual` true
      isLeft (checkConstant signature int (just (ConstantLiteral (LitInt 1)))) `shouldEqual` true
      isLeft (checkConstant signature (maybeOf int) (ConstantConstructor (inMain (Ident "Just")) [])) `shouldEqual` true

    it "of a record has a closed record type, its labels exactly the row's" do
      let field l c = { label: Symbol l, value: c }
      checkConstant signature nameLevel (ConstantRecord [ field "level" (ConstantLiteral (LitInt 1)), field "name" (text "u") ]) `shouldEqual` Right unit
      isLeft (checkConstant signature nameLevel (ConstantRecord [ field "name" (text "u") ])) `shouldEqual` true
      isLeft (checkConstant signature nameLevel (ConstantRecord [ field "name" (text "u"), field "level" (ConstantLiteral (LitInt 1)), field "extra" (ConstantLiteral (LitInt 1)) ])) `shouldEqual` true
      isLeft (checkConstant signature int (ConstantRecord [])) `shouldEqual` true

  describe "an imported attribute entry" do
    it "is checked as a declaration would be, where the signature is assembled" do
      let
        imported info = primSignature { attributes = Map.singleton (Qualified (ModuleName "Lib") (Ident "bad")) info }
        bad = Qualified (ModuleName "Lib") (Ident "bad")
      initialSignature [ imported { positional: [ int ], keyword: [] } ] `shouldSatisfy` isRight
      initialSignature [ imported { positional: [ TVar (TyVar "a") ], keyword: [] } ] `shouldSatisfy` isLeft
      initialSignature [ imported { positional: [ TRowEmpty ], keyword: [] } ] `shouldSatisfy` isLeft
      initialSignature [ imported { positional: [], keyword: [ { label: "k", type: int, default: Just (ConstantLiteral (LitBoolean true)) } ] } ]
        `shouldEqual` Left (AttributeEntryError bad (ConstantNotOfType (ConstantLiteral (LitBoolean true)) int))
      initialSignature [ imported { positional: [], keyword: [ { label: "k", type: int, default: Just (ConstantValue (Qualified (ModuleName "Lib") (Ident "gone"))) } ] } ]
        `shouldEqual` Left (AttributeEntryError bad (UndeclaredGlobal (Qualified (ModuleName "Lib") (Ident "gone"))))

  describe "a module" do
    it "declares its attributes, and checks every attribute attached, against the whole module" do
      let
        attribute = DeclAttribute 9 { name: Ident "json", positional: [ int ], keyword: [] }
        tagged = DeclNonRec 8 { name: Ident "tagged", scheme: monoScheme int, value: Lit 8 (LitInt 0), attributes: [ { name: inMain (Ident "json"), positional: [ ConstantValue (inMain (Ident "later")) ], keyword: [] } ] }
        later = DeclNonRec 10 { name: Ident "later", scheme: monoScheme int, value: Lit 10 (LitInt 2), attributes: [] }
        wrong = DeclNonRec 11 { name: Ident "wrong", scheme: monoScheme int, value: Lit 11 (LitInt 2), attributes: [ { name: inMain (Ident "json"), positional: [ text "u" ], keyword: [] } ] }
      map (const unit) (declare primSignature fixture { decls = fixture.decls <> [ tagged, attribute, later ] }) `shouldEqual` Right unit
      map (const unit) (declare primSignature fixture { decls = fixture.decls <> [ attribute, wrong ] })
        `shouldEqual` Left { at: 11, error: AttributeIllTyped (ConstantNotOfType (text "u") int) }
      map (const unit) (declare primSignature fixture { decls = fixture.decls <> [ attribute, attribute ] })
        `shouldEqual` Left { at: 9, error: DuplicateAttribute (inMain (Ident "json")) }
