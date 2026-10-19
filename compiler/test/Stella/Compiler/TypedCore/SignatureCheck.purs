-- | `Σ ok`, the contract every judgement presupposes of the signature.
-- |
-- | Each malformed signature here is one a declaration never produces and an
-- | assembled interface could: the check is what stands between such an entry
-- | and the rules that read it.
module Test.Stella.Compiler.TypedCore.SignatureCheck (spec) where

import Prelude

import Prim as P

import Stella.Compiler.Macro.Compiled (compiled)
import Stella.Compiler.TypedCore (CanonicalClass(..), CheckError(..), CtorInfo, Decl(..), DeclError(..), Expr(..), Ident(..), Kind(..), KindError(..), KindVar(..), Module, ModuleName(..), Qualified(..), RowElemKind(..), RowEntry(..), Signature, SignatureError(..), TyConInfo(..), TyName(..), TyVar(..), Type(..), declare, emptyContext, envOf, fn, infer, initialSignature, intTy, lookupGlobal, monoScheme, primSignature, pureFn, sigOk, unitCtor, unitTy)
import Stella.Compiler.TypedCore.Name (EffName(..))
import Data.Either (Either(..), isRight)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual, shouldSatisfy)

lib :: ModuleName
lib = ModuleName "Lib"

tyCon :: P.String -> Qualified TyName
tyCon = Qualified lib <<< TyName

ctor :: P.String -> Qualified Ident
ctor = Qualified lib <<< Ident

primAttribute :: P.String -> Qualified Ident
primAttribute = Qualified (ModuleName "Prim") <<< Ident

int :: Type
int = TCon intTy []

a :: TyVar
a = TyVar "a"

-- | `T : Type -> Type`, owning the constructors given.
tOwning :: P.Array (Qualified Ident) -> TyConInfo
tOwning = DataTyCon (monoScheme (KFun KType KType))

tOf :: Type -> Type
tOf = TApp (TCon (tyCon "T") [])

-- | `C : forall (a : Type). a -> T a`, tag 0, the well-formed constructor the
-- | malformed ones below vary one part of.
wellFormedC :: CtorInfo
wellFormedC =
  { owner: tyCon "T"
  , tag: 0
  , params: [ { name: a, kind: KType } ]
  , fields: [ TVar a ]
  , scheme: monoScheme (TForall a KType (pureFn (TVar a) (tOf (TVar a))))
  }

-- | `Σ_Prim` with `T` and the constructors given, which `T` lists.
withCtors :: P.Array { name :: Qualified Ident, info :: CtorInfo } -> Signature
withCtors ctors = primSignature
  { types = Map.insert (tyCon "T") (tOwning (map _.name ctors)) primSignature.types
  , ctors = Map.union (Map.fromFoldable (map (\c -> Tuple c.name c.info) ctors)) primSignature.ctors
  }

-- | One constructor `C`.
withC :: CtorInfo -> Signature
withC info = withCtors [ { name: ctor "C", info } ]

-- | `Σ_Prim` with a value entry.
withValue :: Qualified Ident -> P.Boolean -> Type -> Signature -> Signature
withValue name isForeign body sig = sig
  { values = Map.insert name { scheme: monoScheme body, isForeign } sig.values }

-- | The signature given with `effect Ping`, of no operation.
withPing :: Signature -> Signature
withPing sig = sig { effects = Map.insert (Qualified lib (EffName "Ping")) { params: [], operations: Map.empty } sig.effects }

-- | `module Lib` declaring `data List a = Nil | Cons a (List a)`,
-- | `data Proxy forall k. (p : k) = Proxy`, and `foreign length`.
listModule :: Module Unit
listModule =
  { annotation: unit
  , name: lib
  , imports: []
  , exports: []
  , decls:
      [ DeclData unit
          { name: TyName "List"
          , kindVars: []
          , params: [ { name: a, kind: KType } ]
          , constructors:
              [ { name: Ident "Nil", tag: 0, fields: [] }
              , { name: Ident "Cons", tag: 1, fields: [ TVar a, list (TVar a) ] }
              ]
          , isNewtype: false
          , attributes: []
          }
      , DeclData unit
          { name: TyName "Proxy"
          , kindVars: [ KindVar "k" ]
          , params: [ { name: TyVar "p", kind: KVar (KindVar "k") } ]
          , constructors: [ { name: Ident "Proxy", tag: 0, fields: [] } ]
          , isNewtype: false
          , attributes: []
          }
      , DeclForeign unit
          { name: Ident "length"
          , scheme: monoScheme (TForall a KType (pureFn (list (TVar a)) int))
          , attributes: []
          }
      ]
  }
  where
  list = TApp (TCon (tyCon "List") [])

spec :: Spec Unit
spec = describe "TypedCore.SignatureCheck" do
  describe "a signature that is Σ ok" do
    it "is Σ_Prim" do
      sigOk primSignature `shouldEqual` Right unit

    it "is what a module declaring polymorphic data and a foreign contributes" do
      case declare primSignature listModule of
        Left err -> fail (show err.error)
        Right sig -> sigOk sig `shouldEqual` Right unit

    it "is what the compiler's own modules contribute, Stella.Syntax among them" do
      case compiled of
        Left err -> fail err
        Right c -> sigOk c.signature `shouldEqual` Right unit

    it "holds a well-formed constructor" do
      sigOk (withC wellFormedC) `shouldEqual` Right unit

  describe "a constructor" do
    it "is refused at a scheme landing in another instance of its owner" do
      -- `C : forall a. a -> T Int` would type a branch's field at the
      -- scrutinee's argument while the value carries an `a`
      let info = wellFormedC { scheme = monoScheme (TForall a KType (pureFn (TVar a) (tOf int))) }
      sigOk (withC info) `shouldEqual` Left (CtorSchemeShape (ctor "C"))

    it "is refused at a scheme whose arrows are not pure" do
      let
        row = TRowExtend (RowEffectEntry (Qualified lib (EffName "Ping")) []) TRowEmpty
        info = wellFormedC { scheme = monoScheme (TForall a KType (fn (TVar a) row (tOf (TVar a)))) }
      sigOk (withPing (withC info)) `shouldEqual` Left (CtorSchemeShape (ctor "C"))

    it "is refused at fields its scheme does not take" do
      sigOk (withC wellFormedC { fields = [ int ] }) `shouldEqual` Left (CtorSchemeShape (ctor "C"))
      sigOk (withC wellFormedC { fields = [] }) `shouldEqual` Left (CtorSchemeShape (ctor "C"))

    it "is refused at an ill-kinded field its scheme is equivalent to" do
      -- `() ⊎ Int` is no type, though equivalent to `Int`: the stored field is
      -- what a branch binds, so it is kinded in its own right
      let
        info = wellFormedC
          { params = []
          , fields = [ TRowUnion TRowEmpty int ]
          , scheme = monoScheme (pureFn int (TCon (tyCon "T") []))
          }
        sig = (withC info) { types = Map.insert (tyCon "T") (DataTyCon (monoScheme KType) [ ctor "C" ]) primSignature.types }
      sigOk sig `shouldEqual` Left (CtorEntryError (ctor "C") (NotARowKind int KType))
      sigOk sig { ctors = Map.insert (ctor "C") info { fields = [ int ] } sig.ctors } `shouldEqual` Right unit

    it "is admitted at a scheme differing in the names it binds alone" do
      let b = TyVar "b"
      sigOk (withC wellFormedC { scheme = monoScheme (TForall b KType (pureFn (TVar b) (tOf (TVar b)))) })
        `shouldEqual` Right unit

    it "is refused where its parameters are not its owner's" do
      sigOk (withC wellFormedC { params = [ { name: a, kind: KRow RowType } ] }) `shouldEqual` Left (CtorParams (ctor "C"))
      sigOk (withC wellFormedC { params = [] }) `shouldEqual` Left (CtorParams (ctor "C"))

    it "is refused where its kind variables are not its owner's" do
      sigOk (withC wellFormedC { scheme = { kindVars: [ KindVar "k" ], body: wellFormedC.scheme.body } })
        `shouldEqual` Left (CtorKindVars (ctor "C"))

    it "is refused where its owner is no data type" do
      let sig = (withC wellFormedC) { types = Map.insert (tyCon "T") (IntrinsicTyCon (monoScheme (KFun KType KType)) CanonicalOpaque) primSignature.types }
      sigOk sig `shouldEqual` Left (CtorOwnerNotData (ctor "C") (tyCon "T"))
      sigOk (withC wellFormedC { owner = tyCon "Gone" }) { types = primSignature.types } `shouldEqual` Left (CtorOwnerNotData (ctor "C") (tyCon "Gone"))

    it "is refused where its owner's list and the constructors naming it disagree" do
      let base = withC wellFormedC
      sigOk base { types = Map.insert (tyCon "T") (tOwning []) base.types } `shouldEqual` Left (CtorListing (tyCon "T") (ctor "C"))
      sigOk base { types = Map.insert (tyCon "T") (tOwning [ ctor "C", ctor "C" ]) base.types } `shouldEqual` Left (CtorListing (tyCon "T") (ctor "C"))
      sigOk base { types = Map.insert (tyCon "T") (tOwning [ ctor "C", ctor "D" ]) base.types } `shouldEqual` Left (ListedCtorMissing (tyCon "T") (ctor "D"))

    it "is refused at a tag another constructor of its owner has" do
      sigOk (withCtors [ { name: ctor "C", info: wellFormedC }, { name: ctor "D", info: wellFormedC } ])
        `shouldEqual` Left (CtorTagCollision (tyCon "T") 0)
      sigOk (withCtors [ { name: ctor "C", info: wellFormedC }, { name: ctor "D", info: wellFormedC { tag = 1 } } ])
        `shouldEqual` Right unit

  describe "the names of Σ" do
    it "belong to one of the constructors and the values" do
      let sig = withValue (ctor "C") false int (withC wellFormedC)
      sigOk sig `shouldEqual` Left (CtorValueCollision (ctor "C"))

    it "are not resolved by a precedence where both hold one" do
      let sig = withValue (ctor "C") false int (withC wellFormedC)
      map (const unit) (lookupGlobal sig (ctor "C")) `shouldEqual` Nothing
      map (const unit) (infer (envOf sig emptyContext) TRowEmpty (Global unit (ctor "C") []))
        `shouldEqual` Left { at: unit, error: AmbiguousGlobal (ctor "C") }

  describe "a value or a foreign" do
    it "is refused at an ill-kinded scheme" do
      sigOk (withValue (ctor "x") false (TCon (tyCon "Gone") []) primSignature)
        `shouldEqual` Left (ValueEntryError (ctor "x") (UndeclaredTyCon (tyCon "Gone")))

    it "is refused, being a foreign, at an arrow performing effects" do
      let row = TRowExtend (RowEffectEntry (Qualified lib (EffName "Ping")) []) TRowEmpty
      let sig = withPing primSignature
      sigOk (withValue (ctor "f") true (fn int row int) sig) `shouldEqual` Left (EffectfulForeignEntry (ctor "f") row)
      sigOk (withValue (ctor "f") false (fn int row int) sig) `shouldEqual` Right unit

  describe "Σ prim" do
    it "holds every entry of Σ_Prim as Prim fixes it" do
      sigOk primSignature { types = Map.delete intTy primSignature.types } `shouldEqual` Left (PrimTyCon intTy)
      sigOk primSignature { ctors = map (_ { tag = 1 }) primSignature.ctors } `shouldEqual` Left (PrimCtor unitCtor)
      sigOk primSignature { attributes = Map.empty } `shouldEqual` Left (PrimAttribute (primAttribute "elaborationOnly"))
      sigOk primSignature { attributes = Map.insert (primAttribute "macro") { positional: [ int ], keyword: [] } primSignature.attributes }
        `shouldEqual` Left (PrimAttribute (primAttribute "macro"))

    it "holds nothing else under Prim" do
      let extra = Qualified (ModuleName "Prim") (TyName "Extra")
      sigOk primSignature { types = Map.insert extra (IntrinsicTyCon (monoScheme KType) CanonicalOpaque) primSignature.types }
        `shouldEqual` Left (ForeignPrimEntry (show extra))
      let extraAttribute = primAttribute "extra"
      sigOk primSignature { attributes = Map.insert extraAttribute { positional: [], keyword: [] } primSignature.attributes }
        `shouldEqual` Left (ForeignPrimEntry (show extraAttribute))

    it "lets no other type constructor claim a class Prim's alone have" do
      let fake = tyCon "Fun"
      let claiming cls = primSignature { types = Map.insert fake (IntrinsicTyCon (monoScheme KType) cls) primSignature.types }
      sigOk (claiming CanonicalFunction) `shouldEqual` Left (ClassClaimed fake CanonicalFunction)
      sigOk (claiming CanonicalRecord) `shouldEqual` Left (ClassClaimed fake CanonicalRecord)
      sigOk (claiming CanonicalVariant) `shouldEqual` Left (ClassClaimed fake CanonicalVariant)
      sigOk (claiming CanonicalLiteral) `shouldEqual` Left (ClassClaimed fake CanonicalLiteral)
      sigOk (claiming CanonicalOpaque) `shouldEqual` Right unit

  describe "an assembled signature" do
    it "is held to Σ ok where it is assembled" do
      let part = withC wellFormedC { scheme = monoScheme (TForall a KType (pureFn (TVar a) (tOf int))) }
      map (const unit) (initialSignature [ part ]) `shouldEqual` Left (SignatureIllFormed (CtorSchemeShape (ctor "C")))
      initialSignature [ withC wellFormedC ] `shouldSatisfy` isRight
      map (const unit) (initialSignature [ primSignature { ctors = Map.empty, types = Map.singleton unitTy (DataTyCon (monoScheme KType) []) } ])
        `shouldSatisfy` isConflict
  where
  isConflict = case _ of
    Left (ConflictingTyCon _) -> true
    _ -> false
