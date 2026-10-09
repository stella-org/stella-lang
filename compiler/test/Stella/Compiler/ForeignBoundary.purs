module Test.Stella.Compiler.ForeignBoundary (spec) where

import Prelude
import Prim hiding (Constraint, Type)

import Data.Either (Either(..))
import Data.Map as Map
import Data.Tuple (Tuple(..))
import Stella.Compiler.ForeignBoundary (Position(..), Refusal(..), Refused, crossingOf)
import Stella.Compiler.ForeignManifest (ResultKind(..), Signature, ValueKind(..))
import Stella.Compiler.TypedCore.Kind (Kind(..), RowElemKind(..), monoScheme)
import Stella.Compiler.TypedCore.Name (EffName(..), ModuleName(..), Qualified(..), Symbol(..), TyName(..), TyVar(..))
import Stella.Compiler.TypedCore.Prim (booleanTy, charTy, fn, intTy, ioTy, numberTy, pureFn, recordTy, stringTy, unitTy)
import Stella.Compiler.TypedCore.Signature (CanonicalClass(..), TyConInfo(..), emptySignature)
import Stella.Compiler.TypedCore.Type (Constraint(..), RowEntry(..), RowKey(..), Type(..), TypeScheme)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

-- | A signature declaring `Handle` and `Cell`, foreign types, and `Box`, a data
-- | type.
types :: Map.Map (Qualified TyName) TyConInfo
types = Map.fromFoldable [ Tuple handle (IntrinsicTyCon (monoScheme KType) CanonicalOpaque), Tuple cell (IntrinsicTyCon (monoScheme (KFun KType KType)) CanonicalOpaque), Tuple box (DataTyCon (monoScheme KType) []) ]

handle :: Qualified TyName
handle = Qualified (ModuleName "M") (TyName "Handle")

cell :: Qualified TyName
cell = Qualified (ModuleName "M") (TyName "Cell")

box :: Qualified TyName
box = Qualified (ModuleName "M") (TyName "Box")

con :: Qualified TyName -> Type
con n = TCon n []

io :: Type -> Type
io = TApp (con ioTy)

-- | A row performing `E`.
effects :: Type
effects = TRowExtend (RowEffectEntry (Qualified (ModuleName "M") (EffName "E")) []) TRowEmpty

-- | `x ∉ r`.
lacks :: Constraint
lacks = Lacks (SymbolKey (Symbol "x")) (TVar (TyVar "r"))

scheme :: Type -> TypeScheme
scheme body = { kindVars: [], body }

crossing :: Type -> Either Refused Signature
crossing t = crossingOf (emptySignature { types = types }) (scheme t)

spec :: Spec Unit
spec = describe "Stella.Compiler.ForeignBoundary" do
  describe "a foreign's type that crosses" do
    it "gives each argument and the result the kind it crosses as, a scalar as the host's own and a foreign type as opaque" do
      crossing (pureFn (con intTy) (pureFn (con numberTy) (pureFn (con charTy) (pureFn (con stringTy) (pureFn (con booleanTy) (pureFn (con handle) (con unitTy)))))))
        `shouldEqual` Right { params: [ AsInt, AsNumber, AsChar, AsString, AsBoolean, AsOpaque ], result: AsValue AsUnit }

    it "gives a result `IO τ` as an action producing what τ crosses as, and a constant no argument" do
      crossing (pureFn (con stringTy) (io (con handle))) `shouldEqual` Right { params: [ AsString ], result: AsAction AsOpaque }
      crossing (io (con unitTy)) `shouldEqual` Right { params: [], result: AsAction AsUnit }
      crossing (con intTy) `shouldEqual` Right { params: [], result: AsValue AsInt }

    it "is read under its quantifiers" do
      crossing (TForall (TyVar "a") KType (pureFn (con intTy) (con intTy))) `shouldEqual` Right { params: [ AsInt ], result: AsValue AsInt }

  describe "a foreign's type that does not cross" do
    it "is refused at the first part that does not, counted from one" do
      crossing (pureFn (con intTy) (pureFn (con box) (con intTy))) `shouldEqual` Left { position: Argument 2, refusal: DataType box }
      crossing (pureFn (con intTy) (TApp (con recordTy) TRowEmpty)) `shouldEqual` Left { position: Result, refusal: RecordType }
      crossing (pureFn (pureFn (con intTy) (con intTy)) (con intTy)) `shouldEqual` Left { position: Argument 1, refusal: FunctionType }
      crossing (TForall (TyVar "a") KType (pureFn (TVar (TyVar "a")) (con intTy))) `shouldEqual` Left { position: Argument 1, refusal: TypeVariable (TyVar "a") }

    it "holds an action only as its result, and one producing no action" do
      crossing (pureFn (io (con intTy)) (con unitTy)) `shouldEqual` Left { position: Argument 1, refusal: ActionArgument }
      crossing (io (io (con intTy))) `shouldEqual` Left { position: Result, refusal: ActionOfAction }

    it "is pure at every arrow, and under no constraint" do
      crossing (pureFn (con intTy) (fn (con intTy) effects (con intTy))) `shouldEqual` Left { position: Argument 2, refusal: PerformingArrow }
      crossing (TForall (TyVar "r") (KRow RowType) (TConstrained lacks (con intTy))) `shouldEqual` Left { position: Result, refusal: ConstrainedType }
      crossing (pureFn (TConstrained lacks (con intTy)) (con intTy)) `shouldEqual` Left { position: Argument 1, refusal: ConstrainedType }

    it "takes an arrow whose row's normal form is empty as pure" do
      crossing (fn (con intTy) (TRowUnion TRowEmpty TRowEmpty) (con intTy)) `shouldEqual` Right { params: [ AsInt ], result: AsValue AsInt }
      crossing (pureFn (TApp (con cell) (fn (con intTy) (TRowUnion TRowEmpty TRowEmpty) (con intTy))) (con intTy)) `shouldEqual` Right { params: [ AsOpaque ], result: AsValue AsInt }

    it "refuses an arrow performing effects inside an opaque type's arguments, as an argument or as the result" do
      let performing = TApp (con cell) (fn (con intTy) effects (con intTy))
      crossing (pureFn performing (con intTy)) `shouldEqual` Left { position: Argument 1, refusal: PerformingArrow }
      crossing (pureFn (con intTy) (io performing)) `shouldEqual` Left { position: Result, refusal: PerformingArrow }

    it "names no type that is none of a value's forms" do
      let unknown = con (Qualified (ModuleName "M") (TyName "Unknown"))
      crossing (pureFn unknown (con intTy)) `shouldEqual` Left { position: Argument 1, refusal: NoValue unknown }
