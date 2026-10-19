-- | Kinding.
-- |
-- | The cases the Implementation Plan singles out are here: the stratification
-- | of D24, key well-formedness at each row element kind, and the two side
-- | conditions that make a row sharp and a union disjoint.
module Test.Stella.Compiler.TypedCore.Kinding (spec) where

import Prelude

import Prim as P

import Stella.Compiler.TypedCore (Constraint(..), EffName(..), Ident(..), Kind(..), KindVar(..), ModuleName(..), Qualified(..), RowElemKind(..), RowEntry(..), RowKey(..), Symbol(..), Tag(..), TyName(..), TyVar(..), Type(..), monoScheme)
import Stella.Compiler.TypedCore.Context (Context, assume, bindKindVars, bindTyVar, emptyContext)
import Stella.Compiler.TypedCore.Kinding (KindError(..), Synthesized(..), checkKind, kindOf, wellFormedConstraint)
import Stella.Compiler.TypedCore.Prim (intTy, ioTy, primSignature, recordTy, stringTy, variantTy)
import Stella.Compiler.TypedCore.Signature (Signature, TyConInfo(..))
import Data.Either (Either(..))
import Data.Map as Map
import Data.Tuple (Tuple(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

prim :: ModuleName
prim = ModuleName "Prim"

tyCon :: P.String -> Qualified TyName
tyCon name = Qualified prim (TyName name)

effect :: P.String -> Qualified EffName
effect name = Qualified prim (EffName name)

stateEff :: Qualified EffName
stateEff = effect "State"

consoleEff :: Qualified EffName
consoleEff = effect "Console"

auditEff :: Qualified EffName
auditEff = effect "Audit"

-- | `k`, the one kind variable a scheme here binds.
kindVar :: KindVar
kindVar = KindVar "k"

int :: Type
int = TCon intTy []

string :: Type
string = TCon stringTy []

record :: Type -> Type
record row = TApp (TCon recordTy []) row

variant :: Type -> Type
variant row = TApp (TCon variantTy []) row

io :: Type -> Type
io ty = TApp (TCon ioTy []) ty

proxy :: P.Array Kind -> Type
proxy kinds = TCon (tyCon "Proxy") kinds

-- | `( k : τ | ρ )`
field :: RowKey -> Type -> Type -> Type
field key ty rest = TRowExtend (RowTypeEntry key ty) rest

-- | `( E τ̄ | ρ )`
effectElem :: Qualified EffName -> P.Array Type -> Type -> Type
effectElem name args rest = TRowExtend (RowEffectEntry name args) rest

-- | `( s : E τ̄ | ρ )`
labelled :: Symbol -> Qualified EffName -> P.Array Type -> Type -> Type
labelled s name args rest = TRowExtend (RowLabelledEffectEntry s name args) rest

-- | `Σ_Prim` together with what these cases add: a kind-polymorphic data type
-- | and two effects.
sig :: Signature
sig = primSignature
  { types = Map.insert (tyCon "Proxy")
      ( DataTyCon { kindVars: [ kindVar ], body: KFun (KVar kindVar) KType }
          [ Qualified prim (Ident "Proxy") ]
      )
      primSignature.types
  , effects = Map.fromFoldable
      [ Tuple stateEff { params: [ { name: TyVar "a", kind: KType } ], operations: Map.empty }
      , Tuple consoleEff { params: [], operations: Map.empty }
      ]
  }

-- | A `Σ` holding a type constructor that produces a row. Kinding rejects it
-- | at the occurrence rather than trusting the table.
rowProducingSig :: Signature
rowProducingSig =
  sig
    { types = Map.insert (tyCon "MkRow")
        (DataTyCon (monoScheme (KFun KType (KRow RowType))) [])
        sig.types
    }

-- | `r` and `s` at `Row Type`, `e` at `Row Effect`.
rowVar :: TyVar
rowVar = TyVar "r"

otherRowVar :: TyVar
otherRowVar = TyVar "s"

effRowVar :: TyVar
effRowVar = TyVar "e"

rowCtx :: Context
rowCtx =
  bindTyVar (bindTyVar (bindTyVar emptyContext rowVar (KRow RowType)) otherRowVar (KRow RowType))
    effRowVar
    (KRow RowEffect)

-- | `Γ` extended with one assumption.
assuming :: Constraint -> (Context -> Spec Unit) -> Spec Unit
assuming constraint body = body (assume rowCtx constraint)

nameSym :: Symbol
nameSym = Symbol "name"

cacheSym :: Symbol
cacheSym = Symbol "cache"

counterSym :: Symbol
counterSym = Symbol "counter"

spec :: Spec Unit
spec = describe "TypedCore.Kinding" do
  describe "the quantifiable layer" do
    it "refuses a type variable at Effect" do
      kindOf sig emptyContext (TForall (TyVar "a") KEffect int)
        `shouldEqual` Left (NotQuantifiable KEffect)

    it "refuses one at a kind returning Effect" do
      -- the restriction is on the whole kind, not only on its result
      kindOf sig emptyContext (TForall (TyVar "f") (KFun KType KEffect) int)
        `shouldEqual` Left (NotQuantifiable KEffect)

    it "refuses instantiation at Effect" do
      kindOf sig emptyContext (proxy [ KEffect ])
        `shouldEqual` Left (NotQuantifiable KEffect)

    it "keeps higher-kinded quantification" do
      kindOf sig emptyContext (TForall (TyVar "f") (KFun KType KType) int)
        `shouldEqual` Right (Kinded KType)

    it "admits a row variable at either row element kind" do
      kindOf sig emptyContext (TForall (TyVar "r") (KRow RowEffect) int)
        `shouldEqual` Right (Kinded KType)

  describe "what may produce a row" do
    it "admits a constructor kind consuming a row" do
      kindOf sig emptyContext (TForall (TyVar "f") (KFun (KRow RowType) KType) int)
        `shouldEqual` Right (Kinded KType)

    it "refuses one producing a row" do
      -- row syntax is the only thing that produces a row, which is what keeps
      -- every well-kinded row normalizable
      kindOf sig emptyContext (TForall (TyVar "f") (KFun (KRow RowType) (KRow RowType)) int)
        `shouldEqual` Left (ResultNotType (KRow RowType))

    it "refuses one whose result a kind variable could be instantiated to" do
      kindOf sig (bindKindVars emptyContext [ kindVar ])
        (TForall (TyVar "f") (KFun KType (KVar kindVar)) int)
        `shouldEqual` Left (ResultNotType (KVar kindVar))

    it "refuses a declared constructor producing a row" do
      kindOf rowProducingSig emptyContext (TCon (tyCon "MkRow") [])
        `shouldEqual` Left (ResultNotType (KRow RowType))

    it "refuses it where a row is wanted, rather than taking it for one" do
      kindOf rowProducingSig emptyContext (record (TApp (TCon (tyCon "MkRow") []) int))
        `shouldEqual` Left (ResultNotType (KRow RowType))

  describe "what a type is built from" do
    it "refuses a constructor the signature does not declare" do
      kindOf primSignature emptyContext (TCon (tyCon "Ghost") [])
        `shouldEqual` Left (UndeclaredTyCon (tyCon "Ghost"))

    it "refuses an application whose head takes no argument" do
      let int' = TCon intTy []
      kindOf primSignature emptyContext (TApp int' int')
        `shouldEqual` Left (AppliedNonConstructor int')

    it "refuses a row operator over something that is not a row" do
      let int' = TCon intTy []
      kindOf primSignature emptyContext (TRowUnion int' int')
        `shouldEqual` Left (NotARowKind int' KType)

  describe "instantiation" do
    it "substitutes the kind written at the use site" do
      kindOf sig emptyContext (TApp (proxy [ KType ]) int)
        `shouldEqual` Right (Kinded KType)

    it "instantiates the same scheme at a row kind" do
      kindOf sig emptyContext (TApp (proxy [ KRow RowType ]) (field (SymbolKey nameSym) string TRowEmpty))
        `shouldEqual` Right (Kinded KType)

    it "counts the kinds a scheme binds" do
      kindOf sig emptyContext (proxy [])
        `shouldEqual` Left (KindArgCount (tyCon "Proxy") 1 0)

    it "refuses a kind variable outside the declaration binding it" do
      kindOf sig emptyContext (proxy [ KVar kindVar ])
        `shouldEqual` Left (UnboundKindVar kindVar)

    it "admits it within that declaration" do
      kindOf sig (bindKindVars emptyContext [ kindVar ]) (proxy [ KVar kindVar ])
        `shouldEqual` Right (Kinded (KFun (KVar kindVar) KType))

  describe "the empty row" do
    it "has no element kind of its own" do
      kindOf sig emptyContext TRowEmpty `shouldEqual` Right AnyRow

    it "stands where a row kind is required" do
      checkKind sig emptyContext (record TRowEmpty) KType `shouldEqual` Right unit

    it "does not stand where a type is required" do
      kindOf sig emptyContext (io TRowEmpty)
        `shouldEqual` Left (ExpectedKind TRowEmpty KType AnyRow)

  describe "keys" do
    it "tells a Symbol and a Tag of one spelling apart" do
      kindOf sig emptyContext (field (SymbolKey (Symbol "X")) int (field (TagKey (Tag "X")) int TRowEmpty))
        `shouldEqual` Right (Kinded (KRow RowType))

    it "admits a tuple keyed by position" do
      kindOf sig emptyContext (field (PositionKey 0) int (field (PositionKey 1) string TRowEmpty))
        `shouldEqual` Right (Kinded (KRow RowType))

    it "refuses a negative position" do
      -- the index of a `PositionKey` is a `Nat`; the AST holds an `Int`
      kindOf sig emptyContext (field (PositionKey (-1)) int TRowEmpty)
        `shouldEqual` Left (NegativePosition (-1))

    it "refuses an effect key over a type payload" do
      kindOf sig emptyContext (field (EffectKey stateEff) int TRowEmpty)
        `shouldEqual` Left (KeyNotAtKind (EffectKey stateEff) RowType)

    it "does not narrow the keys by the constructor wrapping the row" do
      -- `Variant ( 0 : Int )` reads oddly and is well-kinded; which keys a
      -- structure uses is settled by the surface
      checkKind sig emptyContext (variant (field (PositionKey 0) int TRowEmpty)) KType
        `shouldEqual` Right unit

    it "refuses a tag as the key of an effect row" do
      wellFormedConstraint sig rowCtx (Lacks (TagKey (Tag "Ok")) (TVar effRowVar))
        `shouldEqual` Left (KeyNotAtKind (TagKey (Tag "Ok")) RowEffect)

    it "admits a Symbol there, which may key a labelled instance" do
      wellFormedConstraint sig rowCtx (Lacks (SymbolKey cacheSym) (TVar effRowVar))
        `shouldEqual` Right unit

    it "admits a declared effect as a key" do
      wellFormedConstraint sig rowCtx (Lacks (EffectKey consoleEff) (TVar effRowVar))
        `shouldEqual` Right unit

    it "refuses an undeclared one" do
      wellFormedConstraint sig rowCtx (Lacks (EffectKey auditEff) (TVar effRowVar))
        `shouldEqual` Left (UndeclaredEffect auditEff)

  describe "effect row elements" do
    it "checks the payload against the declaration" do
      kindOf sig emptyContext (effectElem stateEff [ int ] TRowEmpty)
        `shouldEqual` Right (Kinded (KRow RowEffect))

    it "requires the payload to be saturated" do
      kindOf sig emptyContext (effectElem stateEff [ int, string ] TRowEmpty)
        `shouldEqual` Left (EffectArgCount stateEff 1 2)

    it "requires the declaration to exist" do
      kindOf sig emptyContext (effectElem auditEff [] TRowEmpty)
        `shouldEqual` Left (UndeclaredEffect auditEff)

    it "checks an argument at the kind the parameter has" do
      kindOf sig emptyContext (effectElem stateEff [ TRowEmpty ] TRowEmpty)
        `shouldEqual` Left (ExpectedKind TRowEmpty KType AnyRow)

  describe "sharpness" do
    it "admits one effect twice under written keys" do
      kindOf sig emptyContext
        (labelled cacheSym stateEff [ int ] (labelled counterSym stateEff [ int ] TRowEmpty))
        `shouldEqual` Right (Kinded (KRow RowEffect))

    it "refuses the same written key twice" do
      kindOf sig emptyContext
        (labelled cacheSym stateEff [ int ] (labelled cacheSym stateEff [ string ] TRowEmpty))
        `shouldEqual` Left (NotSharp (SymbolKey cacheSym) (labelled cacheSym stateEff [ string ] TRowEmpty))

    it "refuses one effect twice with no key written" do
      kindOf sig emptyContext (effectElem stateEff [ int ] (effectElem stateEff [ string ] TRowEmpty))
        `shouldEqual` Left (NotSharp (EffectKey stateEff) (effectElem stateEff [ string ] TRowEmpty))

    it "refuses a key over a tail the context does not prove it absent from" do
      kindOf sig rowCtx (field (SymbolKey nameSym) string (TVar rowVar))
        `shouldEqual` Left (NotSharp (SymbolKey nameSym) (TVar rowVar))

    assuming (Lacks (SymbolKey nameSym) (TVar rowVar)) \ctx ->
      it "admits it once the context proves the key absent" do
        kindOf sig ctx (field (SymbolKey nameSym) string (TVar rowVar))
          `shouldEqual` Right (Kinded (KRow RowType))

  describe "constrained types" do
    it "kinds the body under the constraint" do
      -- the sharpness of the row is what the constraint is there to establish
      kindOf sig rowCtx
        ( TConstrained (Lacks (SymbolKey nameSym) (TVar rowVar))
            (record (field (SymbolKey nameSym) string (TVar rowVar)))
        )
        `shouldEqual` Right (Kinded KType)

    it "does not carry it beyond that body" do
      kindOf sig rowCtx (record (field (SymbolKey nameSym) string (TVar rowVar)))
        `shouldEqual` Left (NotSharp (SymbolKey nameSym) (TVar rowVar))

    it "admits an assumption that contradicts itself, which need only be well formed" do
      -- a type application may substitute a row that makes what a constraint
      -- abstraction assumes false, so `Γ, C` does not ask `C` to be satisfiable
      kindOf sig rowCtx
        ( TConstrained (Lacks (SymbolKey nameSym) (field (SymbolKey nameSym) string TRowEmpty))
            int
        )
        `shouldEqual` Right (Kinded KType)

    assuming (Lacks (SymbolKey nameSym) (field (SymbolKey nameSym) int TRowEmpty)) \ctx -> do
      it "discharges a sharpness premise under an inconsistent assumption" do
        -- sharpness is an entailment, and an inconsistent context entails all
        kindOf sig ctx (field (SymbolKey nameSym) string (TVar rowVar))
          `shouldEqual` Right (Kinded (KRow RowType))
        kindOf sig ctx (TRowUnion (TVar rowVar) (TVar rowVar))
          `shouldEqual` Right (Kinded (KRow RowType))

      it "makes nothing else well formed there" do
        kindOf sig ctx (TApp int int) `shouldEqual` Left (AppliedNonConstructor int)
        kindOf sig ctx (TVar (TyVar "unbound")) `shouldEqual` Left (UnboundTyVar (TyVar "unbound"))
        kindOf sig ctx (TRowUnion (TVar rowVar) (TVar effRowVar))
          `shouldEqual` Left (ExpectedKind (TVar effRowVar) (KRow RowType) (Kinded (KRow RowEffect)))

    it "requires the constraint itself to be well formed" do
      kindOf sig rowCtx (TConstrained (Lacks (TagKey (Tag "Ok")) (TVar effRowVar)) int)
        `shouldEqual` Left (KeyNotAtKind (TagKey (Tag "Ok")) RowEffect)

  describe "disjointness" do
    it "refuses a union the context does not prove disjoint" do
      kindOf sig rowCtx (TRowUnion (TVar rowVar) (TVar otherRowVar))
        `shouldEqual` Left (NotDisjoint (TVar rowVar) (TVar otherRowVar))

    assuming (Disjoint (TVar rowVar) (TVar otherRowVar)) \ctx ->
      it "admits it once the context proves them disjoint" do
        kindOf sig ctx (TRowUnion (TVar rowVar) (TVar otherRowVar))
          `shouldEqual` Right (Kinded (KRow RowType))

    it "requires both sides at one row element kind" do
      wellFormedConstraint sig rowCtx (Disjoint (TVar rowVar) (TVar effRowVar))
        `shouldEqual` Left (ExpectedKind (TVar effRowVar) (KRow RowType) (Kinded (KRow RowEffect)))
