-- | The read-only kinding judgement over Core⁺.
-- |
-- | Two things are what these cases are for. **It checks as well as
-- | synthesizes**: a type whose parts do not stand where the whole needs them
-- | is refused rather than given a kind. And **what it answers is settled**:
-- | a kind metavariable anywhere it reads is refused, since a synthesizer could
-- | neither name one nor wait on it.
module Test.Stella.Compiler.Elaborate.Kinding (spec) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.CorePlus.Kind (XKind(..))
import Stella.Compiler.Elaborate.Mechanism.Kinding (KindEvidence(..), KindingEnv, KindingFault(..), KindingScope, synthKind)
import Stella.Compiler.Elaborate.CorePlus.Type (XConstraint(..), XRowEntry(..), XType(..))
import Stella.Compiler.Elaborate.Mechanism.Unify (KindMetaBinding(..), MetaBinding(..), emptyContext, freshKindMeta, freshMeta)
import Stella.Compiler.TypedCore (EffName(..), Kind(..), KindVar(..), ModuleName(..), Qualified(..), RegionName(..), RowElemKind(..), RowKey(..), Symbol(..), Tag(..), TyName(..), TyVar(..))
import Data.Either (Either(..))
import Data.Map (Map)
import Data.Map as Map
import Data.Set as Set
import Data.Tuple (Tuple(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

prim :: ModuleName
prim = ModuleName "Prim"

main' :: ModuleName
main' = ModuleName "Main"

con :: P.String -> P.Array XKind -> XType
con name kinds = XCon (Qualified prim (TyName name)) kinds

xInt :: XType
xInt = con "Int" []

listOf :: XType -> XType
listOf element = XApp (con "List" []) element

recordOf :: XType -> XType
recordOf row = XApp (con "Record" []) row

state :: Qualified EffName
state = Qualified main' (EffName "State")

-- | `Int`, `List`, `Record`, and the kind-polymorphic `Proxy`; the effect
-- | `State` of one type parameter.
env :: KindingEnv
env =
  { types: Map.fromFoldable
      [ Tuple (Qualified prim (TyName "Int")) { kindVars: [], body: KType }
      , Tuple (Qualified prim (TyName "List")) { kindVars: [], body: KFun KType KType }
      , Tuple (Qualified prim (TyName "Record")) { kindVars: [], body: KFun (KRow RowType) KType }
      , Tuple (Qualified prim (TyName "Proxy")) { kindVars: [ KindVar "k" ], body: KFun (KVar (KindVar "k")) KType }
      ]
  , effects: Map.fromFoldable [ Tuple state [ KType ] ]
  }

a :: TyVar
a = TyVar "a"

r :: TyVar
r = TyVar "r"

vars :: Map TyVar XKind
vars = Map.fromFoldable [ Tuple a XKType, Tuple r (XKRow RowType) ]

scope :: KindingScope
scope = { kindVars: Set.empty, tyVars: vars, regions: Set.empty }

kindOf :: XType -> Either KindingFault KindEvidence
kindOf = synthKind env scope emptyContext

keyN :: RowKey
keyN = SymbolKey (Symbol "n")

field :: RowKey -> XType -> XType -> XType
field key ty rest = XRowExtend (XRowTypeEntry key ty) rest

spec :: Spec Unit
spec = describe "Elaborate.Kinding" do
  describe "what it synthesizes" do
    it "reads a variable's kind from the scope, and refuses one it does not bind" do
      kindOf (XVar a) `shouldEqual` Right (ExactKind XKType)
      kindOf (XVar (TyVar "b")) `shouldEqual` Left (UnboundTyVar (TyVar "b"))

    it "instantiates a constructor's kind scheme with the kinds it is written with" do
      kindOf (con "Proxy" [ XKRow RowType ]) `shouldEqual` Right (ExactKind (XKFun (XKRow RowType) XKType))
      kindOf (con "Proxy" []) `shouldEqual` Left (KindArityMismatch (Qualified prim (TyName "Proxy")) 1 0)
      kindOf (con "Proxy" [ XKEffect ]) `shouldEqual` Left (NotQuantifiable XKEffect)
      kindOf (con "Absent" []) `shouldEqual` Left (UnknownTyCon (Qualified prim (TyName "Absent")))

    it "gives an application what its head's arrow produces" do
      kindOf (listOf xInt) `shouldEqual` Right (ExactKind XKType)

    it "gives the empty row any row kind, and a row with an element the kind the element settles" do
      kindOf XRowEmpty `shouldEqual` Right AnyRow
      kindOf (field keyN xInt XRowEmpty) `shouldEqual` Right (ExactKind (XKRow RowType))
      kindOf (XRowExtend (XRowEffectEntry state [ xInt ]) XRowEmpty) `shouldEqual` Right (ExactKind (XKRow RowEffect))

    it "gives a union the kind either side settles" do
      kindOf (XRowUnion XRowEmpty (XVar r)) `shouldEqual` Right (ExactKind (XKRow RowType))
      kindOf (XRowUnion XRowEmpty XRowEmpty) `shouldEqual` Right AnyRow

  describe "what it checks" do
    it "refuses an argument at another kind than the head asks for" do
      kindOf (listOf (XVar r)) `shouldEqual` Left (KindMismatch (ExactKind (XKRow RowType)) XKType)

    it "refuses applying what is not a function" do
      kindOf (XApp xInt xInt) `shouldEqual` Left (NotAFunctionKind XKType)

    it "refuses a binder at a kind that cannot be quantified, and a body not at Type" do
      kindOf (XForall (TyVar "e") XKEffect (XVar (TyVar "e"))) `shouldEqual` Left (NotQuantifiable XKEffect)
      kindOf (XForall (TyVar "s") (XKRow RowType) (XVar (TyVar "s")))
        `shouldEqual` Left (KindMismatch (ExactKind (XKRow RowType)) XKType)

    it "refuses a tail at another row kind than the element" do
      kindOf (field keyN xInt (XRowExtend (XRowEffectEntry state [ xInt ]) XRowEmpty))
        `shouldEqual` Left (KindMismatch (ExactKind (XKRow RowEffect)) (XKRow RowType))

    it "refuses an effect applied to arguments of the wrong number or kind" do
      kindOf (XRowExtend (XRowEffectEntry state []) XRowEmpty) `shouldEqual` Left (EffectArityMismatch state 1 0)
      kindOf (XRowExtend (XRowEffectEntry state [ XVar r ]) XRowEmpty)
        `shouldEqual` Left (KindMismatch (ExactKind (XKRow RowType)) XKType)

    it "refuses a union of two row kinds" do
      kindOf (XRowUnion (XVar r) (XRowExtend (XRowEffectEntry state [ xInt ]) XRowEmpty))
        `shouldEqual` Left (RowKindsDiffer RowType RowEffect)

    it "refuses a constraint's key a row of its kind cannot carry" do
      let
        effectRow = XRowExtend (XRowEffectEntry state [ xInt ]) XRowEmpty
        tag = TagKey (Tag "Ok")
      kindOf (XConstrained (XLacks tag effectRow) xInt) `shouldEqual` Left (KeyNotOfRowKind tag RowEffect)
      kindOf (XConstrained (XLacks keyN (XVar r)) (recordOf (XVar r))) `shouldEqual` Right (ExactKind XKType)

  describe "what it requires of the scope" do
    it "refuses a kind variable the scope does not bind, and admits it where it does" do
      let
        k = KindVar "k"
        polymorphic = XForall (TyVar "b") (XKVar k) xInt
        bound = scope { kindVars = Set.singleton k }
      kindOf polymorphic `shouldEqual` Left (UnboundKindVar k)
      kindOf (con "Proxy" [ XKVar k ]) `shouldEqual` Left (UnboundKindVar k)
      synthKind env bound emptyContext polymorphic `shouldEqual` Right (ExactKind XKType)
      synthKind env bound emptyContext (con "Proxy" [ XKVar k ]) `shouldEqual` Right (ExactKind (XKFun (XKVar k) XKType))

    it "judges every key by one rule, an element's and a constraint's alike" do
      let
        negative = PositionKey (-1)
        absent = EffectKey (Qualified main' (EffName "Absent"))
      kindOf (XConstrained (XLacks negative XRowEmpty) xInt) `shouldEqual` Left (NegativePosition (-1))
      kindOf (XConstrained (XLacks negative (XVar r)) xInt) `shouldEqual` Left (NegativePosition (-1))
      kindOf (field negative xInt XRowEmpty) `shouldEqual` Left (NegativePosition (-1))
      kindOf (XConstrained (XLacks absent XRowEmpty) xInt) `shouldEqual` Left (UnknownEffect (Qualified main' (EffName "Absent")))
      kindOf (field (RegionKey (RegionName "r")) xInt XRowEmpty) `shouldEqual` Left (KeyNotOfRowKind (RegionKey (RegionName "r")) RowType)
      kindOf (XConstrained (XLacks (RegionKey (RegionName "r")) XRowEmpty) xInt) `shouldEqual` Left (UnboundRegion (RegionName "r"))
      kindOf (XRowExtend (XRowRegionEntry (RegionName "r")) XRowEmpty) `shouldEqual` Left (UnboundRegion (RegionName "r"))

  describe "what it reads of Ψ" do
    it "reads an unsolved metavariable's kind, and applies a solved one" do
      let
        Tuple m ctx = freshMeta { kind: XKRow RowType, scope: { types: Set.empty, kinds: Set.empty, regions: Set.empty } } emptyContext
        solved = ctx { bindings = Map.insert m (Assigned xInt) ctx.bindings }
      synthKind env scope ctx (XMeta m) `shouldEqual` Right (ExactKind (XKRow RowType))
      synthKind env scope solved (listOf (XMeta m)) `shouldEqual` Right (ExactKind XKType)

    it "refuses a kind metavariable wherever it reads one" do
      let
        Tuple k ctx0 = freshKindMeta { scope: Set.empty, requirements: Set.empty } emptyContext
        Tuple m ctx = freshMeta { kind: XKMeta k, scope: { types: Set.empty, kinds: Set.empty, regions: Set.empty } } ctx0
        settledK = ctx { kindBindings = Map.insert k (KindAssigned XKType) ctx.kindBindings }
      synthKind env scope ctx (XMeta m) `shouldEqual` Left KindNotSettled
      synthKind env scope ctx (con "Proxy" [ XKMeta k ]) `shouldEqual` Left KindNotSettled
      synthKind env scope ctx (XForall (TyVar "b") (XKMeta k) xInt) `shouldEqual` Left KindNotSettled
      synthKind env scope settledK (XMeta m) `shouldEqual` Right (ExactKind XKType)
      -- The same metavariable, once its kind is solved, stands at that kind.
      synthKind env scope settledK (con "Proxy" [ XKMeta k ]) `shouldEqual` Right (ExactKind (XKFun XKType XKType))
