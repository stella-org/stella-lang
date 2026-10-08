-- | Core⁺ terms, and the boundary they cross into Core.
-- |
-- | Two things are what these cases are for. **The boundary reports everything
-- | left, in one deterministic order, at the nearest node with a location**, so a
-- | diagnostic names every unresolved hole rather than the first one met. And
-- | **the free variables of a term respect every binder of every class**, which is
-- | what the scope of a term metavariable is later checked against.
module Test.Stella.Compiler.Elaborate.Term (spec) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.CorePlus.Kind (KindMetaVar(..), XKind(..))
import Stella.Compiler.Elaborate.CorePlus.Term (FreeVars, Residue(..), TermMetaVar(..), XDecisionTree(..), XExpr(..), fromCoreExpr, freeVarsOf, metasOfTerm, toCoreExpr)
import Stella.Compiler.Elaborate.CorePlus.Type (MetaVar(..), XRowEntry(..), XType(..))
import Stella.Compiler.TypedCore (Constraint(..), DecisionTree(..), EffName(..), Expr(..), Ident(..), JoinName(..), Kind(..), KindVar(..), Literal(..), ModuleName(..), OpClause(..), OpName(..), Occurrence(..), Qualified(..), RegionName(..), RowElemKind(..), RowEntry(..), RowKey(..), Symbol(..), TyName(..), TyVar(..), Type(..))
import Data.Array.NonEmpty as NonEmptyArray
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

prim :: ModuleName
prim = ModuleName "Prim"

main' :: ModuleName
main' = ModuleName "Main"

intTy :: Type
intTy = TCon (Qualified prim (TyName "Int")) []

xInt :: XType
xInt = XCon (Qualified prim (TyName "Int")) []

counter :: Qualified EffName
counter = Qualified main' (EffName "Counter")

keyN :: RowKey
keyN = SymbolKey (Symbol "n")

x :: Ident
x = Ident "x"

y :: Ident
y = Ident "y"

f :: Ident
f = Ident "f"

a :: TyVar
a = TyVar "a"

region :: RegionName
region = RegionName "r"

r :: TyVar
r = TyVar "r"

k :: KindVar
k = KindVar "k"

j :: JoinName
j = JoinName "j"

-- | A Core term reaching most forms: a type abstraction, a `letrec`, a
-- | `letjoin` jumped to from a decision tree, and a region around a handler
-- | whose clause reads its cell.
coreTerm :: Expr P.Int
coreTerm =
  TyLam 1 a KType
    ( LetRec 2
        [ { name: f, ty: intTy, value: Lam 3 x intTy (Var 4 x) } ]
        ( LetJoin 5 j [ { name: y, ty: intTy } ] intTy (Var 6 y)
            ( Case 7 [ Lit 8 (LitInt 0) ]
                ( SwitchLit (OccScrutinee 0)
                    [ { lit: LitInt 0, tree: Leaf (Jump 9 j [ Lit 10 (LitInt 1) ]) } ]
                    (Bind x (OccScrutinee 0) (Leaf (Region 11 region [ { key: keyN, ty: intTy } ] [ Lit 13 (LitInt 0) ] (Handle 16 (Var 12 x) handler))))
                )
            )
        )
    )
  where
  handler =
    { element: RowEffectEntry counter []
    , returnClause: { binder: y, ty: intTy, body: Var 14 y }
    , opClauses:
        [ FastClause
            { op: OpName "next"
            , tyBinders: []
            , argBinder: { name: x, ty: TCon (Qualified prim (TyName "Unit")) [] }
            , body: ReadCell 15 region keyN
            }
        ]
    }

-- | The forms `coreTerm` does not reach: records, variants, the constraint and
-- | type applications, widening, `perform`, a cell write, a full clause, and
-- | the other three dispatches.
otherForms :: Expr P.Int
otherForms =
  ConstraintLam 1 (Lacks keyN (TVar r))
    ( RecordMerge 2
        (RecordExtend 3 keyN (Lit 4 (LitInt 1)) (RecordEmpty 5))
        ( RecordUpdate 6 keyN
            (RecordRestrict 7 keyN (RecordSelect 8 keyN (TyApp 9 (ConstraintApp 10 (Var 11 x)) intTy)))
            ( Case 12 [ VariantWeaken 13 keyN intTy (VariantInject 14 keyN (Var 15 y)) ]
                ( SwitchKey (OccScrutinee 0)
                    [ { key: keyN, tree: Guard (Lit 16 (LitBoolean true)) (Leaf (VariantAbsurd 17 intTy (Var 18 y))) (Leaf (Var 19 y)) } ]
                    ( Just
                        ( SwitchCtor (OccScrutinee 0)
                            [ { ctor: Qualified main' (Ident "C"), tree: Leaf (OpenEff 20 (TVar r) (Perform 21 keyN (OpName "op") [ intTy ] (App 22 (Global 23 (Qualified main' (Ident "g")) [ KRow RowType, KFun KType KType ]) (Var 24 x)))) } ]
                            Nothing
                        )
                    )
                )
            )
        )
    )

fullClause :: Expr P.Int
fullClause = Handle 1 (Var 2 x) handler
  where
  handler =
    { element: RowLabelledEffectEntry (Symbol "cache") counter [ intTy ]
    , returnClause: { binder: y, ty: intTy, body: WriteCell 3 region keyN (Var 4 y) }
    , opClauses:
        [ FullClause
            { op: OpName "next"
            , tyBinders: [ { name: a, kind: KRow RowType } ]
            , argBinder: { name: x, ty: TVar a }
            , contBinder: { name: f, ty: intTy }
            , body: App 5 (Var 6 f) (Var 7 x)
            }
        ]
    }

free :: FreeVars
free = { values: Set.empty, types: Set.empty, kinds: Set.empty, joins: Set.empty, regions: Set.empty }

spec :: Spec Unit
spec = describe "Elaborate.Term" do
  describe "the boundary" do
    it "gives back a Core term lifted into Core⁺ unchanged" do
      toCoreExpr (fromCoreExpr coreTerm) `shouldEqual` Right coreTerm
      toCoreExpr (fromCoreExpr otherForms) `shouldEqual` Right otherForms
      toCoreExpr (fromCoreExpr fullClause) `shouldEqual` Right fullClause

    it "reports every residue, in the order a depth-first walk meets them" do
      let
        term =
          EApp 1
            (ELam 2 x (XMeta (MetaVar 0)) (ETermMeta 3 (TermMetaVar 0)))
            (EApp 4 (EGlobal 5 (Qualified main' f) [ XKMeta (KindMetaVar 0) ]) (EHole 6 xInt))
      toCoreExpr term `shouldEqual` Left
        ( NonEmptyArray.cons' (ResidualTypeMeta 2 (MetaVar 0))
            [ ResidualTermMeta 3 (TermMetaVar 0)
            , ResidualKindMeta 5 (KindMetaVar 0)
            , ResidualHole 6 xInt
            ]
        )

    it "reports what stands in a decision tree or a handler at the term enclosing it" do
      let
        tree = XBind x (OccScrutinee 0) (XLeaf (ETermMeta 3 (TermMetaVar 1)))
        handler =
          { element: XRowEffectEntry counter [ XMeta (MetaVar 1) ]
          , returnClause: { binder: y, ty: xInt, body: EVar 4 y }
          , opClauses: []
          }
        term = ECase 1 [ EHandle 2 (EVar 5 x) handler ] tree
      toCoreExpr term `shouldEqual` Left
        (NonEmptyArray.cons' (ResidualTypeMeta 2 (MetaVar 1)) [ ResidualTermMeta 3 (TermMetaVar 1) ])

    it "reports the metavariables a hole's type holds before the hole itself" do
      let
        ty = XApp (XCon (Qualified prim (TyName "List")) [ XKMeta (KindMetaVar 2) ]) (XMeta (MetaVar 1))
      toCoreExpr (EHole 1 ty) `shouldEqual` Left
        ( NonEmptyArray.cons' (ResidualKindMeta 1 (KindMetaVar 2))
            [ ResidualTypeMeta 1 (MetaVar 1), ResidualHole 1 ty ]
        )

    it "reports a type application's own type before the term it applies" do
      toCoreExpr (ETyApp 1 (ETermMeta 2 (TermMetaVar 0)) (XMeta (MetaVar 0))) `shouldEqual` Left
        (NonEmptyArray.cons' (ResidualTypeMeta 1 (MetaVar 0)) [ ResidualTermMeta 2 (TermMetaVar 0) ])

    it "reports a handler's element before the computation, and its clauses after it" do
      let
        handler =
          { element: XRowEffectEntry counter [ XMeta (MetaVar 0) ]
          , returnClause: { binder: y, ty: XMeta (MetaVar 2), body: ETermMeta 3 (TermMetaVar 1) }
          , opClauses: []
          }
        term = EHandle 1 (ETermMeta 2 (TermMetaVar 0)) handler
      toCoreExpr term `shouldEqual` Left
        ( NonEmptyArray.cons' (ResidualTypeMeta 1 (MetaVar 0))
            [ ResidualTermMeta 2 (TermMetaVar 0)
            , ResidualTypeMeta 1 (MetaVar 2)
            , ResidualTermMeta 3 (TermMetaVar 1)
            ]
        )

    it "reports a region's layout first, its initial values next, and its body last" do
      let
        term = ERegion 1 region [ { key: keyN, ty: XMeta (MetaVar 1) } ] [ ETermMeta 4 (TermMetaVar 2) ] (ETermMeta 2 (TermMetaVar 0))
      toCoreExpr term `shouldEqual` Left
        ( NonEmptyArray.cons' (ResidualTypeMeta 1 (MetaVar 1))
            [ ResidualTermMeta 4 (TermMetaVar 2)
            , ResidualTermMeta 2 (TermMetaVar 0)
            ]
        )

    it "reports a metavariable once for each place it stands" do
      let
        term = ELet 1 x (XMeta (MetaVar 0)) (ETermMeta 2 (TermMetaVar 0)) (ETermMeta 3 (TermMetaVar 0))
      toCoreExpr term `shouldEqual` Left
        ( NonEmptyArray.cons' (ResidualTypeMeta 1 (MetaVar 0))
            [ ResidualTermMeta 2 (TermMetaVar 0), ResidualTermMeta 3 (TermMetaVar 0) ]
        )

  describe "free variables" do
    it "has a closed Core term mention nothing" do
      freeVarsOf (fromCoreExpr coreTerm) `shouldEqual` free

    it "takes a let's binder over its body and not over its right-hand side" do
      freeVarsOf (ELet 1 x xInt (EVar 2 x) (EVar 3 x))
        `shouldEqual` free { values = Set.singleton x }

    it "takes a join point over its definition and its body, and its parameters over the definition alone" do
      let
        term = ELetJoin 1 j [ { name: y, ty: xInt } ] xInt (EJump 2 j [ EVar 3 y ]) (EVar 4 y)
      freeVarsOf term `shouldEqual` free { values = Set.singleton y }
      freeVarsOf (EJump 1 j []) `shouldEqual` free { joins = Set.singleton j }

    it "takes a tree's bind over the tree beneath it" do
      let
        term = ECase 1 [ EVar 2 y ] (XBind x (OccScrutinee 0) (XLeaf (EVar 3 x)))
      freeVarsOf term `shouldEqual` free { values = Set.singleton y }

    it "takes a region name over the body and not over the layout or the initial values" do
      let
        inner = RegionName "inner"
        outer = RegionName "outer"
        opened cellTy initial = ERegion 1 inner [ { key: keyN, ty: cellTy } ] [ initial ] (EReadCell 2 inner keyN)
      freeVarsOf (opened xInt (ELit 3 (LitInt 0)))
        `shouldEqual` free
      freeVarsOf (opened (XVar r) (EReadCell 3 outer keyN))
        `shouldEqual` free { types = Set.singleton r, regions = Set.singleton outer }
      freeVarsOf (opened xInt (EReadCell 3 inner keyN))
        `shouldEqual` free { regions = Set.singleton inner }

    it "takes a type abstraction's binder over its body, and leaves every kind variable free" do
      let
        term = ETyLam 1 a (XKVar k) (ELam 2 x (XVar a) (EVar 3 x))
      freeVarsOf term `shouldEqual` free { kinds = Set.singleton k }

    it "takes a letrec's names over every right-hand side and the body" do
      let
        term = ELetRec 1 [ { name: f, ty: xInt, value: ELam 2 x xInt (EApp 3 (EVar 4 f) (EVar 5 y)) } ] (EVar 6 f)
      freeVarsOf term `shouldEqual` free { values = Set.singleton y }

  describe "metavariables" do
    it "are collected from every position, by class" do
      let
        term =
          EApp 3
            (ELam 1 x (XMeta (MetaVar 0)) (EGlobal 2 (Qualified main' f) [ XKMeta (KindMetaVar 3) ]))
            (ETermMeta 4 (TermMetaVar 5))
      metasOfTerm term `shouldEqual`
        { terms: Set.singleton (TermMetaVar 5)
        , types: Set.singleton (MetaVar 0)
        , kinds: Set.singleton (KindMetaVar 3)
        }
