-- | `Γ*` as an attempt reads it off a site.
-- |
-- | Two properties are what these cases are for. An assumption about a flexible
-- | tail yields no atomic fact, since a fact is about a row variable `Γ` binds
-- | and a metavariable is not one. And the decomposition is redone at each
-- | attempt, so the fact such an assumption is silent about appears once that
-- | tail is solved to a row with a rigid one.
module Test.Stella.Compiler.Elaborate.Context (spec) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.CorePlus.Context (FactsError(..), XContext, assume, emptyXContext, facts)
import Stella.Compiler.Elaborate.CorePlus.Kind (XKind(..))
import Stella.Compiler.Elaborate.CorePlus.Type (MetaVar, XConstraint(..), XRowEntry(..), XType(..))
import Stella.Compiler.Elaborate.Mechanism.Unify (MetaBinding(..), MetaContext, MetaInfo, emptyContext, freshMeta, substitute)
import Stella.Compiler.TypedCore (ModuleName(..), RowElemKind(..), RowKey(..), Symbol(..), TyName(..), TyVar(..), Qualified(..))
import Stella.Compiler.TypedCore.Entailment (AtomicFacts, noFacts)
import Data.Either (Either(..))
import Data.Foldable (foldl)
import Data.Map as Map
import Data.Set as Set
import Data.Tuple (Tuple(..), fst, snd)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

prim :: ModuleName
prim = ModuleName "Prim"

tA :: XType
tA = XCon (Qualified prim (TyName "A")) []

tB :: XType
tB = XCon (Qualified prim (TyName "B")) []

keyA :: RowKey
keyA = SymbolKey (Symbol "a")

keyB :: RowKey
keyB = SymbolKey (Symbol "b")

rigidR :: TyVar
rigidR = TyVar "r"

rigidS :: TyVar
rigidS = TyVar "s"

-- | `( l : τ | ρ )`
field :: RowKey -> XType -> XType -> XType
field key ty rest = XRowExtend (XRowTypeEntry key ty) rest

rowTypeInfo :: MetaInfo
rowTypeInfo =
  { kind: XKRow RowType
  , scope: { types: Set.fromFoldable [ rigidR, rigidS ], kinds: Set.empty, regions: Set.empty }
  }

-- | A context assuming what it is given, over no bindings: what `Γ*` is derived
-- | from is the assumptions alone.
assuming :: P.Array XConstraint -> XContext
assuming = foldl assume emptyXContext

-- | `?r`, and the context it is unsolved in.
flexibleTail :: Tuple MetaVar MetaContext
flexibleTail = freshMeta rowTypeInfo emptyContext

-- | The same metavariable, solved to a row whose tail is rigid.
solvedTo :: XType -> MetaContext
solvedTo ty =
  ctx { bindings = Map.insert m (Assigned ty) ctx.bindings }
  where
  m = fst flexibleTail
  ctx = snd flexibleTail

factsOf :: MetaContext -> XContext -> Either FactsError AtomicFacts
factsOf ctx = facts (substitute ctx)

spec :: Spec Unit
spec = describe "Elaborate.Context" do
  describe "Γ* is the rigid projection of what the site assumes" do
    it "derives nothing where nothing is assumed" do
      factsOf emptyContext (assuming [])
        `shouldEqual` Right noFacts

    it "derives k ∉ r from a Lacks whose tail is rigid" do
      factsOf emptyContext (assuming [ XLacks keyA (XVar rigidR) ])
        `shouldEqual` Right
          { lacks: Map.singleton rigidR (Set.singleton keyA)
          , disjoint: Set.empty
          }

    it "derives nothing from a Lacks whose tail is flexible" do
      factsOf (snd flexibleTail)
        (assuming [ XLacks keyA (XMeta (fst flexibleTail)) ])
        `shouldEqual` Right noFacts

    it "keeps the rigid part of an assumption whose other tail is flexible" do
      factsOf (snd flexibleTail)
        ( assuming
            [ XDisjoint (field keyA tA (XVar rigidR))
                (field keyB tB (XMeta (fst flexibleTail)))
            ]
        )
        `shouldEqual` Right
          { lacks: Map.singleton rigidR (Set.singleton keyB)
          , disjoint: Set.empty
          }

    it "derives the keys of each side against the rigid tail of the other" do
      factsOf emptyContext
        ( assuming
            [ XDisjoint (field keyA tA (XVar rigidR)) (field keyB tB (XVar rigidS)) ]
        )
        `shouldEqual` Right
          { lacks: Map.fromFoldable
              [ Tuple rigidR (Set.singleton keyB)
              , Tuple rigidS (Set.singleton keyA)
              ]
          , disjoint: Set.fromFoldable
              [ Tuple rigidR rigidS, Tuple rigidS rigidR ]
          }

    it "records a disjointness of two rigid tails in both directions" do
      factsOf emptyContext (assuming [ XDisjoint (XVar rigidR) (XVar rigidS) ])
        `shouldEqual` Right
          { lacks: Map.empty
          , disjoint: Set.fromFoldable [ Tuple rigidR rigidS, Tuple rigidS rigidR ]
          }

    it "rejects a Lacks the known part of its row contradicts" do
      factsOf emptyContext (assuming [ XLacks keyA (field keyA tA (XVar rigidR)) ])
        `shouldEqual` Left (LacksContradiction keyA)

    it "rejects a Disjoint whose two sides share a key" do
      factsOf emptyContext
        ( assuming
            [ XDisjoint (field keyA tA (XVar rigidR)) (field keyA tB (XVar rigidS)) ]
        )
        `shouldEqual` Left (DisjointContradiction keyA)

  describe "the assumptions are decomposed afresh at each attempt" do
    it "derives the fact once the flexible tail is solved to a rigid one" do
      factsOf (solvedTo (field keyB tB (XVar rigidS)))
        (assuming [ XLacks keyA (XMeta (fst flexibleTail)) ])
        `shouldEqual` Right
          { lacks: Map.singleton rigidS (Set.singleton keyA)
          , disjoint: Set.empty
          }

    it "rejects the same assumption where the solution carries the key" do
      factsOf (solvedTo (field keyA tA (XVar rigidS)))
        (assuming [ XLacks keyA (XMeta (fst flexibleTail)) ])
        `shouldEqual` Left (LacksContradiction keyA)
