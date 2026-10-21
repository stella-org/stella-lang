-- | Row normalization, type equality, and entailment.
-- |
-- | The cases marked "(step 2)" in the regression catalogue of the
-- | Implementation Plan are covered here, together with the worked normal forms
-- | of the Rows document. Each is a case in which a plausible implementation
-- | gives the wrong answer.
module Test.Stella.Compiler.TypedCore.Row (spec) where

import Prelude

import Prim as P

import Stella.Compiler.TypedCore (Constraint(..), EffName(..), Kind(..), ModuleName(..), Qualified(..), RegionName(..), RowElemKind(..), RowEntry(..), RowError(..), RowKey(..), RowPayload(..), Symbol(..), Tag(..), TyName(..), TyVar(..), Type(..), compareRowKeys, constraintEquiv, decompose, entails, nfSharp, noFacts, typeEquiv)
import Stella.Compiler.TypedCore.Entailment (forget)
import Stella.Compiler.TypedCore.Type (substituteConstraint, substituteType)
import Data.Either (Either(..))
import Data.Map as Map
import Data.Set as Set
import Data.Tuple (Tuple(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

prim :: ModuleName
prim = ModuleName "Prim"

tInt :: Type
tInt = TCon (Qualified prim (TyName "Int")) []

tString :: Type
tString = TCon (Qualified prim (TyName "String")) []

tList :: Type
tList = TCon (Qualified prim (TyName "List")) []

name :: Symbol
name = Symbol "name"

age :: Symbol
age = Symbol "age"

cache :: Symbol
cache = Symbol "cache"

counter :: Symbol
counter = Symbol "counter"

-- | One spelling, used as both a `Symbol` and a `Tag`.
spelled :: P.String
spelled = "X"

consoleEff :: Qualified EffName
consoleEff = Qualified prim (EffName "Console")

stateEff :: Qualified EffName
stateEff = Qualified prim (EffName "State")

readerEff :: Qualified EffName
readerEff = Qualified prim (EffName "Reader")

r :: TyVar
r = TyVar "r"

s :: TyVar
s = TyVar "s"

e :: TyVar
e = TyVar "e"

-- | `( l : τ | ρ )`
field :: Symbol -> Type -> Type -> Type
field l ty rest = TRowExtend (RowTypeEntry (SymbolKey l) ty) rest

-- | `( E τ̄ | ρ )`
effect :: Qualified EffName -> P.Array Type -> Type -> Type
effect eff args rest = TRowExtend (RowEffectEntry eff args) rest

-- | `( s : E τ̄ | ρ )`
labelledEffect :: Symbol -> Qualified EffName -> P.Array Type -> Type -> Type
labelledEffect s' eff args rest = TRowExtend (RowLabelledEffectEntry s' eff args) rest

-- | `( TagKey t : τ | ρ )`
variant :: Tag -> Type -> Type -> Type
variant t ty rest = TRowExtend (RowTypeEntry (TagKey t) ty) rest

-- | `( PositionKey n : τ | ρ )`
component :: P.Int -> Type -> Type -> Type
component n ty rest = TRowExtend (RowTypeEntry (PositionKey n) ty) rest

closed :: Symbol -> Type -> Type
closed l ty = field l ty TRowEmpty

spec :: Spec Unit
spec = describe "Stella.Compiler.TypedCore.Row" do
  describe "normalization" do
    it "collects known fields and leaves the tail open" do
      -- nf( ( name : String | r ) ⊎ ( age : Int ) )
      nfSharp (TRowUnion (field name tString (TVar r)) (closed age tInt)) `shouldEqual`
        Right
          { known: Map.fromFoldable
              [ Tuple (SymbolKey name) (TypePayload tString)
              , Tuple (SymbolKey age) (TypePayload tInt)
              ]
          , tail: Set.singleton r
          }

    it "derives an effect key from the head constructor, with the arguments as payload" do
      -- nf( ( Console | e ) ⊎ ( State Int ) )
      nfSharp (TRowUnion (effect consoleEff [] (TVar e)) (effect stateEff [ tInt ] TRowEmpty)) `shouldEqual`
        Right
          { known: Map.fromFoldable
              [ Tuple (EffectKey consoleEff) (EffectPayload consoleEff [])
              , Tuple (EffectKey stateEff) (EffectPayload stateEff [ tInt ])
              ]
          , tail: Set.singleton e
          }

    it "rejects two payloads at one key, which sharpness forbids" do
      nfSharp (field name tString (closed name tInt)) `shouldEqual` Left (DuplicateKey (SymbolKey name))

    it "projects equal payloads at one key to one, as canonical equality does" do
      nfSharp (TRowUnion (closed name tInt) (closed name tInt)) `shouldEqual`
        Right { known: Map.singleton (SymbolKey name) (TypePayload tInt), tail: Set.empty }

    it "absorbs a repeated row variable, leaving `r # r` to reject it" do
      -- `r ⊎ r` normalizes; what rejects it is the disjointness side condition
      nfSharp (TRowUnion (TVar r) (TVar r)) `shouldEqual`
        Right { known: Map.empty, tail: Set.singleton r }

  describe "keys" do
    it "are ordered by kind, and within one by spelling, number, or qualified name" do
      -- a kind decides first, so a field stands before a tag whatever the spellings
      compareRowKeys (SymbolKey (Symbol "z")) (TagKey (Tag "a")) `shouldEqual` LT
      compareRowKeys (TagKey (Tag "z")) (PositionKey 0) `shouldEqual` LT
      compareRowKeys (PositionKey 9) (EffectKey (Qualified (ModuleName "A") (EffName "E"))) `shouldEqual` LT
      compareRowKeys (EffectKey (Qualified (ModuleName "Z") (EffName "Z"))) (RegionKey (RegionName "a")) `shouldEqual` LT
      compareRowKeys (PositionKey 2) (PositionKey 10) `shouldEqual` LT
      -- an effect by its module's name first, then its own
      compareRowKeys (EffectKey (Qualified (ModuleName "A") (EffName "Z"))) (EffectKey (Qualified (ModuleName "B") (EffName "A"))) `shouldEqual` LT
      compareRowKeys (EffectKey (Qualified (ModuleName "A") (EffName "E"))) (EffectKey (Qualified (ModuleName "A") (EffName "F"))) `shouldEqual` LT
      compareRowKeys (RegionKey (RegionName "r1")) (RegionKey (RegionName "r2")) `shouldEqual` LT
      compareRowKeys (SymbolKey (Symbol "a")) (SymbolKey (Symbol "a")) `shouldEqual` EQ

    it "compare a spelling by scalar value, not by the code units a host holds it in" do
      -- `U+E000` stands below an astral character by scalar value, and above it by
      -- code unit
      compareRowKeys (SymbolKey (Symbol "\xE000")) (SymbolKey (Symbol "\x1F600")) `shouldEqual` LT
      compareRowKeys (TagKey (Tag "\xE000")) (TagKey (Tag "\x1F600")) `shouldEqual` LT

    it "separates a Symbol from a Tag of the same spelling" do
      -- `( SymbolKey X : Int, TagKey X : Int )`: one spelling, two keys
      nfSharp (field (Symbol spelled) tInt (variant (Tag spelled) tInt TRowEmpty)) `shouldEqual`
        Right
          { known: Map.fromFoldable
              [ Tuple (SymbolKey (Symbol spelled)) (TypePayload tInt)
              , Tuple (TagKey (Tag spelled)) (TypePayload tInt)
              ]
          , tail: Set.empty
          }

    it "keys a tuple by position" do
      nfSharp (component 0 tInt (component 1 tString TRowEmpty)) `shouldEqual`
        Right
          { known: Map.fromFoldable
              [ Tuple (PositionKey 0) (TypePayload tInt)
              , Tuple (PositionKey 1) (TypePayload tString)
              ]
          , tail: Set.empty
          }

    it "admits one effect twice where the keys are written" do
      -- `( cache : State Int, counter : State Int )`
      nfSharp (labelledEffect cache stateEff [ tInt ] (labelledEffect counter stateEff [ tInt ] TRowEmpty))
        `shouldEqual`
          Right
            { known: Map.fromFoldable
                [ Tuple (SymbolKey cache) (EffectPayload stateEff [ tInt ])
                , Tuple (SymbolKey counter) (EffectPayload stateEff [ tInt ])
                ]
            , tail: Set.empty
            }

    it "rejects a written key twice, whatever the payloads" do
      nfSharp (labelledEffect cache stateEff [ tInt ] (labelledEffect cache stateEff [ tString ] TRowEmpty))
        `shouldEqual` Left (DuplicateKey (SymbolKey cache))

    it "rejects one effect twice where no key is written" do
      -- Both elements derive `EffectKey State`
      nfSharp (effect stateEff [ tInt ] (effect stateEff [ tString ] TRowEmpty))
        `shouldEqual` Left (DuplicateKey (EffectKey stateEff))

    it "compares the payload, which a written key leaves free" do
      -- The key selects the element; the payload decides the protocol, so two
      -- elements can agree on the key and still carry different effects
      typeEquiv
        (labelledEffect cache stateEff [ tInt ] TRowEmpty)
        (labelledEffect cache readerEff [ tInt ] TRowEmpty)
        `shouldEqual` false

  describe "equality" do
    it "ignores the order in which fields were written" do
      typeEquiv
        (TRowUnion (field name tString (TVar r)) (closed age tInt))
        (field age tInt (field name tString (TVar r)))
        `shouldEqual` true

    it "treats the tail as a set" do
      -- ⟨∅;{r,s}⟩ ≡ ⟨∅;{s,r}⟩
      typeEquiv (TRowUnion (TVar r) (TVar s)) (TRowUnion (TVar s) (TVar r))
        `shouldEqual` true

    it "does not identify distinct row variables" do
      -- ( name : String | r ) and ( name : String | s ) are different rows
      typeEquiv (field name tString (TVar r)) (field name tString (TVar s))
        `shouldEqual` false

    it "distinguishes a closed row from an open one" do
      typeEquiv (closed name tString) (field name tString (TVar r))
        `shouldEqual` false

    it "compares payloads" do
      typeEquiv (closed name tString) (closed name tInt) `shouldEqual` false

    it "identifies types that differ only in the names they bind" do
      typeEquiv
        (TForall r (KRow RowType) (field name tString (TVar r)))
        (TForall s (KRow RowType) (field name tString (TVar s)))
        `shouldEqual` true

    it "keeps a bound variable distinct from a free one of the same name" do
      typeEquiv
        (TForall r (KRow RowType) (TVar r))
        (TForall s (KRow RowType) (TVar r))
        `shouldEqual` false

    it "separates binders of different kinds" do
      typeEquiv
        (TForall r (KRow RowType) tInt)
        (TForall r (KRow RowEffect) tInt)
        `shouldEqual` false

    it "is total, answering a row against a type that is no row" do
      typeEquiv TRowEmpty tInt `shouldEqual` false
      -- A type that is no row stands in a tail as an opaque tail
      typeEquiv (field name tInt tInt) (TRowUnion tInt (closed name tInt)) `shouldEqual` true

    it "treats a row as a set of entries, so a repeated entry is one" do
      -- `( x : Int ) ⊎ ( x : Int ) ≡ ( x : Int )`, the form `r ⊎ r ≡ r` takes
      -- once `( x : Int )` is substituted for `r`
      typeEquiv (TRowUnion (closed name tInt) (closed name tInt)) (closed name tInt) `shouldEqual` true
      typeEquiv (TRowUnion (TVar r) (TVar r)) (TVar r) `shouldEqual` true

    it "keeps two payloads at one key apart rather than leaving the row without a form" do
      let both = TRowUnion (closed name tInt) (closed name tString)
      typeEquiv both (closed name tInt) `shouldEqual` false
      typeEquiv both (closed name tString) `shouldEqual` false
      typeEquiv both (TRowUnion (closed name tString) (closed name tInt)) `shouldEqual` true

    it "takes a row of no entries and one tail to be its tail" do
      typeEquiv (TRowUnion (TVar r) TRowEmpty) (TVar r) `shouldEqual` true
      typeEquiv (TRowUnion TRowEmpty (TVar r)) (TVar r) `shouldEqual` true

    it "stays equal under substitution, whatever is substituted" do
      let
        sub = Map.singleton r (closed name tInt)
        left = TRowUnion (TVar r) (TVar r)
      typeEquiv left (TVar r) `shouldEqual` true
      typeEquiv (substituteType sub left) (substituteType sub (TVar r)) `shouldEqual` true

    it "compares the payload of a labelled effect under its key" do
      typeEquiv
        (TRowUnion (labelledEffect cache stateEff [ tInt ] TRowEmpty) (labelledEffect cache stateEff [ tInt ] TRowEmpty))
        (labelledEffect cache stateEff [ tInt ] TRowEmpty)
        `shouldEqual` true

    it "compares a constraint structurally, so `#` is not symmetric here" do
      -- `r # s` and `s # r` entail each other, but definitional equality is
      -- structural: adapting one to the other is `Λ (_ : s # r). e [•]`
      constraintEquiv (Disjoint (TVar r) (TVar s)) (Disjoint (TVar s) (TVar r))
        `shouldEqual` false
      constraintEquiv (Disjoint (TVar r) (TVar s)) (Disjoint (TVar r) (TVar s))
        `shouldEqual` true

  describe "entailment" do
    it "holds of the empty row without any assumption" do
      entails noFacts (Lacks (SymbolKey name) TRowEmpty) `shouldEqual` true
      entails noFacts (Disjoint (TVar r) TRowEmpty) `shouldEqual` true

    it "fails on a known key in a consistent context" do
      entails noFacts (Lacks (SymbolKey name) (closed name tString)) `shouldEqual` false

    it "needs an assumption to see past an unknown tail" do
      entails noFacts (Lacks (SymbolKey name) (TVar r)) `shouldEqual` false
      entails (decompose [ Lacks (SymbolKey name) (TVar r) ]) (Lacks (SymbolKey name) (TVar r))
        `shouldEqual` true

    it "decomposes an assumption over a composite row" do
      -- `name ∉ ( age : Int | r )` yields the atomic fact `name ∉ r`
      entails (decompose [ Lacks (SymbolKey name) (field age tInt (TVar r)) ]) (Lacks (SymbolKey name) (TVar r))
        `shouldEqual` true

    it "derives the lacks facts a disjointness assumption implies" do
      -- `( name : String | r ) # s` yields `name ∉ s` and `r # s`
      let facts = decompose [ Disjoint (field name tString (TVar r)) (TVar s) ]
      entails facts (Lacks (SymbolKey name) (TVar s)) `shouldEqual` true
      entails facts (Disjoint (TVar r) (TVar s)) `shouldEqual` true

    it "closes `#` under symmetry, and nothing else" do
      let facts = decompose [ Disjoint (TVar r) (TVar s) ]
      entails facts (Disjoint (TVar s) (TVar r)) `shouldEqual` true
      entails facts (Disjoint (TVar r) (TVar e)) `shouldEqual` false

    it "does not derive `r # r` from nothing, which is what makes `r ⊎ r` ill-kinded" do
      entails noFacts (Disjoint (TVar r) (TVar r)) `shouldEqual` false
      entails (decompose [ Disjoint (TVar r) (TVar s) ]) (Disjoint (TVar r) (TVar r)) `shouldEqual` false

    it "derives `r # r` where it is assumed, since an assumption entails itself" do
      -- `r # r` is satisfiable: it constrains `r` to the empty row
      entails (decompose [ Disjoint (TVar r) (TVar r) ]) (Disjoint (TVar r) (TVar r)) `shouldEqual` true

    it "stops at `r # r` and does not pursue what it implies" do
      -- Entailment is sound for the set-theoretic reading of rows and
      -- intentionally incomplete: `r` being empty is a consequence the relation
      -- does not carry, and a solver that grew helpful here would lose that.
      -- `r # r` is no inconsistency either, being satisfiable
      let facts = decompose [ Disjoint (TVar r) (TVar r) ]
      entails facts (Lacks (SymbolKey name) (TVar r)) `shouldEqual` false
      entails facts (Disjoint (TVar r) (TVar s)) `shouldEqual` false

    it "keeps assumptions about one variable together" do
      let facts = decompose [ Lacks (SymbolKey name) (TVar r), Lacks (SymbolKey age) (TVar r) ]
      entails facts (Lacks (SymbolKey name) (TVar r)) `shouldEqual` true
      entails facts (Lacks (SymbolKey age) (TVar r)) `shouldEqual` true

    it "decides an effect row by the same rules" do
      let facts = decompose [ Lacks (EffectKey consoleEff) (TVar e) ]
      entails facts (Lacks (EffectKey consoleEff) (TVar e)) `shouldEqual` true
      entails facts (Lacks (EffectKey stateEff) (TVar e)) `shouldEqual` false

    it "asks of an opaque tail a fact only an assumption about it gives" do
      entails noFacts (Lacks (SymbolKey name) (field age tInt tInt)) `shouldEqual` false
      entails (decompose [ Lacks (SymbolKey name) (field age tString tInt) ]) (Lacks (SymbolKey name) tInt)
        `shouldEqual` true

    it "keeps what is entailed when a type that is no row is substituted for a tail" do
      -- `k ∉ r ⊨ k ∉ r`, and `[r ↦ Int]` makes it `k ∉ Int ⊨ k ∉ Int`
      let sub = Map.singleton r tInt
      let lacks = Lacks (SymbolKey name) (TVar r)
      let apart = Disjoint (TVar r) (TVar s)
      entails (decompose [ substituteConstraint sub lacks ]) (substituteConstraint sub lacks)
        `shouldEqual` true
      entails (decompose [ substituteConstraint sub apart ]) (substituteConstraint sub (Disjoint (TVar s) (TVar r)))
        `shouldEqual` true
      entails (decompose [ substituteConstraint sub (Lacks (SymbolKey name) (field age tString (TVar r))) ])
        (substituteConstraint sub lacks)
        `shouldEqual` true

    it "forgets what was assumed of an opaque tail its variable's binder hides" do
      let facts = decompose [ Lacks (SymbolKey name) (TApp tList (TVar r)), Lacks (SymbolKey name) (TVar s) ]
      entails (forget r facts) (Lacks (SymbolKey name) (TApp tList (TVar r))) `shouldEqual` false
      entails (forget r facts) (Lacks (SymbolKey name) (TVar s)) `shouldEqual` true

  describe "an inconsistent context" do
    it "entails every constraint where an assumption contradicts a known key" do
      -- `Γ, name ∉ ( name : Int ) ⊨ C` for every `C`
      let facts = decompose [ Lacks (SymbolKey name) (closed name tInt) ]
      entails facts (Lacks (SymbolKey name) (closed name tString)) `shouldEqual` true
      entails facts (Lacks (SymbolKey age) (TVar r)) `shouldEqual` true
      entails facts (Disjoint (TVar r) (TVar r)) `shouldEqual` true
      entails facts (Disjoint (closed name tInt) (closed name tInt)) `shouldEqual` true

    it "is reached by a disjointness whose sides share a known key" do
      let facts = decompose [ Disjoint (closed name tString) (field name tInt (TVar r)) ]
      entails facts (Lacks (SymbolKey age) (TVar s)) `shouldEqual` true

    it "is not reached by `r # r` or by a repeated key under no assumption" do
      entails (decompose [ Disjoint (TVar r) (TVar r) ]) (Lacks (SymbolKey age) (TVar s)) `shouldEqual` false
      entails (decompose [ Lacks (SymbolKey name) (TVar r) ]) (Lacks (SymbolKey age) (TVar r)) `shouldEqual` false

    it "is reached by an assumption a substitution makes false" do
      -- `name ∉ r` assumed, then `( name : Int )` substituted for `r`, which a
      -- type application of a constraint abstraction may do
      let assumed = Lacks (SymbolKey name) (TVar r)
      let substituted = decompose [ substituteConstraint (Map.singleton r (closed name tInt)) assumed ]
      entails substituted (Lacks (SymbolKey age) (TVar s)) `shouldEqual` true
