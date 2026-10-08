-- | The constraints a substitution must preserve.
-- |
-- | Two things are what these cases are for. A constraint is decided against the
-- | facts of **the site it came from**, never those of the site the assignment
-- | happened at, and the pair of cases that differ only in which context an
-- | obligation carries is what holds that in place. And what it takes to hold
-- | depends on why it must: an assumption may not be made unsatisfiable, while a
-- | requirement must be proved of every rigid tail that enters it.
module Test.Stella.Compiler.Elaborate.Obligation (spec) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.CorePlus.Context (Origin(..), XContext, assume, emptyXContext, facts)
import Stella.Compiler.Elaborate.CorePlus.Kind (XKind(..))
import Stella.Compiler.Elaborate.Mechanism.Obligation (Breach(..), Basis(..), Obligation, ObligationId(..), ObligationStore, Standing(..), emptyStore, introduce, obligationOf, recheck, standing, touching, watchedBy)
import Stella.Compiler.Elaborate.CorePlus.Type (MetaVar, XConstraint(..), XRowEntry(..), XType(..))
import Stella.Compiler.Elaborate.Mechanism.Unify (MetaBinding(..), MetaContext, MetaInfo, emptyContext, freshMeta, substitute)
import Stella.Compiler.TypedCore (ModuleName(..), Qualified(..), RowElemKind(..), RowKey(..), Symbol(..), TyName(..), TyVar(..), Ident(..))
import Stella.Compiler.TypedCore.Entailment (AtomicFacts, noFacts)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldl)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Data.Tuple (Tuple(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

prim :: ModuleName
prim = ModuleName "Prim"

tA :: XType
tA = XCon (Qualified prim (TyName "A")) []

keyK :: RowKey
keyK = SymbolKey (Symbol "k")

keyA :: RowKey
keyA = SymbolKey (Symbol "a")

-- | Two rigid row variables. What holds of either is what a context gives.
rigidT :: TyVar
rigidT = TyVar "t"

rigidU :: TyVar
rigidU = TyVar "u"

here :: Origin
here = InDeclaration (Qualified prim (Ident "decl"))

-- | `( l : τ | ρ )`
field :: RowKey -> XType -> XType -> XType
field key ty rest = XRowExtend (XRowTypeEntry key ty) rest

rowTypeInfo :: MetaInfo
rowTypeInfo =
  { kind: XKRow RowType
  , scope: { types: Set.fromFoldable [ rigidT, rigidU ], kinds: Set.empty, regions: Set.empty }
  }

-- | `?r`, `?s`, and the context they are unsolved in.
metas :: { r :: MetaVar, s :: MetaVar, ctx :: MetaContext }
metas = { r, s, ctx: ctx2 }
  where
  Tuple r ctx1 = freshMeta rowTypeInfo emptyContext
  Tuple s ctx2 = freshMeta rowTypeInfo ctx1

-- | `Ψ` with the assignments given, which is what a zonk reads.
solving :: P.Array (Tuple MetaVar XType) -> MetaContext
solving assignments =
  metas.ctx
    { bindings = foldl record metas.ctx.bindings assignments }
  where
  record acc (Tuple m ty) = Map.insert m (Assigned ty) acc

assuming :: P.Array XConstraint -> XContext
assuming = foldl assume emptyXContext

-- | An obligation of the basis given, arising at the context given.
obligation :: Basis -> XContext -> XConstraint -> Obligation
obligation basis context constraint =
  { constraint, basis, context, origin: here }

-- | The store holding one obligation, and its identifier.
-- |
-- | Everything introduced this way mentions a metavariable that is unsolved, so
-- | it is watched rather than refused or settled; the other branch is what the
-- | cases on introduction below are about.
holding :: Obligation -> Tuple ObligationId ObligationStore
holding ob = holdingIn ob emptyStore

holdingIn :: Obligation -> ObligationStore -> Tuple ObligationId ObligationStore
holdingIn ob store = case introduce (substitute metas.ctx) ob store of
  Right (Tuple (Just id) store') -> Tuple id store'
  _ -> Tuple (ObligationId 0) store

factsOf :: MetaContext -> XContext -> AtomicFacts
factsOf ctx context = case facts (substitute ctx) context of
  Left _ -> noFacts
  Right derived -> derived

standingOf :: Basis -> AtomicFacts -> MetaContext -> XConstraint -> Either Breach Standing
standingOf basis sitefacts ctx = standing basis sitefacts (substitute ctx)

spec :: Spec Unit
spec = describe "Elaborate.Obligation" do
  describe "what is not yet known defers" do
    it "watches the metavariable of an unsolved tail" do
      standingOf Required noFacts metas.ctx (XLacks keyK (XMeta metas.r))
        `shouldEqual` Right (Watching (Set.singleton metas.r))

    it "watches both sides of a Disjoint between two flexible tails" do
      standingOf Required noFacts metas.ctx (XDisjoint (XMeta metas.r) (XMeta metas.s))
        `shouldEqual` Right (Watching (Set.fromFoldable [ metas.r, metas.s ]))

    it "is discharged where a solution leaves no metavariable in it" do
      standingOf Required noFacts (solving [ Tuple metas.r XRowEmpty ])
        (XLacks keyK (XMeta metas.r))
        `shouldEqual` Right Discharged

  describe "a solution that cannot satisfy it is refused whatever its basis" do
    it "refuses a solution carrying the key a Lacks forbids" do
      standingOf Required noFacts (solving [ Tuple metas.r (field keyK tA XRowEmpty) ])
        (XLacks keyK (XMeta metas.r))
        `shouldEqual` Left (SolutionCarriesKey keyK)

    it "refuses it where the constraint is one the site assumes" do
      standingOf Assumed noFacts (solving [ Tuple metas.r (field keyK tA XRowEmpty) ])
        (XLacks keyK (XMeta metas.r))
        `shouldEqual` Left (SolutionCarriesKey keyK)

    it "refuses a Disjoint whose two solutions share a key" do
      standingOf Required noFacts
        ( solving
            [ Tuple metas.r (field keyA tA XRowEmpty)
            , Tuple metas.s (field keyA tA XRowEmpty)
            ]
        )
        (XDisjoint (XMeta metas.r) (XMeta metas.s))
        `shouldEqual` Left (SidesShareKey keyA)

  describe "a rigid tail is proved where the basis requires it" do
    it "admits one the site's facts prove lacks the key" do
      standingOf Required (factsOf metas.ctx (assuming [ XLacks keyK (XVar rigidT) ]))
        (solving [ Tuple metas.r (XVar rigidT) ])
        (XLacks keyK (XMeta metas.r))
        `shouldEqual` Right Discharged

    it "refuses one nothing proves anything about" do
      standingOf Required noFacts (solving [ Tuple metas.r (XVar rigidT) ])
        (XLacks keyK (XMeta metas.r))
        `shouldEqual` Left (LacksUnprovenAtSite keyK rigidT)

    it "asks nothing of it where the constraint is one the site assumes" do
      standingOf Assumed noFacts (solving [ Tuple metas.r (XVar rigidT) ])
        (XLacks keyK (XMeta metas.r))
        `shouldEqual` Right Discharged

    it "refuses two rigid tails a Disjoint meets that nothing proves apart" do
      standingOf Required noFacts
        (solving [ Tuple metas.r (XVar rigidT), Tuple metas.s (XVar rigidU) ])
        (XDisjoint (XMeta metas.r) (XMeta metas.s))
        `shouldEqual` Left (DisjointUnprovenAtSite rigidT rigidU)

    it "refuses a known key the site cannot prove absent from the other's tail" do
      -- `?r # ?s` with `?r := ( a : A )` and `?s := t` needs `a ∉ t`
      standingOf Required noFacts
        (solving [ Tuple metas.r (field keyA tA XRowEmpty), Tuple metas.s (XVar rigidT) ])
        (XDisjoint (XMeta metas.r) (XMeta metas.s))
        `shouldEqual` Left (LacksUnprovenAtSite keyA rigidT)

    it "admits that key once the site proves it absent" do
      standingOf Required (factsOf metas.ctx (assuming [ XLacks keyA (XVar rigidT) ]))
        (solving [ Tuple metas.r (field keyA tA XRowEmpty), Tuple metas.s (XVar rigidT) ])
        (XDisjoint (XMeta metas.r) (XMeta metas.s))
        `shouldEqual` Right Discharged

    it "refuses a constraint whose metavariable is solved to something that is not a row" do
      -- The subject zonks to a type with no normal form. Only a row metavariable is
      -- named by a row constraint, so this is an invariant of the solver rather
      -- than a property of the program
      case
        standingOf Required noFacts (solving [ Tuple metas.r tA ])
          (XLacks keyK (XMeta metas.r))
        of
        Left (ObligationNotARow _) -> pure unit
        other -> show other `shouldEqual` "Left (ObligationNotARow …)"

    it "admits them where the site assumes the disjointness" do
      standingOf Required
        (factsOf metas.ctx (assuming [ XDisjoint (XVar rigidT) (XVar rigidU) ]))
        (solving [ Tuple metas.r (XVar rigidT), Tuple metas.s (XVar rigidU) ])
        (XDisjoint (XMeta metas.r) (XMeta metas.s))
        `shouldEqual` Right Discharged

  describe "an obligation is decided against the facts of its own site" do
    it "admits an assignment the site it came from proves" do
      let
        outer = assuming [ XLacks keyK (XVar rigidT) ]
        Tuple _ store = holding (obligation Required outer (XLacks keyK (XMeta metas.r)))
        assigned = solving [ Tuple metas.r (XVar rigidT) ]
      map (\s -> Map.isEmpty s.entries)
        (recheck (substitute assigned) (Set.singleton metas.r) store)
        `shouldEqual` Right true

    it "refuses the same assignment where that site does not prove it" do
      let
        elsewhere = assuming [ XLacks keyA (XVar rigidT) ]
        broken = obligation Required elsewhere (XLacks keyK (XMeta metas.r))
        Tuple _ store = holding broken
        assigned = solving [ Tuple metas.r (XVar rigidT) ]
      recheck (substitute assigned) (Set.singleton metas.r) store
        `shouldEqual` Left (Tuple broken (LacksUnprovenAtSite keyK rigidT))

  describe "nothing enters the store undecided" do
    it "refuses a closed requirement its site does not prove" do
      introduce (substitute metas.ctx)
        (obligation Required emptyXContext (XLacks keyK (XVar rigidT)))
        emptyStore
        `shouldEqual` Left (LacksUnprovenAtSite keyK rigidT)

    it "refuses an assumption that is already unsatisfiable" do
      introduce (substitute metas.ctx)
        (obligation Assumed emptyXContext (XLacks keyK (field keyK tA XRowEmpty)))
        emptyStore
        `shouldEqual` Left (SolutionCarriesKey keyK)

    it "keeps no entry for one that is settled where it is introduced" do
      map (\(Tuple id store) -> Tuple id (Map.isEmpty store.entries))
        ( introduce (substitute metas.ctx)
            ( obligation Required (assuming [ XLacks keyK (XVar rigidT) ])
                (XLacks keyK (field keyA tA (XVar rigidT)))
            )
            emptyStore
        )
        `shouldEqual` Right (Tuple Nothing true)

  describe "the index follows the constraint" do
    it "indexes an obligation under every metavariable it mentions" do
      let
        Tuple id store = holding
          (obligation Required emptyXContext (XDisjoint (XMeta metas.r) (XMeta metas.s)))
      touching metas.r store `shouldEqual` Set.singleton id
      touching metas.s store `shouldEqual` Set.singleton id
      watchedBy store id `shouldEqual` Set.fromFoldable [ metas.r, metas.s ]

    it "carries it to the tail a refinement introduced" do
      let
        Tuple id store = holding
          (obligation Required emptyXContext (XLacks keyK (XMeta metas.r)))
        Tuple fresh ctx = freshMeta rowTypeInfo metas.ctx
        assigned = ctx
          { bindings = Map.insert metas.r (Assigned (field keyA tA (XMeta fresh))) ctx.bindings }
      case recheck (substitute assigned) (Set.singleton metas.r) store of
        Left breach ->
          Left breach `shouldEqual` (Right unit :: Either (Tuple Obligation Breach) Unit)
        Right store' -> do
          touching fresh store' `shouldEqual` Set.singleton id
          touching metas.r store' `shouldEqual` Set.empty
          watchedBy store' id `shouldEqual` Set.singleton fresh

    it "stops holding one nothing can break again" do
      let
        Tuple id store = holding
          (obligation Required emptyXContext (XLacks keyK (XMeta metas.r)))
        assigned = solving [ Tuple metas.r XRowEmpty ]
      case recheck (substitute assigned) (Set.singleton metas.r) store of
        Left breach ->
          Left breach `shouldEqual` (Right unit :: Either (Tuple Obligation Breach) Unit)
        Right store' -> do
          obligationOf store' id `shouldEqual` Nothing
          touching metas.r store' `shouldEqual` Set.empty

    it "keeps watching the side an assignment did not reach" do
      let
        Tuple id store = holding
          (obligation Required emptyXContext (XDisjoint (XMeta metas.r) (XMeta metas.s)))
        assigned = solving [ Tuple metas.r XRowEmpty ]
      case recheck (substitute assigned) (Set.singleton metas.r) store of
        Left breach ->
          Left breach `shouldEqual` (Right unit :: Either (Tuple Obligation Breach) Unit)
        Right store' -> do
          watchedBy store' id `shouldEqual` Set.singleton metas.s
          touching metas.r store' `shouldEqual` Set.empty

    it "leaves an obligation no assignment reached alone" do
      let
        Tuple id store = holding
          (obligation Required emptyXContext (XLacks keyK (XMeta metas.s)))
        assigned = solving [ Tuple metas.r XRowEmpty ]
      map (\s -> watchedBy s id) (recheck (substitute assigned) (Set.singleton metas.r) store)
        `shouldEqual` Right (Set.singleton metas.s)

  describe "a store holding several" do
    it "reports the obligation that broke, and not the one that held" do
      let
        Tuple _ store1 = holdingIn (obligation Required emptyXContext (XLacks keyA (XMeta metas.s)))
          emptyStore
        broken = obligation Required emptyXContext (XLacks keyK (XMeta metas.r))
        Tuple _ store2 = holdingIn broken store1
        assigned = solving [ Tuple metas.r (field keyK tA XRowEmpty) ]
      recheck (substitute assigned) (Set.fromFoldable [ metas.r, metas.s ]) store2
        `shouldEqual` Left (Tuple broken (SolutionCarriesKey keyK))

    it "counts what remains after one is discharged" do
      let
        Tuple _ store1 = holdingIn (obligation Required emptyXContext (XLacks keyA (XMeta metas.s)))
          emptyStore
        Tuple _ store2 = holdingIn (obligation Required emptyXContext (XLacks keyK (XMeta metas.r)))
          store1
        assigned = solving [ Tuple metas.r XRowEmpty ]
      map (\s -> Array.length (Map.toUnfoldable s.entries :: P.Array _))
        (recheck (substitute assigned) (Set.singleton metas.r) store2)
        `shouldEqual` Right 1
