-- | The level a metavariable stands at, and a binding group's generalization
-- | prepared and finalized into a plan, over hand-built states.
module Test.Stella.Compiler.Elaborate.Generalize (spec) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Either (Either(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Data.Tuple (Tuple(..))
import Effect.Aff (Aff)
import Stella.Compiler.Elaborate.CorePlus.Context (Origin(..), bindTyVar, emptyXContext)
import Stella.Compiler.Elaborate.CorePlus.Kind (KindMetaVar(..), XKind(..), kindMetasOf)
import Stella.Compiler.Elaborate.CorePlus.Term (FitId(..), XExpr(..))
import Stella.Compiler.Elaborate.CorePlus.Type (MetaVar(..), XConstraint(..), XRowEntry(..), XType(..), metasOf)
import Stella.Compiler.Elaborate.Driver.Attempt (Attempt(Committed), attemptPending, attemptPendingWith, runAttempt)
import Stella.Compiler.Elaborate.Driver.Generalize (Commitment(..), Finalization(..), GeneralizationDraft, Hindrance(..), Member, Preparation(..), commitGeneralization, finalizeGeneralization, prepareGeneralization)
import Stella.Compiler.Elaborate.Driver.Loop (RunResult(..), run)
import Stella.Compiler.Elaborate.Driver.Resolve (resolveByDirection)
import Stella.Compiler.Elaborate.Driver.Synthesis (Registry, attemptJob)
import Stella.Compiler.Elaborate.Environment.Catalog (catalogOf)
import Stella.Compiler.Elaborate.Environment.Constructors (emptyConstructorEnv)
import Stella.Compiler.Elaborate.Environment.Effects (emptyEffectEnv)
import Stella.Compiler.Elaborate.Kernel.Elab (Elab, Outcome(..), SessionEnv, SolverState, assignTerm, atLevel, closeBoundary, createSynthesis, equate, equateKinds, freshKindMeta, freshTermMeta, freshTypeMeta, initialState, openBoundary, placeFit, recursiveRef, require)
import Stella.Compiler.Elaborate.Mechanism.Fit (FitState(..), FitUse(..))
import Stella.Compiler.Elaborate.Mechanism.Kinding (kindingOf)
import Stella.Compiler.Elaborate.Mechanism.Obligation (Basis(..), ResidualAtom(..), residualAtoms)
import Stella.Compiler.Elaborate.Mechanism.Pending (Job(..), Site)
import Stella.Compiler.Elaborate.Mechanism.Scheduler (create, lookupPending, reblock, takeReady)
import Stella.Compiler.Elaborate.Mechanism.Unify (KindMetaBinding(..), KindRequirement(..), MetaBinding(..), lookupMeta, regionScopeOf, substitute, substituteKind)
import Stella.Compiler.Elaborate.Protocol.Facade (Synthesizer)
import Stella.Compiler.Elaborate.Protocol.Facade as F
import Stella.Compiler.Elaborate.Surface.Type (xFunction)
import Stella.Compiler.Elaborate.Vocabulary.Diagnostic (Defect(..))
import Stella.Compiler.Elaborate.Vocabulary.Handle (SessionId(..))
import Stella.Compiler.Elaborate.Vocabulary.Message (MessagePart(..))
import Stella.Compiler.Elaborate.Vocabulary.Trace (Tracing(..))
import Stella.Compiler.Elaborate.Vocabulary.View (TypeView(..))
import Stella.Compiler.TypedCore (Ident(..), Literal(..), ModuleName(..), Qualified(..))
import Stella.Compiler.TypedCore.Kind (RowElemKind(..))
import Stella.Compiler.TypedCore.Name (EffName(..), KindVar(..), RegionName(..), Symbol(..), TyName(..), TyVar(..))
import Stella.Compiler.TypedCore.Prim (intTy, primSignature, recordTy)
import Stella.Compiler.TypedCore.Type (RowKey(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

session :: SessionEnv
session =
  { catalog: catalogOf []
  , kinding: kindingOf primSignature
  , constructors: emptyConstructorEnv
  , effects: emptyEffectEnv
  , tracing: TraceDisabled
  }

decl :: P.String -> Qualified Ident
decl n = Qualified (ModuleName "M") (Ident n)

f :: Qualified Ident
f = decl "f"

siteIn :: Qualified Ident -> Site
siteIn name = { context: emptyXContext, origin: InDeclaration name }

ownerOf :: Origin -> Qualified Ident
ownerOf = case _ of
  InDeclaration name -> name
  AtSource o -> o.declaration

int :: XType
int = XCon intTy []

pure' :: XType -> XType -> XType
pure' a b = xFunction a XRowEmpty b

body :: XExpr Unit
body = ELit unit (LitInt 1)

start :: SolverState
start = initialState (SessionId 0) 100

-- | Answers `1`.
answerOne :: Synthesizer
answerOne _ = F.rootScope >>= \root -> F.literal root (LitInt 1)

-- | Waits on the goal's type while it is a metavariable.
patient :: Synthesizer
patient goal = F.goalType goal >>= F.viewType >>= case _ of
  MetaType m -> F.postpone [ m ]
  _ -> answerOne goal

refusing :: Synthesizer
refusing _ = F.throw [ TextPart "no" ]

-- | Warns, and answers `1`.
warning :: Synthesizer
warning goal = F.warn [ TextPart "w" ] *> answerOne goal

registry :: Registry
registry = Map.fromFoldable [ Tuple (decl "one") answerOne, Tuple (decl "warning") warning, Tuple (decl "patient") patient, Tuple (decl "refusing") refusing ]

-- | The group's elaboration, at level 1, as an attempt.
inGroup :: forall a. Elab a -> (a -> SolverState -> Aff Unit) -> Aff Unit
inGroup action k = case runAttempt session (atLevel 1 action) start of
  Tuple (Done a) s -> k a s
  Tuple (Failed d) _ -> fail ("the group did not elaborate: " <> show d)
  Tuple _ _ -> fail "the group did not elaborate"

levelOf :: SolverState -> MetaVar -> Maybe P.Int
levelOf s m = case lookupMeta s.tentative.metas m of
  Just (Unsolved info) -> Just info.level
  _ -> Nothing

kindLevelOf :: SolverState -> KindMetaVar -> Maybe P.Int
kindLevelOf s k = case Map.lookup k s.tentative.metas.kindBindings of
  Just (KindUnsolved info) -> Just info.level
  _ -> Nothing

metaOf :: XType -> MetaVar
metaOf = case _ of
  XMeta m -> m
  _ -> MetaVar (-1)

kindMetaOf :: XKind -> KindMetaVar
kindMetaOf = case _ of
  XKMeta k -> k
  _ -> KindMetaVar (-1)

-- | The group the action elaborates, its members prepared, finalized, and
-- | committed.
committing :: forall r. Elab r -> (r -> P.Array (Member (Qualified Ident) Unit)) -> (r -> Commitment (Qualified Ident) Unit -> SolverState -> Aff Unit) -> Aff Unit
committing action members k = inGroup action \r s -> case prepareGeneralization (attemptJob session registry) ownerOf 1 (members r) s of
  Tuple { preparation: Drafted draft } s1 -> case finalizeGeneralization ownerOf draft (members r) s1 of
    Tuple (Planned plan) s2 -> case commitGeneralization ownerOf plan (members r) s2 of
      Tuple outcome s3 -> k r outcome s3
    Tuple other _ -> fail ("not planned: " <> show other)
  Tuple other _ -> fail ("not drafted: " <> show other.preparation)

-- | That the terms are the ones given; a term has no `Show` to report them by.
sameTerms :: P.Array (XExpr Unit) -> P.Array (XExpr Unit) -> Aff Unit
sameTerms actual expected = (actual == expected) `shouldEqual` true

-- | Whether `Ψ` no longer holds the metavariable.
isRetired :: SolverState -> MetaVar -> P.Boolean
isRetired s m = case lookupMeta s.tentative.metas m of
  Nothing -> true
  Just _ -> false

-- | The group the action elaborates, its members prepared and finalized.
prepared :: forall r. Elab r -> { members :: r -> P.Array (Member (Qualified Ident) Unit), then :: r -> GeneralizationDraft (Qualified Ident) -> Finalization (Qualified Ident) -> Aff Unit } -> Aff Unit
prepared action k = inGroup action \r s -> case prepareGeneralization (attemptJob session registry) ownerOf 1 (k.members r) s of
  Tuple { preparation: Drafted draft } s' -> case finalizeGeneralization ownerOf draft (k.members r) s' of
    Tuple outcome _ -> k.then r draft outcome
  Tuple other _ -> fail ("not drafted: " <> show other.preparation)

spec :: Spec Unit
spec = describe "Stella.Compiler.Elaborate.Driver.Generalize" do
  describe "a metavariable's level" do
    it "is the level it is created at, 0 outside every group" do
      case runAttempt session ((\a b k -> { a, b, k }) <$> freshTypeMeta emptyXContext XKType <*> atLevel 2 (freshTypeMeta emptyXContext XKType) <*> atLevel 3 (freshKindMeta Set.empty Set.empty)) start of
        Tuple (Done r) s -> do
          levelOf s (metaOf r.a) `shouldEqual` Just 0
          levelOf s (metaOf r.b) `shouldEqual` Just 2
          kindLevelOf s (kindMetaOf r.k) `shouldEqual` Just 3
        _ -> fail "not created"

    it "is lowered by an assignment to what its solution holds, the kinds it stands at among them" do
      case
        runAttempt session
          ( do
              a <- atLevel 1 (freshTypeMeta emptyXContext XKType)
              k <- atLevel 2 (freshKindMeta Set.empty Set.empty)
              g <- atLevel 2 (freshTypeMeta emptyXContext (XKFun k XKType))
              x <- atLevel 2 (freshTypeMeta emptyXContext k)
              equate (siteIn f) { kind: XKType, left: a, right: XApp g x }
              pure { g, x, k }
          )
          start
        of
        Tuple (Done r) s -> do
          levelOf s (metaOf r.g) `shouldEqual` Just 1
          levelOf s (metaOf r.x) `shouldEqual` Just 1
          kindLevelOf s (kindMetaOf r.k) `shouldEqual` Just 1
        _ -> fail "not equated"

    it "of the fresh tail two flexible tails are refined to is the lower of theirs" do
      let
        field n = XRowTypeEntry (SymbolKey (Symbol n)) int
        rowType = XKRow RowType
      case
        runAttempt session
          ( do
              r <- atLevel 1 (freshTypeMeta emptyXContext rowType)
              s' <- atLevel 2 (freshTypeMeta emptyXContext rowType)
              equate (siteIn f) { kind: rowType, left: XRowExtend (field "a") r, right: XRowExtend (field "b") s' }
              pure r
          )
          start
        of
        -- the one metavariable of what `r` is solved to is the fresh tail
        Tuple (Done r) s -> case Set.toUnfoldable (metasOf (substitute s.tentative.metas r)) of
          [ t ] | t /= metaOf r -> levelOf s t `shouldEqual` Just 1
          other -> fail ("not refined: " <> show other)
        _ -> fail "not equated"

    it "of a job's attempt is the level it was created at, whenever it is attempted" do
      case runAttempt session (atLevel 2 (createSynthesis (siteIn f) int (decl "one"))) start of
        Tuple (Done _) s -> case takeReady s.tentative.scheduler of
          Just (Tuple id scheduler) ->
            case attemptPendingWith session (\_ -> void (freshTypeMeta emptyXContext XKType)) id (s { tentative { scheduler = scheduler } }) of
              Tuple Committed after -> levelOf after (MetaVar (after.tentative.metas.next - 1)) `shouldEqual` Just 2
              Tuple other _ -> fail ("not committed: " <> show other)
          Nothing -> fail "no job"
        _ -> fail "not created"

  describe "a group's generalization" do
    let
      member type' = { key: f, name: f, type: type', body, valueForm: true, written: false }

    it "quantifies the candidates of each member's type where each first stands, named apart from what the type writes" do
      prepared
        ( do
            a <- freshTypeMeta emptyXContext XKType
            b <- freshTypeMeta emptyXContext XKType
            z <- atLevel 0 (freshTypeMeta emptyXContext XKType)
            pure { a, b, z }
        )
        { members: \r -> [ member (pure' r.a (pure' (XVar (TyVar "a")) (pure' r.b (pure' r.z r.a)))) ]
        , then: \r _ outcome -> outcome `shouldEqual` Planned
            { level: 1
            , members:
                [ { key: f
                  , kindVars: []
                  , quantifiers: [ { meta: metaOf r.a, name: TyVar "b", kind: XKType }, { meta: metaOf r.b, name: TyVar "c", kind: XKType } ]
                  }
                ]
            }
        }

    it "decides the kind variables first, a quantifier's kind holding them" do
      prepared
        ( do
            k <- freshKindMeta Set.empty Set.empty
            g <- freshTypeMeta emptyXContext (XKFun k XKType)
            x <- freshTypeMeta emptyXContext k
            pure { k, g, x }
        )
        { members: \r -> [ member (pure' (XApp r.g r.x) int) ]
        , then: \r _ outcome -> outcome `shouldEqual` Planned
            { level: 1
            , members:
                [ { key: f
                  , kindVars: [ { meta: kindMetaOf r.k, name: KindVar "k" } ]
                  , quantifiers: [ { meta: metaOf r.g, name: TyVar "a", kind: XKFun r.k XKType }, { meta: metaOf r.x, name: TyVar "b", kind: r.k } ]
                  }
                ]
            }
        }

    it "refuses a kind candidate that must produce `Type`, which no kind variable is" do
      prepared
        ( do
            k <- freshKindMeta Set.empty (Set.singleton ProducesType)
            x <- freshTypeMeta emptyXContext k
            pure { k, x }
        )
        { members: \r -> [ member (pure' r.x int) ]
        , then: \r _ outcome -> outcome `shouldEqual` FinalizationHindered [ KindNotQuantifiable f (kindMetaOf r.k) ]
        }

    it "asks of a candidate its body alone reaches an annotation" do
      prepared ((\a c -> { a, c }) <$> freshTypeMeta emptyXContext XKType <*> freshTypeMeta emptyXContext XKType)
        { members: \r -> [ { key: f, name: f, type: pure' r.a r.a, body: ELam unit (Ident "y") r.c (EVar unit (Ident "y")), valueForm: true, written: false } ]
        , then: \r _ outcome -> outcome `shouldEqual` FinalizationHindered [ AmbiguousCandidates f [ metaOf r.c ] ]
        }

  describe "the value restriction" do

    it "reaches the kinds a body writes, restricting them where it is no value form, ambiguous where its type does not reach them, and names apart from them" do
      inGroup ((\k a -> { k, a }) <$> freshKindMeta Set.empty Set.empty <*> freshTypeMeta emptyXContext XKType) \r s -> do
        let
          writing = EGlobal unit (decl "h") [ r.k ]
        case prepareGeneralization (attemptJob session registry) ownerOf 1 [ { key: f, name: f, type: pure' r.a r.a, body: writing, valueForm: false, written: false } ] s of
          Tuple { preparation: Drafted draft } _ -> map _.kinds draft.restricted `shouldEqual` [ Set.singleton (kindMetaOf r.k) ]
          Tuple other _ -> fail ("not drafted: " <> show other.preparation)
        case prepareGeneralization (attemptJob session registry) ownerOf 1 [ { key: f, name: f, type: pure' r.a r.a, body: writing, valueForm: true, written: false } ] s of
          Tuple { preparation: Drafted draft } s' -> case finalizeGeneralization ownerOf draft [ { key: f, name: f, type: pure' r.a r.a, body: writing, valueForm: true, written: false } ] s' of
            Tuple outcome _ -> outcome `shouldEqual` FinalizationHindered [ AmbiguousKindCandidates f [ kindMetaOf r.k ] ]
          Tuple other _ -> fail ("not drafted: " <> show other.preparation)
      prepared
        ( do
            k <- freshKindMeta Set.empty Set.empty
            g <- freshTypeMeta emptyXContext (XKFun k XKType)
            x <- freshTypeMeta emptyXContext k
            pure { k, g, x }
        )
        { members: \r -> [ { key: f, name: f, type: pure' (XApp r.g r.x) int, body: EGlobal unit (decl "h") [ XKVar (KindVar "k") ], valueForm: true, written: false } ]
        , then: \_ _ outcome -> case outcome of
            Planned plan -> map (map _.name <<< _.kindVars) plan.members `shouldEqual` [ [ KindVar "k1" ] ]
            other -> fail ("not planned: " <> show other)
        }

    let
      restrictedMember type' = { key: f, name: f, type: type', body, valueForm: false, written: false }
    it "keeps what a member that is no value form reaches monomorphic, a signature asked for where nothing solves it" do
      inGroup ((\k a -> { k, a }) <$> freshKindMeta Set.empty Set.empty <*> freshTypeMeta emptyXContext XKType) \r s ->
        case prepareGeneralization (attemptJob session registry) ownerOf 1 [ restrictedMember (pure' r.a r.a) ] s of
          Tuple { preparation: Drafted draft } s' -> do
            draft.provisional `shouldEqual` [ { key: f, quantifiers: [] } ]
            map _.types draft.restricted `shouldEqual` [ Set.singleton (metaOf r.a) ]
            levelOf s' (metaOf r.a) `shouldEqual` Just 0
            case finalizeGeneralization ownerOf draft [ restrictedMember (pure' r.a r.a) ] s' of
              Tuple outcome _ -> outcome `shouldEqual` FinalizationHindered [ RestrictedUnsolved f ]
          Tuple other _ -> fail ("not drafted: " <> show other.preparation)

    it "records the kinds a restricted metavariable stands at, and asks nothing where what it reached is solved before the group is" do
      inGroup
        ( do
            k <- freshKindMeta Set.empty Set.empty
            t <- freshTypeMeta emptyXContext k
            pure { k, t }
        )
        \r s -> case prepareGeneralization (attemptJob session registry) ownerOf 1 [ restrictedMember (pure' r.t int) ] s of
          Tuple { preparation: Drafted draft } s' -> do
            map _.kinds draft.restricted `shouldEqual` [ Set.singleton (kindMetaOf r.k) ]
            -- solved between the two parts, as the closing may
            case runAttempt session (equate (siteIn f) { kind: XKType, left: r.t, right: int }) s' of
              Tuple (Done _) solved -> case finalizeGeneralization ownerOf draft [ restrictedMember (pure' r.t int) ] solved of
                Tuple outcome _ -> outcome `shouldEqual` Planned { level: 1, members: [ { key: f, kindVars: [], quantifiers: [] } ] }
              _ -> fail "not solved"
          Tuple other _ -> fail ("not drafted: " <> show other.preparation)

  describe "a synthesis goal of the group" do
    let
      goalMember r = [ { key: f, name: f, type: pure' r.a r.a, body, valueForm: true, written: false } ]
      preparing synthesizer goalType k = inGroup
        ( do
            a <- freshTypeMeta emptyXContext XKType
            w <- atLevel 0 (freshTypeMeta emptyXContext XKType)
            Tuple id _ <- createSynthesis (siteIn f) (goalType { a, w }) (decl synthesizer)
            pure { a, w, id }
        )
        \r s -> case prepareGeneralization (attemptJob session registry) ownerOf 1 (goalMember r) s of
          Tuple outcome s' -> k r outcome.preparation s'
    it "asks for a signature where its type touches a provisional quantifier" do
      preparing "one" _.a \r outcome _ -> outcome `shouldEqual` Hindered [ GoalTouchesQuantifier f (InDeclaration f) r.id ]

    it "is attempted again where it does not, and the group drafted once it is solved" do
      preparing "one" (const int) \r outcome s -> case outcome of
        Drafted _ -> Map.member r.id s.tentative.scheduler.pending `shouldEqual` false
        other -> fail ("not drafted: " <> show other)

    it "is undecided where it still waits after the loop, and a failure where it fails" do
      preparing "patient" _.w \r outcome _ -> outcome `shouldEqual` Hindered [ SynthesisUndecided f (InDeclaration f) r.id ]
      preparing "refusing" (const int) \_ outcome _ -> case outcome of
        PreparationStopped (Rejected _) -> pure unit
        other -> fail ("not stopped: " <> show other)

    it "is held to the quantifiers of the member it belongs to alone" do
      -- `f`'s goal stands at what only `g`'s type holds
      inGroup
        ( do
            a <- freshTypeMeta emptyXContext XKType
            b <- freshTypeMeta emptyXContext XKType
            Tuple id _ <- createSynthesis (siteIn f) b (decl "one")
            pure { a, b, id }
        )
        \r s -> case prepareGeneralization (attemptJob session registry) ownerOf 1 [ { key: f, name: f, type: pure' r.a r.a, body, valueForm: true, written: false }, { key: decl "g", name: decl "g", type: pure' r.b r.b, body, valueForm: true, written: false } ] s of
          Tuple { preparation: Drafted _ } s' -> Map.member r.id s'.tentative.scheduler.pending `shouldEqual` false
          Tuple other _ -> fail ("not drafted: " <> show other.preparation)

    it "attempted again gives what it warned of with what preparing came to" do
      inGroup (createSynthesis (siteIn f) int (decl "warning")) \_ s ->
        case prepareGeneralization (attemptJob session registry) ownerOf 1 [ { key: f, name: f, type: int, body, valueForm: true, written: false } ] s of
          Tuple { preparation: Drafted _, warnings } _ -> Array.length warnings `shouldEqual` 1
          Tuple other _ -> fail ("not drafted: " <> show other.preparation)

  describe "resolving a group's fits by direction" do
    it "stands what it creates at the group's level, the kinds a payload equation makes among them" do
      let
        state t = XRowEffectEntry (Qualified (ModuleName "M") (EffName "State")) [ t ]
      inGroup
        ( do
            ka <- freshKindMeta Set.empty Set.empty
            a <- freshTypeMeta emptyXContext ka
            kb <- freshKindMeta Set.empty Set.empty
            b <- freshTypeMeta emptyXContext kb
            e <- freshTypeMeta emptyXContext (XKRow RowEffect)
            -- the union of the two sources rule 1 forms equates their payloads
            _ <- placeFit (siteIn f) Wrapping (XRowExtend (state a) XRowEmpty) e
            _ <- placeFit (siteIn f) Wrapping (XRowExtend (state b) XRowEmpty) e
            pure a
        )
        \a s -> do
          let
            Tuple _ quiet = run session s
            Tuple _ after = resolveByDirection session (attemptPending session) ownerOf (const 1) quiet
            metas = after.tentative.metas
            kinds = kindMetasOf
              ( substituteKind metas
                  ( case lookupMeta metas (metaOf (substitute metas a)) of
                      Just (Unsolved info) -> info.kind
                      _ -> XKType
                  )
              )
          Array.null (Set.toUnfoldable kinds :: P.Array KindMetaVar) `shouldEqual` false
          map (kindLevelOf after) (Set.toUnfoldable kinds :: P.Array KindMetaVar) `shouldEqual` map (const (Just 1)) (Set.toUnfoldable kinds :: P.Array KindMetaVar)

  describe "the atoms an obligation leaves" do
    let
      eff n = XRowEffectEntry (Qualified (ModuleName "M") (EffName n)) []
      atomsOf constraint s = residualAtoms (substitute s.tentative.metas) (regionScopeOf s.tentative.metas) { constraint, basis: Required, context: emptyXContext, origin: InDeclaration f }
    it "are each known key against each flexible tail, and each flexible tail against each tail of the other side" do
      inGroup ((\a b -> { a, b }) <$> freshTypeMeta emptyXContext (XKRow RowEffect) <*> freshTypeMeta emptyXContext (XKRow RowEffect)) \r s -> do
        atomsOf (XLacks (EffectKey (Qualified (ModuleName "M") (EffName "Console"))) r.a) s `shouldEqual` Right [ LacksAtom (EffectKey (Qualified (ModuleName "M") (EffName "Console"))) (metaOf r.a) ]
        atomsOf (XDisjoint (XRowExtend (eff "Console") r.a) (XRowExtend (eff "Clock") r.b)) s `shouldEqual` Right
          [ LacksAtom (EffectKey (Qualified (ModuleName "M") (EffName "Console"))) (metaOf r.b)
          , LacksAtom (EffectKey (Qualified (ModuleName "M") (EffName "Clock"))) (metaOf r.a)
          , DisjointFlexible (metaOf r.a) (metaOf r.b)
          ]
        atomsOf (XDisjoint r.a (XVar (TyVar "e"))) s `shouldEqual` Right [ DisjointRigid (metaOf r.a) (TyVar "e") ]

    it "leave out a key a tail's scope settles" do
      inGroup (freshTypeMeta emptyXContext (XKRow RowEffect)) \t s ->
        atomsOf (XLacks (RegionKey (RegionName "l")) t) s `shouldEqual` Right []

  describe "committing a group's generalization" do
    let
      rowType = XKRow RowType
      key = SymbolKey (Symbol "x")
      record r = XApp (XCon recordTy []) r
    it "makes each member's quantifiers rigid, wraps its body in their abstractions, and retires what it quantified" do
      committing (freshTypeMeta emptyXContext XKType)
        (\a -> [ { key: f, name: f, type: pure' a a, body: ELam unit (Ident "y") a (EVar unit (Ident "y")), valueForm: true, written: false } ])
        \a outcome after -> case outcome of
          Generalized group -> do
            map _.scheme group.members `shouldEqual` [ { kindVars: [], body: XForall (TyVar "a") XKType (pure' (XVar (TyVar "a")) (XVar (TyVar "a"))) } ]
            sameTerms (map _.body group.members) [ ETyLam unit (TyVar "a") XKType (ELam unit (Ident "y") (XVar (TyVar "a")) (EVar unit (Ident "y"))) ]
            isRetired after (metaOf a) `shouldEqual` true
          GeneralizationHindered hs -> fail ("hindered: " <> show hs)
          GeneralizationHalted d -> fail ("halted: " <> show d)

    it "constrains a member by the atoms its obligations leave, released from the store once taken up" do
      committing
        ( do
            r <- freshTypeMeta emptyXContext rowType
            require (siteIn f) (XLacks key r)
            pure r
        )
        (\r -> [ { key: f, name: f, type: pure' (record r) int, body, valueForm: true, written: false } ])
        \_ outcome after -> case outcome of
          Generalized group -> do
            map _.scheme group.members `shouldEqual`
              [ { kindVars: [], body: XForall (TyVar "a") rowType (XConstrained (XLacks key (XVar (TyVar "a"))) (pure' (record (XVar (TyVar "a"))) int)) } ]
            Map.isEmpty after.tentative.obligations.entries `shouldEqual` true
          GeneralizationHindered hs -> fail ("hindered: " <> show hs)
          GeneralizationHalted d -> fail ("halted: " <> show d)

    it "keeps no atom of its own obligations that the obligation's own site assumes" do
      committing
        ( do
            r <- freshTypeMeta emptyXContext rowType
            require { context: emptyXContext { assumed = [ XLacks key r ] }, origin: InDeclaration f } (XLacks key r)
            pure r
        )
        (\r -> [ { key: f, name: f, type: pure' (record r) int, body, valueForm: true, written: false } ])
        \_ outcome _ -> case outcome of
          Generalized group -> map _.scheme group.members `shouldEqual` [ { kindVars: [], body: XForall (TyVar "a") rowType (pure' (record (XVar (TyVar "a"))) int) } ]
          GeneralizationHindered hs -> fail ("hindered: " <> show hs)
          GeneralizationHalted d -> fail ("halted: " <> show d)

    it "refuses a constraint naming a rigid variable bound inside the member, which the scheme would leave free" do
      committing
        ( do
            t <- freshTypeMeta emptyXContext rowType
            require { context: bindTyVar emptyXContext (TyVar "r") rowType, origin: InDeclaration f } (XDisjoint t (XVar (TyVar "r")))
            pure t
        )
        (\t -> [ { key: f, name: f, type: pure' (record t) int, body, valueForm: true, written: false } ])
        \_ outcome _ -> case outcome of
          GeneralizationHindered hs -> hs `shouldEqual` [ ConstraintEscapes f (InDeclaration f) (TyVar "r") ]
          Generalized _ -> fail "committed"
          GeneralizationHalted d -> fail ("halted: " <> show d)

    it "retires with what it quantifies every solution naming it — an alias, a kind's, a term metavariable's" do
      committing
        ( do
            k1 <- freshKindMeta Set.empty Set.empty
            k2 <- freshKindMeta Set.empty Set.empty
            equateKinds (siteIn f) k1 k2
            g <- freshTypeMeta emptyXContext (XKFun k1 XKType)
            x <- freshTypeMeta emptyXContext k2
            a <- freshTypeMeta emptyXContext XKType
            b <- freshTypeMeta emptyXContext XKType
            equate (siteIn f) { kind: XKType, left: a, right: b }
            m <- freshTermMeta emptyXContext a
            assignTerm (siteIn f) m (ELam unit (Ident "y") b (EVar unit (Ident "y")))
            pure { k1, k2, g, x, a, b, m }
        )
        (\r -> [ { key: f, name: f, type: pure' (XApp r.g r.x) (pure' r.a r.a), body, valueForm: true, written: false } ])
        \r outcome after -> case outcome of
          Generalized _ -> do
            map (isRetired after <<< metaOf) [ r.a, r.b, r.g, r.x ] `shouldEqual` [ true, true, true, true ]
            map (\k -> Map.member (kindMetaOf k) after.tentative.metas.kindBindings) [ r.k1, r.k2 ] `shouldEqual` [ false, false ]
            Map.member r.m after.tentative.metas.termBindings `shouldEqual` false
          GeneralizationHindered hs -> fail ("hindered: " <> show hs)
          GeneralizationHalted d -> fail ("halted: " <> show d)

    it "halts where what the group would retire is held by what another owns" do
      let
        h = decl "h"
        field n = XRowTypeEntry (SymbolKey (Symbol n)) int
      committing
        ( do
            r <- freshTypeMeta emptyXContext rowType
            s' <- freshTypeMeta emptyXContext rowType
            equate (siteIn h) { kind: rowType, left: XRowUnion r s', right: XRowExtend (field "a") XRowEmpty }
            pure r
        )
        (\r -> [ { key: f, name: f, type: pure' (record r) int, body, valueForm: true, written: false } ])
        \_ outcome _ -> case outcome of
          GeneralizationHalted d -> d `shouldEqual` RetiredMetavariableHeld
          Generalized _ -> fail "committed"
          GeneralizationHindered hs -> fail ("hindered: " <> show hs)

    it "halts where another's fit has decided to widen by what the group would retire" do
      -- the fit alone, what deciding it required of its rows aside
      inGroup (freshTypeMeta emptyXContext (XKRow RowEffect)) \r s0 -> do
        let
          s = s0 { tentative { metas { fits = Map.insert (FitId 99) { use: Wrapping, site: siteIn (decl "h"), state: Widen r } s0.tentative.metas.fits } } }
          members = [ { key: f, name: f, type: xFunction int r int, body, valueForm: true, written: false } ]
        case prepareGeneralization (attemptJob session registry) ownerOf 1 members s of
          Tuple { preparation: Drafted draft } s1 -> case finalizeGeneralization ownerOf draft members s1 of
            Tuple (Planned plan) s2 -> case commitGeneralization ownerOf plan members s2 of
              Tuple (GeneralizationHalted d) _ -> d `shouldEqual` RetiredMetavariableHeld
              Tuple _ _ -> fail "not halted"
            Tuple other _ -> fail ("not planned: " <> show other)
          Tuple other _ -> fail ("not drafted: " <> show other.preparation)

    it "halts where another's job waits on what the group would retire, though nothing it holds names it" do
      let
        h = decl "h"
        field n = XRowTypeEntry (SymbolKey (Symbol n)) int
      inGroup ((\r x y -> { r, x, y }) <$> freshTypeMeta emptyXContext rowType <*> freshTypeMeta emptyXContext rowType <*> freshTypeMeta emptyXContext rowType) \r s0 -> do
        let
          Tuple id created = create 0 (siteIn h) (JobUnify { kind: rowType, left: XRowUnion r.x r.y, right: XRowExtend (field "a") XRowEmpty }) s0.tentative.scheduler
          s = s0
            { tentative
                { scheduler = case lookupPending created id of
                    Just p -> reblock p (Set.singleton (metaOf r.r)) created
                    Nothing -> created
                }
            }
          members = [ { key: f, name: f, type: pure' (record r.r) int, body, valueForm: true, written: false } ]
        case prepareGeneralization (attemptJob session registry) ownerOf 1 members s of
          Tuple { preparation: Drafted draft } s1 -> case finalizeGeneralization ownerOf draft members s1 of
            Tuple (Planned plan) s2 -> case commitGeneralization ownerOf plan members s2 of
              Tuple (GeneralizationHalted d) _ -> d `shouldEqual` RetiredMetavariableHeld
              Tuple _ _ -> fail "not halted"
            Tuple other _ -> fail ("not planned: " <> show other)
          Tuple other _ -> fail ("not drafted: " <> show other.preparation)

    it "halts where another's obligation assumes, in its context alone, of what the group would retire" do
      let
        h = decl "h"
      committing
        ( do
            r <- freshTypeMeta emptyXContext rowType
            q <- freshTypeMeta emptyXContext rowType
            require { context: emptyXContext { assumed = [ XLacks key r ] }, origin: InDeclaration h } (XLacks key q)
            pure r
        )
        (\r -> [ { key: f, name: f, type: pure' (record r) int, body, valueForm: true, written: false } ])
        \_ outcome _ -> case outcome of
          GeneralizationHalted d -> d `shouldEqual` RetiredMetavariableHeld
          Generalized _ -> fail "committed"
          GeneralizationHindered hs -> fail ("hindered: " <> show hs)

    it "asks of a constraint on what the member does not quantify an annotation" do
      committing
        ( do
            a <- freshTypeMeta emptyXContext XKType
            r <- freshTypeMeta emptyXContext rowType
            require (siteIn f) (XLacks key r)
            pure a
        )
        (\a -> [ { key: f, name: f, type: pure' a a, body, valueForm: true, written: false } ])
        \_ outcome _ -> case outcome of
          GeneralizationHindered hs -> hs `shouldEqual` [ AmbiguousConstraint f (InDeclaration f) ]
          Generalized _ -> fail "committed"
          GeneralizationHalted d -> fail ("halted: " <> show d)

    it "makes a recursive reference ordinary, at the callee's quantifiers and constraints, raising its constraints where the site does not prove them" do
      let
        g = decl "g"
      committing
        ( do
            a <- freshTypeMeta emptyXContext rowType
            require (siteIn g) (XLacks key a)
            toG <- recursiveRef (siteIn f) g
            toF <- recursiveRef { context: emptyXContext { assumed = [ XLacks key a ] }, origin: InDeclaration g } f
            pure { a, toG, toF }
        )
        ( \r ->
            [ { key: f, name: f, type: pure' (record r.a) int, body: ERecursiveRef unit r.toG, valueForm: true, written: false }
            , { key: g, name: g, type: pure' (record r.a) int, body: ERecursiveRef unit r.toF, valueForm: true, written: false }
            ]
        )
        \_ outcome after -> case outcome of
          Generalized group -> do
            let
              va = XVar (TyVar "a")
              lacks = XLacks key va
            map _.scheme group.members `shouldEqual`
              [ { kindVars: [], body: XForall (TyVar "a") rowType (XConstrained lacks (pure' (record va) int)) }
              , { kindVars: [], body: XForall (TyVar "a") rowType (XConstrained lacks (pure' (record va) int)) }
              ]
            -- `f` raises `g`'s constraint; `g`'s reference to `f` stands where it is assumed
            sameTerms (map _.body group.members)
              [ ETyLam unit (TyVar "a") rowType (EConstraintLam unit lacks (EConstraintApp unit (ETyApp unit (EGlobal unit g []) va)))
              , ETyLam unit (TyVar "a") rowType (EConstraintLam unit lacks (EConstraintApp unit (ETyApp unit (EGlobal unit f []) va)))
              ]
            Map.isEmpty after.tentative.metas.recursiveUses `shouldEqual` true
          GeneralizationHindered hs -> fail ("hindered: " <> show hs)
          GeneralizationHalted d -> fail ("halted: " <> show d)

    it "does not raise an atom the reference's site assumes" do
      let
        g = decl "g"
      committing
        ( do
            a <- freshTypeMeta emptyXContext rowType
            b <- freshTypeMeta emptyXContext XKType
            require (siteIn g) (XLacks key a)
            toG <- recursiveRef { context: emptyXContext { assumed = [ XLacks key a ] }, origin: InDeclaration f } g
            pure { a, b, toG }
        )
        ( \r ->
            [ { key: f, name: f, type: pure' (record r.a) r.b, body: ERecursiveRef unit r.toG, valueForm: true, written: false }
            , { key: g, name: g, type: pure' (record r.a) int, body, valueForm: true, written: false }
            ]
        )
        \_ outcome _ -> case outcome of
          Generalized group ->
            map
              ( \m -> case m.scheme.body of
                  XForall _ _ (XForall _ _ (XConstrained _ _)) -> true
                  XForall _ _ (XConstrained _ _) -> true
                  _ -> false
              )
              group.members `shouldEqual` [ false, true ]
          GeneralizationHindered hs -> fail ("hindered: " <> show hs)
          GeneralizationHalted d -> fail ("halted: " <> show d)

    it "asks of a recursive reference whose arguments the referring member cannot write an annotation, kinds among them" do
      let
        g = decl "g"
      committing
        ( do
            k <- freshKindMeta Set.empty Set.empty
            h <- freshTypeMeta emptyXContext (XKFun k XKType)
            y <- freshTypeMeta emptyXContext k
            toG <- recursiveRef (siteIn f) g
            pure { h, y, toG }
        )
        ( \r ->
            [ { key: f, name: f, type: pure' int int, body: ERecursiveRef unit r.toG, valueForm: true, written: false }
            , { key: g, name: g, type: pure' (XApp r.h r.y) int, body, valueForm: true, written: false }
            ]
        )
        \_ outcome _ -> case outcome of
          GeneralizationHindered hs -> hs `shouldEqual` [ RecursiveArgumentAmbiguous f (InDeclaration f) ]
          Generalized _ -> fail "committed"
          GeneralizationHalted d -> fail ("halted: " <> show d)
      -- a kind argument alone the referring member cannot write
      committing
        ( do
            k <- freshKindMeta Set.empty Set.empty
            toG <- recursiveRef (siteIn f) g
            pure { k, toG }
        )
        ( \r ->
            [ { key: f, name: f, type: pure' int int, body: ERecursiveRef unit r.toG, valueForm: true, written: false }
            , { key: g, name: g, type: pure' (XCon (Qualified (ModuleName "M") (TyName "Proxy")) [ r.k ]) int, body, valueForm: true, written: false }
            ]
        )
        \_ outcome _ -> case outcome of
          GeneralizationHindered hs -> hs `shouldEqual` [ RecursiveArgumentAmbiguous f (InDeclaration f) ]
          Generalized _ -> fail "committed"
          GeneralizationHalted d -> fail ("halted: " <> show d)

    it "gives a recursive reference the callee's kind arguments, written in the referring member's kind variables" do
      let
        g = decl "g"
      committing
        ( do
            k <- freshKindMeta Set.empty Set.empty
            h <- freshTypeMeta emptyXContext (XKFun k XKType)
            y <- freshTypeMeta emptyXContext k
            toG <- recursiveRef (siteIn f) g
            pure { h, y, toG }
        )
        ( \r ->
            [ { key: f, name: f, type: pure' (XApp r.h r.y) int, body: ERecursiveRef unit r.toG, valueForm: true, written: false }
            , { key: g, name: g, type: pure' (XApp r.h r.y) int, body, valueForm: true, written: false }
            ]
        )
        \_ outcome _ -> case outcome of
          Generalized group -> case Array.head group.members of
            Just m -> sameTerms [ m.body ]
              [ ETyLam unit (TyVar "a") (XKFun (XKVar (KindVar "k")) XKType)
                  (ETyLam unit (TyVar "b") (XKVar (KindVar "k")) (ETyApp unit (ETyApp unit (EGlobal unit g [ XKVar (KindVar "k") ]) (XVar (TyVar "a"))) (XVar (TyVar "b"))))
              ]
            Nothing -> fail "no member"
          GeneralizationHindered hs -> fail ("hindered: " <> show hs)
          GeneralizationHalted d -> fail ("halted: " <> show d)

  describe "a member whose signature writes its scheme" do
    let
      rowType = XKRow RowType
      key = SymbolKey (Symbol "x")
      record r = XApp (XCon recordTy []) r
      written type' = [ { key: f, name: f, type: type', body, valueForm: false, written: true } ]
    it "is restricted by nothing, and leaves no equation of its own waiting beyond its generalization, whatever the equation is about" do
      inGroup
        ( do
            -- an equation about what neither the member's type nor its body
            -- holds
            x <- freshTypeMeta emptyXContext rowType
            y <- freshTypeMeta emptyXContext rowType
            equate (siteIn f) { kind: rowType, left: XRowUnion x y, right: XRowExtend (XRowTypeEntry key int) XRowEmpty }
        )
        \_ s -> case prepareGeneralization (attemptJob session registry) ownerOf 1 (written (pure' int int)) s of
          Tuple { preparation: Drafted draft } s' -> do
            draft.restricted `shouldEqual` []
            case finalizeGeneralization ownerOf draft (written (pure' int int)) s' of
              Tuple (FinalizationHindered [ EquationLeft g (InDeclaration g') _ ]) _ | g == f && g' == f -> pure unit
              Tuple other _ -> fail ("not hindered by the equation: " <> show other)
          Tuple other _ -> fail ("not drafted: " <> show other.preparation)

    it "quantifies nothing, a candidate its type holds ambiguous" do
      inGroup (freshTypeMeta emptyXContext XKType) \a s -> case prepareGeneralization (attemptJob session registry) ownerOf 1 (written (pure' a a)) s of
        Tuple { preparation: Drafted draft } s' -> case finalizeGeneralization ownerOf draft (written (pure' a a)) s' of
          Tuple outcome _ -> outcome `shouldEqual` FinalizationHindered [ AmbiguousCandidates f [ metaOf a ] ]
        Tuple other _ -> fail ("not drafted: " <> show other.preparation)

    it "binds no kind variable, a kind candidate its type writes ambiguous" do
      inGroup (freshKindMeta Set.empty Set.empty) \k s ->
        let
          proxy = XCon (Qualified (ModuleName "M") (TyName "Proxy")) [ k ]
        in
          case prepareGeneralization (attemptJob session registry) ownerOf 1 (written (pure' proxy int)) s of
            Tuple { preparation: Drafted draft } s' -> case finalizeGeneralization ownerOf draft (written (pure' proxy int)) s' of
              Tuple outcome _ -> outcome `shouldEqual` FinalizationHindered [ AmbiguousKindCandidates f [ kindMetaOf k ] ]
            Tuple other _ -> fail ("not drafted: " <> show other.preparation)

    it "gains no constraint, one its obligations leave refused where it arose" do
      committing
        ( do
            -- outside the group, so that nothing would quantify it
            r <- atLevel 0 (freshTypeMeta emptyXContext rowType)
            require (siteIn f) (XLacks key r)
            pure r
        )
        (\r -> written (pure' (record r) int))
        \_ outcome _ -> case outcome of
          GeneralizationHindered [ ConstraintUnwritten g (InDeclaration g') ] | g == f && g' == f -> pure unit
          GeneralizationHindered hs -> fail ("hindered otherwise: " <> show hs)
          Generalized _ -> fail "generalized"
          GeneralizationHalted d -> fail ("halted: " <> show d)

  describe "what does not cross a generalization" do
    it "is reported by its cause: an undecided fit, a pending boundary, a term metavariable, and a restricted metavariable a waiting equation touches" do
      let
        field n = XRowTypeEntry (SymbolKey (Symbol n)) int
        rowEffect = XKRow RowEffect
        rowType = XKRow RowType
      inGroup
        ( do
            a <- freshTypeMeta emptyXContext XKType
            source <- freshTypeMeta emptyXContext rowEffect
            target <- freshTypeMeta emptyXContext rowEffect
            fit <- placeFit (siteIn f) Wrapping source target
            sigma <- openBoundary emptyXContext
            inner <- freshTypeMeta emptyXContext rowEffect
            _ <- placeFit (siteIn f) Wrapping inner (XMeta sigma)
            closeBoundary (siteIn f) sigma XRowEmpty
            x <- freshTypeMeta emptyXContext rowType
            y <- freshTypeMeta emptyXContext rowType
            equate (siteIn f) { kind: rowType, left: XRowUnion x y, right: XRowExtend (field "a") XRowEmpty }
            pure { a, fit }
        )
        \r s -> case prepareGeneralization (attemptJob session registry) ownerOf 1 [ { key: f, name: f, type: pure' r.a r.a, body, valueForm: true, written: false } ] s of
          Tuple { preparation: Drafted draft } s' -> case finalizeGeneralization ownerOf draft [ { key: f, name: f, type: pure' r.a r.a, body, valueForm: true, written: false } ] s' of
            Tuple (FinalizationHindered hindrances) _ -> do
              Array.length (Array.filter isFitLeft hindrances) `shouldEqual` 2
              Array.length (Array.filter isBoundaryLeft hindrances) `shouldEqual` 1
              Array.elem (RestrictedUnsolved f) hindrances `shouldEqual` true
            Tuple other _ -> fail ("not hindered: " <> show other)
          Tuple other _ -> fail ("not drafted: " <> show other.preparation)
  where
  isFitLeft = case _ of
    FitLeft _ _ _ -> true
    _ -> false
  isBoundaryLeft = case _ of
    BoundaryLeft _ _ _ -> true
    _ -> false
