-- | Hand-written Core⁺ with a synthesis hole in it, the hole filled by the
-- | reference synthesizer through the scheduler, and the term zonked and taken
-- | to the Core checker.
-- |
-- | ```text
-- | Core⁺ with ?m → goals and equations submitted or queued → the loop
-- |   → the reference synthesizer → the target assigned → Completed → zonk
-- |   → toCoreExpr → globalsOf → the Core checker
-- | ```
-- |
-- | Five things are what these cases are for. **A goal is answered from where
-- | it was asked**: the synthesizer reads the goal's type and the bindings of
-- | the site it was created at, however late the loop runs it, each goal its
-- | own. **The answer lands where the hole stood**: zonked, the hole is the term
-- | the synthesizer built, carrying the hole's annotation. **A goal that waits
-- | is run again from its beginning**: the attempt that waited leaves nothing
-- | it built, the job holds only its description, the retry alone spends fuel,
-- | and a handle the waiting attempt was given is refused when it is presented
-- | again. **A candidate search takes back what does not fit**: a candidate
-- | that fails is rolled back, what it assigned and built among it, and the
-- | next is tried; one that waits or misuses the kernel is not caught. And
-- | **what crosses the boundary is what committed, and is checked**: nothing
-- | unsolved crosses, the only global referred to is the candidate that
-- | answered, the Core checker accepts the declaration completed, and refuses a
-- | term whose claim was derived and not borne out; the same input gives the
-- | same trace.
module Test.Stella.Compiler.Elaborate.SynthesisVertical (spec) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.CorePlus.Context (Origin(..), bindVar, emptyXContext)
import Stella.Compiler.Elaborate.CorePlus.Term (Residue(..), TermMetaVar, XExpr(..), toCoreExpr)
import Stella.Compiler.Elaborate.CorePlus.Type (MetaVar, XRowEntry(..), XType(..), fromCore)
import Stella.Compiler.Elaborate.CorePlus.Kind (XKind(..))
import Stella.Compiler.Elaborate.Driver.Attempt (Attempt(Committed, Registered), OpenResult(..), Response(..), Step(..), envelopeOf)
import Stella.Compiler.Elaborate.Driver.Attempt as Run
import Stella.Compiler.Elaborate.Driver.Conversation (command, openConversation)
import Stella.Compiler.Elaborate.Driver.Loop (RunReport, RunResult(..), Submission(..), submitAttempting)
import Stella.Compiler.Elaborate.Driver.Synthesis (Registry, attemptJob, runSynthesis, submitSynthesis)
import Stella.Compiler.Elaborate.Environment.Catalog (EntrySort(..), catalogOf)
import Stella.Compiler.Elaborate.Environment.Constructors (constructorsOf)
import Stella.Compiler.Elaborate.Environment.Effects (effectsOf)
import Stella.Compiler.Elaborate.Kernel.Elab (Outcome(..), SessionEnv, SolverState, createSynthesis, freshTypeMeta, initialState, runElabIn)
import Stella.Compiler.Elaborate.Mechanism.Kinding (kindingOf)
import Stella.Compiler.Elaborate.Mechanism.Pending (Job(..), PendingId, Site)
import Stella.Compiler.Elaborate.Mechanism.Scheduler (Phase(..), lookupPending, nextReady, takeReady)
import Stella.Compiler.Elaborate.Mechanism.TermMeta (zonkExpr)
import Stella.Compiler.Elaborate.Mechanism.Unify (MetaBinding(..), TermBinding(..), lookupMeta, lookupTermMeta)
import Stella.Compiler.Elaborate.Protocol.Facade as F
import Stella.Compiler.Elaborate.Vocabulary.Diagnostic (Defect(..), Diagnostic(..))
import Stella.Compiler.Elaborate.Vocabulary.Handle (HandleError(..), SessionId(..), emptyArena)
import Stella.Compiler.Elaborate.Vocabulary.Message (FrozenMessagePart(..), MessagePart(..))
import Stella.Compiler.Elaborate.Vocabulary.Request (Command(..), CommandAnswer(..), KernelAnswer(..), BuildRequest(..), KernelRequest(..), ObserveRequest(..), ReportRequest(..), SolveRequest(..), TermRequest(..))
import Stella.Compiler.Elaborate.Vocabulary.Trace (Fate(..), TraceEvent(..), Tracing(..), fates)
import Stella.Compiler.Elaborate.Vocabulary.View (ConstraintView(..), KindView(KindRow), PayloadView(..), TypeView(..))
import Stella.Compiler.TypedCore (Attribute, Decl(..), Expr(..), Ident(..), Kind(..), KindVar(..), Literal(..), Module, ModuleName(..), Qualified(..), RowElemKind(..), RowEntry(..), RowKey(..), Symbol(..), TyVar(..), Type(..), globalsOf, monoScheme)
import Stella.Compiler.TypedCore.Declare (declare)
import Stella.Compiler.TypedCore.Prim (booleanTy, intTy, primSignature, recordTy)
import Stella.Compiler.TypedCore.Signature (Signature)
import Data.Array.NonEmpty (NonEmptyArray)
import Data.Array.NonEmpty as NonEmptyArray
import Data.Either (Either(..), either, isLeft, isRight)
import Data.Array as Array
import Data.Foldable (foldl)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Effect.Aff (Aff)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)
import Test.Stella.Compiler.Elaborate.Reference (Policy, badApplication, policy, reference, workingOnCandidate, workingWhileWaiting)

main :: ModuleName
main = ModuleName "Main"

mainOne :: Qualified Ident
mainOne = Qualified main (Ident "one")

xInt :: XType
xInt = XCon intTy []

xBoolean :: XType
xBoolean = XCon booleanTy []

-- | `a` and `z`, the keys of the candidates' records. `a` sorts first, so an
-- | equation between two of these rows meets `a` before `z`.
keyA :: RowKey
keyA = SymbolKey (Symbol "a")

keyZ :: RowKey
keyZ = SymbolKey (Symbol "z")

-- | `Record (a : τ, z : σ)`.
recordOf :: Type -> Type -> Type
recordOf a z = TApp (TCon recordTy []) (TRowExtend (RowTypeEntry keyA a) (TRowExtend (RowTypeEntry keyZ z) TRowEmpty))

coreInt :: Type
coreInt = TCon intTy []

coreBoolean :: Type
coreBoolean = TCon booleanTy []

-- | The declarations of `Main`, each with the scheme the catalog gives it:
-- |
-- | ```text
-- | one   : Int                           no attribute
-- | cand0 : forall k. forall (t : k). Int  candidate, with a kind variable
-- | cand1 : Record (a : Int, z : Boolean)  candidate
-- | cand2 : Record (a : Boolean, z : Int)  candidate
-- | decoy : Int                           another attribute
-- | ```
declarations :: P.Array { name :: P.String, kindVars :: P.Array KindVar, type :: Type, value :: Expr P.Int, attributes :: P.Array Attribute }
declarations =
  [ { name: "one", kindVars: [], type: coreInt, value: Lit 1 (LitInt 1), attributes: [] }
  , { name: "cand0", kindVars: [ k ], type: TForall t (KVar k) coreInt, value: TyLam 1 t (KVar k) (Lit 1 (LitInt 0)), attributes: [ marked "candidate" ] }
  , { name: "cand1", kindVars: [], type: recordOf coreInt coreBoolean, value: record (LitInt 1) (LitBoolean true), attributes: [ marked "candidate" ] }
  , { name: "cand2", kindVars: [], type: recordOf coreBoolean coreInt, value: record (LitBoolean true) (LitInt 1), attributes: [ marked "candidate" ] }
  , { name: "decoy", kindVars: [], type: coreInt, value: Lit 1 (LitInt 3), attributes: [ marked "other" ] }
  ]
  where
  k = KindVar "k"
  t = TyVar "t"
  record a z = RecordExtend 1 keyA (Lit 1 a) (RecordExtend 1 keyZ (Lit 1 z) (RecordEmpty 1))
  marked key = { name: Qualified main (Ident key), positional: [], keyword: [] }

valuesModule :: Module P.Int
valuesModule =
  { annotation: 0
  , name: main
  , imports: []
  , exports: []
  , decls:
      map (\n -> DeclAttribute 1 { name: Ident n, positional: [], keyword: [] }) [ "candidate", "other" ]
        <> map (\d -> DeclNonRec 1 { name: Ident d.name, scheme: { kindVars: d.kindVars, body: d.type }, value: d.value, attributes: d.attributes }) declarations
  }

signature :: Signature
signature = either (const primSignature) identity (declare primSignature valuesModule)

session :: SessionEnv
session = sessionWith TraceDisabled

sessionWith :: Tracing -> SessionEnv
sessionWith tracing =
  { catalog: catalogOf (map (\d -> { name: Qualified main (Ident d.name), sort: ValueEntry, scheme: { kindVars: d.kindVars, body: fromCore d.type }, attributes: d.attributes }) declarations)
  , kinding: kindingOf signature
  , constructors: constructorsOf signature
  , effects: effectsOf signature
  , tracing
  }

resolver :: Qualified Ident
resolver = Qualified (ModuleName "Synth") (Ident "reference")

registry :: Registry
registry = Map.fromFoldable
  [ Tuple resolver (reference answering)
  , Tuple working (workingWhileWaiting (reference answering))
  , Tuple searching (reference (assigningOn cand1 (workingOnCandidate cand1 candidatesOnly)))
  , Tuple passingOver (reference (workingOnCandidate cand0 candidatesOnly))
  , Tuple assigningInWinner (reference (assigningOn cand2 candidatesOnly))
  , Tuple postponing (reference (misusingOn cand2 candidatesOnly))
  , Tuple breaking (reference (misusingOn cand1 candidatesOnly))
  , Tuple keeping (reference (workingOnCandidate cand2 candidatesOnly))
  , Tuple badly badApplication
  ]

-- | Answering from `Main.one`, then from the candidates.
answering :: Policy
answering = policy [ mainOne ] (Qualified main (Ident "candidate"))

-- | Answering from the candidates alone.
candidatesOnly :: Policy
candidatesOnly = policy [] (Qualified main (Ident "candidate"))

-- | The policy given, misusing the kernel before the candidate named is tried:
-- | a variable nothing binds.
misusingOn :: Qualified Ident -> Policy -> Policy
misusingOn candidate given = given
  { beforeTrying = \root goalType name -> do
      given.beforeTrying root goalType name
      when (name == candidate) (void (F.localVariable root (Ident "missing")))
  }

-- | The policy given, except that where the candidate named is tried it first
-- | equates the field `a` of the goal's record with `Int`, an equation of its
-- | own that succeeds and assigns what it can before the candidate is referred
-- | to. A goal that is not a record with that field is a misuse of the fixture,
-- | and stops the attempt as a defect rather than failing the candidate.
assigningOn :: Qualified Ident -> Policy -> Policy
assigningOn candidate given = given
  { beforeTrying = \root goalType name -> do
      given.beforeTrying root goalType name
      when (name == candidate) do
        field <- F.viewType goalType >>= case _ of
          AppType _ row -> F.normalizeRow row <#> \view -> Array.find (\entry -> entry.key == keyA) view.known
          _ -> pure Nothing
        case field of
          Just { payload: TypePayload a } -> F.typeConstructor root intTy [] >>= F.unify root a
          _ -> void (F.localVariable root (Ident "no field a in the goal"))
  }

cand0 :: Qualified Ident
cand0 = Qualified main (Ident "cand0")

cand1 :: Qualified Ident
cand1 = Qualified main (Ident "cand1")

cand2 :: Qualified Ident
cand2 = Qualified main (Ident "cand2")

searching :: Qualified Ident
searching = Qualified (ModuleName "Synth") (Ident "searching")

postponing :: Qualified Ident
postponing = Qualified (ModuleName "Synth") (Ident "postponing")

breaking :: Qualified Ident
breaking = Qualified (ModuleName "Synth") (Ident "breaking")

keeping :: Qualified Ident
keeping = Qualified (ModuleName "Synth") (Ident "keeping")

badly :: Qualified Ident
badly = Qualified (ModuleName "Synth") (Ident "badly")

passingOver :: Qualified Ident
passingOver = Qualified (ModuleName "Synth") (Ident "passingOver")

assigningInWinner :: Qualified Ident
assigningInWinner = Qualified (ModuleName "Synth") (Ident "assigningInWinner")

x :: Ident
x = Ident "x"

y :: Ident
y = Ident "y"

-- | A site binding the variables given.
siteBinding :: P.Array (Tuple Ident XType) -> Site
siteBinding bindings =
  { context: foldl (\ctx (Tuple name ty) -> bindVar ctx name ty) emptyXContext bindings
  , origin: InDeclaration (Qualified main (Ident "decl"))
  }

-- | Goals asked of the reference synthesizer at the sites and types given,
-- | queued in that order from one action, and the loop run over them.
answered :: P.Array (Tuple Site XType) -> Either P.String (Tuple (P.Array TermMetaVar) (Tuple RunResult SolverState))
answered asks = case runElabIn session (initialState (SessionId 0) 10) (traverse ask asks) of
  Tuple (Done targets) queued -> case runSynthesis session registry queued of
    Tuple report s -> Right (Tuple targets (Tuple report.result s))
  Tuple other _ -> Left (show other)
  where
  ask (Tuple site ty) = createSynthesis site ty resolver <#> \(Tuple _ target) -> target

givenAnswered :: P.Array (Tuple Site XType) -> (P.Array TermMetaVar -> RunResult -> SolverState -> Aff Unit) -> Aff Unit
givenAnswered asks check = case answered asks of
  Right (Tuple targets (Tuple result s)) -> check targets result s
  Left err -> fail err

spec :: Spec Unit
spec = describe "Elaborate, a synthesis hole filled by the reference synthesizer" do
  it "is answered from what its site binds, and zonks to the variable where the hole stood" do
    givenAnswered [ Tuple (siteBinding [ Tuple x xInt ]) xInt ] \targets result s -> case targets of
      [ m ] -> do
        result `shouldEqual` Completed
        -- `λ(x : Int). ?m`, the hole annotated 7 and the rest 0.
        zonkExpr s.tentative.metas (ELam 0 x xInt (ETermMeta 7 m)) `shouldEqual` ELam 0 x xInt (EVar 7 x)
      other -> fail (show other)

  it "is answered from the globals given where nothing its site binds has its type" do
    givenAnswered [ Tuple (siteBinding [ Tuple x xBoolean ]) xInt ] \targets result s -> case targets of
      [ m ] -> do
        result `shouldEqual` Completed
        -- `λ(x : Boolean). ?m`.
        zonkExpr s.tentative.metas (ELam 0 x xBoolean (ETermMeta 7 m)) `shouldEqual` ELam 0 x xBoolean (EGlobal 7 mainOne [])
      other -> fail (show other)

  it "reads the site each goal was created at, however late the loop runs it" do
    let
      -- Two goals queued together, each at a site binding one variable at
      -- `Int`: each is answered with its own.
      asks = [ Tuple (siteBinding [ Tuple x xInt ]) xInt, Tuple (siteBinding [ Tuple y xInt ]) xInt ]
    givenAnswered asks \targets result s -> do
      result `shouldEqual` Completed
      map (\m -> zonkExpr s.tentative.metas (ETermMeta 3 m)) targets `shouldEqual` [ EVar 3 x, EVar 3 y ]

  it "fails where nothing its site binds, and no global given, has its type, the hole left" do
    givenAnswered [ Tuple (siteBinding []) xBoolean ] \targets result s -> case targets of
      [ m ] -> do
        case result of
          Rejected (SynthesisFailed _) -> pure unit
          other -> fail (show other)
        case lookupTermMeta s.tentative.metas m of
          Just (TermUnsolved _) -> pure unit
          other -> fail ("the hole was not left: " <> show other)
      other -> fail (show other)

  it "waits on its type's metavariable, leaves nothing of the attempt that waited, and is answered once the host solves it" do
    case waiting working of
      Left err -> fail err
      Right w -> do
        let
          before = w.queued.tentative
          Tuple first s1 = runSynthesis session registry w.queued
          -- The host submits `?a ≡ Int`, between the two runs of the loop.
          Tuple equation s2 = submitAttempting (attemptJob session registry) w.site (JobUnify { kind: XKType, left: XMeta w.a, right: xInt }) s1
          Tuple second s3 = runSynthesis session registry s2
        -- What the attempt starts from: nothing written, no handle, no warning.
        before.written `shouldEqual` Set.empty
        before.arena `shouldEqual` emptyArena
        before.warnings `shouldEqual` []
        w.queued.retained.fuel `shouldEqual` 10
        -- The first attempt waits, and what it built is gone.
        case first.result of
          Blocked _ -> pure unit
          other -> fail ("the goal did not wait: " <> show other)
        first.warnings `shouldEqual` []
        s1.tentative.metas `shouldEqual` before.metas
        s1.tentative.obligations `shouldEqual` before.obligations
        s1.tentative.names `shouldEqual` before.names
        s1.tentative.open `shouldEqual` before.open
        s1.tentative.written `shouldEqual` Set.empty
        s1.tentative.arena `shouldEqual` emptyArena
        s1.tentative.warnings `shouldEqual` []
        lookupPending s1.tentative.scheduler w.id `shouldEqual` map (_ { awaiting = Set.singleton w.a }) (lookupPending before.scheduler w.id)
        nextReady s1.tentative.scheduler `shouldEqual` Nothing
        unsolved s1 w.target `shouldEqual` true
        s1.retained.fuel `shouldEqual` 10
        (s1.retained.nextGeneration > w.queued.retained.nextGeneration) `shouldEqual` true
        (s1.retained.nextConversation > w.queued.retained.nextConversation) `shouldEqual` true
        s1.retained.session `shouldEqual` w.queued.retained.session
        s1.retained.trace `shouldEqual` []
        -- The equation commits, and wakes the goal for a retry.
        case equation of
          Continue { attempt: Committed } -> pure unit
          Continue other -> fail (show other.attempt)
          Stop report -> fail (show report.result)
        s2.retained.fuel `shouldEqual` 10
        nextReady s2.tentative.scheduler `shouldEqual` Just { id: w.id, phase: Retry }
        -- The retry answers from the same site, spending the one unit.
        second.result `shouldEqual` Completed
        second.warnings `shouldEqual` []
        s3.retained.fuel `shouldEqual` 9
        zonkExpr s3.tentative.metas (ELam 0 x xInt (ETermMeta 7 w.target)) `shouldEqual` ELam 0 x xInt (EVar 7 x)
        Map.isEmpty s3.tentative.scheduler.pending `shouldEqual` true

  it "requires, while it waits, a constraint that stays open until the attempt is rolled back" do
    case waiting working of
      Left err -> fail err
      Right w -> case takeReady w.queued.tentative.scheduler of
        Nothing -> fail "no job was queued"
        Just (Tuple id scheduler) -> case openConversation session id (w.queued { tentative { scheduler = scheduler } }) of
          OpenStopped attempt _ -> fail (show attempt)
          Opened c0 ->
            -- The requests the waiting work makes, up to its constraint.
            case ask (BuildRequest RootScope) c0 of
              Answered (Returned (KernelAnswered (HandleAnswer root))) c1 -> case ask (SolveRequest (FreshMetaType root (KindRow RowType))) c1 of
                Answered (Returned (KernelAnswered (HandleAnswer row))) c2 -> case ask (SolveRequest (Require root (LacksView (SymbolKey (Symbol "waiting")) row))) c2 of
                  Answered (Returned _) c3 -> (c3.state.tentative.obligations == w.queued.tentative.obligations) `shouldEqual` false
                  other -> fail (describeStep other)
                other -> fail (describeStep other)
              other -> fail (describeStep other)

  it "refuses a handle an attempt that waited was given, presented again when the goal is retried" do
    case waiting resolver of
      Left err -> fail err
      Right w -> case takeReady w.queued.tentative.scheduler of
        Nothing -> fail "no job was queued"
        Just (Tuple id scheduler) -> case openConversation session id (w.queued { tentative { scheduler = scheduler } }) of
          OpenStopped attempt _ -> fail (show attempt)
          Opened c0 -> case c0.goal of
            Nothing -> fail "the goal was given no handle"
            Just goal ->
              -- The first attempt is driven by commands, as a guest drives it,
              -- and the guest keeps the handle of the goal's type.
              case ask (ObserveRequest (GoalType goal)) c0 of
                Answered (Returned (KernelAnswered (HandleAnswer kept))) c1 -> case ask (ObserveRequest (ViewType kept)) c1 of
                  Answered (Returned (KernelAnswered (TypeViewAnswer (MetaType m)))) c2 -> case ask (ReportRequest (Postpone [ m ])) c2 of
                    Finished (Registered _) s1 -> do
                      let
                        Tuple _ s2 = submitAttempting (attemptJob session registry) w.site (JobUnify { kind: XKType, left: XMeta w.a, right: xInt }) s1
                        -- The retry presents the handle it kept.
                        caching _ = F.viewType kept *> F.throw [ TextPart "the kept handle was taken" ]
                        Tuple report _ = runSynthesis session (Map.singleton resolver caching) s2
                      report.result `shouldEqual` Halted (InvalidHandle kept StaleHandle)
                    other -> fail (describeStep other)
                  other -> fail (describeStep other)
                other -> fail (describeStep other)

  describe "searching the candidates an attribute marks" do
    it "declares its candidates to the Core checker as the catalog gives them" do
      isRight (declare primSignature valuesModule) `shouldEqual` true

    it "reads the same candidates, in ascending order and by their key alone, before a wait and after it" do
      case waiting resolver of
        Left err -> fail err
        Right w -> case takeReady w.queued.tentative.scheduler of
          Nothing -> fail "no job was queued"
          Just (Tuple id scheduler) -> case openConversation session id (w.queued { tentative { scheduler = scheduler } }) of
            OpenStopped attempt _ -> fail (show attempt)
            Opened c0 -> case c0.goal, ask (ObserveRequest (DeclsWithAttr (Qualified main (Ident "candidate")))) c0 of
              Just goal, Answered (Returned (KernelAnswered (NamesAnswer before))) c1 -> case ask (ObserveRequest (GoalType goal)) c1 of
                Answered (Returned (KernelAnswered (HandleAnswer ty))) c2 -> case ask (ObserveRequest (ViewType ty)) c2 of
                  Answered (Returned (KernelAnswered (TypeViewAnswer (MetaType m)))) c3 -> case ask (ReportRequest (Postpone [ m ])) c3 of
                    Finished (Registered _) s1 -> do
                      let
                        Tuple _ s2 = submitAttempting (attemptJob session registry) w.site (JobUnify { kind: XKType, left: XMeta w.a, right: xInt }) s1
                      before `shouldEqual` [ cand0, cand1, cand2 ]
                      case takeReady s2.tentative.scheduler of
                        Nothing -> fail "the goal was not woken"
                        Just (Tuple retried taken) -> case openConversation session retried (s2 { tentative { scheduler = taken } }) of
                          OpenStopped attempt _ -> fail (show attempt)
                          Opened d0 -> case ask (ObserveRequest (DeclsWithAttr (Qualified main (Ident "candidate")))) d0 of
                            Answered (Returned (KernelAnswered (NamesAnswer after))) _ -> after `shouldEqual` before
                            other -> fail (describeStep other)
                    other -> fail (describeStep other)
                  other -> fail (describeStep other)
                other -> fail (describeStep other)
              _, other -> fail (describeStep other)

    it "rolls back a candidate that does not fit, what it assigned and built among it, and takes the next" do
      let
        -- A goal at `Record (a : ?t, z : Int)`. Inside its transaction, `cand1`
        -- builds a metavariable, an open constraint, and a warning, and equates
        -- the goal's field `a` with `Int` on its own, which assigns `?t := Int`;
        -- then its claim fails at `z`. `cand2` fits only once `?t` is unsolved
        -- again, with `?t := Boolean`.
        created = do
          t <- freshTypeMeta emptyXContext XKType
          let
            goalType = XApp (XCon recordTy []) (XRowExtend (XRowTypeEntry keyA t) (XRowExtend (XRowTypeEntry keyZ xInt) XRowEmpty))
          Tuple _ target <- createSynthesis (siteBinding []) goalType searching
          pure { t, target }
      case runElabIn session (initialState (SessionId 0) 10) created of
        Tuple (Done made@{ t: XMeta t }) queued -> do
          let
            Tuple report s = runSynthesis session registry queued
          report.result `shouldEqual` Completed
          report.warnings `shouldEqual` []
          zonkExpr s.tentative.metas (ETermMeta 7 made.target) `shouldEqual` EGlobal 7 cand2 []
          lookupMeta s.tentative.metas t `shouldEqual` Just (Assigned xBoolean)
          Map.keys s.tentative.metas.bindings `shouldEqual` Map.keys queued.tentative.metas.bindings
          s.tentative.obligations `shouldEqual` queued.tentative.obligations
        Tuple other _ -> fail (show other)

    it "passes over a candidate with a kind variable, doing nothing for it" do
      case recordGoal passingOver of
        Left err -> fail err
        Right made -> do
          let
            Tuple report s = runSynthesis session registry made.queued
          report.result `shouldEqual` Completed
          report.warnings `shouldEqual` []
          zonkExpr s.tentative.metas (ETermMeta 7 made.target) `shouldEqual` EGlobal 7 cand2 []
          Map.keys s.tentative.metas.bindings `shouldEqual` Map.keys made.queued.tentative.metas.bindings
          s.tentative.obligations `shouldEqual` made.queued.tentative.obligations

    it "fails the candidate that fits where the same assignment is made in it first" do
      -- The control of the rollback: `?t := Int` made in `cand2` leaves no
      -- candidate that fits, so the case before is not passing for want of
      -- the assignment made.
      case recordGoal assigningInWinner of
        Left err -> fail err
        Right made -> do
          let
            Tuple report s = runSynthesis session registry made.queued
          case report.result of
            Rejected (SynthesisFailed _) -> pure unit
            other -> fail (show other)
          case lookupMeta s.tentative.metas made.t of
            Just (Unsolved _) -> pure unit
            other -> fail ("?t was left assigned: " <> show other)

    it "keeps what the candidate that fits built, where the same work is done in it" do
      let
        -- The control of the case before: the work `searching` does in `cand1`,
        -- done in `cand2`, which fits, is kept.
        created = do
          t <- freshTypeMeta emptyXContext XKType
          let
            goalType = XApp (XCon recordTy []) (XRowExtend (XRowTypeEntry keyA t) (XRowExtend (XRowTypeEntry keyZ xInt) XRowEmpty))
          createSynthesis (siteBinding []) goalType keeping
      case runElabIn session (initialState (SessionId 0) 10) created of
        Tuple (Done _) queued -> do
          let
            Tuple report s = runSynthesis session registry queued
          report.result `shouldEqual` Completed
          map _.message report.warnings `shouldEqual` [ [ FrozenText "trying" ] ]
          (s.tentative.obligations == queued.tentative.obligations) `shouldEqual` false
        Tuple other _ -> fail (show other)

    it "does not catch a candidate that waits: the goal waits, and no later candidate is tried" do
      let
        -- A goal at `Record (?r ∪ ?s)`: `cand1` cannot be equated with it until
        -- `?r` or `?s` is solved. `cand2` would misuse the kernel if tried.
        created = do
          r <- freshTypeMeta emptyXContext (XKRow RowType)
          r' <- freshTypeMeta emptyXContext (XKRow RowType)
          Tuple id _ <- createSynthesis (siteBinding []) (XApp (XCon recordTy []) (XRowUnion r r')) postponing
          pure { id, r, r' }
      case runElabIn session (initialState (SessionId 0) 10) created of
        Tuple (Done made@{ r: XMeta r, r': XMeta r' }) queued -> case runSynthesis session registry queued of
          Tuple report s -> do
            case report.result of
              Blocked _ -> pure unit
              other -> fail ("the goal did not wait: " <> show other)
            map _.awaiting (lookupPending s.tentative.scheduler made.id) `shouldEqual` Just (Set.fromFoldable [ r, r' ])
        Tuple other _ -> fail (show other)

    it "does not hide a candidate's defect: the loop stops, and runs no job after it" do
      let
        -- Two goals at `Int`, the first asked of a policy whose `cand1` misuses
        -- the kernel.
        created = traverse (\by -> createSynthesis (siteBinding []) xInt by) [ breaking, resolver ]
      case runElabIn session (initialState (SessionId 0) 10) created of
        Tuple (Done goals) queued -> case runSynthesis session registry queued of
          Tuple report s -> do
            case report.result of
              Halted (BuildRejected _) -> pure unit
              other -> fail (show other)
            map (\(Tuple _ target) -> unsolved s target) goals `shouldEqual` [ true, true ]
            map _.id (nextReady s.tentative.scheduler) `shouldEqual` map (\(Tuple id _) -> id) (Array.last goals)
        Tuple other _ -> fail (show other)

    it "refuses a handle built inside a candidate that failed, presented after it" do
      case waiting resolver of
        Left err -> fail err
        Right w -> case takeReady w.queued.tentative.scheduler of
          Nothing -> fail "no job was queued"
          Just (Tuple id scheduler) -> case openConversation session id (w.queued { tentative { scheduler = scheduler } }) of
            OpenStopped attempt _ -> fail (show attempt)
            Opened c0 -> case ask (BuildRequest RootScope) c0 of
              Answered (Returned (KernelAnswered (HandleAnswer root))) c1 -> case command (envelopeOf c1) BeginTransaction c1 of
                Answered (Returned (TransactionBegun _)) c2 -> case ask (TermRequest (GlobalRef root cand1 [])) c2 of
                  Answered (Returned (KernelAnswered (HandleAnswer kept))) c3 -> case ask (ReportRequest (Throw [ TextPart "not this one" ])) c3 of
                    Answered (CandidateFailed _ _) c4 -> case ask (ObserveRequest (TypeOf kept)) c4 of
                      Finished attempt _ -> attempt `shouldEqual` Run.Halted (InvalidHandle kept StaleHandle)
                      other -> fail (describeStep other)
                    other -> fail (describeStep other)
                  other -> fail (describeStep other)
                other -> fail (describeStep other)
              other -> fail (describeStep other)

  describe "carried to the Core checker" do
    it "solves a goal through a wait and a candidate search, and the Core checker accepts the declaration it completes" do
      case scenario session of
        Left err -> fail err
        Right run -> do
          case run.first of
            Continue { attempt: Registered waited } -> waited `shouldEqual` Set.singleton run.g
            other -> fail ("the first attempt did not wait: " <> show other)
          case run.equation of
            Continue { attempt: Committed } -> pure unit
            other -> fail ("the equation did not commit: " <> show other)
          run.report.result `shouldEqual` Completed
          lookupMeta run.state.tentative.metas run.g `shouldEqual` Just (Assigned answerType)
          run.zonked `shouldEqual` ELet 0 y answerType (EGlobal 7 cand2 []) (EVar 0 y)
          case run.core of
            Right core -> do
              globalsOf core `shouldEqual` Set.singleton cand2
              isRight (declare primSignature (completedWith "answer" (recordOf coreBoolean coreInt) core)) `shouldEqual` true
            Left residues -> fail ("the declaration did not cross the boundary: " <> show residues)

    it "commits an application whose argument is not at the function's parameter type, and the Core checker refuses it" do
      case submitSynthesis session registry (siteBinding []) xInt badly (initialState (SessionId 0) 10) of
        Tuple { target, submission: Continue { attempt: Committed } } s -> case toCoreExpr (zonkExpr s.tentative.metas (ETermMeta 7 target)) of
          Right core -> isLeft (declare primSignature (completedWith "answer" coreInt core)) `shouldEqual` true
          Left residues -> fail ("the term did not cross the boundary: " <> show residues)
        Tuple { submission } _ -> fail ("the term was not committed: " <> show submission)

    it "does not let an unsolved term metavariable cross the boundary" do
      case runElabIn session (initialState (SessionId 0) 10) (createSynthesis (siteBinding []) xInt resolver) of
        Tuple (Done (Tuple _ m)) s ->
          case toCoreExpr (zonkExpr s.tentative.metas (ETermMeta 7 m)) of
            Left residues -> NonEmptyArray.toArray residues `shouldEqual` [ ResidualTermMeta 7 m ]
            Right _ -> fail "an unsolved term metavariable crossed the boundary"
        Tuple other _ -> fail (show other)

    it "gives the same submissions, report, term, state, and trace from the same input, the candidate that failed rolled back in it" do
      case scenario (sessionWith TraceEnabled), scenario (sessionWith TraceEnabled) of
        Right firstRun, Right secondRun -> do
          secondRun.first `shouldEqual` firstRun.first
          secondRun.equation `shouldEqual` firstRun.equation
          secondRun.report `shouldEqual` firstRun.report
          secondRun.core `shouldEqual` firstRun.core
          (secondRun.state == firstRun.state) `shouldEqual` true
          secondRun.state.retained.trace `shouldEqual` firstRun.state.retained.trace
          let
            events = firstRun.state.retained.trace
            conversations = Array.mapMaybe
              ( case _ of
                  AttemptOpened e -> Just e.conversation
                  _ -> Nothing
              )
              events
          case conversations of
            [ waited, retried ] -> do
              -- The attempt that waited is rolled back whole.
              Array.nub (fatesWhere (inConversation waited) events) `shouldEqual` [ RolledBack ]
              -- `cand0` is passed over in a transaction that commits; `cand1`
              -- fails in its own; `cand2` answers, and the attempt finishes.
              fatesWhere (inConversation retried && commanded (Kernel (ObserveRequest (LookupGlobal cand0)))) events `shouldEqual` [ Kept ]
              fatesWhere (inConversation retried && refersTo cand1) events `shouldEqual` [ RolledBack ]
              fatesWhere (inConversation retried && refersTo cand2) events `shouldEqual` [ Kept ]
              fatesWhere (inConversation retried && finishing) events `shouldEqual` [ Kept ]
            other -> fail ("expected two conversations: " <> show other)
        Left err, _ -> fail err
        _, Left err -> fail err
  where
  ask request c = command (envelopeOf c) (Kernel request) c

  fatesWhere holds events = Array.catMaybes (Array.zipWith (\event fate -> if holds event then Just fate else Nothing) events (fates events))

  inConversation c = case _ of
    AttemptOpened e -> e.conversation == c
    CommandHandled e -> e.conversation == c
    AttemptAbandoned e -> e.conversation == c
    AttemptCancelled e -> e.conversation == c
    AttemptNotOpened _ -> false

  commanded sent = case _ of
    CommandHandled e -> e.command == sent
    _ -> false

  refersTo name = case _ of
    CommandHandled { command: Kernel (TermRequest (GlobalRef _ referred _)) } -> referred == name
    _ -> false

  finishing = case _ of
    CommandHandled { command: Finish _ } -> true
    _ -> false

  describeStep :: forall a. Show a => Step a -> P.String
  describeStep = case _ of
    Answered (Returned a) _ -> "returned " <> show a
    Answered (CandidateFailed token d) _ -> "failed in " <> show token <> ": " <> show d
    Finished attempt _ -> "finished: " <> show attempt

working :: Qualified Ident
working = Qualified (ModuleName "Synth") (Ident "working")

-- | A goal at `?a` asked of the synthesizer named where `x : Int` is bound,
-- | queued, with `?a` created before it.
type Waiting = { a :: MetaVar, id :: PendingId, target :: TermMetaVar, site :: Site, queued :: SolverState }

waiting :: Qualified Ident -> Either P.String Waiting
waiting name = case runElabIn session (initialState (SessionId 0) 10) created of
  Tuple (Done (Tuple (XMeta a) (Tuple id target))) queued -> Right { a, id, target, site, queued }
  Tuple other _ -> Left (show other)
  where
  site = siteBinding [ Tuple x xInt ]
  created = do
    a <- freshTypeMeta emptyXContext XKType
    goal <- createSynthesis site a name
    pure (Tuple a goal)

-- | A goal at `Record (a : ?t, z : Int)` asked of the synthesizer named where
-- | nothing is bound, queued, with `?t` created before it.
recordGoal :: Qualified Ident -> Either P.String { t :: MetaVar, target :: TermMetaVar, queued :: SolverState }
recordGoal name = case runElabIn session (initialState (SessionId 0) 10) created of
  Tuple (Done (Tuple (XMeta t) target)) queued -> Right { t, target, queued }
  Tuple other _ -> Left (show other)
  where
  created = do
    t <- freshTypeMeta emptyXContext XKType
    let
      goalType = XApp (XCon recordTy []) (XRowExtend (XRowTypeEntry keyA t) (XRowExtend (XRowTypeEntry keyZ xInt) XRowEmpty))
    Tuple _ target <- createSynthesis (siteBinding []) goalType name
    pure (Tuple t target)

-- | `Record (a : Boolean, z : Int)`, the type `cand2` answers.
answerType :: XType
answerType = fromCore (recordOf coreBoolean coreInt)

-- | The module declaring what `Main` declares, then the declaration named, at
-- | the type given, with the right-hand side given.
completedWith :: P.String -> Type -> Expr P.Int -> Module P.Int
completedWith name ty value =
  valuesModule { decls = valuesModule.decls <> [ DeclNonRec 1 { name: Ident name, scheme: monoScheme ty, value, attributes: [] } ] }

-- | Every step of carrying `let y : ?g = ?m in y` to the Core boundary, and what
-- | each came to.
type Scenario =
  { first :: Submission
  , equation :: Submission
  , report :: RunReport
  , g :: MetaVar
  , zonked :: XExpr P.Int
  , core :: Either (NonEmptyArray (Residue P.Int)) (Expr P.Int)
  , state :: SolverState
  }

-- | `answer = let y : ?g = ?m in y`, `?m` a goal at `?g`: the goal submitted,
-- | and waiting on `?g`; the equation `?g ≡ Record (a : Boolean, z : Int)`
-- | submitted through the same attempter, which wakes it; the loop run, the
-- | retry searching the candidates; and the right-hand side zonked and taken
-- | across the boundary.
scenario :: SessionEnv -> Either P.String Scenario
scenario env = case runElabIn env (initialState (SessionId 0) 10) (freshTypeMeta emptyXContext XKType) of
  Tuple (Done (XMeta g)) s0 ->
    let
      Tuple submitted s1 = submitSynthesis env registry (siteBinding []) (XMeta g) resolver s0
      Tuple equation s2 = submitAttempting (attemptJob env registry) (siteBinding []) (JobUnify { kind: XKType, left: XMeta g, right: answerType }) s1
      Tuple report s3 = runSynthesis env registry s2
      zonked = zonkExpr s3.tentative.metas (ELet 0 y (XMeta g) (ETermMeta 7 submitted.target) (EVar 0 y))
    in
      Right { first: submitted.submission, equation, report, g, zonked, core: toCoreExpr zonked, state: s3 }
  Tuple other _ -> Left (show other)

-- | Whether the target is held, and unsolved.
unsolved :: SolverState -> TermMetaVar -> P.Boolean
unsolved s m = case lookupTermMeta s.tentative.metas m of
  Just (TermUnsolved _) -> true
  _ -> false
