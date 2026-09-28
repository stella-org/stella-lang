-- | Hand-written Core⁺ with a synthesis hole in it, the hole filled by the
-- | reference synthesizer through the scheduler, and the term zonked.
-- |
-- | ```text
-- | Core⁺ with ?m → a goal queued → the loop → the reference synthesizer
-- |   → the target assigned → Completed → zonk
-- | ```
-- |
-- | Three things are what these cases are for. **A goal is answered from where
-- | it was asked**: the synthesizer reads the goal's type and the bindings of
-- | the site it was created at, however late the loop runs it, each goal its
-- | own. **The answer lands where the hole stood**: zonked, the hole is the term
-- | the synthesizer built, carrying the hole's annotation. And **a goal that
-- | waits is run again from its beginning**: the attempt that waited leaves
-- | nothing it built, the job holds only its description, the retry alone
-- | spends fuel, and a handle the waiting attempt was given is refused when it
-- | is presented again.
module Test.Stella.Compiler.Elaborate.SynthesisVertical (spec) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.CorePlus.Context (Origin(..), bindVar, emptyXContext)
import Stella.Compiler.Elaborate.CorePlus.Term (TermMetaVar, XExpr(..))
import Stella.Compiler.Elaborate.CorePlus.Type (MetaVar, XType(..))
import Stella.Compiler.Elaborate.CorePlus.Kind (XKind(..))
import Stella.Compiler.Elaborate.Driver.Attempt (Attempt(Committed, Registered), OpenResult(..), Response(..), Step(..), envelopeOf)
import Stella.Compiler.Elaborate.Driver.Conversation (command, openConversation)
import Stella.Compiler.Elaborate.Driver.Loop (RunResult(..), Submission(..), submitAttempting)
import Stella.Compiler.Elaborate.Driver.Synthesis (Registry, attemptJob, runSynthesis)
import Stella.Compiler.Elaborate.Environment.Catalog (EntrySort(..), catalogOf)
import Stella.Compiler.Elaborate.Environment.Constructors (constructorsOf)
import Stella.Compiler.Elaborate.Environment.Effects (effectsOf)
import Stella.Compiler.Elaborate.Kernel.Elab (Outcome(..), SessionEnv, SolverState, createSynthesis, freshTypeMeta, initialState, runElabIn)
import Stella.Compiler.Elaborate.Mechanism.Kinding (kindingOf)
import Stella.Compiler.Elaborate.Mechanism.Pending (Job(..), PendingId, Site)
import Stella.Compiler.Elaborate.Mechanism.Scheduler (Phase(..), lookupPending, nextReady, takeReady)
import Stella.Compiler.Elaborate.Mechanism.TermMeta (zonkExpr)
import Stella.Compiler.Elaborate.Mechanism.Unify (TermBinding(..), lookupTermMeta)
import Stella.Compiler.Elaborate.Protocol.Facade as F
import Stella.Compiler.Elaborate.Vocabulary.Diagnostic (Defect(..), Diagnostic(..))
import Stella.Compiler.Elaborate.Vocabulary.Handle (HandleError(..), SessionId(..), emptyArena)
import Stella.Compiler.Elaborate.Vocabulary.Message (MessagePart(..))
import Stella.Compiler.Elaborate.Vocabulary.Request (Command(..), CommandAnswer(..), KernelAnswer(..), BuildRequest(..), KernelRequest(..), ObserveRequest(..), ReportRequest(..), SolveRequest(..))
import Stella.Compiler.Elaborate.Vocabulary.Trace (Tracing(..))
import Stella.Compiler.Elaborate.Vocabulary.View (ConstraintView(..), KindView(..), TypeView(..))
import Stella.Compiler.TypedCore (Decl(..), Expr(..), Ident(..), Literal(..), Module, ModuleName(..), Qualified(..), RowElemKind(..), RowKey(..), Symbol(..), Type(..), monoScheme)
import Stella.Compiler.TypedCore.Declare (declare)
import Stella.Compiler.TypedCore.Prim (booleanTy, intTy, primSignature)
import Stella.Compiler.TypedCore.Signature (Signature)
import Data.Either (Either(..), either)
import Data.Foldable (foldl)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Effect.Aff (Aff)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)
import Test.Stella.Compiler.Elaborate.Reference (reference, workingWhileWaiting)

main :: ModuleName
main = ModuleName "Main"

mainOne :: Qualified Ident
mainOne = Qualified main (Ident "one")

xInt :: XType
xInt = XCon intTy []

xBoolean :: XType
xBoolean = XCon booleanTy []

-- | `one = 1`, a monomorphic global at `Int`.
valuesModule :: Module P.Int
valuesModule =
  { annotation: 0
  , name: main
  , imports: []
  , exports: []
  , decls: [ DeclNonRec 1 { name: Ident "one", scheme: monoScheme (TCon intTy []), value: Lit 1 (LitInt 1), attributes: [] } ]
  }

signature :: Signature
signature = either (const primSignature) identity (declare primSignature valuesModule)

session :: SessionEnv
session =
  { catalog: catalogOf [ { name: mainOne, sort: ValueEntry, scheme: { kindVars: [], body: xInt }, attributes: [] } ]
  , kinding: kindingOf signature
  , constructors: constructorsOf signature
  , effects: effectsOf signature
  , tracing: TraceDisabled
  }

resolver :: Qualified Ident
resolver = Qualified (ModuleName "Synth") (Ident "reference")

registry :: Registry
registry = Map.fromFoldable
  [ Tuple resolver (reference [ mainOne ])
  , Tuple working (workingWhileWaiting (reference [ mainOne ]))
  ]

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
  ask (Tuple site ty) = createSynthesis site ty resolver Nothing <#> \(Tuple _ target) -> target

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
  where
  ask request c = command (envelopeOf c) (Kernel request) c

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
    goal <- createSynthesis site a name Nothing
    pure (Tuple a goal)

-- | Whether the target is held, and unsolved.
unsolved :: SolverState -> TermMetaVar -> P.Boolean
unsolved s m = case lookupTermMeta s.tentative.metas m of
  Just (TermUnsolved _) -> true
  _ -> false
