-- | Synthesis jobs run by the scheduler: submitted, retried by the loop, and
-- | carried out by the synthesizer their goal names in the registry.
-- |
-- | Three things are what these cases are for. **A job's lifecycle is the
-- | scheduler's whatever runs it**: a result assigned and the job gone, a
-- | failure reported and the job gone, a defect stopping everything with the
-- | jobs after it left where they were. **A synthesizer is resolved once its
-- | attempt has opened**, so a malformed job is reported as that before a
-- | missing synthesizer is, and a missing one abandons an attempt that asked
-- | nothing. And **one loop runs every kind of job**, a subgoal a synthesizer
-- | asked for among them, and a subgoal asked for by an attempt that fails goes
-- | with it.
module Test.Stella.Compiler.Elaborate.Synthesis (spec) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.CorePlus.Context (Origin(..), emptyXContext)
import Stella.Compiler.Elaborate.CorePlus.Kind (XKind(..))
import Stella.Compiler.Elaborate.CorePlus.Term (TermMetaVar, XExpr(..))
import Stella.Compiler.Elaborate.CorePlus.Type (XType(..))
import Stella.Compiler.Elaborate.Driver.Attempt (Attempt(Committed), runAttempt)
import Stella.Compiler.Elaborate.Driver.Attempt as Run
import Stella.Compiler.Elaborate.Driver.Loop (RunResult(..), Submission(..), submitAttempting)
import Stella.Compiler.Elaborate.Driver.Synthesis (Registry, attemptJob, runSynthesis, submitSynthesis)
import Stella.Compiler.Elaborate.Environment.Catalog (catalogOf)
import Stella.Compiler.Elaborate.Environment.Constructors (emptyConstructorEnv)
import Stella.Compiler.Elaborate.Environment.Effects (emptyEffectEnv)
import Stella.Compiler.Elaborate.Kernel.Elab (Outcome(..), SessionEnv, SolverState, assignTerm, createSynthesis, freshTypeMeta, initialState, runElabIn)
import Stella.Compiler.Elaborate.Mechanism.Kinding (kindingOf)
import Stella.Compiler.Elaborate.Mechanism.Pending (Job(..), PendingId(..), Site)
import Stella.Compiler.Elaborate.Mechanism.Scheduler (lookupPending, nextReady, takeReady)
import Stella.Compiler.Elaborate.Mechanism.TermMeta (zonkExpr)
import Stella.Compiler.Elaborate.Mechanism.Unify (TermBinding(..), lookupTermMeta)
import Stella.Compiler.Elaborate.Protocol.Facade (Synthesizer)
import Stella.Compiler.Elaborate.Protocol.Facade as F
import Stella.Compiler.Elaborate.Vocabulary.Diagnostic (Defect(..), Diagnostic(..), MalformedGoal(..))
import Stella.Compiler.Elaborate.Vocabulary.Handle (SessionId(..))
import Stella.Compiler.Elaborate.Vocabulary.Message (MessagePart(..))
import Stella.Compiler.Elaborate.Vocabulary.Trace (TraceEvent(..), Tracing(..))
import Stella.Compiler.Elaborate.Vocabulary.View (TypeView(..))
import Stella.Compiler.TypedCore (Ident(..), Literal(..), ModuleName(..), Qualified(..))
import Stella.Compiler.TypedCore.Prim (intTy, primSignature)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Map as Map
import Data.Maybe (Maybe(..), isNothing)
import Data.Tuple (Tuple(..))
import Effect.Aff (Aff)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

xInt :: XType
xInt = XCon intTy []

session :: SessionEnv
session =
  { catalog: catalogOf []
  , kinding: kindingOf primSignature
  , constructors: emptyConstructorEnv
  , effects: emptyEffectEnv
  , tracing: TraceEnabled
  }

site :: Site
site = { context: emptyXContext, origin: InDeclaration (Qualified (ModuleName "Main") (Ident "decl")) }

named :: P.String -> Qualified Ident
named name = Qualified (ModuleName "Synth") (Ident name)

-- | Answers `1`.
answerOne :: Synthesizer
answerOne _ = F.rootScope >>= \root -> F.literal root (LitInt 1)

-- | Fails.
refusing :: Synthesizer
refusing _ = F.throw [ TextPart "no" ]

-- | Misuses the kernel: a variable nothing binds.
misusing :: Synthesizer
misusing _ = F.rootScope >>= \root -> F.localVariable root (Ident "missing")

-- | Waits on the goal's type while it is a metavariable, and answers `1` once
-- | it is not.
patient :: Synthesizer
patient goal = F.goalType goal >>= F.viewType >>= case _ of
  MetaType m -> F.postpone [ m ]
  _ -> answerOne goal

-- | Asks `inner` for a term at `Int`, and answers it.
outer :: Synthesizer
outer _ = do
  root <- F.rootScope
  i <- F.typeConstructor root intTy []
  F.subgoal root i (named "inner")

-- | Asks `inner` for a term at `Int`, then fails.
outerFailing :: Synthesizer
outerFailing goal = outer goal *> F.throw [ TextPart "no" ]

registry :: Registry
registry = Map.fromFoldable
  [ Tuple (named "one") answerOne
  , Tuple (named "refusing") refusing
  , Tuple (named "misusing") misusing
  , Tuple (named "patient") patient
  , Tuple (named "outer") outer
  , Tuple (named "outerFailing") outerFailing
  , Tuple (named "inner") answerOne
  ]

start :: SolverState
start = initialState (SessionId 0) 10

-- | Goals at `Int` asked of the synthesizers named, queued in that order from
-- | inside an attempt, with their jobs and targets.
queued :: P.Array P.String -> Either P.String (Tuple (P.Array { id :: PendingId, target :: TermMetaVar }) SolverState)
queued names = case runElabIn session start (Array.foldM ask [] names) of
  Tuple (Done goals) s -> Right (Tuple goals s)
  Tuple other _ -> Left (show other)
  where
  ask acc name = createSynthesis site xInt (named name) <#> \(Tuple id target) -> Array.snoc acc { id, target }

givenQueued :: P.Array P.String -> (P.Array { id :: PendingId, target :: TermMetaVar } -> SolverState -> Aff Unit) -> Aff Unit
givenQueued names check = case queued names of
  Right (Tuple goals s) -> check goals s
  Left err -> fail err

assigned :: SolverState -> TermMetaVar -> Maybe (XExpr Unit)
assigned s m = case lookupTermMeta s.tentative.metas m of
  Just (TermAssigned e) -> Just e
  _ -> Nothing

-- | Whether the target is held, and unsolved.
unsolved :: SolverState -> TermMetaVar -> P.Boolean
unsolved s m = case lookupTermMeta s.tentative.metas m of
  Just (TermUnsolved _) -> true
  _ -> false

-- | Whether the scheduler holds no job at all, on a queue or off one.
noJobs :: SolverState -> P.Boolean
noJobs s = Map.isEmpty s.tentative.scheduler.pending

-- | A synthesis submitted at `Int` from outside every attempt.
submitted :: P.String -> Tuple { target :: TermMetaVar, submission :: Submission } SolverState
submitted name = submitSynthesis session registry site xInt (named name) start

spec :: Spec Unit
spec = describe "Elaborate.Driver.Synthesis" do
  describe "a job submitted" do
    it "whose synthesizer answers has its target assigned, and is gone" do
      case submitted "one" of
        Tuple { target, submission: Continue { id, attempt: Committed } } s -> do
          assigned s target `shouldEqual` Just (ELit unit (LitInt 1))
          isNothing (lookupPending s.tentative.scheduler id) `shouldEqual` true
        Tuple { submission } _ -> fail (show (stopOrGoOn submission))

    it "whose synthesizer fails stops with the failure, its target unassigned" do
      case submitted "refusing" of
        Tuple { target, submission: Stop report } s -> do
          case report.result of
            Rejected (SynthesisFailed _) -> pure unit
            other -> fail (show other)
          unsolved s target `shouldEqual` true
          noJobs s `shouldEqual` true
        Tuple { submission } _ -> fail (show (stopOrGoOn submission))

  describe "the loop" do
    it "runs a queued job by the synthesizer its goal names" do
      givenQueued [ "one" ] \goals s0 -> case runSynthesis session registry s0 of
        Tuple report s -> do
          report.result `shouldEqual` Completed
          map (assigned s <<< _.target) goals `shouldEqual` [ Just (ELit unit (LitInt 1)) ]

    it "stops at a failure, the job gone and its target unassigned" do
      givenQueued [ "refusing" ] \goals s0 -> case runSynthesis session registry s0 of
        Tuple report s -> do
          case report.result of
            Rejected (SynthesisFailed _) -> pure unit
            other -> fail (show other)
          noJobs s `shouldEqual` true
          map (unsolved s <<< _.target) goals `shouldEqual` [ true ]

    it "stops at a defect, and runs no job after it" do
      givenQueued [ "misusing", "one" ] \goals s0 -> case runSynthesis session registry s0 of
        Tuple report s -> do
          case report.result of
            Halted (BuildRejected _) -> pure unit
            other -> fail (show other)
          map (unsolved s <<< _.target) goals `shouldEqual` [ true, true ]
          map _.id (Array.drop 1 goals) `shouldEqual` Array.fromFoldable (map _.id (nextReady s.tentative.scheduler))

    it "runs an equation and a synthesis alike, each by its own runner" do
      let
        -- A goal at `?a`, which waits until an equation solves `?a`.
        created = do
          a <- freshTypeMeta emptyXContext XKType
          Tuple id target <- createSynthesis site a (named "patient")
          pure { a, id, target }
      case runElabIn session start created of
        Tuple (Done made) s0 -> do
          let
            Tuple first s1 = runSynthesis session registry s0
            Tuple equation s2 = submitAttempting (attemptJob session registry) site (JobUnify { kind: XKType, left: made.a, right: xInt }) s1
            Tuple second s3 = runSynthesis session registry s2
          case first.result of
            Blocked _ -> pure unit
            other -> fail ("the goal did not wait: " <> show other)
          case equation of
            Continue { attempt: Committed } -> pure unit
            other -> fail (show (stopOrGoOn other))
          second.result `shouldEqual` Completed
          assigned s3 made.target `shouldEqual` Just (ELit unit (LitInt 1))
        Tuple other _ -> fail (show other)

  describe "a subgoal" do
    it "is run by the loop from the same registry, and fills the goal that asked for it" do
      givenQueued [ "outer" ] \goals s0 -> case runSynthesis session registry s0 of
        Tuple report s -> do
          report.result `shouldEqual` Completed
          map (\g -> zonkExpr s.tentative.metas (ETermMeta unit g.target)) goals `shouldEqual` [ ELit unit (LitInt 1) ]

    it "asked for by an attempt that fails goes with it" do
      givenQueued [ "outerFailing" ] \_ s0 -> case runSynthesis session registry s0 of
        Tuple report s -> do
          case report.result of
            Rejected (SynthesisFailed _) -> pure unit
            other -> fail (show other)
          noJobs s `shouldEqual` true

  describe "a job the scheduler does not hold" do
    it "is reported by the host's runner, and not traced as a synthesis attempt" do
      case attemptJob session registry absent start of
        Tuple attempt s -> do
          attempt `shouldEqual` Run.Halted (PendingAbsent absent)
          map kind s.retained.trace `shouldEqual` []

  describe "a synthesizer the registry does not hold" do
    it "is a defect of the session, the attempt opened and abandoned without a command" do
      case submitSynthesis session registry site xInt (named "missing") start of
        Tuple { submission: Stop report } s -> do
          report.result `shouldEqual` Halted (SynthesizerUnavailable (named "missing"))
          map kind s.retained.trace `shouldEqual` [ "opened", "abandoned" ]
        Tuple { submission } _ -> fail (show (stopOrGoOn submission))

    it "is reported after a malformed target, the attempt not opened" do
      givenQueued [ "missing" ] \goals s0 -> case Array.head goals of
        Just goal -> do
          let
            -- The target solved before the job is attempted.
            Tuple _ s1 = runAttempt session (assignTerm site goal.target (ELit unit (LitInt 1))) s0
          case takeReady s1.tentative.scheduler of
            Just (Tuple id scheduler) -> case attemptJob session registry id (s1 { tentative { scheduler = scheduler } }) of
              Tuple attempt s -> do
                attempt `shouldEqual` Run.Halted (MalformedSynthesisJob id (TargetSolved goal.target))
                map kind s.retained.trace `shouldEqual` [ "not opened" ]
            Nothing -> fail "no job was queued"
        Nothing -> fail "no goal was asked"
  where
  kind = case _ of
    AttemptOpened _ -> "opened"
    AttemptNotOpened _ -> "not opened"
    CommandHandled _ -> "command"
    AttemptAbandoned _ -> "abandoned"
    AttemptCancelled _ -> "cancelled"

  absent = PendingId 99

  stopOrGoOn = case _ of
    Continue submitted' -> "went on: " <> show submitted'.attempt
    Stop report -> "stopped: " <> show report.result
