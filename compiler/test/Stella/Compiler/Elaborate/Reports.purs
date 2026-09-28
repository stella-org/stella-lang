-- | How a synthesizer fails and warns.
-- |
-- | Three things are what these cases are for. **A report is frozen where it is
-- | made**: its handles resolved and what they hold zonked then, with the goal
-- | it is about, so that nothing it shows changes after. **A warning is kept only
-- | where what made it commits**: an attempt that fails, postpones, or breaks,
-- | and a candidate a `transact` discards, leave none, and a goal run again
-- | reports its warning once. And **what commits is reported once**: the loop
-- | drains it where it stops.
module Test.Stella.Compiler.Elaborate.Reports (spec) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.Trace (Tracing(..))
import Stella.Compiler.Elaborate.Build (closeForall, openForall, rootScope, typeConstructor)
import Stella.Compiler.Elaborate.BuildTerm (literal)
import Stella.Compiler.Elaborate.Catalog (catalogOf)
import Stella.Compiler.Elaborate.Constructors (emptyConstructorEnv)
import Stella.Compiler.Elaborate.Context (Origin(..), emptyXContext)
import Stella.Compiler.Elaborate.Diagnostic (Defect(..), Diagnostic(..))
import Stella.Compiler.Elaborate.Effects (emptyEffectEnv)
import Stella.Compiler.Elaborate.Elab (Elab, Outcome(..), SessionEnv, SolverState, break, createSynthesis, currentMetas, freshTypeMeta, initialState, postpone, runElabIn, transact, unify, withFrame)
import Stella.Compiler.Elaborate.Handle (HandleClass(..), HandleError(..), SessionId(..))
import Stella.Compiler.Elaborate.Kind (XKind(..))
import Stella.Compiler.Elaborate.Kinding (KindEvidence(..), kindingOf)
import Stella.Compiler.Elaborate.Loop (RunResult(Completed, Halted, Rejected), Submission(..), runWith, submitEquality, submitWith)
import Stella.Compiler.Elaborate.Message (FrozenMessagePart(..), MessagePart(..))
import Stella.Compiler.Elaborate.Observe (viewType)
import Stella.Compiler.Elaborate.Pending (Job(..), Pending, PendingId, Site, newGoal)
import Stella.Compiler.Elaborate.Report (throw, warn)
import Stella.Compiler.Elaborate.Run (Attempt(Committed), attemptPendingWith, runAttempt)
import Stella.Compiler.Elaborate.Run as Run
import Stella.Compiler.Elaborate.Scheduler (takeReady)
import Stella.Compiler.Elaborate.Solve (freshMetaType)
import Stella.Compiler.Elaborate.Solve as Solve
import Stella.Compiler.Elaborate.Term (XExpr(..))
import Stella.Compiler.Elaborate.Type (MetaVar, XType(..))
import Stella.Compiler.Elaborate.Unify (MetaBinding(..), lookupMeta)
import Stella.Compiler.Elaborate.View (KindView(..), TypeView(..))
import Stella.Compiler.TypedCore (Ident(..), Literal(..), ModuleName(..), Qualified(..), TyName(..))
import Stella.Compiler.TypedCore.Prim (intTy, primSignature)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Data.Tuple (Tuple(..), fst)
import Effect.Aff (Aff)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

xInt :: XType
xInt = XCon intTy []

session :: SessionEnv
session = { catalog: catalogOf [], kinding: kindingOf primSignature, constructors: emptyConstructorEnv, effects: emptyEffectEnv, tracing: TraceDisabled }

resolver :: Qualified Ident
resolver = Qualified (ModuleName "Typeclass") (Ident "resolve")

site :: Site
site = { context: emptyXContext, origin: InDeclaration (Qualified (ModuleName "Main") (Ident "decl")) }

-- | A goal at `Int`, created and queued, and a type metavariable `?a` beside
-- | it.
type Asked = { id :: PendingId, a :: MetaVar, queued :: SolverState }

asked :: Either P.String Asked
asked = case runElabIn session (initialState (SessionId 0) 10) created of
  Tuple (Done (Tuple id (XMeta a))) queued -> Right { id, a, queued }
  Tuple other _ -> Left (show other)
  where
  created = do
    Tuple id _ <- createSynthesis site xInt resolver Nothing
    a <- freshTypeMeta emptyXContext XKType
    pure (Tuple id a)

-- | The goal attempted once by the runner given, taken from the ready queue.
attemptWith :: Asked -> (Pending -> Elab Unit) -> Tuple Attempt SolverState
attemptWith g runner = case takeReady g.queued.tentative.scheduler of
  Just (Tuple id taken) -> attemptPendingWith session runner id (g.queued { tentative { scheduler = taken } })
  Nothing -> Tuple (Run.Halted (PendingAbsent g.id)) g.queued

given :: (Asked -> Aff Unit) -> Aff Unit
given check = case asked of
  Right g -> check g
  Left err -> fail err

text :: P.String -> P.Array MessagePart
text t = [ TextPart t ]

spec :: Spec Unit
spec = describe "Elaborate.Report" do
  describe "throw" do
    it "fails with the message frozen, and the goal it is about" do
      given \g -> do
        let
          throwing _ = do
            root <- rootScope
            i <- typeConstructor root intTy []
            one <- literal root (LitInt 1)
            throw [ TextPart "no instance for", TypePart i, TermPart one, NamePart resolver ]
        fst (attemptWith g throwing) `shouldEqual`
          Run.Rejected
            ( SynthesisFailed
                { goal: { origin: site.origin, pending: g.id, synthesizer: resolver, expectedType: xInt }
                , message:
                    [ FrozenText "no instance for"
                    , FrozenType { type: xInt, kind: ExactKind XKType }
                    , FrozenTerm { term: ELit unit (LitInt 1), claimed: xInt }
                    , FrozenName resolver
                    ]
                }
            )

    it "is a synthesizer's, and a frame running no goal has none to report on" do
      case fst (runElabIn session (initialState (SessionId 0) 10) (withFrame { site, goal: Nothing } (throw (text "no") :: Elab Unit))) of
        Broke NoGoal -> pure unit
        other -> fail ("expected a defect: " <> show other)

  describe "a message's handles" do
    it "are shown whatever scope they were built in, and must be of the class named" do
      given \g -> do
        let
          underBinder _ = do
            root <- rootScope
            opened <- openForall root "t" KindType
            whole <- closeForall root opened.binder opened.variable
            viewType whole >>= case _ of
              ForallType _ _ body -> warn [ TypePart body ]
              _ -> throw (text "not a forall")
          wrongClass _ = do
            root <- rootScope
            warn [ TypePart root ]
        fst (attemptWith g underBinder) `shouldEqual` Committed
        case fst (attemptWith g wrongClass) of
          Run.Halted (InvalidHandle _ (HandleClassMismatch TypeClass)) -> pure unit
          other -> fail ("expected the handle to be refused: " <> show other)

    it "are frozen where the message is made, and do not change as Ψ does" do
      given \g -> do
        let
          warnedThenSolved _ = do
            root <- rootScope
            m <- freshMetaType root KindType
            warn [ TypePart m ]
            typeConstructor root intTy [] >>= Solve.unify root m
        case runWith session warnedThenSolved g.queued of
          Tuple report _ -> case report.warnings of
            [ { message: [ FrozenType { type: XMeta _ } ] } ] -> pure unit
            other -> fail ("expected the metavariable as it was: " <> show other)

  describe "a warning" do
    it "is kept where the attempt commits, and not where a transact discards the candidate" do
      given \g -> do
        let
          runner _ = do
            _ <- transact (warn (text "discarded") *> throw (text "no"))
            warn (text "kept")
        case runWith session runner g.queued of
          Tuple report s -> do
            report.result `shouldEqual` Completed
            map _.message report.warnings `shouldEqual` [ [ FrozenText "kept" ] ]
            s.tentative.warnings `shouldEqual` []

    it "is not kept where the attempt postpones, fails, or breaks" do
      given \g -> do
        let
          postponing _ = warn (text "w") *> postpone (Set.singleton g.a)
          failing _ = warn (text "w") *> throw (text "no")
          breaking _ = warn (text "w") *> break (SynthesizerUnavailable resolver)
          journal runner = (attemptWith g runner # \(Tuple _ s) -> s.tentative.warnings)
        journal postponing `shouldEqual` []
        journal failing `shouldEqual` []
        journal breaking `shouldEqual` []

    it "of a goal run again is reported once, by the run that commits" do
      given \g -> do
        let
          -- Warns, and waits on `?a` while it is unsolved.
          runner _ = do
            warn (text "w")
            metas <- currentMetas
            case lookupMeta metas g.a of
              Just (Unsolved _) -> postpone (Set.singleton g.a)
              _ -> pure unit
          Tuple first s1 = runWith session runner g.queued
          Tuple _ s2 = runAttempt session (unify site { kind: XKType, left: XMeta g.a, right: xInt }) s1
          Tuple second _ = runWith session runner s2
        first.warnings `shouldEqual` []
        second.result `shouldEqual` Completed
        map _.message second.warnings `shouldEqual` [ [ FrozenText "w" ] ]

    it "committed before a submission that stops is drained into the report it stops with" do
      let
        initial = initialState (SessionId 0) 10
        Tuple record metas = newGoal site xInt resolver Nothing initial.tentative.metas
        start = initial { tentative { metas = metas } }
        warning = [ FrozenText "from A" ]
        -- A warns and commits; B fails, or breaks.
        Tuple a s1 = submitWith session (\_ -> warn (text "from A")) site (JobSynthesis record) start
        Tuple failed s2 = submitEquality session site { kind: XKType, left: xInt, right: XCon (Qualified (ModuleName "Prim") (TyName "Boolean")) [] } s1
        Tuple broken s3 = submitWith session (\_ -> break (SynthesizerUnavailable resolver)) site (JobUnify { kind: XKType, left: xInt, right: xInt }) s1
      case a of
        Continue _ -> pure unit
        other -> fail ("A did not go on: " <> show other)
      case failed of
        Stop report -> do
          case report.result of
            Rejected _ -> pure unit
            other -> fail ("B was not rejected: " <> show other)
          map _.message report.warnings `shouldEqual` [ warning ]
        other -> fail ("B did not stop: " <> show other)
      s2.tentative.warnings `shouldEqual` []
      case broken of
        Stop report -> do
          report.result `shouldEqual` Halted (SynthesizerUnavailable resolver)
          map _.message report.warnings `shouldEqual` [ warning ]
        other -> fail ("B did not stop: " <> show other)
      s3.tentative.warnings `shouldEqual` []
