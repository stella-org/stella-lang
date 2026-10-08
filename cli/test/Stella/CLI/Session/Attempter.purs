-- | The scheduler's attempts carried out on one session: a synthesis job by its
-- | guest, an equation by the host.
-- |
-- | The session is a process written inline standing in for Steam, as the broker's
-- | cases have it: each `invoke` notes the global, the attempt, and the budget it was
-- | given, then asks for its goal's type, waits where that is a metavariable, and
-- | otherwise answers `1`.
module Test.Stella.CLI.Session.Attempter (spec) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Effect.Aff (Aff, Milliseconds(..))
import Effect.Class (liftEffect)
import Effect.Ref as Ref
import Stella.CLI.Session.Broker (SessionHealth(..), cancel, newCancellation)
import Stella.CLI.Session.Broker.Attempter (Guests, Interrupted(..), lastAttempt, runGuests, submitGuest, submitGuestSynthesis)
import Stella.CLI.Session.Client (Session)
import Stella.Compiler.Elaborate.CorePlus.Context (Origin(..), emptyXContext)
import Stella.Compiler.Elaborate.CorePlus.Kind (XKind(..))
import Stella.Compiler.Elaborate.CorePlus.Type (XType(..))
import Stella.Compiler.Elaborate.Driver.Loop (RunResult(..), Submission(..))
import Stella.Compiler.Elaborate.Environment.Catalog (catalogOf)
import Stella.Compiler.Elaborate.Environment.Constructors (constructorsOf)
import Stella.Compiler.Elaborate.Environment.Effects (effectsOf)
import Stella.Compiler.Elaborate.Kernel.Elab (Outcome(..), SessionEnv, SolverState, freshTypeMeta, initialState, runElabIn)
import Stella.Compiler.Elaborate.Mechanism.Kinding (kindingOf)
import Stella.Compiler.Elaborate.Mechanism.Pending (Job(..), Site)
import Stella.Compiler.Elaborate.Mechanism.Scheduler (create, enqueueInitial)
import Stella.Compiler.Elaborate.Mechanism.Unify (MetaBinding(..), lookupMeta)
import Stella.Compiler.Elaborate.Vocabulary.Diagnostic (Defect(..))
import Stella.Compiler.Elaborate.Vocabulary.Handle (SessionId(..))
import Stella.Compiler.Elaborate.Vocabulary.Trace (TraceEvent(..), Tracing(..))
import Stella.Compiler.TypedCore (Ident(..), ModuleName(..), Qualified(..))
import Stella.Compiler.TypedCore.Prim (intTy, primSignature)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)
import Test.Stella.CLI.Session.Broker (descriptor, node, withSession)

env :: SessionEnv
env =
  { catalog: catalogOf []
  , kinding: kindingOf primSignature
  , constructors: constructorsOf primSignature
  , effects: effectsOf primSignature
  , tracing: TraceEnabled
  }

site :: Site
site = { context: emptyXContext, origin: InDeclaration (Qualified (ModuleName "User") (Ident "answer")) }

synth :: Qualified Ident
synth = Qualified (ModuleName "Synth") (Ident "synth")

xInt :: XType
xInt = XCon intTy []

-- | A state with `?a` created in it, and `?a`.
withA :: Either String { a :: XType, state :: SolverState }
withA = case runElabIn env (initialState (SessionId 1) 10) (freshTypeMeta emptyXContext XKType) of
  Tuple (Done a) s -> Right { a, state: s }
  Tuple other _ -> Left (show other)

-- | The guest: note what it was invoked with, ask for its goal's type, wait on it
-- | where it is a metavariable, and otherwise answer `1`.
waiting :: String
waiting = "const guest = async (p) => { const a = p.attempt;"
  <> " note(p.global.module + '.' + p.global.name + ' ' + a + ' ' + p.budget);"
  <> " const t = handleOf(await kernel(a, cmd('ObserveRequest', d('GoalType', [{ token: p.arguments[0] }]))));"
  <> " const v = await kernel(a, cmd('ObserveRequest', d('ViewType', [{ token: t }])));"
  <> " const view = v.payload.answer.fields[0].fields[0];"
  <> " if (view.data.name === 'MetaType') { note((await kernel(a, cmd('ReportRequest', d('Postpone', [list([view.fields[0]])])))).kind); return failed('abandoned'); }"
  <> " return returned(await answerOne(a)); };"

-- | `?a ≡ Int`.
equating :: XType -> Job
equating a = JobUnify { kind: XKType, left: a, right: xInt }

-- | Whether `?a` is held unsolved.
unsolved :: SolverState -> XType -> Boolean
unsolved s = case _ of
  XMeta m -> case lookupMeta s.tentative.metas m of
    Just (Unsolved _) -> true
    _ -> false
  _ -> false

cancelledEvent :: TraceEvent -> Boolean
cancelledEvent = case _ of
  AttemptCancelled _ -> true
  _ -> false

guestsOn :: Session -> Aff Guests
guestsOn session = liftEffect do
  cancellation <- newCancellation (Milliseconds 1000.0)
  attempts <- Ref.new 0
  health <- Ref.new Reusable
  pure { session, descriptor, env, budget: 1000, cancellation, attempts, health }

spec :: Spec Unit
spec = describe "Stella.CLI.Session.Broker.Attempter" do
  it "runs a synthesis job by its synthesizer's global, a new invocation each attempt, and an equation by the host" do
    result <- liftEffect (Ref.new "")
    seen <- withSession waiting \session -> case withA of
      Left err -> fail err
      Right { a, state } -> do
        guests <- guestsOn session
        node (submitGuestSynthesis guests site a synth state) >>= case _ of
          Right (Tuple { submission: Continue _ } s1) -> node (submitGuest guests site (equating a) s1) >>= case _ of
            Right (Tuple (Continue _) s2) -> node (runGuests guests s2) >>= case _ of
              Right (Tuple report s3) -> liftEffect do
                Ref.write (show report.result) result
                attempts <- Ref.read guests.attempts
                health <- Ref.read guests.health
                Ref.modify_ (_ <> (" " <> show attempts <> " " <> show health <> " fuel " <> show s3.retained.fuel <> " pending " <> show (Map.size s3.tentative.scheduler.pending))) result
              Left _ -> fail "the run was called off"
            Right (Tuple other _) -> fail ("the equation did not go on: " <> show other)
            Left _ -> fail "the equation was called off"
          Right (Tuple { submission } _) -> fail ("the goal did not wait: " <> show submission)
          Left _ -> fail "the submission was called off"
    liftEffect (Ref.read result) >>= shouldEqual "Completed 2 Reusable fuel 9 pending 0"
    seen `shouldEqual` [ "Synth.synth 1 1000", "abandoned", "Synth.synth 2 1000" ]

  it "stops the driver where the compilation is called off, with nothing sent" do
    result <- liftEffect (Ref.new "")
    seen <- withSession waiting \session -> case withA of
      Left err -> fail err
      Right { a, state } -> do
        guests <- guestsOn session
        liftEffect (cancel guests.cancellation)
        node (submitGuestSynthesis guests site a synth state) >>= case _ of
          Left (CalledOff s health) -> do
            liftEffect (Ref.write ("CalledOff " <> show health) result)
            -- the guest's attempt opened, and was rolled back as cancelled
            Array.any cancelledEvent s.retained.trace `shouldEqual` true
          Right _ -> fail "the submission went on"
        liftEffect (Ref.read guests.attempts) >>= shouldEqual 1
    liftEffect (Ref.read result) >>= shouldEqual "CalledOff Reusable"
    seen `shouldEqual` []

  it "does not attempt an equation once the compilation is called off" do
    seen <- withSession waiting \session -> case withA of
      Left err -> fail err
      Right { a, state } -> do
        guests <- guestsOn session
        liftEffect (cancel guests.cancellation)
        node (submitGuest guests site (equating a) state) >>= case _ of
          Left (CalledOff s health) -> do
            health `shouldEqual` Reusable
            unsolved s a `shouldEqual` true
          Right (Tuple submission _) -> fail ("the equation was attempted: " <> show submission)
    seen `shouldEqual` []

  it "stops a loop of equations alone where the compilation is called off, and runs it where it is not" do
    seen <- withSession waiting \session -> case withA of
      Left err -> fail err
      Right { a, state } -> do
        let
          Tuple id created = create site (equating a) state.tentative.scheduler
          queued = state { tentative { scheduler = enqueueInitial id created } }
        running <- guestsOn session
        node (runGuests running queued) >>= case _ of
          Right (Tuple report s) -> do
            report.result `shouldEqual` Completed
            unsolved s a `shouldEqual` false
          Left _ -> fail "the run was called off"
        stopping <- guestsOn session
        liftEffect (cancel stopping.cancellation)
        node (runGuests stopping queued) >>= case _ of
          Left (CalledOff s health) -> do
            health `shouldEqual` Reusable
            unsolved s a `shouldEqual` true
          Right (Tuple report _) -> fail ("the loop went on: " <> show report.result)
    seen `shouldEqual` []

  it "halts where the session is lost, and has it replaced" do
    result <- liftEffect (Ref.new Nothing)
    _ <- withSession "const guest = async (p) => { socket.destroy(); process.exitCode = 1; return new Promise(() => {}); };" \session -> case withA of
      Left err -> fail err
      Right { a, state } -> do
        guests <- guestsOn session
        node (submitGuestSynthesis guests site a synth state) >>= case _ of
          Right (Tuple { submission: Stop report } _) -> do
            health <- liftEffect (Ref.read guests.health)
            liftEffect (Ref.write (Just (Tuple report.result health)) result)
          _ -> fail "the submission did not stop"
    liftEffect (Ref.read result) >>= case _ of
      Just (Tuple (Halted (GuestSessionBroke _)) Replace) -> pure unit
      other -> fail ("ended otherwise: " <> show (map (\(Tuple r h) -> show r <> " " <> show h) other))

  it "draws no attempt number past the last, and has the session replaced, sending nothing" do
    result <- liftEffect (Ref.new Nothing)
    seen <- withSession waiting \session -> case withA of
      Left err -> fail err
      Right { a, state } -> do
        guests <- guestsOn session
        liftEffect (Ref.write lastAttempt guests.attempts)
        node (submitGuestSynthesis guests site a synth state) >>= case _ of
          Right (Tuple { submission: Stop report } s) -> do
            health <- liftEffect (Ref.read guests.health)
            let
              abandonedTraced = Array.any
                ( case _ of
                    AttemptAbandoned _ -> true
                    _ -> false
                )
                s.retained.trace
            liftEffect (Ref.write (Just { result: report.result, health, abandonedTraced }) result)
          _ -> fail "the submission did not stop"
    liftEffect (Ref.read result) >>= case _ of
      Just r -> do
        r.result `shouldEqual` Halted GuestAttemptsExhausted
        r.health `shouldEqual` Replace
        r.abandonedTraced `shouldEqual` true
      Nothing -> fail "no result"
    seen `shouldEqual` []
