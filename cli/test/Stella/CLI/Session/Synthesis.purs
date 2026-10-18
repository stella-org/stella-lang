-- | A build's synthesis jobs on its compile-time session: an equation by the
-- | host with no session opened, and a synthesizer that faults or uses up its
-- | budget thrown as a failure of compile-time execution, where the goal stands.
-- |
-- | The session is the broker's inline stand-in for Steam; the synthesizer's
-- | module is no module of the build, so nothing is loaded before it runs.
module Test.Stella.CLI.Session.Synthesis (spec) where

import Prelude

import Data.Either (Either(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Data.Tuple (Tuple(..))
import Effect.Aff (Aff, Milliseconds(..))
import Effect.Class (liftEffect)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Run (AFF, EFFECT, Run)
import Run.Except (EXCEPT)
import Run.Except as Except
import Stella.CLI.Effect.Process (Output(..), PROCESS)
import Stella.CLI.Session.Broker (SessionHealth(..), newCancellation)
import Stella.CLI.Session.Client (Session)
import Stella.CLI.Session.CompileTime (CompileTimeError(..))
import Stella.CLI.Session.Synthesis (Synthesizing, openingSynthesis)
import Stella.Compiler.Elaborate.CorePlus.Context (Origin(..), emptyXContext)
import Stella.Compiler.Elaborate.CorePlus.Kind (XKind(..))
import Stella.Compiler.Elaborate.CorePlus.Type (XType(..))
import Stella.Compiler.Elaborate.Driver.Loop (Submission(..), submitAttemptingM)
import Stella.Compiler.Elaborate.Driver.Synthesis (submitSynthesisM)
import Stella.Compiler.Elaborate.Environment.Catalog (catalogOf)
import Stella.Compiler.Elaborate.Environment.Constructors (constructorsOf)
import Stella.Compiler.Elaborate.Environment.Effects (effectsOf)
import Stella.Compiler.Elaborate.Kernel.Elab (Outcome(..), SessionEnv, SolverState, freshTypeMeta, initialState, runElabIn)
import Stella.Compiler.Elaborate.Mechanism.Kinding (kindingOf)
import Stella.Compiler.Elaborate.Mechanism.Pending (Job(..), Site)
import Stella.Compiler.Elaborate.Vocabulary.Handle (SessionId(..))
import Stella.Compiler.Elaborate.Vocabulary.Trace (Tracing(..))
import Stella.Compiler.TypedCore (Ident(..), ModuleName(..), Qualified(..))
import Stella.Compiler.TypedCore.Prim (intTy, primSignature)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)
import Test.Stella.CLI.Session.Broker (descriptor, node, withSession)
import Type.Row (type (+))

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

type Running = Run (EXCEPT CompileTimeError + PROCESS + AFF + EFFECT + ())

-- | What the synthesizers run with, the session the one held, or none.
synthesizing :: Ref (Maybe Session) -> Aff (Synthesizing ())
synthesizing held = liftEffect do
  loaded <- Ref.new Set.empty
  cancellation <- newCancellation (Milliseconds 1000.0)
  attempts <- Ref.new 0
  health <- Ref.new Reusable
  pure
    { held
    , launch: { command: "false", args: [], output: Inherit, hello: { protocol: 1, profile: "elaboration", offers: [], requires: [] } }
    , descriptor
    , loading: { seed: Map.empty, importsOf: const Nothing, loaded, locate: \_ -> pure Nothing }
    , budget: 1000
    , cancellation
    , attempts
    , health
    }

-- | The goal `?m : Int by Synth.synth` submitted, on a session whose guest is
-- | the one given, and what stopped it.
thrownBy :: String -> Aff (Maybe String)
thrownBy guest = do
  thrown <- liftEffect (Ref.new Nothing)
  _ <- withSession guest \session -> case withA of
    Left err -> fail err
    Right { state } -> do
      held <- liftEffect (Ref.new (Just session))
      running <- synthesizing held
      outcome <- node (Except.runExcept (submitSynthesisM (openingSynthesis running Map.empty env) site xInt synth state :: Running _))
      liftEffect $ Ref.write (Just (either' outcome)) thrown
  liftEffect (Ref.read thrown)
  where
  either' = case _ of
    Left failure -> show failure
    Right _ -> "submitted"

spec :: Spec Unit
spec = describe "Stella.CLI.Session.Synthesis" do
  it "attempts an equation by the host, and opens no session for it" do
    case withA of
      Left err -> fail err
      Right { a, state } -> do
        held <- liftEffect (Ref.new Nothing)
        running <- synthesizing held
        outcome <- node (Except.runExcept (submitAttemptingM (openingSynthesis running Map.empty env) site (JobUnify { kind: XKType, left: a, right: xInt }) state :: Running _))
        case outcome of
          Right (Tuple (Continue _) _) -> pure unit
          Right (Tuple other _) -> fail ("the equation did not go on: " <> show other)
          Left failure -> fail (show failure)
        opened <- liftEffect (Ref.read held)
        map (const unit) opened `shouldEqual` Nothing

  it "throws a synthesizer's fault as a failure of compile-time execution, naming the synthesizer and the goal" do
    thrownBy "const guest = async (p) => failed('fault');" >>= shouldEqual
      (Just (show (SynthesizerFaulted { synthesizer: synth, goal: site.origin, detail: "" })))

  it "throws a synthesizer's budget used up likewise, with the budget" do
    thrownBy "const guest = async (p) => failed('budgetExhausted');" >>= shouldEqual
      (Just (show (SynthesizerBudgetExhausted { synthesizer: synth, goal: site.origin, budget: 1000 })))
