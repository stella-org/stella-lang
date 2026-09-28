-- | An attempt held open across a synthesizer's requests.
-- |
-- | Three things are what these cases are for. **A failure inside a transaction
-- | is answered**: the innermost transaction alone is rolled back and closed,
-- | and the synthesizer goes on outside it; a failure outside every
-- | transaction, a postponement, and a defect end the attempt, rolled back to
-- | its checkpoint. **A request names where the conversation stands**: another
-- | conversation, or a transaction the host no longer holds, is a defect. And
-- | **nothing commits before the attempt is finished**: finishing checks that
-- | no transaction and no binder is open, and then runs the acceptance given,
-- | inside the attempt.
module Test.Stella.Compiler.Elaborate.Conversations (spec) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.Trace (Tracing(..))
import Stella.Compiler.Elaborate.Build (rootScope, typeConstructor)
import Stella.Compiler.Elaborate.BuildTerm (literal, openLambda)
import Stella.Compiler.Elaborate.Catalog (catalogOf)
import Stella.Compiler.Elaborate.Constructors (emptyConstructorEnv)
import Stella.Compiler.Elaborate.Context (Origin(..), emptyXContext)
import Stella.Compiler.Elaborate.Diagnostic (Defect(..), Diagnostic(..), MalformedGoal(..))
import Stella.Compiler.Elaborate.Effects (emptyEffectEnv)
import Stella.Compiler.Elaborate.Elab (Elab, Outcome(..), SessionEnv, SolverState, assignTerm, break, createSynthesis, freshTypeMeta, initialState, issue, resolveType, runElabIn, unify)
import Stella.Compiler.Elaborate.Handle (Handle, HandleError(..), HandleObject(..), SessionId(..))
import Stella.Compiler.Elaborate.Kind (XKind(..))
import Stella.Compiler.Elaborate.Kinding (kindingOf)
import Stella.Compiler.Elaborate.Message (FrozenMessagePart(..), MessagePart(..))
import Stella.Compiler.Elaborate.Pending (PendingId, Site)
import Stella.Compiler.Elaborate.Protocol (ConversationId(..), TransactionToken)
import Stella.Compiler.Elaborate.Report (postpone, throw, warn)
import Stella.Compiler.Elaborate.Run (Attempt(..), Conversation, OpenResult(..), Response(..), Step(..), beginTransaction, commitTransaction, envelopeOf, finishAttempt, innermost, openAttempt, request, runAttempt)
import Stella.Compiler.Elaborate.Scheduler (lookupPending, takeReady)
import Stella.Compiler.Elaborate.Term (TermMetaVar, XExpr(..))
import Stella.Compiler.Elaborate.Type (MetaVar, XType(..))
import Stella.Compiler.Elaborate.Unify (MetaBinding(..), lookupMeta)
import Stella.Compiler.TypedCore (Ident(..), Literal(..), ModuleName(..), Qualified(..))
import Stella.Compiler.TypedCore.Prim (intTy, primSignature)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..), isJust, isNothing)
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

-- | A goal at `Int` with its target, and a type metavariable `?a` beside it,
-- | created and queued; and the state with the goal taken from the ready queue.
type Asked = { id :: PendingId, target :: TermMetaVar, a :: MetaVar, queued :: SolverState, taken :: SolverState }

asked :: Either P.String Asked
asked = case runElabIn session (initialState (SessionId 0) 10) created of
  Tuple (Done (Tuple (Tuple id target) (XMeta a))) queued -> case takeReady queued.tentative.scheduler of
    Just (Tuple _ scheduler) -> Right { id, target, a, queued, taken: queued { tentative { scheduler = scheduler } } }
    Nothing -> Left "no job was queued"
  Tuple other _ -> Left (show other)
  where
  created = do
    goal <- createSynthesis site xInt resolver Nothing
    a <- freshTypeMeta emptyXContext XKType
    pure (Tuple goal a)

given :: (Asked -> Aff Unit) -> Aff Unit
given check = case asked of
  Right g -> check g
  Left err -> fail err

-- | The goal's attempt opened, from the state given.
opened :: Asked -> SolverState -> (Conversation -> Aff Unit) -> Aff Unit
opened g s check = case openAttempt session g.id s of
  Opened conversation -> check conversation
  OpenStopped attempt _ -> fail ("the attempt did not open: " <> show attempt)

-- | The request answered with what it asked for.
returned :: forall a. Step a -> (a -> Conversation -> Aff Unit) -> Aff Unit
returned step check = case step of
  Answered (Returned a) conversation -> check a conversation
  Answered (CandidateFailed token d) _ -> fail ("the candidate failed in " <> show token <> ": " <> show d)
  Finished attempt _ -> fail ("the attempt ended: " <> show attempt)

-- | The request that ends the attempt.
ending :: forall a. Step a -> (Attempt -> SolverState -> Aff Unit) -> Aff Unit
ending step check = case step of
  Finished attempt s -> check attempt s
  Answered _ _ -> fail "the attempt went on"

-- | A request standing where the conversation stands.
ask :: forall a. Elab a -> Conversation -> Step a
ask action conversation = request (envelopeOf conversation) action conversation

begin :: Conversation -> Step TransactionToken
begin conversation = beginTransaction (envelopeOf conversation) conversation

commit :: Conversation -> Step Unit
commit conversation = commitTransaction (envelopeOf conversation) conversation

finish :: Elab Unit -> Conversation -> Tuple Attempt SolverState
finish accept conversation = finishAttempt (envelopeOf conversation) accept conversation

text :: P.String -> P.Array MessagePart
text t = [ TextPart t ]

-- | A type handle built at the root.
intHandle :: Elab Handle
intHandle = rootScope >>= \root -> typeConstructor root intTy []

-- | `?a := Int`.
solveA :: Asked -> Elab Unit
solveA g = unify site { kind: XKType, left: XMeta g.a, right: xInt }

unsolved :: SolverState -> MetaVar -> P.Boolean
unsolved s m = case lookupMeta s.tentative.metas m of
  Just (Unsolved _) -> true
  _ -> false

spec :: Spec Unit
spec = describe "Elaborate.Run, a conversation" do
  describe "a transaction" do
    it "keeps what was done inside it where it commits" do
      given \g -> opened g g.taken \c0 ->
        returned (begin c0) \t c1 -> do
          innermost c1 `shouldEqual` Just t
          returned (ask (warn (text "in") *> solveA g) c1) \_ c2 ->
            returned (commit c2) \_ c3 -> do
              innermost c3 `shouldEqual` Nothing
              case finish (pure unit) c3 of
                Tuple Committed s -> do
                  unsolved s g.a `shouldEqual` false
                  map _.message s.tentative.warnings `shouldEqual` [ [ FrozenText "in" ] ]
                  isNothing (lookupPending s.tentative.scheduler g.id) `shouldEqual` true
                Tuple other _ -> fail (show other)

    it "that fails is rolled back and closed, and the synthesizer goes on outside it" do
      given \g -> opened g g.taken \c0 ->
        returned (ask intHandle c0) \outer c1 ->
          returned (begin c1) \t c2 ->
            returned (ask (warn (text "in") *> solveA g *> intHandle) c2) \inner c3 ->
              case ask (throw (text "no") :: Elab Unit) c3 of
                Answered (CandidateFailed failedIn (SynthesisFailed report)) c4 -> do
                  failedIn `shouldEqual` t
                  report.message `shouldEqual` [ FrozenText "no" ]
                  innermost c4 `shouldEqual` Nothing
                  c4.state.tentative.warnings `shouldEqual` []
                  unsolved c4.state g.a `shouldEqual` true
                  -- The handle issued before the transaction still resolves;
                  -- the one issued inside it does not.
                  returned (ask (resolveType outer) c4) \_ c5 ->
                    ending (ask (resolveType inner) c5) \attempt _ ->
                      attempt `shouldEqual` Halted (InvalidHandle inner StaleHandle)
                other -> fail ("expected the candidate to fail: " <> showStep other)

    it "nested inside another is the only one a failure closes" do
      given \g -> opened g g.taken \c0 ->
        returned (begin c0) \t0 c1 ->
          returned (begin c1) \t1 c2 ->
            case ask (throw (text "no") :: Elab Unit) c2 of
              Answered (CandidateFailed failedIn _) c3 -> do
                failedIn `shouldEqual` t1
                innermost c3 `shouldEqual` Just t0
                returned (commit c3) \_ c4 ->
                  fst (finish (pure unit) c4) `shouldEqual` Committed
              other -> fail ("expected the candidate to fail: " <> showStep other)

    it "is never issued a token issued before" do
      given \g -> opened g g.taken \c0 ->
        returned (begin c0) \t0 c1 ->
          case ask (throw (text "no") :: Elab Unit) c1 of
            Answered (CandidateFailed _ _) c2 ->
              returned (begin c2) \t1 _ -> (t0 == t1) `shouldEqual` false
            other -> fail ("expected the candidate to fail: " <> showStep other)

  describe "the attempt" do
    it "is rejected by a failure outside every transaction, and the job is gone" do
      given \g -> opened g g.taken \c0 ->
        returned (ask (warn (text "w")) c0) \_ c1 ->
          ending (ask (throw (text "no") :: Elab Unit) c1) \attempt s -> do
            case attempt of
              Rejected (SynthesisFailed _) -> pure unit
              other -> fail (show other)
            s.tentative.warnings `shouldEqual` []
            isNothing (lookupPending s.tentative.scheduler g.id) `shouldEqual` true

    it "postponed inside a transaction is rolled back to its checkpoint, and waits on what the attempt solved" do
      given \g -> opened g g.taken \c0 ->
        returned (begin c0) \_ c1 ->
          ending (ask (solveA g *> issue (MetaObject g.a) >>= \a -> postpone [ a ]) c1) \attempt s -> do
            attempt `shouldEqual` Registered (Set.singleton g.a)
            unsolved s g.a `shouldEqual` true
            isJust (lookupPending s.tentative.scheduler g.id) `shouldEqual` true

    it "postponed on a metavariable solved before it is a defect" do
      let
        solvedBefore g = case runAttempt session (solveA g) g.taken of
          Tuple (Done _) s -> s
          Tuple _ s -> s
      given \g -> opened g (solvedBefore g) \c0 ->
        ending (ask (issue (MetaObject g.a) >>= \a -> postpone [ a ]) c0) \attempt _ ->
          case attempt of
            Halted (PostponementInadmissible _) -> pure unit
            other -> fail (show other)

    it "that breaks inside a transaction is rolled back to its checkpoint" do
      given \g -> opened g g.taken \c0 ->
        returned (ask (warn (text "w") *> solveA g) c0) \_ c1 ->
          returned (begin c1) \_ c2 ->
            ending (ask (break (SynthesizerUnavailable resolver) :: Elab Unit) c2) \attempt s -> do
              attempt `shouldEqual` Halted (SynthesizerUnavailable resolver)
              s.tentative.warnings `shouldEqual` []
              unsolved s g.a `shouldEqual` true

    it "is not opened where the job is still queued, or its target is solved" do
      given \g -> do
        case openAttempt session g.id g.queued of
          OpenStopped attempt s -> do
            attempt `shouldEqual` Halted (PendingStillScheduled g.id)
            isJust (lookupPending s.tentative.scheduler g.id) `shouldEqual` true
          Opened _ -> fail "a queued job was opened"
        let
          targetSolved = case runAttempt session (assignTerm site g.target (ELit unit (LitInt 1))) g.taken of
            Tuple _ s -> s
        case openAttempt session g.id targetSolved of
          OpenStopped attempt s -> do
            attempt `shouldEqual` Halted (MalformedSynthesisJob g.id (TargetSolved g.target))
            isJust (lookupPending s.tentative.scheduler g.id) `shouldEqual` true
          Opened _ -> fail "a job with a solved target was opened"

    it "is identified afresh every time it is opened, a rollback notwithstanding" do
      given \g -> opened g g.taken \c0 ->
        ending (ask (break (SynthesizerUnavailable resolver) :: Elab Unit) c0) \_ s ->
          opened g s \c1 -> (c0.id == c1.id) `shouldEqual` false

    it "is not opened where every identifier has been issued, and the state is left as it was" do
      given \g -> do
        let
          spent = g.taken { retained { nextConversation = top } }
        case openAttempt session g.id spent of
          OpenStopped attempt s -> do
            attempt `shouldEqual` Halted ConversationsExhausted
            s.retained `shouldEqual` spent.retained
            unsolved s g.a `shouldEqual` true
            isJust (lookupPending s.tentative.scheduler g.id) `shouldEqual` true
          Opened _ -> fail "an identifier was issued past the last"

  describe "a transaction token" do
    it "issued past the last is a defect, rolled back to the attempt's checkpoint" do
      given \g -> opened g g.taken \c0 ->
        returned (ask (warn (text "w") *> solveA g) c0) \_ c1 ->
          ending (begin (c1 { nextSerial = top })) \attempt s -> do
            attempt `shouldEqual` Halted TransactionsExhausted
            s.tentative.warnings `shouldEqual` []
            unsolved s g.a `shouldEqual` true
            isJust (lookupPending s.tentative.scheduler g.id) `shouldEqual` true

    it "committed where none is open is a defect" do
      given \g -> opened g g.taken \c0 ->
        ending (commit c0) \attempt _ ->
          attempt `shouldEqual` Halted NoTransactionToCommit

  describe "a request's envelope" do
    it "naming another conversation is a defect" do
      given \g -> opened g g.taken \c0 ->
        ending (request { conversation: ConversationId 99, transaction: Nothing } (pure unit) c0) \attempt _ ->
          attempt `shouldEqual` Halted (ConversationMismatch { holding: c0.id, named: ConversationId 99 })

    it "naming a transaction a failure closed is a defect" do
      given \g -> opened g g.taken \c0 ->
        returned (begin c0) \t c1 ->
          case ask (throw (text "no") :: Elab Unit) c1 of
            Answered (CandidateFailed _ _) c2 ->
              ending (request { conversation: c2.id, transaction: Just t } (pure unit) c2) \attempt _ ->
                attempt `shouldEqual` Halted (TransactionMismatch { holding: Nothing, named: Just t })
            other -> fail ("expected the candidate to fail: " <> showStep other)

  describe "finishing" do
    it "with a transaction open is a defect" do
      given \g -> opened g g.taken \c0 ->
        returned (begin c0) \t c1 ->
          case finish (pure unit) c1 of
            Tuple attempt s -> do
              attempt `shouldEqual` Halted (TransactionsLeftOpen [ t ])
              isJust (lookupPending s.tentative.scheduler g.id) `shouldEqual` true

    it "checks the binders before it accepts" do
      given \g -> opened g g.taken \c0 ->
        returned (ask (rootScope >>= \root -> intHandle >>= openLambda root "x") c0) \_ c1 ->
          case finish (throw (text "refused")) c1 of
            Tuple (Halted (BindersLeftOpen _)) _ -> pure unit
            Tuple other _ -> fail (show other)

    it "rolls back what the requests did where the acceptance fails" do
      given \g -> opened g g.taken \c0 ->
        returned (ask (warn (text "w") *> solveA g *> rootScope >>= \root -> literal root (LitInt 1)) c0) \_ c1 ->
          case finish (throw (text "refused")) c1 of
            Tuple (Rejected (SynthesisFailed _)) s -> do
              s.tentative.warnings `shouldEqual` []
              unsolved s g.a `shouldEqual` true
              isNothing (lookupPending s.tentative.scheduler g.id) `shouldEqual` true
            Tuple other _ -> fail (show other)

showStep :: forall a. Step a -> P.String
showStep = case _ of
  Answered (Returned _) _ -> "returned"
  Answered (CandidateFailed token d) _ -> "failed in " <> show token <> ": " <> show d
  Finished attempt _ -> "finished: " <> show attempt
