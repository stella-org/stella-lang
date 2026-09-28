-- | The trace of a synthesis attempt, and what it fixes.
-- |
-- | Four things are what these cases are for. **A trace is determined by what
-- | it starts from**: the same synthesizer from the same state gives the same
-- | trace, outcome, and state, and the commands it recorded, sent again from that
-- | state, give them again. **What became of each event is computed from the
-- | trace**: kept where the attempt commits, rolled back with a transaction, or
-- | one around it, that fails, and undecided where the conversation has not
-- | ended. **A retry sends the same commands up to the first reply that
-- | differs**, and parts from the first attempt's commands only after it. And
-- | **the kernel carries a goal from its first attempt to the Core checker**
-- | through a postponement, a candidate search, and a retry, by its requests
-- | alone.
module Test.Stella.Compiler.Elaborate.Traces (spec) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.Catalog (EntrySort(..), catalogOf)
import Stella.Compiler.Elaborate.Constructors (constructorsOf)
import Stella.Compiler.Elaborate.Context (Origin(..), emptyXContext)
import Stella.Compiler.Elaborate.Diagnostic (Defect(..))
import Stella.Compiler.Elaborate.Drive (command, openConversation, runSynthesizer)
import Stella.Compiler.Elaborate.Effects (effectsOf)
import Stella.Compiler.Elaborate.Elab (Outcome(..), SessionEnv, SolverState, createSynthesis, freshTypeMeta, initialState, runElabIn)
import Stella.Compiler.Elaborate.Facade (Synthesizer)
import Stella.Compiler.Elaborate.Facade as F
import Stella.Compiler.Elaborate.Handle (SessionId(..))
import Stella.Compiler.Elaborate.Kind (XKind(..))
import Stella.Compiler.Elaborate.Kinding (kindingOf)
import Stella.Compiler.Elaborate.Message (MessagePart(..))
import Stella.Compiler.Elaborate.Pending (PendingId, Site)
import Stella.Compiler.Elaborate.Request (Command(..), CommandAnswer(..), KernelAnswer(..), KernelRequest(..), ObserveRequest(..))
import Stella.Compiler.Elaborate.Run (Attempt(..), OpenResult(..), Step(..), envelopeOf, runAttempt)
import Stella.Compiler.Elaborate.Scheduler (takeReady)
import Stella.Compiler.Elaborate.Term (TermMetaVar, XExpr(..), toCoreExpr)
import Stella.Compiler.Elaborate.TermMeta (zonkExpr)
import Stella.Compiler.Elaborate.Trace (Fate(..), TraceEvent(..), TraceReply(..), Tracing(..), canonicalCommands, commandsOf, fates)
import Stella.Compiler.Elaborate.Type (MetaVar, XType(..))
import Stella.Compiler.Elaborate.Elab as Elab
import Stella.Compiler.Elaborate.View (TypeView(..))
import Stella.Compiler.TypedCore (Decl(..), Expr(..), Ident(..), Literal(..), Module, ModuleName(..), Qualified(..), Type(..), globalsOf, monoScheme)
import Stella.Compiler.TypedCore.Declare (declare)
import Stella.Compiler.TypedCore.Prim (intTy, primSignature)
import Stella.Compiler.TypedCore.Signature (Signature)
import Data.Array as Array
import Data.Either (Either(..), either, isRight)
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Data.Tuple (Tuple(..), fst, snd)
import Effect.Aff (Aff)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

main :: ModuleName
main = ModuleName "Main"

qualified :: P.String -> Qualified Ident
qualified name = Qualified main (Ident name)

xInt :: XType
xInt = XCon intTy []

coreInt :: Type
coreInt = TCon intTy []

-- | `one = 1` and `two = 2`, the globals a term may refer to.
valuesModule :: Module P.Int
valuesModule =
  { annotation: 0
  , name: main
  , imports: []
  , exports: []
  , decls:
      [ DeclNonRec 1 { name: Ident "one", scheme: monoScheme coreInt, value: Lit 1 (LitInt 1), attributes: [] }
      , DeclNonRec 2 { name: Ident "two", scheme: monoScheme coreInt, value: Lit 2 (LitInt 2), attributes: [] }
      ]
  }

signature :: Signature
signature = either (const primSignature) identity (declare primSignature valuesModule)

sessionTracing :: Tracing -> SessionEnv
sessionTracing tracing =
  { catalog: catalogOf (map entry [ "one", "two" ])
  , kinding: kindingOf signature
  , constructors: constructorsOf signature
  , effects: effectsOf signature
  , tracing
  }
  where
  entry name = { name: qualified name, sort: ValueEntry, scheme: { kindVars: [], body: xInt }, attributes: [] }

session :: SessionEnv
session = sessionTracing TraceEnabled

resolver :: Qualified Ident
resolver = Qualified (ModuleName "Typeclass") (Ident "resolve")

site :: Site
site = { context: emptyXContext, origin: InDeclaration (Qualified (ModuleName "User") (Ident "answer")) }

-- | A goal at the type given of `?a`, with its target, and the type
-- | metavariable `?a` created before it: the state with the goal queued, and
-- | with it taken from the ready queue.
type Asked = { id :: PendingId, target :: TermMetaVar, a :: MetaVar, queued :: SolverState, taken :: SolverState }

asking :: (XType -> XType) -> Either P.String Asked
asking goalAt = case runElabIn session (initialState (SessionId 0) 10) created of
  Tuple (Done (Tuple (Tuple id target) (XMeta a))) queued -> case takeReady queued.tentative.scheduler of
    Just (Tuple _ scheduler) -> Right { id, target, a, queued, taken: queued { tentative { scheduler = scheduler } } }
    Nothing -> Left "no job was queued"
  Tuple other _ -> Left (show other)
  where
  created = do
    a <- freshTypeMeta emptyXContext XKType
    goal <- createSynthesis site (goalAt a) resolver Nothing
    pure (Tuple goal a)

given :: (Asked -> Aff Unit) -> Aff Unit
given = givenAt (const xInt)

givenAt :: (XType -> XType) -> (Asked -> Aff Unit) -> Aff Unit
givenAt goalAt check = case asking goalAt of
  Right g -> check g
  Left err -> fail err

-- | The trace a state holds.
traceOf :: SolverState -> P.Array TraceEvent
traceOf s = s.retained.trace

-- | The commands of the trace given, with their envelopes, sent again to an
-- | attempt of the job named opened from the state given.
replay :: PendingId -> SolverState -> P.Array TraceEvent -> Maybe (Tuple Attempt SolverState)
replay id s0 events = case openConversation session id s0 of
  OpenStopped attempt s -> Just (Tuple attempt s)
  Opened c0 -> go c0 (Array.mapMaybe sent events)
  where
  sent = case _ of
    CommandHandled e -> Just { envelope: e.envelope, command: e.command }
    _ -> Nothing
  go c commands = case Array.uncons commands of
    Just { head, tail } -> case command head.envelope head.command c of
      Answered _ c' -> go c' tail
      Finished attempt s -> Just (Tuple attempt s)
    Nothing -> Nothing

-- | The events' commands and fates, where they are commands.
commandFates :: P.Array TraceEvent -> P.Array (Tuple P.String Fate)
commandFates events = Array.catMaybes (Array.zipWith named events (fates events))
  where
  named event fate = case event of
    CommandHandled e -> Just (Tuple (label e.command) fate)
    _ -> Nothing
  label = case _ of
    Kernel _ -> "kernel"
    BeginTransaction -> "begin"
    CommitTransaction -> "commit"
    Finish _ -> "finish"

answerOne :: Synthesizer
answerOne _ = F.rootScope >>= \root -> F.literal root (LitInt 1)

-- | Tries a candidate that warns and fails, then answers `1`.
searching :: Synthesizer
searching goal = do
  _ <- F.transact (F.warn [ TextPart "discarded" ] *> F.throw [ TextPart "no" ] :: F.Facade Unit)
  answerOne goal

-- | Waits on the goal's type while it is a metavariable, and answers `Main.one`
-- | once it is not, after a candidate the goal's type refutes.
patient :: Synthesizer
patient goal = do
  ty <- F.goalType goal
  F.viewType ty >>= case _ of
    MetaType m -> F.postpone [ m ]
    _ -> do
      root <- F.rootScope
      refuted <- F.transact do
        yes <- F.literal root (LitBoolean true)
        F.typeOf yes >>= F.unify root ty
        pure yes
      case refuted of
        Right _ -> F.throw [ TextPart "a Boolean was taken for the goal's type" ]
        Left _ -> F.globalRef root (qualified "one") []

spec :: Spec Unit
spec = describe "Elaborate.Trace" do
  describe "a trace" do
    it "is the same, with the same outcome and state, from the same state" do
      given \g -> do
        let
          first = runSynthesizer session searching g.id g.taken
          second = runSynthesizer session searching g.id g.taken
        fst first `shouldEqual` Committed
        fst second `shouldEqual` fst first
        traceOf (snd second) `shouldEqual` traceOf (snd first)
        (snd second == snd first) `shouldEqual` true

    it "holds commands that, sent again from the same state, give the same trace, outcome, and state" do
      given \g -> do
        let
          Tuple attempt s = runSynthesizer session searching g.id g.taken
        case replay g.id g.taken (traceOf s) of
          Just (Tuple replayed s') -> do
            replayed `shouldEqual` attempt
            traceOf s' `shouldEqual` traceOf s
            (s' == s) `shouldEqual` true
          Nothing -> fail "the commands did not finish the attempt"

    it "is not recorded where the session does not trace" do
      given \g -> do
        let
          Tuple attempt s = runSynthesizer (sessionTracing TraceDisabled) searching g.id g.taken
        attempt `shouldEqual` Committed
        traceOf s `shouldEqual` []

    it "holds the commands a rollback undid, and the attempt's end" do
      given \g -> do
        let
          Tuple _ s = runSynthesizer session searching g.id g.taken
          events = traceOf s
        case Array.head events of
          Just (AttemptOpened _) -> pure unit
          other -> fail ("the attempt's opening is not first: " <> show other)
        map fst (commandFates events) `shouldEqual` [ "begin", "kernel", "kernel", "kernel", "kernel", "finish" ]
        case Array.last events of
          Just (CommandHandled { reply: Ended Committed }) -> pure unit
          other -> fail ("the attempt's end is not last: " <> show other)

  describe "the fate of an event" do
    it "is rolled back with the transaction that failed, and kept where the attempt commits" do
      given \g -> do
        let
          Tuple _ s = runSynthesizer session searching g.id g.taken
        map snd (commandFates (traceOf s))
          `shouldEqual` [ RolledBack, RolledBack, RolledBack, Kept, Kept, Kept ]
        Array.head (fates (traceOf s)) `shouldEqual` Just Kept

    it "committed inside a transaction later rolled back is rolled back" do
      given \g -> do
        let
          nested goal = do
            _ <- F.transact do
              _ <- F.transact (F.warn [ TextPart "inner" ])
              F.throw [ TextPart "outer" ] :: F.Facade Unit
            answerOne goal
          Tuple _ s = runSynthesizer session nested g.id g.taken
        commandFates (traceOf s) `shouldEqual`
          [ Tuple "begin" RolledBack
          , Tuple "begin" RolledBack
          , Tuple "kernel" RolledBack
          , Tuple "commit" RolledBack
          , Tuple "kernel" RolledBack
          , Tuple "kernel" Kept
          , Tuple "kernel" Kept
          , Tuple "finish" Kept
          ]

    it "is rolled back, every one, where the attempt ends without a result" do
      givenAt identity \g -> do
        let
          Tuple attempt s = runSynthesizer session patient g.id g.taken
        attempt `shouldEqual` Registered (Set.singleton g.a)
        Array.nub (fates (traceOf s)) `shouldEqual` [ RolledBack ]
        case Array.last (traceOf s) of
          Just (CommandHandled { reply: Ended (Registered waited) }) -> waited `shouldEqual` Set.singleton g.a
          other -> fail ("the postponement is not last: " <> show other)

    it "is undecided where the conversation has not ended" do
      given \g -> case openConversation session g.id g.taken of
        Opened c0 -> case command (envelopeOf c0) BeginTransaction c0 of
          Answered _ c1 -> case command (envelopeOf c1) (Kernel (ObserveRequest LocalContext)) c1 of
            Answered _ c2 -> Array.nub (fates (traceOf c2.state)) `shouldEqual` [ Pending ]
            Finished attempt _ -> fail (show attempt)
          Finished attempt _ -> fail (show attempt)
        OpenStopped attempt _ -> fail (show attempt)

    it "is that nothing ran where the attempt did not open" do
      given \g -> do
        let
          Tuple attempt s = runSynthesizer session answerOne g.id g.queued
        attempt `shouldEqual` Halted (PendingStillScheduled g.id)
        fates (traceOf s) `shouldEqual` [ NotRun ]

  describe "a defect" do
    it "ends the conversation, and is told apart from a failure" do
      given \g -> do
        let
          misusing goal = do
            root <- F.rootScope
            _ <- F.transact (F.rootScope *> F.throw [ TextPart "no" ] :: F.Facade Unit)
            _ <- F.localVariable root (Ident "missing")
            answerOne goal
          Tuple attempt s = runSynthesizer session misusing g.id g.taken
          replies = Array.mapMaybe
            ( case _ of
                CommandHandled e -> Just e.reply
                _ -> Nothing
            )
            (traceOf s)
        case attempt of
          Halted _ -> pure unit
          other -> fail (show other)
        case Array.last replies of
          Just (Ended (Halted _)) -> pure unit
          other -> fail (show other)
        Array.length (Array.filter isFailedCandidate replies) `shouldEqual` 1

  describe "a retry" do
    it "sends the first attempt's commands up to the first reply that differs, and parts from them after it" do
      givenAt identity \g -> do
        let
          Tuple first s1 = runSynthesizer session patient g.id g.taken
          -- The host solves `?a` between the two conversations, which wakes the
          -- goal: no command of either does.
          Tuple _ s2 = runAttempt session (Elab.unify site { kind: XKType, left: XMeta g.a, right: xInt }) s1
        first `shouldEqual` Registered (Set.singleton g.a)
        case takeReady s2.tentative.scheduler of
          Just (Tuple id scheduler) -> do
            let
              Tuple second s3 = runSynthesizer session patient id (s2 { tentative { scheduler = scheduler } })
              events = traceOf s3
              conversations = Array.nub (Array.mapMaybe conversationOf events)
            second `shouldEqual` Committed
            case conversations of
              [ c1, c2 ] -> do
                let
                  before = canonicalCommands (commandsOf c1 events)
                  after = canonicalCommands (commandsOf c2 events)
                Array.take 2 after `shouldEqual` Array.take 2 before
                (Array.index after 2 == Array.index before 2) `shouldEqual` false
                viewed c1 events `shouldEqual` Just "meta"
                viewed c2 events `shouldEqual` Just "constructor"
              other -> fail ("expected two conversations: " <> show other)
          Nothing -> fail "the goal was not woken"

  describe "the kernel" do
    it "carries a goal through a postponement, a candidate search, and a retry to the Core checker" do
      givenAt identity \g -> do
        let
          Tuple first s1 = runSynthesizer session patient g.id g.taken
          Tuple _ s2 = runAttempt session (Elab.unify site { kind: XKType, left: XMeta g.a, right: xInt }) s1
        first `shouldEqual` Registered (Set.singleton g.a)
        case takeReady s2.tentative.scheduler of
          Just (Tuple id scheduler) -> case runSynthesizer session patient id (s2 { tentative { scheduler = scheduler } }) of
            Tuple Committed s3 -> case toCoreExpr (zonkExpr s3.tentative.metas (ETermMeta unit g.target)) of
              Right core -> do
                globalsOf core `shouldEqual` Set.singleton (qualified "one")
                isRight (verdict core) `shouldEqual` true
              Left residues -> fail ("the solution did not cross the boundary: " <> show residues)
            Tuple other _ -> fail (show other)
          Nothing -> fail "the goal was not woken"
  where
  isFailedCandidate = case _ of
    FailedCandidate _ _ -> true
    _ -> false

  conversationOf = case _ of
    AttemptOpened e -> Just e.conversation
    _ -> Nothing

  -- What the conversation's `viewType` of the goal's type was answered.
  viewed c events = Array.findMap
    ( case _ of
        CommandHandled { conversation, command: Kernel (ObserveRequest (ViewType _)), reply: Replied (KernelAnswered (TypeViewAnswer view)) }
          | conversation == c -> Just case view of
              MetaType _ -> "meta"
              ConType _ _ -> "constructor"
              _ -> "other"
        _ -> Nothing
    )
    events

-- | A module declaring `answer : Int` with the right-hand side given, checked
-- | by the Core type checker.
verdict :: Expr Unit -> Either P.String Unit
verdict value = case declare signature m of
  Left e -> Left (show e.error)
  Right _ -> Right unit
  where
  m =
    { annotation: unit
    , name: ModuleName "User"
    , imports: [ main ]
    , exports: []
    , decls: [ DeclNonRec unit { name: Ident "answer", scheme: monoScheme coreInt, value, attributes: [] } ]
    }
