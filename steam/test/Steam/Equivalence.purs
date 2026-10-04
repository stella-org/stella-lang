-- | One synthesis scenario run twice from one state: by the host's runner, the policy
-- | a script in the host, and by a guest on a `steam session` the CLI started, the
-- | same policy compiled from Typed Core. **What the two come to must be the same
-- | in everything the host holds** — the submissions, the report, the final state,
-- | the trace, and the Core the hole is filled with.
-- |
-- | ```text
-- | answer = let y : ?g = ?m in y        ?m a goal at ?g, by Policy.searching
-- |   → the goal waits on ?g
-- |   → ?g ≡ Record (a : Boolean, z : Int) submitted, which wakes it
-- |   → the retry, a new invocation: cand0 passed over, cand1 rolled back, cand2 fits
-- |   → zonk → toCoreExpr → globalsOf → the Core checker
-- | ```
-- |
-- | The host's policy is written here against the facade, request for request what
-- | the guest's asks ([Reference](Reference.purs)): it waits on a metavariable, looks
-- | through what the site binds and the globals it is given — none — and tries the
-- | candidates, `Main.cand1` leaving behind a metavariable, an open constraint, and a
-- | warning as it is tried.
module Test.Steam.Equivalence (spec) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Array.NonEmpty (NonEmptyArray)
import Data.Either (Either(..), either, isRight)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Data.Tuple (Tuple(..))
import Effect.Aff (Aff, Milliseconds(..))
import Effect.Class (liftEffect)
import Effect.Ref as Ref
import Node.Buffer as Buffer
import Node.FS.Aff as FS
import Node.FS.Perms as Perms
import Stella.CLI.Session.Broker (SessionHealth(..), newCancellation)
import Stella.CLI.Session.Broker.Attempter (Guests, runGuests, submitGuest, submitGuestSynthesis)
import Stella.CLI.Session.Client (OpenFailure, Session)
import Stella.CLI.Session.Protocol (Hello)
import Stella.CLI.Session.Client as Client
import Stella.Compiler.Bytecode (encode)
import Stella.Compiler.Elaborate.CorePlus.Context (Origin(..), emptyXContext)
import Stella.Compiler.Elaborate.CorePlus.Kind (XKind(..))
import Stella.Compiler.Elaborate.CorePlus.Term (Residue, XExpr(..), toCoreExpr)
import Stella.Compiler.Elaborate.CorePlus.Type (MetaVar, XType(..), fromCore)
import Stella.Compiler.Elaborate.Driver.Attempt (Attempt(..))
import Stella.Compiler.Elaborate.Driver.Loop (RunReport, RunResult(..), Submission(..), submitAttempting)
import Stella.Compiler.Elaborate.Driver.Synthesis (Registry, attemptJob, runSynthesis, submitSynthesis)
import Stella.Compiler.Elaborate.Environment.Catalog (EntrySort(..), catalogOf)
import Stella.Compiler.Elaborate.Environment.Constructors (constructorsOf)
import Stella.Compiler.Elaborate.Environment.Effects (effectsOf)
import Stella.Compiler.Elaborate.Kernel.Elab (Outcome(..), SessionEnv, SolverState, freshTypeMeta, initialState, runElabIn)
import Stella.Compiler.Elaborate.Mechanism.Kinding (kindingOf)
import Stella.Compiler.Elaborate.Mechanism.Pending (Job(..), Site)
import Stella.Compiler.Elaborate.Mechanism.TermMeta (zonkExpr)
import Stella.Compiler.Elaborate.Mechanism.Unify (MetaBinding(..), lookupMeta)
import Stella.Compiler.Elaborate.Protocol.Facade (Facade, Synthesizer)
import Stella.Compiler.Elaborate.Protocol.Facade as F
import Stella.Compiler.Elaborate.Protocol.Guest (bundle)
import Stella.Compiler.Elaborate.Vocabulary.Handle (Handle, SessionId(..))
import Stella.Compiler.Elaborate.Vocabulary.Message (MessagePart(..))
import Stella.Compiler.Elaborate.Vocabulary.Request (Command(..), KernelRequest(..), ObserveRequest(..), TermRequest(..))
import Stella.Compiler.Elaborate.Vocabulary.Trace (Fate(..), TraceEvent(..), Tracing(..), fates)
import Stella.Compiler.Elaborate.Vocabulary.View (ConstraintView(LacksView), KindView(KindRow), TypeView(ConType, MetaType))
import Stella.Compiler.TypedCore (Attribute, Decl(..), Expr(..), Ident(..), Kind(..), KindVar(..), Literal(..), Module, ModuleName(..), Qualified(..), RowElemKind(..), RowEntry(..), RowKey(..), Symbol(..), TyVar(..), Type(..), globalsOf, monoScheme)
import Stella.Compiler.TypedCore.Declare (declare)
import Stella.Compiler.TypedCore.Prim (booleanTy, intTy, primSignature, recordTy)
import Stella.Compiler.TypedCore.Signature (Signature)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)
import Test.Steam.Command (dir, pathOf)
import Test.Steam.Guest (compileGuests)
import Test.Steam.Reference (policyModule, stringModule, synthesizerNamed)
import Test.Steam.InProcess (openInProcess)
import Test.Steam.Session (close', draining, hello, node, open', streams)

-- The fixture ------------------------------------------------------------------------------------

main :: ModuleName
main = ModuleName "Main"

inMain :: P.String -> Qualified Ident
inMain = Qualified main <<< Ident

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
-- | one   : Int                            no attribute
-- | cand0 : forall k. forall (t : k). Int  candidate, with a kind variable
-- | cand1 : Record (a : Int, z : Boolean)  candidate
-- | cand2 : Record (a : Boolean, z : Int)  candidate
-- | decoy : Int                            another attribute
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

env :: SessionEnv
env =
  { catalog: catalogOf (map (\d -> { name: inMain d.name, sort: ValueEntry, scheme: { kindVars: d.kindVars, body: fromCore d.type }, attributes: d.attributes }) declarations)
  , kinding: kindingOf signature
  , constructors: constructorsOf signature
  , effects: effectsOf signature
  , tracing: TraceEnabled
  }

site :: Site
site = { context: emptyXContext, origin: InDeclaration (inMain "answer") }

-- | The synthesizer the goal names: the guest's global, and the host's registry key.
searching :: Qualified Ident
searching = synthesizerNamed "searching"

-- | `Record (a : Boolean, z : Int)`, the type `cand2` answers.
answerType :: XType
answerType = fromCore (recordOf coreBoolean coreInt)

-- The host's policy --------------------------------------------------------------------------------

-- | The reference policy with no globals, the attribute `candidate`, and
-- | `Main.cand1` leaving behind what a candidate can where it is tried.
hostPolicy :: Synthesizer
hostPolicy goal = do
  root <- F.rootScope
  goalType <- F.goalType goal
  F.viewType goalType >>= case _ of
    MetaType m -> F.postpone [ m ]
    view -> F.localContext >>= findLocal view >>= case _ of
      Just local -> F.localVariable root local
      Nothing -> F.declsWithAttr (Qualified main (Ident "candidate")) >>= search root goalType >>= case _ of
        Just found -> pure found
        Nothing -> F.throw
          [ TextPart "nothing the site binds, no global given, and no monomorphic declaration carrying the attribute"
          , NamePart (Qualified main (Ident "candidate"))
          , TextPart "fits the type"
          , TypePart goalType
          ]
  where
  findLocal view entries = case Array.uncons entries of
    Nothing -> pure Nothing
    Just { head, tail } -> F.viewType head.type >>= \viewed ->
      if sameConstructorView view viewed then pure (Just head.name) else findLocal view tail

  search :: Handle -> Handle -> P.Array (Qualified Ident) -> Facade (Maybe Handle)
  search root goalType names = case Array.uncons names of
    Nothing -> pure Nothing
    Just { head, tail } -> F.transact (trying root goalType head) >>= case _ of
      Right (Just found) -> pure (Just found)
      _ -> search root goalType tail

  trying root goalType name = F.lookupGlobal name >>= case _ of
    Just decl | Array.null decl.kindVars -> do
      when (name == inMain "cand1") do
        row <- F.freshMetaType root (KindRow RowType)
        F.require root (LacksView (SymbolKey (Symbol "trying")) row)
        F.warn [ TextPart "trying" ]
      e <- F.globalRef root name []
      claimed <- F.typeOf e
      F.unify root claimed goalType
      pure (Just e)
    _ -> pure Nothing

  sameConstructorView = case _, _ of
    ConType ln lk, ConType rn rk -> ln == rn && lk == rk
    _, _ -> false

registry :: Registry
registry = Map.singleton searching hostPolicy

-- Running it ---------------------------------------------------------------------------------------

-- | What each step of the scenario came to.
type Scenario =
  { first :: Submission
  , equation :: Submission
  , report :: RunReport
  , zonked :: XExpr P.Int
  , core :: Either (NonEmptyArray (Residue P.Int)) (Expr P.Int)
  , state :: SolverState
  }

-- | The state the scenario starts from, with `?g` created in it.
start :: Either P.String (Tuple MetaVar SolverState)
start = case runElabIn env (initialState (SessionId 0) 10) (freshTypeMeta emptyXContext XKType) of
  Tuple (Done (XMeta g)) s -> Right (Tuple g s)
  Tuple other _ -> Left (show other)

-- | The hole filled, zonked, and taken across the boundary.
finished :: MetaVar -> Submission -> Submission -> RunReport -> SolverState -> XExpr P.Int -> Scenario
finished g first equation report state hole =
  let
    zonked = zonkExpr state.tentative.metas (ELet 0 (Ident "y") (XMeta g) hole (EVar 0 (Ident "y")))
  in
    { first, equation, report, zonked, core: toCoreExpr zonked, state }

-- | The scenario, the host's runner carrying out every attempt.
byHost :: Either P.String Scenario
byHost = start <#> \(Tuple g s0) ->
  let
    Tuple submitted s1 = submitSynthesis env registry site (XMeta g) searching Nothing s0
    Tuple equation s2 = submitAttempting (attemptJob env registry) site (equating g) s1
    Tuple report s3 = runSynthesis env registry s2
  in
    finished g submitted.submission equation report s3 (ETermMeta 7 submitted.target)

-- | The scenario, the goal's attempts carried out by the guest on the session.
byGuest :: Session -> Aff (Either P.String { scenario :: Scenario, attempts :: P.Int, health :: SessionHealth })
byGuest session = case start, bundle of
  Left err, _ -> pure (Left err)
  _, Left err -> pure (Left err)
  Right (Tuple g s0), Right trusted -> do
    guests <- liftEffect do
      cancellation <- newCancellation (Milliseconds 5000.0)
      attempts <- Ref.new 0
      health <- Ref.new Reusable
      pure { session, descriptor: trusted.descriptor, env, budget: 10_000_000, cancellation, attempts, health } :: _ Guests
    node (submitGuestSynthesis guests site (XMeta g) searching Nothing s0) >>= case _ of
      Left _ -> pure (Left "the submission was called off")
      Right (Tuple submitted s1) -> node (submitGuest guests site (equating g) s1) >>= case _ of
        Left _ -> pure (Left "the equation was called off")
        Right (Tuple equation s2) -> node (runGuests guests s2) >>= case _ of
          Left _ -> pure (Left "the run was called off")
          Right (Tuple report s3) -> liftEffect do
            attempts <- Ref.read guests.attempts
            health <- Ref.read guests.health
            pure (Right { scenario: finished g submitted.submission equation report s3 (ETermMeta 7 submitted.target), attempts, health })

-- | `?g ≡ Record (a : Boolean, z : Int)`.
equating :: MetaVar -> Job
equating g = JobUnify { kind: XKType, left: XMeta g, right: answerType }

-- | A session that has loaded `Base.String` and the policy, opened as given.
withPolicySession :: (Hello -> Aff (Either OpenFailure Session)) -> (Session -> Aff Unit) -> Aff Unit
withPolicySession open k = case compileGuests [ stringModule, policyModule ] of
  Left err -> fail ("the policy did not compile: " <> err)
  Right [ string, policy ] -> do
    FS.mkdir' dir { recursive: true, mode: Perms.mkPerms Perms.all Perms.all Perms.all }
    write "BaseStringEq" string
    write "Policy" policy
    open (hello { offers = [ "modules", "invoke", "kernel" ] }) >>= case _ of
      Left failure -> fail ("the session did not open: " <> show failure)
      Right session -> do
        node (Client.load session (pathOf "BaseStringEq")) >>= shouldEqual (Right (Right "Base.String"))
        node (Client.load session (pathOf "Policy")) >>= shouldEqual (Right (Right "Policy"))
        k session
        close' session >>= shouldEqual (Right unit)
  Right other -> fail ("expected two modules, got " <> show (Array.length other))
  where
  write name dmo = case encode dmo of
    Left err -> fail ("could not encode " <> name <> ": " <> show err)
    Right bytes -> liftEffect (Buffer.fromArray bytes) >>= FS.writeFile (pathOf name)

-- | `steam session`, started as a process.
asProcess :: Hello -> Aff (Either OpenFailure Session)
asProcess h = do
  s <- streams
  open' { command: "node", args: [ "steam/index.dev.js", "session" ], output: draining s, hello: h }

-- The cases ----------------------------------------------------------------------------------------

spec :: Spec Unit
spec = describe "a guest synthesizer against the host's, one scenario" do
  it "solves the goal through a wait and a candidate search, by the host, and the Core checker accepts it" do
    case byHost of
      Left err -> fail err
      Right host -> checkScenario host

  it "comes to the same, by a guest on a session, in every part of what the host holds" do
    withPolicySession asProcess \session -> byGuest session >>= case _, byHost of
      Left err, _ -> fail err
      _, Left err -> fail err
      Right guest, Right host -> do
        checkScenario guest.scenario
        -- one invocation for the attempt that waited, and one for the retry
        guest.attempts `shouldEqual` 2
        guest.health `shouldEqual` Reusable
        guest.scenario.first `shouldEqual` host.first
        guest.scenario.equation `shouldEqual` host.equation
        guest.scenario.report `shouldEqual` host.report
        guest.scenario.zonked `shouldEqual` host.zonked
        guest.scenario.core `shouldEqual` host.core
        guest.scenario.state.tentative.metas `shouldEqual` host.state.tentative.metas
        guest.scenario.state.tentative.obligations `shouldEqual` host.state.tentative.obligations
        guest.scenario.state.tentative.scheduler `shouldEqual` host.state.tentative.scheduler
        guest.scenario.state.retained.trace `shouldEqual` host.state.retained.trace
        fates guest.scenario.state.retained.trace `shouldEqual` fates host.state.retained.trace
        (guest.scenario.state == host.state) `shouldEqual` true

  it "comes to the same in a session served in this process, whether a guest runs in stretches of ten thousand steps or of one" do
    long <- runIn 10_000
    short <- runIn 1
    case long, short, byHost of
      Right l, Right s, Right host -> do
        checkScenario s.scenario
        s.attempts `shouldEqual` 2
        s.scenario.first `shouldEqual` l.scenario.first
        s.scenario.equation `shouldEqual` l.scenario.equation
        s.scenario.report `shouldEqual` l.scenario.report
        s.scenario.core `shouldEqual` l.scenario.core
        s.scenario.state.retained.trace `shouldEqual` l.scenario.state.retained.trace
        (s.scenario.state == l.scenario.state) `shouldEqual` true
        -- and what the host's runner came to, stretch by stretch
        (l.scenario.state == host.state) `shouldEqual` true
      Left err, _, _ -> fail err
      _, Left err, _ -> fail err
      _, _, Left err -> fail err
  where
  runIn quantum = do
    result <- liftEffect (Ref.new (Left "the session did not run"))
    withPolicySession (openInProcess quantum) \session -> byGuest session >>= liftEffect <<< flip Ref.write result
    liftEffect (Ref.read result)

-- | What one run of the scenario must come to, whichever runner ran it.
checkScenario :: Scenario -> Aff Unit
checkScenario run = do
  case run.first of
    Continue { attempt: Registered waited } -> Set.size waited `shouldEqual` 1
    other -> fail ("the first attempt did not wait: " <> show other)
  case run.equation of
    Continue { attempt: Committed } -> pure unit
    other -> fail ("the equation did not commit: " <> show other)
  run.report.result `shouldEqual` Completed
  -- the warning `cand1` made was rolled back with it
  run.report.warnings `shouldEqual` []
  case start of
    Right (Tuple g _) -> lookupMeta run.state.tentative.metas g `shouldEqual` Just (Assigned answerType)
    Left err -> fail err
  run.zonked `shouldEqual` ELet 0 (Ident "y") answerType (EGlobal 7 (inMain "cand2") []) (EVar 0 (Ident "y"))
  case run.core of
    Right core -> do
      globalsOf core `shouldEqual` Set.singleton (inMain "cand2")
      isRight (declare primSignature (completedWith core)) `shouldEqual` true
    Left residues -> fail ("the declaration did not cross the boundary: " <> show residues)
  let events = run.state.retained.trace
  case conversations events of
    [ waited, retried ] -> do
      Array.nub (fatesWhere (inConversation waited) events) `shouldEqual` [ RolledBack ]
      fatesWhere (inConversation retried && commanded (Kernel (ObserveRequest (LookupGlobal (inMain "cand0"))))) events `shouldEqual` [ Kept ]
      fatesWhere (inConversation retried && refersTo (inMain "cand1")) events `shouldEqual` [ RolledBack ]
      fatesWhere (inConversation retried && refersTo (inMain "cand2")) events `shouldEqual` [ Kept ]
    other -> fail ("expected two conversations: " <> show other)
  where
  completedWith value = valuesModule
    { decls = valuesModule.decls <> [ DeclNonRec 1 { name: Ident "answer", scheme: monoScheme (recordOf coreBoolean coreInt), value, attributes: [] } ] }

  conversations = Array.mapMaybe case _ of
    AttemptOpened e -> Just e.conversation
    _ -> Nothing

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
