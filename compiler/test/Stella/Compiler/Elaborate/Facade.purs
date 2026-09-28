-- | A synthesizer written against the kernel's requests alone, and the driver
-- | that runs it.
-- |
-- | Three things are what these cases are for. **The vocabulary is complete**:
-- | every public kernel operation has its request, each operation makes the
-- | request its name says, and takes back only the shape of answer that request
-- | is answered in. **A script is driven as a conversation**: its transactions
-- | are the conversation's, a failure inside answerOne resumes the script after it,
-- | and the goal it is given is the answerOne the attempt runs. And **a result is
-- | accepted before anything commits**: built at the goal's root, its claim
-- | unified with the goal's type, then assigned to the goal's target.
module Test.Stella.Compiler.Elaborate.Facade (spec) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.Catalog (catalogOf)
import Stella.Compiler.Elaborate.Constructors (emptyConstructorEnv)
import Stella.Compiler.Elaborate.Context (Origin(..), bindVar, emptyXContext)
import Stella.Compiler.Elaborate.Diagnostic (Defect(..), Diagnostic(..))
import Stella.Compiler.Elaborate.Drive (command, runSynthesizer)
import Stella.Compiler.Elaborate.Effects (emptyEffectEnv)
import Stella.Compiler.Elaborate.Elab (Outcome(..), SessionEnv, SolverState, createSynthesis, freshTypeMeta, initialState, runElabIn)
import Stella.Compiler.Elaborate.Facade (Synthesizer)
import Stella.Compiler.Elaborate.Facade.Internal (Facade(..), kernel)
import Stella.Compiler.Elaborate.Facade as F
import Stella.Compiler.Elaborate.Handle (Handle(..), HandleClass(..), SessionId(..))
import Stella.Compiler.Elaborate.Kind (XKind(..))
import Stella.Compiler.Elaborate.Kinding (kindingOf)
import Stella.Compiler.Elaborate.Message (FrozenMessagePart(..), MessagePart(..))
import Stella.Compiler.Elaborate.Pending (Job(..), PendingId, Site, goalOf, newGoal)
import Stella.Compiler.Elaborate.Request (AnswerShape(..), BuildRequest(..), Command(..), CommandAnswer(..), HandlerRequest(..), KernelAnswer(..), KernelRequest(..), ObserveRequest(..), RecordRequest(..), ReportRequest(..), SolveRequest(..), TermRequest(..), TreeRequest(..), answerShape, answersAs, expectedAnswerShape)
import Stella.Compiler.Elaborate.Run (Attempt(..), OpenResult(..), Response(..), Step(..), envelopeOf, openAttempt)
import Stella.Compiler.Elaborate.Scheduler (create, lookupPending, takeReady)
import Stella.Compiler.Elaborate.Term (TermMetaVar, XExpr(..))
import Stella.Compiler.Elaborate.Type (MetaVar, XType(..))
import Stella.Compiler.Elaborate.Unify (MetaBinding(..), TermBinding(..), lookupMeta, lookupTermMeta)
import Stella.Compiler.Elaborate.View (ConstraintView(..), KindView(..), PayloadView(..), TypeView(..))
import Stella.Compiler.TypedCore (Ident(..), Literal(..), ModuleName(..), OpName(..), Qualified(..), RowElemKind(..), RowKey(..), Symbol(..), TyVar(..))
import Stella.Compiler.TypedCore.Prim (intTy, primSignature, recordTy)
import Data.Array as Array
import Data.Either (Either(..), either)
import Data.Maybe (Maybe(..), isJust, isNothing)
import Data.Set as Set
import Data.Tuple (Tuple(..), fst)
import Effect.Aff (Aff)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

-- The vocabulary

-- | The name of the public kernel operation a request asks for. It matches
-- | every request, so a request added to the vocabulary does not compile here
-- | until it is named.
operationOf :: KernelRequest -> P.String
operationOf = case _ of
  BuildRequest r -> case r of
    RootScope -> "rootScope"
    TypeVariable _ _ -> "typeVariable"
    TypeConstructor _ _ _ -> "typeConstructor"
    ApplyType _ _ _ -> "applyType"
    EmptyRow _ -> "emptyRow"
    ExtendRow _ _ _ _ -> "extendRow"
    UnionRow _ _ _ -> "unionRow"
    OpenForall _ _ _ -> "openForall"
    CloseForall _ _ _ -> "closeForall"
    OpenConstraint _ _ -> "openConstraint"
    CloseConstraint _ _ _ -> "closeConstraint"
    InstantiateForall _ _ _ -> "instantiateForall"
    InstantiateScheme _ _ _ -> "instantiateScheme"
  TermRequest r -> case r of
    LocalVariable _ _ -> "localVariable"
    GlobalRef _ _ _ -> "globalRef"
    LiteralTerm _ _ -> "literal"
    TermApply _ _ _ -> "termApply"
    TypeApply _ _ _ -> "typeApply"
    ConstraintApply _ _ -> "constraintApply"
    OpenLambda _ _ _ -> "openLambda"
    CloseLambda _ _ _ _ -> "closeLambda"
    OpenTypeAbs _ _ _ -> "openTypeAbs"
    CloseTypeAbs _ _ _ -> "closeTypeAbs"
    OpenConstraintAbs _ _ -> "openConstraintAbs"
    CloseConstraintAbs _ _ _ -> "closeConstraintAbs"
    OpenLet _ _ _ -> "openLet"
    CloseLet _ _ _ -> "closeLet"
    OpenLetRec _ _ -> "openLetRec"
    CloseLetRec _ _ _ _ -> "closeLetRec"
    OpenJoin _ _ _ _ -> "openJoin"
    CloseJoin _ _ _ _ -> "closeJoin"
    Jump _ _ _ -> "jump"
  TreeRequest r -> case r of
    OpenCase _ _ -> "openCase"
    CloseCase _ _ _ _ -> "closeCase"
    Leaf _ _ -> "leaf"
    Guard _ _ _ _ -> "guard"
    OpenBind _ _ _ -> "openBind"
    CloseBind _ _ _ -> "closeBind"
    RecordField _ _ _ -> "recordField"
    OpenSwitchCtor _ _ _ _ -> "openSwitchCtor"
    OpenSwitchLit _ _ _ -> "openSwitchLit"
    OpenSwitchKey _ _ _ _ -> "openSwitchKey"
    CloseSwitch _ _ _ _ -> "closeSwitch"
  RecordRequest r -> case r of
    RecordEmpty _ -> "recordEmpty"
    RecordExtend _ _ _ _ -> "recordExtend"
    RecordSelect _ _ _ -> "recordSelect"
    RecordRestrict _ _ _ -> "recordRestrict"
    RecordUpdate _ _ _ _ -> "recordUpdate"
    RecordMerge _ _ _ -> "recordMerge"
    VariantInject _ _ _ -> "variantInject"
    VariantWeaken _ _ _ _ -> "variantWeaken"
    VariantAbsurd _ _ _ -> "variantAbsurd"
    OpenEff _ _ _ -> "openEff"
  HandlerRequest r -> case r of
    Perform _ _ _ _ _ _ -> "perform"
    OpenHandle _ _ _ _ _ _ _ _ -> "openHandle"
    CloseHandle _ _ _ _ _ -> "closeHandle"
    ReadCell _ _ -> "readCell"
    WriteCell _ _ _ -> "writeCell"
  SolveRequest r -> case r of
    FreshMetaType _ _ -> "freshMetaType"
    IsAssigned _ -> "isAssigned"
    Unify _ _ _ -> "unify"
    Entails _ _ -> "entails"
    Require _ _ -> "require"
    Subgoal _ _ _ -> "subgoal"
  ObserveRequest r -> case r of
    GoalType _ -> "goalType"
    ViewType _ -> "viewType"
    Whnf _ -> "whnf"
    NormalizeRow _ -> "normalizeRow"
    KindOf _ -> "kindOf"
    TypeOf _ -> "typeOf"
    LocalContext -> "localContext"
    LocalConstraints -> "localConstraints"
    LookupGlobal _ -> "lookupGlobal"
    DeclsWithAttr _ -> "declsWithAttr"
  ReportRequest r -> case r of
    Throw _ -> "throw"
    Warn _ -> "warn"
    Postpone _ -> "postpone"

-- | The public kernel operations, as the kernel's modules export them.
publicOperations :: P.Array P.String
publicOperations =
  -- Build
  [ "rootScope"
  , "typeVariable"
  , "typeConstructor"
  , "applyType"
  , "emptyRow"
  , "extendRow"
  , "unionRow"
  , "openForall"
  , "closeForall"
  , "openConstraint"
  , "closeConstraint"
  , "instantiateForall"
  , "instantiateScheme"
  -- BuildTerm
  , "localVariable"
  , "globalRef"
  , "literal"
  , "termApply"
  , "typeApply"
  , "constraintApply"
  , "openLambda"
  , "closeLambda"
  , "openTypeAbs"
  , "closeTypeAbs"
  , "openConstraintAbs"
  , "closeConstraintAbs"
  , "openLet"
  , "closeLet"
  , "openLetRec"
  , "closeLetRec"
  , "openJoin"
  , "closeJoin"
  , "jump"
  -- BuildTree
  , "openCase"
  , "closeCase"
  , "leaf"
  , "guard"
  , "openBind"
  , "closeBind"
  , "recordField"
  , "openSwitchCtor"
  , "openSwitchLit"
  , "openSwitchKey"
  , "closeSwitch"
  -- BuildRecord
  , "recordEmpty"
  , "recordExtend"
  , "recordSelect"
  , "recordRestrict"
  , "recordUpdate"
  , "recordMerge"
  , "variantInject"
  , "variantWeaken"
  , "variantAbsurd"
  , "openEff"
  -- BuildHandler
  , "perform"
  , "openHandle"
  , "closeHandle"
  , "readCell"
  , "writeCell"
  -- Solve
  , "freshMetaType"
  , "isAssigned"
  , "unify"
  , "entails"
  , "require"
  , "subgoal"
  -- Observe
  , "goalType"
  , "viewType"
  , "whnf"
  , "normalizeRow"
  , "kindOf"
  , "typeOf"
  , "localContext"
  , "localConstraints"
  , "lookupGlobal"
  , "declsWithAttr"
  -- Report
  , "throw"
  , "warn"
  , "postpone"
  ]

-- | Every shape of answer.
allShapes :: P.Array AnswerShape
allShapes =
  [ UnitShape
  , HandleShape
  , BooleanShape
  , TypeViewShape
  , RowViewShape
  , KindViewShape
  , ContextShape
  , ConstraintsShape
  , DeclShape
  , NamesShape
  , BinderShape
  , AssumptionShape
  , ConstraintAbsShape
  , LetRecShape
  , JoinShape
  , CaseShape
  , SwitchCtorShape
  , SwitchLitShape
  , SwitchKeyShape
  , HandlerShape
  ]

-- | A handle standing for whatever an operation is given; nothing here resolves
-- | answerOne.
h :: P.Int -> Handle
h n = Handle { session: SessionId 0, handleClass: TypeClass, slot: n, generation: n }

-- | An answer of every shape.
answers :: P.Array KernelAnswer
answers =
  [ UnitAnswer
  , HandleAnswer (h 0)
  , BooleanAnswer true
  , TypeViewAnswer (VarType (TyVar "t"))
  , RowViewAnswer { elementKind: Nothing, known: [], rigid: [], flexible: [] }
  , KindViewAnswer KindType
  , ContextAnswer []
  , ConstraintsAnswer []
  , DeclAnswer Nothing
  , NamesAnswer []
  , BinderAnswer { binder: h 0, variable: h 1, bodyScope: h 2 }
  , AssumptionAnswer { assumption: h 0, bodyScope: h 1 }
  , ConstraintAbsAnswer { binder: h 0, bodyScope: h 1 }
  , LetRecAnswer { binder: h 0, variables: [], bodyScope: h 1 }
  , JoinAnswer { binder: h 0, join: h 1, params: [], definitionScope: h 2, bodyScope: h 3 }
  , CaseAnswer { binder: h 0, scrutinees: [], treeScope: h 1 }
  , SwitchCtorAnswer { binder: h 0, branches: [], fallback: Nothing }
  , SwitchLitAnswer { binder: h 0, branches: [], fallback: h 1 }
  , SwitchKeyAnswer { binder: h 0, branches: [], fallback: Nothing }
  , HandlerAnswer { binder: h 0, returnClause: { variable: h 1, scope: h 2 }, clauses: [] }
  ]

-- | What an operation, called once, makes and takes back.
type Probe = { operation :: P.String, request :: Maybe KernelRequest, accepted :: P.Array AnswerShape }

probe :: forall a. P.String -> Facade a -> Probe
probe operation = case _ of
  Ask request next -> { operation, request: Just request, accepted: map answerShape (Array.filter (isJust <<< next) answers) }
  _ -> { operation, request: Nothing, accepted: [] }

-- | Every operation, called once.
probes :: P.Array Probe
probes =
  [ p "rootScope" F.rootScope
  , p "typeVariable" (F.typeVariable s (TyVar "t"))
  , p "typeConstructor" (F.typeConstructor s intTy [])
  , p "applyType" (F.applyType s s s)
  , p "emptyRow" (F.emptyRow s)
  , p "extendRow" (F.extendRow s key (TypePayload s) s)
  , p "unionRow" (F.unionRow s s s)
  , p "openForall" (F.openForall s "t" KindType)
  , p "closeForall" (F.closeForall s s s)
  , p "openConstraint" (F.openConstraint s (LacksView key s))
  , p "closeConstraint" (F.closeConstraint s s s)
  , p "instantiateForall" (F.instantiateForall s s s)
  , p "instantiateScheme" (F.instantiateScheme s name [])
  , p "localVariable" (F.localVariable s (Ident "x"))
  , p "globalRef" (F.globalRef s name [])
  , p "literal" (F.literal s (LitInt 1))
  , p "termApply" (F.termApply s s s)
  , p "typeApply" (F.typeApply s s s)
  , p "constraintApply" (F.constraintApply s s)
  , p "openLambda" (F.openLambda s "x" s)
  , p "closeLambda" (F.closeLambda s s s s)
  , p "openTypeAbs" (F.openTypeAbs s "t" KindType)
  , p "closeTypeAbs" (F.closeTypeAbs s s s)
  , p "openConstraintAbs" (F.openConstraintAbs s (LacksView key s))
  , p "closeConstraintAbs" (F.closeConstraintAbs s s s)
  , p "openLet" (F.openLet s "x" s)
  , p "closeLet" (F.closeLet s s s)
  , p "openLetRec" (F.openLetRec s [ { hint: "f", type: s } ])
  , p "closeLetRec" (F.closeLetRec s s [ s ] s)
  , p "openJoin" (F.openJoin s "j" [] s)
  , p "closeJoin" (F.closeJoin s s s s)
  , p "jump" (F.jump s s [])
  , p "openCase" (F.openCase s [ s ])
  , p "closeCase" (F.closeCase s s Nothing s)
  , p "leaf" (F.leaf s s)
  , p "guard" (F.guard s s s s)
  , p "openBind" (F.openBind s s "x")
  , p "closeBind" (F.closeBind s s s)
  , p "recordField" (F.recordField s s key)
  , p "openSwitchCtor" (F.openSwitchCtor s s [ name ] false)
  , p "openSwitchLit" (F.openSwitchLit s s [ LitInt 1 ])
  , p "openSwitchKey" (F.openSwitchKey s s [ key ] false)
  , p "closeSwitch" (F.closeSwitch s s [ s ] Nothing)
  , p "recordEmpty" (F.recordEmpty s)
  , p "recordExtend" (F.recordExtend s key s s)
  , p "recordSelect" (F.recordSelect s key s)
  , p "recordRestrict" (F.recordRestrict s key s)
  , p "recordUpdate" (F.recordUpdate s key s s)
  , p "recordMerge" (F.recordMerge s s s)
  , p "variantInject" (F.variantInject s key s)
  , p "variantWeaken" (F.variantWeaken s key s s)
  , p "variantAbsurd" (F.variantAbsurd s s s)
  , p "openEff" (F.openEff s s s)
  , p "perform" (F.perform s key (TypePayload s) (OpName "op") [] s)
  , p "openHandle" (F.openHandle s s key (TypePayload s) Nothing s s [])
  , p "closeHandle" (F.closeHandle s s s [] [])
  , p "readCell" (F.readCell s key)
  , p "writeCell" (F.writeCell s key s)
  , p "freshMetaType" (F.freshMetaType s KindType)
  , p "isAssigned" (F.isAssigned s)
  , p "unify" (F.unify s s s)
  , p "entails" (F.entails s (LacksView key s))
  , p "require" (F.require s (LacksView key s))
  , p "subgoal" (F.subgoal s s name)
  , p "goalType" (F.goalType s)
  , p "viewType" (F.viewType s)
  , p "whnf" (F.whnf s)
  , p "normalizeRow" (F.normalizeRow s)
  , p "kindOf" (F.kindOf s)
  , p "typeOf" (F.typeOf s)
  , p "localContext" F.localContext
  , p "localConstraints" F.localConstraints
  , p "lookupGlobal" (F.lookupGlobal name)
  , p "declsWithAttr" (F.declsWithAttr "instance")
  , p "throw" (F.throw [ TextPart "no" ] :: Facade Unit)
  , p "warn" (F.warn [ TextPart "w" ])
  , p "postpone" (F.postpone [ s ] :: Facade Unit)
  ]
  where
  s = h 0
  key = SymbolKey (Symbol "k")
  name = Qualified (ModuleName "Main") (Ident "x")

  p :: forall a. P.String -> Facade a -> Probe
  p = probe

-- Driving

xInt :: XType
xInt = XCon intTy []

session :: SessionEnv
session = { catalog: catalogOf [], kinding: kindingOf primSignature, constructors: emptyConstructorEnv, effects: emptyEffectEnv }

resolver :: Qualified Ident
resolver = Qualified (ModuleName "Typeclass") (Ident "resolve")

site :: Site
site = { context: emptyXContext, origin: InDeclaration (Qualified (ModuleName "Main") (Ident "decl")) }

-- | A goal at the type given of `?a`, created and taken from the ready queue, with its
-- | target, and the type metavariable `?a` created before it.
type Asked = { id :: PendingId, target :: TermMetaVar, a :: MetaVar, taken :: SolverState }

asking :: (XType -> XType) -> Either P.String Asked
asking goalAt = case runElabIn session (initialState (SessionId 0) 10) created of
  Tuple (Done (Tuple (Tuple id target) (XMeta a))) queued -> case takeReady queued.tentative.scheduler of
    Just (Tuple _ scheduler) -> Right { id, target, a, taken: queued { tentative { scheduler = scheduler } } }
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

assigned :: SolverState -> TermMetaVar -> Maybe (XExpr Unit)
assigned s m = case lookupTermMeta s.tentative.metas m of
  Just (TermAssigned e) -> Just e
  _ -> Nothing

answerOne :: Synthesizer
answerOne _ = F.rootScope >>= \root -> F.literal root (LitInt 1)

spec :: Spec Unit
spec = describe "Elaborate.Facade" do
  describe "the vocabulary" do
    it "has a request for every public kernel operation, each made by the operation of its name" do
      Array.length publicOperations `shouldEqual` 77
      Set.size (Set.fromFoldable publicOperations) `shouldEqual` 77
      map _.operation probes `shouldEqual` publicOperations
      map (\e -> map operationOf e.request) probes `shouldEqual` map Just publicOperations

    it "has an answer of every shape to try an operation with" do
      Set.fromFoldable (map answerShape answers) `shouldEqual` Set.fromFoldable allShapes
      Array.length allShapes `shouldEqual` Set.size (Set.fromFoldable allShapes)

    it "has each operation take back only the shape the table gives its request, and none for throw and postpone" do
      map (\e -> { operation: e.operation, accepted: e.accepted }) probes
        `shouldEqual` map (\e -> { operation: e.operation, accepted: Array.fromFoldable (e.request >>= expectedAnswerShape) }) probes
      map (\e -> e.request >>= expectedAnswerShape) (Array.filter (\e -> e.operation == "throw" || e.operation == "postpone") probes)
        `shouldEqual` [ Nothing, Nothing ]

    it "holds the host's answers to the table" do
      answersAs (BuildRequest RootScope) (HandleAnswer (h 0)) `shouldEqual` true
      answersAs (BuildRequest RootScope) UnitAnswer `shouldEqual` false
      answersAs (ReportRequest (Throw [])) UnitAnswer `shouldEqual` false
      Array.filter (answersAs (ReportRequest (Postpone []))) answers `shouldEqual` []

  describe "a synthesizer" do
    it "is given its goal, and its result is assigned to the goal's target" do
      given \g -> do
        let
          observed goal = do
            ty <- F.goalType goal
            F.viewType ty >>= case _ of
              ConType name [] | name == intTy -> answerOne goal
              other -> F.throw [ TextPart (show other) ]
        case runSynthesizer session observed g.id g.taken of
          Tuple Committed s -> do
            assigned s g.target `shouldEqual` Just (ELit unit (LitInt 1))
            isNothing (lookupPending s.tentative.scheduler g.id) `shouldEqual` true
          Tuple other _ -> fail (show other)

    it "has its result's claim unified with the goal's type before the result is assigned" do
      givenAt identity \g -> case runSynthesizer session answerOne g.id g.taken of
        Tuple Committed s -> do
          case lookupMeta s.tentative.metas g.a of
            Just (Assigned ty) -> ty `shouldEqual` xInt
            other -> fail ("?a was not solved: " <> show (map (const unit) other))
          assigned s g.target `shouldEqual` Just (ELit unit (LitInt 1))
        Tuple other _ -> fail (show other)

    it "whose result's claim the goal's type refutes fails, and nothing is assigned" do
      given \g -> do
        let
          misclaimed _ = F.rootScope >>= \root -> F.literal root (LitBoolean true)
        case runSynthesizer session misclaimed g.id g.taken of
          Tuple (Rejected (EquationFailed _ _)) s -> do
            assigned s g.target `shouldEqual` Nothing
            isNothing (lookupPending s.tentative.scheduler g.id) `shouldEqual` true
          Tuple other _ -> fail (show other)

    it "whose result's claim the goal's type cannot yet be equated with waits, and nothing is assigned" do
      let
        -- A goal at `Record (?r ∪ ?s)`, which a result at `Record (n : Int)`
        -- is equated with only once `?r` or `?s` is solved: the row has two
        -- solutions until then.
        created = do
          r <- freshTypeMeta emptyXContext (XKRow RowType)
          s <- freshTypeMeta emptyXContext (XKRow RowType)
          Tuple id t <- createSynthesis site (XApp (XCon recordTy []) (XRowUnion r s)) resolver Nothing
          pure { id, target: t, r, s }
        record _ = do
          root <- F.rootScope
          one <- F.literal root (LitInt 1)
          F.recordEmpty root >>= F.recordExtend root (SymbolKey (Symbol "n")) one
      case runElabIn session (initialState (SessionId 0) 10) created of
        Tuple (Done made@{ r: XMeta r, s: XMeta s }) queued -> case takeReady queued.tentative.scheduler of
          Just (Tuple _ scheduler) -> case runSynthesizer session record made.id (queued { tentative { scheduler = scheduler } }) of
            Tuple (Registered waited) after -> do
              waited `shouldEqual` Set.fromFoldable [ r, s ]
              assigned after made.target `shouldEqual` Nothing
              isJust (lookupPending after.tentative.scheduler made.id) `shouldEqual` true
            Tuple other _ -> fail (show other)
          Nothing -> fail "no job was queued"
        Tuple other _ -> fail (show other)

    it "whose result escapes its target is rejected, and the claim's equation is rolled back with it" do
      let
        -- The job stands where `x : Int` is bound, and its target where
        -- nothing is: a result mentioning `x` is equated with the goal's `?a`,
        -- then refused by the target.
        x = Ident "x"
        wide = site { context = bindVar emptyXContext x xInt }
        created = do
          a <- freshTypeMeta emptyXContext XKType
          pure a
      case runElabIn session (initialState (SessionId 0) 10) created of
        Tuple (Done (XMeta a)) s0 ->
          let
            Tuple goal metas = newGoal site (XMeta a) resolver Nothing s0.tentative.metas
            Tuple id scheduler = create wide (JobSynthesis goal) s0.tentative.scheduler
            start = s0 { tentative { metas = metas, scheduler = scheduler } }
            mentioning _ = F.rootScope >>= \root -> F.localVariable root x
          in
            case runSynthesizer session mentioning id start of
              Tuple (Rejected (TermAssignmentFailed _ _)) s -> do
                case lookupMeta s.tentative.metas a of
                  Just (Unsolved _) -> pure unit
                  _ -> fail "the claim's equation was kept"
                assigned s (goalOf goal).target `shouldEqual` Nothing
              Tuple other _ -> fail (show other)
        Tuple other _ -> fail (show other)

    it "whose result is not built at the goal's root is a defect" do
      given \g -> do
        let
          inner _ = do
            root <- F.rootScope
            i <- F.typeConstructor root intTy []
            lam <- F.openLambda root "x" i
            body <- F.literal lam.bodyScope (LitInt 1)
            _ <- F.emptyRow root >>= F.closeLambda root lam.binder body
            pure body
        case runSynthesizer session inner g.id g.taken of
          Tuple (Halted (ResultNotAtRoot _)) s -> do
            assigned s g.target `shouldEqual` Nothing
            isJust (lookupPending s.tentative.scheduler g.id) `shouldEqual` true
          Tuple other _ -> fail (show other)

    it "tries a candidate in a transaction, and goes on after it with the failure that ended it" do
      given \g -> do
        let
          tried goal = do
            first <- F.transact (F.warn [ TextPart "discarded" ] *> F.throw [ TextPart "no" ] :: Facade Handle)
            case first of
              Left (SynthesisFailed report) | report.message == [ FrozenText "no" ] -> do
                F.warn [ TextPart "kept" ]
                answerOne goal
              _ -> F.throw [ TextPart "the candidate did not fail as it should" ]
        case runSynthesizer session tried g.id g.taken of
          Tuple Committed s -> do
            map _.message s.tentative.warnings `shouldEqual` [ [ FrozenText "kept" ] ]
            assigned s g.target `shouldEqual` Just (ELit unit (LitInt 1))
          Tuple other _ -> fail (show other)

    it "has a failure inside nested transactions caught by the inner one alone" do
      given \g -> do
        let
          nested goal = do
            outer <- F.transact do
              inner <- F.transact (F.throw [ TextPart "inner" ] :: Facade Unit)
              F.warn [ TextPart (either (const "caught") (const "missed") inner) ]
            case outer of
              Right _ -> answerOne goal
              Left _ -> F.throw [ TextPart "the outer transaction failed" ]
        case runSynthesizer session nested g.id g.taken of
          Tuple Committed s -> map _.message s.tentative.warnings `shouldEqual` [ [ FrozenText "caught" ] ]
          Tuple other _ -> fail (show other)

    it "that postpones on a metavariable its goal's type shows is registered under it" do
      givenAt identity \g -> do
        let
          waiting goal = F.goalType goal >>= F.viewType >>= case _ of
            MetaType m -> F.postpone [ m ]
            other -> F.throw [ TextPart (show other) ]
        case runSynthesizer session waiting g.id g.taken of
          Tuple attempt s -> do
            attempt `shouldEqual` Registered (Set.singleton g.a)
            isJust (lookupPending s.tentative.scheduler g.id) `shouldEqual` true

    it "that postpones on nothing is a defect" do
      given \g -> case runSynthesizer session (\_ -> F.postpone []) g.id g.taken of
        Tuple (Halted (PostponementInadmissible _)) _ -> pure unit
        Tuple other _ -> fail (show other)

    it "taking back an answer of the wrong shape is a defect, and rolled back" do
      given \g -> do
        let
          mistaken _ = F.warn [ TextPart "w" ] *> kernel (BuildRequest RootScope) (const Nothing)
        case runSynthesizer session mistaken g.id g.taken of
          Tuple (Halted (AnswerShapeMismatch (BuildRequest RootScope) (HandleAnswer _))) s -> do
            s.tentative.warnings `shouldEqual` []
            isJust (lookupPending s.tentative.scheduler g.id) `shouldEqual` true
          Tuple other _ -> fail (show other)

  describe "a conversation driven by commands" do
    it "answers each command, and finishes by accepting the result" do
      given \g -> case openAttempt session g.id g.taken of
        Opened c0 -> case command (envelopeOf c0) BeginTransaction c0 of
          Answered (Returned (TransactionBegun _)) c1 -> case command (envelopeOf c1) (Kernel (BuildRequest RootScope)) c1 of
            Answered (Returned (KernelAnswered (HandleAnswer root))) c2 ->
              case command (envelopeOf c2) (Kernel (TermRequest (LiteralTerm root (LitInt 1)))) c2 of
                Answered (Returned (KernelAnswered (HandleAnswer e))) c3 -> case command (envelopeOf c3) CommitTransaction c3 of
                  Answered (Returned TransactionCommitted) c4 -> case command (envelopeOf c4) (Finish e) c4 of
                    Finished Committed s -> assigned s g.target `shouldEqual` Just (ELit unit (LitInt 1))
                    other -> fail (showStep other)
                  other -> fail (showStep other)
                other -> fail (showStep other)
            other -> fail (showStep other)
          other -> fail (showStep other)
        OpenStopped attempt _ -> fail (show attempt)

    it "answers a failure inside a transaction with the transaction it closed" do
      given \g -> case openAttempt session g.id g.taken of
        Opened c0 -> case command (envelopeOf c0) BeginTransaction c0 of
          Answered (Returned (TransactionBegun t)) c1 ->
            case command (envelopeOf c1) (Kernel (ReportRequest (Throw [ TextPart "no" ]))) c1 of
              Answered (CandidateFailed failed _) _ -> failed `shouldEqual` t
              other -> fail (showStep other)
          other -> fail (showStep other)
        OpenStopped attempt _ -> fail (show attempt)

  describe "a job" do
    it "with no goal gives a synthesizer nothing, and is a defect" do
      let
        start = initialState (SessionId 0) 10
        Tuple id scheduler = create site (JobUnify { kind: XKType, left: xInt, right: xInt }) start.tentative.scheduler
      fst (runSynthesizer session answerOne id (start { tentative { scheduler = scheduler } })) `shouldEqual` Halted NoGoal

showStep :: forall a. Show a => Step a -> P.String
showStep = case _ of
  Answered (Returned a) _ -> "returned " <> show a
  Answered (CandidateFailed token d) _ -> "failed in " <> show token <> ": " <> show d
  Finished attempt _ -> "finished: " <> show attempt
