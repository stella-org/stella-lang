-- | The kernel's observations.
-- |
-- | Three things are what these cases are for. **An observation reads against the
-- | current `Ψ` and changes nothing but the arena**, so one handle shows a
-- | metavariable before it is solved and its solution after. **Every part a view
-- | hands out carries kind evidence that is true where it stands**, binders a
-- | view descended under included. And **what depends on where it stands reads
-- | the frame**, which the runner sets from the job, so a goal woken far from its
-- | site still sees that site.
module Test.Stella.Compiler.Elaborate.Observe (spec) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.Catalog (EntrySort(..), catalogOf)
import Stella.Compiler.Elaborate.Context (Origin(..), XContext, assume, bindTyVar, bindVar, emptyXContext)
import Stella.Compiler.Elaborate.Diagnostic (Defect(..), Diagnostic(..))
import Stella.Compiler.Elaborate.Elab (Elab, Frame, Outcome(..), SessionEnv, SolverState, initialState, issue, runElabIn, throw, withFrame)
import Stella.Compiler.Elaborate.Handle (Handle, HandleClass(..), HandleError(..), HandleObject(..), SessionId(..))
import Stella.Compiler.Elaborate.Kind (XKind(..))
import Stella.Compiler.Elaborate.Kinding (KindEvidence(..), KindingEnv, KindingFault(..))
import Stella.Compiler.Elaborate.Observe (declsWithAttr, goalType, kindOf, localConstraints, localContext, lookupGlobal, normalizeRow, typeOf, viewType)
import Stella.Compiler.Elaborate.Pending (Job(..), PendingId(..), Site, newGoal)
import Stella.Compiler.Elaborate.Run (Attempt(..), attemptPendingWith)
import Stella.Compiler.Elaborate.Scheduler (create)
import Stella.Compiler.Elaborate.Term (XExpr(..))
import Stella.Compiler.Elaborate.Type (XConstraint(..), XRowEntry(..), XType(..))
import Stella.Compiler.Elaborate.Unify (MetaBinding(..), UnifyError(..), emptyContext, freshKindMeta, freshMeta)
import Stella.Compiler.Elaborate.View (ConstraintView(..), KindView(..), PayloadView(..), TypeView(..))
import Stella.Compiler.TypedCore as Core
import Stella.Compiler.TypedCore (AttrValue(..), EffName(..), Ident(..), Kind(..), Literal(..), ModuleName(..), Qualified(..), RowElemKind(..), RowKey(..), Symbol(..), TyName(..), TyVar(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..), fst)
import Effect.Aff (Aff)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

prim :: ModuleName
prim = ModuleName "Prim"

con :: P.String -> XType
con name = XCon (Qualified prim (TyName name)) []

xInt :: XType
xInt = con "Int"

listOf :: XType -> XType
listOf element = XApp (con "List") element

recordOf :: XType -> XType
recordOf row = XApp (con "Record") row

state :: Qualified EffName
state = Qualified (ModuleName "Main") (EffName "State")

kinding :: KindingEnv
kinding =
  { types: Map.fromFoldable
      [ Tuple (Qualified prim (TyName "Int")) { kindVars: [], body: KType }
      , Tuple (Qualified prim (TyName "List")) { kindVars: [], body: KFun KType KType }
      , Tuple (Qualified prim (TyName "Record")) { kindVars: [], body: KFun (KRow RowType) KType }
      ]
  , effects: Map.fromFoldable [ Tuple state [ KType ] ]
  }

showInt :: Qualified Ident
showInt = Qualified (ModuleName "Data.Show") (Ident "showInt")

session :: SessionEnv
session =
  { catalog: catalogOf
      [ { name: showInt
        , sort: ValueEntry
        , scheme: { kindVars: [], body: xInt }
        , attributes: [ { key: "typeclass.instance", value: AttrUnit } ]
        }
      ]
  , kinding
  }

x :: Ident
x = Ident "x"

y :: Ident
y = Ident "y"

a :: TyVar
a = TyVar "a"

r :: TyVar
r = TyVar "r"

keyN :: RowKey
keyN = SymbolKey (Symbol "n")

-- | A site binding `x : Int` and `y : List a`, with `a` and `r` in scope and
-- | `n ∉ r` assumed.
context :: XContext
context =
  assume
    (bindVar (bindVar (bindTyVar (bindTyVar emptyXContext a XKType) r (XKRow RowType)) y (listOf (XVar a))) x xInt)
    (XLacks keyN (XVar r))

site :: Site
site = { context, origin: InDeclaration (Qualified prim (Ident "decl")) }

frame :: Frame
frame = { site, goal: Nothing }

start :: SolverState
start = initialState (SessionId 0) 10

-- | Run an action under the frame, and continue with what it produced.
observing :: forall a. Show a => SolverState -> Elab a -> (a -> SolverState -> Aff Unit) -> Aff Unit
observing s action k = case runElabIn session s (withFrame frame action) of
  Tuple (Done value) s' -> k value s'
  Tuple outcome _ -> fail ("the observation did not complete: " <> show outcome)

outcomeOf :: forall a. SolverState -> Elab a -> Outcome a
outcomeOf s action = fst (runElabIn session s (withFrame frame action))

-- | A handle to a type standing at the kind evidence given, under the site's
-- | variables.
typeHandle :: XType -> KindEvidence -> Elab Handle
typeHandle ty kind = issue (TypeObject { type: ty, kind, scope: { kindVars: context.kindVars, tyVars: context.tyVars } })

-- | The type of `y`, from the local context.
typeOfY :: Elab Handle
typeOfY = do
  entries <- localContext
  case entries of
    [ _, entry ] -> pure entry.type
    _ -> throw failure

failure :: Diagnostic
failure = EquationFailed site.origin (TypeNotEqual xInt xInt)

spec :: Spec Unit
spec = describe "Elaborate.Observe" do
  describe "the local context" do
    it "is the site's bindings in ascending order of name, and its assumptions in order" do
      observing start (map (map _.name) localContext) \names _ -> names `shouldEqual` [ x, y ]
      observing start (localConstraints >>= traverseRow) \rows _ -> rows `shouldEqual` [ [ r ] ]

    it "is read from the frame, and refused where there is none" do
      fst (runElabIn session start localContext) `shouldEqual` Broke NoFrame

    it "is the job's own site where the runner attempts it, whatever the elaboration reached" do
      let
        Tuple id scheduler = create site (JobUnify { kind: XKType, left: xInt, right: xInt }) start.tentative.scheduler
        s0 = start { tentative { scheduler = scheduler } }
        reading _ = do
          names <- map (map _.name) localContext
          if names == [ x, y ] then pure unit else throw failure
      fst (attemptPendingWith session reading id s0) `shouldEqual` Committed

  describe "a view" do
    it "takes an application apart into handles standing at the kinds the head gives" do
      let
        action = do
          ty <- typeOfY
          view <- viewType ty
          case view of
            AppType f arg -> do
              fk <- kindOf f
              argView <- viewType arg
              pure (Tuple fk argView)
            _ -> throw failure
      observing start action \(Tuple fk argView) _ -> do
        fk `shouldEqual` KindFun KindType KindType
        argView `shouldEqual` VarType a

    it "carries a binder's kind to the body it descends into" do
      let
        b = TyVar "b"
        action = do
          ty <- typeHandle (XForall b XKType (listOf (XVar b))) (ExactKind XKType)
          view <- viewType ty
          case view of
            ForallType _ k body -> do
              inner <- viewType body
              case inner of
                AppType _ arg -> Tuple k <$> viewType arg
                _ -> throw failure
            _ -> throw failure
      observing start action \(Tuple k argView) _ -> do
        k `shouldEqual` KindType
        argView `shouldEqual` VarType b

    it "shows a row as its normal form, at the row kind it stands at" do
      let
        row = XRowExtend (XRowTypeEntry keyN xInt) (XVar r)
        action = do
          ty <- typeHandle (recordOf row) (ExactKind XKType)
          view <- viewType ty
          case view of
            AppType _ arg -> normalizeRow arg
            _ -> throw failure
      observing start action \rv _ -> do
        rv.elementKind `shouldEqual` Just RowType
        map _.key rv.known `shouldEqual` [ keyN ]
        rv.rigid `shouldEqual` [ r ]

    it "gives the empty row the kind its place fixes, and any row kind where nothing does" do
      let
        underRecord = do
          ty <- typeHandle (recordOf XRowEmpty) (ExactKind XKType)
          view <- viewType ty
          case view of
            AppType _ arg -> normalizeRow arg
            _ -> throw failure
        bare = typeHandle XRowEmpty AnyRow >>= \h -> Tuple <$> normalizeRow h <*> kindOf h
      observing start underRecord \rv _ -> rv.elementKind `shouldEqual` Just RowType
      observing start bare \(Tuple rv k) _ -> do
        rv.elementKind `shouldEqual` Nothing
        k `shouldEqual` KindAnyRow

    it "shows an effect's arguments at the kinds the effect declares" do
      let
        action = do
          ty <- typeHandle (XRowExtend (XRowEffectEntry state [ xInt ]) XRowEmpty) (ExactKind (XKRow RowEffect))
          rv <- normalizeRow ty
          case map _.payload rv.known of
            [ EffectPayload _ [ arg ] ] -> kindOf arg
            _ -> throw failure
      observing start action \k _ -> k `shouldEqual` KindType

    it "refuses a row observation of a type at no row kind" do
      let
        action = typeHandle xInt (ExactKind XKType) >>= \h -> Tuple h <$> normalizeRow h
      case outcomeOf start action of
        Broke (NotARowType _) -> pure unit
        outcome -> fail ("the row observation was not refused: " <> show outcome)

  describe "a metavariable" do
    it "is shown as a Meta handle, and as its solution once it is solved" do
      let
        Tuple m metas = freshMeta { kind: XKType, scope: { types: Set.empty, kinds: Set.empty } } emptyContext
        s0 = start { tentative { metas = metas } }
      observing s0 (typeHandle (XMeta m) (ExactKind XKType)) \h s1 -> do
        observing s1 (viewType h) \view _ -> case view of
          MetaType _ -> pure unit
          _ -> fail ("not a metavariable: " <> show view)
        let
          solved = s1 { tentative { metas { bindings = Map.insert m (Assigned xInt) s1.tentative.metas.bindings } } }
        observing solved (viewType h) \view _ -> view `shouldEqual` ConType (Qualified prim (TyName "Int")) []

    it "whose kind is not settled is not shown" do
      let
        Tuple k metas0 = freshKindMeta { scope: Set.empty, requirements: Set.empty } emptyContext
        Tuple m metas = freshMeta { kind: XKMeta k, scope: { types: Set.empty, kinds: Set.empty } } metas0
        s0 = start { tentative { metas = metas } }
        unsettled = frame { site { context = bindVar context (Ident "z") (XMeta m) } }
        action = withFrame unsettled (map (map _.name) localContext)
      fst (runElabIn session s0 action) `shouldEqual` Broke (KindingFailed KindNotSettled)

  describe "a goal and a term" do
    it "gives the running goal's type at Type, and a term's claimed type" do
      let
        Tuple goal metas = newGoal site xInt showInt start.tentative.metas
        s0 = start { tentative { metas = metas } }
        running = frame { goal = Just { id: PendingId 0, goal } }
        action = do
          g <- issue (GoalObject { id: PendingId 0, goal })
          e <- issue (ExprObject { term: ELit unit (LitInt 0), claimed: xInt })
          gv <- goalType g >>= viewType
          ev <- typeOf e >>= viewType
          pure (Tuple gv ev)
      case runElabIn session s0 (withFrame running action) of
        Tuple (Done (Tuple gv ev)) _ -> do
          gv `shouldEqual` ConType (Qualified prim (TyName "Int")) []
          ev `shouldEqual` ConType (Qualified prim (TyName "Int")) []
        Tuple outcome _ -> fail ("the observation did not complete: " <> show outcome)

    it "refuses a goal observed where no goal runs, or one not running" do
      let
        Tuple goal metas = newGoal site xInt showInt start.tentative.metas
        s0 = start { tentative { metas = metas } }
        observed = issue (GoalObject { id: PendingId 0, goal }) >>= goalType
        elsewhere = frame { goal = Just { id: PendingId 1, goal } }
      fst (runElabIn session s0 (withFrame frame (void observed)))
        `shouldEqual` Broke NoGoal
      fst (runElabIn session s0 (withFrame elsewhere (void observed)))
        `shouldEqual` Broke (GoalNotCurrent (PendingId 0) (PendingId 1))

    it "refuses a handle of the wrong class rather than answering nothing" do
      let
        action = do
          e <- issue (ExprObject { term: ELit unit (LitInt 0), claimed: xInt })
          Tuple e <$> viewType e
      case outcomeOf start action of
        Broke (InvalidHandle _ (HandleClassMismatch TypeClass)) -> pure unit
        outcome -> fail ("the handle was not refused: " <> show outcome)

  describe "the catalog" do
    it "looks an entry up, with its scheme at Type, and lists what carries an attribute" do
      let
        action = do
          decl <- lookupGlobal showInt
          absent <- lookupGlobal (Qualified prim (Ident "absent"))
          instances <- declsWithAttr "typeclass.instance"
          case decl of
            Just d -> do
              scheme <- viewType d.scheme
              pure { scheme, absent: map _.name absent, instances }
            Nothing -> throw failure
      observing start action \found _ -> do
        found.scheme `shouldEqual` ConType (Qualified prim (TyName "Int")) []
        found.absent `shouldEqual` Nothing
        found.instances `shouldEqual` [ showInt ]

  describe "a kind-polymorphic scheme" do
    it "is kinded under the kind variables it declares, and refused over ones it does not" do
      let
        k = Core.KindVar "k"
        polymorphic = XForall a (XKVar k) xInt
        entryOf name kindVars = { name, sort: ValueEntry, scheme: { kindVars, body: polymorphic }, attributes: [] }
        declared = Qualified prim (Ident "declared")
        undeclared = Qualified prim (Ident "undeclared")
        polySession = session { catalog = catalogOf [ entryOf declared [ k ], entryOf undeclared [] ] }
        viewed name = do
          decl <- lookupGlobal name
          case decl of
            Just d -> viewType d.scheme
            Nothing -> throw failure
      case fst (runElabIn polySession start (withFrame frame (viewed declared))) of
        Done (ForallType bound kind _) -> do
          bound `shouldEqual` a
          kind `shouldEqual` KindVar k
        outcome -> fail ("the scheme was not viewed: " <> show outcome)
      fst (runElabIn polySession start (withFrame frame (void (viewed undeclared))))
        `shouldEqual` Broke (KindingFailed (UnboundKindVar k))

  describe "what an observation changes" do
    it "is the arena and the generation, and nothing else" do
      let
        action = do
          ty <- typeOfY
          _ <- viewType ty
          _ <- localConstraints
          _ <- lookupGlobal showInt
          pure unit
      observing start action \_ s -> do
        s.tentative.metas `shouldEqual` start.tentative.metas
        s.tentative.obligations `shouldEqual` start.tentative.obligations
        s.tentative.scheduler `shouldEqual` start.tentative.scheduler
        s.tentative.written `shouldEqual` start.tentative.written
        s.retained.fuel `shouldEqual` start.retained.fuel
  where
  traverseRow :: P.Array ConstraintView -> Elab (P.Array (P.Array TyVar))
  traverseRow = traverse \c -> case c of
    LacksView _ h -> map _.rigid (normalizeRow h)
    DisjointView _ _ -> pure []
