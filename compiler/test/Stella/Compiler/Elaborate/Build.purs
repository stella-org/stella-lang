-- | The kernel's type builders.
-- |
-- | Three things are what these cases are for. **A builder uses a type only
-- | where it was built**: in the scope given or in one of its ancestors, never
-- | in a descendant or a sibling. **A type observed carries the scope it came
-- | from**: the site's is the root's, a part of a type is the scope of the
-- | whole, and a `forall` body, a constraint's body and a catalog scheme belong
-- | to no scope until the operation that opens them. And **what a builder
-- | allocates is the attempt's**: a rolled-back attempt gives back its fresh
-- | names and scopes with its handles.
module Test.Stella.Compiler.Elaborate.Build (spec) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.Build (applyType, closeConstraint, closeForall, emptyRow, extendRow, instantiateForall, instantiateScheme, openConstraint, openForall, rootScope, typeConstructor, typeVariable, unionRow)
import Stella.Compiler.Elaborate.Constructors (emptyConstructorEnv)
import Stella.Compiler.Elaborate.Effects (emptyEffectEnv)
import Stella.Compiler.Elaborate.Catalog (EntrySort(..), catalogOf)
import Stella.Compiler.Elaborate.Context (Origin(..), XContext, bindKindVars, bindTyVar, bindVar, emptyXContext)
import Stella.Compiler.Elaborate.Diagnostic (BuildError(..), Defect(..), Diagnostic(..))
import Stella.Compiler.Elaborate.Elab (Cause(..), Elab, Frame, Outcome(..), SessionEnv, SolverState, initialState, issue, resolveType, runElabIn, raiseDiagnostic, transact, unify, withFrame)
import Stella.Compiler.Elaborate.Handle (Handle, HandleObject(..), ScopeId(..), SessionId(..), TypeObject)
import Stella.Compiler.Elaborate.Kind (XKind(..))
import Stella.Compiler.Elaborate.Kinding (KindEvidence(..), KindingEnv, KindingFault(..))
import Stella.Compiler.Elaborate.Observe (localContext, lookupGlobal, normalizeRow, viewType)
import Stella.Compiler.Elaborate.Obligation (Basis(..), Breach(..))
import Stella.Compiler.Elaborate.Pending (EqualityGoal, Job(..), Pending, Site)
import Stella.Compiler.Elaborate.Run (Attempt(..), attemptPendingWith, runAttempt)
import Stella.Compiler.Elaborate.Scheduler (create, emptyScheduler)
import Stella.Compiler.Elaborate.Type (MetaVar, XConstraint(..), XRowEntry(..), XType(..))
import Stella.Compiler.Elaborate.Unify (MetaBinding(..), MetaContext, UnifyError(..), emptyContext, freshMeta)
import Stella.Compiler.Elaborate.View (ConstraintView(..), KindView(..), PayloadView(..), TypeView(..))
import Stella.Compiler.TypedCore as Core
import Stella.Compiler.TypedCore (EffName(..), Ident(..), Kind(..), ModuleName(..), Qualified(..), RowElemKind(..), RowKey(..), Symbol(..), Tag(..), TyName(..), TyVar(..))
import Data.Either (Either(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Data.Tuple (Tuple(..), fst, snd)
import Effect.Aff (Aff)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

prim :: ModuleName
prim = ModuleName "Prim"

tyName :: P.String -> Qualified TyName
tyName name = Qualified prim (TyName name)

con :: P.String -> XType
con name = XCon (tyName name) []

xInt :: XType
xInt = con "Int"

listOf :: XType -> XType
listOf element = XApp (con "List") element

recordOf :: XType -> XType
recordOf row = XApp (con "Record") row

kinding :: KindingEnv
kinding =
  { types: Map.fromFoldable
      [ Tuple (tyName "Int") { kindVars: [], body: KType }
      , Tuple (tyName "List") { kindVars: [], body: KFun KType KType }
      , Tuple (tyName "Record") { kindVars: [], body: KFun (KRow RowType) KType }
      ]
  , effects: Map.fromFoldable [ Tuple state [ KType ] ]
  }

state :: Qualified EffName
state = Qualified (ModuleName "Main") (EffName "State")

global :: P.String -> Qualified Ident
global name = Qualified (ModuleName "Main") (Ident name)

k :: Core.KindVar
k = Core.KindVar "k"

j :: Core.KindVar
j = Core.KindVar "j"

keyN :: RowKey
keyN = SymbolKey (Symbol "n")

-- | Monomorphic schemes whose parts a view hands out, one scheme polymorphic in
-- | a kind, and two ill-formed schemes mentioning a type variable and a kind
-- | variable they do not declare, which the site happens to bind.
session :: SessionEnv
session =
  { catalog: catalogOf
      [ entry "ints" [] (listOf xInt)
      , entry "record" [] (recordOf (XRowExtend (XRowTypeEntry keyN xInt) XRowEmpty))
      , entry "poly" [ k ] (XForall (TyVar "v") (XKVar k) xInt)
      , entry "freeType" [] (listOf (XVar a))
      , entry "freeKind" [] (XForall (TyVar "v") (XKVar j) xInt)
      ]
  , kinding
  , constructors: emptyConstructorEnv
  , effects: emptyEffectEnv
  }
  where
  entry name kindVars body = { name: global name, sort: ValueEntry, scheme: { kindVars, body }, attributes: [] }

a :: TyVar
a = TyVar "a"

r :: TyVar
r = TyVar "r"

-- | A site binding the kind variable `j`, `a : Type` and `r : Row Type`, with
-- | `y : List a`.
context :: XContext
context =
  bindVar (bindTyVar (bindTyVar (bindKindVars emptyXContext [ j ]) a XKType) r (XKRow RowType)) (Ident "y") (listOf (XVar a))

site :: Site
site = { context, origin: InDeclaration (Qualified prim (Ident "decl")) }

frame :: Frame
frame = { site, goal: Nothing }

start :: SolverState
start = initialState (SessionId 0) 10

outcomeOf :: forall a. SolverState -> Elab a -> Outcome a
outcomeOf s action = fst (runElabIn session s (withFrame frame action))

-- | The type an action builds, as the arena holds it.
builds :: SolverState -> Elab Handle -> (TypeObject -> Aff Unit) -> Aff Unit
builds s action check = case outcomeOf s (action >>= resolveType) of
  Done object -> check object
  other -> fail ("the builder did not complete: " <> show other)

-- | What a builder refuses, as the defect it reports.
refuses :: forall a. Show a => Elab a -> (BuildError -> Aff Unit) -> Aff Unit
refuses = refusesIn start

refusesIn :: forall a. Show a => SolverState -> Elab a -> (BuildError -> Aff Unit) -> Aff Unit
refusesIn s action check = case outcomeOf s action of
  Broke (BuildRejected err) -> check err
  other -> fail ("the builder did not refuse: " <> show other)

scopeViolation :: BuildError -> Aff Unit
scopeViolation = case _ of
  ScopeViolation _ -> pure unit
  other -> fail ("not a scope violation: " <> show other)

-- | A handle to a type observed at the site, carrying the root's scope.
observed :: XType -> KindEvidence -> Elab Handle
observed ty kind = issue (TypeObject { type: ty, kind, scope: { kindVars: context.kindVars, tyVars: context.tyVars }, builtIn: Just (ScopeId 0) })

int :: Handle -> Elab Handle
int scope = typeConstructor scope (tyName "Int") []

list :: Handle -> Elab Handle
list scope = typeConstructor scope (tyName "List") []

-- | `forall t. List t`, built in the root.
forallList :: Elab Handle
forallList = do
  root <- rootScope
  opened <- openForall root "t" KindType
  body <- list opened.bodyScope >>= \l -> applyType opened.bodyScope l opened.variable
  closeForall root opened.binder body

-- | The scheme a catalog entry is observed at.
scheme :: P.String -> Elab Handle
scheme name = lookupGlobal (global name) >>= case _ of
  Just decl -> pure decl.scheme
  Nothing -> raiseDiagnostic failure

failure :: Diagnostic
failure = EquationFailed site.origin (TypeNotEqual xInt xInt)

t0 :: TyVar
t0 = TyVar "t#0"

spec :: Spec Unit
spec = describe "Elaborate.Build" do
  describe "the root scope" do
    it "is opened on the frame, and there is none without one" do
      case fst (runElabIn session start rootScope) of
        Broke NoFrame -> pure unit
        other -> fail ("expected NoFrame: " <> show other)

    it "builds what the site binds, and refuses a variable it does not bind" do
      builds start (rootScope >>= \root -> typeVariable root a) \object -> do
        object.type `shouldEqual` XVar a
        object.kind `shouldEqual` ExactKind XKType
        object.builtIn `shouldEqual` Just (ScopeId 0)
      refuses (rootScope >>= \root -> typeVariable root (TyVar "b")) (_ `shouldEqual` UnboundTypeVariable (TyVar "b"))

  describe "constructors and applications" do
    it "kinds what they build" do
      builds start (rootScope >>= \root -> join (applyType root <$> list root <*> int root)) \object -> do
        object.type `shouldEqual` listOf xInt
        object.kind `shouldEqual` ExactKind XKType
      builds start (rootScope >>= emptyRow) \object -> object.kind `shouldEqual` AnyRow

    it "refuses an application the kinds do not admit" do
      refuses (rootScope >>= \root -> join (applyType root <$> int root <*> int root)) case _ of
        IllKinded _ -> pure unit
        other -> fail ("not ill-kinded: " <> show other)

  describe "forall" do
    it "opens a binder whose body closes into a forall of the scope it was opened in" do
      builds start forallList \object -> do
        object.type `shouldEqual` XForall t0 XKType (listOf (XVar t0))
        object.builtIn `shouldEqual` Just (ScopeId 0)

    it "names each binder afresh, whatever the hint" do
      let
        twice = do
          root <- rootScope
          first <- openForall root "t" KindType
          second <- openForall root "t" KindType
          one <- resolveType first.variable
          other <- resolveType second.variable
          pure (Tuple one.type other.type)
      case outcomeOf start twice of
        Done (Tuple one other) -> do
          one `shouldEqual` XVar t0
          other `shouldEqual` XVar (TyVar "t#1")
        other -> fail (show other)

    it "refuses a kind no variable can stand at" do
      refuses (rootScope >>= \root -> openForall root "t" KindAnyRow) (_ `shouldEqual` AnyRowAsKind)
      refuses (rootScope >>= \root -> openForall root "t" KindEffect) case _ of
        IllKinded (NotQuantifiable _) -> pure unit
        other -> fail ("not NotQuantifiable: " <> show other)

    it "refuses closing a binder anywhere but the scope it was opened in" do
      let
        misplaced = do
          root <- rootScope
          opened <- openForall root "t" KindType
          closeForall opened.bodyScope opened.binder opened.variable
      refuses misplaced case _ of
        BinderMisuse _ -> pure unit
        other -> fail ("not a binder misuse: " <> show other)

  describe "scopes" do
    it "lets a child use what its ancestors built" do
      let
        grandchild = do
          root <- rootScope
          l <- list root
          outer <- openForall root "t" KindType
          inner <- openForall outer.bodyScope "u" KindType
          applyType inner.bodyScope l outer.variable
      builds start grandchild \object -> do
        object.type `shouldEqual` listOf (XVar t0)
        object.builtIn `shouldEqual` Just (ScopeId 2)

    it "refuses in an ancestor what a child built" do
      let
        escaping = do
          root <- rootScope
          opened <- openForall root "t" KindType
          l <- list root
          applyType root l opened.variable
      refuses escaping scopeViolation

    it "refuses in one sibling what the other built, however alike their binders are" do
      let
        across = do
          root <- rootScope
          left <- openForall root "t" KindType
          right <- openForall root "t" KindType
          l <- list right.bodyScope
          applyType right.bodyScope l left.variable
        closedOver = do
          root <- rootScope
          left <- openForall root "t" KindType
          right <- openForall root "t" KindType
          closeForall root right.binder left.variable
      refuses across scopeViolation
      refuses closedOver scopeViolation

  describe "observed types" do
    it "are the root's where the site gives them" do
      let
        fromSite = do
          root <- rootScope
          entries <- localContext
          case entries of
            [ entry ] -> list root >>= \l -> applyType root l entry.type
            _ -> raiseDiagnostic failure
      builds start fromSite \object -> object.type `shouldEqual` listOf (listOf (XVar a))

    it "leave a catalog scheme, and every part a view takes of it, in no scope" do
      let
        whole = do
          root <- rootScope
          s <- scheme "ints"
          l <- list root
          applyType root l s
        part = do
          root <- rootScope
          s <- scheme "ints"
          viewType s >>= case _ of
            AppType _ argument -> list root >>= \l -> applyType root l argument
            _ -> raiseDiagnostic failure
        payload = do
          root <- rootScope
          s <- scheme "record"
          viewType s >>= case _ of
            AppType _ row -> normalizeRow row >>= \view -> case view.known of
              [ { payload: TypePayload ty } ] -> list root >>= \l -> applyType root l ty
              _ -> raiseDiagnostic failure
            _ -> raiseDiagnostic failure
      refuses whole scopeViolation
      refuses part scopeViolation
      refuses payload scopeViolation

    it "leave the body of a forall or of a constraint in no scope" do
      let
        forallBody = do
          root <- rootScope
          whole <- observed (XForall (TyVar "b") XKType (XVar (TyVar "b"))) (ExactKind XKType)
          viewType whole >>= case _ of
            ForallType _ _ body -> list root >>= \l -> applyType root l body
            _ -> raiseDiagnostic failure
        constrainedBody = do
          root <- rootScope
          whole <- observed (XConstrained (XLacks keyN (XVar r)) xInt) (ExactKind XKType)
          viewType whole >>= case _ of
            ConstrainedType (LacksView _ _) body -> list root >>= \l -> applyType root l body
            _ -> raiseDiagnostic failure
      refuses forallBody scopeViolation
      refuses constrainedBody scopeViolation

  describe "instantiateForall" do
    it "substitutes the argument for the binder" do
      let
        applied = do
          root <- rootScope
          whole <- forallList
          int root >>= instantiateForall root whole
      builds start applied \object -> do
        object.type `shouldEqual` listOf xInt
        object.builtIn `shouldEqual` Just (ScopeId 0)

    it "opens the body of an observed forall into the scope" do
      let
        applied = do
          root <- rootScope
          whole <- observed (XForall (TyVar "b") XKType (listOf (XVar (TyVar "b")))) (ExactKind XKType)
          l <- list root
          body <- int root >>= instantiateForall root whole
          applyType root l body
      builds start applied \object -> object.type `shouldEqual` listOf (listOf xInt)

    it "renames a binder of the body that would capture the argument" do
      let
        applied = do
          root <- rootScope
          whole <- observed (XForall (TyVar "b") XKType (XForall a XKType (XVar (TyVar "b")))) (ExactKind XKType)
          typeVariable root a >>= instantiateForall root whole
      builds start applied \object ->
        object.type `shouldEqual` XForall (TyVar "a#0") XKType (XVar a)

    it "refuses an argument at another kind, and a type that is no forall" do
      refuses (forallList >>= \whole -> rootScope >>= \root -> emptyRow root >>= instantiateForall root whole) case _ of
        IllKinded _ -> pure unit
        other -> fail ("not ill-kinded: " <> show other)
      refuses (rootScope >>= \root -> int root >>= \i -> instantiateForall root i i) case _ of
        NotAForall _ -> pure unit
        other -> fail ("not NotAForall: " <> show other)

    it "waits on a metavariable of the body that may mention the binder" do
      let
        b = TyVar "b"
        Tuple mentioning metas1 = freshMeta { kind: XKType, scope: { types: Set.fromFoldable [ a, b ], kinds: Set.empty } } emptyContext
        Tuple outside metas2 = freshMeta { kind: XKType, scope: { types: Set.singleton a, kinds: Set.empty } } metas1
        s = start { tentative = start.tentative { metas = metas2 } }
        applyTo m = do
          root <- rootScope
          whole <- observed (XForall b XKType (listOf (XMeta m))) (ExactKind XKType)
          int root >>= instantiateForall root whole
      case outcomeOf s (applyTo mentioning) of
        Postponed (ExplicitPostponement ms) -> ms `shouldEqual` Set.singleton mentioning
        other -> fail ("expected a postponement: " <> show other)
      builds s (applyTo outside) \object -> object.type `shouldEqual` listOf (XMeta outside)

    it "renames a binder that a solved metavariable of the argument names, the argument being zonked first" do
      let
        Tuple m metas1 = freshMeta { kind: XKType, scope: { types: Set.singleton a, kinds: Set.empty } } emptyContext
        s = start { tentative = start.tentative { metas = metas1 { bindings = Map.insert m (Assigned (XVar a)) metas1.bindings } } }
        applied = do
          root <- rootScope
          whole <- observed (XForall (TyVar "x") XKType (XForall a XKType (XVar (TyVar "x")))) (ExactKind XKType)
          argument <- observed (XMeta m) (ExactKind XKType)
          instantiateForall root whole argument
      builds s applied \object ->
        object.type `shouldEqual` XForall (TyVar "a#0") XKType (XVar a)

    it "waits on an unsolved metavariable of the argument that may mention a binder of the body" do
      let
        Tuple mentioning metas1 = freshMeta { kind: XKType, scope: { types: Set.singleton a, kinds: Set.empty } } emptyContext
        Tuple outside metas2 = freshMeta { kind: XKType, scope: { types: Set.empty, kinds: Set.empty } } metas1
        s = start { tentative = start.tentative { metas = metas2 } }
        applyTo m = do
          root <- rootScope
          whole <- observed (XForall (TyVar "x") XKType (XForall a XKType (XVar (TyVar "x")))) (ExactKind XKType)
          observed (XMeta m) (ExactKind XKType) >>= instantiateForall root whole
      case outcomeOf s (applyTo mentioning) of
        Postponed (ExplicitPostponement ms) -> ms `shouldEqual` Set.singleton mentioning
        other -> fail ("expected a postponement: " <> show other)
      builds s (applyTo outside) \object -> object.type `shouldEqual` XForall a XKType (XMeta outside)

  describe "instantiateScheme" do
    it "judges the scheme under what it declares, whatever the caller's scope binds" do
      case outcomeOf start (rootScope >>= \root -> instantiateScheme root (global "freeType") []) of
        Broke (KindingFailed (UnboundTyVar v)) -> v `shouldEqual` a
        other -> fail ("expected an unbound type variable: " <> show other)
      case outcomeOf start (rootScope >>= \root -> instantiateScheme root (global "freeKind") []) of
        Broke (KindingFailed (UnboundKindVar v)) -> v `shouldEqual` j
        other -> fail ("expected an unbound kind variable: " <> show other)

    it "makes a scheme usable, at the kinds given" do
      let
        applied = do
          root <- rootScope
          l <- list root
          instantiateScheme root (global "ints") [] >>= applyType root l
      builds start applied \object -> object.type `shouldEqual` listOf (listOf xInt)
      builds start (rootScope >>= \root -> instantiateScheme root (global "poly") [ KindType ]) \object ->
        object.type `shouldEqual` XForall (TyVar "v") XKType xInt

    it "refuses a name the catalog lacks, a count it does not bind, and a kind it cannot take" do
      refuses (rootScope >>= \root -> instantiateScheme root (global "absent") []) (_ `shouldEqual` UnknownScheme (global "absent"))
      refuses (rootScope >>= \root -> instantiateScheme root (global "poly") []) (_ `shouldEqual` SchemeArity (global "poly") 1 0)
      refuses (rootScope >>= \root -> instantiateScheme root (global "poly") [ KindEffect ]) case _ of
        IllKinded (NotQuantifiable _) -> pure unit
        other -> fail ("not NotQuantifiable: " <> show other)
      refuses (rootScope >>= \root -> instantiateScheme root (global "poly") [ KindVar (Core.KindVar "q") ]) case _ of
        IllKinded (UnboundKindVar _) -> pure unit
        other -> fail ("not UnboundKindVar: " <> show other)

  describe "a rolled-back attempt" do
    it "gives back the names and scopes it drew" do
      let
        again = do
          root <- rootScope
          _ <- transact (openForall root "t" KindType *> raiseDiagnostic failure)
          opened <- openForall root "t" KindType
          resolveType opened.variable
      case outcomeOf start again of
        Done object -> do
          object.type `shouldEqual` XVar t0
          object.builtIn `shouldEqual` Just (ScopeId 1)
        other -> fail (show other)

  describe "extendRow" do
    it "builds an element over a row, at the row's kind" do
      builds start (rootScope >>= \root -> emptyRow root >>= withN root) \object -> do
        object.type `shouldEqual` XRowExtend (XRowTypeEntry keyN xInt) XRowEmpty
        object.kind `shouldEqual` ExactKind (XKRow RowType)

    it "makes an effect unlabelled under its own key, and labelled under a symbol" do
      let
        effect key = do
          root <- rootScope
          i <- int root
          emptyRow root >>= extendRow root key (EffectPayload state [ i ])
      builds start (effect (EffectKey state)) \object ->
        object.type `shouldEqual` XRowExtend (XRowEffectEntry state [ xInt ]) XRowEmpty
      builds start (effect (SymbolKey (Symbol "cache"))) \object ->
        object.type `shouldEqual` XRowExtend (XRowLabelledEffectEntry (Symbol "cache") state [ xInt ]) XRowEmpty

    it "refuses a payload its key does not admit, and any region" do
      let
        extended key payload = do
          root <- rootScope
          i <- int root
          e <- emptyRow root
          extendRow root key (payload i e) e
      refuses (extended (EffectKey state) \i _ -> TypePayload i) (_ `shouldEqual` EntryMismatch (EffectKey state))
      refuses (extended keyN \_ _ -> EffectPayload state []) case _ of
        IllKinded _ -> pure unit
        other -> fail ("not ill-kinded: " <> show other)
      refuses (extended (TagKey (Tag "Ok")) \i _ -> EffectPayload state [ i ]) (_ `shouldEqual` EntryMismatch (TagKey (Tag "Ok")))
      refuses (extended RegionKey RegionPayload) (_ `shouldEqual` RegionEntryForbidden)

    it "fails on a key the row already has" do
      rejectsObligation start (rootScope >>= \root -> emptyRow root >>= withN root >>= withN root) Required (SolutionCarriesKey keyN)

    it "fails on a rigid tail its scope does not prove lacks the key" do
      rejectsObligation start (rootScope >>= \root -> typeVariable root r >>= withN root) Required (LacksUnprovenAtSite keyN r)

    it "holds the requirement over a flexible tail, which an assignment must then keep" do
      let
        solving = do
          root <- rootScope
          _ <- tailType >>= withN root
          unify site solvedWithN
      case outcomeOf withTail solving of
        Failed (ObligationBroken broken) -> do
          broken.basis `shouldEqual` Required
          broken.breach `shouldEqual` SolutionCarriesKey keyN
        other -> fail ("expected the obligation to break: " <> show other)

    it "leaves no obligation behind where it fails" do
      let
        Tuple outcome s = runElabIn session withTail
          ( withFrame frame do
              root <- rootScope
              row <- tailType >>= withN root
              transact (withN root row)
          )
      case outcome of
        Done (Left _) -> Map.size s.tentative.obligations.entries `shouldEqual` 1
        other -> fail ("expected a caught failure: " <> show other)

  describe "unionRow" do
    it "joins rows that share no key" do
      let
        joined = do
          root <- rootScope
          e <- emptyRow root
          n <- withN root e
          m <- int root >>= \i -> extendRow root keyM (TypePayload i) e
          unionRow root n m
      builds start joined \object -> object.kind `shouldEqual` ExactKind (XKRow RowType)

    it "fails where the sides share a key, or a key is not proved absent from a rigid tail" do
      let
        shared = do
          root <- rootScope
          e <- emptyRow root
          n <- withN root e
          n' <- withN root e
          unionRow root n n'
        overRigid = do
          root <- rootScope
          n <- emptyRow root >>= withN root
          typeVariable root r >>= unionRow root n
      rejectsObligation start shared Required (SidesShareKey keyN)
      rejectsObligation start overRigid Required (LacksUnprovenAtSite keyN r)

  describe "constraints" do
    it "are assumed in their body, which reaches the root only once closed" do
      let
        underLacks = do
          root <- rootScope
          rv <- typeVariable root r
          opened <- openConstraint root (LacksView keyN rv)
          row <- withN opened.bodyScope rv
          pure { root, opened, row }
        closed = do
          c <- underLacks
          record <- typeConstructor c.opened.bodyScope (tyName "Record") []
          body <- applyType c.opened.bodyScope record c.row
          closeConstraint c.root c.opened.assumption body
        escaping = do
          c <- underLacks
          record <- typeConstructor c.root (tyName "Record") []
          applyType c.root record c.row
      builds start closed \object -> do
        object.type `shouldEqual` XConstrained (XLacks keyN (XVar r)) (recordOf (XRowExtend (XRowTypeEntry keyN xInt) (XVar r)))
        object.builtIn `shouldEqual` Just (ScopeId 0)
      refuses escaping scopeViolation

    it "hold their assumption from where they are closed, and not before" do
      let
        opening = do
          root <- rootScope
          tv <- tailType
          opened <- openConstraint root (LacksView keyN tv)
          pure { root, opened }
        openOnly = opening *> unify site solvedWithN
        closed = do
          c <- opening
          i <- int c.opened.bodyScope
          _ <- closeConstraint c.root c.opened.assumption i
          unify site solvedWithN
      case outcomeOf withTail openOnly of
        Done _ -> pure unit
        other -> fail ("expected the assignment to pass: " <> show other)
      case outcomeOf withTail closed of
        Failed (ObligationBroken broken) -> broken.basis `shouldEqual` Assumed
        other -> fail ("expected the assumption to refuse it: " <> show other)

    it "fail where one that cannot hold is closed" do
      let
        contradiction = do
          root <- rootScope
          n <- emptyRow root >>= withN root
          opened <- openConstraint root (LacksView keyN n)
          int root >>= closeConstraint root opened.assumption
      rejectsObligation start contradiction Assumed (SolutionCarriesKey keyN)

    it "refuse one that is not well-formed, or taken from where no build scope reaches" do
      let
        illFormed = do
          root <- rootScope
          n <- emptyRow root >>= withN root
          openConstraint root (LacksView (EffectKey state) n)
        underBinder = do
          root <- rootScope
          let
            q = TyVar "q"
          whole <- observed (XForall q (XKRow RowType) (XConstrained (XLacks keyN (XVar q)) xInt)) (ExactKind XKType)
          viewType whole >>= case _ of
            ForallType _ _ body -> viewType body >>= case _ of
              ConstrainedType c _ -> openConstraint root c
              _ -> raiseDiagnostic failure
            _ -> raiseDiagnostic failure
      refuses illFormed case _ of
        IllKinded (KeyNotOfRowKind _ _) -> pure unit
        other -> fail ("not KeyNotOfRowKind: " <> show other)
      refuses underBinder scopeViolation

  describe "binders" do
    it "refuse being closed by the operation for the other sort" do
      let
        forallAsConstraint = do
          root <- rootScope
          opened <- openForall root "t" KindType
          int root >>= closeConstraint root opened.binder
        constraintAsForall = do
          root <- rootScope
          opened <- typeVariable root r >>= \rv -> openConstraint root (LacksView keyN rv)
          int root >>= closeForall root opened.assumption
        misuse = case _ of
          BinderMisuse _ -> pure unit
          other -> fail ("not a binder misuse: " <> show other)
      refuses forallAsConstraint misuse
      refuses constraintAsForall misuse

    it "refuse being closed twice" do
      let
        twice = do
          root <- rootScope
          opened <- openForall root "t" KindType
          _ <- closeForall root opened.binder opened.variable
          closeForall root opened.binder opened.variable
      refuses twice case _ of
        BinderClosed _ -> pure unit
        other -> fail ("not BinderClosed: " <> show other)

  describe "an attempt the runner ends in success" do
    it "halts with a binder still open, of either sort" do
      attemptWith (\_ -> void (rootScope >>= \root -> openForall root "t" KindType))
        `shouldEqual` Halted (BindersLeftOpen (Set.singleton (ScopeId 1)))
      attemptWith (\_ -> void (rootScope >>= \root -> typeVariable root r >>= \rv -> openConstraint root (LacksView keyN rv)))
        `shouldEqual` Halted (BindersLeftOpen (Set.singleton (ScopeId 1)))

    it "commits once every binder is closed, a discarded candidate's included" do
      attemptWith (\_ -> void forallList) `shouldEqual` Committed
      attemptWith (\_ -> void (rootScope >>= \root -> transact (openForall root "t" KindType *> raiseDiagnostic failure)))
        `shouldEqual` Committed

    it "commits nested binders closed inside out, and siblings closed in either order" do
      let
        insideOut = do
          c <- nested openLacks openLacks
          _ <- int c.inner.bodyScope >>= c.inner.close c.outer.bodyScope
          void (int c.outer.bodyScope >>= c.outer.close c.root)
        siblings = do
          root <- rootScope
          left <- openLacks root
          right <- openLacks root
          _ <- int root >>= left.close root
          void (int root >>= right.close root)
      attemptWith (\_ -> insideOut) `shouldEqual` Committed
      attemptWith (\_ -> siblings) `shouldEqual` Committed

    it "is held to it by runAttempt itself, whoever runs the attempt" do
      case fst (runAttempt session (withFrame frame (rootScope >>= \root -> openForall root "t" KindType)) start) of
        Broke (BindersLeftOpen open) -> open `shouldEqual` Set.singleton (ScopeId 1)
        other -> fail ("expected the attempt to halt: " <> show other)

  describe "a binder enclosing one still open" do
    it "refuses to close, for either sort around either sort" do
      let
        -- Close the outer binder over a body from its own scope, the inner one
        -- still open; then close the inner one, which would empty the ledger.
        outerFirst outer inner = do
          c <- nested outer inner
          _ <- int c.root >>= c.outer.close c.root
          int c.inner.bodyScope >>= c.inner.close c.outer.bodyScope
        enclosing = case _ of
          EnclosesOpenBinder _ -> pure unit
          other -> fail ("not EnclosesOpenBinder: " <> show other)
      refuses (outerFirst openLacks openLacks) enclosing
      refuses (outerFirst openT openLacks) enclosing
      refuses (outerFirst openLacks openT) enclosing
      refuses (outerFirst openT openT) enclosing

    it "halts the attempt rather than commit what was built under the inner one" do
      let
        outerFirst = do
          c <- nested openLacks openLacks
          _ <- int c.root >>= c.outer.close c.root
          void (int c.inner.bodyScope >>= c.inner.close c.outer.bodyScope)
      case attemptWith (\_ -> outerFirst) of
        Halted (BuildRejected (EnclosesOpenBinder _)) -> pure unit
        other -> fail ("expected the attempt to halt: " <> show other)

  describe "a row view's flexible tail" do
    it "is also a type, built where the row was and at its kind" do
      let
        rebuilt = do
          root <- rootScope
          row <- observed (XRowExtend (XRowTypeEntry keyN xInt) (XMeta tail)) (ExactKind (XKRow RowType))
          view <- normalizeRow row
          case view.flexible of
            [ flexible ] -> do
              object <- resolveType flexible.type
              extended <- int root >>= \i -> extendRow root keyM (TypePayload i) flexible.type
              pure (Tuple object extended)
            _ -> raiseDiagnostic failure
      case outcomeOf withTail rebuilt of
        Done (Tuple object _) -> do
          object.type `shouldEqual` XMeta tail
          object.kind `shouldEqual` ExactKind (XKRow RowType)
          object.builtIn `shouldEqual` Just (ScopeId 0)
        other -> fail (show other)

    it "is in no build scope where the row is in none" do
      let
        underBinder = do
          root <- rootScope
          whole <- observed (XForall (TyVar "q") XKType (recordOf (XRowExtend (XRowTypeEntry keyN xInt) (XMeta tail)))) (ExactKind XKType)
          viewType whole >>= case _ of
            ForallType _ _ body -> viewType body >>= case _ of
              AppType _ row -> normalizeRow row >>= \view -> case view.flexible of
                [ flexible ] -> int root >>= \i -> extendRow root keyM (TypePayload i) flexible.type
                _ -> raiseDiagnostic failure
              _ -> raiseDiagnostic failure
            _ -> raiseDiagnostic failure
      refusesIn withTail underBinder scopeViolation

keyM :: RowKey
keyM = SymbolKey (Symbol "m")

-- | `( n : Int | rest )`, built in the scope.
withN :: Handle -> Handle -> Elab Handle
withN scope rest = int scope >>= \i -> extendRow scope keyN (TypePayload i) rest

-- | A flexible row tail `?t : Row Type`, created under the site's variables.
tailed :: Tuple MetaVar MetaContext
tailed = freshMeta { kind: XKRow RowType, scope: { types: Set.fromFoldable [ a, r ], kinds: Set.empty } } emptyContext

tail :: MetaVar
tail = fst tailed

withTail :: SolverState
withTail = start { tentative = start.tentative { metas = snd tailed } }

-- | `?t`, as the site gives it.
tailType :: Elab Handle
tailType = observed (XMeta tail) (ExactKind (XKRow RowType))

-- | `?t ≡ ( n : Int )`.
solvedWithN :: EqualityGoal
solvedWithN = { kind: XKRow RowType, left: XMeta tail, right: XRowExtend (XRowTypeEntry keyN xInt) XRowEmpty }

-- | What an action fails with, where an obligation it introduced is rejected.
rejectsObligation :: forall a. Show a => SolverState -> Elab a -> Basis -> Breach -> Aff Unit
rejectsObligation s action basis breach = case outcomeOf s action of
  Failed (ObligationRejected rejected) -> do
    rejected.basis `shouldEqual` basis
    rejected.breach `shouldEqual` breach
  other -> fail ("expected a rejected obligation: " <> show other)

-- | What attempting an equality job with the runner given comes to.
attemptWith :: (Pending -> Elab Unit) -> Attempt
attemptWith runner = fst (attemptPendingWith session runner id held)
  where
  Tuple id scheduler = create site (JobUnify { kind: XKType, left: xInt, right: xInt }) emptyScheduler
  held = start { tentative = start.tentative { scheduler = scheduler } }

-- | A binder opened in a scope: the scope its body is built in, and how to close
-- | it in a scope over a body.
type Opened = { bodyScope :: Handle, close :: Handle -> Handle -> Elab Handle }

-- | `forall (t : Type)`.
openT :: Handle -> Elab Opened
openT scope = do
  opened <- openForall scope "t" KindType
  pure { bodyScope: opened.bodyScope, close: \s body -> closeForall s opened.binder body }

-- | `n ∉ r =>`.
openLacks :: Handle -> Elab Opened
openLacks scope = do
  rv <- typeVariable scope r
  opened <- openConstraint scope (LacksView keyN rv)
  pure { bodyScope: opened.bodyScope, close: \s body -> closeConstraint s opened.assumption body }

-- | One binder opened in the root, and another inside its body.
nested :: (Handle -> Elab Opened) -> (Handle -> Elab Opened) -> Elab { root :: Handle, outer :: Opened, inner :: Opened }
nested openOuter openInner = do
  root <- rootScope
  outer <- openOuter root
  inner <- openInner outer.bodyScope
  pure { root, outer, inner }
