-- | Term metavariables: their scope, their assignment, and zonking a term.
-- |
-- | Two things are what these cases are for. **A solution may mention only what
-- | was in scope where its metavariable was created**, and narrowing is what
-- | keeps that true through a chain of metavariables, where each link is in
-- | scope on its own. And **a zonked solution stands where the metavariable
-- | stood**, every node of it taking that place's annotation.
module Test.Stella.Compiler.Elaborate.TermMeta (spec) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.Context (Origin(..), XContext, bindKindVars, bindTyVar, bindVar, emptyXContext)
import Stella.Compiler.Elaborate.Diagnostic (Defect(..), Diagnostic(..))
import Stella.Compiler.Elaborate.Handle (SessionId(..))
import Stella.Compiler.Elaborate.Elab (Elab, Outcome(..), assignTerm, freshTermMeta, initialState, runElab, throw, transact)
import Stella.Compiler.Elaborate.Kind (XKind(..))
import Stella.Compiler.Elaborate.Pending (Site)
import Stella.Compiler.Elaborate.Term (Residue(..), TermMetaVar(..), XExpr(..), toCoreExpr)
import Stella.Compiler.Elaborate.TermMeta (TermError(..), assignTermMeta, termScopeOf, zonkExpr)
import Stella.Compiler.Elaborate.TermMeta as TermMeta
import Stella.Compiler.Elaborate.Type (XType(..))
import Stella.Compiler.Elaborate.Unify (MetaBinding(..), MetaContext, TermBinding(..), TermScope, emptyContext, freshMeta, lookupMeta, lookupTermMeta)
import Stella.Compiler.TypedCore (Ident(..), JoinName(..), KindVar(..), ModuleName(..), Qualified(..), TyName(..), TyVar(..))
import Data.Array.NonEmpty as NonEmptyArray
import Data.Either (Either(..))
import Data.Foldable (foldl)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Data.Tuple (Tuple(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

prim :: ModuleName
prim = ModuleName "Prim"

xInt :: XType
xInt = XCon (Qualified prim (TyName "Int")) []

x :: Ident
x = Ident "x"

y :: Ident
y = Ident "y"

a :: TyVar
a = TyVar "a"

k :: KindVar
k = KindVar "k"

here :: Origin
here = InDeclaration (Qualified prim (Ident "decl"))

site :: Site
site = { context: emptyXContext, origin: here }

-- | Everything in scope: `x`, `y`, `a`, and `k`.
wide :: TermScope
wide =
  { values: Set.fromFoldable [ x, y ]
  , types: Set.singleton a
  , kinds: Set.singleton k
  , region: Nothing
  }

-- | The context `wide` is the scope of.
wideContext :: XContext
wideContext = bindKindVars (bindTyVar (bindVar (bindVar emptyXContext x xInt) y xInt) a XKType) [ k ]

-- | Nothing in scope.
narrow :: TermScope
narrow = { values: Set.empty, types: Set.empty, kinds: Set.empty, region: Nothing }

-- | `Ψ` holding the term metavariables given, in order, each at `Int`.
holding :: P.Array TermScope -> Tuple (P.Array TermMetaVar) MetaContext
holding = foldl step (Tuple [] emptyContext)
  where
  step (Tuple acc ctx) scope =
    let
      Tuple m ctx' = TermMeta.freshTermMeta { ty: xInt, scope } ctx
    in
      Tuple (acc <> [ m ]) ctx'

single :: TermScope -> Tuple TermMetaVar MetaContext
single scope = TermMeta.freshTermMeta { ty: xInt, scope } emptyContext

solved :: MetaContext -> TermMetaVar -> P.Boolean
solved ctx m = case lookupTermMeta ctx m of
  Just (TermAssigned _) -> true
  _ -> false

spec :: Spec Unit
spec = describe "Elaborate.TermMeta" do
  describe "a scope" do
    it "is what a context binds, in each class" do
      termScopeOf wideContext Nothing `shouldEqual` wide

  describe "an assignment" do
    it "admits a solution naming what is in scope" do
      let
        Tuple m ctx = single wide
      map (\c -> solved c m) (assignTermMeta ctx m (EApp 1 (EVar 2 x) (EVar 3 y))) `shouldEqual` Right true

    it "admits a join point the solution binds itself" do
      let
        Tuple m ctx = single wide
        j = JoinName "j"
        solution = ELetJoin 1 j [] xInt (EVar 2 x) (EJump 3 j [])
      map (\c -> solved c m) (assignTermMeta ctx m solution) `shouldEqual` Right true

    it "refuses a value, a type, and a kind out of scope" do
      let
        Tuple m ctx = single narrow
      assignTermMeta ctx m (EVar 1 x) `shouldEqual` Left (TermEscapingValue m x)
      assignTermMeta ctx m (ELam 1 y (XVar a) (EVar 2 y)) `shouldEqual` Left (TermEscapingType m a)
      assignTermMeta ctx m (ELam 1 y (XCon (Qualified prim (TyName "P")) [ XKVar k ]) (EVar 2 y))
        `shouldEqual` Left (TermEscapingKind m k)

    it "refuses a jump to a join point of the place it stands in" do
      let
        Tuple m ctx = single wide
        j = JoinName "j"
      assignTermMeta ctx m (EJump 1 j []) `shouldEqual` Left (TermCapturesJoin m j)

    it "refuses a solution containing the metavariable" do
      let
        Tuple m ctx = single wide
      assignTermMeta ctx m (EApp 1 (EVar 2 x) (ETermMeta 3 m)) `shouldEqual` Left (TermOccursCheck m)

    it "refuses one containing it through another metavariable's solution" do
      let
        Tuple ms ctx0 = holding [ wide, wide ]
      case ms of
        [ p, q ] -> do
          let
            step = assignTermMeta ctx0 p (ETermMeta 1 q)
          case step of
            Left err -> fail ("the first assignment was refused: " <> show err)
            Right ctx1 -> assignTermMeta ctx1 q (EApp 2 (EVar 3 x) (ETermMeta 4 p)) `shouldEqual` Left (TermOccursCheck q)
        _ -> ms `shouldEqual` []

    it "refuses a metavariable Ψ does not hold, and one solved already" do
      let
        Tuple m ctx = single wide
        absent = TermMetaVar 9
      assignTermMeta ctx absent (EVar 1 x) `shouldEqual` Left (TermMetaUnbound absent)
      case assignTermMeta ctx m (EVar 1 x) of
        Left err -> fail ("the first assignment was refused: " <> show err)
        Right ctx1 -> assignTermMeta ctx1 m (EVar 2 y) `shouldEqual` Left (TermMetaAlreadyAssigned m)

  describe "narrowing" do
    it "stops an escape through a chain of metavariables" do
      -- `?outer` stands where nothing is in scope and `?inner` where `x` is. Each
      -- assignment is in scope on its own, and the pair would put `x` where
      -- `?outer` stood.
      let
        Tuple ms ctx0 = holding [ narrow, wide ]
      case ms of
        [ outer, inner ] -> case assignTermMeta ctx0 outer (ETermMeta 1 inner) of
          Left err -> fail ("the first assignment was refused: " <> show err)
          Right ctx1 -> assignTermMeta ctx1 inner (EVar 2 x) `shouldEqual` Left (TermEscapingValue inner x)
        _ -> ms `shouldEqual` []

    it "refuses a metavariable whose own type the narrower scope excludes" do
      let
        Tuple outer ctx0 = TermMeta.freshTermMeta { ty: xInt, scope: narrow } emptyContext
        Tuple inner ctx1 = TermMeta.freshTermMeta { ty: XVar a, scope: wide } ctx0
      assignTermMeta ctx1 outer (ETermMeta 1 inner) `shouldEqual` Left (TermEscapingType inner a)

    it "narrows a type metavariable in the solution to the scope of the one assigned" do
      let
        Tuple tm ctx0 = freshMeta { kind: XKType, scope: { types: Set.singleton a, kinds: Set.empty } } emptyContext
        Tuple m ctx1 = TermMeta.freshTermMeta { ty: xInt, scope: narrow } ctx0
        narrowed = case assignTermMeta ctx1 m (ELam 1 y (XMeta tm) (EVar 2 y)) of
          Right ctx2 -> lookupMeta ctx2 tm
          Left _ -> Nothing
      narrowed `shouldEqual` Just (Unsolved { kind: XKType, scope: { types: Set.empty, kinds: Set.empty } })

  describe "zonking" do
    it "puts a solution where the metavariable stood, under its annotation" do
      let
        Tuple m ctx0 = single wide
        zonked = case assignTermMeta ctx0 m (EApp 90 (EVar 91 x) (EVar 92 y)) of
          Right ctx1 -> Just (zonkExpr ctx1 (ELam 1 x xInt (ETermMeta 7 m)))
          Left _ -> Nothing
      zonked `shouldEqual` Just (ELam 1 x xInt (EApp 7 (EVar 7 x) (EVar 7 y)))

    it "follows a chain of solutions" do
      let
        Tuple ms ctx0 = holding [ wide, wide ]
        zonked = case ms of
          [ p, q ] -> do
            ctx1 <- hush (assignTermMeta ctx0 p (ETermMeta 1 q))
            ctx2 <- hush (assignTermMeta ctx1 q (EVar 2 x))
            pure (zonkExpr ctx2 (ETermMeta 5 p))
          _ -> Nothing
      zonked `shouldEqual` Just (EVar 5 x)

    it "applies solved type metavariables inside a term metavariable's solution" do
      let
        Tuple tm ctx0 = freshMeta { kind: XKType, scope: { types: Set.empty, kinds: Set.empty } } emptyContext
        Tuple m ctx1 = TermMeta.freshTermMeta { ty: xInt, scope: wide } ctx0
        solvedType = ctx1 { bindings = Map.insert tm (Assigned xInt) ctx1.bindings }
        zonked = map (\c -> zonkExpr c (ETermMeta 4 m)) (hush (assignTermMeta solvedType m (ELam 1 y (XMeta tm) (EVar 2 y))))
      zonked `shouldEqual` Just (ELam 4 y xInt (EVar 4 y))

    it "leaves an unsolved metavariable for the boundary to report" do
      let
        Tuple m ctx = single wide
      toCoreExpr (zonkExpr ctx (ETermMeta 3 m)) `shouldEqual` Left (NonEmptyArray.singleton (ResidualTermMeta 3 m))

  describe "through Elab" do
    it "creates a metavariable whose scope is what the context binds" do
      let
        Tuple outcome s = runElab (initialState (SessionId 0) 0) (freshTermMeta wideContext Nothing xInt)
      outcome `shouldEqual` Done (TermMetaVar 0)
      lookupTermMeta s.tentative.metas (TermMetaVar 0) `shouldEqual` Just (TermUnsolved { ty: xInt, scope: wide })

    it "reports an escaping solution as a failure at the site" do
      let
        Tuple outcome _ = runElab (initialState (SessionId 0) 0) do
          m <- freshTermMeta emptyXContext Nothing xInt
          assignTerm site m (EVar 1 x)
      outcome `shouldEqual` Failed (TermAssignmentFailed here (TermEscapingValue (TermMetaVar 0) x))

    it "reports a metavariable Ψ does not hold as a defect" do
      let
        Tuple outcome _ = runElab (initialState (SessionId 0) 0) (assignTerm site (TermMetaVar 5) (EVar 1 x))
      outcome `shouldEqual` Broke (TermMisuse here (TermMetaUnbound (TermMetaVar 5)))

    it "rolls back a metavariable, its solution, and the name it took" do
      let
        attempt :: Elab Unit
        attempt = do
          m <- freshTermMeta wideContext Nothing xInt
          assignTerm site m (EVar 1 x)
          throw (TermAssignmentFailed here (TermMetaUnbound m))

        Tuple outcome s = runElab (initialState (SessionId 0) 0) (transact attempt)
      outcome `shouldEqual` Done (Left (TermAssignmentFailed here (TermMetaUnbound (TermMetaVar 0))))
      s.tentative.metas.nextTerm `shouldEqual` 0
      Map.size s.tentative.metas.termBindings `shouldEqual` 0
  where
  hush :: forall e b. Either e b -> Maybe b
  hush = case _ of
    Left _ -> Nothing
    Right b -> Just b
