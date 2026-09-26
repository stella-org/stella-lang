-- | Row unification.
-- |
-- | The three cases the Implementation Plan singles out are here: refinement of
-- | two flexible tails through a fresh one, the rigid/flexible asymmetry, and a
-- | constraint with two flexible tails on one side, which waits rather than
-- | fails.
module Test.Stella.Compiler.Elaborate.Unify (spec) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.Kind (KindMetaVar(..), XKind(..))
import Stella.Compiler.Elaborate.Row (xnf)
import Stella.Compiler.Elaborate.Type (MetaVar(..), Scope, XConstraint(..), XRowEntry(..), XType(..), emptyScope)
import Stella.Compiler.Elaborate.Unify (KindMetaBinding(..), KindMetaInfo, KindRequirement(..), MetaBinding(..), MetaContext, MetaInfo, UnifyEnv, UnifyError(..), UnifyResult(..), emptyContext, freshKindMeta, freshMeta, lookupKindMeta, lookupMeta, requireProducesType, requireQuantifiable, substitute, substituteKind, unifyKind, unifyRow, unifyType)
import Stella.Compiler.TypedCore (EffName(..), KindVar(..), ModuleName(..), Qualified(..), RowElemKind(..), RowKey(..), Symbol(..), TyName(..), TyVar(..))
import Data.Array as Array
import Data.Either (Either(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Set as Set
import Data.Tuple (Tuple(..), fst, snd)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

prim :: ModuleName
prim = ModuleName "Prim"

tA :: XType
tA = XCon (Qualified prim (TyName "A")) []

tB :: XType
tB = XCon (Qualified prim (TyName "B")) []

a :: Symbol
a = Symbol "a"

b :: Symbol
b = Symbol "b"

cache :: Symbol
cache = Symbol "cache"

stateEff :: Qualified EffName
stateEff = Qualified prim (EffName "State")

readerEff :: Qualified EffName
readerEff = Qualified prim (EffName "Reader")

rigidR :: TyVar
rigidR = TyVar "r"

-- | `( l : τ | ρ )`
field :: Symbol -> XType -> XType -> XType
field l ty rest = XRowExtend (XRowTypeEntry (SymbolKey l) ty) rest

-- | `( region r ι | ρ )`
regionOf :: XType -> XType -> XType -> XType
regionOf var cells rest = XRowExtend (XRowRegionEntry var cells) rest

-- | `( s : E τ̄ | ρ )`
labelledEffect :: Symbol -> Qualified EffName -> P.Array XType -> XType -> XType
labelledEffect s eff args rest = XRowExtend (XRowLabelledEffectEntry s eff args) rest

-- | A metavariable created where `r` is in scope, which is what the escape
-- | check compares a solution against.
rowTypeInfo :: MetaInfo
rowTypeInfo =
  { kind: XKRow RowType
  , scope: { types: Set.singleton rigidR, kinds: Set.empty }
  }

effectRowInfo :: MetaInfo
effectRowInfo = rowTypeInfo { kind = XKRow RowEffect }

-- | Two fresh metavariables over an empty context.
twoMetas :: MetaInfo -> MetaInfo -> { r :: MetaVar, s :: MetaVar, ctx :: MetaContext }
twoMetas infoR infoS =
  let
    first = freshMeta infoR emptyContext
    second = freshMeta infoS (snd first)
  in
    { r: fst first, s: fst second, ctx: snd second }

solutionOf :: MetaContext -> MetaVar -> Maybe XType
solutionOf ctx m = case lookupMeta ctx m of
  Just (Assigned ty) -> Just (substitute ctx ty)
  _ -> Nothing

-- | The known keys of a solved row, which is what the refinement cases assert.
knownKeysOf :: MetaContext -> MetaVar -> Maybe (P.Array RowKey)
knownKeysOf ctx m = case solutionOf ctx m of
  Nothing -> Nothing
  Just ty -> case xnf ty of
    Left _ -> Nothing
    Right n -> Just (Set.toUnfoldable (Set.fromFoldable (Map.keys n.known)))

-- | The flexible tail of a solved row.
tailOf :: MetaContext -> MetaVar -> Maybe (P.Array MetaVar)
tailOf ctx m = case solutionOf ctx m of
  Nothing -> Nothing
  Just ty -> case xnf ty of
    Left _ -> Nothing
    Right n -> Just (Set.toUnfoldable n.flexible)

-- | A kind metavariable created where no kind variable is in scope.
closedKindInfo :: KindMetaInfo
closedKindInfo = { scope: Set.empty, requirements: Set.empty }

-- | A kind metavariable created under one kind variable.
kindInfoUnder :: KindVar -> KindMetaInfo
kindInfoUnder k = closedKindInfo { scope = Set.singleton k }

-- | Two fresh kind metavariables over an empty context.
twoKindMetas :: KindMetaInfo -> KindMetaInfo -> { j :: KindMetaVar, k :: KindMetaVar, ctx :: MetaContext }
twoKindMetas infoJ infoK =
  let
    first = freshKindMeta infoJ emptyContext
    second = freshKindMeta infoK (snd first)
  in
    { j: fst first, k: fst second, ctx: snd second }

kindSolutionOf :: MetaContext -> KindMetaVar -> Maybe XKind
kindSolutionOf ctx m = case lookupKindMeta ctx m of
  Just (KindAssigned kind) -> Just (substituteKind ctx kind)
  _ -> Nothing

scopeOfMeta :: MetaContext -> MetaVar -> Maybe Scope
scopeOfMeta ctx m = case lookupMeta ctx m of
  Just (Unsolved info) -> Just info.scope
  _ -> Nothing

requirementsOf :: MetaContext -> KindMetaVar -> Maybe (Set KindRequirement)
requirementsOf ctx m = case lookupKindMeta ctx m of
  Just (KindUnsolved info) -> Just info.requirements
  _ -> Nothing

-- | A metavariable standing at `Type` rather than at a row kind.
typeInfo :: MetaInfo
typeInfo = rowTypeInfo { kind = XKType }

tvA :: TyVar
tvA = TyVar "a0"

tvB :: TyVar
tvB = TyVar "b0"

tvB' :: TyVar
tvB' = TyVar "b1"

tvR :: TyVar
tvR = TyVar "r0"

tvS :: TyVar
tvS = TyVar "s0"

-- | `Pair τ1 τ2`, which is what the structural cases descend.
pairOf :: XType -> XType -> XType
pairOf x y = XApp (XApp (XCon (Qualified prim (TyName "Pair")) []) x) y

-- | `Record ρ`, which is what puts a row under a `forall`.
recordOf :: XType -> XType
recordOf row = XApp (XCon (Qualified prim (TyName "Record")) []) row

-- | What a unification reads off the site of an equation. No kind variable is in
-- | scope in any case here, so a kind metavariable one creates may mention none.
env :: UnifyEnv
env = { kindVars: Set.empty }

-- | Whether two closed types unify, which is what the cases carrying no
-- | metavariable assert.
unifiesAt :: XKind -> XType -> XType -> P.Boolean
unifiesAt kind t1 t2 = case unifyType env emptyContext kind t1 t2 of
  Solved _ -> true
  _ -> false

spec :: Spec Unit
spec = describe "Stella.Compiler.Elaborate.Unify" do
  describe "kind unification" do
    it "accepts two identical kinds" do
      case unifyKind emptyContext XKType XKType of
        Right _ -> pure unit
        Left err -> show err `shouldEqual` "Right"

    it "rejects two kinds no substitution equates" do
      case unifyKind emptyContext XKType (XKRow RowType) of
        Left (KindNotEqual left right) -> do
          left `shouldEqual` XKType
          right `shouldEqual` XKRow RowType
        other -> show other `shouldEqual` "Left (KindNotEqual …)"

    it "rejects Effect against Type" do
      -- `Effect` is a kind and not a quantifiable one (D24), and it equals
      -- nothing but itself here either
      case unifyKind emptyContext XKEffect XKType of
        Left (KindNotEqual _ _) -> pure unit
        other -> show other `shouldEqual` "Left (KindNotEqual …)"

    it "assigns a metavariable, whichever side it stands on" do
      let m = twoKindMetas closedKindInfo closedKindInfo
      case unifyKind m.ctx (XKMeta m.j) XKType of
        Right ctx -> kindSolutionOf ctx m.j `shouldEqual` Just XKType
        Left err -> show err `shouldEqual` "Right"
      case unifyKind m.ctx (XKRow RowEffect) (XKMeta m.k) of
        Right ctx -> kindSolutionOf ctx m.k `shouldEqual` Just (XKRow RowEffect)
        Left err -> show err `shouldEqual` "Right"

    it "identifies two metavariables" do
      let m = twoKindMetas closedKindInfo closedKindInfo
      case unifyKind m.ctx (XKMeta m.j) (XKMeta m.k) of
        Right ctx -> case unifyKind ctx (XKMeta m.k) XKType of
          Right ctx' -> kindSolutionOf ctx' m.j `shouldEqual` Just XKType
          Left err -> show err `shouldEqual` "Right"
        Left err -> show err `shouldEqual` "Right"

    it "solves both sides of an arrow" do
      -- ?j -> Type  ≡  Row Type -> ?k
      let
        m = twoKindMetas closedKindInfo closedKindInfo
        left = XKFun (XKMeta m.j) XKType
        right = XKFun (XKRow RowType) (XKMeta m.k)
      case unifyKind m.ctx left right of
        Right ctx -> do
          kindSolutionOf ctx m.j `shouldEqual` Just (XKRow RowType)
          kindSolutionOf ctx m.k `shouldEqual` Just XKType
        Left err -> show err `shouldEqual` "Right"

    it "looks through what is already solved" do
      let m = twoKindMetas closedKindInfo closedKindInfo
      case unifyKind m.ctx (XKMeta m.j) XKType of
        Right ctx -> case unifyKind ctx (XKMeta m.j) (XKRow RowType) of
          Left (KindNotEqual _ _) -> pure unit
          other -> show other `shouldEqual` "Left (KindNotEqual …)"
        Left err -> show err `shouldEqual` "Right"

    it "refuses a solution that would make a metavariable refer to itself" do
      let m = twoKindMetas closedKindInfo closedKindInfo
      case unifyKind m.ctx (XKMeta m.j) (XKFun (XKMeta m.j) XKType) of
        Left (KindOccursCheck escaping _) -> escaping `shouldEqual` m.j
        other -> show other `shouldEqual` "Left (KindOccursCheck …)"

    it "refuses a kind variable the metavariable was not created under" do
      let
        k = KindVar "k"
        m = twoKindMetas closedKindInfo closedKindInfo
      case unifyKind m.ctx (XKMeta m.j) (XKVar k) of
        Left (KindEscapingVariable _ escaping) -> escaping `shouldEqual` k
        other -> show other `shouldEqual` "Left (KindEscapingVariable …)"

    it "accepts that kind variable when the metavariable was created under it" do
      let
        k = KindVar "k"
        m = twoKindMetas (kindInfoUnder k) closedKindInfo
      case unifyKind m.ctx (XKMeta m.j) (XKVar k) of
        Right ctx -> kindSolutionOf ctx m.j `shouldEqual` Just (XKVar k)
        Left err -> show err `shouldEqual` "Right"

    it "reports a kind metavariable the context does not hold" do
      case unifyKind emptyContext (XKMeta (KindMetaVar 0)) XKType of
        Left (KindMetaUnbound _) -> pure unit
        other -> show other `shouldEqual` "Left (KindMetaUnbound …)"

    it "reports it against itself too, where reflexivity would otherwise pass" do
      case unifyKind emptyContext (XKMeta (KindMetaVar 0)) (XKMeta (KindMetaVar 0)) of
        Left (KindMetaUnbound _) -> pure unit
        other -> show other `shouldEqual` "Left (KindMetaUnbound …)"

  describe "the row kind of a metavariable" do
    it "solves an unknown row kind against the one the other side carries" do
      -- neither bare metavariable gives its row element kind away, so the two
      -- kinds meet at the refinement rather than at an element
      let
        kindMeta = freshKindMeta closedKindInfo emptyContext
        unknownKind = rowTypeInfo { kind = XKMeta (fst kindMeta) }
        first = freshMeta unknownKind (snd kindMeta)
        second = freshMeta rowTypeInfo (snd first)
        ctx = snd second
        result = unifyRow ctx (XMeta (fst first)) (XMeta (fst second))
      case fst result of
        Solved { metas: ctx' } -> kindSolutionOf ctx' (fst kindMeta) `shouldEqual` Just (XKRow RowType)
        other -> show other `shouldEqual` "Solved …"

  describe "type unification" do
    it "accepts two alpha-equivalent closed foralls" do
      -- forall a. Pair a a  ≡  forall b. Pair b b
      let
        left = XForall tvA XKType (pairOf (XVar tvA) (XVar tvA))
        right = XForall tvB XKType (pairOf (XVar tvB) (XVar tvB))
      unifiesAt XKType left right `shouldEqual` true

    it "reads a nested correspondence innermost first" do
      -- the inner binder of each side shadows the outer, and one name written
      -- twice on the left is what the innermost entry has to settle
      let
        left = XForall tvA XKType (XForall tvA XKType (pairOf (XVar tvA) (XVar tvA)))
        inner = XForall tvB XKType (XForall tvB' XKType (pairOf (XVar tvB') (XVar tvB')))
        outer = XForall tvB XKType (XForall tvB' XKType (pairOf (XVar tvB) (XVar tvB)))
      unifiesAt XKType left inner `shouldEqual` true
      unifiesAt XKType left outer `shouldEqual` false

    it "refuses a bound variable against a free one of the same name" do
      -- the right's `a` is free, so it is not the left's binder however it reads
      let
        left = XForall tvA XKType (XVar tvA)
        right = XForall tvB XKType (XVar tvA)
      unifiesAt XKType left right `shouldEqual` false

    it "solves a metavariable under a forall where the solution needs no binder" do
      let
        m = freshMeta typeInfo emptyContext
        left = XForall tvA XKType (XMeta (fst m))
        right = XForall tvB XKType tA
      case unifyType env (snd m) XKType left right of
        Solved { metas: ctx } -> solutionOf ctx (fst m) `shouldEqual` Just tA
        other -> show other `shouldEqual` "Solved …"

    it "refuses a metavariable whose solution is the other side's binder" do
      -- solving this needs the two binders identified rather than corresponded
      let
        m = freshMeta typeInfo emptyContext
        left = XForall tvA XKType (XMeta (fst m))
        right = XForall tvB XKType (XVar tvB)
      case unifyType env (snd m) XKType left right of
        Mismatch (CannotSolveAcrossForall _ binder) -> binder `shouldEqual` tvB
        other -> show other `shouldEqual` "Mismatch (CannotSolveAcrossForall …)"

    it "refuses it for a binder of its own side too" do
      -- a free `a` on the right shares its spelling with the left's binder, and
      -- the two are told apart by the correspondence rather than by the name
      let
        m = freshMeta (typeInfo { scope = { types: Set.singleton tvA, kinds: Set.empty } }) emptyContext
        left = XForall tvA XKType (XMeta (fst m))
        right = XForall tvB XKType (XVar tvA)
      case unifyType env (snd m) XKType left right of
        Mismatch (CannotSolveAcrossForall _ binder) -> binder `shouldEqual` tvA
        other -> show other `shouldEqual` "Mismatch (CannotSolveAcrossForall …)"

    it "discharges the payload equations a row emits" do
      -- `{ a : A | ?r } ≡ { a : B | ?s }` solves the tails and leaves `A ≡ B`,
      -- which is what fails
      let m = twoMetas rowTypeInfo rowTypeInfo
      case unifyType env m.ctx (XKRow RowType) (field a tA (XMeta m.r)) (field a tB (XMeta m.s)) of
        Mismatch (TypeNotEqual _ _) -> pure unit
        other -> show other `shouldEqual` "Mismatch (TypeNotEqual …)"

    it "solves a metavariable of a kind that is not a row" do
      let m = freshMeta typeInfo emptyContext
      case unifyType env (snd m) XKType (XMeta (fst m)) tA of
        Solved { metas: ctx } -> solutionOf ctx (fst m) `shouldEqual` Just tA
        other -> show other `shouldEqual` "Solved …"

    it "reports a row metavariable met at a kind that is not a row" do
      let m = freshMeta rowTypeInfo emptyContext
      case unifyType env (snd m) XKType (XMeta (fst m)) tA of
        Mismatch (KindMismatch _ _ _) -> pure unit
        other -> show other `shouldEqual` "Mismatch (KindMismatch …)"

    it "descends an application and its head" do
      let m = freshMeta typeInfo emptyContext
      case unifyType env (snd m) XKType (pairOf tA (XMeta (fst m))) (pairOf tA tB) of
        Solved { metas: ctx } -> solutionOf ctx (fst m) `shouldEqual` Just tB
        other -> show other `shouldEqual` "Solved …"

    it "refuses two constructors that differ" do
      unifiesAt XKType tA tB `shouldEqual` false

    it "solves the rows of two Lacks constraints" do
      let
        m = twoMetas rowTypeInfo rowTypeInfo
        left = XConstrained (XLacks (SymbolKey a) (XMeta m.r)) tA
        right = XConstrained (XLacks (SymbolKey a) (XMeta m.s)) tA
      case unifyType env m.ctx XKType left right of
        Solved _ -> pure unit
        other -> show other `shouldEqual` "Solved …"

    it "gives each payload equation of an effect row its own kind" do
      -- the two arguments stand at different kinds, so one kind metavariable
      -- shared between the equations would identify them
      let
        first = freshMeta typeInfo emptyContext
        second = freshMeta (typeInfo { kind = XKFun XKType XKType }) (snd first)
        left = XRowExtend (XRowEffectEntry stateEff [ tA, tB ]) XRowEmpty
        right = XRowExtend (XRowEffectEntry stateEff [ XMeta (fst first), XMeta (fst second) ]) XRowEmpty
      case unifyType env (snd second) (XKRow RowEffect) left right of
        Solved { metas: ctx } -> do
          solutionOf ctx (fst first) `shouldEqual` Just tA
          solutionOf ctx (fst second) `shouldEqual` Just tB
        other -> show other `shouldEqual` "Solved …"

    it "reads the row element kind a Lacks key settles" do
      -- an `EffectKey` keys a `Row Effect` and nothing else, so a row
      -- metavariable of the other kind is caught here
      let
        m = twoMetas effectRowInfo effectRowInfo
        wrong = twoMetas effectRowInfo rowTypeInfo
        lacksOn r = XConstrained (XLacks (EffectKey stateEff) (XMeta r)) tA
      case unifyType env m.ctx XKType (lacksOn m.r) (lacksOn m.s) of
        Solved _ -> pure unit
        other -> show other `shouldEqual` "Solved …"
      case unifyType env wrong.ctx XKType (lacksOn wrong.r) (lacksOn wrong.s) of
        Mismatch (KindMismatch _ _ _) -> pure unit
        other -> show other `shouldEqual` "Mismatch (KindMismatch …)"

    it "checks the kind of a metavariable met against itself" do
      let m = freshMeta rowTypeInfo emptyContext
      case unifyType env (snd m) XKType (XMeta (fst m)) (XMeta (fst m)) of
        Mismatch (KindMismatch _ _ _) -> pure unit
        other -> show other `shouldEqual` "Mismatch (KindMismatch …)"

    it "cancels corresponding rigid row tails" do
      -- forall r. Record ( a : A | r )  ≡  forall s. Record ( a : A | s )
      let
        left = XForall tvR (XKRow RowType) (recordOf (field a tA (XVar tvR)))
        right = XForall tvS (XKRow RowType) (recordOf (field a tA (XVar tvS)))
        differing = XForall tvS (XKRow RowType) (recordOf (field b tA (XVar tvS)))
      unifiesAt XKType left right `shouldEqual` true
      unifiesAt XKType left differing `shouldEqual` false

    it "cancels them beside a flexible tail" do
      -- the corresponding rigid tails cancel, and what is left for the flexible
      -- one on the right is the empty row
      let
        m = freshMeta rowTypeInfo emptyContext
        left = XForall tvR (XKRow RowType) (recordOf (field a tA (XVar tvR)))
        right = XForall tvS (XKRow RowType) (recordOf (field a tA (XRowUnion (XVar tvS) (XMeta (fst m)))))
      case unifyType env (snd m) XKType left right of
        Solved _ -> pure unit
        other -> show other `shouldEqual` "Solved …"

    it "refuses a row metavariable that would absorb one side's binder" do
      let
        m = freshMeta rowTypeInfo emptyContext
        left = XForall tvR (XKRow RowType) (recordOf (field a tA (XVar tvR)))
        right = XForall tvS (XKRow RowType) (recordOf (XMeta (fst m)))
      case unifyType env (snd m) XKType left right of
        Mismatch (CannotSolveAcrossForall _ binder) -> binder `shouldEqual` tvR
        other -> show other `shouldEqual` "Mismatch (CannotSolveAcrossForall …)"

    it "holds a row metavariable to the carried kind where the row has no element" do
      -- `()` gives its row element kind away nowhere, so a flexible root is the
      -- only thing left to read the kind off
      let m = freshMeta effectRowInfo emptyContext
      case unifyType env (snd m) (XKRow RowType) (XMeta (fst m)) XRowEmpty of
        Mismatch (KindMismatch _ _ _) -> pure unit
        other -> show other `shouldEqual` "Mismatch (KindMismatch …)"
      case unifyType env (snd m) (XKRow RowEffect) (XMeta (fst m)) XRowEmpty of
        Solved { metas: ctx } -> solutionOf ctx (fst m) `shouldEqual` Just XRowEmpty
        other -> show other `shouldEqual` "Solved …"

    it "leaves behind no kind metavariable of its own" do
      -- each application stands for its argument's kind with a metavariable, and
      -- a comparison constraining none of them keeps none
      case unifyType env emptyContext XKType (pairOf tA tB) (pairOf tA tB) of
        Solved { metas: ctx } -> Map.isEmpty ctx.kindBindings `shouldEqual` true
        other -> show other `shouldEqual` "Solved …"

    it "keeps a kind metavariable that stood there before it ran" do
      let m = freshKindMeta closedKindInfo emptyContext
      case unifyType env (snd m) XKType (pairOf tA tB) (pairOf tA tB) of
        Solved { metas: ctx } -> Map.member (fst m) ctx.kindBindings `shouldEqual` true
        other -> show other `shouldEqual` "Solved …"

    it "refuses two constraints that differ" do
      let
        m = twoMetas rowTypeInfo rowTypeInfo
        left = XConstrained (XLacks (SymbolKey a) (XMeta m.r)) tA
        right = XConstrained (XLacks (SymbolKey b) (XMeta m.s)) tA
      case unifyType env m.ctx XKType left right of
        Mismatch (ConstraintNotEqual _ _) -> pure unit
        other -> show other `shouldEqual` "Mismatch (ConstraintNotEqual …)"

  describe "kind requirements" do
    it "rejects Effect where a quantifiable kind is required" do
      case requireQuantifiable emptyContext XKEffect of
        Left (KindNotQuantifiable _) -> pure unit
        other -> show other `shouldEqual` "Left (KindNotQuantifiable …)"

    it "accepts an arrow that consumes a row and produces Type" do
      case requireQuantifiable emptyContext (XKFun (XKRow RowType) XKType) of
        Right _ -> pure unit
        Left err -> show err `shouldEqual` "Right"

    it "rejects an arrow that produces a row" do
      -- only row syntax produces a row, so this is not quantifiable however its
      -- argument reads
      case requireQuantifiable emptyContext (XKFun (XKRow RowType) (XKRow RowType)) of
        Left (KindDoesNotProduceType _) -> pure unit
        other -> show other `shouldEqual` "Left (KindDoesNotProduceType …)"

    it "rejects a rigid kind variable where Type must be produced" do
      -- a scheme says nothing about what instantiates `k`, and a row kind is
      -- among the possibilities
      case requireProducesType emptyContext (XKVar (KindVar "k")) of
        Left (KindDoesNotProduceType _) -> pure unit
        other -> show other `shouldEqual` "Left (KindDoesNotProduceType …)"

    it "attaches a requirement to an unsolved metavariable and decides it later" do
      let m = twoKindMetas closedKindInfo closedKindInfo
      case requireQuantifiable m.ctx (XKMeta m.j) of
        Right ctx -> do
          requirementsOf ctx m.j `shouldEqual` Just (Set.singleton Quantifiable)
          case unifyKind ctx (XKMeta m.j) XKEffect of
            Left (KindNotQuantifiable _) -> pure unit
            other -> show other `shouldEqual` "Left (KindNotQuantifiable …)"
        Left err -> show err `shouldEqual` "Right"

    it "decides ProducesType at the assignment" do
      let m = twoKindMetas closedKindInfo closedKindInfo
      case requireProducesType m.ctx (XKMeta m.j) of
        Right ctx -> case unifyKind ctx (XKMeta m.j) (XKRow RowType) of
          Left (KindDoesNotProduceType _) -> pure unit
          other -> show other `shouldEqual` "Left (KindDoesNotProduceType …)"
        Left err -> show err `shouldEqual` "Right"

    it "keeps both requirements where it identifies two metavariables" do
      let m = twoKindMetas closedKindInfo closedKindInfo
      case requireQuantifiable m.ctx (XKMeta m.j) >>= \c -> requireProducesType c (XKMeta m.k) of
        Right ctx -> case unifyKind ctx (XKMeta m.j) (XKMeta m.k) of
          Right ctx' -> do
            requirementsOf ctx' m.k `shouldEqual` Just (Set.fromFoldable [ Quantifiable, ProducesType ])
            case unifyKind ctx' (XKMeta m.k) (XKRow RowType) of
              Left (KindDoesNotProduceType _) -> pure unit
              other -> show other `shouldEqual` "Left (KindDoesNotProduceType …)"
          Left err -> show err `shouldEqual` "Right"
        Left err -> show err `shouldEqual` "Right"

    it "carries a requirement into the arrow a metavariable is solved to" do
      -- ?j is quantifiable and ?j := ?k1 -> ?k2, so ?k2 owes `ProducesType`
      let
        first = freshKindMeta closedKindInfo emptyContext
        second = freshKindMeta closedKindInfo (snd first)
        third = freshKindMeta closedKindInfo (snd second)
        arrow = XKFun (XKMeta (fst second)) (XKMeta (fst third))
      case requireQuantifiable (snd third) (XKMeta (fst first)) of
        Right ctx1 -> case unifyKind ctx1 (XKMeta (fst first)) arrow of
          Right ctx2 -> case unifyKind ctx2 (XKMeta (fst third)) (XKRow RowType) of
            Left (KindDoesNotProduceType _) -> pure unit
            other -> show other `shouldEqual` "Left (KindDoesNotProduceType …)"
          Left err -> show err `shouldEqual` "Right"
        Left err -> show err `shouldEqual` "Right"

  describe "a flexible tail the context does not hold unsolved" do
    it "reports one standing against itself" do
      -- the two occurrences cancel each other, so nothing later in the case
      -- analysis would look at either
      case fst (unifyRow emptyContext (XMeta (MetaVar 0)) (XMeta (MetaVar 0))) of
        Mismatch (MetaUnbound _) -> pure unit
        other -> show other `shouldEqual` "Mismatch (MetaUnbound …)"

    it "reports one standing against a metavariable the context holds" do
      let m = twoMetas rowTypeInfo rowTypeInfo
      case fst (unifyRow m.ctx (XMeta m.r) (XMeta (MetaVar 99))) of
        Mismatch (MetaUnbound unbound) -> unbound `shouldEqual` MetaVar 99
        other -> show other `shouldEqual` "Mismatch (MetaUnbound …)"

  describe "the scope of a metavariable inside a solution" do
    it "narrows a type metavariable the solution mentions" do
      -- `?r` was created under nothing, so what `?p` may later be solved to is
      -- what `?r` may mention and no more
      let
        outer = rowTypeInfo { scope = emptyScope }
        payload = rowTypeInfo { scope = { types: Set.singleton rigidR, kinds: Set.singleton (KindVar "k") } }
        first = freshMeta outer emptyContext
        second = freshMeta payload (snd first)
        ctx = snd second
        result = unifyRow ctx (XMeta (fst first)) (field a (XMeta (fst second)) XRowEmpty)
      case fst result of
        Solved { metas: ctx' } -> scopeOfMeta ctx' (fst second) `shouldEqual` Just emptyScope
        other -> show other `shouldEqual` "Solved …"

    it "narrows a kind metavariable a type solution mentions" do
      -- the escape check reads the rigid variables a solution mentions now, and
      -- an unsolved kind inside it mentions none until it is solved
      let
        k = KindVar "k"
        kindMeta = freshKindMeta (kindInfoUnder k) emptyContext
        outer = rowTypeInfo { scope = emptyScope }
        first = freshMeta outer (snd kindMeta)
        proxied = XCon (Qualified prim (TyName "Proxy")) [ XKMeta (fst kindMeta) ]
        result = unifyRow (snd first) (XMeta (fst first)) (field a proxied XRowEmpty)
      case fst result of
        Solved { metas: ctx } -> case unifyKind ctx (XKMeta (fst kindMeta)) (XKVar k) of
          Left (KindEscapingVariable _ escaping) -> escaping `shouldEqual` k
          other -> show other `shouldEqual` "Left (KindEscapingVariable …)"
        other -> show other `shouldEqual` "Solved …"

    it "refuses where the narrowed metavariable's own kind would escape" do
      -- `?p` stands at a rigid kind variable, and narrowing `?p` to what `?r`
      -- may mention puts that variable outside the scope `?p` keeps it in
      let
        k = KindVar "k"
        outer = rowTypeInfo { scope = emptyScope }
        payload = rowTypeInfo
          { kind = XKVar k
          , scope = { types: Set.empty, kinds: Set.singleton k }
          }
        first = freshMeta outer emptyContext
        second = freshMeta payload (snd first)
        result = unifyRow (snd second) (XMeta (fst first)) (field a (XMeta (fst second)) XRowEmpty)
      case fst result of
        Mismatch (EscapingKindVariable _ escaping) -> escaping `shouldEqual` k
        other -> show other `shouldEqual` "Mismatch (EscapingKindVariable …)"

    it "narrows a kind metavariable standing in the narrowed metavariable's kind" do
      let
        k = KindVar "k"
        kindMeta = freshKindMeta (kindInfoUnder k) emptyContext
        outer = rowTypeInfo { scope = emptyScope }
        payload = rowTypeInfo { kind = XKMeta (fst kindMeta), scope = emptyScope }
        first = freshMeta outer (snd kindMeta)
        second = freshMeta payload (snd first)
        result = unifyRow (snd second) (XMeta (fst first)) (field a (XMeta (fst second)) XRowEmpty)
      case fst result of
        Solved { metas: ctx } -> case unifyKind ctx (XKMeta (fst kindMeta)) (XKVar k) of
          Left (KindEscapingVariable _ escaping) -> escaping `shouldEqual` k
          other -> show other `shouldEqual` "Left (KindEscapingVariable …)"
        other -> show other `shouldEqual` "Solved …"

    it "refuses where a solved kind the metavariable stands at would escape" do
      -- `?p` stands at `?k`, and `?k` is already solved to a rigid kind
      -- variable, so what `?p` holds is that variable however it reads
      let
        k = KindVar "k"
        kindMeta = freshKindMeta (kindInfoUnder k) emptyContext
        outer = rowTypeInfo { scope = emptyScope }
        payload = rowTypeInfo
          { kind = XKMeta (fst kindMeta)
          , scope = { types: Set.empty, kinds: Set.singleton k }
          }
      case unifyKind (snd kindMeta) (XKMeta (fst kindMeta)) (XKVar k) of
        Right solvedKind ->
          let
            first = freshMeta outer solvedKind
            second = freshMeta payload (snd first)
            result = unifyRow (snd second) (XMeta (fst first)) (field a (XMeta (fst second)) XRowEmpty)
          in
            case fst result of
              Mismatch (EscapingKindVariable _ escaping) -> escaping `shouldEqual` k
              other -> show other `shouldEqual` "Mismatch (EscapingKindVariable …)"
        Left err -> show err `shouldEqual` "Right"

    it "narrows a kind metavariable a kind solution mentions" do
      let
        k = KindVar "k"
        m = twoKindMetas closedKindInfo (kindInfoUnder k)
      case unifyKind m.ctx (XKMeta m.j) (XKFun (XKMeta m.k) XKType) of
        Right ctx -> case unifyKind ctx (XKMeta m.k) (XKVar k) of
          Left (KindEscapingVariable _ escaping) -> escaping `shouldEqual` k
          other -> show other `shouldEqual` "Left (KindEscapingVariable …)"
        Left err -> show err `shouldEqual` "Right"

  describe "two flexible tails" do
    it "refines both sides through one fresh tail" do
      -- { a : A | ?r } ≡ { b : B | ?s }
      --   ?r := ( b : B | ?t )   and   ?s := ( a : A | ?t )
      let
        m = twoMetas rowTypeInfo rowTypeInfo
        result = unifyRow m.ctx (field a tA (XMeta m.r)) (field b tB (XMeta m.s))
      case fst result of
        Solved { metas: ctx } -> do
          knownKeysOf ctx m.r `shouldEqual` Just [ SymbolKey b ]
          knownKeysOf ctx m.s `shouldEqual` Just [ SymbolKey a ]
          -- the same fresh tail stands on both sides
          (tailOf ctx m.r == tailOf ctx m.s) `shouldEqual` true
          map Array.length (tailOf ctx m.r) `shouldEqual` Just 1
        other -> show other `shouldEqual` "Solved"

    it "gives the fresh tail the scope both sides had, and nothing else" do
      -- What the tail is obliged to is not here: an obligation that named either
      -- of the two it replaces names it once its constraint is zonked
      let
        outer = rowTypeInfo { scope = emptyScope }
        m = twoMetas outer rowTypeInfo
        result = unifyRow m.ctx (field a tA (XMeta m.r)) (field b tB (XMeta m.s))
      case fst result of
        Solved { metas: ctx } ->
          case tailOf ctx m.r of
            Just [ t ] -> scopeOfMeta ctx t `shouldEqual` Just emptyScope
            _ -> "one fresh tail" `shouldEqual` "…"
        other -> show other `shouldEqual` "Solved"

  describe "rigid and flexible tails" do
    it "lets a flexible tail absorb a rigid one" do
      -- ?s ≡ ( a : A | r ) succeeds: `r` is rigid but the other side can take it
      let
        m = twoMetas rowTypeInfo rowTypeInfo
        result = unifyRow m.ctx (XMeta m.s) (field a tA (XVar rigidR))
      case fst result of
        Solved { metas: ctx } -> knownKeysOf ctx m.s `shouldEqual` Just [ SymbolKey a ]
        other -> show other `shouldEqual` "Solved"

    it "does not let a rigid tail absorb a known field" do
      -- `forall (r : Row Type). r ≡ ( a : A )` fails: `r` is not assignable
      let result = unifyRow emptyContext (XVar rigidR) (field a tA XRowEmpty)
      case fst result of
        Mismatch (RigidTailRemains vars) -> Set.member rigidR vars `shouldEqual` true
        other -> show other `shouldEqual` "Mismatch (RigidTailRemains …)"

    it "does not identify two distinct rigid tails" do
      -- ( a : A | r ) ≡ ( a : A | s ) fails: they stand for different unknowns
      let
        other = TyVar "s"
        result = unifyRow emptyContext (field a tA (XVar rigidR)) (field a tA (XVar other))
      case fst result of
        Mismatch (RigidTailRemains vars) -> do
          Set.member rigidR vars `shouldEqual` true
          Set.member other vars `shouldEqual` true
        outcome -> show outcome `shouldEqual` "Mismatch (RigidTailRemains …)"

    it "cancels a rigid tail the two sides share" do
      -- ( a : A | r ) ≡ ( a : A | r )
      let
        row = field a tA (XVar rigidR)
        result = unifyRow emptyContext row row
      case fst result of
        Solved _ -> pure unit
        other -> show other `shouldEqual` "Solved"

  describe "waiting rather than failing" do
    it "is stuck when one side has two flexible tails" do
      -- ⟨∅;{?r,?s}⟩ ≡ ⟨{a↦A};∅⟩ has two solutions, so it waits
      let
        m = twoMetas rowTypeInfo rowTypeInfo
        result = unifyRow m.ctx (XRowUnion (XMeta m.r) (XMeta m.s)) (field a tA XRowEmpty)
      case fst result of
        Stuck { blockedOn: waiting } -> do
          Set.member m.r waiting `shouldEqual` true
          Set.member m.s waiting `shouldEqual` true
        other -> show other `shouldEqual` "Stuck"

    it "distinguishes waiting from a mismatch" do
      -- one flexible tail and a leftover on the determined side is a failure
      let
        m = twoMetas rowTypeInfo rowTypeInfo
        result = unifyRow m.ctx (field a tA XRowEmpty) (field b tB (XMeta m.s))
      case fst result of
        Mismatch _ -> pure unit
        other -> show other `shouldEqual` "Mismatch"

  describe "what a substitution must preserve" do
    it "refuses a solution of the wrong row kind" do
      let
        effectInfo = rowTypeInfo { kind = XKRow RowEffect }
        m = twoMetas rowTypeInfo effectInfo
        result = unifyRow m.ctx (XMeta m.s) (field a tA XRowEmpty)
      case fst result of
        Mismatch (KindMismatch _ expected actual) -> do
          expected `shouldEqual` XKRow RowEffect
          actual `shouldEqual` XKRow RowType
        other -> show other `shouldEqual` "Mismatch (KindMismatch …)"

    it "refuses a solution mentioning a variable bound inside the metavariable" do
      -- `?m` was created where only `r` is in scope, so a variable bound further
      -- in must not escape into it
      let
        inner = TyVar "inner"
        m = twoMetas rowTypeInfo rowTypeInfo
        result = unifyRow m.ctx (XMeta m.s) (field a tA (XVar inner))
      case fst result of
        Mismatch (EscapingVariable _ escaping) -> escaping `shouldEqual` inner
        other -> show other `shouldEqual` "Mismatch (EscapingVariable …)"

    it "refuses a refinement that would absorb a rigid tail out of scope" do
      -- `?s` was created outside `r` and `?q` inside it, so refining the two
      -- together would put `r` into the solution of `?s`
      let
        outer = rowTypeInfo { scope = emptyScope }
        m = twoMetas rowTypeInfo outer
        result = unifyRow m.ctx (XRowUnion (XMeta m.r) (XVar rigidR)) (XMeta m.s)
      case fst result of
        Mismatch (EscapingVariable _ escaping) -> escaping `shouldEqual` rigidR
        other -> show other `shouldEqual` "Mismatch (EscapingVariable …)"

    it "refuses a solution mentioning a kind variable out of scope" do
      -- `[Γ]` covers kind variables too, which reach a type through the kind
      -- arguments of a constructor
      let
        k = KindVar "k"
        m = twoMetas rowTypeInfo rowTypeInfo
        proxied = XCon (Qualified prim (TyName "Proxy")) [ XKVar k ]
        result = unifyRow m.ctx (XMeta m.s) (field a proxied XRowEmpty)
      case fst result of
        Mismatch (EscapingKindVariable _ escaping) -> escaping `shouldEqual` k
        other -> show other `shouldEqual` "Mismatch (EscapingKindVariable …)"

    it "accepts that kind variable when the metavariable was created under it" do
      let
        k = KindVar "k"
        info = rowTypeInfo { scope = { types: Set.singleton rigidR, kinds: Set.singleton k } }
        m = twoMetas rowTypeInfo info
        proxied = XCon (Qualified prim (TyName "Proxy")) [ XKVar k ]
        result = unifyRow m.ctx (XMeta m.s) (field a proxied XRowEmpty)
      case fst result of
        Solved _ -> pure unit
        other -> show other `shouldEqual` "Solved"

    it "substitutes inside a constraint, not only under it" do
      -- a hole left in `XLacks`'s row would survive zonking and fail `toCore`
      let
        m = twoMetas rowTypeInfo rowTypeInfo
        result = unifyRow m.ctx (XMeta m.s) XRowEmpty
        constrained = XConstrained (XLacks (SymbolKey a) (XMeta m.s)) (XVar rigidR)
      case fst result of
        Solved { metas: ctx } ->
          substitute ctx constrained
            `shouldEqual` XConstrained (XLacks (SymbolKey a) XRowEmpty) (XVar rigidR)
        other -> show other `shouldEqual` "Solved"

    it "does not solve two bare metavariables of different row kinds" do
      -- neither side has an element to give its row element kind away
      let
        m = twoMetas rowTypeInfo (rowTypeInfo { kind = XKRow RowEffect })
        result = unifyRow m.ctx (XMeta m.r) (XMeta m.s)
      case fst result of
        Mismatch (KindMismatch _ _ _) -> pure unit
        other -> show other `shouldEqual` "Mismatch (KindMismatch …)"

    it "emits an equation for each key the two sides share" do
      -- the payloads are not unified here; they are handed back to the caller
      let
        m = twoMetas rowTypeInfo rowTypeInfo
        result = unifyRow m.ctx (field a tA (XMeta m.r)) (field a tB (XMeta m.s))
      snd result `shouldEqual` [ Tuple tA tB ]

    it "equates the arguments of two elements sharing a key and an effect" do
      let
        m = twoMetas effectRowInfo effectRowInfo
        result = unifyRow m.ctx
          (labelledEffect cache stateEff [ tA ] (XMeta m.r))
          (labelledEffect cache stateEff [ tB ] (XMeta m.s))
      snd result `shouldEqual` [ Tuple tA tB ]

    it "fails where a shared key stands over different effects" do
      -- A written key does not determine the payload, so two elements can agree
      -- on the key and still name different protocols
      let
        m = twoMetas effectRowInfo effectRowInfo
        result = unifyRow m.ctx
          (labelledEffect cache stateEff [ tA ] (XMeta m.r))
          (labelledEffect cache readerEff [ tA ] (XMeta m.s))
      case fst result of
        Mismatch (PayloadMismatch key _ _) -> key `shouldEqual` SymbolKey cache
        other -> show other `shouldEqual` "Mismatch (PayloadMismatch …)"

    it "fails where a shared key and effect stand over different arities" do
      -- Arity belongs to the payload, so the shorter argument vector is a
      -- mismatch rather than a prefix of the longer one
      let
        m = twoMetas effectRowInfo effectRowInfo
        result = unifyRow m.ctx
          (labelledEffect cache stateEff [ tA ] (XMeta m.r))
          (labelledEffect cache stateEff [ tA, tB ] (XMeta m.s))
      case fst result of
        Mismatch (PayloadMismatch key _ _) -> key `shouldEqual` SymbolKey cache
        other -> show other `shouldEqual` "Mismatch (PayloadMismatch …)"

    it "equates both the variable and the layout of two regions sharing the key" do
      let
        m = twoMetas effectRowInfo effectRowInfo
        result = unifyRow m.ctx
          (regionOf tA (field a tA XRowEmpty) (XMeta m.r))
          (regionOf tB (field a tB XRowEmpty) (XMeta m.s))
      snd result `shouldEqual`
        [ Tuple tA tB, Tuple (field a tA XRowEmpty) (field a tB XRowEmpty) ]

    it "leaves two regions whose layouts differ to the layout equation" do
      -- The key does not decide the layout, so the two are handed back as an
      -- equation and fail where that equation is solved, not here
      let
        m = twoMetas effectRowInfo effectRowInfo
        left = field a tA XRowEmpty
        right = field b tA XRowEmpty
        result = unifyRow m.ctx
          (regionOf tA left (XMeta m.r))
          (regionOf tA right (XMeta m.s))
      snd result `shouldEqual` [ Tuple tA tA, Tuple left right ]
      case fst (unifyRow m.ctx left right) of
        Mismatch (RowMismatch _ _) -> pure unit
        other -> show other `shouldEqual` "Mismatch (RowMismatch …)"

  describe "what a unification reports" do
    it "names the metavariables it assigned" do
      let
        m = twoMetas rowTypeInfo rowTypeInfo
      case
        unifyType env m.ctx (XKRow RowType)
          (field a tA (XMeta m.r))
          (field b tB (XMeta m.s))
        of
        Solved progress ->
          progress.assigned `shouldEqual` Set.fromFoldable [ m.r, m.s ]
        other -> show other `shouldEqual` "Solved …"

    it "names none where an equation assigned nothing" do
      case unifyType env emptyContext XKType (pairOf tA tB) (pairOf tA tB) of
        Solved progress -> Set.isEmpty progress.assigned `shouldEqual` true
        other -> show other `shouldEqual` "Solved …"

    it "leaves no journal in the context it reports" do
      -- What is reported is read once. A context carrying the same set would have
      -- a caller that threads it act on one assignment twice.
      let
        m = twoMetas rowTypeInfo rowTypeInfo
      case
        unifyType env m.ctx (XKRow RowType)
          (field a tA (XMeta m.r))
          (field b tB (XMeta m.s))
        of
        Solved progress -> Set.isEmpty progress.metas.assigned `shouldEqual` true
        other -> show other `shouldEqual` "Solved …"

    it "refuses a context whose journal nobody has read" do
      -- Emptying it here would make losing an assignment the quiet default: each
      -- one in the set is owed a wake and a re-deciding of what watches it.
      let
        m = twoMetas rowTypeInfo rowTypeInfo
        unread = m.ctx { assigned = Set.singleton m.r }
      case unifyType env unread XKType tA tA of
        Mismatch (AssignmentsUnread ms) -> ms `shouldEqual` Set.singleton m.r
        other -> show other `shouldEqual` "Mismatch (AssignmentsUnread …)"
      case fst (unifyRow unread XRowEmpty XRowEmpty) of
        Mismatch (AssignmentsUnread ms) -> ms `shouldEqual` Set.singleton m.r
        other -> show other `shouldEqual` "Mismatch (AssignmentsUnread …)"

    it "reports what it assigned before a sub-equation it cannot decide" do
      -- The first argument refines both tails; the second has two flexible tails
      -- on one side and waits. What the first did stands in what is reported, so
      -- that a caller re-decides the obligations those assignments were watched by
      -- rather than reading the equation as merely waiting.
      let
        one = freshMeta rowTypeInfo emptyContext
        two = freshMeta rowTypeInfo (snd one)
        three = freshMeta rowTypeInfo (snd two)
        four = freshMeta rowTypeInfo (snd three)
        r = fst one
        s = fst two
        v = fst three
        w = fst four
        left = pairOf (field a tA (XMeta r)) (XRowUnion (XMeta v) (XMeta w))
        right = pairOf (field b tB (XMeta s)) (field cache tA XRowEmpty)
      case unifyType env (snd four) XKType left right of
        Stuck { progress, blockedOn } -> do
          blockedOn `shouldEqual` Set.fromFoldable [ v, w ]
          progress.assigned `shouldEqual` Set.fromFoldable [ r, s ]
          knownKeysOf progress.metas r `shouldEqual` Just [ SymbolKey b ]
        other -> show other `shouldEqual` "Stuck …"
