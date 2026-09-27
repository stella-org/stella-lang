-- | The kernel's observations: what a synthesizer may read of its goal, its
-- | site, the types it holds, and the catalog, without changing anything.
-- |
-- | **An observation changes nothing but the arena.** It issues handles for the
-- | parts of what it shows, and that is all: no metavariable, obligation, job,
-- | or unit of fuel is touched, so reading is never what makes one run differ
-- | from another.
-- |
-- | **What is shown is read against the current `Ψ`.** A handle holds the type
-- | it was issued for, and each observation zonks it first, so one handle viewed
-- | before a metavariable is solved and after shows the metavariable and then
-- | its solution.
-- |
-- | **Every type shown has passed the read-only kinding judgement**, under the
-- | type variables in scope where it stands, so each handle carries kind
-- | evidence that is settled and true. A type the judgement refuses is a defect
-- | of the host, not something a synthesizer is shown.
module Stella.Compiler.Elaborate.Observe
  ( goalType
  , viewType
  , whnf
  , normalizeRow
  , kindOf
  , typeOf
  , localContext
  , localConstraints
  , lookupGlobal
  , declsWithAttr
  ) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.Catalog (lookupEntry, namesWithAttr)
import Stella.Compiler.Elaborate.Diagnostic (Defect(..))
import Stella.Compiler.Elaborate.Elab (Elab, Frame, askEnv, break, currentMetas, issue, resolveExpr, resolveGoal, resolveType)
import Stella.Compiler.Elaborate.Handle (Handle, HandleObject(..), ScopeId(..))
import Stella.Compiler.Elaborate.Kind (XKind(..), fromCoreKind)
import Stella.Compiler.Elaborate.Kinding (KindEvidence(..), KindingFault(..), KindingScope, settledIn, synthKind)
import Stella.Compiler.Elaborate.Pending (goalOf)
import Stella.Compiler.Elaborate.Row (xnf)
import Stella.Compiler.Elaborate.Type (XConstraint(..), XRowEntry(..), XType(..))
import Stella.Compiler.Elaborate.Unify (substitute)
import Stella.Compiler.Elaborate.View (ConstraintView(..), ContextEntry, DeclView, KindView(..), PayloadView(..), RowView, TypeView(..))
import Stella.Compiler.TypedCore (Ident, Qualified, RowElemKind(..), RowKey(..))
import Data.Array as Array
import Data.Either (Either(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))

-- | The type the current goal is written at, standing at `Type`, kinded under
-- | its site's scope.
-- |
-- | The handle names a goal and the frame says which goal is running; the two
-- | must agree. A frame with no goal, or a handle to another goal, is a defect of
-- | the host, since the scope the type is read under is the running goal's site.
goalType :: Handle -> Elab Handle
goalType handle = do
  goal <- resolveGoal handle
  frame <- currentFrame
  case frame.goal of
    Nothing -> break NoGoal
    Just current
      | current.id /= goal.id -> break (GoalNotCurrent goal.id current.id)
      | otherwise -> issueTypeAt root (siteScope frame) (Just XKType) (goalOf current.goal).expectedType

-- | A type one level deep, zonked first.
viewType :: Handle -> Elab TypeView
viewType handle = do
  object <- resolveType handle
  metas <- currentMetas
  let
    vars = object.scope
    builtIn = object.builtIn
  case substitute metas object.type of
    XVar a -> pure (VarType a)
    XMeta m -> MetaType <$> issue (MetaObject m)
    XCon name kinds -> ConType name <$> traverse (kindView vars) kinds
    XApp f a -> do
      headKind <- synthAt vars f
      case headKind of
        ExactKind (XKFun domain result) ->
          AppType
            <$> issueTypeAt builtIn vars (Just (XKFun domain result)) f
            <*> issueTypeAt builtIn vars (Just domain) a
        ExactKind other -> break (KindingFailed (NotAFunctionKind other))
        AnyRow -> break (KindingFailed (KindMismatch AnyRow (XKFun XKType XKType)))
    XForall a kind body -> do
      k <- settledKind vars kind
      ForallType a <$> kindView vars k <*> issueTypeAt Nothing (vars { tyVars = Map.insert a k vars.tyVars }) (Just XKType) body
    XConstrained c body ->
      ConstrainedType <$> constraintView builtIn vars c <*> issueTypeAt Nothing vars (Just XKType) body
    row -> NormalRow <$> rowView handle builtIn vars object.kind row

-- | The same type, zonked. There is no computation at the type level (D1), so
-- | the weak head normal form of a type is the type with what `Ψ` has solved
-- | applied to it.
whnf :: Handle -> Elab Handle
whnf handle = do
  object <- resolveType handle
  metas <- currentMetas
  issue (TypeObject object { type = substitute metas object.type })

-- | A row type in normal form. A type that stands at no row kind is refused.
normalizeRow :: Handle -> Elab RowView
normalizeRow handle = do
  object <- resolveType handle
  metas <- currentMetas
  rowView handle object.builtIn object.scope object.kind (substitute metas object.type)

-- | The kind evidence a type handle holds.
kindOf :: Handle -> Elab KindView
kindOf handle = do
  object <- resolveType handle
  case object.kind of
    AnyRow -> pure KindAnyRow
    ExactKind k -> kindView object.scope k

-- | The type a term is claimed to have, standing at `Type`.
typeOf :: Handle -> Elab Handle
typeOf handle = do
  object <- resolveExpr handle
  frame <- currentFrame
  issueTypeAt root (siteScope frame) (Just XKType) object.claimed

-- | The site's bindings, in ascending order of name, each with its type.
localContext :: Elab (P.Array ContextEntry)
localContext = do
  frame <- currentFrame
  let
    vars = siteScope frame
  traverse
    (\(Tuple name ty) -> { name, type: _ } <$> issueTypeAt root vars (Just XKType) ty)
    (Map.toUnfoldable frame.site.context.vars :: P.Array (Tuple Ident XType))

-- | The row constraints the site assumes, in the order they were assumed.
localConstraints :: Elab (P.Array ConstraintView)
localConstraints = do
  frame <- currentFrame
  traverse (constraintView root (siteScope frame)) frame.site.context.assumed

-- | A catalog entry, with its scheme's body at `Type`, zonked when read.
lookupGlobal :: Qualified Ident -> Elab (Maybe DeclView)
lookupGlobal name = do
  env <- askEnv
  case lookupEntry env.session.catalog name of
    Nothing -> pure Nothing
    Just entry -> do
      scheme <- issueTypeAt Nothing { kindVars: Set.fromFoldable entry.scheme.kindVars, tyVars: Map.empty } (Just XKType) entry.scheme.body
      pure
        ( Just
            { name: entry.name
            , sort: entry.sort
            , kindVars: entry.scheme.kindVars
            , scheme
            , attributes: entry.attributes
            }
        )

-- | The names carrying an attribute of the key given, in ascending order.
declsWithAttr :: P.String -> Elab (P.Array (Qualified Ident))
declsWithAttr key = do
  env <- askEnv
  pure (namesWithAttr env.session.catalog key)

-- The frame, which a kernel operation reading where it stands requires.
currentFrame :: Elab Frame
currentFrame = do
  env <- askEnv
  case env.frame of
    Just frame -> pure frame
    Nothing -> break NoFrame

-- | The root build scope, opened on the site of the running job. What the site
-- | gives — its bindings, its assumptions, the goal's type, a term's claimed
-- | type — is built in it.
root :: Maybe ScopeId
root = Just (ScopeId 0)

siteScope :: Frame -> KindingScope
siteScope frame = { kindVars: frame.site.context.kindVars, tyVars: frame.site.context.tyVars }

-- | Issue a handle to a type, kinded under the type variables given.
-- |
-- | Where the place the type stands at fixes its kind, that kind is given, and
-- | it refines what the judgement alone says of a row standing at any row kind.
-- | A type the judgement refuses, or one not standing at the kind given, is a
-- | defect.
issueTypeAt :: Maybe ScopeId -> KindingScope -> Maybe XKind -> XType -> Elab Handle
issueTypeAt builtIn vars expected ty = do
  metas <- currentMetas
  let
    zonked = substitute metas ty
  evidence <- synthAt vars zonked
  kind <- case evidence, expected of
    _, Nothing -> pure evidence
    AnyRow, Just k@(XKRow _) -> pure (ExactKind k)
    ExactKind k, Just k' | k == k' -> pure evidence
    _, Just k -> break (KindingFailed (KindMismatch evidence k))
  issue (TypeObject { type: zonked, kind, scope: vars, builtIn })

-- | A row view of a type at the kind evidence given.
rowView :: Handle -> Maybe ScopeId -> KindingScope -> KindEvidence -> XType -> Elab RowView
rowView handle builtIn vars evidence row = do
  elementKind <- case evidence of
    ExactKind (XKRow e) -> pure (Just e)
    AnyRow -> pure Nothing
    _ -> break (NotARowType handle)
  case xnf row of
    Left _ -> break (NotARowType handle)
    Right n -> do
      known <- traverse
        (\(Tuple key entry) -> { key, payload: _ } <$> payloadView builtIn vars entry)
        (Map.toUnfoldable n.known :: P.Array (Tuple RowKey XRowEntry))
      flexible <- traverse (issue <<< MetaObject) (Set.toUnfoldable n.flexible)
      pure { elementKind, known, rigid: Set.toUnfoldable n.rigid, flexible }

payloadView :: Maybe ScopeId -> KindingScope -> XRowEntry -> Elab PayloadView
payloadView builtIn vars = case _ of
  XRowTypeEntry _ ty -> TypePayload <$> issueTypeAt builtIn vars (Just XKType) ty
  XRowEffectEntry e args -> EffectPayload e <$> effectArgs e args
  XRowLabelledEffectEntry _ e args -> EffectPayload e <$> effectArgs e args
  XRowRegionEntry var cells ->
    RegionPayload
      <$> issueTypeAt builtIn vars (Just XKType) var
      <*> issueTypeAt builtIn vars (Just (XKRow RowType)) cells
  where
  effectArgs e args = do
    env <- askEnv
    case Map.lookup e env.session.kinding.effects of
      Nothing -> break (KindingFailed (UnknownEffect e))
      Just params ->
        traverse (\(Tuple k a) -> issueTypeAt builtIn vars (Just (fromCoreKind k)) a) (Array.zip params args)

constraintView :: Maybe ScopeId -> KindingScope -> XConstraint -> Elab ConstraintView
constraintView builtIn vars = case _ of
  XLacks key row -> LacksView key <$> issueTypeAt builtIn vars (keyRowKind key) row
  XDisjoint l r -> do
    left <- synthAt vars l
    right <- synthAt vars r
    let
      shared = case left, right of
        ExactKind k, _ -> Just k
        _, ExactKind k -> Just k
        _, _ -> Nothing
    DisjointView <$> issueTypeAt builtIn vars shared l <*> issueTypeAt builtIn vars shared r

keyRowKind :: RowKey -> Maybe XKind
keyRowKind = case _ of
  TagKey _ -> Just (XKRow RowType)
  PositionKey _ -> Just (XKRow RowType)
  EffectKey _ -> Just (XKRow RowEffect)
  RegionKey -> Just (XKRow RowEffect)
  SymbolKey _ -> Nothing

-- | A settled kind, well-formed in the scope given, as a view.
kindView :: KindingScope -> XKind -> Elab KindView
kindView scope kind = do
  k <- settledKind scope kind
  case go k of
    Just view -> pure view
    Nothing -> break (KindingFailed KindNotSettled)
  where
  go = case _ of
    XKType -> Just KindType
    XKEffect -> Just KindEffect
    XKRow e -> Just (KindRow e)
    XKFun a b -> KindFun <$> go a <*> go b
    XKVar v -> Just (KindVar v)
    XKMeta _ -> Nothing

kinded :: forall a. Either KindingFault a -> Elab a
kinded = case _ of
  Left fault -> break (KindingFailed fault)
  Right a -> pure a

-- | The kind evidence of a type under the type variables given, read against the
-- | session's type-level environment and the current `Ψ`.
synthAt :: KindingScope -> XType -> Elab KindEvidence
synthAt vars ty = do
  env <- askEnv
  metas <- currentMetas
  kinded (synthKind env.session.kinding vars metas ty)

-- | A kind, zonked, where it is settled and well-formed in the scope given.
settledKind :: KindingScope -> XKind -> Elab XKind
settledKind scope kind = do
  metas <- currentMetas
  kinded (settledIn scope metas kind)
