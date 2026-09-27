-- | What the kernel's requests over types share: resolving a build scope's
-- | types, kinding what is built in one, and the site an obligation raised in
-- | one carries.
-- |
-- | A request takes a build scope as a handle the host issued, and everything
-- | here reads the scope and nothing the caller states: the types it may use are
-- | the ones built in it or in its ancestors, what is built in it is kinded under
-- | what it binds, and an obligation raised in it is decided against its context.
module Stella.Compiler.Elaborate.BuildScope
  ( usableIn
  , usableTermIn
  , issueTerm
  , built
  , kinded
  , issueBuilt
  , siteOf
  , requiredIn
  , constraintIn
  , kindingScopeOf
  , kindIn
  , rejected
  , schemeAt
  , mapChildren
  , foldChildren
  ) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.Catalog (lookupEntry)
import Stella.Compiler.Elaborate.Diagnostic (BuildError(..), Defect(..))
import Stella.Compiler.Elaborate.Elab (Elab, askEnv, break, currentMetas, issue, require, resolveExpr, resolveType)
import Stella.Compiler.Elaborate.Handle (ExprObject, Handle, HandleObject(..), ScopeObject, TypeObject)
import Stella.Compiler.Elaborate.Kind (XKind(..))
import Stella.Compiler.Elaborate.Kinding (KindEvidence, KindingScope, checkConstraint, checkKind, quantifiable, settledIn, synthKind)
import Stella.Compiler.Elaborate.Pending (Site)
import Stella.Compiler.Elaborate.Term (XExpr)
import Stella.Compiler.Elaborate.Type (XConstraint(..), XRowEntry(..), XType(..))
import Stella.Compiler.Elaborate.Unify (substitute)
import Stella.Compiler.Elaborate.View (ConstraintView(..), KindView(..))
import Stella.Compiler.TypedCore (Ident, KindVar, Qualified)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldMap, for_)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Data.Traversable (traverse)

-- | A type the scope may use: one built in it or in one of its ancestors.
usableIn :: ScopeObject -> Handle -> Elab TypeObject
usableIn scope handle = do
  object <- resolveType handle
  case object.builtIn of
    Just id | id == scope.id || Set.member id scope.ancestors -> pure object
    _ -> rejected (ScopeViolation handle)

-- | A term the scope may use: one built in it or in one of its ancestors, by the
-- | rule a type is held to. A term built under a binder mentions what the binder
-- | binds or assumes, and one built in no build scope belongs to none.
usableTermIn :: ScopeObject -> Handle -> Elab ExprObject
usableTermIn scope handle = do
  object <- resolveExpr handle
  case object.builtIn of
    Just id | id == scope.id || Set.member id scope.ancestors -> pure object
    _ -> rejected (ScopeViolation handle)

-- | Issue a term built in the scope, claimed at the type given, zonked.
-- |
-- | The claim is kinded at `Type` under the scope. A claim the host computed, or
-- | one taken from a type the scope may use, stands there already, so a claim
-- | that does not is a defect of the host.
issueTerm :: ScopeObject -> XExpr Unit -> XType -> Elab Handle
issueTerm scope term claimed = do
  env <- askEnv
  metas <- currentMetas
  let
    zonked = substitute metas claimed
  case checkKind env.session.kinding (kindingScopeOf scope) metas XKType zonked of
    Left fault -> break (KindingFailed fault)
    Right _ ->
      issue (ExprObject { term, claimed: zonked, scope: kindingScopeOf scope, builtIn: Just scope.id })

-- | Issue a type built in the scope, once the kinding judgement admits it.
built :: ScopeObject -> XType -> Elab Handle
built scope ty = kinded scope ty >>= issueBuilt scope

-- | A type zonked, with the kind evidence the judgement gives it in the scope.
kinded :: ScopeObject -> XType -> Elab { type :: XType, kind :: KindEvidence }
kinded scope ty = do
  env <- askEnv
  metas <- currentMetas
  let
    zonked = substitute metas ty
  case synthKind env.session.kinding (kindingScopeOf scope) metas zonked of
    Left fault -> rejected (IllKinded fault)
    Right kind -> pure { type: zonked, kind }

issueBuilt :: ScopeObject -> { type :: XType, kind :: KindEvidence } -> Elab Handle
issueBuilt scope typed =
  issue (TypeObject { type: typed.type, kind: typed.kind, scope: kindingScopeOf scope, builtIn: Just scope.id })

-- | The site an obligation built in the scope carries: the scope's context, which
-- | holds every assumption opened around it, and the origin of the running job.
siteOf :: ScopeObject -> Elab Site
siteOf scope = do
  env <- askEnv
  case env.frame of
    Nothing -> break NoFrame
    Just frame -> pure { context: scope.context, origin: frame.site.origin }

-- | Require what a row being built needs, of the scope it is built in.
requiredIn :: ScopeObject -> XConstraint -> Elab Unit
requiredIn scope constraint = do
  site <- siteOf scope
  require site constraint

-- | A constraint from types the scope may use, judged well-formed there.
constraintIn :: ScopeObject -> ConstraintView -> Elab XConstraint
constraintIn scope view = do
  constraint <- case view of
    LacksView key row -> XLacks key <<< _.type <$> usableIn scope row
    DisjointView l r -> XDisjoint <$> (_.type <$> usableIn scope l) <*> (_.type <$> usableIn scope r)
  env <- askEnv
  metas <- currentMetas
  case checkConstraint env.session.kinding (kindingScopeOf scope) metas constraint of
    Left fault -> rejected (IllKinded fault)
    Right _ -> pure constraint

kindingScopeOf :: ScopeObject -> KindingScope
kindingScopeOf scope = { kindVars: scope.context.kindVars, tyVars: scope.context.tyVars }

-- | A kind view as a kind the scope can write.
kindIn :: ScopeObject -> KindView -> Elab XKind
kindIn scope view = case toKind view of
  Nothing -> rejected AnyRowAsKind
  Just kind -> do
    metas <- currentMetas
    case settledIn (kindingScopeOf scope) metas kind of
      Left fault -> rejected (IllKinded fault)
      Right k -> pure k
  where
  toKind = case _ of
    KindType -> Just XKType
    KindEffect -> Just XKEffect
    KindRow e -> Just (XKRow e)
    KindFun a b -> XKFun <$> toKind a <*> toKind b
    KindVar v -> Just (XKVar v)
    KindAnyRow -> Nothing

rejected :: forall a. BuildError -> Elab a
rejected err = break (BuildRejected err)

-- | A catalog entry's scheme at the kinds given, read by name: the kinds as
-- | they are written in a reference to it, and `τ[k̄ := κ̄]`.
-- |
-- | **The scheme is judged in its own scope before the caller's is involved**:
-- | at `Type`, under the kind variables it declares and no type variable, as
-- | `lookupGlobal` judges it. Judged only after substitution, in the caller's
-- | scope, a variable free in the scheme would be taken for one of the caller's
-- | that happens to share its name. A scheme failing that is the host's defect,
-- | the catalog being the host's. The kinds must be quantifiable and mention
-- | only kind variables the scope binds.
schemeAt :: ScopeObject -> Qualified Ident -> P.Array KindView -> Elab { kinds :: P.Array XKind, type :: XType }
schemeAt scope name kinds = do
  env <- askEnv
  case lookupEntry env.session.catalog name of
    Nothing -> rejected (UnknownScheme name)
    Just entry
      | Array.length entry.scheme.kindVars /= Array.length kinds ->
          rejected (SchemeArity name (Array.length entry.scheme.kindVars) (Array.length kinds))
      | otherwise -> do
          metas <- currentMetas
          let
            declared = { kindVars: Set.fromFoldable entry.scheme.kindVars, tyVars: Map.empty }
          case checkKind env.session.kinding declared metas XKType (substitute metas entry.scheme.body) of
            Left fault -> break (KindingFailed fault)
            Right _ -> pure unit
          ks <- traverse (kindIn scope) kinds
          for_ ks \k -> case quantifiable k of
            Left fault -> rejected (IllKinded fault)
            Right _ -> pure unit
          let
            instantiation = Map.fromFoldable (Array.zip entry.scheme.kindVars ks)
          pure { kinds: ks, type: substituteKindVars instantiation entry.scheme.body }

-- | `τ[k̄ := κ̄]` over the kinds written in a type.
substituteKindVars :: Map KindVar XKind -> XType -> XType
substituteKindVars instantiation = go
  where
  kind = case _ of
    XKVar v -> case Map.lookup v instantiation of
      Just k -> k
      Nothing -> XKVar v
    XKFun a b -> XKFun (kind a) (kind b)
    other -> other

  go = case _ of
    XCon name kinds -> XCon name (map kind kinds)
    XForall b k body -> XForall b (kind k) (go body)
    other -> mapChildren go other

-- | A function applied to the immediate type children of a type, binders and
-- | kinds left as they are.
mapChildren :: (XType -> XType) -> XType -> XType
mapChildren f = case _ of
  XApp g a -> XApp (f g) (f a)
  XForall b k body -> XForall b k (f body)
  XConstrained c body -> XConstrained (constraint c) (f body)
  XRowExtend entry rest -> XRowExtend (entryOf entry) (f rest)
  XRowUnion l r -> XRowUnion (f l) (f r)
  other -> other
  where
  constraint = case _ of
    XLacks key row -> XLacks key (f row)
    XDisjoint l r -> XDisjoint (f l) (f r)

  entryOf = case _ of
    XRowTypeEntry key ty -> XRowTypeEntry key (f ty)
    XRowEffectEntry e args -> XRowEffectEntry e (map f args)
    XRowLabelledEffectEntry s e args -> XRowLabelledEffectEntry s e (map f args)
    XRowRegionEntry var cells -> XRowRegionEntry (f var) (f cells)

-- | The immediate type children of a type, folded.
foldChildren :: forall m. Monoid m => (XType -> m) -> XType -> m
foldChildren f = case _ of
  XApp g a -> f g <> f a
  XForall _ _ body -> f body
  XConstrained c body -> constraint c <> f body
  XRowExtend entry rest -> entryOf entry <> f rest
  XRowUnion l r -> f l <> f r
  _ -> mempty
  where
  constraint = case _ of
    XLacks _ row -> f row
    XDisjoint l r -> f l <> f r

  entryOf = case _ of
    XRowTypeEntry _ ty -> f ty
    XRowEffectEntry _ args -> foldMap f args
    XRowLabelledEffectEntry _ _ args -> foldMap f args
    XRowRegionEntry var cells -> f var <> f cells
