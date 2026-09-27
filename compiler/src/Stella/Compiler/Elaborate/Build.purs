-- | The kernel's type builders: how a synthesizer assembles a type from the
-- | handles it holds.
-- |
-- | **A type is built in a build scope**, an opaque handle naming what the type
-- | may mention. The root is opened on the site of the running job; opening a
-- | `forall` or a constraint gives a child scope whose body is built in it. A
-- | builder uses a type only where the type was built in the scope given or in
-- | one of its ancestors, and never merges the scopes of the types it is given:
-- | two binders that share a name and a kind are still two binders, and only the
-- | scope a type was built in says which one it mentions.
-- |
-- | **A type observed rather than built carries the scope it came from.** What the
-- | site gives is the root's; a part of a type is the scope of the whole; the body
-- | of a `forall` or of a constraint, and a catalog scheme, belong to no build
-- | scope and reach a builder only through the operation that opens them —
-- | `instantiateForall` for a type, `instantiateScheme` for a scheme.
-- |
-- | **The host ABI is first order.** Opening a binder hands back the binder and
-- | the scope its body is built in, and closing it takes both back, in the scope
-- | it was opened in. No request of the host waits on a guest closure. **Every
-- | binder opened is closed exactly once, inside out, before the attempt
-- | succeeds**: what is built under one — an obligation proved from its assumption, a job, a
-- | metavariable — would otherwise commit without the type carrying it.
-- |
-- | **A row is sharp by construction.** Kinding judges a row's shape; that no key
-- | occurs twice is what extending and joining a row require of it, and each
-- | builder introduces that requirement together with the row, as an obligation
-- | decided against the facts of the scope it is built in. A row it breaks is a
-- | failure, as any constraint a candidate breaks is.
-- |
-- | Every result is kinded by the read-only kinding judgement under its scope. A
-- | builder asked for what cannot be built — a kind that does not fit, a type
-- | from another scope, a binder closed where it was not opened — is a defect of
-- | the synthesizer that asked; whether a candidate fits a goal is `unify`'s to
-- | decide.
module Stella.Compiler.Elaborate.Build
  ( rootScope
  , typeVariable
  , typeConstructor
  , applyType
  , emptyRow
  , extendRow
  , unionRow
  , openForall
  , closeForall
  , openConstraint
  , closeConstraint
  , instantiateForall
  , instantiateScheme
  ) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.Catalog (lookupEntry)
import Stella.Compiler.Elaborate.Context as Context
import Stella.Compiler.Elaborate.Context (bindTyVar)
import Stella.Compiler.Elaborate.Diagnostic (BuildError(..), Defect(..))
import Stella.Compiler.Elaborate.Elab (Elab, askEnv, assume, break, currentMetas, freshBinderName, freshScopeId, holdOpen, issue, postpone, release, Release(..), require, resolveBinder, resolveScope, resolveType)
import Stella.Compiler.Elaborate.Handle (BinderObject(..), Handle, HandleObject(..), ScopeId(..), ScopeObject, TypeObject)
import Stella.Compiler.Elaborate.Kind (XKind(..))
import Stella.Compiler.Elaborate.Kinding (KindEvidence, KindingScope, checkConstraint, checkKind, quantifiable, settledIn, synthKind)
import Stella.Compiler.Elaborate.Pending (Site)
import Stella.Compiler.Elaborate.Type (MetaVar, XConstraint(..), XRowEntry(..), XType(..), freeRigids, metasOf, xRowEntryKey)
import Stella.Compiler.Elaborate.Unify (MetaBinding(..), MetaContext, lookupMeta, substitute)
import Stella.Compiler.Elaborate.View (ConstraintView(..), KindView(..), PayloadView(..))
import Stella.Compiler.TypedCore (Ident, KindVar, Qualified, RowKey(..), TyName, TyVar(..))
import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldMap, for_)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Set as Set
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))

-- | The root build scope, opened on the site of the running job.
rootScope :: Elab Handle
rootScope = do
  env <- askEnv
  case env.frame of
    Nothing -> break NoFrame
    Just frame -> issue (ScopeObject { id: ScopeId 0, ancestors: Set.empty, context: frame.site.context })

-- | A type variable the scope binds.
typeVariable :: Handle -> TyVar -> Elab Handle
typeVariable scopeHandle name = do
  scope <- resolveScope scopeHandle
  if Map.member name scope.context.tyVars then built scope (XVar name)
  else rejected (UnboundTypeVariable name)

-- | A type constructor at the kinds given.
typeConstructor :: Handle -> Qualified TyName -> P.Array KindView -> Elab Handle
typeConstructor scopeHandle name kinds = do
  scope <- resolveScope scopeHandle
  ks <- traverse (kindIn scope) kinds
  built scope (XCon name ks)

-- | `f a`.
applyType :: Handle -> Handle -> Handle -> Elab Handle
applyType scopeHandle f a = do
  scope <- resolveScope scopeHandle
  head <- usableIn scope f
  argument <- usableIn scope a
  built scope (XApp head.type argument.type)

-- | `()`, standing at any row kind.
emptyRow :: Handle -> Elab Handle
emptyRow scopeHandle = do
  scope <- resolveScope scopeHandle
  built scope XRowEmpty

-- | `( key : payload | rest )`, requiring `key ∉ rest`.
-- |
-- | The key says which element the payload makes: a structural key a field of a
-- | type, `EffectKey E` an unlabelled `E`, and a `SymbolKey` over an effect a
-- | labelled one. A region element is refused: only the handler owning a region
-- | introduces or removes one.
extendRow :: Handle -> RowKey -> PayloadView -> Handle -> Elab Handle
extendRow scopeHandle key payload restHandle = do
  scope <- resolveScope scopeHandle
  entry <- entryIn scope key payload
  rest <- usableIn scope restHandle
  row <- kinded scope (XRowExtend entry rest.type)
  requiredIn scope (XLacks (xRowEntryKey entry) rest.type)
  issueBuilt scope row

-- | `left ⊎ right`, requiring `left # right`.
unionRow :: Handle -> Handle -> Handle -> Elab Handle
unionRow scopeHandle leftHandle rightHandle = do
  scope <- resolveScope scopeHandle
  left <- usableIn scope leftHandle
  right <- usableIn scope rightHandle
  row <- kinded scope (XRowUnion left.type right.type)
  requiredIn scope (XDisjoint left.type right.type)
  issueBuilt scope row

-- | Open `forall (a : κ)`: a binder, the variable it binds as a type built in the
-- | body's scope, and that scope.
-- |
-- | The variable is named after the hint and made fresh by the host, so it
-- | captures no name the scope already binds.
openForall
  :: Handle
  -> P.String
  -> KindView
  -> Elab { binder :: Handle, variable :: Handle, bodyScope :: Handle }
openForall scopeHandle hint kindView = do
  scope <- resolveScope scopeHandle
  kind <- kindIn scope kindView
  case quantifiable kind of
    Left fault -> rejected (IllKinded fault)
    Right _ -> pure unit
  name <- freshBinderName hint
  childId <- freshScopeId
  let
    child =
      { id: childId
      , ancestors: Set.insert scope.id scope.ancestors
      , context: bindTyVar scope.context name kind
      }
  binder <- issue (BinderObject (ForallBinder { name, kind, parent: scope.id, body: childId }))
  holdOpen childId child.ancestors
  variable <- built child (XVar name)
  bodyScope <- issue (ScopeObject child)
  pure { binder, variable, bodyScope }

-- | Close a `forall` opened in this scope, over a body built in the body's scope
-- | or in one this scope can use.
closeForall :: Handle -> Handle -> Handle -> Elab Handle
closeForall scopeHandle binderHandle bodyHandle = do
  scope <- resolveScope scopeHandle
  resolveBinder binderHandle >>= case _ of
    ForallBinder b -> do
      body <- closing scope binderHandle b bodyHandle
      built scope (XForall b.name b.kind body)
    AssumedConstraint _ -> rejected (BinderMisuse binderHandle)

-- | Open `constraint =>`: a binder, and the scope its body is built in, which
-- | assumes the constraint.
-- |
-- | The constraint is judged well-formed here, and nothing more. **Whether it
-- | can hold is decided where it is closed**, where the assumption is held as an
-- | obligation; a constraint that cannot hold makes every requirement built
-- | under it fail on the facts of its scope, and the binder must be closed
-- | before the attempt succeeds.
openConstraint :: Handle -> ConstraintView -> Elab { assumption :: Handle, bodyScope :: Handle }
openConstraint scopeHandle view = do
  scope <- resolveScope scopeHandle
  constraint <- constraintIn scope view
  childId <- freshScopeId
  let
    child =
      { id: childId
      , ancestors: Set.insert scope.id scope.ancestors
      , context: Context.assume scope.context constraint
      }
  assumption <- issue (BinderObject (AssumedConstraint { constraint, parent: scope.id, body: childId }))
  holdOpen childId child.ancestors
  bodyScope <- issue (ScopeObject child)
  pure { assumption, bodyScope }

-- | Close a constraint opened in this scope, over a body built in the body's
-- | scope or in one this scope can use, holding the assumption from here on.
-- |
-- | **The assumption is held as an obligation where it is closed**: an
-- | assignment making it unsatisfiable is refused from then on, and one it
-- | already cannot satisfy is a failure now.
closeConstraint :: Handle -> Handle -> Handle -> Elab Handle
closeConstraint scopeHandle binderHandle bodyHandle = do
  scope <- resolveScope scopeHandle
  resolveBinder binderHandle >>= case _ of
    AssumedConstraint b -> do
      body <- closing scope binderHandle b bodyHandle
      constrained <- kinded scope (XConstrained b.constraint body)
      site <- siteOf scope
      _ <- assume site b.constraint
      issueBuilt scope constrained
    ForallBinder _ -> rejected (BinderMisuse binderHandle)

-- | `forall (a : κ). body` applied to a type at `κ`: `body[a := argument]`.
-- |
-- | Both sides are zonked first. The substitution is capture-avoiding: a binder
-- | of the body that the argument mentions free is renamed, to a name drawn from
-- | the host's supply of fresh binder names, which nothing else mentions.
-- |
-- | **An unsolved metavariable that could come to mention a variable the
-- | substitution treats specially postpones the instantiation until it is
-- | solved**: one in the body whose scope holds the binder or a binder being
-- | renamed, and one in the argument whose scope holds a binder of the body. A
-- | substitution stops at an unsolved metavariable, so the first's later solution
-- | could mention a binder the result no longer has, and the second's could be
-- | captured by a binder that was not renamed.
instantiateForall :: Handle -> Handle -> Handle -> Elab Handle
instantiateForall scopeHandle forallHandle argumentHandle = do
  scope <- resolveScope scopeHandle
  whole <- usableIn scope forallHandle
  argumentObject <- usableIn scope argumentHandle
  metas <- currentMetas
  let
    argument = substitute metas argumentObject.type
  case substitute metas whole.type of
    XForall a kind body -> do
      env <- askEnv
      case checkKind env.session.kinding (kindingScopeOf scope) metas kind argument of
        Left fault -> rejected (IllKinded fault)
        Right _ -> do
          let
            binders = bindersOf body
            capturing = Set.intersection binders (freeRigids argument)
            reaching =
              Set.filter (mayMention metas (Set.insert a capturing)) (metasOf body)
                <> Set.filter (mayMention metas binders) (metasOf argument)
          unless (Set.isEmpty reaching) (postpone reaching)
          renames <- traverse renamed (Set.toUnfoldable capturing :: P.Array TyVar)
          built scope (substituteTyVar a argument (Map.fromFoldable renames) body)
    _ -> rejected (NotAForall forallHandle)
  where
  renamed b@(TyVar hint) = Tuple b <$> freshBinderName hint

-- | A catalog entry's scheme at the kinds given: `forall k̄. τ` with `k̄ := κ̄`.
-- |
-- | The entry is read from the catalog by name. The kinds must be quantifiable
-- | and mention only kind variables the scope binds.
-- |
-- | **The scheme is judged in its own scope before the caller's is involved**:
-- | at `Type`, under the kind variables it declares and no type variable, as
-- | `lookupGlobal` judges it. Judged only after substitution, in the caller's
-- | scope, a variable free in the scheme would be taken for one of the caller's
-- | that happens to share its name. A scheme failing that is the host's defect,
-- | the catalog being the host's.
instantiateScheme :: Handle -> Qualified Ident -> P.Array KindView -> Elab Handle
instantiateScheme scopeHandle name kinds = do
  scope <- resolveScope scopeHandle
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
          built scope (substituteKindVars instantiation entry.scheme.body)

-- A type the scope may use: one built in it or in one of its ancestors.
usableIn :: ScopeObject -> Handle -> Elab TypeObject
usableIn scope handle = do
  object <- resolveType handle
  case object.builtIn of
    Just id | id == scope.id || Set.member id scope.ancestors -> pure object
    _ -> rejected (ScopeViolation handle)

-- Issue a type built in the scope, once the kinding judgement admits it.
built :: ScopeObject -> XType -> Elab Handle
built scope ty = kinded scope ty >>= issueBuilt scope

-- A type zonked, with the kind evidence the judgement gives it in the scope.
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

-- What closing a binder checks, whatever sort it is: that it was opened in this
-- scope, that its body is built where its own scope or this one can use it, and
-- that it is still open with nothing opened inside its body still open, which
-- closing it ends. The body's type is the answer.
closing
  :: forall r
   . ScopeObject
  -> Handle
  -> { parent :: ScopeId, body :: ScopeId | r }
  -> Handle
  -> Elab XType
closing scope binderHandle binder bodyHandle = do
  when (binder.parent /= scope.id) (rejected (BinderMisuse binderHandle))
  body <- resolveType bodyHandle
  let
    visible = case body.builtIn of
      Just id -> id == binder.body || id == scope.id || Set.member id scope.ancestors
      Nothing -> false
  unless visible (rejected (ScopeViolation bodyHandle))
  release binder.body >>= case _ of
    Released -> pure unit
    NotOpen -> rejected (BinderClosed binderHandle)
    EnclosesOpen _ -> rejected (EnclosesOpenBinder binderHandle)
  pure body.type

-- The site an obligation built in the scope carries: the scope's context, which
-- holds every assumption opened around it, and the origin of the running job.
siteOf :: ScopeObject -> Elab Site
siteOf scope = do
  env <- askEnv
  case env.frame of
    Nothing -> break NoFrame
    Just frame -> pure { context: scope.context, origin: frame.site.origin }

-- Require what a row being built needs, of the scope it is built in.
requiredIn :: ScopeObject -> XConstraint -> Elab Unit
requiredIn scope constraint = do
  site <- siteOf scope
  require site constraint

-- The element a key and a payload make, from types the scope may use.
entryIn :: ScopeObject -> RowKey -> PayloadView -> Elab XRowEntry
entryIn scope key = case _ of
  RegionPayload _ _ -> rejected RegionEntryForbidden
  TypePayload h -> case key of
    SymbolKey _ -> XRowTypeEntry key <$> typeIn h
    TagKey _ -> XRowTypeEntry key <$> typeIn h
    PositionKey _ -> XRowTypeEntry key <$> typeIn h
    _ -> rejected (EntryMismatch key)
  EffectPayload e args -> case key of
    EffectKey e' | e' == e -> XRowEffectEntry e <$> traverse typeIn args
    SymbolKey s -> XRowLabelledEffectEntry s e <$> traverse typeIn args
    _ -> rejected (EntryMismatch key)
  where
  typeIn h = _.type <$> usableIn scope h

-- A constraint from types the scope may use, judged well-formed there.
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

-- A kind view as a kind the scope can write.
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

-- | Whether an unsolved metavariable's scope holds any of the variables given.
mayMention :: MetaContext -> Set TyVar -> MetaVar -> P.Boolean
mayMention metas vars m = case lookupMeta metas m of
  Just (Unsolved info) -> not (Set.isEmpty (Set.intersection info.scope.types vars))
  _ -> false

-- | `τ[a := σ]`, with each binder of `τ` the map names renamed to the fresh name
-- | it gives.
-- |
-- | Renaming by name is sound because every new name is fresh: two binders
-- | sharing a name get one new name, and the inner still shadows the outer. Below
-- | a binder named `a` nothing is substituted, and only the renaming continues.
substituteTyVar :: TyVar -> XType -> Map TyVar TyVar -> XType -> XType
substituteTyVar a argument renames = go false Map.empty
  where
  go shadowed inScope = case _ of
    XVar v
      | not shadowed && v == a -> argument
      | otherwise -> case Map.lookup v inScope of
          Just v' -> XVar v'
          Nothing -> XVar v
    XForall b k body
      | b == a -> XForall b k (go true (Map.delete b inScope) body)
      | otherwise -> case Map.lookup b renames of
          Just b' -> XForall b' k (go shadowed (Map.insert b b' inScope) body)
          Nothing -> XForall b k (go shadowed (Map.delete b inScope) body)
    other -> mapChildren (go shadowed inScope) other

-- | The type variables a `forall` inside the type binds.
bindersOf :: XType -> Set TyVar
bindersOf = case _ of
  XForall b _ body -> Set.insert b (bindersOf body)
  other -> foldChildren bindersOf other

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
