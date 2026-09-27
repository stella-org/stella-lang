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
  , inheritingChild
  , abstractedChild
  , childWith
  , closedOverParts
  , joinsWithin
  , visibleUnder
  , closedOver
  , Shape(..)
  , functionShape
  , forallShape
  , constrainedShape
  , instantiatedAt
  ) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.Catalog (lookupEntry)
import Stella.Compiler.Elaborate.Diagnostic (BuildError(..), Defect(..))
import Stella.Compiler.Elaborate.Context (XContext)
import Stella.Compiler.Elaborate.Elab (Elab, Release(..), askEnv, break, currentMetas, freshBinderName, freshScopeId, issue, postpone, release, require, resolveExpr, resolveType)
import Stella.Compiler.Elaborate.Handle (ExprObject, Handle, HandleObject(..), JoinSignature, ScopeId, ScopeObject, TypeObject)
import Stella.Compiler.Elaborate.Kind (XKind(..))
import Stella.Compiler.Elaborate.Kinding (KindEvidence, KindingScope, checkConstraint, checkKind, quantifiable, settledIn, synthKind)
import Stella.Compiler.Elaborate.Pending (Site)
import Stella.Compiler.Elaborate.Term (XExpr, freeVarsOf)
import Stella.Compiler.Elaborate.Type (MetaVar, XConstraint(..), XRowEntry(..), XType(..), freeRigids, metasOf)
import Stella.Compiler.Elaborate.Unify (MetaBinding(..), MetaContext, lookupMeta, substitute, substituteKind)
import Stella.Compiler.Elaborate.View (ConstraintView(..), KindView(..))
import Stella.Compiler.TypedCore (Ident, JoinName, KindVar, Qualified, RowElemKind(..), TyVar(..))
import Stella.Compiler.TypedCore.Prim (functionTy)
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
-- |
-- | **Every join point the term jumps to must be one the scope may jump to.** A
-- | term built outside an abstraction is visible inside it, and one that jumps
-- | to a join point outside would carry the jump under the abstraction.
usableTermIn :: ScopeObject -> Handle -> Elab ExprObject
usableTermIn scope handle = do
  object <- resolveExpr handle
  case object.builtIn of
    Just id | id == scope.id || Set.member id scope.ancestors ->
      if joinsWithin scope object.term then pure object
      else rejected (JoinOutOfScope handle)
    _ -> rejected (ScopeViolation handle)

-- | Whether every join point a term jumps to free is one the scope may jump to.
joinsWithin :: ScopeObject -> XExpr Unit -> P.Boolean
joinsWithin scope term = Set.subset (freeVarsOf term).joins (Map.keys scope.joins)

-- | Issue a term built in the scope, claimed at the type given, zonked.
-- |
-- | The claim is kinded at `Type` under the scope, and every join point the term
-- | jumps to must be one the scope may jump to. A builder's claim is the host's
-- | own or taken from a type the scope may use, and what it is given is checked
-- | against the scope, so a term failing either is a defect of the host.
issueTerm :: ScopeObject -> XExpr Unit -> XType -> Elab Handle
issueTerm scope term claimed = do
  env <- askEnv
  metas <- currentMetas
  let
    zonked = substitute metas claimed
  unless (joinsWithin scope term)
    (break (JoinsOutOfScope (Set.difference (freeVarsOf term).joins (Map.keys scope.joins))))
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

-- | A child of the scope for a binder's body, with the context given, whose
-- | terms may jump to the join points the scope's may: the body of a `let`, a
-- | `letrec`, a branch, a `letjoin`, and a type's binder. Drawn from the
-- | attempt's supply of scopes.
inheritingChild :: ScopeObject -> XContext -> Elab ScopeObject
inheritingChild scope context = childWith scope context scope.joins

-- | A child of the scope for the body of an abstraction — `λ`, `Λ(a)`,
-- | `Λ(_ : C)` — which jumps to no join point outside it: a join point is a
-- | continuation of the evaluation the abstraction delays, and a body run
-- | later has no such continuation to jump to.
abstractedChild :: ScopeObject -> XContext -> Elab ScopeObject
abstractedChild scope context = childWith scope context Map.empty

-- | A child of the scope with the context and the join points given.
childWith :: ScopeObject -> XContext -> Map JoinName JoinSignature -> Elab ScopeObject
childWith scope context joins = do
  id <- freshScopeId
  pure { id, ancestors: Set.insert scope.id scope.ancestors, context, joins }

-- | Whether what was built in the scope named is visible under a binder closed
-- | in the scope given: built in the binder's own body scope, in the scope, or
-- | in one of its ancestors.
visibleUnder :: forall r. ScopeObject -> { body :: ScopeId | r } -> Maybe ScopeId -> P.Boolean
visibleUnder scope binder = case _ of
  Just id -> id == binder.body || id == scope.id || Set.member id scope.ancestors
  Nothing -> false

-- | What closing a binder checks, whatever its sort: that it was opened in this
-- | scope, that its body is visible under it, and that it is still open with
-- | nothing opened inside its body still open, which closing it ends.
closedOver
  :: forall r
   . ScopeObject
  -> Handle
  -> { parent :: ScopeId, body :: ScopeId | r }
  -> Maybe ScopeId
  -> Handle
  -> Elab Unit
closedOver scope binderHandle binder builtIn bodyHandle =
  closedOverParts scope binderHandle binder [ { within: binder.body, builtIn, handle: bodyHandle } ]

-- | `closedOver`, for a binder whose body is in several parts, each visible
-- | under the scope it names and not under another's: a part built in its own
-- | scope, in the scope the binder is closed in, or in one of that scope's
-- | ancestors.
closedOverParts
  :: forall r
   . ScopeObject
  -> Handle
  -> { parent :: ScopeId, body :: ScopeId | r }
  -> P.Array { within :: ScopeId, builtIn :: Maybe ScopeId, handle :: Handle }
  -> Elab Unit
closedOverParts scope binderHandle binder parts = do
  when (binder.parent /= scope.id) (rejected (BinderMisuse binderHandle))
  for_ parts \part ->
    unless (visibleUnder scope { body: part.within } part.builtIn) (rejected (ScopeViolation part.handle))
  release binder.body >>= case _ of
    Released -> pure unit
    NotOpen -> rejected (BinderClosed binderHandle)
    EnclosesOpen _ -> rejected (EnclosesOpenBinder binderHandle)

-- | What a type read for a shape comes to.
data Shape a
  -- | The shape is there.
  = Seen a
  -- | It is not there yet, and these metavariables are what decide whether it
  -- | will be.
  | Blocked (Set MetaVar)
  -- | It is not there, and no solution can put it there.
  | Otherwise

-- | A function type's three parts, read off the zonked type.
-- |
-- | A function type is an application spine headed by `Function`. **A spine
-- | headed by an unsolved metavariable may become one only where the two are
-- | compatible with `Function` partially applied**: at most three arguments, and
-- | the metavariable's kind that of `Function` with the arguments the spine does
-- | not supply already given — `?f : Type -> Type` applied to one argument can
-- | be solved to `Function τ ρ`, and `?f : Row Type -> Type` applied to one can
-- | be solved to nothing that makes it an arrow. Only a compatible head is waited
-- | on; waiting on another would register a job under a metavariable whose
-- | solution could never give it the shape. Once the head is `Function`, what
-- | its arguments hold is not waited on.
functionShape :: MetaContext -> XType -> Shape { argument :: XType, row :: XType, result :: XType }
functionShape metas ty = case spine (substitute metas ty) [] of
  { head: XCon name [], args: [ argument, row, result ] }
    | name == functionTy -> Seen { argument, row, result }
  { head: XMeta m, args } -> case lookupMeta metas m of
    Just (Unsolved info)
      | Array.length args <= 3
      , compatible (substituteKind metas info.kind) (dropArrows (3 - Array.length args) functionKind) ->
          Blocked (Set.singleton m)
    _ -> Otherwise
  _ -> Otherwise
  where
  -- `Function : Type -> Row Effect -> Type -> Type`, as `Prim` declares it.
  functionKind = XKFun XKType (XKFun (XKRow RowEffect) (XKFun XKType XKType))

  dropArrows i k = case i, k of
    0, _ -> k
    _, XKFun _ rest -> dropArrows (i - 1) rest
    _, _ -> k

  -- A kind metavariable left in the head's kind rules nothing out.
  compatible actual expected = case actual, expected of
    XKMeta _, _ -> true
    XKFun a1 r1, XKFun a2 r2 -> compatible a1 a2 && compatible r1 r2
    _, _ -> actual == expected

  spine t args = case t of
    XApp f a -> spine f (Array.cons a args)
    head -> { head, args }

-- | A `forall`'s binder, kind, and body, read off the zonked type. Only an
-- | unsolved metavariable at the root is waited on.
forallShape :: MetaContext -> XType -> Shape { binder :: TyVar, kind :: XKind, body :: XType }
forallShape metas ty = case substitute metas ty of
  XForall binder kind body -> Seen { binder, kind, body }
  XMeta m -> blockedOn metas m
  _ -> Otherwise

-- | A constrained type's constraint and body, read off the zonked type. Only an
-- | unsolved metavariable at the root is waited on.
constrainedShape :: MetaContext -> XType -> Shape { constraint :: XConstraint, body :: XType }
constrainedShape metas ty = case substitute metas ty of
  XConstrained constraint body -> Seen { constraint, body }
  XMeta m -> blockedOn metas m
  _ -> Otherwise

-- A zonked type's metavariable is unsolved; one `Ψ` does not hold is no
-- shape at all.
blockedOn :: forall a. MetaContext -> MetaVar -> Shape a
blockedOn metas m = case lookupMeta metas m of
  Just (Unsolved _) -> Blocked (Set.singleton m)
  Just (Assigned _) -> Otherwise
  Nothing -> Otherwise

-- | `body[a := argument]` in the scope, for `forall (a : kind). body` and an
-- | argument the scope may use, zonked.
-- |
-- | The argument must stand at `kind`. The substitution is capture-avoiding: a
-- | binder of the body that the argument mentions free is renamed, to a name
-- | drawn from the host's supply of fresh binder names that neither side, nor
-- | the scope, mentions.
-- |
-- | **An unsolved metavariable that could come to mention a variable the
-- | substitution treats specially postpones the instantiation until it is
-- | solved**: one in the body whose scope holds the binder or a binder being
-- | renamed, and one in the argument whose scope holds a binder of the body. A
-- | substitution stops at an unsolved metavariable, so the first's later solution
-- | could mention a binder the result no longer has, and the second's could be
-- | captured by a binder that was not renamed.
instantiatedAt :: ScopeObject -> TyVar -> XKind -> XType -> XType -> Elab XType
instantiatedAt scope a kind body argument = do
  env <- askEnv
  metas <- currentMetas
  case checkKind env.session.kinding (kindingScopeOf scope) metas kind argument of
    Left fault -> rejected (IllKinded fault)
    Right _ -> pure unit
  let
    binders = bindersOf body
    capturing = Set.intersection binders (freeRigids argument)
    reaching =
      Set.filter (mayMention metas (Set.insert a capturing)) (metasOf body)
        <> Set.filter (mayMention metas binders) (metasOf argument)
  unless (Set.isEmpty reaching) (postpone reaching)
  let
    -- A new name must capture nothing the renamed binder's body, the argument,
    -- or the scope mentions.
    taken = Set.unions [ Map.keys scope.context.tyVars, binders, freeRigids body, freeRigids argument, Set.singleton a ]
  renames <- traverse (renamed taken) (Set.toUnfoldable capturing :: P.Array TyVar)
  pure (substituteTyVar a argument (Map.fromFoldable renames) body)
  where
  renamed taken b@(TyVar hint) = Tuple b <$> freshBinderName taken hint

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
