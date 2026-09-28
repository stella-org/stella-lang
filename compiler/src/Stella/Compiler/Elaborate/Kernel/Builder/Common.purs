-- | What the kernel's requests over types share: resolving a build scope's
-- | types, kinding what is built in one, and the site an obligation raised in
-- | one carries.
-- |
-- | A request takes a build scope as a handle the host issued, and everything
-- | here reads the scope and nothing the caller states: the types it may use are
-- | the ones built in it or in its ancestors, what is built in it is kinded under
-- | what it binds, and an obligation raised in it is decided against its context.
module Stella.Compiler.Elaborate.Kernel.Builder.Common
  ( usableIn
  , usableTermIn
  , regionFits
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
  , treeChild
  , caseRoot
  , treeScopeOf
  , usableOccurrenceIn
  , usableTreeIn
  , treeOfCase
  , issueTree
  , rowAt
  , valueType
  , appliedShape
  , recordShape
  , variantShape
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
  , substitutedAt
  , instantiateConstructorFields
  ) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.Environment.Catalog (lookupEntry)
import Stella.Compiler.Elaborate.Vocabulary.Diagnostic (BuildError(..), Defect(..))
import Stella.Compiler.Elaborate.Environment.Constructors (ConstructorShape)
import Stella.Compiler.Elaborate.CorePlus.Context (XContext)
import Stella.Compiler.Elaborate.Kernel.Elab (Elab, Release(..), askEnv, break, currentMetas, freshBinderName, freshScopeId, issue, postpone, release, require, resolveExpr, resolveOccurrence, resolveScope, resolveTree, resolveType)
import Stella.Compiler.Elaborate.Vocabulary.Handle (ExprObject, Handle, HandleObject(..), JoinSignature, OccurrenceObject, ScopeId, ScopeObject, TreeObject, TypeObject)
import Stella.Compiler.Elaborate.CorePlus.Kind (XKind(..))
import Stella.Compiler.Elaborate.Mechanism.Kinding (KindEvidence(..), KindingScope, checkConstraint, checkKind, quantifiable, settledIn, synthKind, wellFormedKey)
import Stella.Compiler.Elaborate.CorePlus.Row (rebuild, xnf)
import Stella.Compiler.Elaborate.Mechanism.Pending (Site)
import Stella.Compiler.Elaborate.CorePlus.Term (Region, XDecisionTree, XExpr, freeVarsOf, termMetasUnderRegions)
import Stella.Compiler.Elaborate.Mechanism.TermMeta (zonkExpr)
import Stella.Compiler.Elaborate.CorePlus.Type (MetaVar, XConstraint(..), XRowEntry(..), XType(..), freeRigids, metasOf)
import Stella.Compiler.Elaborate.Mechanism.Unify (MetaBinding(..), MetaContext, TermBinding(..), lookupMeta, lookupTermMeta, substitute, substituteKind)
import Stella.Compiler.Elaborate.Vocabulary.View (ConstraintView(..), KindView(..))
import Stella.Compiler.TypedCore (Ident, JoinName, KindVar, Qualified, RowElemKind(..), RowKey, TyName, TyVar(..))
import Stella.Compiler.TypedCore.Prim (functionTy, recordTy, variantTy)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldMap, for_)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), isJust)
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
-- |
-- | **A term that depends on its region must stand in the one it was built
-- | in**, by `regionFits`.
usableTermIn :: ScopeObject -> Handle -> Elab ExprObject
usableTermIn scope handle = do
  object <- resolveExpr handle
  case object.builtIn of
    Just id | id == scope.id || Set.member id scope.ancestors ->
      unless (joinsWithin scope object.term) (rejected (JoinOutOfScope handle))
    _ -> rejected (ScopeViolation handle)
  regionFits scope.region handle object
  pure object

-- | Refuse a term that depends on the region it was built in where another
-- | region stands.
-- |
-- | **A cell is named by its key alone and means the innermost region's**, so a
-- | `readCell n` built in one handler's clause and placed in a clause of another
-- | handler holding an `n` would read the other's cell. A term depends on its
-- | region where it reads or writes a cell outside every handler owning cells
-- | it binds, or holds, outside those handlers' clauses, an unsolved term
-- | metavariable created in a region — a goal asked for there, which may be
-- | solved by one that does. A goal asked for in a clause of a handler inside
-- | the term is filled in that handler's region, which the term binds itself. Such a term stands only in the
-- | region it was built in. A term depending on none — pure, or one whose cells
-- | are all a handler's own inside it — stands anywhere its scope allows.
regionFits :: Maybe Region -> Handle -> ExprObject -> Elab Unit
regionFits region handle object = do
  metas <- currentMetas
  let
    term = zonkExpr metas object.term
    -- A metavariable is filled in the region it was created in, which the term
    -- binds itself where that is a handler's inside it.
    freeIn occurrence = case lookupTermMeta metas occurrence.meta of
      Just (TermUnsolved info) -> case info.scope.region of
        Just r -> not (Set.member r.var occurrence.bound)
        Nothing -> false
      _ -> false
    depends =
      not (Set.isEmpty (freeVarsOf term).cells)
        || Array.any freeIn (termMetasUnderRegions term)
  when (depends && map _.var object.region /= map _.var region) (rejected (RegionMismatch handle))

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
      issue (ExprObject { term, claimed: zonked, scope: kindingScopeOf scope, builtIn: Just scope.id, region: scope.region })

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
-- | terms may jump to the join points the scope's may, and which stands in no
-- | decision tree: the body of a `let`, a `letrec`, a `letjoin`, and a type's
-- | binder. Drawn from the
-- | attempt's supply of scopes.
inheritingChild :: ScopeObject -> XContext -> Elab ScopeObject
inheritingChild scope context = childWith scope context scope.joins Nothing

-- | A child of the scope for the body of an abstraction — `λ`, `Λ(a)`,
-- | `Λ(_ : C)` — which jumps to no join point outside it: a join point is a
-- | continuation of the evaluation the abstraction delays, and a body run
-- | later has no such continuation to jump to.
abstractedChild :: ScopeObject -> XContext -> Elab ScopeObject
abstractedChild scope context = childWith scope context Map.empty Nothing

-- | A child of the scope within the decision tree the scope stands in, with the
-- | context given: the body of a `bind`, a switch, or one of its branches.
treeChild :: ScopeObject -> XContext -> Elab ScopeObject
treeChild scope context = childWith scope context scope.joins scope.tree

-- | The scope a `case`'s decision tree is built in, a child of the scope: it
-- | names the `case`, and inherits its join points.
caseRoot :: ScopeObject -> Elab ScopeObject
caseRoot scope = do
  id <- freshScopeId
  pure { id, ancestors: Set.insert scope.id scope.ancestors, context: scope.context, joins: scope.joins, tree: Just id, region: scope.region }

-- | A child of the scope with the context, the join points, and the decision tree
-- | given, standing in the scope's region of cells: a region is lexical, and
-- | only an operation clause of a handler owning one opens another.
childWith :: ScopeObject -> XContext -> Map JoinName JoinSignature -> Maybe ScopeId -> Elab ScopeObject
childWith scope context joins tree = do
  id <- freshScopeId
  pure { id, ancestors: Set.insert scope.id scope.ancestors, context, joins, tree, region: scope.region }

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

-- | A type constructor applied to all its parameters, read off the zonked type:
-- | the kinds it is written at and the arguments it is applied to.
-- |
-- | **A spine headed by an unsolved metavariable may become one only where the
-- | two are compatible with the constructor partially applied**: no more
-- | arguments than it has parameters, and the metavariable's kind that of the
-- | constructor with the arguments the spine does not supply already given —
-- | `?f : Type -> Type` applied to one argument can be solved to
-- | `Function τ ρ`, and `?f : Row Type -> Type` applied to one can be solved to
-- | nothing that makes an arrow. Only a compatible head is waited on; waiting on
-- | another would register a job under a metavariable whose solution could never
-- | give it the shape. Once the head is the constructor, what its arguments hold
-- | is not waited on.
-- |
-- | The parameters' kinds are given. A kind variable among them stands for one
-- | kind throughout, so the head's kind must give it the same one wherever it
-- | occurs; a kind metavariable left in the head's kind rules nothing out.
appliedShape
  :: MetaContext
  -> Qualified TyName
  -> P.Array XKind
  -> XType
  -> Shape { kinds :: P.Array XKind, args :: P.Array XType }
appliedShape metas name params ty = case spine (substitute metas ty) [] of
  { head: XCon n kinds, args }
    | n == name && Array.length args == Array.length params -> Seen { kinds, args }
  { head: XMeta m, args } -> case lookupMeta metas m of
    Just (Unsolved info)
      | Array.length args <= Array.length params
      , isJust (match Map.empty (substituteKind metas info.kind) (arrows (Array.drop (Array.length params - Array.length args) params))) ->
          Blocked (Set.singleton m)
    _ -> Otherwise
  _ -> Otherwise
  where
  arrows = Array.foldr XKFun XKType

  -- The head's kind against the one expected, each kind variable of the
  -- expected bound to the kind it first meets and held to it after.
  match bound actual expected = case actual, expected of
    XKMeta _, _ -> Just bound
    _, XKVar v -> case Map.lookup v bound of
      Nothing -> Just (Map.insert v actual bound)
      Just earlier -> if agree earlier actual then Just bound else Nothing
    XKFun a1 r1, XKFun a2 r2 -> match bound a1 a2 >>= \b -> match b r1 r2
    _, _ -> if actual == expected then Just bound else Nothing

  -- Two kinds a kind metavariable in either may still make one.
  agree k1 k2 = case k1, k2 of
    XKMeta _, _ -> true
    _, XKMeta _ -> true
    XKFun a1 r1, XKFun a2 r2 -> agree a1 a2 && agree r1 r2
    _, _ -> k1 == k2

  spine t args = case t of
    XApp f a -> spine f (Array.cons a args)
    head -> { head, args }

-- | A function type's three parts, read off the zonked type: `Function`, as
-- | `Prim` declares it, at `Type -> Row Effect -> Type -> Type`.
functionShape :: MetaContext -> XType -> Shape { argument :: XType, row :: XType, result :: XType }
functionShape metas ty =
  case appliedShape metas functionTy [ XKType, XKRow RowEffect, XKType ] ty of
    Seen { args: [ argument, row, result ] } -> Seen { argument, row, result }
    Seen _ -> Otherwise
    Blocked ms -> Blocked ms
    Otherwise -> Otherwise

-- | A record's row, read off the zonked type.
recordShape :: MetaContext -> XType -> Shape XType
recordShape metas = rowOf <<< appliedShape metas recordTy [ XKRow RowType ]

-- | A variant's row, read off the zonked type.
variantShape :: MetaContext -> XType -> Shape XType
variantShape metas = rowOf <<< appliedShape metas variantTy [ XKRow RowType ]

rowOf :: Shape { kinds :: P.Array XKind, args :: P.Array XType } -> Shape XType
rowOf = case _ of
  Seen { args: [ row ] } -> Seen row
  Seen _ -> Otherwise
  Blocked ms -> Blocked ms
  Otherwise -> Otherwise

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
-- | argument the scope may use, zonked: the argument must stand at `kind`, and
-- | the substitution is the one `substitutedAt` makes.
instantiatedAt :: ScopeObject -> TyVar -> XKind -> XType -> XType -> Elab XType
instantiatedAt scope a kind body argument = do
  env <- askEnv
  metas <- currentMetas
  case checkKind env.session.kinding (kindingScopeOf scope) metas kind argument of
    Left fault -> rejected (IllKinded fault)
    Right _ -> pure unit
  substitutedAt scope (Map.singleton a argument) body

-- | `body[ā := σ̄]` in the scope, simultaneously, for arguments the scope may
-- | use, zonked.
-- |
-- | The substitution is capture-avoiding: a binder of the body that an argument
-- | mentions free is renamed, to a name drawn from the host's supply of fresh
-- | binder names that neither side, nor the scope, mentions. Below a binder named
-- | like a substituted variable, that variable is not substituted.
-- |
-- | **An unsolved metavariable that could come to mention a variable the
-- | substitution treats specially postpones the substitution until it is
-- | solved**: one in the body whose scope holds a substituted variable or a
-- | binder being renamed, and one in an argument whose scope holds a binder of
-- | the body. A substitution stops at an unsolved metavariable, so the first's
-- | later solution could mention a variable the result no longer has, and the
-- | second's could be captured by a binder that was not renamed.
substitutedAt :: ScopeObject -> Map TyVar XType -> XType -> Elab XType
substitutedAt scope substitution body = do
  metas <- currentMetas
  let
    variables = Map.keys substitution
    arguments = Array.fromFoldable (Map.values substitution)
    argumentsFree = foldMap freeRigids arguments
    binders = bindersOf body
    capturing = Set.intersection binders argumentsFree
    reaching =
      Set.filter (mayMention metas (Set.union variables capturing)) (metasOf body)
        <> Set.filter (mayMention metas binders) (foldMap metasOf arguments)
  unless (Set.isEmpty reaching) (postpone reaching)
  let
    -- A new name must capture nothing the renamed binder's body, an argument,
    -- or the scope mentions.
    taken = Set.unions [ Map.keys scope.context.tyVars, binders, freeRigids body, argumentsFree, variables ]
  renames <- traverse (renamed taken) (Set.toUnfoldable capturing :: P.Array TyVar)
  pure (substituteTyVars substitution (Map.fromFoldable renames) body)
  where
  renamed taken b@(TyVar hint) = Tuple b <$> freshBinderName taken hint

-- | A constructor's fields where its data type stands at the kinds and the
-- | arguments given: the kind variables first, then the type parameters, the
-- | order the Core type checker instantiates them in. Every field reached by an
-- | occurrence is instantiated here.
instantiateConstructorFields :: ScopeObject -> ConstructorShape -> P.Array XKind -> P.Array XType -> Elab (P.Array XType)
instantiateConstructorFields scope shape kinds args =
  traverse
    ( substitutedAt scope (Map.fromFoldable (Array.zip (map _.name shape.params) args))
        <<< substituteKindVars (Map.fromFoldable (Array.zip shape.kindVars kinds))
    )
    shape.fields

-- | Whether an unsolved metavariable's scope holds any of the variables given.
mayMention :: MetaContext -> Set TyVar -> MetaVar -> P.Boolean
mayMention metas vars m = case lookupMeta metas m of
  Just (Unsolved info) -> not (Set.isEmpty (Set.intersection info.scope.types vars))
  _ -> false

-- | `τ[ā := σ̄]`, simultaneously, with each binder of `τ` the map of renames names
-- | renamed to the fresh name it gives.
-- |
-- | Renaming by name is sound because every new name is fresh: two binders
-- | sharing a name get one new name, and the inner still shadows the outer.
-- | **A binder is handled as two things at once.** Below it, the variable it
-- | shadows is no longer substituted; and where it would capture a variable of
-- | another argument that is still substituted below it, it is renamed. A binder
-- | named like one substituted variable can capture what another is replaced
-- | by — `forall b. a` with `a := b, b := Int` — so neither may wait for the
-- | other.
substituteTyVars :: Map TyVar XType -> Map TyVar TyVar -> XType -> XType
substituteTyVars substitution renames = go substitution Map.empty
  where
  go active inScope = case _ of
    XVar v -> case Map.lookup v active of
      Just argument -> argument
      Nothing -> case Map.lookup v inScope of
        Just v' -> XVar v'
        Nothing -> XVar v
    XForall b k body ->
      let
        below = Map.delete b active
      in
        case Map.lookup b renames of
          Just b' -> XForall b' k (go below (Map.insert b b' inScope) body)
          Nothing -> XForall b k (go below (Map.delete b inScope) body)
    other -> mapChildren (go active inScope) other

-- | The type variables a `forall` inside the type binds.
bindersOf :: XType -> Set TyVar
bindersOf = case _ of
  XForall b _ body -> Set.insert b (bindersOf body)
  other -> foldChildren bindersOf other

-- | A scope a tree node is built in: one standing in a decision tree, and the
-- | `case` whose tree it is.
treeScopeOf :: Handle -> Elab { scope :: ScopeObject, caseId :: ScopeId }
treeScopeOf scopeHandle = do
  scope <- resolveScope scopeHandle
  case scope.tree of
    Just caseId -> pure { scope, caseId }
    Nothing -> rejected (NotATreeScope scopeHandle)

-- | An occurrence the scope may read: established by a branch the scope stands
-- | under, of the `case` whose tree the scope stands in. An occurrence of an
-- | enclosing `case` is not one: its path is read from another `case`'s
-- | scrutinees.
usableOccurrenceIn :: ScopeObject -> Handle -> Elab OccurrenceObject
usableOccurrenceIn scope handle = do
  occurrence <- resolveOccurrence handle
  case occurrence.builtIn of
    Just id | id == scope.id || Set.member id scope.ancestors -> pure unit
    _ -> rejected (ScopeViolation handle)
  unless (scope.tree == Just occurrence.case) (rejected (OccurrenceOfAnotherCase handle))
  pure occurrence

-- | A tree the scope may use: one of the `case` named, built in the scope or in
-- | one of its ancestors.
usableTreeIn :: ScopeObject -> ScopeId -> Handle -> Elab TreeObject
usableTreeIn scope caseId handle = do
  tree <- treeOfCase caseId handle
  case tree.builtIn of
    Just id | id == scope.id || Set.member id scope.ancestors -> pure tree
    _ -> rejected (ScopeViolation handle)

-- | A tree of the `case` named. A tree of another `case` — an enclosing one's,
-- | visible from an inner `case` built under it — reads its occurrences from
-- | other scrutinees.
treeOfCase :: ScopeId -> Handle -> Elab TreeObject
treeOfCase caseId handle = do
  tree <- resolveTree handle
  unless (tree.case == caseId) (rejected (TreeOfAnotherCase handle))
  pure tree

-- | Issue a tree of the `case` named, built in the scope, with the type its first
-- | leaf is claimed at, zonked.
issueTree :: ScopeObject -> ScopeId -> XDecisionTree Unit -> Maybe XType -> Elab Handle
issueTree scope caseId tree inferred = do
  metas <- currentMetas
  issue (TreeObject { tree, inferred: map (substitute metas) inferred, case: caseId, builtIn: Just scope.id })

-- | A row taken apart at a key: the type it carries there, and the row with
-- | the key taken out.
-- |
-- | **Every term and occurrence that reads a row at a key reads it here**, so
-- | none of them decides otherwise: known with a type as its payload, it is
-- | there; known with another payload, or absent from a row whose tails are all
-- | rigid, it is a misuse — a rigid tail says nothing of what it carries; and
-- | absent from a row with a flexible tail, the tails are waited on, any of them
-- | being what could carry it. A row with no normal form is the error given.
-- |
-- | **The key is judged well-formed for a `Row Type` first.** No solution puts an
-- | ill-formed key in a row, so waiting on a tail for one would wait forever.
rowAt :: BuildError -> Handle -> XType -> RowKey -> Elab { payload :: XType, rest :: XType }
rowAt notARow handle row key = do
  env <- askEnv
  case wellFormedKey env.session.kinding key (Just RowType) of
    Left fault -> rejected (IllKinded fault)
    Right _ -> pure unit
  metas <- currentMetas
  case xnf (substitute metas row) of
    Left _ -> rejected notARow
    Right n -> case Map.lookup key n.known of
      Just (XRowTypeEntry _ ty) -> pure { payload: ty, rest: rebuild (n { known = Map.delete key n.known }) }
      Just _ -> rejected (PayloadNotAType handle key)
      Nothing
        | not (Set.isEmpty n.flexible) -> postpone n.flexible
        | otherwise -> rejected (FieldAbsent handle key)

-- | A type a value may be bound or written at: one the scope may use, standing
-- | at `Type`.
valueType :: ScopeObject -> Handle -> Elab XType
valueType scope handle = do
  ty <- usableIn scope handle
  case ty.kind of
    ExactKind XKType -> pure ty.type
    _ -> rejected (NotAType handle)
