-- | Generalizing a binding group: a step of the driver, taken outside every
-- | attempt once the group's bodies are elaborated
-- | ([Elaboration](../../../../../docs/technical-references/02-Surface-Language/01-Elaboration.md#generalization)).
-- |
-- | **It runs in two parts, closing between them.** Preparing applies the value
-- | restriction, reads each member's provisional quantifiers, and settles the
-- | group's synthesis goals against them; finalizing confirms that nothing
-- | which cannot cross a generalization is left, and decides each member's
-- | kind and type quantifiers. What it decides is a plan: no metavariable is
-- | made rigid here.
-- |
-- | **The candidates of a group are the unsolved metavariables at its level.**
-- | What the value restriction keeps monomorphic is lowered below it, and is
-- | recorded by the draft the preparation returns rather than in `Ψ`: a group
-- | declining to quantify a metavariable says nothing of it once the group is
-- | done. Whether such a metavariable is solved is read off its zonked
-- | representative.
module Stella.Compiler.Elaborate.Driver.Generalize
  ( Member
  , Restricted
  , GeneralizationDraft
  , MemberPlan
  , GeneralizationPlan
  , Hindrance(..)
  , Preparation(..)
  , Finalization(..)
  , prepareGeneralization
  , finalizeGeneralization
  , FinalizedMember
  , FinalizedGroup
  , Commitment(..)
  , commitGeneralization
  ) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldl, foldr)
import Data.Generic.Rep (class Generic)
import Data.Map as Map
import Data.Maybe (Maybe(..), maybe)
import Data.Set (Set)
import Data.Set as Set
import Data.Show.Generic (genericShow)
import Data.String.CodeUnits as CodeUnits
import Data.Tuple (Tuple(..))
import Stella.Compiler.Elaborate.CorePlus.Context (Origin(..), XContext)
import Stella.Compiler.Elaborate.CorePlus.Kind (KindMetaVar, XKind(..), kindMetasOf, kindVarsOf)
import Stella.Compiler.Elaborate.CorePlus.Term (FitId, RecRefId, TermMetaVar, XExpr(..), freeVarsOf, metasOfTerm, typeVarsOfTerm, typeVarsOfType, typesOfTerm, xExprAnnotation)
import Stella.Compiler.Elaborate.CorePlus.Type (MetaVar, XConstraint(..), XType(..), freeKindVars, freeRigids, kindMetasOfType, metaOccurrences, metasOf)
import Stella.Compiler.Elaborate.Driver.Loop (Attempter, RunResult(..), runAttempting)
import Stella.Compiler.Elaborate.Kernel.Elab (SolverState)
import Stella.Compiler.Elaborate.Mechanism.Fit (FitState(..))
import Stella.Compiler.Elaborate.Mechanism.Obligation (Basis(..), Breach, ObligationId, ResidualAtom(..), atomConstraint, release, residualAtoms)
import Stella.Compiler.Elaborate.Mechanism.Pending (Job(..), PendingId, goalOf)
import Stella.Compiler.Elaborate.Mechanism.Scheduler (requeue)
import Stella.Compiler.Elaborate.Mechanism.TermMeta (zonkExpr)
import Stella.Compiler.Elaborate.Mechanism.Unify (KindMetaBinding(..), KindRequirement(..), MetaBinding(..), MetaContext, TermBinding(..), lookupMeta, lowerLevels, regionScopeOf, substitute, substituteKind)
import Stella.Compiler.Elaborate.Vocabulary.Diagnostic (Defect(..), Warning)
import Stella.Compiler.TypedCore.Name (Ident, KindVar(..), Qualified, TyVar(..))

-- | A member of the group: its key, the name it is declared by, the type it was
-- | elaborated at, its body, whether that body is a value form, which the
-- | caller judges of the zonked term once every fit of it is decided, and
-- | whether a signature writes its scheme, in part: such a member is
-- | restricted by nothing, and gains no quantifier and no constraint.
type Member k a =
  { key :: k
  , name :: Qualified Ident
  , type :: XType
  , body :: XExpr a
  , valueForm :: P.Boolean
  , written :: P.Boolean
  }

-- | What a member's generalization does not quantify: the metavariables its
-- | type and body reached where it is no value form, or that an equation still
-- | waiting touches, as they were recorded.
type Restricted k = { key :: k, types :: Set MetaVar, kinds :: Set KindMetaVar }

-- | What preparing a group's generalization decided: the group's level, each
-- | member's provisional quantifiers, and what is restricted.
type GeneralizationDraft k =
  { level :: P.Int
  , provisional :: P.Array { key :: k, quantifiers :: P.Array MetaVar }
  , restricted :: P.Array (Restricted k)
  }

-- | A member's quantifiers: the kind variables its scheme binds, each in place
-- | of a kind metavariable, and then its type variables, each in place of a
-- | type metavariable and at the kind that metavariable stands at.
type MemberPlan k =
  { key :: k
  , kindVars :: P.Array { meta :: KindMetaVar, name :: KindVar }
  , quantifiers :: P.Array { meta :: MetaVar, name :: TyVar, kind :: XKind }
  }

type GeneralizationPlan k = { level :: P.Int, members :: P.Array (MemberPlan k) }

-- | What keeps a member from being generalized, each the member's.
data Hindrance k
  -- | A synthesis goal whose type touches a provisional quantifier, where it
  -- | was created: a signature is asked for.
  = GoalTouchesQuantifier k Origin PendingId
  -- | A synthesis goal still waiting once attempted again.
  | SynthesisUndecided k Origin PendingId
  -- | A restricted metavariable nothing solved: a signature is asked for.
  | RestrictedUnsolved k
  -- | Candidates the body alone reaches, which no caller could determine.
  | AmbiguousCandidates k (P.Array MetaVar)
  -- | Kind candidates the body alone reaches, directly or through the types it
  -- | holds.
  | AmbiguousKindCandidates k (P.Array KindMetaVar)
  -- | A kind candidate required to produce `Type`, which no kind variable is.
  | KindNotQuantifiable k KindMetaVar
  -- | A fit still undecided, where it was placed.
  | FitLeft k Origin FitId
  -- | A checking boundary's job still pending, where the boundary stands.
  | BoundaryLeft k Origin PendingId
  -- | A term metavariable the body holds unsolved.
  | TermMetaLeft k TermMetaVar
  -- | An obligation that no longer holds where the group's constraints are
  -- | read off.
  | ConstraintRefused k Origin Breach
  -- | A constraint holding a metavariable the member does not quantify, where
  -- | it arose.
  | AmbiguousConstraint k Origin
  -- | A recursive reference whose arguments the referring member cannot write.
  | RecursiveArgumentAmbiguous k Origin
  -- | A constraint naming a rigid variable bound inside the member, which its
  -- | scheme would leave free, where the constraint arose.
  | ConstraintEscapes k Origin TyVar
  -- | A constraint a member whose signature writes its scheme needs and the
  -- | signature does not write, where it arose.
  | ConstraintUnwritten k Origin
  -- | An equation of a member whose signature writes its scheme still waiting,
  -- | which nothing the member's generalization restricts, where it was stated.
  | EquationLeft k Origin PendingId

-- | What preparing came to: a draft, what keeps the group from being
-- | generalized, or the loop stopping short of quiescence.
data Preparation k
  = Drafted (GeneralizationDraft k)
  | Hindered (P.Array (Hindrance k))
  | PreparationStopped RunResult

-- | What finalizing came to: a plan, or what keeps the group from being
-- | generalized.
data Finalization k
  = Planned (GeneralizationPlan k)
  | FinalizationHindered (P.Array (Hindrance k))

derive instance Eq k => Eq (Hindrance k)
derive instance Generic (Hindrance k) _
instance Show k => Show (Hindrance k) where
  show x = genericShow x

derive instance Eq k => Eq (Preparation k)
derive instance Generic (Preparation k) _
instance Show k => Show (Preparation k) where
  show x = genericShow x

derive instance Eq k => Eq (Finalization k)
derive instance Generic (Finalization k) _
instance Show k => Show (Finalization k) where
  show x = genericShow x

-- | Steps 3 to 6: the value restriction, the provisional quantifiers, and the
-- | group's synthesis goals — one touching a provisional quantifier asks for a
-- | signature, any other is attempted again, and one still waiting after the
-- | loop is undecided. What the goals attempted again warned of is given with
-- | what preparing came to.
prepareGeneralization :: forall k a. Ord k => Attempter -> (Origin -> k) -> P.Int -> P.Array (Member k a) -> SolverState -> Tuple { preparation :: Preparation k, warnings :: P.Array Warning } SolverState
prepareGeneralization attempter owner level members s0 =
  case touching of
    [] -> case report.result of
      Completed -> settled
      Blocked _ -> settled
      other -> Tuple { preparation: PreparationStopped other, warnings: report.warnings } ran
    _ -> Tuple { preparation: Hindered (map (\g -> GoalTouchesQuantifier g.key g.origin g.id) touching), warnings: [] } restrictedState
  where
  ctx0 = s0.tentative.metas
  keys = Set.fromFoldable (map _.key members)

  -- a member that is no value form keeps what it reaches monomorphic
  restricted = Array.mapMaybe
    ( \m ->
        if m.valueForm || m.written then Nothing
        else
          let
            zonked = substitute ctx0 m.type
            inBody = metasOfTerm (zonkExpr ctx0 m.body)
            types = metasOf zonked <> inBody.types
          in
            Just
              { key: m.key
              , types: Set.filter (candidate ctx0 level) types
              , kinds: Set.filter (kindCandidate ctx0 level) (kindsReached ctx0 zonked <> inBody.kinds <> kindsOfMetas ctx0 types)
              }
    )
    members
  lowered = foldl (\c r -> lowerLevels (level - 1) r.types r.kinds c) ctx0 restricted
  restrictedState = s0 { tentative { metas = lowered } }

  provisional = map (\m -> { key: m.key, quantifiers: if m.written then [] else quantifiersOf lowered level m.type }) members
  -- a goal is held to the quantifiers of the member it belongs to
  quantifiedOf key = Set.fromFoldable (Array.concatMap _.quantifiers (Array.filter (\p -> p.key == key) provisional))

  goals = Array.mapMaybe
    ( \p -> case p.job of
        JobSynthesis goal | Set.member (owner p.site.origin) keys ->
          Just { id: p.id, key: owner p.site.origin, origin: p.site.origin, type: (goalOf goal).expectedType }
        _ -> Nothing
    )
    (Array.fromFoldable (Map.values s0.tentative.scheduler.pending))
  touching = Array.filter (\g -> not (Set.isEmpty (Set.intersection (quantifiedOf g.key) (metasOf (substitute lowered g.type))))) goals

  Tuple report ran = runAttempting attempter
    (restrictedState { tentative { scheduler = foldl (\s g -> requeue g.id s) restrictedState.tentative.scheduler goals } })

  settled = case Array.filter (\g -> Map.member g.id ran.tentative.scheduler.pending) goals of
    [] -> Tuple { preparation: Drafted { level, provisional, restricted }, warnings: report.warnings } ran
    waiting -> Tuple { preparation: Hindered (map (\g -> SynthesisUndecided g.key g.origin g.id) waiting), warnings: report.warnings } ran

-- | Steps 10, 11, and 13: what cannot cross a generalization is confirmed
-- | absent, what a waiting equation touches is restricted, a restricted
-- | metavariable left unsolved asks for a signature, and each member's
-- | quantifiers are decided — its kind variables first, then its type variables,
-- | each named apart from every type variable its type and its body write.
finalizeGeneralization :: forall k a. Ord k => (Origin -> k) -> GeneralizationDraft k -> P.Array (Member k a) -> SolverState -> Tuple (Finalization k) SolverState
finalizeGeneralization owner draft members s0 =
  case crossing <> unsolved <> ambiguous <> ambiguousKinds <> unquantifiable of
    [] -> Tuple (Planned { level: draft.level, members: plans }) final
    hindrances -> Tuple (FinalizationHindered hindrances) final
  where
  level = draft.level
  ctx0 = s0.tentative.metas
  keys = Set.fromFoldable (map _.key members)

  owned :: forall r. { origin :: Origin | r } -> P.Boolean
  owned at = Set.member (owner at.origin) keys
  pendings = Array.filter (owned <<< _.site) (Array.fromFoldable (Map.values s0.tentative.scheduler.pending))

  -- what no generalization crosses, each reported by its cause
  crossing =
    Array.mapMaybe
      ( \p -> case p.job of
          JobSynthesis _ -> Just (SynthesisUndecided (owner p.site.origin) p.site.origin p.id)
          JobImplicitHandler _ -> Just (BoundaryLeft (owner p.site.origin) p.site.origin p.id)
          -- a member whose signature writes its scheme restricts nothing, so
          -- its equations cannot be left to wait beyond it
          JobUnify _ | Set.member (owner p.site.origin) writtenKeys -> Just (EquationLeft (owner p.site.origin) p.site.origin p.id)
          _ -> Nothing
      )
      pendings
      <> Array.mapMaybe
        ( \(Tuple id record) -> case record.state of
            Undecided _ | owned record.site -> Just (FitLeft (owner record.site.origin) record.site.origin id)
            _ -> Nothing
        )
        (Map.toUnfoldable ctx0.fits)
      <> Array.concatMap
        ( \m -> map (TermMetaLeft m.key)
            (Array.filter (unsolvedTerm ctx0) (Set.toUnfoldable (metasOfTerm (zonkExpr ctx0 m.body)).terms))
        )
        members

  -- what an equation still waiting may yet assign is restricted, but for a
  -- member whose signature writes its scheme
  writtenKeys = Set.fromFoldable (map _.key (Array.filter _.written members))
  touched = Array.mapMaybe
    ( \p -> case p.job of
        JobUnify goal | not (Set.member (owner p.site.origin) writtenKeys) ->
          let
            sides = [ substitute ctx0 goal.left, substitute ctx0 goal.right ] <> map (substitute ctx0 <<< XMeta) (Set.toUnfoldable p.awaiting)
          in
            Just
              { key: owner p.site.origin
              , types: Set.filter (candidate ctx0 level) (Set.unions (map metasOf sides))
              , kinds: Set.filter (kindCandidate ctx0 level) (Set.unions (map (kindsReached ctx0) sides))
              }
        _ -> Nothing
    )
    pendings
  restricted = draft.restricted <> touched
  ctx = foldl (\c r -> lowerLevels (level - 1) r.types r.kinds c) ctx0 touched
  final = s0 { tentative { metas = ctx } }

  unsolved = map (RestrictedUnsolved <<< _.key) (Array.nubByEq (\x y -> x.key == y.key) (Array.filter stillOpen restricted))
  stillOpen r =
    Array.any (\m -> not (Set.isEmpty (Set.filter (unsolvedType ctx) (metasOf (substitute ctx (XMeta m)))))) (Set.toUnfoldable r.types)
      || Array.any (\k -> not (Set.isEmpty (Set.filter (unsolvedKind ctx) (kindMetasOf (substituteKind ctx (XKMeta k)))))) (Set.toUnfoldable r.kinds)

  -- a candidate the body reaches and the type does not is ambiguous, and so
  -- is one the type of a member whose signature writes its scheme reaches,
  -- nothing quantifying it
  quantifiersOfMember m = if m.written then [] else quantifiersOf ctx level m.type
  ambiguous = Array.mapMaybe
    ( \m ->
        let
          own = Set.fromFoldable (quantifiersOfMember m)
          written = if m.written then [ m.type ] else []
          reached = Array.nub (Array.filter (\v -> candidate ctx level v && not (Set.member v own)) (Array.concatMap (metaOccurrences <<< substitute ctx) (written <> typesOfTerm (zonkExpr ctx m.body))))
        in
          if Array.null reached then Nothing else Just (AmbiguousCandidates m.key reached)
    )
    members

  -- a kind candidate the body reaches, directly or through what its types
  -- hold, and the member's type does not, is ambiguous
  ambiguousKinds = Array.mapMaybe
    ( \m ->
        let
          zonkedType = substitute ctx m.type
          -- a member whose signature writes its scheme binds no kind variable:
          -- a kind its type writes is ambiguous, and one it reaches through a
          -- type candidate is that candidate's, reported as the candidate is
          own =
            if m.written then kindsOfMetas ctx (metasOf zonkedType)
            else Set.fromFoldable (kindCandidatesOf m) <> kindsReached ctx zonkedType
          writes = if m.written then kindMetasOfType zonkedType else Set.empty
          inBody = metasOfTerm (zonkExpr ctx m.body)
          reached = Set.filter (\k -> kindCandidate ctx level k && not (Set.member k own)) (writes <> inBody.kinds <> kindsOfMetas ctx inBody.types)
        in
          if Set.isEmpty reached then Nothing else Just (AmbiguousKindCandidates m.key (Set.toUnfoldable reached))
    )
    members

  -- the kind candidates of a member: those its quantifiers stand at, then those
  -- its type's constructors are applied at
  kindCandidatesOf m =
    if m.written then []
    else
      Array.nub
        ( Array.concatMap (\v -> Set.toUnfoldable (Set.filter (kindCandidate ctx level) (kindMetasOf (substituteKind ctx (kindOf ctx v))))) (quantifiersOfMember m)
            <> Set.toUnfoldable (Set.filter (kindCandidate ctx level) (kindMetasOfType (substitute ctx m.type)))
        )
  unquantifiable = Array.concatMap
    (\m -> map (KindNotQuantifiable m.key) (Array.filter (producesType ctx) (kindCandidatesOf m)))
    members

  plans = map plan members
  plan m =
    let
      zonkedType = substitute ctx m.type
      zonkedBody = zonkExpr ctx m.body
      takenTypes = typeVarsOfType zonkedType <> typeVarsOfTerm zonkedBody
      takenKinds = freeKindVars zonkedType <> (freeVarsOf zonkedBody).kinds <> Set.unions (map (\v -> kindVarsOf (substituteKind ctx (kindOf ctx v))) (quantifiersOfMember m))
      kindNames = names (\i -> KindVar (lettered "k" i)) takenKinds (Array.length (kindCandidatesOf m))
      typeNames = names (\i -> TyVar (alphabet i)) takenTypes (Array.length (quantifiersOfMember m))
    in
      { key: m.key
      , kindVars: Array.zipWith (\meta name -> { meta, name }) (kindCandidatesOf m) kindNames
      , quantifiers: Array.zipWith (\meta name -> { meta, name, kind: substituteKind ctx (kindOf ctx meta) }) (quantifiersOfMember m) typeNames
      }

-- | A constraint with what `Ψ` solved put in.
substituteConstraint :: MetaContext -> XConstraint -> XConstraint
substituteConstraint ctx = case _ of
  XLacks key row -> XLacks key (substitute ctx row)
  XDisjoint l r -> XDisjoint (substitute ctx l) (substitute ctx r)

-- | A member's quantifiers: the candidates its type holds, where each first
-- | stands, read left to right.
quantifiersOf :: MetaContext -> P.Int -> XType -> P.Array MetaVar
quantifiersOf ctx level t = Array.nub (Array.filter (candidate ctx level) (metaOccurrences (substitute ctx t)))

-- | Whether a type metavariable is a candidate of the group at the level given:
-- | unsolved, at that level or within it.
candidate :: MetaContext -> P.Int -> MetaVar -> P.Boolean
candidate ctx level m = case lookupMeta ctx m of
  Just (Unsolved info) -> info.level >= level
  _ -> false

kindCandidate :: MetaContext -> P.Int -> KindMetaVar -> P.Boolean
kindCandidate ctx level k = case Map.lookup k ctx.kindBindings of
  Just (KindUnsolved info) -> info.level >= level
  _ -> false

-- | The kind metavariables the kinds of the metavariables given hold.
kindsOfMetas :: MetaContext -> Set MetaVar -> Set KindMetaVar
kindsOfMetas ctx ms = Set.unions (map (\m -> kindMetasOf (substituteKind ctx (kindOf ctx m))) (Set.toUnfoldable ms :: P.Array MetaVar))

-- | The kind metavariables a type reaches: those it is applied at, and those the
-- | kinds of its metavariables hold.
kindsReached :: MetaContext -> XType -> Set KindMetaVar
kindsReached ctx t = kindMetasOfType t <> Set.unions (map (\m -> kindMetasOf (substituteKind ctx (kindOf ctx m))) (Set.toUnfoldable (metasOf t) :: P.Array MetaVar))

kindOf :: MetaContext -> MetaVar -> XKind
kindOf ctx m = case lookupMeta ctx m of
  Just (Unsolved info) -> info.kind
  _ -> XKType

producesType :: MetaContext -> KindMetaVar -> P.Boolean
producesType ctx k = case Map.lookup k ctx.kindBindings of
  Just (KindUnsolved info) -> Set.member ProducesType info.requirements
  _ -> false

unsolvedType :: MetaContext -> MetaVar -> P.Boolean
unsolvedType ctx m = case lookupMeta ctx m of
  Just (Unsolved _) -> true
  _ -> false

unsolvedKind :: MetaContext -> KindMetaVar -> P.Boolean
unsolvedKind ctx k = case Map.lookup k ctx.kindBindings of
  Just (KindUnsolved _) -> true
  _ -> false

unsolvedTerm :: MetaContext -> TermMetaVar -> P.Boolean
unsolvedTerm ctx m = case Map.lookup m ctx.termBindings of
  Just (TermUnsolved _) -> true
  _ -> false

-- | As many names as asked for, in the order the supply gives them, none of
-- | those taken.
names :: forall n. Ord n => (P.Int -> n) -> Set n -> P.Int -> P.Array n
names supply taken count = go 0 []
  where
  go i acc
    | Array.length acc >= count = acc
    | Set.member (supply i) taken = go (i + 1) acc
    | otherwise = go (i + 1) (Array.snoc acc (supply i))

-- | `a` to `z`, then `a1` to `z1`, and so on.
alphabet :: P.Int -> P.String
alphabet i = lettered (CodeUnits.singleton (letter (i `mod` 26))) (i / 26)
  where
  letter n = case CodeUnits.charAt n "abcdefghijklmnopqrstuvwxyz" of
    Just c -> c
    Nothing -> 'a'

-- | The hint, then the number where it is not zero.
lettered :: P.String -> P.Int -> P.String
lettered hint i = if i == 0 then hint else hint <> show i

-- | Steps 12 and 14 to 16: each member's constraints found, its quantifiers
-- | made rigid, and its recursive references made ordinary, the group whole or
-- | not at all.
-- |
-- | **A member's constraints are its own obligations' atoms and those its
-- | recursive references raise**, each by the atom of the obligation it began
-- | as, to a least fixpoint: an atom of the member referred to is raised where
-- | the reference stands unless that site proves it, by scope or by what it
-- | assumes. Every atom must stand in the member's quantifiers and kind
-- | variables, and so must every argument a recursive reference is given.
-- |
-- | **Each member is rewritten apart**: a metavariable two members share may be
-- | quantified by both under names of their own, so nothing is assigned in
-- | `Ψ`. Once every member is rewritten, the group's metavariables are retired
-- | from `Ψ`, and its obligations, fits, and recursive references released.
commitGeneralization :: forall k a. Ord k => (Origin -> k) -> GeneralizationPlan k -> P.Array (Member k a) -> SolverState -> Tuple (Commitment k a) SolverState
commitGeneralization owner plan members s0 =
  case breached <> unwritten <> ambiguousAtoms <> escaping <> ambiguousReferences of
    []
      | danglingIn -> Tuple (GeneralizationHalted RetiredMetavariableHeld) s0
      | otherwise -> Tuple (Generalized { members: map finalized members }) retired
    hindrances -> Tuple (GeneralizationHindered hindrances) s0
  where
  ctx0 = s0.tentative.metas
  store = s0.tentative.obligations
  keys = Set.fromFoldable (map _.key members)

  owned :: forall r. { origin :: Origin | r } -> P.Boolean
  owned at = Set.member (owner at.origin) keys
  zonk = substitute ctx0
  regions = regionScopeOf ctx0
  planOf key = Array.find (\p -> p.key == key) plan.members
  memberNamed name = Array.find (\m -> m.name == name) members

  -- the atoms each required obligation of the group leaves
  decomposed = map
    (\(Tuple id entry) -> { id, entry, atoms: residualAtoms zonk regions entry.obligation })
    (Array.filter (\(Tuple _ e) -> e.obligation.basis == Required && owned e.obligation) (Map.toUnfoldable store.entries))
  breached = Array.mapMaybe
    ( \d -> case d.atoms of
        Left breach -> Just (ConstraintRefused (owner d.entry.obligation.origin) d.entry.obligation.origin breach)
        Right _ -> Nothing
    )
    decomposed
  own = Array.concatMap
    ( \d -> case d.atoms of
        -- an atom the obligation's own site proves is no constraint, each kept
        -- at the place it has among the obligation's atoms
        Right atoms -> Array.filter (\o -> not (provedAt d.entry.obligation o.atom))
          (Array.mapWithIndex (\slot atom -> { root: { obligation: d.id, slot }, atom, key: owner d.entry.obligation.origin, origin: d.entry.obligation.origin }) atoms)
        Left _ -> []
    )
    decomposed
  atomOf root = map _.atom (Array.find (\o -> o.root == root) own)

  -- the recursive references the group's bodies make
  uses = Array.mapMaybe
    ( \(Tuple id use) ->
        if owned use then map (\callee -> { id, use, key: owner use.origin, callee }) (memberNamed use.callee) else Nothing
    )
    (Map.toUnfoldable ctx0.recursiveUses)

  -- whether a site proves an atom: by scope, or by what it assumes
  provedAt :: forall r. { context :: XContext, origin :: Origin | r } -> ResidualAtom -> P.Boolean
  provedAt use atom = case residualAtoms zonk regions { constraint: atomConstraint atom, basis: Required, context: use.context, origin: use.origin } of
    Right [] -> true
    Right _ -> Array.elem atom (Array.concatMap (assumedAtoms use) use.context.assumed)
    Left _ -> false

  assumedAtoms :: forall r. { context :: XContext, origin :: Origin | r } -> XConstraint -> P.Array ResidualAtom
  assumedAtoms use c = case residualAtoms zonk regions { constraint: c, basis: Assumed, context: use.context, origin: use.origin } of
    Right atoms -> atoms
    Left _ -> []

  -- the least fixpoint of each member's constraints
  initial = Map.fromFoldable (map (\m -> Tuple m.key (Set.fromFoldable (map (\o -> Local o.root) (Array.filter (\o -> o.key == m.key) own)))) members)
  constraints = fixpoint initial
  fixpoint cs =
    let
      next = foldl raise cs uses
    in
      if next == cs then cs else fixpoint next
  raise cs u =
    let
      raised = Set.fromFoldable
        ( Array.mapMaybe
            ( \id -> case atomOf (rootOf id) of
                Just atom | not (provedAt u.use atom) -> Just (Propagated u.id (rootOf id))
                _ -> Nothing
            )
            (Set.toUnfoldable (constraintsOf cs u.callee.key))
        )
    in
      Map.insert u.key (Set.union (constraintsOf cs u.key) raised) cs
  constraintsOf cs key = case Map.lookup key cs of
    Just c -> c
    Nothing -> Set.empty

  -- what a member's plan quantifies
  quantifiedBy key = case planOf key of
    Just p -> { types: Set.fromFoldable (map _.meta p.quantifiers), kinds: Set.fromFoldable (map _.meta p.kindVars) }
    Nothing -> { types: Set.empty, kinds: Set.empty }
  representable key ts ks =
    let
      q = quantifiedBy key
      typeMetas = Set.filter (unsolvedType ctx0) (Set.unions (map (metasOf <<< zonk) ts))
      kindMetas = Set.filter (unsolvedKind ctx0) (Set.unions (map (kindMetasOf <<< substituteKind ctx0) ks) <> kindsOfMetas ctx0 typeMetas)
    in
      Set.subset typeMetas q.types && Set.subset kindMetas q.kinds

  -- a member whose signature writes its scheme gains no constraint
  unwritten = Array.concatMap
    (\m -> map (\id -> ConstraintUnwritten m.key (originOf m id)) (Set.toUnfoldable (constraintsOf constraints m.key)))
    writtenMembers
  writtenMembers = Array.filter _.written members
  inferredMembers = Array.filter (not <<< _.written) members

  ambiguousAtoms = Array.concatMap
    ( \m -> Array.mapMaybe
        ( \id -> case atomOf (rootOf id) of
            Just atom | not (representable m.key (map XMeta (atomMetas atom)) []) -> Just (AmbiguousConstraint m.key (originOf m id))
            _ -> Nothing
        )
        (Set.toUnfoldable (constraintsOf constraints m.key))
    )
    inferredMembers
  -- where an atom arose: its obligation's site, or the reference raising it
  originOf m = case _ of
    Local root -> maybe (InDeclaration m.name) _.origin (Array.find (\o -> o.root == root) own)
    Propagated use _ -> maybe (InDeclaration m.name) (_.use >>> _.origin) (Array.find (\u -> u.id == use) uses)

  ambiguousReferences = Array.mapMaybe
    ( \u -> case planOf u.callee.key of
        Just callee | not (representable u.key (map (XMeta <<< _.meta) callee.quantifiers) (map (XKMeta <<< _.meta) callee.kindVars)) -> Just (RecursiveArgumentAmbiguous u.key u.use.origin)
        _ -> Nothing
    )
    uses

  -- a rigid tail an atom names is bound where the member stands, or the atom
  -- would leave it free in the member's scheme
  escaping = Array.concatMap
    ( \m ->
        let
          inScope = freeRigids (zonk m.type)
        in
          Array.mapMaybe
            ( \id -> case atomOf (rootOf id) of
                Just (DisjointRigid _ r) | not (Set.member r inScope) -> Just (ConstraintEscapes m.key (originOf m id) r)
                _ -> Nothing
            )
            (Set.toUnfoldable (constraintsOf constraints m.key))
    )
    inferredMembers

  -- the final constraints of a member, in the order their atoms are held, each
  -- once once it is written in the member's variables
  finalConstraints m = Array.nubEq (map (substituteConstraint (memberContext ctx0 m.key) <<< atomConstraint) (Array.mapMaybe (atomOf <<< rootOf) (Set.toUnfoldable (constraintsOf constraints m.key))))

  -- each recursive reference made ordinary: the callee at its kind variables,
  -- its type variables, and a `[•]` for each of its constraints, still written
  -- in the group's metavariables
  resolved = foldl
    ( \acc u -> case planOf u.callee.key of
        Just callee ->
          let
            base = EGlobal unit u.callee.name (map (XKMeta <<< _.meta) callee.kindVars)
            typed = foldl (\e q -> ETyApp unit e (XMeta q.meta)) base callee.quantifiers
            applied = foldl (\e _ -> EConstraintApp unit e) typed (finalConstraints u.callee)
          in
            acc { recursiveUses = Map.insert u.id (u.use { resolution = Just applied }) acc.recursiveUses }
        Nothing -> acc
    )
    ctx0
    uses

  -- a member's variables in place of its quantified metavariables, over the
  -- context given
  memberContext base key = case planOf key of
    Just p ->
      base
        { bindings = foldl (\b q -> Map.insert q.meta (Assigned (XVar q.name)) b) base.bindings p.quantifiers
        , kindBindings = foldl (\b kv -> Map.insert kv.meta (KindAssigned (XKVar kv.name)) b) base.kindBindings p.kindVars
        }
    Nothing -> base

  finalized m =
    let
      context = memberContext resolved m.key
      quantifiers = maybe [] _.quantifiers (planOf m.key)
      kindVars = maybe [] (map _.name <<< _.kindVars) (planOf m.key)
      cs = finalConstraints m
      annotation = xExprAnnotation m.body
      binders = map (\q -> { name: q.name, kind: substituteKind context q.kind }) quantifiers
    in
      { key: m.key
      , name: m.name
      , scheme:
          { kindVars
          , body: foldr (\b t -> XForall b.name b.kind t) (foldr XConstrained (substitute context m.type) cs) binders
          }
      , body: foldr (\b e -> ETyLam annotation b.name b.kind e) (foldr (EConstraintLam annotation) (zonkExpr context m.body) cs) binders
      }

  -- the group's metavariables retired, with every solution `Ψ` holds that
  -- names one of them, and what the group owned released
  retiredKinds = closure (Set.fromFoldable (Array.concatMap (map _.meta <<< _.kindVars) plan.members)) \acc ->
    Set.fromFoldable
      ( Array.mapMaybe
          ( \(Tuple k binding) -> case binding of
              KindAssigned solution | meets acc (kindMetasOf solution) -> Just k
              _ -> Nothing
          )
          (Map.toUnfoldable ctx0.kindBindings)
      )
  retiredTypes = closure (Set.fromFoldable (Array.concatMap (map _.meta <<< _.quantifiers) plan.members)) \acc ->
    Set.fromFoldable
      ( Array.mapMaybe
          ( \(Tuple m binding) -> case binding of
              Assigned solution | meets acc (metasOf solution) || meets retiredKinds (kindMetasOfType solution) -> Just m
              _ -> Nothing
          )
          (Map.toUnfoldable ctx0.bindings)
      )
  retiredTerms = closure Set.empty \acc ->
    Set.fromFoldable
      ( Array.mapMaybe
          ( \(Tuple m binding) -> case binding of
              TermAssigned solution | namesRetired acc (metasOfTerm solution) -> Just m
              _ -> Nothing
          )
          (Map.toUnfoldable ctx0.termBindings)
      )
  namesRetired terms held = meets retiredTypes held.types || meets retiredKinds held.kinds || meets terms held.terms
  released = ctx0
    { bindings = Map.filterKeys (not <<< flip Set.member retiredTypes) ctx0.bindings
    , kindBindings = Map.filterKeys (not <<< flip Set.member retiredKinds) ctx0.kindBindings
    , termBindings = Map.filterKeys (not <<< flip Set.member retiredTerms) ctx0.termBindings
    , instantiationRows = Set.difference ctx0.instantiationRows retiredTypes
    , boundaryRows = Set.difference ctx0.boundaryRows retiredTypes
    , fits = Map.filter (not <<< owned <<< _.site) ctx0.fits
    , recursiveUses = Map.filter (not <<< owned) ctx0.recursiveUses
    }
  releasedStore = release owned store
  retired = s0 { tentative { metas = released, obligations = releasedStore } }

  -- nothing left in `Ψ` names what was retired: no binding, no obligation, no
  -- fit, no job, and no recursive reference, in what it holds or in the
  -- context it carries
  danglingIn =
    Array.any
      ( case _ of
          Unsolved info -> kindHolds info.kind
          Assigned solution -> typeHolds solution
      )
      (Array.fromFoldable (Map.values released.bindings))
      || Array.any
        ( case _ of
            KindAssigned solution -> kindHolds solution
            KindUnsolved _ -> false
        )
        (Array.fromFoldable (Map.values released.kindBindings))
      || Array.any
        ( case _ of
            TermAssigned solution -> termHolds solution
            TermUnsolved info -> typeHolds info.ty
        )
        (Array.fromFoldable (Map.values released.termBindings))
      || Array.any
        (\entry -> constraintHolds entry.obligation.constraint || contextHolds entry.obligation.context || meets retiredTypes entry.watching)
        (Array.fromFoldable (Map.values releasedStore.entries))
      || Array.any
        ( \record -> contextHolds record.site.context || case record.state of
            Undecided u -> typeHolds u.source || typeHolds u.target
            Widen w -> typeHolds w
            Equal -> false
        )
        (Array.fromFoldable (Map.values released.fits))
      || Array.any
        ( \p -> contextHolds p.site.context || meets retiredTypes p.awaiting || case p.job of
            JobUnify goal -> typeHolds goal.left || typeHolds goal.right || kindHolds goal.kind
            JobSynthesis goal -> typeHolds (goalOf goal).expectedType || Set.member (goalOf goal).target retiredTerms
            JobImplicitHandler goal -> Set.member goal.boundary retiredTypes || typeHolds goal.expected
            JobEffectFit _ -> false
        )
        (Array.fromFoldable (Map.values s0.tentative.scheduler.pending))
      || Array.any
        (\use -> contextHolds use.context || maybe false termHolds use.resolution)
        (Array.fromFoldable (Map.values released.recursiveUses))
  typeHolds t = meets retiredTypes (metasOf t) || meets retiredKinds (kindMetasOfType t)
  kindHolds k = meets retiredKinds (kindMetasOf k)

  termHolds :: forall b. XExpr b -> P.Boolean
  termHolds e = namesRetired retiredTerms (metasOfTerm e)
  constraintHolds = case _ of
    XLacks _ row -> typeHolds row
    XDisjoint l r -> typeHolds l || typeHolds r

  -- everything a context holds: its variables' types, its type variables'
  -- kinds, its regions' cells, and what it assumes
  contextHolds :: XContext -> P.Boolean
  contextHolds context =
    Array.any typeHolds (Array.fromFoldable (Map.values context.vars))
      || Array.any kindHolds (Array.fromFoldable (Map.values context.tyVars))
      || Array.any (\region -> Array.any typeHolds (Array.fromFoldable (Map.values region.layout))) (Array.fromFoldable (Map.values context.regions))
      || Array.any constraintHolds context.assumed

-- | A member as its group's generalization leaves it: its name, its scheme —
-- | the kind variables it binds and its type — and its definition.
type FinalizedMember k a =
  { key :: k
  , name :: Qualified Ident
  , scheme :: { kindVars :: P.Array KindVar, body :: XType }
  , body :: XExpr a
  }

type FinalizedGroup k a = { members :: P.Array (FinalizedMember k a) }

-- | What committing came to: the group generalized, or what keeps it from
-- | being.
data Commitment k a
  = Generalized (FinalizedGroup k a)
  | GeneralizationHindered (P.Array (Hindrance k))
  -- | `Ψ` holding what the group would retire, which is the host's defect.
  | GeneralizationHalted Defect

-- | The least set holding the one given and closed under the step given.
closure :: forall x. Ord x => Set x -> (Set x -> Set x) -> Set x
closure start step = let next = Set.union start (step start) in if next == start then start else closure next step

meets :: forall x. Ord x => Set x -> Set x -> P.Boolean
meets a b = not (Set.isEmpty (Set.intersection a b))

-- | An atom of one of the group's obligations: the obligation, and its place
-- | among the atoms the obligation leaves.
type OwnAtomId = { obligation :: ObligationId, slot :: P.Int }

-- | An atom a member's constraints hold: one of its own obligations', or one a
-- | recursive reference it makes raises, each by the atom it began as.
data AtomId
  = Local OwnAtomId
  | Propagated RecRefId OwnAtomId

rootOf :: AtomId -> OwnAtomId
rootOf = case _ of
  Local root -> root
  Propagated _ root -> root

atomMetas :: ResidualAtom -> P.Array MetaVar
atomMetas = case _ of
  LacksAtom _ t -> [ t ]
  DisjointRigid t _ -> [ t ]
  DisjointFlexible t1 t2 -> [ t1, t2 ]

derive instance Eq AtomId
derive instance Ord AtomId
