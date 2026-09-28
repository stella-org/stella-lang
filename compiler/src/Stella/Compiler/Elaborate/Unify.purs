-- | Unification over Core⁺, at kinds and at rows.
-- |
-- | Solving `ρ1 ≡ ρ2` operates on the normal form, and the procedure is
-- | identical at `Row Type` and `Row Effect`: every key is rigid, so the domain
-- | of a normal form does not depend on how metavariables are solved.
-- |
-- | Three outcomes are distinguished. `Solved` records a substitution,
-- | `Mismatch` is a failure to report, and `Stuck` is neither: it names the
-- | metavariables whose solution would let the constraint be retried.
-- |
-- | **`Stuck` arises at one place**, the case where a side carries more than one
-- | flexible tail and no solution is unique yet. Every metavariable it names is
-- | one the context holds unsolved, so each can be woken by an assignment; a
-- | metavariable that is absent or already solved is a caller error and is
-- | reported as one.
-- |
-- | **A `Stuck` reports the state it reached, as a `Solved` does.** Unification
-- | assigns as it descends, so an equation can refine one metavariable and then
-- | meet a sub-equation it cannot decide; the assignments it made stand in what
-- | it reports, together with the metavariables it made them to. Its caller owes
-- | two things to both outcomes — the obligations those assignments were watched
-- | by are re-decided, and the jobs blocked on them are woken — and an outcome
-- | that reported the dependency alone would have the caller read an equation
-- | that has already broken a constraint as one that is merely waiting.
-- |
-- | What the caller commits is another matter: only a `Solved` is committed, and
-- | what a `Stuck` reports is read and then rolled back with the attempt.
-- |
-- | Kind unification has no third outcome and says so in its type: kind equality
-- | is syntactic (D2), so a kind metavariable is assigned or the two kinds
-- | differ, and there is nothing to wait for.
module Stella.Compiler.Elaborate.Unify
  ( MetaInfo
  , MetaBinding(..)
  , KindRequirement(..)
  , KindMetaInfo
  , KindMetaBinding(..)
  , TermScope
  , TermMetaInfo
  , TermBinding(..)
  , MetaContext
  , UnifyEnv
  , UnifyProgress
  , UnifyError(..)
  , UnifyResult(..)
  , emptyContext
  , freshMeta
  , freshKindMeta
  , lookupMeta
  , lookupKindMeta
  , lookupTermMeta
  , narrowMetas
  , substitute
  , substituteKind
  , requireQuantifiable
  , requireProducesType
  , unifyKind
  , unifyType
  , unifyRow
  ) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.Kind (KindMetaVar(..), XKind(..), kindMetasOf, kindVarsOf, occursInKind)
import Stella.Compiler.Elaborate.Row (XRowError, XRowNormalForm, payloadEquations, rebuild, xnf)
import Stella.Compiler.Elaborate.Term (Region, TermMetaVar, XExpr)
import Stella.Compiler.Elaborate.Type (MetaVar(..), Scope, XConstraint(..), XRowEntry(..), XType(..), freeRigids, kindMetasOfType, metasOf, occursIn, outOfScope)
import Stella.Compiler.TypedCore (Ident, KindVar, RowElemKind(..), RowKey(..), TyVar)
import Data.Array as Array

import Data.Either (Either(..))
import Data.Foldable (any, foldM, foldr)
import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Set as Set
import Data.Show.Generic (genericShow)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..), snd)

-- | What `Ψ` records of an unsolved metavariable, that is, `?α : κ [Γ]`.
-- |
-- | `scope` is the `[Γ]`: the type and kind variables that were in scope where
-- | the metavariable was created. A solution mentioning any other lets a
-- | variable bound further in escape.
-- |
-- | The row constraints a substitution must preserve are **not** here. One may
-- | relate two metavariables, so no single one of them owns it, and it has to be
-- | decided against the facts of the site it came from rather than those of
-- | whatever equation reaches the metavariable. The obligations carry both.
type MetaInfo =
  { kind :: XKind
  , scope :: Scope
  }

data MetaBinding
  = Unsolved MetaInfo
  | Assigned XType

-- | What a site that created a kind metavariable requires of whatever solves it.
-- |
-- | Kind equality decides nothing about these: `?k ≡ Effect` is a kind equation
-- | that solves, and it is wrong only where `?k` stands somewhere a quantifiable
-- | kind is called for (D24). So a requirement is carried by the metavariable and
-- | re-applied at every assignment, rather than being a condition on equality.
data KindRequirement
  -- | `Γ ⊢ κ qkind`: the kind may stand where a type variable is introduced, and
  -- | in a `[[κ̄]]`.
  = Quantifiable
  -- | `result(κ) = Type`: the kind produces `Type` once fully applied, which is
  -- | what the right-hand side of a quantifiable arrow must do.
  | ProducesType

-- | What `Ψ` records of an unsolved kind metavariable, that is, `?k [Γ]`.
-- |
-- | A kind variable enters `Γ` only while a declaration whose scheme binds it is
-- | being checked (D3), so a solution mentioning one the metavariable was not
-- | created under keeps that variable alive past its declaration.
type KindMetaInfo =
  { scope :: Set KindVar
  , requirements :: Set KindRequirement
  }

data KindMetaBinding
  = KindUnsolved KindMetaInfo
  | KindAssigned XKind

-- | What a term metavariable's solution may mention: the value, type, and kind
-- | variables in scope where it was created.
-- |
-- | Join points are not among them. A solution may jump only to a join point it
-- | binds itself, so no join point of the place it stands in is in scope.
-- |
-- | `region` is the region of cells where it was created, if one is there: a
-- | solution reads and writes only cells of that region, a cell being named by
-- | its key alone and meaning the innermost region's.
type TermScope =
  { values :: Set Ident
  , types :: Set TyVar
  , kinds :: Set KindVar
  , region :: Maybe Region
  }

-- | What `Ψ` records of an unsolved term metavariable, that is, `?m : τ [Γ]`.
type TermMetaInfo =
  { ty :: XType
  , scope :: TermScope
  }

-- | A term metavariable's solution is held without annotations. Where it is
-- | zonked into a term it takes the annotation of the `?m` it replaces, which is
-- | the place the goal stood.
data TermBinding
  = TermUnsolved TermMetaInfo
  | TermAssigned (XExpr Unit)

-- | `Ψ`, together with the journal of one unification.
-- |
-- | `assigned` is the type metavariables assigned since a unification began. It
-- | is what a caller owes an assignment to — waking what is blocked on it, and
-- | re-deciding the obligations watching it.
-- |
-- | **A context between unifications holds none.** What a unification reports has
-- | it emptied, and a unification given one that is not empty **fails** rather
-- | than emptying it: a caller that has not acted on an assignment is owed the
-- | error, and normalizing here would make losing them the quiet default.
-- |
-- | It rides with `Ψ` rather than beside it so that no step of a unification has
-- | to remember to carry it: a substitution and the record of having made one are
-- | written in one place.
type MetaContext =
  { bindings :: Map MetaVar MetaBinding
  , kindBindings :: Map KindMetaVar KindMetaBinding
  , termBindings :: Map TermMetaVar TermBinding
  , next :: P.Int
  , nextKind :: P.Int
  , nextTerm :: P.Int
  , assigned :: Set MetaVar
  }

-- | What a unification reads off the site of the equation it is given.
-- |
-- | `kindVars` are the kind variables in scope there, which a kind metavariable
-- | created during the unification may mention. It is read-only: nothing here is
-- | state and nothing is written back.
-- |
-- | **`Γ*` is not among it.** Unification decides equality, and the atomic facts
-- | of a context decide row constraints, which the obligations hold and their own
-- | sites decide.
type UnifyEnv =
  { kindVars :: Set KindVar
  }

-- | What a unification did: the tentative `Ψ` it reached, and what it assigned
-- | on the way.
type UnifyProgress =
  { metas :: MetaContext
  , assigned :: Set MetaVar
  }

data UnifyError
  -- | The two sides cannot be made equal by any substitution.
  = RowMismatch XRowNormalForm XRowNormalForm
  -- | A rigid tail on a side that has nothing left to absorb it.
  | RigidTailRemains (Set TyVar)
  -- | Assigning would make a metavariable refer to itself.
  | OccursCheck MetaVar XType
  -- | Two entries share a key but carry payloads no substitution equates.
  | PayloadMismatch RowKey XRowEntry XRowEntry
  -- | A rigid variable that would outlive its binder through a metavariable:
  -- | mentioned by a solution the metavariable was not created under, or left in
  -- | what that metavariable holds once a narrowing has put it out of scope.
  | EscapingVariable MetaVar TyVar
  -- | The same, for a kind variable.
  | EscapingKindVariable MetaVar KindVar
  -- | The kind of a solution does not match the kind of the metavariable. The
  -- | whole of each kind is reported, the metavariable being what names the
  -- | failure, rather than the sub-kinds at which the two first differed.
  | KindMismatch MetaVar XKind XKind
  -- | Two kinds no substitution equates.
  | KindNotEqual XKind XKind
  -- | Assigning would make a kind metavariable refer to itself.
  | KindOccursCheck KindMetaVar XKind
  -- | A kind solution mentions a kind variable that was not in scope where the
  -- | metavariable was created.
  | KindEscapingVariable KindMetaVar KindVar
  -- | A kind required to be quantifiable that is not (D24).
  | KindNotQuantifiable XKind
  -- | A kind required to produce `Type` once fully applied that does not.
  | KindDoesNotProduceType XKind
  -- | A kind metavariable the context does not hold, which is a caller error.
  | KindMetaUnbound KindMetaVar
  -- | Two types no substitution equates.
  | TypeNotEqual XType XType
  -- | Two constraints no substitution equates.
  | ConstraintNotEqual XConstraint XConstraint
  -- | A metavariable whose solution would mention a variable bound by a `forall`
  -- | the two sides are being compared under. Solving it needs the two binders
  -- | identified rather than corresponded, which is higher-rank unification;
  -- | this unifier refuses rather than guess, and a checker that reads an
  -- | annotation is where such a type belongs.
  | CannotSolveAcrossForall MetaVar TyVar
  -- | A metavariable the context does not hold, and one it holds solved. Both
  -- | are caller errors rather than unification failures, and neither may be
  -- | reported as `Stuck`: a dependency that is absent, or already solved, is
  -- | one no assignment can wake.
  | MetaUnbound MetaVar
  | MetaAlreadyAssigned MetaVar
  -- | A context handed to a unification that still holds assignments nobody has
  -- | acted on. Each is owed a wake and a re-deciding of the obligations watching
  -- | it, so beginning another unification over it would lose both; emptying the
  -- | journal here instead would make silently dropping them the normal case.
  | AssignmentsUnread (Set MetaVar)
  | NotARow XRowError

-- | What a unification reports to the caller that asked for it.
data UnifyResult
  = Solved UnifyProgress
  -- | Undecided for now. `blockedOn` is what would decide it, and `progress`
  -- | holds what the attempt did before meeting it, which the caller reads and
  -- | then rolls back.
  | Stuck
      { progress :: UnifyProgress
      , blockedOn :: Set MetaVar
      }
  | Mismatch UnifyError

-- | One step of a unification, over `Ψ` alone.
-- |
-- | The public judgements report a `UnifyResult`; this is what their steps thread
-- | between themselves, and the journal it carries is inside the context.
data Step
  = Stepped MetaContext
  | Stuck' MetaContext (Set MetaVar)
  | Broke UnifyError

emptyContext :: MetaContext
emptyContext =
  { bindings: Map.empty
  , kindBindings: Map.empty
  , termBindings: Map.empty
  , next: 0
  , nextKind: 0
  , nextTerm: 0
  , assigned: Set.empty
  }

-- | What a step reached, as its caller reads it. The journal is emptied in the
-- | context reported, so that nothing reads one assignment twice.
progressOf :: MetaContext -> UnifyProgress
progressOf ctx =
  { metas: ctx { assigned = Set.empty }
  , assigned: ctx.assigned
  }

-- | A step's outcome as a result, which is what the public judgements return.
resultOf :: Step -> UnifyResult
resultOf = case _ of
  Stepped ctx -> Solved (progressOf ctx)
  Stuck' ctx ms -> Stuck { progress: progressOf ctx, blockedOn: ms }
  Broke err -> Mismatch err

freshMeta :: MetaInfo -> MetaContext -> Tuple MetaVar MetaContext
freshMeta info ctx =
  Tuple m ctx
    { bindings = Map.insert m (Unsolved info) ctx.bindings
    , next = ctx.next + 1
    }
  where
  m = MetaVar ctx.next

freshKindMeta :: KindMetaInfo -> MetaContext -> Tuple KindMetaVar MetaContext
freshKindMeta info ctx =
  Tuple k ctx
    { kindBindings = Map.insert k (KindUnsolved info) ctx.kindBindings
    , nextKind = ctx.nextKind + 1
    }
  where
  k = KindMetaVar ctx.nextKind

lookupMeta :: MetaContext -> MetaVar -> Maybe MetaBinding
lookupMeta ctx m = Map.lookup m ctx.bindings

lookupKindMeta :: MetaContext -> KindMetaVar -> Maybe KindMetaBinding
lookupKindMeta ctx k = Map.lookup k ctx.kindBindings

lookupTermMeta :: MetaContext -> TermMetaVar -> Maybe TermBinding
lookupTermMeta ctx m = Map.lookup m ctx.termBindings

-- | Apply what is already solved. Normalizing without this would leave an
-- | assigned metavariable in the flexible tail, where the case analysis would
-- | treat it as an unknown.
substitute :: MetaContext -> XType -> XType
substitute ctx = go
  where
  go = case _ of
    XMeta m -> case Map.lookup m ctx.bindings of
      Just (Assigned ty) -> go ty
      _ -> XMeta m
    XCon n kinds -> XCon n (map (substituteKind ctx) kinds)
    XApp f a -> XApp (go f) (go a)
    XForall a k body -> XForall a (substituteKind ctx k) (go body)
    XConstrained c body -> XConstrained (goConstraint c) (go body)
    XRowExtend entry rest -> XRowExtend (goEntry entry) (go rest)
    XRowUnion l r -> XRowUnion (go l) (go r)
    ty -> ty

  goEntry = case _ of
    XRowTypeEntry k ty -> XRowTypeEntry k (go ty)
    XRowEffectEntry e args -> XRowEffectEntry e (map go args)
    XRowLabelledEffectEntry s e args -> XRowLabelledEffectEntry s e (map go args)
    XRowRegionEntry var cells -> XRowRegionEntry (go var) (go cells)

  -- A constraint carries rows of its own, and a hole left in one of them would
  -- survive zonking and fail `toCore`.
  goConstraint = case _ of
    XLacks key row -> XLacks key (go row)
    XDisjoint l r -> XDisjoint (go l) (go r)

-- | Apply what is already solved at the kind level.
substituteKind :: MetaContext -> XKind -> XKind
substituteKind ctx = go
  where
  go = case _ of
    XKMeta m -> case Map.lookup m ctx.kindBindings of
      Just (KindAssigned kind) -> go kind
      _ -> XKMeta m
    XKFun a b -> XKFun (go a) (go b)
    kind -> kind

-- | `κ1 ≡ κ2`.
-- |
-- | There is no computation at the kind level and no subsumption, so this is
-- | first-order unification with an occurs check. Every outcome is decided here:
-- | a kind metavariable is assigned, or the two kinds differ.
unifyKind :: MetaContext -> XKind -> XKind -> Either UnifyError MetaContext
unifyKind ctx kind1 kind2 = go ctx kind1 kind2
  where
  go c a b = case substituteKind c a, substituteKind c b of
    -- One metavariable against itself holds whatever it is, but only where the
    -- context has it: an unknown one is a caller error on either side.
    XKMeta m, XKMeta n | m == n ->
      if Map.member m c.kindBindings then Right c else Left (KindMetaUnbound m)
    XKMeta m, solution -> assignKind c m solution
    solution, XKMeta n -> assignKind c n solution
    XKVar x, XKVar y | x == y -> Right c
    XKType, XKType -> Right c
    XKEffect, XKEffect -> Right c
    XKRow e, XKRow f | e == f -> Right c
    XKFun a1 a2, XKFun b1 b2 -> do
      c1 <- go c a1 b1
      go c1 a2 b2
    left, right -> Left (KindNotEqual left right)

-- | Every kind substitution performs an occurs check and a scope check, as a
-- | type substitution does, and then holds the solution to what the
-- | metavariable requires of it.
assignKind :: MetaContext -> KindMetaVar -> XKind -> Either UnifyError MetaContext
assignKind ctx m given = case Map.lookup m ctx.kindBindings of
  Just (KindUnsolved info) ->
    let
      solution = substituteKind ctx given
    in
      if occursInKind m solution then
        Left (KindOccursCheck m solution)
      else case Set.findMin (Set.difference (kindVarsOf solution) info.scope) of
        Just escaping ->
          Left (KindEscapingVariable m escaping)
        Nothing -> do
          -- A requirement reaching an unsolved kind attaches itself there, so
          -- assigning one metavariable to another moves the requirements across
          -- and the two sets merge.
          required <- foldM (applyRequirement solution) ctx
            (Set.toUnfoldable info.requirements :: P.Array KindRequirement)
          narrowed <- foldM (narrowKindTo info.scope) required
            (Set.toUnfoldable (kindMetasOf solution) :: P.Array KindMetaVar)
          pure narrowed { kindBindings = Map.insert m (KindAssigned solution) narrowed.kindBindings }

  _ ->
    Left (KindMetaUnbound m)

applyRequirement :: XKind -> MetaContext -> KindRequirement -> Either UnifyError MetaContext
applyRequirement kind ctx = case _ of
  Quantifiable -> requireQuantifiable ctx kind
  ProducesType -> requireProducesType ctx kind

-- | `Γ ⊢ κ qkind`, as an obligation rather than as a judgement.
-- |
-- | Where the kind is unsolved there is nothing to decide yet, so the
-- | requirement is attached to the metavariable and decided when it is
-- | assigned. An arrow is quantifiable only where it produces `Type`, so both
-- | sides carry the requirement and the right-hand one carries a second.
-- |
-- | **A rigid kind variable is admitted unconditionally, and that it is bound is
-- | the caller's to establish.** This takes no `Γ`: every kind variable of a
-- | well-formed kind is bound by the scheme of the declaration being checked
-- | (D3), so the judgement `k ∈ Γ` belongs where the kind is built. A caller
-- | that skips it leaves an unbound kind variable for the Core kind checker to
-- | find rather than reporting it where it was written.
requireQuantifiable :: MetaContext -> XKind -> Either UnifyError MetaContext
requireQuantifiable ctx kind = case substituteKind ctx kind of
  XKType -> Right ctx
  XKRow _ -> Right ctx
  XKVar _ -> Right ctx
  XKMeta m -> attachRequirement Quantifiable m ctx
  XKEffect -> Left (KindNotQuantifiable XKEffect)
  XKFun a b -> do
    ctx1 <- requireQuantifiable ctx a
    ctx2 <- requireQuantifiable ctx1 b
    requireProducesType ctx2 b

-- | `result(κ) = Type`.
-- |
-- | A rigid kind variable fails: a scheme says nothing about what instantiates
-- | it, and a row kind is among the possibilities.
requireProducesType :: MetaContext -> XKind -> Either UnifyError MetaContext
requireProducesType ctx kind = case substituteKind ctx kind of
  XKType -> Right ctx
  XKFun _ b -> requireProducesType ctx b
  XKMeta m -> attachRequirement ProducesType m ctx
  other -> Left (KindDoesNotProduceType other)

attachRequirement :: KindRequirement -> KindMetaVar -> MetaContext -> Either UnifyError MetaContext
attachRequirement requirement m ctx = case Map.lookup m ctx.kindBindings of
  Just (KindUnsolved info) ->
    Right ctx
      { kindBindings = Map.insert m
          (KindUnsolved (info { requirements = Set.insert requirement info.requirements }))
          ctx.kindBindings
      }

  -- Substituting leaves no assigned metavariable in the position this reaches.
  _ ->
    Left (KindMetaUnbound m)

-- | `solve(ρ1 ≡ ρ2)`.
-- |
-- | Payload equations are returned rather than solved: equating `F1(k)` with
-- | `F2(k)` is type unification, which is a separate judgement. The caller
-- | discharges them. A payload the two sides cannot share at all is decided
-- | here, since no substitution repairs it.
-- | Two corresponding `forall` binders, innermost first.
-- |
-- | Unification identifies the binders of two `forall`s by position rather than
-- | by renaming either side, so a variable is read through this rather than
-- | compared by name.
type Correspondence = P.Array { left :: TyVar, right :: TyVar }

-- | `τ1 ≡ τ2` at a kind both sides stand at.
-- |
-- | **The kind is a parameter because unification never has to synthesize one.**
-- | Both sides of an equation stand at one kind by the premise of whoever wrote
-- | it, so it is carried down rather than derived, and the only thing a
-- | metavariable's own kind is checked against is that. `kindVars` are the kind
-- | variables `Γ` holds, which a kind metavariable created here may mention.
-- |
-- | Rows go to `unifyRow`, and the payload equations it emits are discharged
-- | here: solving them is type unification, which is this judgement.
-- |
-- | **A unification imposes no obligation of its own**, so what it reports is
-- | assignments and nothing else. A fresh row tail introduced by a two-sided
-- | refinement stands for what the two tails it replaces had in common, and what
-- | it is obliged to is what they were obliged to: zonking a constraint that
-- | named one of them names the fresh tail, so the obligation that reaches it is
-- | the one already held rather than a new one. Every obligation is therefore
-- | introduced before a unification is asked for, and the caller has none to take
-- | on afterwards.
unifyType :: UnifyEnv -> MetaContext -> XKind -> XType -> XType -> UnifyResult
unifyType env ctx kind left right
  | not (Set.isEmpty ctx.assigned) = Mismatch (AssignmentsUnread ctx.assigned)
  | otherwise =
      resultOf case go ctx [] kind left right of
        -- The kind metavariables an equation created are dropped where it
        -- succeeds. Nothing commits what a `Stuck` reached, so there is nothing
        -- there to tidy.
        Stepped c -> Stepped (discardLocalKinds ctx.nextKind c)
        other -> other
      where
      kindVars = env.kindVars

      go c bound k t1 t2 = case substitute c t1, substitute c t2 of
        a, b | isRowSyntax a || isRowSyntax b ->
          rows c bound k a b

        XMeta m, XMeta n | m == n -> case metaStandsAt c k m of
          Left err -> Broke err
          Right c' -> Stepped c'

        XMeta m, solution -> solve' c bound k m solution
        solution, XMeta n -> solve' c bound k n solution

        XVar x, XVar y ->
          if corresponds bound x y then Stepped c
          else Broke (TypeNotEqual (XVar x) (XVar y))

        XCon n1 ks1, XCon n2 ks2
          | n1 == n2 && Array.length ks1 == Array.length ks2 ->
              case foldM (\acc (Tuple k1 k2) -> unifyKind acc k1 k2) c (Array.zip ks1 ks2) of
                Left err -> Broke err
                Right c' -> Stepped c'

        -- The kind of the argument is what neither side says, so a metavariable
        -- stands for it and the head is read at an arrow into the carried kind.
        XApp f1 a1, XApp f2 a2 ->
          let
            Tuple ka c1 = freshKindMeta { scope: kindVars, requirements: Set.empty } c
          in
            case go c1 bound (XKFun (XKMeta ka) k) f1 f2 of
              Stepped c2 -> go c2 bound (XKMeta ka) a1 a2
              other -> other

        XForall a k1 b1, XForall b k2 b2 ->
          case unifyKind c k XKType >>= \c1 -> unifyKind c1 k1 k2 of
            Left err -> Broke err
            Right c' -> go c' (Array.cons { left: a, right: b } bound) XKType b1 b2

        XConstrained c1 b1, XConstrained c2 b2 ->
          case unifyKind c k XKType of
            Left err -> Broke err
            Right c' -> case constraints c' bound c1 c2 of
              Stepped c'' -> go c'' bound XKType b1 b2
              other -> other

        a, b ->
          Broke (TypeNotEqual a b)

      -- Assigning a metavariable, once what stands across a `forall` is refused.
      --
      -- **Both sides are held to the carried kind, not only the one being
      -- assigned.** A metavariable at the root of the solution stands at that kind
      -- too, and its own is the only kind of a solution this judgement ever has: one
      -- deeper inside stands at a kind of its own, and a solution that is not a
      -- metavariable has none recorded anywhere.
      solve' c bound k m solution = case acrossForall bound solution of
        Just binder ->
          Broke (CannotSolveAcrossForall m binder)
        Nothing -> case metaStandsAt c k m >>= \c1 -> rootStandsAt c1 k solution of
          Left err -> Broke err
          Right c' -> assignMeta c' m solution

      rootStandsAt c k = case _ of
        XMeta n -> metaStandsAt c k n
        _ -> Right c

      metaStandsAt c k m = case Map.lookup m c.bindings of
        Just (Unsolved info) -> case unifyKind c info.kind k of
          Left _ -> Left (KindMismatch m info.kind k)
          Right c' -> Right c'
        Just (Assigned _) -> Left (MetaAlreadyAssigned m)
        Nothing -> Left (MetaUnbound m)

      -- **Every flexible tail of a row stands at the row's own kind**, so each is
      -- held to the carried one here. A row with no known element gives `rowKindOf`
      -- nothing, and a side that is a bare metavariable never reaches `solve'`, so
      -- this is where either is caught.
      rows c bound k a b = case tailsStandAt c k a >>= \c1 -> tailsStandAt c1 k b of
        Left err ->
          Broke err
        Right c1 ->
          let
            Tuple result equations = unifyRowUnder bound c1 a b
          in
            case result of
              Stepped c2 -> case knownRowKind c2 a b of
                Nothing -> discharge c2 bound k equations
                Just rowKind -> case unifyKind c2 k rowKind of
                  Left err -> Broke err
                  Right c3 -> discharge c3 bound k equations
              other -> other

      tailsStandAt c k side = case xnf (substitute c side) of
        Left _ ->
          Right c
        Right n ->
          foldM (\acc m -> metaStandsAt acc k m) c (Set.toUnfoldable n.flexible :: P.Array MetaVar)

      knownRowKind c x y = case rowKindOf (substitute c x) of
        Just fromLeft -> Just fromLeft
        Nothing -> rowKindOf (substitute c y)

      -- A `Row Type` element carries a type, so its payload equations stand at
      -- `Type`. What an effect argument stands at is `Σ`'s to say, and a
      -- metavariable stands for it here — **one per equation**, two arguments of one
      -- effect having no reason to share a kind.
      discharge c bound k equations = case Array.uncons equations of
        Nothing ->
          Stepped c
        Just { head: Tuple t1 t2, tail } ->
          let
            Tuple equationKind c1 = case substituteKind c k of
              XKRow RowType ->
                Tuple XKType c
              _ ->
                let
                  Tuple ka c' = freshKindMeta { scope: kindVars, requirements: Set.empty } c
                in
                  Tuple (XKMeta ka) c'
          in
            case go c1 bound equationKind t1 t2 of
              Stepped c2 -> discharge c2 bound k tail
              other -> other

      constraints c bound k1 k2 = case k1, k2 of
        XLacks key1 r1, XLacks key2 r2
          | key1 == key2 ->
              let
                Tuple rowKind c1 = kindOfRowKeyed key1 c
              in
                go c1 bound rowKind r1 r2

        -- Both sides of `#` share one row element kind, so one kind serves the two.
        XDisjoint l1 r1, XDisjoint l2 r2 ->
          let
            Tuple ka c1 = freshKindMeta { scope: kindVars, requirements: Set.empty } c
          in
            case go c1 bound (XKMeta ka) l1 l2 of
              Stepped c2 -> go c2 bound (XKMeta ka) r1 r2
              other -> other

        _, _ ->
          Broke (ConstraintNotEqual k1 k2)

      -- Which row a key belongs to, where the key settles it. A `SymbolKey` keys a
      -- field and a labelled effect instance alike, so it settles nothing.
      kindOfRowKeyed key c = case key of
        TagKey _ -> Tuple (XKRow RowType) c
        PositionKey _ -> Tuple (XKRow RowType) c
        EffectKey _ -> Tuple (XKRow RowEffect) c
        RegionKey -> Tuple (XKRow RowEffect) c
        SymbolKey _ ->
          let
            Tuple ka c' = freshKindMeta { scope: kindVars, requirements: Set.empty } c
          in
            Tuple (XKMeta ka) c'

-- | Drop the kind metavariables one unification created that nothing refers to.
-- |
-- | Each stands for a kind the judgement cannot name — an effect argument's,
-- | which is `Σ`'s, or the argument of an application, which neither side says —
-- | so it is a local existential rather than part of the solver's state. One
-- | left unsolved and unreferenced would grow `Ψ` by every application a
-- | unification descends and by every payload equation it discharges.
-- |
-- | What refers to one is the kind of a metavariable, or a kind another
-- | metavariable is solved to, or a kind standing in a solution; what a
-- | metavariable created before this unification holds is left alone whichever.
discardLocalKinds :: P.Int -> MetaContext -> MetaContext
discardLocalKinds watermark ctx =
  ctx { kindBindings = Map.filterWithKey keep ctx.kindBindings }
  where
  referenced =
    foldr (\binding acc -> inKind binding <> acc) Set.empty (Map.values ctx.kindBindings)
      <> foldr (\binding acc -> inType binding <> acc) Set.empty (Map.values ctx.bindings)

  inKind = case _ of
    KindAssigned kind -> kindMetasOf kind
    KindUnsolved _ -> Set.empty

  inType = case _ of
    Unsolved info -> kindMetasOf info.kind
    Assigned ty -> kindMetasOfType ty

  keep k = case _ of
    KindAssigned _ -> true
    KindUnsolved _ -> before k || Set.member k referenced

  before (KindMetaVar n) = n < watermark

-- | Whether a type is written as a row. A row variable and a row metavariable are
-- | rows too, and each is taken by the case that reads a variable.
isRowSyntax :: XType -> P.Boolean
isRowSyntax = case _ of
  XRowEmpty -> true
  XRowExtend _ _ -> true
  XRowUnion _ _ -> true
  _ -> false

-- | Whether two variables are the same one, read through the correspondence.
-- |
-- | The innermost entry mentioning either variable is what decides: a variable
-- | bound there is that binder and no other, so one bound against one free is a
-- | mismatch however the two are spelled. Neither being bound leaves name
-- | equality, which is what a free variable is compared by.
corresponds :: Correspondence -> TyVar -> TyVar -> P.Boolean
corresponds bound x y =
  case Array.find (\e -> e.left == x || e.right == y) bound of
    Just e -> e.left == x && e.right == y
    Nothing -> x == y

-- | A variable of the correspondence that a metavariable's solution mentions.
-- |
-- | Solving such a metavariable needs the two binders identified rather than
-- | corresponded, which is higher-rank unification. Refusing covers a binder of
-- | either side, so a name the two happen to share cannot be mistaken for the
-- | other's.
acrossForall :: Correspondence -> XType -> Maybe TyVar
acrossForall bound solution =
  Set.findMin (Set.intersection (freeRigids solution) names)
  where
  names = Set.fromFoldable (Array.concatMap (\e -> [ e.left, e.right ]) bound)

unifyRow :: MetaContext -> XType -> XType -> Tuple UnifyResult (P.Array (Tuple XType XType))
unifyRow ctx row1 row2
  | not (Set.isEmpty ctx.assigned) =
      Tuple (Mismatch (AssignmentsUnread ctx.assigned)) []
  | otherwise = case unifyRowUnder [] ctx row1 row2 of
      Tuple step equations -> Tuple (resultOf step) equations

-- | The same, under the `forall` binders the two sides are being compared under.
-- |
-- | **Rigid tails cancel through the correspondence rather than by name**, so
-- | `forall r. ( a : A | r )` and `forall s. ( a : A | s )` are the one type they
-- | are. Comparing the two tails as a set of names would leave each standing and
-- | reject an ordinary row-polymorphic scheme.
unifyRowUnder :: Correspondence -> MetaContext -> XType -> XType -> Tuple Step (P.Array (Tuple XType XType))
unifyRowUnder bound ctx row1 row2 =
  case xnf (substitute ctx row1), xnf (substitute ctx row2) of
    Left err, _ -> Tuple (Broke (NotARow err)) []
    _, Left err -> Tuple (Broke (NotARow err)) []
    Right n1, Right n2 -> case unsolvedTails ctx (Set.union n1.flexible n2.flexible) of
      Just err -> Tuple (Broke err) []
      Nothing -> solve bound ctx n1 n2

-- | Every flexible tail is a metavariable the context holds unsolved.
-- |
-- | Deciding this before the case analysis is what keeps a `Stuck` honest. Two
-- | occurrences of one tail cancel each other, and a tail nothing holds would
-- | otherwise pass through that cancellation into a `Solved`, or stand in the
-- | dependency set of a `Stuck` that no assignment can ever wake.
unsolvedTails :: MetaContext -> Set MetaVar -> Maybe UnifyError
unsolvedTails ctx metas =
  Array.head (Array.mapMaybe unsolved (Set.toUnfoldable metas :: P.Array MetaVar))
  where
  unsolved m = case Map.lookup m ctx.bindings of
    Just (Unsolved _) -> Nothing
    Just (Assigned _) -> Just (MetaAlreadyAssigned m)
    Nothing -> Just (MetaUnbound m)

solve :: Correspondence -> MetaContext -> XRowNormalForm -> XRowNormalForm -> Tuple Step (P.Array (Tuple XType XType))
solve bound ctx n1 n2 =
  case traverse payloadsAt (Set.toUnfoldable shared :: P.Array RowKey) of
    Left err ->
      Tuple (Broke err) []
    Right equations ->
      Tuple (step4 bound ctx d1 d2 r1 r2 m1 m2 n1 n2) (Array.concat equations)
  where
  -- 1. match the payloads of shared keys
  shared = Set.intersection (domain n1) (domain n2)

  payloadsAt key = case Map.lookup key n1.known, Map.lookup key n2.known of
    Just e1, Just e2 -> case payloadEquations e1 e2 of
      Just equations -> Right equations
      Nothing -> Left (PayloadMismatch key e1 e2)
    _, _ -> Right []

  d1 = Map.filterKeys (\k -> not (Set.member k shared)) n1.known
  d2 = Map.filterKeys (\k -> not (Set.member k shared)) n2.known

  -- 2. cancel shared tails, on both the rigid and the flexible side
  --
  -- A rigid tail cancels the one it corresponds to, which is the same as
  -- cancelling by name wherever the correspondence is empty. A metavariable
  -- belongs to `Ψ` rather than to either side, so the flexible tails cancel by
  -- identity whatever binders stand around them.
  r1 = Set.filter (\x -> not (any (corresponds bound x) n2.rigid)) n1.rigid
  r2 = Set.filter (\y -> not (any (\x -> corresponds bound x y) n1.rigid)) n2.rigid
  m1 = Set.difference n1.flexible n2.flexible
  m2 = Set.difference n2.flexible n1.flexible

-- | 4. case analysis on the number of flexible tails.
step4
  :: Correspondence
  -> MetaContext
  -> Map RowKey XRowEntry
  -> Map RowKey XRowEntry
  -> Set TyVar
  -> Set TyVar
  -> Set MetaVar
  -> Set MetaVar
  -> XRowNormalForm
  -> XRowNormalForm
  -> Step
step4 bound ctx d1 d2 r1 r2 m1 m2 n1 n2 =
  case Set.toUnfoldable m1 :: P.Array MetaVar, Set.toUnfoldable m2 :: P.Array MetaVar of
    -- (a) both sides are determined
    [], [] ->
      if Map.isEmpty d1 && Map.isEmpty d2 && Set.isEmpty r1 && Set.isEmpty r2 then
        Stepped ctx
      else if not (Set.isEmpty r1) || not (Set.isEmpty r2) then
        Broke (RigidTailRemains (Set.union r1 r2))
      else
        Broke (RowMismatch n1 n2)

    -- (b) one side is determined, so the other's remainder must be empty
    [], [ s ] ->
      assign bound ctx s { known: d1, rigid: r1, flexible: Set.empty } d2 r2

    [ r ], [] ->
      assign bound ctx r { known: d2, rigid: r2, flexible: Set.empty } d1 r1

    -- (c) both tails are flexible: refine them together through a fresh one
    [ r ], [ s ] ->
      refine bound ctx r s d1 d2 r1 r2

    -- (d) more than one flexible tail on a side: no unique solution yet
    _, _ ->
      Stuck' ctx (Set.union m1 m2)

-- | Case (b). The side with no flexible tail has nothing left to absorb what
-- | remains on the other, so a leftover there is a mismatch. A rigid tail
-- | **can** be absorbed by the flexible side, which is the point of the split.
assign
  :: Correspondence
  -> MetaContext
  -> MetaVar
  -> XRowNormalForm
  -> Map RowKey XRowEntry
  -> Set TyVar
  -> Step
assign bound ctx m solution leftoverKnown leftoverRigid =
  if not (Map.isEmpty leftoverKnown) then
    Broke (RowMismatch solution { known: leftoverKnown, rigid: leftoverRigid, flexible: Set.empty })
  else if not (Set.isEmpty leftoverRigid) then
    Broke (RigidTailRemains leftoverRigid)
  else
    assignRow bound ctx m (rebuild solution)

-- | A row assignment, refused where the row is one side's binder.
-- |
-- | A corresponding tail has cancelled by the time this is reached, so what is
-- | left of the correspondence in a solution is a binder the other side has no
-- | counterpart for, which is the higher-rank case (D3, [Open Questions]).
assignRow :: Correspondence -> MetaContext -> MetaVar -> XType -> Step
assignRow bound ctx m solution = case acrossForall bound solution of
  Just binder -> Broke (CannotSolveAcrossForall m binder)
  Nothing -> assignMeta ctx m solution

-- | Case (c). A substitution on one side alone either fails an occurs check or
-- | produces an unequal pair, so a fresh tail is introduced and **both** sides
-- | are refined through it.
refine
  :: Correspondence
  -> MetaContext
  -> MetaVar
  -> MetaVar
  -> Map RowKey XRowEntry
  -> Map RowKey XRowEntry
  -> Set TyVar
  -> Set TyVar
  -> Step
refine bound ctx r s d1 d2 r1 r2 =
  case lookupMeta ctx r, lookupMeta ctx s of
    Just (Unsolved infoR), Just (Unsolved infoS) ->
      -- Two bare metavariables have no element to give their row element kind
      -- away, so the kinds are unified here rather than at the assignment.
      case unifyKind ctx infoR.kind infoS.kind of
        Left _ ->
          Broke (KindMismatch s infoS.kind infoR.kind)

        Right ctxK ->
          let
            -- The fresh tail stands where both stood, so it may mention only
            -- what both had in scope.
            sharedScope =
              { types: Set.intersection infoR.scope.types infoS.scope.types
              , kinds: Set.intersection infoR.scope.kinds infoS.scope.kinds
              }

            -- **The fresh tail carries no constraint of its own.** What it is
            -- obliged to is what the two tails it replaces were obliged to, and
            -- an obligation that named either of them names this one once its
            -- constraint is zonked, so nothing has to be copied here.
            freshInfo =
              { kind: substituteKind ctxK infoR.kind
              , scope: sharedScope
              }
          in
            let
              Tuple t ctx' = freshMeta freshInfo ctxK
            in
              case assignRow bound ctx' r (rebuild { known: d2, rigid: r2, flexible: Set.singleton t }) of
                Stepped ctx'' ->
                  assignRow bound ctx'' s (rebuild { known: d1, rigid: r1, flexible: Set.singleton t })
                other ->
                  other

    Just (Assigned _), _ -> Broke (MetaAlreadyAssigned r)
    Nothing, _ -> Broke (MetaUnbound r)
    _, Just (Assigned _) -> Broke (MetaAlreadyAssigned s)
    _, Nothing -> Broke (MetaUnbound s)

-- | Every substitution performs an occurs check, verifies the kind, and narrows
-- | the scope of what stands in the solution.
-- |
-- | **What the row constraints of the metavariable allow is not decided here.**
-- | One is decided against the facts of the site it came from, which this
-- | equation's site need not be, so it is the caller that re-decides what the
-- | assignment recorded here is watched by. Reaching for the facts at hand
-- | instead would prove an obligation from assumptions that do not hold where it
-- | arose, and refuse one the assumptions that do hold prove.
assignMeta :: MetaContext -> MetaVar -> XType -> Step
assignMeta ctx m solution =
  case lookupMeta ctx m of
    Just (Unsolved info) ->
      if occursIn m solution then
        Broke (OccursCheck m solution)
      else case escapes info.scope solution of
        Just escaping ->
          Broke (escaping m)
        Nothing -> case kindAgrees ctx m info solution of
          Left err ->
            Broke err
          Right ctxK ->
            case narrowScopes ctxK info.scope solution of
              Left err ->
                Broke err
              Right ctx' ->
                Stepped ctx'
                  { bindings = Map.insert m (Assigned solution) ctx'.bindings
                  , assigned = Set.insert m ctx'.assigned
                  }

    Just (Assigned _) ->
      Broke (MetaAlreadyAssigned m)

    Nothing ->
      Broke (MetaUnbound m)

-- | The kind a solution commits to, unified against the kind of the
-- | metavariable. A solution whose elements give no row element kind away
-- | commits to nothing, and there is nothing to unify.
kindAgrees :: MetaContext -> MetaVar -> MetaInfo -> XType -> Either UnifyError MetaContext
kindAgrees ctx m info solution = case rowKindOf solution of
  Nothing ->
    Right ctx
  Just k -> case unifyKind ctx info.kind k of
    Left _ -> Left (KindMismatch m info.kind k)
    Right ctxK -> Right ctxK

-- | Narrow every metavariable the solution mentions to the scope of the
-- | metavariable being solved, in both classes.
-- |
-- | `escapes` decides the rigid variables a solution mentions **now**, and a
-- | metavariable standing in one mentions none until it is solved. Without this
-- | narrowing, `?α` created outside a binder and solved to a type mentioning
-- | `?β` would admit whatever `?β` was later solved to, binder and all.
-- |
-- | **A narrowed metavariable carries metadata of its own, and that travels
-- | wherever the metavariable does.** Its kind names rigid kind variables and may
-- | hold kind metavariables, so narrowing the scope alone would leave the
-- | metavariable standing at a kind its new scope excludes. Refusing is why this
-- | reports rather than returning a context.
narrowScopes :: MetaContext -> Scope -> XType -> Either UnifyError MetaContext
narrowScopes ctx scope solution =
  -- Substituting first leaves only unsolved metavariables to narrow, so the
  -- fold reaches what a solution stands on rather than what it was written with.
  narrowMetas ctx scope (metasOf substituted) (kindMetasOfType substituted)
  where
  substituted = substitute ctx solution

-- | Narrow the type and kind metavariables given to a scope, as a solution
-- | standing in that scope requires of every metavariable it holds unsolved.
-- |
-- | The caller substitutes first, so what is given is unsolved; a type
-- | metavariable solved already is a caller error.
narrowMetas :: MetaContext -> Scope -> Set MetaVar -> Set KindMetaVar -> Either UnifyError MetaContext
narrowMetas ctx scope typeMetas kindMetas = do
  narrowed <- foldM narrowType ctx types
  foldM (narrowKindTo scope.kinds) narrowed kinds
  where
  types = Set.toUnfoldable typeMetas :: P.Array MetaVar
  kinds = Set.toUnfoldable kindMetas :: P.Array KindMetaVar

  narrowType acc t = case Map.lookup t acc.bindings of
    Just (Unsolved tInfo) ->
      let
        within =
          { types: Set.intersection tInfo.scope.types scope.types
          , kinds: Set.intersection tInfo.scope.kinds scope.kinds
          }

        -- A kind the metavariable stands at may itself be solved, and a rigid
        -- variable reaches the metadata through that solution as readily as it
        -- is written there. Substituting is what brings either into view.
        kind = substituteKind acc tInfo.kind
      in
        case Set.findMin (Set.difference (kindVarsOf kind) within.kinds) of
          Just escaping ->
            Left (EscapingKindVariable t escaping)
          Nothing -> do
            acc' <- foldM (narrowKindTo within.kinds) acc
              (Set.toUnfoldable (kindMetasOf kind) :: P.Array KindMetaVar)
            pure acc'
              { bindings = Map.insert t
                  (Unsolved (tInfo { kind = kind, scope = within }))
                  acc'.bindings
              }

    Just (Assigned _) ->
      Left (MetaAlreadyAssigned t)

    Nothing ->
      Left (MetaUnbound t)

-- | Narrow one kind metavariable against a scope, in the three states the
-- | context can hold it in.
-- |
-- | A solved one is closed rather than skipped: its solution is where a rigid
-- | variable outside the new scope would otherwise sit.
narrowKindTo :: Set KindVar -> MetaContext -> KindMetaVar -> Either UnifyError MetaContext
narrowKindTo scope ctx k = case Map.lookup k ctx.kindBindings of
  Just (KindUnsolved kInfo) ->
    Right ctx
      { kindBindings = Map.insert k
          (KindUnsolved (kInfo { scope = Set.intersection kInfo.scope scope }))
          ctx.kindBindings
      }

  Just (KindAssigned _) ->
    let
      -- Substituting resolves the chain entire, so what remains to narrow is
      -- unsolved and the recursion goes no deeper than that.
      solution = substituteKind ctx (XKMeta k)
    in
      case Set.findMin (Set.difference (kindVarsOf solution) scope) of
        Just escaping ->
          Left (KindEscapingVariable k escaping)
        Nothing ->
          foldM (narrowKindTo scope) ctx
            (Set.toUnfoldable (kindMetasOf solution) :: P.Array KindMetaVar)

  Nothing ->
    Left (KindMetaUnbound k)

-- | Whether a solution mentions anything its metavariable was not created
-- | under, in either class of variable.
escapes :: Scope -> XType -> Maybe (MetaVar -> UnifyError)
escapes scope solution =
  case Set.findMin escaped.types of
    Just a -> Just (\m -> EscapingVariable m a)
    Nothing -> map (\k m -> EscapingKindVariable m k) (Set.findMin escaped.kinds)
  where
  escaped = outOfScope scope solution

-- | away: an element carrying a type belongs to `Row Type`, one carrying an
-- | effect to `Row Effect`. A row of variables alone commits to neither, and
-- | there is nothing to check.
rowKindOf :: XType -> Maybe XKind
rowKindOf ty = case xnf ty of
  Left _ -> Nothing
  Right n -> map entryKind (Array.head (Map.toUnfoldable n.known # map snd :: P.Array XRowEntry))

entryKind :: XRowEntry -> XKind
entryKind = case _ of
  XRowTypeEntry _ _ -> XKRow RowType
  XRowEffectEntry _ _ -> XKRow RowEffect
  XRowLabelledEffectEntry _ _ _ -> XKRow RowEffect
  XRowRegionEntry _ _ -> XKRow RowEffect

domain :: XRowNormalForm -> Set RowKey
domain n = Set.fromFoldable (Map.keys n.known)

derive instance Eq MetaBinding
derive instance Generic MetaBinding _

instance Show MetaBinding where
  show x = genericShow x

derive instance Eq KindRequirement
derive instance Ord KindRequirement
derive instance Generic KindRequirement _

instance Show KindRequirement where
  show = genericShow

derive instance Eq TermBinding
derive instance Generic TermBinding _

instance Show TermBinding where
  show x = genericShow x

derive instance Eq KindMetaBinding
derive instance Generic KindMetaBinding _

instance Show KindMetaBinding where
  show x = genericShow x

derive instance Eq UnifyError
derive instance Generic UnifyError _

instance Show UnifyError where
  show x = genericShow x

derive instance Eq UnifyResult
derive instance Generic UnifyResult _

instance Show UnifyResult where
  show x = genericShow x
