-- | Types, rows, and row constraints of Typed Core.
-- |
-- | The type grammar has application but no abstraction, so Core lies between
-- | System F and System Fω (D1) and type equality is syntactic apart from row
-- | normalization.
module Stella.Compiler.TypedCore.Type
  ( Type(..)
  , RowEntry(..)
  , RowKey(..)
  , RowPayload(..)
  , Constraint(..)
  , TyBinder
  , TypeScheme
  , rowEntryKey
  , rowEntryPayload
  , substituteType
  , substituteConstraint
  , substituteKindsInType
  , freeTypeVars
  ) where

import Prelude

-- `Prim` is imported qualified, which replaces its implicit open import. Core's
-- own `Type` and `Constraint` would otherwise shadow the `Prim` names of those
-- spellings.
import Prim as P

import Stella.Compiler.TypedCore.Kind (Kind, Scheme, substituteKind)
import Stella.Compiler.TypedCore.Name (EffName, KindVar, Qualified, Symbol, Tag, TyName, TyVar(..))
import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Foldable (foldMap)
import Data.Set (Set)
import Data.Set as Set
import Data.Show.Generic (genericShow)

-- | A type, written `τ`, `σ`, or `ρ`.
-- |
-- | Rows are types: `TRowEmpty`, `TRowExtend`, and `TRowUnion` are the three row
-- | operators Core has (D6). A function type is an application of the type
-- | constructor `Prim.Function`; Core has no arrow syntax.
data Type
  = TVar TyVar
  -- | A type constructor with its kind scheme instantiated, `T [[κ̄]]`. The
  -- | array is empty where the scheme is.
  | TCon (Qualified TyName) (P.Array Kind)
  | TApp Type Type
  | TForall TyVar Kind Type
  -- | Constraint abstraction, `C => τ`, erased at run time.
  | TConstrained Constraint Type
  -- | The empty row, `()`.
  | TRowEmpty
  -- | Row extension, `( ent | ρ )`. Well-kindedness requires the entry's key to
  -- | be absent from the tail, which is what makes rows sharp (D4).
  | TRowExtend RowEntry Type
  -- | Row union, `ρ1 ⊎ ρ2`, well-kinded only where the two are disjoint.
  | TRowUnion Type Type

-- | An element of a row.
-- |
-- | Every element is a key together with a payload. At `Row Type` the key is
-- | written; at `Row Effect` it is derived from the effect at the head of the
-- | payload unless a `Symbol` is written for it.
data RowEntry
  -- | `k : τ` — an element of a `Row Type`. The key is written, and any
  -- | structural key may stand there; which one a structure conventionally
  -- | uses is settled by the surface, not by kinding.
  = RowTypeEntry RowKey Type
  -- | `E τ̄` — an element of a `Row Effect` whose key is derived from the
  -- | effect at the head of its payload.
  | RowEffectEntry (Qualified EffName) (P.Array Type)
  -- | `SymbolKey s : E τ̄` — the same, with a key written for it. This is what
  -- | lets one effect appear twice in a row.
  | RowLabelledEffectEntry Symbol (Qualified EffName) (P.Array Type)
  -- | `region r ι` — the region a handler owns, its variable and the row of its
  -- | cells. It names no declaration, which is why nothing can declare one and
  -- | why the rules that read a payload for an effect find nothing to read.
  | RowRegionEntry Type Type

-- | The key of a row element. Keys are rigid — independent of metavariable
-- | solving — which is what makes row equality decidable (D13, D16).
-- | Three of these are **structural**, decided by the syntax that writes them,
-- | and one is **nominal**, decided by a declaration in `Σ`. The row theory
-- | tells them apart nowhere: to normalization, equality, and entailment all
-- | four are rigid keys that compare for equality. Only well-formedness looks,
-- | since only an `EffectKey` sends the checker to `Σ`.
data RowKey
  = SymbolKey Symbol
  | TagKey Tag
  -- | A tuple component, 0-origin. Elaborating a tuple derives it from where
  -- | the component stands (D13).
  | PositionKey P.Int
  | EffectKey (Qualified EffName)
  -- | A handler's region of cells (D36). No source syntax writes it: only a
  -- | handler's `cells` produces one, which is what keeps a region from being
  -- | discharged by anything but the `handle` that owns it. There is one such
  -- | key, so a sharp row holds at most one region.
  | RegionKey

-- | What an element carries once its key is taken away.
-- |
-- | At `Row Type` that is the type; at `Row Effect` it is an application of a
-- | declared effect constructor, and **the payload is what decides the
-- | protocol** — a `perform` reads its operation's signature from `E`, never
-- | from the key.
data RowPayload
  = TypePayload Type
  | EffectPayload (Qualified EffName) (P.Array Type)
  -- | A region carries no effect application, so no operation is looked up
  -- | through it and no handler may write one (D36).
  | RegionPayload Type Type

rowEntryKey :: RowEntry -> RowKey
rowEntryKey = case _ of
  RowTypeEntry k _ -> k
  RowEffectEntry e _ -> EffectKey e
  RowLabelledEffectEntry s _ _ -> SymbolKey s
  RowRegionEntry _ _ -> RegionKey

rowEntryPayload :: RowEntry -> RowPayload
rowEntryPayload = case _ of
  RowTypeEntry _ ty -> TypePayload ty
  RowEffectEntry e args -> EffectPayload e args
  RowLabelledEffectEntry _ e args -> EffectPayload e args
  RowRegionEntry var cells -> RegionPayload var cells

-- | Instantiate type variables, all at once: what a variable is replaced by is
-- | not substituted into again, so `{a := b, b := a}` swaps the two.
-- |
-- | **No binder captures a variable of what is substituted in.** A `forall`
-- | shadows the variable it binds, which the substitution then leaves alone
-- | beneath it; and a `forall` binding a variable free in what is substituted
-- | is renamed first, to the variable's name followed by the least number
-- | that clashes with nothing in scope, so the result is the same type up to
-- | the names of its binders. Core gives no binder a name unique across a
-- | module: a scheme is instantiated at the variables of whatever term uses it.
substituteType :: Map TyVar Type -> Type -> Type
substituteType sub = goType sub

substituteConstraint :: Map TyVar Type -> Constraint -> Constraint
substituteConstraint sub = goConstraintIn sub

goType :: Map TyVar Type -> Type -> Type
goType sub ty
  | Map.isEmpty sub = ty
  | otherwise = case ty of
      TVar a -> fromMaybe (TVar a) (Map.lookup a sub)
      TCon name kinds -> TCon name kinds
      TApp f x -> TApp (goType sub f) (goType sub x)
      TForall a kind body ->
        let
          inner = Map.delete a sub
          substituted = foldMap freeTypeVars (Map.values inner)
        in
          if Set.member a substituted then
            let
              renamed = freshVar (substituted <> freeTypeVars body <> Set.fromFoldable (Map.keys inner)) a
            in
              TForall renamed kind (goType (Map.insert a (TVar renamed) inner) body)
          else TForall a kind (goType inner body)
      TConstrained constraint body -> TConstrained (goConstraintIn sub constraint) (goType sub body)
      TRowEmpty -> TRowEmpty
      TRowExtend entry rest -> TRowExtend (goEntryIn sub entry) (goType sub rest)
      TRowUnion left right -> TRowUnion (goType sub left) (goType sub right)

goConstraintIn :: Map TyVar Type -> Constraint -> Constraint
goConstraintIn sub = case _ of
  Lacks key row -> Lacks key (goType sub row)
  Disjoint left right -> Disjoint (goType sub left) (goType sub right)

goEntryIn :: Map TyVar Type -> RowEntry -> RowEntry
goEntryIn sub = case _ of
  RowTypeEntry key ty -> RowTypeEntry key (goType sub ty)
  RowEffectEntry name args -> RowEffectEntry name (map (goType sub) args)
  RowLabelledEffectEntry s name args -> RowLabelledEffectEntry s name (map (goType sub) args)
  RowRegionEntry var cells -> RowRegionEntry (goType sub var) (goType sub cells)

-- | The variable's name followed by the least number that names nothing given.
freshVar :: Set TyVar -> TyVar -> TyVar
freshVar taken (TyVar base) = go 1
  where
  go n =
    let
      candidate = TyVar (base <> show n)
    in
      if Set.member candidate taken then go (n + 1) else candidate

-- | Instantiate the kind variables a declaration's scheme binds, which is what
-- | `M.x [[κ̄]]` asks for. Kinds reach a type through the arguments of a
-- | constructor and through the binder of a `forall`.
substituteKindsInType :: Map KindVar Kind -> Type -> Type
substituteKindsInType sub = go
  where
  go = case _ of
    TVar a -> TVar a
    TCon name kinds -> TCon name (map (substituteKind sub) kinds)
    TApp f x -> TApp (go f) (go x)
    TForall a kind body -> TForall a (substituteKind sub kind) (go body)
    TConstrained constraint body -> TConstrained (goConstraint constraint) (go body)
    TRowEmpty -> TRowEmpty
    TRowExtend entry rest -> TRowExtend (goEntry entry) (go rest)
    TRowUnion left right -> TRowUnion (go left) (go right)

  goConstraint = case _ of
    Lacks key row -> Lacks key (go row)
    Disjoint left right -> Disjoint (go left) (go right)

  goEntry = case _ of
    RowTypeEntry key ty -> RowTypeEntry key (go ty)
    RowEffectEntry name args -> RowEffectEntry name (map go args)
    RowLabelledEffectEntry s name args -> RowLabelledEffectEntry s name (map go args)
    RowRegionEntry var cells -> RowRegionEntry (go var) (go cells)

-- | A row constraint. Core has exactly two, and neither carries run-time
-- | content: the checker re-derives entailment rather than accepting a proof
-- | term (D5).
data Constraint
  -- | `k ∉ ρ`
  = Lacks RowKey Type
  -- | `ρ1 # ρ2`
  | Disjoint Type Type

-- | A type variable together with the kind it is introduced at. Every such site
-- | requires a quantifiable kind (D24).
type TyBinder =
  { name :: TyVar
  , kind :: Kind
  }

-- | The declared type of a value, foreign, or data constructor, `forall k̄. σ`.
type TypeScheme = Scheme Type

-- | Structural equality of the syntax. This is not the type equality `≡` of the
-- | specification, which compares rows by their normal form.
derive instance Eq Type
derive instance Ord Type
derive instance Generic Type _

instance Show Type where
  show x = genericShow x

derive instance Eq RowEntry
derive instance Ord RowEntry
derive instance Generic RowEntry _

instance Show RowEntry where
  show x = genericShow x

derive instance Eq RowKey
derive instance Ord RowKey
derive instance Generic RowKey _

instance Show RowKey where
  show = genericShow

derive instance Eq RowPayload
derive instance Ord RowPayload
derive instance Generic RowPayload _

instance Show RowPayload where
  show x = genericShow x

derive instance Eq Constraint
derive instance Ord Constraint
derive instance Generic Constraint _

instance Show Constraint where
  show x = genericShow x

-- | The type variables a type mentions free, payloads and constraints included.
-- |
-- | `r ∉ ftv(β) ∪ ftv(ρ)` is what keeps a region from outliving the `handle`
-- | that owns it (D36): every way to reach a cell mentions the region, so a
-- | closure over a `readCell` carries it in its own arrow and this rejects it
-- | where it would become the answer or join the residual row.
freeTypeVars :: Type -> Set TyVar
freeTypeVars = go Set.empty
  where
  go bound = case _ of
    TVar a -> if Set.member a bound then Set.empty else Set.singleton a
    TCon _ _ -> Set.empty
    TApp f x -> go bound f <> go bound x
    TForall a _ body -> go (Set.insert a bound) body
    TConstrained constraint body -> goConstraint bound constraint <> go bound body
    TRowEmpty -> Set.empty
    TRowExtend entry rest -> goEntry bound entry <> go bound rest
    TRowUnion left right -> go bound left <> go bound right

  goConstraint bound = case _ of
    Lacks _ row -> go bound row
    Disjoint left right -> go bound left <> go bound right

  goEntry bound = case _ of
    RowTypeEntry _ ty -> go bound ty
    RowEffectEntry _ args -> foldMap (go bound) args
    RowLabelledEffectEntry _ _ args -> foldMap (go bound) args
    RowRegionEntry var cells -> go bound var <> go bound cells
