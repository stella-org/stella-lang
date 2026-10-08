-- | Types of Core⁺, that is, Core's types with unsolved holes added.
-- |
-- | Core has no metavariables (D12), so these are a separate type rather than a
-- | widening of `Stella.Compiler.TypedCore.Type`. Nothing here can reach the Core
-- | type checker except through `toCore`, which fails while a hole remains.
-- |
-- | A rigid variable and a flexible one are distinct constructors: `XVar` is a
-- | type variable of `Γ`, bound by a `forall` and never assignable, while
-- | `XMeta` is a metavariable of `Ψ`.
module Stella.Compiler.Elaborate.CorePlus.Type
  ( MetaVar(..)
  , XType(..)
  , XRowEntry(..)
  , XRowPayload(..)
  , XConstraint(..)
  , xRowEntryKey
  , xRowEntryPayload
  , fromCore
  , fromCoreEntry
  , fromCoreConstraint
  , toCore
  , toCoreConstraint
  , metasOf
  , kindMetasOfType
  , freeRigids
  , freeKindVars
  , freeRegions
  , Scope
  , emptyScope
  , scopeOf
  , outOfScope
  , occursIn
  ) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.CorePlus.Kind (KindMetaVar, XKind, fromCoreKind, kindMetasOf, kindVarsOf, toCoreKind)
import Stella.Compiler.TypedCore (Constraint(..), EffName, KindVar, Qualified, RegionName, RowEntry(..), RowKey(..), Symbol, TyName, TyVar, Type(..))
import Data.Foldable (foldMap)
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Set as Set
import Data.Show.Generic (genericShow)
import Data.Traversable (traverse)

-- | A metavariable of `Ψ`. Its kind and the constraints assumed of it live in
-- | the metavariable context, not here.
newtype MetaVar = MetaVar P.Int

data XType
  -- | A rigid type variable: it can equal only itself.
  = XVar TyVar
  -- | A flexible metavariable: unification may assign to it.
  | XMeta MetaVar
  | XCon (Qualified TyName) (P.Array XKind)
  | XApp XType XType
  | XForall TyVar XKind XType
  | XConstrained XConstraint XType
  | XRowEmpty
  | XRowExtend XRowEntry XType
  | XRowUnion XType XType

-- | An element of a row of Core⁺, in the three forms Core has.
data XRowEntry
  = XRowTypeEntry RowKey XType
  | XRowEffectEntry (Qualified EffName) (P.Array XType)
  | XRowLabelledEffectEntry Symbol (Qualified EffName) (P.Array XType)
  -- | `region ℓ`, the region named `ℓ` being open (D36).
  | XRowRegionEntry RegionName

-- | What an element carries once its key is taken away. Two elements sharing a
-- | key are equal exactly when these are, which is what unification decides.
data XRowPayload
  = XTypePayload XType
  | XEffectPayload (Qualified EffName) (P.Array XType)
  | XRegionPayload RegionName

data XConstraint
  = XLacks RowKey XType
  | XDisjoint XType XType

-- | Keys stay rigid in Core⁺ as well: a structural key is a literal and a
-- | nominal one is the head constructor, so neither depends on how a
-- | metavariable is solved. That is what lets a normal form be computed before
-- | unification finishes.
xRowEntryKey :: XRowEntry -> RowKey
xRowEntryKey = case _ of
  XRowTypeEntry k _ -> k
  XRowEffectEntry e _ -> EffectKey e
  XRowLabelledEffectEntry s _ _ -> SymbolKey s
  XRowRegionEntry name -> RegionKey name

xRowEntryPayload :: XRowEntry -> XRowPayload
xRowEntryPayload = case _ of
  XRowTypeEntry _ ty -> XTypePayload ty
  XRowEffectEntry e args -> XEffectPayload e args
  XRowLabelledEffectEntry _ e args -> XEffectPayload e args
  XRowRegionEntry name -> XRegionPayload name

fromCore :: Type -> XType
fromCore = case _ of
  TVar a -> XVar a
  TCon n kinds -> XCon n (map fromCoreKind kinds)
  TApp f a -> XApp (fromCore f) (fromCore a)
  TForall a k body -> XForall a (fromCoreKind k) (fromCore body)
  TConstrained c body -> XConstrained (fromCoreConstraint c) (fromCore body)
  TRowEmpty -> XRowEmpty
  TRowExtend entry rest -> XRowExtend (fromCoreEntry entry) (fromCore rest)
  TRowUnion l r -> XRowUnion (fromCore l) (fromCore r)

fromCoreEntry :: RowEntry -> XRowEntry
fromCoreEntry = case _ of
  RowTypeEntry k ty -> XRowTypeEntry k (fromCore ty)
  RowEffectEntry e args -> XRowEffectEntry e (map fromCore args)
  RowLabelledEffectEntry s e args -> XRowLabelledEffectEntry s e (map fromCore args)
  RowRegionEntry name -> XRowRegionEntry name

fromCoreConstraint :: Constraint -> XConstraint
fromCoreConstraint = case _ of
  Lacks key row -> XLacks key (fromCore row)
  Disjoint l r -> XDisjoint (fromCore l) (fromCore r)

-- | The invariant of the elaboration boundary: a term handed to the Core type
-- | checker has no hole left. `Nothing` is the unresolved goal that fails
-- | compilation.
toCore :: XType -> Maybe Type
toCore = case _ of
  XVar a -> Just (TVar a)
  XMeta _ -> Nothing
  XCon n kinds -> TCon n <$> traverse toCoreKind kinds
  XApp f a -> TApp <$> toCore f <*> toCore a
  XForall a k body -> TForall a <$> toCoreKind k <*> toCore body
  XConstrained c body -> TConstrained <$> toCoreConstraint c <*> toCore body
  XRowEmpty -> Just TRowEmpty
  XRowExtend entry rest -> TRowExtend <$> toCoreEntry entry <*> toCore rest
  XRowUnion l r -> TRowUnion <$> toCore l <*> toCore r

toCoreEntry :: XRowEntry -> Maybe RowEntry
toCoreEntry = case _ of
  XRowTypeEntry k ty -> RowTypeEntry k <$> toCore ty
  XRowEffectEntry e args -> RowEffectEntry e <$> traverse toCore args
  XRowLabelledEffectEntry s e args -> RowLabelledEffectEntry s e <$> traverse toCore args
  XRowRegionEntry name -> pure (RowRegionEntry name)

toCoreConstraint :: XConstraint -> Maybe Constraint
toCoreConstraint = case _ of
  XLacks key row -> Lacks key <$> toCore row
  XDisjoint l r -> Disjoint <$> toCore l <*> toCore r

-- | Every metavariable occurring anywhere in a type, payloads included. The
-- | occurs check consults this rather than the tail of a normal form alone.
metasOf :: XType -> Set MetaVar
metasOf = case _ of
  XVar _ -> Set.empty
  XMeta m -> Set.singleton m
  XCon _ _ -> Set.empty
  XApp f a -> metasOf f <> metasOf a
  XForall _ _ body -> metasOf body
  XConstrained c body -> constraintMetas c <> metasOf body
  XRowEmpty -> Set.empty
  XRowExtend entry rest -> entryMetas entry <> metasOf rest
  XRowUnion l r -> metasOf l <> metasOf r

entryMetas :: XRowEntry -> Set MetaVar
entryMetas = case _ of
  XRowTypeEntry _ ty -> metasOf ty
  XRowEffectEntry _ args -> foldMap metasOf args
  XRowLabelledEffectEntry _ _ args -> foldMap metasOf args
  XRowRegionEntry _ -> Set.empty

constraintMetas :: XConstraint -> Set MetaVar
constraintMetas = case _ of
  XLacks _ row -> metasOf row
  XDisjoint l r -> metasOf l <> metasOf r

-- | Whether assigning to `m` would make it refer to itself.
occursIn :: MetaVar -> XType -> P.Boolean
occursIn m ty = Set.member m (metasOf ty)

-- | Every kind metavariable occurring anywhere in a type.
-- |
-- | A kind reaches a type through the kind arguments of a constructor and
-- | through the kind a binder introduces, so a type carries unsolved kinds as
-- | readily as it carries unsolved types.
kindMetasOfType :: XType -> Set KindMetaVar
kindMetasOfType = case _ of
  XVar _ -> Set.empty
  XMeta _ -> Set.empty
  XCon _ kinds -> foldMap kindMetasOf kinds
  XApp f a -> kindMetasOfType f <> kindMetasOfType a
  XForall _ k body -> kindMetasOf k <> kindMetasOfType body
  XConstrained c body -> constraintKindMetas c <> kindMetasOfType body
  XRowEmpty -> Set.empty
  XRowExtend entry rest -> entryKindMetas entry <> kindMetasOfType rest
  XRowUnion l r -> kindMetasOfType l <> kindMetasOfType r

entryKindMetas :: XRowEntry -> Set KindMetaVar
entryKindMetas = case _ of
  XRowTypeEntry _ ty -> kindMetasOfType ty
  XRowEffectEntry _ args -> foldMap kindMetasOfType args
  XRowLabelledEffectEntry _ _ args -> foldMap kindMetasOfType args
  XRowRegionEntry _ -> Set.empty

constraintKindMetas :: XConstraint -> Set KindMetaVar
constraintKindMetas = case _ of
  XLacks _ row -> kindMetasOfType row
  XDisjoint l r -> kindMetasOfType l <> kindMetasOfType r

-- | The rigid type variables a type mentions free, payloads and constraints
-- | included.
-- |
-- | A metavariable records the variables that were in scope where it was
-- | created, and a solution may mention no others; without that check, a
-- | variable bound inside a `forall` escapes into a metavariable created
-- | outside it.
freeRigids :: XType -> Set TyVar
freeRigids = go Set.empty
  where
  go bound = case _ of
    XVar a -> if Set.member a bound then Set.empty else Set.singleton a
    XMeta _ -> Set.empty
    XCon _ _ -> Set.empty
    XApp f a -> go bound f <> go bound a
    XForall a _ body -> go (Set.insert a bound) body
    XConstrained c body -> goConstraint bound c <> go bound body
    XRowEmpty -> Set.empty
    XRowExtend entry rest -> goEntry bound entry <> go bound rest
    XRowUnion l r -> go bound l <> go bound r

  goEntry bound = case _ of
    XRowTypeEntry _ ty -> go bound ty
    XRowEffectEntry _ args -> foldMap (go bound) args
    XRowLabelledEffectEntry _ _ args -> foldMap (go bound) args
    XRowRegionEntry _ -> Set.empty

  goConstraint bound = case _ of
    XLacks _ row -> go bound row
    XDisjoint l r -> go bound l <> go bound r

-- | The kind variables a type mentions, which reach it through the kind
-- | arguments of a constructor and through the kind a binder introduces.
-- |
-- | Kind schemes are opened only at a declaration (D3), so there is no binder
-- | here to exclude: every occurrence is free.
freeKindVars :: XType -> Set KindVar
freeKindVars = case _ of
  XVar _ -> Set.empty
  XMeta _ -> Set.empty
  XCon _ kinds -> foldMap kindVarsOf kinds
  XApp f a -> freeKindVars f <> freeKindVars a
  XForall _ k body -> kindVarsOf k <> freeKindVars body
  XConstrained c body -> constraintKindVars c <> freeKindVars body
  XRowEmpty -> Set.empty
  XRowExtend entry rest -> entryKindVars entry <> freeKindVars rest
  XRowUnion l r -> freeKindVars l <> freeKindVars r

entryKindVars :: XRowEntry -> Set KindVar
entryKindVars = case _ of
  XRowTypeEntry _ ty -> freeKindVars ty
  XRowEffectEntry _ args -> foldMap freeKindVars args
  XRowLabelledEffectEntry _ _ args -> foldMap freeKindVars args
  XRowRegionEntry _ -> Set.empty

constraintKindVars :: XConstraint -> Set KindVar
constraintKindVars = case _ of
  XLacks _ row -> freeKindVars row
  XDisjoint l r -> freeKindVars l <> freeKindVars r

-- | `[Γ]`: what a metavariable was created under.
-- |
-- | Every class is tracked: a kind variable of an inner declaration escapes as
-- | readily as a type variable does, and a region name as readily as either.
type Scope =
  { types :: Set TyVar
  , kinds :: Set KindVar
  , regions :: Set RegionName
  }

emptyScope :: Scope
emptyScope = { types: Set.empty, kinds: Set.empty, regions: Set.empty }

scopeOf :: XType -> Scope
scopeOf ty = { types: freeRigids ty, kinds: freeKindVars ty, regions: freeRegions ty }

-- | What a solution mentions but its metavariable was not created under.
outOfScope :: Scope -> XType -> Scope
outOfScope scope solution =
  { types: Set.difference (freeRigids solution) scope.types
  , kinds: Set.difference (freeKindVars solution) scope.kinds
  , regions: Set.difference (freeRegions solution) scope.regions
  }

derive instance Eq MetaVar
derive instance Ord MetaVar
derive newtype instance Show MetaVar

derive instance Eq XType
derive instance Generic XType _

instance Show XType where
  show x = genericShow x

derive instance Eq XRowEntry
derive instance Generic XRowEntry _

instance Show XRowEntry where
  show x = genericShow x

derive instance Eq XRowPayload
derive instance Generic XRowPayload _

instance Show XRowPayload where
  show x = genericShow x

derive instance Eq XConstraint
derive instance Generic XConstraint _

instance Show XConstraint where
  show x = genericShow x

-- | The region names a type mentions, `frn(τ)`: those of its region elements
-- | and of the keys of its rows and constraints. A type binds no region name.
freeRegions :: XType -> Set RegionName
freeRegions = case _ of
  XVar _ -> Set.empty
  XMeta _ -> Set.empty
  XCon _ _ -> Set.empty
  XApp f x -> freeRegions f <> freeRegions x
  XForall _ _ body -> freeRegions body
  XConstrained constraint body -> constraintRegions constraint <> freeRegions body
  XRowEmpty -> Set.empty
  XRowExtend entry rest -> entryRegions entry <> freeRegions rest
  XRowUnion left right -> freeRegions left <> freeRegions right
  where
  constraintRegions = case _ of
    XLacks key row -> keyRegions key <> freeRegions row
    XDisjoint left right -> freeRegions left <> freeRegions right

  entryRegions = case _ of
    XRowTypeEntry key ty -> keyRegions key <> freeRegions ty
    XRowEffectEntry _ args -> foldMap freeRegions args
    XRowLabelledEffectEntry _ _ args -> foldMap freeRegions args
    XRowRegionEntry name -> Set.singleton name

  keyRegions = case _ of
    RegionKey name -> Set.singleton name
    _ -> Set.empty
