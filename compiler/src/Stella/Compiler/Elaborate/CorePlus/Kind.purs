-- | Kinds of Core⁺, that is, Core's kinds with unsolved holes added.
-- |
-- | Core has no metavariables (D12), so these are a separate type rather than a
-- | widening of `Stella.Compiler.TypedCore.Kind`. Nothing here reaches the Core
-- | type checker except through `toCoreKind`, which fails while a hole remains.
-- |
-- | A rigid kind variable and a flexible one are distinct constructors: `XKVar`
-- | is bound by the kind scheme of the declaration being checked and is never
-- | assignable, while `XKMeta` is a metavariable of `Ψ`.
module Stella.Compiler.Elaborate.CorePlus.Kind
  ( KindMetaVar(..)
  , XKind(..)
  , fromCoreKind
  , toCoreKind
  , kindMetasOf
  , kindVarsOf
  , occursInKind
  ) where

import Prelude

import Prim as P

import Stella.Compiler.TypedCore (Kind(..), KindVar, RowElemKind)
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Set as Set
import Data.Show.Generic (genericShow)

-- | A kind metavariable of `Ψ`. What it was created under lives in the
-- | metavariable context, not here.
newtype KindMetaVar = KindMetaVar P.Int

data XKind
  -- | A rigid kind variable, bound by a declaration's kind scheme (D3).
  = XKVar KindVar
  -- | A flexible metavariable: unification may assign to it.
  | XKMeta KindMetaVar
  | XKType
  | XKEffect
  | XKRow RowElemKind
  | XKFun XKind XKind

fromCoreKind :: Kind -> XKind
fromCoreKind = case _ of
  KVar k -> XKVar k
  KType -> XKType
  KEffect -> XKEffect
  KRow e -> XKRow e
  KFun a b -> XKFun (fromCoreKind a) (fromCoreKind b)

-- | The invariant of the elaboration boundary, at the kind level: a kind handed
-- | to the Core type checker has no hole left.
toCoreKind :: XKind -> Maybe Kind
toCoreKind = case _ of
  XKVar k -> Just (KVar k)
  XKMeta _ -> Nothing
  XKType -> Just KType
  XKEffect -> Just KEffect
  XKRow e -> Just (KRow e)
  XKFun a b -> KFun <$> toCoreKind a <*> toCoreKind b

kindMetasOf :: XKind -> Set KindMetaVar
kindMetasOf = case _ of
  XKVar _ -> Set.empty
  XKMeta m -> Set.singleton m
  XKType -> Set.empty
  XKEffect -> Set.empty
  XKRow _ -> Set.empty
  XKFun a b -> kindMetasOf a <> kindMetasOf b

-- | The kind variables a kind mentions.
-- |
-- | Kind schemes are prenex (D3), so a kind has no binder of its own and every
-- | occurrence is free.
kindVarsOf :: XKind -> Set KindVar
kindVarsOf = case _ of
  XKVar k -> Set.singleton k
  XKMeta _ -> Set.empty
  XKType -> Set.empty
  XKEffect -> Set.empty
  XKRow _ -> Set.empty
  XKFun a b -> kindVarsOf a <> kindVarsOf b

-- | Whether assigning to `m` would make it refer to itself.
occursInKind :: KindMetaVar -> XKind -> P.Boolean
occursInKind m kind = Set.member m (kindMetasOf kind)

derive instance Eq KindMetaVar
derive instance Ord KindMetaVar
derive newtype instance Show KindMetaVar

derive instance Eq XKind
derive instance Ord XKind
derive instance Generic XKind _

instance Show XKind where
  show x = genericShow x
