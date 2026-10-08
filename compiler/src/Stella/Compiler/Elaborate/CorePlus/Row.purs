-- | Row normal forms over Core⁺.
-- |
-- | The tail is split in two. A rigid variable stands for an unknown the solver
-- | may not touch; a flexible one may be assigned. Keeping them apart in the
-- | type is what stops a case analysis from reading "the tail is not empty" as
-- | "the tail can absorb this", which is the error the Implementation Plan
-- | singles out.
-- |
-- | `known` holds entries rather than payloads, so a key and what it carries
-- | cannot drift apart when a normal form is written back as a row.
module Stella.Compiler.Elaborate.CorePlus.Row
  ( XRowNormalForm
  , XRowError(..)
  , emptyXNormalForm
  , xnf
  , knownKeys
  , rigidTails
  , sharedKey
  , payloadEquations
  , rebuild
  ) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.CorePlus.Type (MetaVar, XRowEntry, XRowPayload(..), XType(..), xRowEntryKey, xRowEntryPayload)
import Stella.Compiler.TypedCore (RowKey, TyVar)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldr)
import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Set as Set
import Data.Show.Generic (genericShow)
import Data.Tuple (Tuple(..))

-- | `⟨ F ; T ⟩` with `T` separated into the part that cannot be solved and the
-- | part that can.
type XRowNormalForm =
  { known :: Map RowKey XRowEntry
  , rigid :: Set TyVar
  , flexible :: Set MetaVar
  }

data XRowError
  = XDuplicateKey RowKey
  | XNotARow XType

emptyXNormalForm :: XRowNormalForm
emptyXNormalForm = { known: Map.empty, rigid: Set.empty, flexible: Set.empty }

-- | The type equations two entries sharing a key impose.
-- |
-- | `Nothing` is a payload mismatch, which no substitution repairs. A key does
-- | not determine the payload: a written key leaves the effect constructor free,
-- | so two entries can share a key and still carry different protocols.
payloadEquations :: XRowEntry -> XRowEntry -> Maybe (P.Array (Tuple XType XType))
payloadEquations e1 e2 = case xRowEntryPayload e1, xRowEntryPayload e2 of
  XTypePayload a, XTypePayload b ->
    Just [ Tuple a b ]

  XEffectPayload n1 as, XEffectPayload n2 bs
    | n1 == n2 && Array.length as == Array.length bs ->
        Just (Array.zip as bs)

  -- A region's payload is its name, which no metavariable stands for: two
  -- agree with no equation when the names are equal, and never otherwise (D36).
  XRegionPayload r1, XRegionPayload r2
    | r1 == r2 -> Just []

  _, _ ->
    Nothing

-- | `nf` over Core⁺.
-- |
-- | A metavariable normalizes into the flexible tail without being looked
-- | through: a solved one is substituted away before normalizing, so reaching
-- | `XMeta` here means it is still unsolved.
-- |
-- | As in Core, the caller establishes that what it passes is a row of one row
-- | element kind. `XNotARow` and `XDuplicateKey` are defensive.
xnf :: XType -> Either XRowError XRowNormalForm
xnf = case _ of
  XRowEmpty ->
    Right emptyXNormalForm

  XVar a ->
    Right (emptyXNormalForm { rigid = Set.singleton a })

  XMeta m ->
    Right (emptyXNormalForm { flexible = Set.singleton m })

  XRowExtend entry rest -> do
    n <- xnf rest
    let key = xRowEntryKey entry
    case Map.lookup key n.known of
      Just _ -> Left (XDuplicateKey key)
      Nothing -> Right (n { known = Map.insert key entry n.known })

  XRowUnion left right -> do
    l <- xnf left
    r <- xnf right
    union l r

  ty ->
    Left (XNotARow ty)

union :: XRowNormalForm -> XRowNormalForm -> Either XRowError XRowNormalForm
union l r =
  case Set.findMin (Set.intersection (domain l) (domain r)) of
    Just shared ->
      Left (XDuplicateKey shared)
    Nothing ->
      Right
        { known: Map.union l.known r.known
        , rigid: Set.union l.rigid r.rigid
        , flexible: Set.union l.flexible r.flexible
        }

domain :: XRowNormalForm -> Set RowKey
domain n = Set.fromFoldable (Map.keys n.known)

-- | The keys of the known part, and the tails no substitution can touch. Every
-- | reading of a normal form that decides a constraint asks for exactly these
-- | two, so they are named once here.
knownKeys :: XRowNormalForm -> P.Array RowKey
knownKeys n = Set.toUnfoldable (domain n)

rigidTails :: XRowNormalForm -> P.Array TyVar
rigidTails n = Set.toUnfoldable n.rigid

-- | A key both known parts carry, which is what makes two rows impossible to
-- | keep apart.
sharedKey :: XRowNormalForm -> XRowNormalForm -> Maybe RowKey
sharedKey l r = Array.head (Array.filter (\key -> Map.member key r.known) (knownKeys l))

-- | A normal form written back as a row, which is how a solution is recorded:
-- | `?s := D ⊎ R ⊎ ?t` is built here.
rebuild :: XRowNormalForm -> XType
rebuild n =
  foldr XRowUnion (foldr XRowUnion knownRow rigidRows) flexibleRows
  where
  knownRow =
    foldr XRowExtend XRowEmpty
      (Map.values n.known)

  rigidRows = map XVar (Set.toUnfoldable n.rigid) :: P.Array XType
  flexibleRows = map XMeta (Set.toUnfoldable n.flexible) :: P.Array XType

derive instance Eq XRowError
derive instance Generic XRowError _

instance Show XRowError where
  show x = genericShow x
