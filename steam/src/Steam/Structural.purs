-- | A snapshot of a value, as a report answers with one
-- | ([Abstract Machine](../../../docs/technical-references/07-Runtime/01-Abstract-Machine.md)).
-- |
-- | **What a request naming a global is answered with is structural.** A scalar
-- | stands for itself, a
-- | constructor carries the name its declaration gave it, a record carries its keys,
-- | and a closure, a continuation, or an `IO` is what it is and nothing more.
-- |
-- | **The snapshot is not the interpreter's representation.** A `Value` holds
-- | identities, references, and a stack; this holds names and immutable structure,
-- | so it can be printed, compared, or encoded without reaching anything the
-- | interpreter owns. No runtime identity, register, or address appears in one.
-- |
-- | **A snapshot is what a report answers with, and not what every boundary
-- | carries.** A compile-time session passes live values: what a synthesizer is
-- | applied to, what it produces, and the answer to an `Elab` request cross as
-- | handles on what the interpreter holds. A snapshot of one would say only that it
-- | is a value a foreign observes, and nothing could turn it back.
-- |
-- | **Nothing here renders.** Text is a layer above: what a newline, an ellipsis, or
-- | a type-directed form looks like belongs to whoever prints the snapshot
-- | ([Render](Render.purs)).
module Steam.Structural
  ( StructuralValue(..)
  , NumberAtom(..)
  , Field
  , Cut
  , RuntimeNames
  , SnapshotLimits
  , defaultLimits
  , inspect
  , compareKeys
  ) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Steam.Value (CtorId, KeyId, OpId, Value(..))
import Stella.Compiler.Bytecode.Module (Key(..))
import Stella.Compiler.TypedCore.Domain (ScalarString, ScalarValue, codePointOf, compareByScalar, compareNumber, sameNumber, scalarLength, scalarStringOf, scalarsOf, textOf)
import Stella.Compiler.TypedCore.Name (EffName(..), Ident, ModuleName(..), OpName, Qualified(..), RegionName(..), Symbol(..), Tag(..))
import Stella.Compiler.TypedCore.Type (RowKey(..))

-- | A `Number` under the identity of a literal: equality of the bit pattern, with
-- | all NaNs taken as one (D37). The host's `==` decides neither, identifying the
-- | two zeros and separating a NaN from itself.
newtype NumberAtom = NumberAtom P.Number

-- | A field of a record, under the key it stands at.
type Field =
  { key :: RowKey
  , value :: StructuralValue
  }

-- | A sequence a snapshot carries, and whether it is all of it. What the limits cut
-- | short says so here rather than through an element of its own, a record's fields
-- | having no key to hang one on.
type Cut a =
  { items :: P.Array a
  , complete :: P.Boolean
  }

data StructuralValue
  = SInt P.Int
  | SNumber NumberAtom
  | SChar ScalarValue
  -- | The text, and whether it is all of it: a string longer than the limits allow
  -- | is carried as the prefix that fits.
  | SString { text :: ScalarString, complete :: P.Boolean }
  | SBoolean P.Boolean
  -- | A constructor under its fully qualified name, with its fields in the order it
  -- | was applied.
  | SData (Qualified Ident) (Cut StructuralValue)
  -- | The fields of a record, in the order of their keys rather than the order the
  -- | interpreter happened to hold them in.
  | SRecord (Cut Field)
  | SVariant RowKey StructuralValue
  -- | A value applying is the only thing to do with. Nothing under one is reached:
  -- | a capture list, a captured stack, and the inside of an action are the
  -- | interpreter's, and a snapshot that carried them would carry mutable state and
  -- | cycles with them.
  | SClosure
  | SPartialApplication
  | SContinuation
  | SIO
  | SOpaque
  -- | What the limits stopped short of, and what a name the registry does not hold
  -- | leaves behind.
  | STruncated

-- | The way back from an identity to the name it was assigned for, which is what
-- | loading keeps ([Load](Load.purs)).
type RuntimeNames =
  { ctors :: Map CtorId (Qualified Ident)
  , keys :: Map KeyId Key
  , ops :: Map OpId OpName
  }

-- | What bounds a snapshot, so that taking one terminates whatever the value is.
-- |
-- | A value may be deep, wide, or cyclic through a closure nothing here reaches;
-- | exceeding any of these is not an error but a `STruncated` in place of what was
-- | left.
-- | `maxDepth` is how many levels of nesting a snapshot carries, `maxNodes` how
-- | many nodes in all, `maxItems` how many fields or arguments of one value, and
-- | `maxTextUnits` how many scalar values of a string.
-- |
-- | **Each is a count and none of them is negative.** A request carries these, so
-- | one that names a negative is read as naming none of that kind: nothing here
-- | fails on a number, and nothing below sees one.
type SnapshotLimits =
  { maxDepth :: P.Int
  , maxNodes :: P.Int
  , maxItems :: P.Int
  , maxTextUnits :: P.Int
  }

defaultLimits :: SnapshotLimits
defaultLimits =
  { maxDepth: 12
  , maxNodes: 512
  , maxItems: 64
  , maxTextUnits: 1024
  }

-- | What taking a snapshot of one value gave: the value and what is left of the node
-- | budget, or nothing where the budget had no room for it.
data Taken
  = Taken StructuralValue P.Int
  | NotTaken

-- | The canonical order of keys, which is the order a snapshot's fields stand in.
-- |
-- | **A kind decides first**, and within one kind the payload does: a spelling by
-- | scalar value, a position by its number, an effect by its module's name and then
-- | its own. Text is compared by scalar value and **not by what a host holds it in**,
-- | which would make an answer depend on the host.
-- |
-- | `RegionKey` is ordered with the rest and reached by nothing: erasure keeps no
-- | region element, so no value carries one (D36).
compareKeys :: RowKey -> RowKey -> Ordering
compareKeys a b = case compare (kind a) (kind b) of
  EQ -> within a b
  other -> other
  where
  kind :: RowKey -> P.Int
  kind = case _ of
    SymbolKey _ -> 0
    TagKey _ -> 1
    PositionKey _ -> 2
    EffectKey _ -> 3
    RegionKey _ -> 4

  within :: RowKey -> RowKey -> Ordering
  within x y = case x, y of
    SymbolKey (Symbol left), SymbolKey (Symbol right) -> compareByScalar left right
    TagKey (Tag left), TagKey (Tag right) -> compareByScalar left right
    PositionKey left, PositionKey right -> compare left right
    EffectKey left, EffectKey right -> effect left right
    RegionKey (RegionName left), RegionKey (RegionName right) -> compareByScalar left right
    _, _ -> EQ

  effect (Qualified (ModuleName leftModule) (EffName left)) (Qualified (ModuleName rightModule) (EffName right)) =
    case compareByScalar leftModule rightModule of
      EQ -> compareByScalar left right
      other -> other

-- | The snapshot of a value.
inspect :: SnapshotLimits -> RuntimeNames -> Value -> StructuralValue
inspect given names value = case go limits.maxDepth limits.maxNodes value of
  Taken taken _ -> taken
  NotTaken -> STruncated
  where
  limits =
    { maxDepth: atLeastNone given.maxDepth
    , maxNodes: atLeastNone given.maxNodes
    , maxItems: atLeastNone given.maxItems
    , maxTextUnits: atLeastNone given.maxTextUnits
    }

  atLeastNone n = if n < 0 then 0 else n

  -- | **What costs nothing is taken whatever the budget.** A marker stands in place
  -- | of a value rather than being one, so the depth being spent and an identity
  -- | having no name are answered before the budget is looked at; a value the
  -- | snapshot would carry is not taken where the budget is gone.
  -- |
  -- | Naming the identities a value carries is therefore all that happens ahead of
  -- | the budget, and it reads no value under this one.
  go :: P.Int -> P.Int -> Value -> Taken
  go depth nodes v
    | depth <= 0 = marker nodes
    | otherwise = case v of
        VInt n -> paying nodes \_ -> leaf (SInt n) nodes
        VNumber n -> paying nodes \_ -> leaf (SNumber (NumberAtom n)) nodes
        VChar c -> paying nodes \_ -> leaf (SChar c) nodes
        VString s -> paying nodes \_ -> leaf (text s) nodes
        VBoolean b -> paying nodes \_ -> leaf (SBoolean b) nodes
        VClos _ -> paying nodes \_ -> leaf SClosure nodes
        VPap _ -> paying nodes \_ -> leaf SPartialApplication nodes
        VCont _ -> paying nodes \_ -> leaf SContinuation nodes
        VIO _ -> paying nodes \_ -> leaf SIO nodes
        VOpaque _ -> paying nodes \_ -> leaf SOpaque nodes

        VData ctor fields -> case Map.lookup ctor names.ctors of
          Nothing -> marker nodes
          Just name -> paying nodes \_ ->
            let
              capped = Array.take limits.maxItems fields
              taken = sequence (depth - 1) (nodes - 1) capped
            in
              Taken
                ( SData name
                    { items: taken.values
                    , complete: taken.complete && Array.length capped == Array.length fields
                    }
                )
                taken.nodes

        VVariant key payload -> case keyOf key of
          Nothing -> marker nodes
          Just rowKey -> paying nodes \_ -> case go (depth - 1) (nodes - 1) payload of
            Taken inner left -> Taken (SVariant rowKey inner) left
            NotTaken -> Taken (SVariant rowKey STruncated) (nodes - 1)

        VRecord fields -> case named (Map.toUnfoldable fields) of
          Nothing -> marker nodes
          Just entries -> paying nodes \_ ->
            let
              ordered = Array.sortBy (\x y -> compareKeys x.key y.key) entries
              capped = Array.take limits.maxItems ordered
              taken = fieldsOf (depth - 1) (nodes - 1) capped
            in
              Taken
                ( SRecord
                    { items: taken.fields
                    , complete: taken.complete && Array.length capped == Array.length ordered
                    }
                )
                taken.nodes

  -- | A value the snapshot carries, which costs a node of the budget.
  leaf value' nodes = Taken value' (nodes - 1)

  -- | What stands in place of what was not taken. It is the absence of a value rather
  -- | than one, so it spends nothing and is taken whatever is left.
  marker nodes = Taken STruncated nodes

  -- | A value the snapshot would carry, which the budget must have room for. **What
  -- | the value is made of is reached only once the budget has room**, so an
  -- | exhausted budget reads no further into the value it stopped at. It is the
  -- | descent that the budget bounds: the width of the value at hand is read
  -- | whatever is left of it.
  paying :: P.Int -> (Unit -> Taken) -> Taken
  paying nodes build = if nodes <= 0 then NotTaken else build unit

  -- | The text, cut to what the limits allow.
  text s
    | scalarLength s <= limits.maxTextUnits = SString { text: s, complete: true }
    | otherwise = SString { text: prefix s, complete: false }

  -- | The first scalar values of a string, which is what a snapshot of a longer one
  -- | carries.
  prefix s = scalarStringOf (Array.take limits.maxTextUnits (scalarsOf s))

  -- | **The depth is a place and the nodes are a budget.** What the node budget runs
  -- | out on is a tail, so the elements taken are carried and the sequence says it is
  -- | not all of them. The depth stops no sequence: at the limit every value under it
  -- | is a marker, each element among them, and the sequence is still all of what the
  -- | value held.
  sequence depth nodes values = case Array.uncons values of
    Nothing -> { values: [], nodes, complete: true }
    Just { head, tail } -> case go depth nodes head of
      NotTaken -> { values: [], nodes, complete: false }
      Taken first left ->
        let
          rest = sequence depth left tail
        in
          { values: Array.cons first rest.values
          , nodes: rest.nodes
          , complete: rest.complete
          }

  fieldsOf depth nodes entries = case Array.uncons entries of
    Nothing -> { fields: [], nodes, complete: true }
    Just { head, tail } -> case go depth nodes head.value of
      NotTaken -> { fields: [], nodes, complete: false }
      Taken first left ->
        let
          rest = fieldsOf depth left tail
        in
          { fields: Array.cons { key: head.key, value: first } rest.fields
          , nodes: rest.nodes
          , complete: rest.complete
          }

  named entries = traverseFields entries []

  traverseFields entries acc = case Array.uncons entries of
    Nothing -> Just (Array.reverse acc)
    Just { head: Tuple key held, tail } -> case keyOf key of
      Nothing -> Nothing
      Just rowKey -> traverseFields tail (Array.cons { key: rowKey, value: held } acc)

  -- | The key an identity was assigned for. A machine's key is the erased form of a
  -- | row key, and no region key is among them: erasure keeps no region element
  -- | (D36).
  keyOf key = case Map.lookup key names.keys of
    Nothing -> Nothing
    Just (KSymbol symbol) -> Just (SymbolKey symbol)
    Just (KTag tag) -> Just (TagKey tag)
    Just (KPosition i) -> Just (PositionKey i)
    Just (KEffect effect) -> Just (EffectKey effect)

derive instance Eq StructuralValue

-- | Identity of a literal, not the host's equality (D37).
instance Eq NumberAtom where
  eq (NumberAtom a) (NumberAtom b) = sameNumber a b

instance Ord NumberAtom where
  compare (NumberAtom a) (NumberAtom b) = compareNumber a b

instance Show NumberAtom where
  show (NumberAtom n) = show n

instance Show StructuralValue where
  show = case _ of
    SInt n -> "SInt " <> show n
    SNumber n -> "SNumber " <> show n
    SChar c -> "SChar " <> show (codePointOf c)
    SString s -> "SString " <> show (textOf s.text) <> " " <> show s.complete
    SBoolean b -> "SBoolean " <> show b
    SData name fields -> "SData " <> show name <> " " <> show fields.items <> " " <> show fields.complete
    SRecord fields ->
      "SRecord "
        <> show (map (\field -> show field.key <> ": " <> show field.value) fields.items)
        <> " "
        <> show fields.complete
    SVariant key value -> "SVariant " <> show key <> " " <> show value
    SClosure -> "SClosure"
    SPartialApplication -> "SPartialApplication"
    SContinuation -> "SContinuation"
    SIO -> "SIO"
    SOpaque -> "SOpaque"
    STruncated -> "STruncated"
