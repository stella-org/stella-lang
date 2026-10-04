-- | A module's interface, assembled from what each stage decides of it.
-- |
-- | **An interface is decided in three places.** Name resolution decides what
-- | the module publishes, what each declaration is, its members, its fixities,
-- | its attributes, and its foreign observations: the **surface part**.
-- | Elaboration decides every Core type in it — schemes, kinds, constructor
-- | fields, synonym bodies, operation signatures, attribute parameter types,
-- | and what an implicit handler handles: the **Core part**. Lowering decides the
-- | arities.
-- |
-- | **The parts are keyed by the declarations**, and assembling them checks
-- | that they speak of one module: each declaration the surface part holds has
-- | its Core entry and no other has one, the two agree on what each is, and a
-- | data type or an effect has as many constructors or operations in both. A
-- | part that disagrees is refused rather than made into an interface.
module Stella.Compiler.Interface.Assemble
  ( SurfaceInterface
  , SurfaceTypeSort(..)
  , CoreInterface
  , CoreTypeSort(..)
  , Table(..)
  , AssembleError(..)
  , surfaceInterface
  , assemble
  ) where

import Prelude
import Prim hiding (Type, Symbol)

import Data.Array as Array
import Data.Either (Either(..))
import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Set as Set
import Data.Show.Generic (genericShow)
import Data.Traversable (for, traverse)
import Data.Tuple (Tuple(..))
import Stella.Compiler.Interface.Module (Attribute, ConstructorEntry, Exports, ModuleInterface, OperatorEntry, TypeEntry, TypeOperatorEntry, TypeSort(..), ValueEntry, ValueSort(..), Via(..))
import Stella.Compiler.TypedCore.Decl (Constant(..))
import Stella.Compiler.Interface.Scheme (Scheme)
import Stella.Compiler.Surface.Decl as Surface
import Stella.Compiler.Surface.Decl (FixityTarget(..))
import Stella.Compiler.Surface.Name (OperatorName(..))
import Stella.Compiler.TypedCore.Kind (KindScheme)
import Stella.Compiler.TypedCore.Name (EffName(..), Ident(..), ModuleName, Qualified(..), TyName(..))
import Stella.Compiler.TypedCore.Type (RowEntry, TyBinder, Type)

-- | What name resolution decides of an interface.
type SurfaceInterface =
  { name :: ModuleName
  , imports :: Array ModuleName
  , exports :: Exports
  , values :: Map Ident { sort :: ValueSort, attributes :: Array Attribute }
  , types :: Map TyName { sort :: SurfaceTypeSort, attributes :: Array Attribute }
  , effects :: Map EffName { operations :: Array Ident, attributes :: Array Attribute }
  , operators :: Map OperatorName OperatorEntry
  , typeOperators :: Map OperatorName TypeOperatorEntry
  -- | Each attribute declaration: how many positional parameters it has, and
  -- | its keyword parameters with their defaults.
  , attributes :: Map Ident { positional :: Int, keyword :: Array { label :: String, default :: Maybe Constant } }
  -- | The handlers declared `implicit`, in the order declared.
  , implicit :: Array Ident
  , catalogOnly :: Set Ident
  }

-- | What a type declaration is, and a data type's constructors in the order
-- | of their tags.
data SurfaceTypeSort
  = SurfaceData { constructors :: Array Ident, isNewtype :: Boolean }
  | SurfaceSynonym
  | SurfaceForeign

-- | What elaboration decides of an interface, keyed as the surface part is.
type CoreInterface =
  { schemes :: Map Ident Scheme
  , types :: Map TyName { kind :: KindScheme, sort :: CoreTypeSort }
  , effects :: Map EffName { params :: Array TyBinder, operations :: Array { binders :: Array TyBinder, arguments :: Array Type, resumesWith :: Type } }
  , attributes :: Map Ident { positional :: Array Type, keyword :: Array Type }
  , implicitHandlers :: Map Ident { source :: RowEntry, targets :: Array RowEntry }
  }

-- | The Core types of a type declaration: a data type's parameters and the
-- | fields of each constructor in the order of their tags, a synonym's
-- | parameters and body, or nothing for a foreign type.
data CoreTypeSort
  = CoreData { params :: Array TyBinder, fields :: Array (Array Type) }
  | CoreSynonym { params :: Array TyBinder, body :: Type }
  | CoreForeign

-- | A table of declarations the two parts are keyed by.
data Table
  = ValueTable
  | TypeTable
  | EffectTable
  | AttributeTable
  | ImplicitHandlerTable

data AssembleError
  -- | A declaration the surface part holds and the Core part does not.
  = CoreMissing Table String
  -- | A Core entry for no declaration the surface part holds.
  | CoreExtra Table String
  -- | A type declaration of one sort in one part and another in the other.
  | TypeSortMismatch TyName
  -- | A data type with as many constructors in one part as the first count
  -- | says, and as many in the other as the second does.
  | ConstructorCount TyName Int Int
  | OperationCount EffName Int Int
  -- | An attribute declaration with as many positional or keyword parameters
  -- | in one part as the first count says, and as many in the other as the
  -- | second does.
  | AttributeParameterCount Ident Int Int
  -- | An arity of a value the module does not declare and export, or one
  -- | below one.
  | ArityNotOwn Ident
  | ArityBelowOne Ident Int

derive instance Eq Table
derive instance Generic Table _

instance Show Table where
  show = genericShow

derive instance Eq AssembleError
derive instance Generic AssembleError _

instance Show AssembleError where
  show = genericShow

derive instance Eq SurfaceTypeSort
derive instance Eq CoreTypeSort

-- | The surface part of the interface of a module resolved without error, and
-- | its exports. A module holding an invalid constant, which only one resolved
-- | with an error does, has none.
surfaceInterface :: Surface.Module -> Exports -> Maybe SurfaceInterface
surfaceInterface m exports = do
  entries <- traverse declaration m.declarations
  pure (Array.foldl add start (Array.concat entries))
  where
  start =
    { name: m.name
    , imports: map _.module m.imports
    , exports
    , values: Map.empty
    , types: Map.empty
    , effects: Map.empty
    , operators: Map.empty
    , typeOperators: Map.empty
    , attributes: Map.empty
    , implicit: []
    , catalogOnly: Set.empty
    }
  add acc = case _ of
    Value k v -> acc { values = Map.insert k v acc.values }
    TypeDecl k v -> acc { types = Map.insert k v acc.types }
    EffectDecl k v -> acc { effects = Map.insert k v acc.effects }
    OperatorDecl k v -> acc { operators = Map.insert k v acc.operators }
    TypeOperatorDecl k v -> acc { typeOperators = Map.insert k v acc.typeOperators }
    AttributeDecl k v -> acc { attributes = Map.insert k v acc.attributes }
    Implicit k -> acc { implicit = Array.snoc acc.implicit k }

-- | What one declaration contributes to the surface part.
data Entry
  = Value Ident { sort :: ValueSort, attributes :: Array Attribute }
  | TypeDecl TyName { sort :: SurfaceTypeSort, attributes :: Array Attribute }
  | EffectDecl EffName { operations :: Array Ident, attributes :: Array Attribute }
  | OperatorDecl OperatorName OperatorEntry
  | TypeOperatorDecl OperatorName TypeOperatorEntry
  | AttributeDecl Ident { positional :: Int, keyword :: Array { label :: String, default :: Maybe Constant } }
  | Implicit Ident

declaration :: Surface.Declaration -> Maybe (Array Entry)
declaration = case _ of
  Surface.DeclValue d -> value d.name SortValue d.attributes
  Surface.DeclComputation d -> value d.name SortValue d.attributes
  Surface.DeclHandler d -> do
    entries <- value d.name SortHandler d.attributes
    pure (entries <> if d.implicit then [ Implicit (local d.name) ] else [])
  Surface.DeclForeign d -> value d.name (SortForeign d.observation) d.attributes
  Surface.DeclData d -> do
    attributes <- traverse attribute d.attributes
    let constructors = map _.name d.constructors
    pure
      ( [ TypeDecl (local d.name) { sort: SurfaceData { constructors: map local constructors, isNewtype: false }, attributes } ]
          <> map (\c -> Value (local c) { sort: SortConstructor d.name, attributes: [] }) constructors
      )
  Surface.DeclNewtype d -> do
    attributes <- traverse attribute d.attributes
    let c = d.constructor.name
    pure
      [ TypeDecl (local d.name) { sort: SurfaceData { constructors: [ local c ], isNewtype: true }, attributes }
      , Value (local c) { sort: SortConstructor d.name, attributes: [] }
      ]
  Surface.DeclSynonym d -> do
    attributes <- traverse attribute d.attributes
    pure [ TypeDecl (local d.name) { sort: SurfaceSynonym, attributes } ]
  Surface.DeclForeignType d -> do
    attributes <- traverse attribute d.attributes
    pure [ TypeDecl (local d.name) { sort: SurfaceForeign, attributes } ]
  Surface.DeclEffect d -> do
    attributes <- traverse attribute d.attributes
    let operations = map _.name d.operations
    pure
      ( [ EffectDecl (local d.name) { operations: map local operations, attributes } ]
          <> map (\o -> Value (local o) { sort: SortOperation d.name, attributes: [] }) operations
      )
  Surface.DeclFixity d ->
    pure [ OperatorDecl d.operator { associativity: d.associativity, precedence: d.precedence, target: d.target } ]
  Surface.DeclTypeFixity d ->
    pure [ TypeOperatorDecl d.operator { associativity: d.associativity, precedence: d.precedence, target: d.target } ]
  Surface.DeclAttribute d -> do
    keyword <- for d.keyword \k -> { label: k.label, default: _ } <$> traverse constant k.default
    pure [ AttributeDecl (local d.name) { positional: Array.length d.positional, keyword } ]
  where
  value name sort attributes = do
    attributes' <- traverse attribute attributes
    pure [ Value (local name) { sort, attributes: attributes' } ]

local :: forall a. Qualified a -> a
local (Qualified _ a) = a

attribute :: Surface.Attribute -> Maybe Attribute
attribute a = do
  positional <- traverse constant a.positional
  keyword <- for a.keyword \k -> { label: k.label, value: _ } <$> constant k.value
  pure { name: a.name, positional, keyword }

constant :: Surface.Constant -> Maybe Constant
constant = case _ of
  Surface.ConstantLiteral _ l -> Just (ConstantLiteral l)
  Surface.ConstantValue _ q -> Just (ConstantValue q)
  Surface.ConstantConstructor _ q cs -> ConstantConstructor q <$> traverse constant cs
  Surface.ConstantRecord _ fs -> ConstantRecord <$> for fs \f -> { label: f.label, value: _ } <$> constant f.value
  Surface.ConstantInvalid _ -> Nothing

-- | The interface the parts make, or where they do not speak of one module.
assemble :: SurfaceInterface -> CoreInterface -> Map Ident Int -> Either AssembleError ModuleInterface
assemble s c arities = do
  sameKeys ValueTable identText s.values c.schemes
  sameKeys TypeTable tyNameText s.types c.types
  sameKeys EffectTable effNameText s.effects c.effects
  sameKeys AttributeTable identText s.attributes c.attributes
  sameKeys ImplicitHandlerTable identText (Map.fromFoldable (map (\h -> Tuple h unit) s.implicit)) c.implicitHandlers
  values <- for (pairs s.values c.schemes) \(Tuple k (Tuple v scheme)) ->
    pure (Tuple k ({ sort: v.sort, scheme, attributes: v.attributes } :: ValueEntry))
  types <- for (pairs s.types c.types) \(Tuple k (Tuple v core)) -> Tuple k <$> typeEntry k v core
  effects <- for (pairs s.effects c.effects) \(Tuple k (Tuple v core)) ->
    if Array.length v.operations /= Array.length core.operations then Left (OperationCount k (Array.length v.operations) (Array.length core.operations))
    else pure
      ( Tuple k
          { params: core.params
          , operations: Array.zipWith (\name o -> { name, binders: o.binders, arguments: o.arguments, resumesWith: o.resumesWith }) v.operations core.operations
          , attributes: v.attributes
          }
      )
  attributes <- for (pairs s.attributes c.attributes) \(Tuple k (Tuple v core)) ->
    if v.positional /= Array.length core.positional then Left (AttributeParameterCount k v.positional (Array.length core.positional))
    else if Array.length v.keyword /= Array.length core.keyword then Left (AttributeParameterCount k (Array.length v.keyword) (Array.length core.keyword))
    else pure (Tuple k { positional: core.positional, keyword: Array.zipWith (\p t -> { label: p.label, type: t, default: p.default }) v.keyword core.keyword })
  implicitHandlers <- for s.implicit \h -> case Map.lookup h c.implicitHandlers of
    Just core -> pure { handler: h, source: core.source, targets: core.targets }
    Nothing -> Left (CoreMissing ImplicitHandlerTable (identText h))
  for_' (Map.toUnfoldable arities :: Array (Tuple Ident Int)) \(Tuple k n) ->
    if not (ownExport k) then Left (ArityNotOwn k)
    else if n < 1 then Left (ArityBelowOne k n)
    else pure unit
  pure
    { name: s.name
    , imports: s.imports
    , exports: s.exports
    , declarations:
        { values: Map.fromFoldable values
        , types: Map.fromFoldable types
        , effects: Map.fromFoldable effects
        , operators: s.operators
        , typeOperators: s.typeOperators
        , attributes: Map.fromFoldable attributes
        }
    , implicitHandlers
    , catalogOnly: s.catalogOnly
    , arities
    }
  where
  -- A value is reached from outside by its name, as a macro by its name in the
  -- macro namespace, or through an operator the module declares and exports.
  ownExport name = Map.member name s.values && (declaredIn s.exports.values || declaredIn s.exports.macros || throughOperator)
    where
    declaredIn table = case Map.lookup (identText name) table of
      Just { entity: Qualified m n, via: Declared } -> m == s.name && n == name
      _ -> false
    throughOperator = Array.any exportedTarget (Map.toUnfoldable s.operators :: Array (Tuple OperatorName OperatorEntry))
    exportedTarget (Tuple op entry) = case entry.target of
      FixityValue (Qualified m n) | m == s.name && n == name -> case Map.lookup (operatorText op) s.exports.operators of
        Just { entity: Qualified m' o, via: Declared } -> m' == s.name && o == op
        _ -> false
      _ -> false

  typeEntry k v core = case v.sort, core.sort of
    SurfaceData d, CoreData cd
      | Array.length d.constructors /= Array.length cd.fields ->
          Left (ConstructorCount k (Array.length d.constructors) (Array.length cd.fields))
      | otherwise ->
          let
            constructors :: Array ConstructorEntry
            constructors = Array.zipWith { name: _, fields: _ } d.constructors cd.fields
          in
            pure (entry (DataType { params: cd.params, constructors, isNewtype: d.isNewtype }))
    SurfaceSynonym, CoreSynonym cs -> pure (entry (Synonym cs))
    SurfaceForeign, CoreForeign -> pure (entry ForeignType)
    _, _ -> Left (TypeSortMismatch k)
    where
    entry :: TypeSort -> TypeEntry
    entry sort = { kind: core.kind, sort, attributes: v.attributes }

-- | Both parts hold one key set for a table.
sameKeys :: forall k a b. Ord k => Table -> (k -> String) -> Map k a -> Map k b -> Either AssembleError Unit
sameKeys table spelling surface core =
  case Array.find (\k -> not (Map.member k core)) (keys surface), Array.find (\k -> not (Map.member k surface)) (keys core) of
    Just k, _ -> Left (CoreMissing table (spelling k))
    _, Just k -> Left (CoreExtra table (spelling k))
    Nothing, Nothing -> Right unit
  where
  keys :: forall v. Map k v -> Array k
  keys = Array.fromFoldable <<< Map.keys

-- | The entries of two maps of one key set, together.
pairs :: forall k a b. Ord k => Map k a -> Map k b -> Array (Tuple k (Tuple a b))
pairs a b = Array.mapMaybe (\(Tuple k x) -> Tuple k <<< Tuple x <$> Map.lookup k b) (Map.toUnfoldable a)

for_' :: forall a. Array a -> (a -> Either AssembleError Unit) -> Either AssembleError Unit
for_' xs f = void (traverse f xs)

operatorText :: OperatorName -> String
operatorText (OperatorName o) = o

identText :: Ident -> String
identText (Ident n) = n

tyNameText :: TyName -> String
tyNameText (TyName n) = n

effNameText :: EffName -> String
effNameText (EffName n) = n
