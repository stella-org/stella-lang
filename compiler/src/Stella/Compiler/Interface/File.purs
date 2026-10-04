-- | The `.dmi` file: a module's interface, as bytes
-- | ([Interface](../../../../docs/technical-references/05-Backend/03-Interface.md)).
-- |
-- | **It holds the whole interface**: what the module publishes, every
-- | declaration with its Core types, its implicit handlers, what it publishes
-- | to the catalog alone, and its arities. Beside it the file holds what is
-- | about the file rather than the module, a build hash where one was computed.
-- |
-- | **The layout is the `.dmo`'s**: a header, then the string table, then one
-- | section per table in ascending order of id. Every name is an index into the
-- | string table, which is in order of first use, the sections written in the
-- | order of their ids. A map is written in ascending order of its keys by
-- | scalar value, and a reader refuses one that does not ascend, so one
-- | interface has one file.
-- |
-- | **A reader checks the bytes, not the interface.** A tag it does not know, an
-- | index outside the string table, a map out of order, and an arity below one
-- | are refused; whether a type is well kinded, or an export names a
-- | declaration that exists, is not this file's to say.
module Stella.Compiler.Interface.File
  ( StoredInterface
  , magic
  , formatVersion
  , encode
  , decode
  ) where

import Prelude
import Prim hiding (Type, Constraint, Symbol)

import Prim as P

import Data.Array as Array
import Data.Either (Either)
import Data.Foldable (traverse_)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Data.Tuple (Tuple(..))
import Stella.Compiler.Bytecode.Bytes (Bytes, DecodeError(..), EncodeError(..), R, TagKind(..), byte, expect, f64, f64R, runR, structuralR, svar, svarR, takeR, throwR, u8, utf8, uvar, uvarR, vecR)
import Stella.Compiler.Bytecode.Container (E, Strings, qname, qnameR, runE, section, str, strR, strings, text, throwE, vec)
import Stella.Compiler.Bytecode.Container as C
import Stella.Compiler.Bytecode.Module (abiVersion)
import Stella.Compiler.Interface.Module (Attribute, AttributeEntry, Constant(..), Declarations, EffectEntry, Export, Exports, ImplicitHandler, ModuleInterface, OperatorEntry, TypeEntity(..), TypeEntry, TypeExport, TypeOperatorEntry, TypeSort(..), ValueEntry, ValueSort(..), Via(..))
import Stella.Compiler.Interface.Scheme (Scheme, SchemeBody(..))
import Stella.Compiler.Surface.Decl (Associativity(..), FixityTarget(..), Observation(..))
import Stella.Compiler.Surface.Name (OperatorName(..))
import Stella.Compiler.Surface.Type (TypeOperatorTarget(..))
import Stella.Compiler.TypedCore.Domain (codePointOf, compareByScalar, scalarString, scalarValue, textOf)
import Stella.Compiler.TypedCore.Kind (Kind(..), KindScheme, RowElemKind(..))
import Stella.Compiler.TypedCore.Name (EffName(..), Ident(..), KindVar(..), ModuleName(..), Symbol(..), Tag(..), TyName(..), TyVar(..))
import Stella.Compiler.TypedCore.Signature (CanonicalClass(..))
import Stella.Compiler.TypedCore.Term (Literal(..))
import Stella.Compiler.TypedCore.Type (Constraint(..), RowEntry(..), RowKey(..), TyBinder, Type(..))

-- | An interface as a file holds it: the interface, and the build hash of the
-- | module, where one was computed. What the hash is computed from is not
-- | settled, so the file carries it as bytes it does not read.
type StoredInterface =
  { interface :: ModuleInterface
  , buildHash :: Maybe Bytes
  }

-- | `"DMI\0"`, the four bytes a `.dmi` begins with.
magic :: Bytes
magic = [ 0x44, 0x4D, 0x49, 0x00 ]

-- | The version of the format this module reads and writes.
formatVersion :: P.Int
formatVersion = 1

-- Sections -------------------------------------------------------------------------

sectionStrings :: P.Int
sectionStrings = 0x01

sectionModule :: P.Int
sectionModule = 0x02

sectionImports :: P.Int
sectionImports = 0x03

sectionExports :: P.Int
sectionExports = 0x04

sectionValues :: P.Int
sectionValues = 0x05

sectionTypes :: P.Int
sectionTypes = 0x06

sectionEffects :: P.Int
sectionEffects = 0x07

sectionOperators :: P.Int
sectionOperators = 0x08

sectionTypeOperators :: P.Int
sectionTypeOperators = 0x09

sectionAttributes :: P.Int
sectionAttributes = 0x0A

sectionImplicitHandlers :: P.Int
sectionImplicitHandlers = 0x0B

sectionCatalogOnly :: P.Int
sectionCatalogOnly = 0x0C

sectionArities :: P.Int
sectionArities = 0x0D

-- | The build hash, which says nothing of the module and is skippable.
sectionBuildHash :: P.Int
sectionBuildHash = 0x70

layout :: C.Layout
layout =
  { skippableFrom: 0x70
  , required:
      [ sectionStrings
      , sectionModule
      , sectionImports
      , sectionExports
      , sectionValues
      , sectionTypes
      , sectionEffects
      , sectionOperators
      , sectionTypeOperators
      , sectionAttributes
      , sectionImplicitHandlers
      , sectionCatalogOnly
      , sectionArities
      ]
  }

-- Writing --------------------------------------------------------------------------

-- | **What this writes, a decoder returns.** An arity below one is refused
-- | rather than written, absence being what a value without one has, and so is
-- | a count below zero and a name no reader could read.
encode :: StoredInterface -> Either EncodeError Bytes
encode stored = do
  abi <- utf8 abiVersion
  Tuple sections table <- runE { indices: Map.empty, strings: [] } (sectionsOf stored.interface)
  stringTable <- strings table.strings
  pure
    ( magic
        <> uvar formatVersion
        <> uvar 0
        <> uvar (Array.length abi)
        <> abi
        <> section sectionStrings stringTable
        <> sections
        <> case stored.buildHash of
          Just hash -> section sectionBuildHash (uvar (Array.length hash) <> hash)
          Nothing -> []
    )

sectionsOf :: ModuleInterface -> E Bytes
sectionsOf i = do
  name <- moduleName i.name
  imports <- vec moduleName i.imports
  exports <- exportsE i.exports
  values <- mapE identText valueEntry i.declarations.values
  types <- mapE tyNameText typeEntry i.declarations.types
  effects <- mapE effNameText effectEntry i.declarations.effects
  operators <- mapE operatorText operatorEntry i.declarations.operators
  typeOperators <- mapE operatorText typeOperatorEntry i.declarations.typeOperators
  attributes <- mapE identText attributeEntry i.declarations.attributes
  implicit <- vec implicitHandler i.implicitHandlers
  catalogOnly <- vec (str <<< identText) (Array.sortBy (\a b -> compareByScalar (identText a) (identText b)) (Set.toUnfoldable i.catalogOnly))
  arities <- vec arity (Array.sortBy (\(Tuple a _) (Tuple b _) -> compareByScalar (identText a) (identText b)) (Map.toUnfoldable i.arities))
  pure
    ( section sectionModule name
        <> section sectionImports imports
        <> section sectionExports exports
        <> section sectionValues values
        <> section sectionTypes types
        <> section sectionEffects effects
        <> section sectionOperators operators
        <> section sectionTypeOperators typeOperators
        <> section sectionAttributes attributes
        <> section sectionImplicitHandlers implicit
        <> section sectionCatalogOnly catalogOnly
        <> section sectionArities arities
    )
  where
  arity (Tuple name n)
    | n < 1 = throwE (ArityBelowOne name n)
    | otherwise = (_ <> uvar n) <$> str (identText name)

-- | A map, each key as its spelling then its value, in ascending order of the
-- | spelling by scalar value.
mapE :: forall k v. (k -> P.String) -> (v -> E Bytes) -> Map k v -> E Bytes
mapE spelling value m = vec entry (Array.sortBy order (Map.toUnfoldable m))
  where
  order (Tuple a _) (Tuple b _) = compareByScalar (spelling a) (spelling b)
  entry (Tuple k v) = do
    key <- str (spelling k)
    written <- value v
    pure (key <> written)

moduleName :: ModuleName -> E Bytes
moduleName (ModuleName m) = str m

identText :: Ident -> P.String
identText (Ident s) = s

tyNameText :: TyName -> P.String
tyNameText (TyName s) = s

effNameText :: EffName -> P.String
effNameText (EffName s) = s

operatorText :: OperatorName -> P.String
operatorText (OperatorName s) = s

optional :: forall a. (a -> E Bytes) -> Maybe a -> E Bytes
optional item = case _ of
  Nothing -> pure (u8 0)
  Just a -> (u8 1 <> _) <$> item a

boolean :: P.Boolean -> Bytes
boolean b = u8 (if b then 1 else 0)

count :: P.Int -> E Bytes
count n
  | n < 0 = throwE (CountBelowZero n)
  | otherwise = pure (uvar n)

exportsE :: Exports -> E Bytes
exportsE e = do
  values <- mapE identity (export (qname identText)) e.values
  types <- mapE identity typeExport e.types
  operators <- mapE identity (export (qname operatorText)) e.operators
  typeOperators <- mapE identity (export (qname operatorText)) e.typeOperators
  macros <- mapE identity (export (qname identText)) e.macros
  attributes <- mapE identity (export (qname identText)) e.attributes
  modules <- vec moduleName e.modules
  pure (values <> types <> operators <> typeOperators <> macros <> attributes <> modules)

export :: forall a. (a -> E Bytes) -> Export a -> E Bytes
export entity x = (<>) <$> entity x.entity <*> via x.via

via :: Via -> E Bytes
via = case _ of
  Declared -> pure (u8 0)
  ThroughImport m -> (u8 1 <> _) <$> moduleName m

typeExport :: TypeExport -> E Bytes
typeExport x = do
  entity <- case x.entity of
    TypeEntity q -> (u8 0 <> _) <$> qname tyNameText q
    EffectEntity q -> (u8 1 <> _) <$> qname effNameText q
  v <- via x.via
  members <- vec (str <<< identText) x.members
  pure (entity <> v <> members)

valueEntry :: ValueEntry -> E Bytes
valueEntry v = do
  sort <- case v.sort of
    SortValue -> pure (u8 0)
    SortForeign o -> pure (u8 1 <> observation o)
    SortHandler -> pure (u8 2)
    SortConstructor q -> (u8 3 <> _) <$> qname tyNameText q
    SortOperation q -> (u8 4 <> _) <$> qname effNameText q
  s <- scheme v.scheme
  attributes <- vec attribute v.attributes
  pure (sort <> s <> attributes)

observation :: Observation -> Bytes
observation = case _ of
  MayObserve -> u8 0
  ObservesNone -> u8 1

typeEntry :: TypeEntry -> E Bytes
typeEntry t = do
  k <- kindScheme t.kind
  sort <- case t.sort of
    DataType d -> do
      params <- vec tyBinder d.params
      constructors <- vec (\c -> (<>) <$> str (identText c.name) <*> vec type_ c.fields) d.constructors
      pure (u8 0 <> params <> constructors <> boolean d.isNewtype)
    Synonym s -> do
      params <- vec tyBinder s.params
      b <- type_ s.body
      pure (u8 1 <> params <> b)
    ForeignType -> pure (u8 2)
    Intrinsic c -> pure (u8 3 <> canonicalClass c)
  attributes <- vec attribute t.attributes
  pure (k <> sort <> attributes)

canonicalClass :: CanonicalClass -> Bytes
canonicalClass = u8 <<< case _ of
  CanonicalLiteral -> 0
  CanonicalFunction -> 1
  CanonicalRecord -> 2
  CanonicalVariant -> 3
  CanonicalOpaque -> 4

effectEntry :: EffectEntry -> E Bytes
effectEntry e = do
  params <- vec tyBinder e.params
  operations <- vec operation e.operations
  attributes <- vec attribute e.attributes
  pure (params <> operations <> attributes)
  where
  operation o = do
    name <- str (identText o.name)
    binders <- vec tyBinder o.binders
    arguments <- vec type_ o.arguments
    resumesWith <- type_ o.resumesWith
    pure (name <> binders <> arguments <> resumesWith)

associativity :: Associativity -> Bytes
associativity = u8 <<< case _ of
  AssociateNone -> 0
  AssociateLeft -> 1
  AssociateRight -> 2

operatorEntry :: OperatorEntry -> E Bytes
operatorEntry o = do
  precedence <- count o.precedence
  target <- case o.target of
    FixityValue q -> (u8 0 <> _) <$> qname identText q
    FixityConstructor q -> (u8 1 <> _) <$> qname identText q
  pure (associativity o.associativity <> precedence <> target)

typeOperatorEntry :: TypeOperatorEntry -> E Bytes
typeOperatorEntry o = do
  precedence <- count o.precedence
  target <- case o.target of
    TargetTypeConstructor q -> (u8 0 <> _) <$> qname tyNameText q
    TargetTypeSynonym q -> (u8 1 <> _) <$> qname tyNameText q
    TargetEffect q -> (u8 2 <> _) <$> qname effNameText q
  pure (associativity o.associativity <> precedence <> target)

attributeEntry :: AttributeEntry -> E Bytes
attributeEntry a = do
  positional <- vec type_ a.positional
  keyword <- vec
    ( \k -> do
        label <- str k.label
        t <- type_ k.type
        d <- optional constant k.default
        pure (label <> t <> d)
    )
    a.keyword
  pure (positional <> keyword)

attribute :: Attribute -> E Bytes
attribute a = do
  name <- qname identText a.name
  positional <- vec constant a.positional
  keyword <- vec (\k -> (<>) <$> str k.label <*> constant k.value) a.keyword
  pure (name <> positional <> keyword)

constant :: Constant -> E Bytes
constant = case _ of
  ConstantLiteral l -> (u8 0 <> _) <$> literal l
  ConstantValue q -> (u8 1 <> _) <$> qname identText q
  ConstantConstructor q cs -> do
    name <- qname identText q
    args <- vec constant cs
    pure (u8 2 <> name <> args)
  ConstantRecord fs -> (u8 3 <> _) <$> vec (\f -> (<>) <$> str (symbolText f.label) <*> constant f.value) fs

literal :: Literal -> E Bytes
literal = case _ of
  LitInt n -> pure (u8 0 <> svar n)
  LitNumber x -> pure (u8 1 <> f64 x)
  LitString s -> (u8 2 <> _) <$> str (textOf s)
  LitChar c -> pure (u8 3 <> uvar (codePointOf c))
  LitBoolean b -> pure (u8 4 <> boolean b)

implicitHandler :: ImplicitHandler -> E Bytes
implicitHandler h = do
  name <- str (identText h.handler)
  source <- rowEntry h.source
  targets <- vec rowEntry h.targets
  pure (name <> source <> targets)

symbolText :: Symbol -> P.String
symbolText (Symbol s) = s

-- Types ------------------------------------------------------------------------------

kind :: Kind -> E Bytes
kind = case _ of
  KVar (KindVar v) -> (u8 0 <> _) <$> str v
  KType -> pure (u8 1)
  KEffect -> pure (u8 2)
  KRow RowType -> pure (u8 3 <> u8 0)
  KRow RowEffect -> pure (u8 3 <> u8 1)
  KFun a b -> do
    a' <- kind a
    b' <- kind b
    pure (u8 4 <> a' <> b')

kindScheme :: KindScheme -> E Bytes
kindScheme s = (<>) <$> vec (\(KindVar v) -> str v) s.kindVars <*> kind s.body

tyBinder :: TyBinder -> E Bytes
tyBinder b = (<>) <$> str (case b.name of TyVar v -> v) <*> kind b.kind

type_ :: Type -> E Bytes
type_ = case _ of
  TVar (TyVar v) -> (u8 0 <> _) <$> str v
  TCon q ks -> do
    name <- qname tyNameText q
    ks' <- vec kind ks
    pure (u8 1 <> name <> ks')
  TApp f a -> do
    f' <- type_ f
    a' <- type_ a
    pure (u8 2 <> f' <> a')
  TForall (TyVar v) k body -> do
    v' <- str v
    k' <- kind k
    body' <- type_ body
    pure (u8 3 <> v' <> k' <> body')
  TConstrained c body -> do
    c' <- constraint c
    body' <- type_ body
    pure (u8 4 <> c' <> body')
  TRowEmpty -> pure (u8 5)
  TRowExtend e rest -> do
    e' <- rowEntry e
    rest' <- type_ rest
    pure (u8 6 <> e' <> rest')
  TRowUnion a b -> do
    a' <- type_ a
    b' <- type_ b
    pure (u8 7 <> a' <> b')

rowEntry :: RowEntry -> E Bytes
rowEntry = case _ of
  RowTypeEntry k t -> do
    k' <- rowKey k
    t' <- type_ t
    pure (u8 0 <> k' <> t')
  RowEffectEntry e args -> do
    e' <- qname effNameText e
    args' <- vec type_ args
    pure (u8 1 <> e' <> args')
  RowLabelledEffectEntry s e args -> do
    s' <- str (symbolText s)
    e' <- qname effNameText e
    args' <- vec type_ args
    pure (u8 2 <> s' <> e' <> args')
  RowRegionEntry v cells -> do
    v' <- type_ v
    cells' <- type_ cells
    pure (u8 3 <> v' <> cells')

rowKey :: RowKey -> E Bytes
rowKey = case _ of
  SymbolKey s -> (u8 0 <> _) <$> str (symbolText s)
  TagKey (Tag t) -> (u8 1 <> _) <$> str t
  PositionKey n -> (u8 2 <> _) <$> count n
  EffectKey e -> (u8 3 <> _) <$> qname effNameText e
  RegionKey -> pure (u8 4)

constraint :: Constraint -> E Bytes
constraint = case _ of
  Lacks k t -> do
    k' <- rowKey k
    t' <- type_ t
    pure (u8 0 <> k' <> t')
  Disjoint a b -> do
    a' <- type_ a
    b' <- type_ b
    pure (u8 1 <> a' <> b')

scheme :: Scheme -> E Bytes
scheme s = (<>) <$> vec (\(KindVar v) -> str v) s.kindVars <*> schemeBody s.body

schemeBody :: SchemeBody -> E Bytes
schemeBody = case _ of
  Plain t -> (u8 0 <> _) <$> type_ t
  Computation result row -> do
    result' <- type_ result
    row' <- type_ row
    pure (u8 1 <> result' <> row')
  Forall (TyVar v) k body -> do
    v' <- str v
    k' <- kind k
    body' <- schemeBody body
    pure (u8 2 <> v' <> k' <> body')
  Constrained c body -> do
    c' <- constraint c
    body' <- schemeBody body
    pure (u8 3 <> c' <> body')
  Synthesized p body -> do
    name <- optional (str <<< identText) p.name
    dictionary <- type_ p.dictionary
    synthesizer <- qname identText p.synthesizer
    body' <- schemeBody body
    pure (u8 4 <> name <> dictionary <> synthesizer <> body')

-- Reading ----------------------------------------------------------------------------

decode :: Bytes -> Either DecodeError StoredInterface
decode bytes = runR bytes do
  traverse_ (\b -> expect b BadMagic) magic
  format <- uvarR
  when (format /= formatVersion) (throwR (UnsupportedFormatVersion format))
  flags <- uvarR
  when (flags /= 0) (throwR (UnknownFlags flags))
  abi <- map textOf text
  when (abi /= abiVersion) (throwR (UnknownAbiVersion abi))
  stringTable <- sectionR 0 sectionStrings (vecR (map textOf text))
  let ss = stringTable.value
  name <- sectionR stringTable.previous sectionModule (map ModuleName (strR ss))
  imports <- sectionR name.previous sectionImports (vecR (map ModuleName (strR ss)))
  exports <- sectionR imports.previous sectionExports (exportsR ss)
  values <- sectionR exports.previous sectionValues (tableR ss Ident (valueEntryR ss))
  types <- sectionR values.previous sectionTypes (tableR ss TyName (typeEntryR ss))
  effects <- sectionR types.previous sectionEffects (tableR ss EffName (effectEntryR ss))
  operators <- sectionR effects.previous sectionOperators (tableR ss OperatorName (operatorEntryR ss))
  typeOperators <- sectionR operators.previous sectionTypeOperators (tableR ss OperatorName (typeOperatorEntryR ss))
  attributes <- sectionR typeOperators.previous sectionAttributes (tableR ss Ident (attributeEntryR ss))
  implicit <- sectionR attributes.previous sectionImplicitHandlers (vecR (implicitHandlerR ss))
  catalogOnly <- sectionR implicit.previous sectionCatalogOnly (tableR ss Ident (pure unit))
  arities <- sectionR catalogOnly.previous sectionArities (tableR ss Ident arityR)
  trailing <- C.trailingR layout known arities.previous
  let
    declarations :: Declarations
    declarations =
      { values: values.value
      , types: types.value
      , effects: effects.value
      , operators: operators.value
      , typeOperators: typeOperators.value
      , attributes: attributes.value
      }
  pure
    { interface:
        { name: name.value
        , imports: imports.value
        , exports: exports.value
        , declarations
        , implicitHandlers: implicit.value
        , catalogOnly: Set.fromFoldable (Map.keys catalogOnly.value)
        , arities: arities.value
        }
    , buildHash: map (\(Tuple _ hash) -> hash) (Array.head trailing)
    }
  where
  sectionR :: forall a. P.Int -> P.Int -> R a -> R (C.Read a)
  sectionR = C.sectionR layout
  known id
    | id == sectionBuildHash = Just do
        n <- structuralR
        takeR n
    | otherwise = Nothing
  arityR = do
    n <- structuralR
    when (n < 1) (throwR (ArityNotPositive n))
    pure n

-- | A map, its keys ascending strictly by scalar value, which is also what
-- | refuses a key twice.
tableR :: forall k v. Ord k => Strings -> (P.String -> k) -> R v -> R (Map k v)
tableR ss key value = do
  entries <- vecR do
    k <- strR ss
    v <- value
    pure (Tuple k v)
  traverse_ ascending (Array.zip entries (Array.drop 1 entries))
  pure (Map.fromFoldable (map (\(Tuple k v) -> Tuple (key k) v) entries))
  where
  ascending (Tuple (Tuple a _) (Tuple b _)) = case compareByScalar a b of
    LT -> pure unit
    _ -> throwR EntriesOutOfOrder

unknown :: forall a. TagKind -> P.Int -> R a
unknown kind' t = throwR (UnknownTag kind' t)

optionalR :: forall a. R a -> R (Maybe a)
optionalR item = do
  t <- byte
  case t of
    0 -> pure Nothing
    1 -> Just <$> item
    _ -> unknown OptionByte t

booleanR :: TagKind -> R P.Boolean
booleanR kind' = do
  t <- byte
  case t of
    0 -> pure false
    1 -> pure true
    _ -> unknown kind' t

exportsR :: Strings -> R Exports
exportsR ss = do
  values <- tableR ss identity (exportR ss (qnameR ss Ident))
  types <- tableR ss identity typeExportR
  operators <- tableR ss identity (exportR ss (qnameR ss OperatorName))
  typeOperators <- tableR ss identity (exportR ss (qnameR ss OperatorName))
  macros <- tableR ss identity (exportR ss (qnameR ss Ident))
  attributes <- tableR ss identity (exportR ss (qnameR ss Ident))
  modules <- vecR (map ModuleName (strR ss))
  pure { values, types, operators, typeOperators, macros, attributes, modules }
  where
  typeExportR = do
    t <- byte
    entity <- case t of
      0 -> TypeEntity <$> qnameR ss TyName
      1 -> EffectEntity <$> qnameR ss EffName
      _ -> unknown EntityTag t
    v <- viaR ss
    members <- vecR (map Ident (strR ss))
    pure { entity, via: v, members }

exportR :: forall a. Strings -> R a -> R (Export a)
exportR ss entity = { entity: _, via: _ } <$> entity <*> viaR ss

viaR :: Strings -> R Via
viaR ss = do
  t <- byte
  case t of
    0 -> pure Declared
    1 -> ThroughImport <<< ModuleName <$> strR ss
    _ -> unknown ViaTag t

valueEntryR :: Strings -> R ValueEntry
valueEntryR ss = do
  t <- byte
  sort <- case t of
    0 -> pure SortValue
    1 -> SortForeign <$> observationR
    2 -> pure SortHandler
    3 -> SortConstructor <$> qnameR ss TyName
    4 -> SortOperation <$> qnameR ss EffName
    _ -> unknown ValueSortTag t
  s <- schemeR ss
  attributes <- vecR (attributeR ss)
  pure { sort, scheme: s, attributes }

observationR :: R Observation
observationR = do
  t <- byte
  case t of
    0 -> pure MayObserve
    1 -> pure ObservesNone
    _ -> unknown ObservationTag t

typeEntryR :: Strings -> R TypeEntry
typeEntryR ss = do
  k <- kindSchemeR ss
  t <- byte
  sort <- case t of
    0 -> do
      params <- vecR (tyBinderR ss)
      constructors <- vecR ({ name: _, fields: _ } <$> map Ident (strR ss) <*> vecR (typeR ss))
      isNewtype <- booleanR NewtypeByte
      pure (DataType { params, constructors, isNewtype })
    1 -> do
      params <- vecR (tyBinderR ss)
      b <- typeR ss
      pure (Synonym { params, body: b })
    2 -> pure ForeignType
    3 -> Intrinsic <$> canonicalClassR
    _ -> unknown TypeSortTag t
  attributes <- vecR (attributeR ss)
  pure { kind: k, sort, attributes }

canonicalClassR :: R CanonicalClass
canonicalClassR = do
  t <- byte
  case t of
    0 -> pure CanonicalLiteral
    1 -> pure CanonicalFunction
    2 -> pure CanonicalRecord
    3 -> pure CanonicalVariant
    4 -> pure CanonicalOpaque
    _ -> unknown CanonicalClassTag t

effectEntryR :: Strings -> R EffectEntry
effectEntryR ss = do
  params <- vecR (tyBinderR ss)
  operations <- vecR do
    name <- Ident <$> strR ss
    binders <- vecR (tyBinderR ss)
    arguments <- vecR (typeR ss)
    resumesWith <- typeR ss
    pure { name, binders, arguments, resumesWith }
  attributes <- vecR (attributeR ss)
  pure { params, operations, attributes }

associativityR :: R Associativity
associativityR = do
  t <- byte
  case t of
    0 -> pure AssociateNone
    1 -> pure AssociateLeft
    2 -> pure AssociateRight
    _ -> unknown AssociativityTag t

operatorEntryR :: Strings -> R OperatorEntry
operatorEntryR ss = do
  a <- associativityR
  precedence <- structuralR
  t <- byte
  target <- case t of
    0 -> FixityValue <$> qnameR ss Ident
    1 -> FixityConstructor <$> qnameR ss Ident
    _ -> unknown FixityTargetTag t
  pure { associativity: a, precedence, target }

typeOperatorEntryR :: Strings -> R TypeOperatorEntry
typeOperatorEntryR ss = do
  a <- associativityR
  precedence <- structuralR
  t <- byte
  target <- case t of
    0 -> TargetTypeConstructor <$> qnameR ss TyName
    1 -> TargetTypeSynonym <$> qnameR ss TyName
    2 -> TargetEffect <$> qnameR ss EffName
    _ -> unknown FixityTargetTag t
  pure { associativity: a, precedence, target }

attributeEntryR :: Strings -> R AttributeEntry
attributeEntryR ss = do
  positional <- vecR (typeR ss)
  keyword <- vecR do
    label <- strR ss
    t <- typeR ss
    d <- optionalR (constantR ss)
    pure { label, type: t, default: d }
  pure { positional, keyword }

attributeR :: Strings -> R Attribute
attributeR ss = do
  name <- qnameR ss Ident
  positional <- vecR (constantR ss)
  keyword <- vecR ({ label: _, value: _ } <$> strR ss <*> constantR ss)
  pure { name, positional, keyword }

constantR :: Strings -> R Constant
constantR ss = do
  t <- byte
  case t of
    0 -> ConstantLiteral <$> literalR ss
    1 -> ConstantValue <$> qnameR ss Ident
    2 -> ConstantConstructor <$> qnameR ss Ident <*> vecR (constantR ss)
    3 -> ConstantRecord <$> vecR ({ label: _, value: _ } <$> map Symbol (strR ss) <*> constantR ss)
    _ -> unknown AttributeConstantTag t

literalR :: Strings -> R Literal
literalR ss = do
  t <- byte
  case t of
    0 -> LitInt <$> svarR
    1 -> LitNumber <$> f64R
    2 -> do
      s <- strR ss
      case scalarString s of
        Just v -> pure (LitString v)
        Nothing -> throwR BadUtf8
    3 -> do
      code <- structuralR
      case scalarValue code of
        Just v -> pure (LitChar v)
        Nothing -> throwR (NotAScalarValue code)
    4 -> LitBoolean <$> booleanR BooleanByte
    _ -> unknown LiteralTag t

implicitHandlerR :: Strings -> R ImplicitHandler
implicitHandlerR ss = do
  handler <- Ident <$> strR ss
  source <- rowEntryR ss
  targets <- vecR (rowEntryR ss)
  pure { handler, source, targets }

kindR :: Strings -> R Kind
kindR ss = do
  t <- byte
  case t of
    0 -> KVar <<< KindVar <$> strR ss
    1 -> pure KType
    2 -> pure KEffect
    3 -> do
      r <- byte
      case r of
        0 -> pure (KRow RowType)
        1 -> pure (KRow RowEffect)
        _ -> unknown RowKindTag r
    4 -> KFun <$> kindR ss <*> kindR ss
    _ -> unknown KindTag t

kindSchemeR :: Strings -> R KindScheme
kindSchemeR ss = { kindVars: _, body: _ } <$> vecR (KindVar <$> strR ss) <*> kindR ss

tyBinderR :: Strings -> R TyBinder
tyBinderR ss = { name: _, kind: _ } <$> map TyVar (strR ss) <*> kindR ss

typeR :: Strings -> R Type
typeR ss = do
  t <- byte
  case t of
    0 -> TVar <<< TyVar <$> strR ss
    1 -> TCon <$> qnameR ss TyName <*> vecR (kindR ss)
    2 -> TApp <$> typeR ss <*> typeR ss
    3 -> TForall <$> map TyVar (strR ss) <*> kindR ss <*> typeR ss
    4 -> TConstrained <$> constraintR ss <*> typeR ss
    5 -> pure TRowEmpty
    6 -> TRowExtend <$> rowEntryR ss <*> typeR ss
    7 -> TRowUnion <$> typeR ss <*> typeR ss
    _ -> unknown TypeTag t

rowEntryR :: Strings -> R RowEntry
rowEntryR ss = do
  t <- byte
  case t of
    0 -> RowTypeEntry <$> rowKeyR ss <*> typeR ss
    1 -> RowEffectEntry <$> qnameR ss EffName <*> vecR (typeR ss)
    2 -> RowLabelledEffectEntry <$> map Symbol (strR ss) <*> qnameR ss EffName <*> vecR (typeR ss)
    3 -> RowRegionEntry <$> typeR ss <*> typeR ss
    _ -> unknown RowEntryTag t

rowKeyR :: Strings -> R RowKey
rowKeyR ss = do
  t <- byte
  case t of
    0 -> SymbolKey <<< Symbol <$> strR ss
    1 -> TagKey <<< Tag <$> strR ss
    2 -> PositionKey <$> structuralR
    3 -> EffectKey <$> qnameR ss EffName
    4 -> pure RegionKey
    _ -> unknown RowKeyTag t

constraintR :: Strings -> R Constraint
constraintR ss = do
  t <- byte
  case t of
    0 -> Lacks <$> rowKeyR ss <*> typeR ss
    1 -> Disjoint <$> typeR ss <*> typeR ss
    _ -> unknown ConstraintTag t

schemeR :: Strings -> R Scheme
schemeR ss = { kindVars: _, body: _ } <$> vecR (KindVar <$> strR ss) <*> schemeBodyR ss

schemeBodyR :: Strings -> R SchemeBody
schemeBodyR ss = do
  t <- byte
  case t of
    0 -> Plain <$> typeR ss
    1 -> Computation <$> typeR ss <*> typeR ss
    2 -> Forall <$> map TyVar (strR ss) <*> kindR ss <*> schemeBodyR ss
    3 -> Constrained <$> constraintR ss <*> schemeBodyR ss
    4 -> do
      name <- optionalR (Ident <$> strR ss)
      dictionary <- typeR ss
      synthesizer <- qnameR ss Ident
      Synthesized { name, dictionary, synthesizer } <$> schemeBodyR ss
    _ -> unknown SchemeTag t
