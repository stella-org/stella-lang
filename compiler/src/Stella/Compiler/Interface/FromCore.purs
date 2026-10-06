-- | The canonical interface of a module written in Core: one the compiler
-- | owns, or a test writes, with no source behind it.
-- |
-- | **It is a projection of what Core holds, and no inverse of the surface
-- | interface.** Core keeps nothing of fixities, of what is published to the
-- | catalog alone, of implicit handlers, of a handler as opposed to a value, or
-- | of what a foreign asserts of its observational effects, so each is given
-- | one value:
-- |
-- | - a value is a value, and a foreign one that may observe;
-- | - an operation takes its one Core argument as its one argument;
-- | - there are no operators, type operators, implicit handlers, or entries
-- |   published to the catalog alone, and no type is a synonym or a foreign
-- |   type;
-- | - an exported value carrying `Prim.macro` is exported as a macro, and as no
-- |   value; it is declared as any value is.
-- |
-- | **What the module owns is read from its checked signature**, those entries
-- | of it qualified by the module's name: an intrinsic type the signature was
-- | given — `Stella.Syntax`'s `OriginRef` — is a type of the module as a
-- | declared one is. The order of a data type's constructors and of an
-- | effect's operations is the declaration's.
module Stella.Compiler.Interface.FromCore
  ( FromCoreError(..)
  , interfaceOfCore
  ) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Data.Show.Generic (genericShow)
import Data.Traversable (for, traverse_)
import Data.Tuple (Tuple(..))
import Stella.Compiler.Interface.Assemble (reachedFromOutside)
import Stella.Compiler.Interface.Module (Attribute, EffectEntry, Exports, ModuleInterface, TypeEntity(..), TypeEntry, TypeExport, TypeSort(..), ValueEntry, ValueSort(..), Via(..), emptyDeclarations, emptyExports)
import Stella.Compiler.Interface.Prim (primAttribute)
import Stella.Compiler.Interface.Scheme (plainScheme)
import Stella.Compiler.Surface.Decl (Observation(..))
import Stella.Compiler.TypedCore (Decl(..), Declared, Module)
import Stella.Compiler.TypedCore.Decl (Export(..)) as Core
import Stella.Compiler.TypedCore.Name (EffName(..), Ident(..), OpName(..), Qualified(..), TyName(..))
import Stella.Compiler.TypedCore.Prim (pureFn, primModule)
import Stella.Compiler.TypedCore.Signature (TyConInfo(..))
import Stella.Compiler.TypedCore.Type (Type(..))

data FromCoreError
  -- | An export naming nothing the module declares.
  = ExportUndeclared Core.Export
  -- | A data type in the signature with no declaration of the module behind it.
  | DataTypeUndeclared TyName
  -- | An arity of a value the module does not declare and a module downstream
  -- | reaches, or one below one.
  | ArityNotOwn Ident
  | ArityBelowOne Ident Int

-- | The interface of a module written in Core, checked as `Declared` says, with
-- | the arities its translation gave.
interfaceOfCore :: forall a. Module a -> Declared a -> Map Ident Int -> Either FromCoreError ModuleInterface
interfaceOfCore m declared arities = do
  types <- for ownTypes typeEntry
  exports <- exportsOf
  traverse_ (arityOk exports) (Map.toUnfoldable arities :: Array (Tuple Ident Int))
  pure
    { name: self
    , imports: Array.filter (_ /= primModule) m.imports
    , exports
    , declarations: emptyDeclarations
        { values = values
        , types = Map.fromFoldable types
        , effects = Map.fromFoldable (map (\e -> Tuple e.name (effectEntry e)) effects)
        , attributes = Map.fromFoldable (Array.mapMaybe ownAttribute (Map.toUnfoldable sig.attributes))
        }
    , implicitHandlers: []
    , catalogOnly: Set.empty
    , arities
    }
  where
  self = m.name
  sig = declared.signature

  own :: forall n. Qualified n -> Maybe n
  own (Qualified owner n) = if owner == self then Just n else Nothing

  dataDecls = Array.mapMaybe
    ( case _ of
        DeclData _ d -> Just d
        _ -> Nothing
    )
    m.decls
  effects = Array.mapMaybe
    ( case _ of
        DeclEffect _ e -> Just e
        _ -> Nothing
    )
    m.decls

  ownTypes = Array.mapMaybe (\(Tuple q info) -> map (\n -> Tuple n info) (own q)) (Map.toUnfoldable sig.types)

  typeEntry :: Tuple TyName TyConInfo -> Either FromCoreError (Tuple TyName TypeEntry)
  typeEntry (Tuple n info) = case info of
    IntrinsicTyCon kind canonical -> Right (Tuple n { kind, sort: Intrinsic canonical, attributes: [] })
    DataTyCon kind _ -> case Array.find (\d -> d.name == n) dataDecls of
      Nothing -> Left (DataTypeUndeclared n)
      Just d -> Right
        ( Tuple n
            { kind
            , sort: DataType
                { params: d.params
                , constructors: map (\c -> { name: c.name, fields: c.fields }) (Array.sortWith _.tag d.constructors)
                , isNewtype: d.isNewtype
                }
            , attributes: d.attributes
            }
        )

  effectEntry e =
    { params: e.params
    , operations: map (\o -> { name: opIdent o.name, binders: o.tyBinders, arguments: [ o.argument ], resumesWith: o.resumesWith }) e.operations
    , attributes: e.attributes
    } :: EffectEntry

  -- every value the module declares: its bindings and foreigns, the
  -- constructors of its data types, and the operations of its effects
  values = Map.fromFoldable (Array.concatMap valuesOf m.decls)
  valuesOf = case _ of
    DeclNonRec _ b -> [ binding b ]
    DeclRec _ bs -> map binding bs
    DeclForeign _ f -> [ Tuple f.name { sort: SortForeign MayObserve, scheme: plainScheme f.scheme, attributes: f.attributes } ]
    DeclData _ d -> Array.mapMaybe
      (\c -> map (\info -> Tuple c.name { sort: SortConstructor (Qualified self d.name), scheme: plainScheme info.scheme, attributes: [] }) (Map.lookup (Qualified self c.name) sig.ctors))
      d.constructors
    DeclEffect _ e -> map
      ( \o -> Tuple (opIdent o.name)
          { sort: SortOperation (Qualified self e.name)
          , scheme: plainScheme { kindVars: [], body: Array.foldr (\b t -> TForall b.name b.kind t) (pureFn o.argument o.resumesWith) (e.params <> o.tyBinders) }
          , attributes: []
          }
      )
      e.operations
    DeclAttribute _ _ -> []
  binding b = Tuple b.name ({ sort: SortValue, scheme: plainScheme b.scheme, attributes: b.attributes } :: ValueEntry)

  ownAttribute (Tuple q info) = map (\n -> Tuple n info) (own q)

  isMacro :: Array Attribute -> Boolean
  isMacro = Array.any (\a -> a.name == primAttribute "macro")

  exportsOf :: Either FromCoreError Exports
  exportsOf = Array.foldM export emptyExports m.exports
  export acc e = case e of
    Core.ExportValue x -> case Map.lookup x values of
      Just entry
        | isMacro entry.attributes -> Right acc { macros = Map.insert (identText x) (declaredAs x) acc.macros }
        | otherwise -> Right acc { values = Map.insert (identText x) (declaredAs x) acc.values }
      Nothing -> Left (ExportUndeclared e)
    Core.ExportCtor c
      | Map.member c values -> Right acc { values = Map.insert (identText c) (declaredAs c) acc.values }
      | otherwise -> Left (ExportUndeclared e)
    Core.ExportType t -> case Array.find (\d -> d.name == t) dataDecls of
      Just d ->
        let
          members = map _.name (Array.filter (\c -> Array.elem (Core.ExportCtor c.name) m.exports) (Array.sortWith _.tag d.constructors))
        in
          Right acc { types = Map.insert (tyNameText t) (typeExport (TypeEntity (Qualified self t)) members) acc.types }
      Nothing
        | Array.any (\(Tuple n _) -> n == t) ownTypes -> Right acc { types = Map.insert (tyNameText t) (typeExport (TypeEntity (Qualified self t)) []) acc.types }
        | otherwise -> Left (ExportUndeclared e)
    Core.ExportEffect n -> case Array.find (\x -> x.name == n) effects of
      Just eff ->
        let
          members = map (opIdent <<< _.name) eff.operations
        in
          Right acc
            { types = Map.insert (effNameText n) (typeExport (EffectEntity (Qualified self n)) members) acc.types
            , values = Array.foldl (\vs o -> Map.insert (identText o) (declaredAs o) vs) acc.values members
            }
      Nothing -> Left (ExportUndeclared e)

  declaredAs x = { entity: Qualified self x, via: Declared }
  typeExport entity members = { entity, via: Declared, members } :: TypeExport

  -- an arity is of a value the module declares and a module downstream reaches
  arityOk exports (Tuple x n)
    | not (Map.member x values) || not (reachedFromOutside self exports Map.empty x) = Left (ArityNotOwn x)
    | n < 1 = Left (ArityBelowOne x n)
    | otherwise = Right unit

opIdent :: OpName -> Ident
opIdent (OpName o) = Ident o

identText :: Ident -> String
identText (Ident x) = x

tyNameText :: TyName -> String
tyNameText (TyName x) = x

effNameText :: EffName -> String
effNameText (EffName x) = x

derive instance Eq FromCoreError
derive instance Generic FromCoreError _

instance Show FromCoreError where
  show = genericShow
