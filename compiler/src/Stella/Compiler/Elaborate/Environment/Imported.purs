-- | What a module being compiled is elaborated and checked against, read off
-- | the interfaces of the modules it imports
-- | ([Elaborator API](../../../../../docs/technical-references/02-Surface-Language/03-Elaborator-API.md)).
-- |
-- | **The signature and the catalog see different things.** The signature is
-- | what Core checks against, and holds every declaration of every module the
-- | imports reach, a private one among them: an exported scheme may mention a
-- | type its module does not export, and an attribute's default a value it
-- | does not. The catalog is what a synthesizer may find, and holds what source
-- | could reach — the values each module imported exports, and those it
-- | publishes to the catalog alone — each read from the interface of the module
-- | declaring it.
-- |
-- | **Everything elaboration reads of types is derived from the one
-- | signature**: the kinding environment, the constructors, and the effects,
-- | so no interface is read by two rules.
module Stella.Compiler.Elaborate.Environment.Imported
  ( ImportError(..)
  , importedSignature
  , compilationSignature
  , importedCatalog
  , sessionEnvOf
  , operationArgument
  ) where

import Prelude
import Prim hiding (Type)

import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldl, foldr)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Data.Tuple (Tuple(..))
import Stella.Compiler.Elaborate.CorePlus.Type (fromCore)
import Stella.Compiler.Elaborate.Environment.Catalog (CatalogEntry, EntrySort(..), catalogOf)
import Stella.Compiler.Elaborate.Environment.Constructors (constructorsOf)
import Stella.Compiler.Elaborate.Environment.Effects (effectsOf)
import Stella.Compiler.Elaborate.Kernel.Elab (SessionEnv)
import Stella.Compiler.Elaborate.Mechanism.Kinding (kindingOf)
import Stella.Compiler.Elaborate.Vocabulary.Trace (Tracing(..))
import Stella.Compiler.Interface.Environment (BuildEnvironment, ModuleView, abiOf, lookupInterface, lookupValue, reachable)
import Stella.Compiler.Interface.Module (ModuleInterface, TypeEntry, TypeSort(..), ValueEntry, ValueSort(..))
import Stella.Compiler.Interface.Scheme (coreScheme)
import Stella.Compiler.TypedCore.Declare (DeclError, ctorInfo, dataEntry, initialSignature)
import Stella.Compiler.TypedCore.Name (Ident(..), ModuleName, OpName(..), Qualified(..), TyName)
import Stella.Compiler.TypedCore.Prim (primModule, recordTy, unitTy)
import Stella.Compiler.TypedCore.Type (RowEntry(..), RowKey(..), Type(..))
import Stella.Compiler.TypedCore.Signature (CanonicalClass(..), Signature, TyConInfo(..), emptySignature)

data ImportError
  -- | The interfaces together are no signature Core admits.
  = SignatureRejected DeclError

-- | The signature of everything the imports reach, `Prim` and what the ABI
-- | manifest supplies among it, checked as an imported signature is.
-- |
-- | **A type synonym reaches no signature**, being expanded wherever it is used.
-- | A foreign type has no Core declaration and stands as an opaque type of the
-- | module declaring it.
importedSignature :: BuildEnvironment -> ModuleView -> Either ImportError Signature
importedSignature env view = reachedSignature env view []

-- | The signature a module is compiled against: what its imports reach, as
-- | `importedSignature` gives it, and the types the ABI manifest supplies to
-- | the module itself.
compilationSignature :: BuildEnvironment -> ModuleView -> ModuleName -> Either ImportError Signature
compilationSignature env view self = reachedSignature env view
  [ foldl (addType self) emptySignature (Map.toUnfoldable (abiOf self env) :: Array _) ]

reachedSignature :: BuildEnvironment -> ModuleView -> Array Signature -> Either ImportError Signature
reachedSignature env view own = do
  let parts = map part (Array.filter (_ /= primModule) (Set.toUnfoldable (reachable view))) <> own
  case initialSignature parts of
    Left err -> Left (SignatureRejected err)
    Right sig -> Right sig
  where
  part m =
    let
      declared = case lookupInterface m env of
        Just i -> signatureOf i
        Nothing -> emptySignature
    in
      foldl (addType m) declared (Map.toUnfoldable (abiOf m env) :: Array _)

-- | What one interface declares, as Core reads it.
signatureOf :: ModuleInterface -> Signature
signatureOf i =
  { types: (foldl (addType i.name) emptySignature types).types
  , ctors: (foldl (addType i.name) emptySignature types).ctors
  , effects: Map.fromFoldable (map effect (Map.toUnfoldable i.declarations.effects :: Array _))
  , values: Map.fromFoldable (Array.mapMaybe value (Map.toUnfoldable i.declarations.values))
  , attributes: Map.fromFoldable (map (\(Tuple n a) -> Tuple (Qualified i.name n) a) (Map.toUnfoldable i.declarations.attributes :: Array _))
  }
  where
  types = Map.toUnfoldable i.declarations.types :: Array _

  value (Tuple n entry) = case entry.sort of
    SortValue -> Just (Tuple (Qualified i.name n) { scheme: coreScheme entry.scheme, isForeign: false })
    SortHandler -> Just (Tuple (Qualified i.name n) { scheme: coreScheme entry.scheme, isForeign: false })
    SortForeign _ -> Just (Tuple (Qualified i.name n) { scheme: coreScheme entry.scheme, isForeign: true })
    -- a constructor is the type's, and an operation the effect's
    _ -> Nothing

  effect (Tuple n entry) =
    Tuple (Qualified i.name n) { params: entry.params, operations: Map.fromFoldable (map operation entry.operations) }

  operation o =
    let
      name = case o.name of Ident x -> OpName x
    in
      Tuple name { name, tyBinders: o.binders, argument: operationArgument o.arguments, resumesWith: o.resumesWith }

-- | The one argument Core gives an operation written with the arguments given
-- | (D21): none is `Prim.Unit`, one is itself, and several are a record of them,
-- | each under its position.
operationArgument :: Array Type -> Type
operationArgument = case _ of
  [] -> TCon unitTy []
  [ one ] -> one
  several -> TApp (TCon recordTy []) (foldr (\(Tuple n t) row -> TRowExtend (RowTypeEntry (PositionKey n) t) row) TRowEmpty (Array.mapWithIndex Tuple several))

-- | A type declaration and the constructors it gives, read by the rules Core
-- | declares a data type by.
addType :: ModuleName -> Signature -> Tuple TyName TypeEntry -> Signature
addType m sig (Tuple n entry) = case entry.sort of
  DataType d ->
    let
      decl =
        { name: n
        , kindVars: entry.kind.kindVars
        , params: d.params
        , constructors: Array.mapWithIndex (\tag c -> { name: c.name, tag, fields: c.fields }) d.constructors
        , isNewtype: d.isNewtype
        , attributes: []
        }
      owner = Qualified m n
    in
      sig
        { types = Map.insert owner (dataEntry m decl) sig.types
        , ctors = foldl (\acc c -> Map.insert (Qualified m c.name) (ctorInfo owner decl c) acc) sig.ctors decl.constructors
        }
  Intrinsic class' -> sig { types = Map.insert (Qualified m n) (IntrinsicTyCon entry.kind class') sig.types }
  Synonym _ -> sig
  -- a foreign type has no Core declaration, and is an opaque type of the module
  -- declaring it
  ForeignType -> sig { types = Map.insert (Qualified m n) (IntrinsicTyCon entry.kind CanonicalOpaque) sig.types }

-- | The catalog of what the header reaches: each value a module the imports
-- | reach exports, and each it publishes to the catalog alone, `Prim` among
-- | them, its scheme and attributes read from the interface of the module
-- | declaring it. A value a module keeps to itself is no entry, and neither is
-- | an operation, which is the effect's.
importedCatalog :: BuildEnvironment -> ModuleView -> Array CatalogEntry
importedCatalog env view = Array.nubByEq (\a b -> a.name == b.name) (Array.concatMap entriesOf (Set.toUnfoldable (reachable view)))
  where
  entriesOf m = case lookupInterface m env of
    Nothing -> []
    Just i ->
      let
        exported = map _.entity (Array.fromFoldable (Map.values i.exports.values))
        published = map (Qualified m) (Array.fromFoldable i.catalogOnly)
      in
        Array.mapMaybe (\q -> lookupValue q view >>= entryOf q) (exported <> published)

  entryOf q entry = do
    sort <- sortOf entry
    let scheme = coreScheme entry.scheme
    pure { name: q, sort, scheme: { kindVars: scheme.kindVars, body: fromCore scheme.body }, attributes: entry.attributes }

  sortOf :: ValueEntry -> Maybe EntrySort
  sortOf entry = case entry.sort of
    SortValue -> Just ValueEntry
    SortHandler -> Just ValueEntry
    SortForeign _ -> Just ForeignEntry
    SortConstructor _ -> Just ConstructorEntry
    SortOperation _ -> Nothing

-- | The session a module is elaborated in: the catalog given, and what is read
-- | of types derived from the signature.
sessionEnvOf :: Signature -> Array CatalogEntry -> SessionEnv
sessionEnvOf sig entries =
  { catalog: catalogOf entries
  , kinding: kindingOf sig
  , constructors: constructorsOf sig
  , effects: effectsOf sig
  , tracing: TraceDisabled
  }

derive instance Eq ImportError

instance Show ImportError where
  show = case _ of
    SignatureRejected err -> "SignatureRejected " <> show err
