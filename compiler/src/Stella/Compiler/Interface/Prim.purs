-- | The interface of `Prim`, which the compiler builds rather than reads.
-- |
-- | `Prim` has no source: its types are intrinsics no declaration produces, and
-- | the attributes it declares are the ones the compiler acts on
-- | ([Prim and Base](../../../../docs/technical-references/06-Modules/02-Prim-and-Base.md)).
-- | It is the first interface of every build environment, and every module sees
-- | it without importing it.
module Stella.Compiler.Interface.Prim
  ( primInterface
  , primAttribute
  ) where

import Prelude

import Data.Array as Array
import Data.Map as Map
import Data.Set as Set
import Data.Tuple (Tuple(..))
import Stella.Compiler.Interface.Module (ModuleInterface, TypeEntity(..), TypeEntry, TypeSort(..), ValueSort(..), Via(..), emptyExports)
import Stella.Compiler.Interface.Scheme (plainScheme)
import Stella.Compiler.TypedCore.Name (Ident(..), Qualified(..), TyName(..), unqualified)
import Stella.Compiler.TypedCore.Prim (primModule, primSignature, unitCtor, unitTy)
import Stella.Compiler.TypedCore.Kind (monoScheme)
import Stella.Compiler.TypedCore.Signature (TyConInfo(..), tyConKind)
import Stella.Compiler.TypedCore.Type (Type(..))

-- | An attribute `Prim` declares: `macro`, `entrypoint`, `elaborationOnly`.
primAttribute :: String -> Qualified Ident
primAttribute = Qualified primModule <<< Ident

attributeNames :: Array String
attributeNames = [ "macro", "entrypoint", "elaborationOnly" ]

primInterface :: ModuleInterface
primInterface =
  { name: primModule
  , imports: []
  , exports: emptyExports
      { values = Map.singleton "Unit" { entity: unitCtor, via: Declared }
      , types = Map.fromFoldable (map typeExport typeNames)
      , attributes = Map.fromFoldable (map (\n -> Tuple n { entity: primAttribute n, via: Declared }) attributeNames)
      }
  , declarations:
      { values: Map.singleton (Ident "Unit")
          { sort: SortConstructor unitTy
          , scheme: plainScheme (monoScheme (TCon unitTy []))
          , attributes: []
          }
      , types: Map.fromFoldable (map typeEntry (Map.toUnfoldable primSignature.types :: Array _))
      , effects: Map.empty
      , operators: Map.empty
      , attributes: Map.fromFoldable (map (\n -> Tuple (Ident n) { positional: [], keyword: [] }) attributeNames)
      }
  , implicitHandlers: []
  , catalogOnly: Set.empty
  , arities: Map.empty
  }
  where
  typeNames = map (\(Qualified _ (TyName n)) -> n) (Array.fromFoldable (Map.keys primSignature.types))

  typeExport n =
    Tuple n
      { entity: TypeEntity (Qualified primModule (TyName n))
      , via: Declared
      , members: if TyName n == unqualified unitTy then [ Ident "Unit" ] else []
      }

  typeEntry :: Tuple (Qualified TyName) TyConInfo -> Tuple TyName TypeEntry
  typeEntry (Tuple (Qualified _ name) info) =
    Tuple name
      { kind: tyConKind info
      , attributes: []
      , sort: case info of
          IntrinsicTyCon _ cls -> Intrinsic cls
          DataTyCon _ ctors ->
            DataType
              { params: []
              , constructors: Array.mapMaybe
                  (\c -> map (\i -> { name: unqualified c, fields: i.fields }) (Map.lookup c primSignature.ctors))
                  ctors
              , isNewtype: false
              }
      }
