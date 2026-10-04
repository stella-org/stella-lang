-- | The `Prim` module.
-- |
-- | `Prim` holds the vocabulary the rules name and nothing else. It is reserved
-- | and no module imports it, so the rules that build `Σ` put it there before
-- | anything else.
-- |
-- | Every kind scheme here is empty, so no use site writes `[[κ̄]]`.
module Stella.Compiler.TypedCore.Prim
  ( primModule
  , functionTy
  , recordTy
  , variantTy
  , intTy
  , numberTy
  , stringTy
  , charTy
  , booleanTy
  , unitTy
  , ioTy
  , unitCtor
  , fn
  , pureFn
  , asFunction
  , litType
  , primSignature
  ) where

import Prelude

import Prim as P

import Stella.Compiler.TypedCore.Kind (Kind(..), RowElemKind(..), monoScheme)
import Stella.Compiler.TypedCore.Name (Ident(..), ModuleName(..), Qualified(..), TyName(..))
import Stella.Compiler.TypedCore.Signature (CanonicalClass(..), Signature, TyConInfo(..), emptySignature)
import Stella.Compiler.TypedCore.Term (Literal(..))
import Stella.Compiler.TypedCore.Type (Type(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))

-- | The reserved module name. No module may be named this, so nothing can
-- | supply a second `Prim.Int`.
primModule :: ModuleName
primModule = ModuleName "Prim"

tyName :: P.String -> Qualified TyName
tyName name = Qualified primModule (TyName name)

-- | `Function τ1 ρ τ2`, which every arrow written `τ1 -{ρ}-> τ2` abbreviates.
-- | Core has no arrow syntax.
functionTy :: Qualified TyName
functionTy = tyName "Function"

recordTy :: Qualified TyName
recordTy = tyName "Record"

variantTy :: Qualified TyName
variantTy = tyName "Variant"

intTy :: Qualified TyName
intTy = tyName "Int"

numberTy :: Qualified TyName
numberTy = tyName "Number"

stringTy :: Qualified TyName
stringTy = tyName "String"

charTy :: Qualified TyName
charTy = tyName "Char"

booleanTy :: Qualified TyName
booleanTy = tyName "Boolean"

unitTy :: Qualified TyName
unitTy = tyName "Unit"

ioTy :: Qualified TyName
ioTy = tyName "IO"

-- | `Prim` declares one data type, so that a `switchCtor` exhausts `Unit` with
-- | one branch. As a literal it would fall under `switchLit`, where a default
-- | is mandatory.
unitCtor :: Qualified Ident
unitCtor = Qualified primModule (Ident "Unit")

-- | `τ1 -{ρ}-> τ2`.
fn :: Type -> Type -> Type -> Type
fn argument row result =
  TApp (TApp (TApp (TCon functionTy []) argument) row) result

-- | `τ1 -> τ2`, an arrow performing no effect.
pureFn :: Type -> Type -> Type
pureFn argument result = fn argument TRowEmpty result

-- | The three parts of an arrow, where the type is a saturated `Function`.
asFunction :: Type -> Maybe { argument :: Type, row :: Type, result :: Type }
asFunction = case _ of
  TApp (TApp (TApp (TCon name []) argument) row) result
    | name == functionTy -> Just { argument, row, result }
  _ -> Nothing

-- | The type of a literal. A literal produces no effect, so it is typeable
-- | under any ambient row.
litType :: Literal -> Type
litType = case _ of
  LitInt _ -> TCon intTy []
  LitNumber _ -> TCon numberTy []
  LitString _ -> TCon stringTy []
  LitChar _ -> TCon charTy []
  LitBoolean _ -> TCon booleanTy []

-- | `Σ_Prim`.
-- |
-- | A compiler builds this rather than reading it from source: an intrinsic is
-- | a canonical value form, typing rules, an erasure, and a backend
-- | representation together, which no declaration supplies.
primSignature :: Signature
primSignature = emptySignature
  { types = Map.fromFoldable
      [ Tuple functionTy
          (IntrinsicTyCon (monoScheme (KFun KType (KFun (KRow RowEffect) (KFun KType KType)))) CanonicalFunction)
      , Tuple recordTy (IntrinsicTyCon (monoScheme (KFun (KRow RowType) KType)) CanonicalRecord)
      , Tuple variantTy (IntrinsicTyCon (monoScheme (KFun (KRow RowType) KType)) CanonicalVariant)
      , Tuple intTy (IntrinsicTyCon (monoScheme KType) CanonicalLiteral)
      , Tuple numberTy (IntrinsicTyCon (monoScheme KType) CanonicalLiteral)
      , Tuple stringTy (IntrinsicTyCon (monoScheme KType) CanonicalLiteral)
      , Tuple charTy (IntrinsicTyCon (monoScheme KType) CanonicalLiteral)
      , Tuple booleanTy (IntrinsicTyCon (monoScheme KType) CanonicalLiteral)
      , Tuple ioTy (IntrinsicTyCon (monoScheme (KFun KType KType)) CanonicalOpaque)
      , Tuple unitTy (DataTyCon (monoScheme KType) [ unitCtor ])
      ]
  , ctors = Map.singleton unitCtor
      { owner: unitTy
      , tag: 0
      , params: []
      , fields: []
      , scheme: monoScheme (TCon unitTy [])
      }
  -- The attributes the compiler reads, none of which takes a parameter.
  , attributes = Map.fromFoldable
      (map (\n -> Tuple (Qualified primModule (Ident n)) { positional: [], keyword: [] }) [ "macro", "entrypoint", "elaborationOnly" ])
  }
