-- | How a foreign declaration's arguments and result cross to the host, read
-- | off its declared type (D44,
-- | [Foreign Manifest](../../../../docs/technical-references/05-Backend/04-Foreign-Manifest.md)).
-- |
-- | **Only what has a kind crosses**: `Int`, `Number`, `Char`, `String`, and
-- | `Boolean` as the host's own, `Unit` as nothing, a type of an intrinsic of
-- | the class opaque as whatever it was handed, and a result `IO τ` as an
-- | action producing what `τ` crosses as. A data type, a record, a variant, a
-- | function, a type variable, a type under a constraint, and an action anywhere
-- | but a result are refused: nothing marshals one. Each arrow of the type is
-- | pure (D23), wherever a value passes through it, an opaque type's arguments
-- | and a row element's payload included: the boundary performs no effect a row
-- | could name. A row is empty by its normal form, as the Core checker reads it.
-- |
-- | The crossing is target-independent: what a target does with each kind is
-- | its own, and what is written into a foreign manifest is this.
module Stella.Compiler.ForeignBoundary
  ( Position(..)
  , Refusal(..)
  , Refused
  , crossingOf
  ) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Either (Either(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Stella.Compiler.ForeignManifest (ResultKind(..), Signature, ValueKind(..))
import Stella.Compiler.TypedCore.Name (Qualified, TyName, TyVar)
import Stella.Compiler.TypedCore.Prim (asFunction, booleanTy, charTy, intTy, ioTy, numberTy, recordTy, stringTy, unitTy, variantTy)
import Stella.Compiler.TypedCore.Declare (impureArrow, isEmptyRow)
import Stella.Compiler.TypedCore.Signature (CanonicalClass(..), TyConInfo(..))
import Stella.Compiler.TypedCore.Signature (Signature) as Core
import Stella.Compiler.TypedCore.Type (Type(..), TypeScheme)

-- | Where in a foreign's type a part stands.
data Position
  -- | The argument of that place, counted from one.
  = Argument P.Int
  | Result

-- | Why a part of a foreign's type cannot cross.
data Refusal
  = DataType (Qualified TyName)
  | RecordType
  | VariantType
  | FunctionType
  | TypeVariable TyVar
  -- | An action standing where only a result may be one.
  | ActionArgument
  -- | An action producing an action.
  | ActionOfAction
  -- | A type under a constraint, which no host could be handed evidence of.
  | ConstrainedType
  -- | An arrow performing effects, where a value passes through.
  | PerformingArrow
  -- | A type that is none of the forms a value has.
  | NoValue Type

type Refused = { position :: Position, refusal :: Refusal }

-- | How a foreign of the scheme given crosses, against the signature its
-- | types are declared in.
crossingOf :: Core.Signature -> TypeScheme -> Either Refused Signature
crossingOf sig scheme = spine [] scheme.body
  where
  spine params t = case t, asFunction t of
    TForall _ _ body, _ -> spine params body
    TConstrained _ _, _ -> Left { position: Result, refusal: ConstrainedType }
    _, Just f
      | not (isEmptyRow f.row) -> Left { position: Argument (Array.length params + 1), refusal: PerformingArrow }
      | otherwise -> do
          kind <- valueAt (Argument (Array.length params + 1)) f.argument
          spine (Array.snoc params kind) f.result
    _, Nothing -> { params, result: _ } <$> resultOf t

  resultOf t = case headOf t of
    Just { name, arguments: [ produced ] } | name == ioTy -> case headOf produced of
      Just { name: inner } | inner == ioTy -> Left { position: Result, refusal: ActionOfAction }
      _ -> AsAction <$> valueAt Result produced
    _ -> AsValue <$> valueAt Result t

  -- an arrow performing effects is refused wherever it stands, as the Core
  -- checker refuses it
  valueAt position t = case impureArrow t, refusalOf t of
    Just _, _ -> Left { position, refusal: PerformingArrow }
    _, Left refusal -> Left { position, refusal }
    _, Right kind -> Right kind

  refusalOf t = case t of
    TVar a -> Left (TypeVariable a)
    TConstrained _ _ -> Left ConstrainedType
    _ | Just _ <- asFunction t -> Left FunctionType
    _ -> case headOf t of
      Just { name }
        | name == intTy -> Right AsInt
        | name == numberTy -> Right AsNumber
        | name == charTy -> Right AsChar
        | name == stringTy -> Right AsString
        | name == booleanTy -> Right AsBoolean
        | name == unitTy -> Right AsUnit
        | name == ioTy -> Left ActionArgument
        | name == recordTy -> Left RecordType
        | name == variantTy -> Left VariantType
        | otherwise -> case Map.lookup name sig.types of
            Just (IntrinsicTyCon _ CanonicalOpaque) -> Right AsOpaque
            Just (DataTyCon _ _) -> Left (DataType name)
            _ -> Left (NoValue t)
      Nothing -> Left (NoValue t)

  -- the constructor a type applies, and what it is applied to
  headOf t = go t []
    where
    go x arguments = case x of
      TApp f a -> go f (Array.cons a arguments)
      TCon name _ -> Just { name, arguments }
      _ -> Nothing

derive instance Eq Position
derive instance Eq Refusal

instance Show Position where
  show = case _ of
    Argument n -> "Argument " <> show n
    Result -> "Result"

instance Show Refusal where
  show = case _ of
    DataType n -> "DataType " <> show n
    RecordType -> "RecordType"
    VariantType -> "VariantType"
    FunctionType -> "FunctionType"
    TypeVariable v -> "TypeVariable " <> show v
    ActionArgument -> "ActionArgument"
    ActionOfAction -> "ActionOfAction"
    ConstrainedType -> "ConstrainedType"
    PerformingArrow -> "PerformingArrow"
    NoValue t -> "NoValue " <> show t
