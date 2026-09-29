-- | The runtime shape descriptor: what a value of each data type of `Stella.Elab`
-- | looks like once types are gone.
-- |
-- | **A value handed to a guest has to be one its type admits**, and a `.dmo` carries
-- | no type to check it against. The machine answering a guest's `command` resumes
-- | it with a value whose static type is `GuestAnswer`; one of another shape reaches
-- | a constructor dispatch that cannot take it, which is a defect of the interpreter
-- | rather than of whoever sent the value. The descriptor is what lets a machine
-- | check the value before resuming, without knowing the kernel's vocabulary itself:
-- | it is data, read by a checker that knows only this grammar.
-- |
-- | **It is derived from the module, not written beside it**, so the two cannot
-- | disagree: every field of every constructor is read off the data declaration
-- | that declares it.
module Stella.Compiler.Elaborate.Protocol.Guest.Shape
  ( Shape(..)
  , FieldShape
  , ConstructorShape
  , TypeShape
  , Descriptor
  , describe
  , typeShape
  ) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldM)
import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Show.Generic (genericShow)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Stella.Compiler.TypedCore (Decl(..), Ident, Module, Qualified(..), RowEntry(..), RowKey(..), Symbol(..), TyName, TyVar, Type(..))
import Stella.Compiler.TypedCore.Prim (booleanTy, charTy, intTy, numberTy, recordTy, stringTy)

-- | The shape of one field.
data Shape
  = ShapeInt
  | ShapeNumber
  | ShapeChar
  | ShapeString
  | ShapeBoolean
  -- | A host token: the value is opaque and stands for a handle the host issued.
  | ShapeToken
  -- | A record, by its fields in ascending order of key.
  | ShapeRecord (P.Array FieldShape)
  -- | The data type's own parameter at that position.
  | ShapeParam P.Int
  -- | A data type of the module, applied to the shapes of its arguments.
  | ShapeData (Qualified TyName) (P.Array Shape)

derive instance Eq Shape
derive instance Generic Shape _
instance Show Shape where
  show x = genericShow x

type FieldShape = { key :: P.String, shape :: Shape }

type ConstructorShape = { name :: Qualified Ident, fields :: P.Array Shape }

type TypeShape = { params :: P.Int, constructors :: P.Array ConstructorShape }

-- | Every data type of the module, by its qualified name.
type Descriptor = Map (Qualified TyName) TypeShape

-- | The descriptor of a module whose data types hold only literals, tokens of the
-- | given type, records, their own parameters, and data types of the same module.
-- | Anything else is refused, naming the field: the descriptor would have no shape
-- | to give it.
describe :: forall a. Qualified TyName -> Module a -> Either P.String Descriptor
describe token m = do
  let
    datas = Array.mapMaybe
      ( case _ of
          DeclData _ d -> Just d
          _ -> Nothing
      )
      m.decls
    arities = Map.fromFoldable
      (map (\d -> Tuple (Qualified m.name d.name) (Array.length d.params)) datas)
  foldM
    ( \acc d -> do
        let params = map _.name d.params
        constructors <- traverse
          ( \c -> do
              fields <- traverse (shapeOf token arities params) c.fields
              pure { name: Qualified m.name c.name, fields }
          )
          d.constructors
        pure (Map.insert (Qualified m.name d.name) { params: Array.length params, constructors } acc)
    )
    Map.empty
    datas

shapeOf
  :: Qualified TyName
  -> Map (Qualified TyName) P.Int
  -> P.Array TyVar
  -> Type
  -> Either P.String Shape
shapeOf token arities params = go
  where
  go = case _ of
    TCon name []
      | name == intTy -> Right ShapeInt
      | name == numberTy -> Right ShapeNumber
      | name == charTy -> Right ShapeChar
      | name == stringTy -> Right ShapeString
      | name == booleanTy -> Right ShapeBoolean
      | name == token -> Right ShapeToken
    TVar v -> case Array.elemIndex v params of
      Just i -> Right (ShapeParam i)
      Nothing -> Left ("a type variable that is not a parameter: " <> show v)
    TApp (TCon name []) row | name == recordTy -> ShapeRecord <$> fieldsOf row
    other -> case spine other [] of
      Just { head, args } -> case Map.lookup head arities of
        Just arity
          | arity == Array.length args -> ShapeData head <$> traverse go args
          | otherwise -> Left ("a data type applied to the wrong number of arguments: " <> show head)
        Nothing -> Left ("a type with no shape: " <> show other)
      Nothing -> Left ("a type with no shape: " <> show other)

  spine t args = case t of
    TCon head [] -> Just { head, args }
    TApp f x -> spine f (Array.cons x args)
    _ -> Nothing

  fieldsOf row = do
    fields <- collect row []
    pure (Array.sortWith _.key fields)

  collect row acc = case row of
    TRowEmpty -> Right acc
    TRowExtend (RowTypeEntry (SymbolKey (Symbol key)) t) rest -> do
      shape <- go t
      collect rest (Array.snoc acc { key, shape })
    other -> Left ("a record row with no shape: " <> show other)

-- | The shape of a data type, where the descriptor holds it.
typeShape :: Qualified TyName -> Descriptor -> Maybe TypeShape
typeShape = Map.lookup
