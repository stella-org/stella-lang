-- | Whether a generic value is one a data type admits, as a runtime shape
-- | descriptor says.
-- |
-- | **A value can be canonical and still be no value of the type its place
-- | wants.** A guest resumed with one would reach a constructor dispatch that
-- | cannot take it, so the answer is checked whole before it is handed over. The
-- | checker knows only the descriptor's grammar and nothing of what the types
-- | mean: the kernel's vocabulary is the descriptor's.
-- |
-- | Like the codec, it walks the value with a stack of its own, so a value deep
-- | enough to be long is checked all the same.
module Stella.CLI.Session.Value.Shape
  ( conforms
  ) where

import Prelude

import Control.Monad.Rec.Class as Rec
import Data.Array as Array
import Data.Either (Either(..))
import Data.List (List(..), (:))
import Data.List as List
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Stella.CLI.Session.Value (Step(..), ValueProblem, WireValue(..))
import Stella.Compiler.Bytecode.Module (Key(..))
import Stella.Compiler.Elaborate.Protocol.Guest.Shape (Descriptor, Shape(..))
import Stella.Compiler.TypedCore.Name (Ident(..), ModuleName(..), Qualified(..), Symbol(..), TyName(..))

type Check = { path :: List Step, shape :: Shape, value :: WireValue }

-- | That the value is one of the named data type: a constructor of it, each field
-- | of the shape its declaration gives, a token exactly where a field is one.
conforms :: Descriptor -> Qualified TyName -> WireValue -> Either ValueProblem Unit
conforms descriptor top value = Rec.tailRec go ({ path: Nil, shape: ShapeData top [], value } : Nil)
  where
  go = case _ of
    Nil -> Rec.Done (Right unit)
    next : rest -> case check descriptor next of
      Left problem -> Rec.Done (Left problem)
      Right parts -> Rec.Loop (List.fromFoldable parts <> rest)

-- | What one value's shape asks of it, and the parts still to check.
check :: Descriptor -> Check -> Either ValueProblem (Array Check)
check descriptor { path, shape, value } = case shape, value of
  ShapeInt, WInt _ -> Right []
  ShapeNumber, WNumber _ -> Right []
  ShapeChar, WChar _ -> Right []
  ShapeString, WString _ -> Right []
  ShapeBoolean, WBoolean _ -> Right []
  ShapeToken, WToken _ -> Right []
  ShapeRecord fields, WRecord entries
    | Array.length fields == Array.length entries ->
        -- every field the shape names is among the entries, which with as many
        -- entries as fields leaves none twice and none besides
        traverse
          ( \field -> case Array.findIndex (\e -> e.key == KSymbol (Symbol field.key)) entries of
              Just i | Just entry <- Array.index entries i ->
                Right { path: Member "value" : Index i : Member "record" : path, shape: field.shape, value: entry.value }
              _ -> refuse path ("a record with the field " <> field.key)
          )
          fields
    | otherwise -> refuse path ("a record of " <> show (Array.length fields) <> " fields")
  ShapeData name args, WData ctor fields -> case Map.lookup name descriptor of
    Nothing -> refuse path ("a value of " <> typeText name <> ", which the descriptor does not hold")
    Just declared -> case Array.find (\c -> c.name == ctor) declared.constructors of
      Nothing -> refuse path ("a constructor of " <> typeText name <> ", not " <> ctorText ctor)
      Just c
        | Array.length c.fields /= Array.length fields ->
            refuse (Member "fields" : path)
              (ctorText ctor <> " with " <> show (Array.length c.fields) <> " fields")
        | otherwise -> Right $ Array.mapWithIndex
            (\i (Tuple field s) -> { path: Index i : Member "fields" : path, shape: given args s, value: field })
            (Array.zip fields c.fields)
  expected, _ -> refuse path (describe expected)

-- | A field's shape with the data type's arguments put for its parameters.
given :: Array Shape -> Shape -> Shape
given args = case _ of
  ShapeParam i -> fromMaybe (ShapeParam i) (Array.index args i)
  ShapeRecord fields -> ShapeRecord (map (\f -> f { shape = given args f.shape }) fields)
  ShapeData name inner -> ShapeData name (map (given args) inner)
  other -> other

describe :: Shape -> String
describe = case _ of
  ShapeInt -> "an int"
  ShapeNumber -> "a number"
  ShapeChar -> "a char"
  ShapeString -> "a string"
  ShapeBoolean -> "a boolean"
  ShapeToken -> "a token"
  ShapeRecord _ -> "a record"
  ShapeParam i -> "a value of the type's parameter " <> show i <> ", which nothing gave"
  ShapeData name _ -> "a value of " <> typeText name

typeText :: Qualified TyName -> String
typeText (Qualified (ModuleName m) (TyName t)) = m <> "." <> t

ctorText :: Qualified Ident -> String
ctorText (Qualified (ModuleName m) (Ident c)) = m <> "." <> c

refuse :: forall a. List Step -> String -> Either ValueProblem a
refuse path problem = Left { path: Array.reverse (Array.fromFoldable path), problem }
