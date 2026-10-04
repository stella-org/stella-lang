-- | What a `.dmo` and a `.dmi` share past their primitives: a string table that
-- | every name is an index into, and sections, each an id and a length-prefixed
-- | payload, whose ids ascend through the file.
-- |
-- | **The string table is in order of first use with no string twice.** A
-- | writer interns each string as it is reached, so the order the sections are
-- | written in, and the order within each, decide the table; a format fixes
-- | both, and one value has one file.
-- |
-- | **An id at or above a format's boundary carries no meaning**, and a reader
-- | skips one it does not know; one below it bears on what the file means, and
-- | a reader that does not know it rejects the file.
module Stella.Compiler.Bytecode.Container
  ( Table
  , E
  , runE
  , throwE
  , liftE
  , str
  , qname
  , vec
  , vecOf
  , section
  , strings
  , Strings
  , Read
  , Layout
  , text
  , sectionR
  , trailingR
  , strR
  , qnameR
  ) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Either (Either(..))
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Stella.Compiler.Bytecode.Bytes (Bytes, DecodeError(..), EncodeError, R, TableKind(..), atEndR, byte, positionR, skipR, structuralR, throwR, u8, utf8, utf8R, uvar)
import Stella.Compiler.TypedCore.Domain (ScalarString)
import Stella.Compiler.TypedCore.Name (ModuleName(..), Qualified(..))

-- Writing ------------------------------------------------------------------------

-- | The string table as it is built: what each string was given, and the
-- | strings in the order they were first reached.
type Table =
  { indices :: Map P.String P.Int
  , strings :: P.Array P.String
  }

newtype E a = E (Table -> Either EncodeError (Tuple a Table))

runE :: forall a. Table -> E a -> Either EncodeError (Tuple a Table)
runE table (E f) = f table

instance Functor E where
  map f (E g) = E \t -> case g t of
    Left err -> Left err
    Right (Tuple a t') -> Right (Tuple (f a) t')

instance Apply E where
  apply = ap

instance Applicative E where
  pure a = E \t -> Right (Tuple a t)

instance Bind E where
  bind (E g) f = E \t -> case g t of
    Left err -> Left err
    Right (Tuple a t') -> case f a of E h -> h t'

instance Monad E

throwE :: forall a. EncodeError -> E a
throwE err = E \_ -> Left err

liftE :: forall a. Either EncodeError a -> E a
liftE = case _ of
  Left err -> throwE err
  Right a -> pure a

-- | A string, as the index it is given. One that has been written before keeps
-- | the index it was given, which is what leaves the table free of duplicates.
str :: P.String -> E Bytes
str s = E \t -> case Map.lookup s t.indices of
  Just i -> Right (Tuple (uvar i) t)
  Nothing ->
    let
      i = Array.length t.strings
    in
      Right
        ( Tuple (uvar i)
            { indices: Map.insert s i t.indices
            , strings: Array.snoc t.strings s
            }
        )

-- | A qualified name: the module, then the name within it.
qname :: forall a. (a -> P.String) -> Qualified a -> E Bytes
qname spelling (Qualified (ModuleName m) name) = do
  a <- str m
  b <- str (spelling name)
  pure (a <> b)

-- | A count, then that many of what follows it.
vec :: forall a. (a -> E Bytes) -> P.Array a -> E Bytes
vec item items = do
  written <- traverse item items
  pure (uvar (Array.length items) <> Array.concat written)

-- | The same, where the item needs no string.
vecOf :: forall a. (a -> Bytes) -> P.Array a -> Bytes
vecOf item items = uvar (Array.length items) <> Array.concatMap item items

section :: P.Int -> Bytes -> Bytes
section id payload = u8 id <> uvar (Array.length payload) <> payload

-- | The payload of the string table: a count, then each string, length-prefixed
-- | UTF-8.
strings :: P.Array P.String -> Either EncodeError Bytes
strings ss = do
  written <- traverse one ss
  pure (uvar (Array.length ss) <> Array.concat written)
  where
  one s = do
    bytes <- utf8 s
    pure (uvar (Array.length bytes) <> bytes)

-- Reading ------------------------------------------------------------------------

-- | The strings a file holds, which every name in it is an index into.
type Strings = P.Array P.String

-- | A section's payload together with the id it stood at, which the next section
-- | must exceed.
type Read a =
  { value :: a
  , previous :: P.Int
  }

-- | What a format says of its sections: the id at and above which one carries
-- | no meaning, and the ids a file holds whether or not they are empty.
type Layout =
  { skippableFrom :: P.Int
  , required :: P.Array P.Int
  }

-- | A length-prefixed run of UTF-8, which is how the string table and the
-- | header's text are written.
text :: R ScalarString
text = do
  n <- structuralR
  utf8R n

-- | One section, at the id it must stand at.
-- |
-- | The ids ascend strictly, so an id at or below the one before is out of order
-- | and a repeated section is the same failure. An unknown id at or above the
-- | boundary is skipped; one below it stops the reader.
sectionR :: forall a. Layout -> P.Int -> P.Int -> R a -> R (Read a)
sectionR layout previous wanted payload = go previous
  where
  go prev = do
    done <- atEndR
    if done then throwR (SectionMissing wanted)
    else do
      id <- byte
      len <- structuralR
      if id <= prev then throwR (SectionOutOfOrder prev id)
      else if id == wanted then do
        start <- positionR
        value <- payload
        end <- positionR
        if end - start /= len then throwR (SectionLengthMismatch id)
        else pure { value, previous: id }
      else if id >= layout.skippableFrom then do
        skipR len
        go id
      else if Array.elem id layout.required then throwR (SectionMissing wanted)
      else throwR (UnknownSection id)

-- | What stands after the last required section: sections above the boundary,
-- | in ascending order, and nothing else. One the format knows is read by the
-- | reader given for its id, and any other is skipped.
trailingR :: forall a. Layout -> (P.Int -> Maybe (R a)) -> P.Int -> R (P.Array (Tuple P.Int a))
trailingR layout known = go []
  where
  go acc previous = do
    done <- atEndR
    if done then pure acc
    else do
      id <- byte
      len <- structuralR
      if id <= previous then throwR (SectionOutOfOrder previous id)
      else if id < layout.skippableFrom then throwR (UnknownSection id)
      else case known id of
        Just payload -> do
          start <- positionR
          value <- payload
          end <- positionR
          if end - start /= len then throwR (SectionLengthMismatch id)
          else go (Array.snoc acc (Tuple id value)) id
        Nothing -> do
          skipR len
          go acc id

-- | A string, by its index into the table.
strR :: Strings -> R P.String
strR ss = do
  i <- structuralR
  case Array.index ss i of
    Nothing -> throwR (IndexOutOfRange StringTable i)
    Just s -> pure s

qnameR :: forall a. Strings -> (P.String -> a) -> R (Qualified a)
qnameR ss name = do
  m <- strR ss
  n <- strR ss
  pure (Qualified (ModuleName m) (name n))
