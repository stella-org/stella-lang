-- | The frames a session's channel carries.
-- |
-- | ```text
-- | frame   = length payload
-- | length  = unsigned 32-bit big-endian, the byte count of payload
-- | payload = a JSON object, in UTF-8
-- | ```
-- |
-- | **A frame is cut out of the bytes as they arrive**, not out of one read: a
-- | channel may deliver several frames in one chunk and one frame across several,
-- | and a `Reader` holds whatever has arrived of the next frame until the rest does.
-- | The chunks are joined once a frame is complete, not as each arrives, so a large
-- | frame costs its size once.
-- |
-- | Two kinds of trouble are kept apart. A length above `maxPayload`, and a channel
-- | ending inside a frame, leave no boundary to trust, so the session cannot go
-- | on: those are a `FrameFailure`. A payload that is not a JSON object, where the
-- | length was honest, leaves the next frame where it was: that is a
-- | `PayloadProblem`, and the session answers it and continues.
module Stella.CLI.Session.Frame
  ( maxPayload
  , FrameFailure(..)
  , Reader
  , emptyReader
  , feed
  , finish
  , frame
  , u32BE
  , PayloadProblem(..)
  , parsePayload
  , renderPayload
  ) where

import Prelude

import Data.Argonaut.Core (Json, caseJsonObject, fromObject, stringify)
import Data.Argonaut.Parser (jsonParser)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Generic.Rep (class Generic)
import Data.Int (toNumber)
import Data.Int as Int
import Data.Int.Bits as Bits
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Show.Generic (genericShow)
import Foreign.Object (Object)
import Stella.Compiler.Bytecode.Bytes (Bytes, runR, utf8, utf8R)
import Stella.Compiler.TypedCore.Domain (textOf)

-- | The largest payload, in bytes: 16 MiB. A module crosses as a path rather than
-- | as its bytes, so nothing a session carries comes near it.
maxPayload :: Int
maxPayload = 16 * 1024 * 1024

-- | What leaves the channel with no frame boundary to trust.
data FrameFailure
  -- | A length above `maxPayload`, as the length read.
  = Oversized Number
  -- | The channel ended inside a length, as the bytes of it that had arrived.
  | TruncatedPrefix Int
  -- | The channel ended inside a payload, as the length and the bytes of the
  -- | payload that had arrived.
  | TruncatedPayload { expected :: Int, received :: Int }

derive instance Eq FrameFailure
derive instance Generic FrameFailure _
instance Show FrameFailure where
  show = genericShow

-- | What has arrived of the next frame: the chunks in order, and how many bytes
-- | they hold together.
newtype Reader = Reader { chunks :: Array Bytes, size :: Int }

emptyReader :: Reader
emptyReader = Reader { chunks: [], size: 0 }

-- | Take in a chunk and hand back every payload it completes, in order.
feed :: Bytes -> Reader -> Either FrameFailure { payloads :: Array Bytes, reader :: Reader }
feed chunk (Reader held) = do
  let
    chunks = Array.snoc held.chunks chunk
    size = held.size + Array.length chunk
    waiting = Right { payloads: [], reader: Reader { chunks, size } }
  if size < 4 then waiting
  else do
    let declared = lengthAt 0 (Array.take 4 (Array.concat (Array.take 4 chunks)))
    if declared > toNumber maxPayload then Left (Oversized declared)
    else if size < 4 + Int.floor declared then waiting
    else scan (Array.concat chunks) 0 []

-- Every complete frame from `offset` on, and what is left as the next frame's.
scan :: Bytes -> Int -> Array Bytes -> Either FrameFailure { payloads :: Array Bytes, reader :: Reader }
scan bytes offset payloads
  | Array.length bytes - offset < 4 = Right { payloads, reader: restFrom offset bytes }
  | otherwise =
      let
        declared = lengthAt offset bytes
        end = offset + 4 + Int.floor declared
      in
        if declared > toNumber maxPayload then Left (Oversized declared)
        else if Array.length bytes < end then Right { payloads, reader: restFrom offset bytes }
        else scan bytes end (Array.snoc payloads (Array.slice (offset + 4) end bytes))

-- What is left from `offset` on, as the start of the next frame.
restFrom :: Int -> Bytes -> Reader
restFrom offset bytes =
  let
    remaining = Array.drop offset bytes
  in
    if Array.null remaining then emptyReader
    else Reader { chunks: [ remaining ], size: Array.length remaining }

-- The unsigned 32-bit big-endian integer at `offset`. The caller has checked that
-- four bytes stand there.
lengthAt :: Int -> Bytes -> Number
lengthAt offset bytes =
  byte 0 * 16777216.0 + byte 1 * 65536.0 + byte 2 * 256.0 + byte 3
  where
  byte i = toNumber (fromMaybe 0 (Array.index bytes (offset + i)))

-- | What the channel ending leaves: nothing where it ended between frames, and the
-- | failure where it ended inside one.
finish :: Reader -> Maybe FrameFailure
finish (Reader held)
  | held.size == 0 = Nothing
  | held.size < 4 = Just (TruncatedPrefix held.size)
  | otherwise = Just
      ( TruncatedPayload
          { expected: Int.floor (lengthAt 0 (Array.concat held.chunks))
          , received: held.size - 4
          }
      )

-- | Four bytes, big-endian, of an integer in `0 … 2³¹−1`.
u32BE :: Int -> Bytes
u32BE n = map (\shift -> Bits.and (Bits.zshr n shift) 0xFF) [ 24, 16, 8, 0 ]

-- | A payload framed with its length, or the length where it is above
-- | `maxPayload`. A sender refuses such a payload rather than writing a frame no
-- | reader may read.
frame :: Bytes -> Either FrameFailure Bytes
frame payload
  | Array.length payload > maxPayload = Left (Oversized (toNumber (Array.length payload)))
  | otherwise = Right (u32BE (Array.length payload) <> payload)

-- | What makes a payload not a message, the boundary around it being intact.
data PayloadProblem
  = EmptyPayload
  | NotUtf8
  | NotJson String
  | NotAnObject

derive instance Eq PayloadProblem
derive instance Generic PayloadProblem _
instance Show PayloadProblem where
  show = genericShow

-- | The JSON object a payload holds.
parsePayload :: Bytes -> Either PayloadProblem (Object Json)
parsePayload payload
  | Array.null payload = Left EmptyPayload
  | otherwise = case runR payload (utf8R (Array.length payload)) of
      Left _ -> Left NotUtf8
      Right text -> case jsonParser (textOf text) of
        Left reason -> Left (NotJson reason)
        Right json -> caseJsonObject (Left NotAnObject) Right json

-- | The bytes of a JSON object, as a payload. **JSON text holds no unpaired
-- | surrogate**, one in a string being written as an escape, so the encoding
-- | always succeeds; `Nothing` would mean a serializer that did not escape one.
renderPayload :: Object Json -> Maybe Bytes
renderPayload object = case utf8 (stringify (fromObject object)) of
  Left _ -> Nothing
  Right bytes -> Just bytes
