-- | The envelope every message of a session travels in.
-- |
-- | ```text
-- | request      = { kind, id, payload }
-- | response     = { kind, replyTo, payload }
-- | notification = { kind, payload }
-- | ```
-- |
-- | **Each side numbers its own requests**, from 1 and never reusing one, and a
-- | response names by `replyTo` a request the side receiving it sent. The two
-- | numberings are independent, so a request of either side can stand inside a
-- | request of the other and each response still finds its way back. Whatever a
-- | message is about beyond that — an attempt, a module — travels in its payload.
module Stella.CLI.Session.Envelope
  ( MessageId
  , messageId
  , firstMessageId
  , nextMessageId
  , messageIdValue
  , Message(..)
  , EnvelopeReason(..)
  , EnvelopeProblem
  , decodeMessage
  , encodeMessage
  , kindOf
  ) where

import Prelude

import Data.Argonaut.Core (Json, caseJsonNumber, caseJsonObject, caseJsonString, fromNumber, fromObject, fromString)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Generic.Rep (class Generic)
import Data.Int (fromNumber, toNumber) as Int
import Data.Maybe (Maybe(..))
import Data.Show.Generic (genericShow)
import Data.Tuple (Tuple(..))
import Foreign.Object (Object)
import Foreign.Object as Object

-- | A request's number within the side that sent it: `1 … 2³¹−1`.
newtype MessageId = MessageId Int

derive instance Eq MessageId
derive instance Ord MessageId
instance Show MessageId where
  show (MessageId n) = "(MessageId " <> show n <> ")"

-- | The number, where it is in range.
messageId :: Int -> Maybe MessageId
messageId n
  | n >= 1 && n <= idCeiling = Just (MessageId n)
  | otherwise = Nothing

firstMessageId :: MessageId
firstMessageId = MessageId 1

-- | The number after this one, or `Nothing` where none is left. **A side that has
-- | used every number stops rather than wrapping**, since a late response could
-- | still name a number it would reissue.
nextMessageId :: MessageId -> Maybe MessageId
nextMessageId (MessageId n)
  | n < idCeiling = Just (MessageId (n + 1))
  | otherwise = Nothing

messageIdValue :: MessageId -> Int
messageIdValue (MessageId n) = n

idCeiling :: Int
idCeiling = 2147483647

data Message
  = Request { kind :: String, id :: MessageId, payload :: Object Json }
  | Response { kind :: String, replyTo :: MessageId, payload :: Object Json }
  | Notification { kind :: String, payload :: Object Json }

derive instance Eq Message
derive instance Generic Message _
instance Show Message where
  show = case _ of
    Request r -> "(Request " <> r.kind <> " " <> show r.id <> ")"
    Response r -> "(Response " <> r.kind <> " " <> show r.replyTo <> ")"
    Notification r -> "(Notification " <> r.kind <> ")"

kindOf :: Message -> String
kindOf = case _ of
  Request r -> r.kind
  Response r -> r.kind
  Notification r -> r.kind

-- | What makes an object not an envelope.
data EnvelopeReason
  = KindMissing
  | PayloadMissing
  -- | An `id` or a `replyTo` that is not a number in range.
  | IdMalformed
  | ReplyToMalformed
  | IdAndReplyTo
  -- | A field the envelope does not have, by its name.
  | FieldUnknown String

derive instance Eq EnvelopeReason
derive instance Generic EnvelopeReason _
instance Show EnvelopeReason where
  show = genericShow

-- | Why an object is not an envelope, with the request it can be answered as
-- | where it names one. **A problem is answerable exactly when the object carries
-- | a well-formed `id` and no `replyTo`**; any other is answered as a notification.
type EnvelopeProblem = { reason :: EnvelopeReason, answerable :: Maybe MessageId }

decodeMessage :: Object Json -> Either EnvelopeProblem Message
decodeMessage object = do
  let
    answerable = case Tuple (field "id") (field "replyTo") of
      Tuple (Just raw) Nothing -> idOf raw
      _ -> Nothing

    problem :: forall a. EnvelopeReason -> Either EnvelopeProblem a
    problem reason = Left { reason, answerable }
  case Array.find (\name -> not (Array.elem name known)) (Object.keys object) of
    Just unknown -> problem (FieldUnknown unknown)
    Nothing -> pure unit
  kind <- case field "kind" >>= caseJsonString Nothing Just of
    Nothing -> problem KindMissing
    Just k -> pure k
  payload <- case field "payload" >>= caseJsonObject Nothing Just of
    Nothing -> problem PayloadMissing
    Just p -> pure p
  case Tuple (field "id") (field "replyTo") of
    Tuple (Just _) (Just _) -> problem IdAndReplyTo
    Tuple (Just raw) Nothing -> case idOf raw of
      Nothing -> problem IdMalformed
      Just id -> Right (Request { kind, id, payload })
    Tuple Nothing (Just raw) -> case idOf raw of
      Nothing -> problem ReplyToMalformed
      Just replyTo -> Right (Response { kind, replyTo, payload })
    Tuple Nothing Nothing -> Right (Notification { kind, payload })
  where
  field name = Object.lookup name object
  known = [ "kind", "id", "replyTo", "payload" ]

idOf :: Json -> Maybe MessageId
idOf = caseJsonNumber Nothing (\n -> Int.fromNumber n >>= messageId)

encodeMessage :: Message -> Object Json
encodeMessage = case _ of
  Request r -> Object.fromFoldable
    [ Tuple "kind" (fromString r.kind)
    , Tuple "id" (number r.id)
    , Tuple "payload" (fromObject r.payload)
    ]
  Response r -> Object.fromFoldable
    [ Tuple "kind" (fromString r.kind)
    , Tuple "replyTo" (number r.replyTo)
    , Tuple "payload" (fromObject r.payload)
    ]
  Notification r -> Object.fromFoldable
    [ Tuple "kind" (fromString r.kind)
    , Tuple "payload" (fromObject r.payload)
    ]
  where
  number (MessageId n) = fromNumber (Int.toNumber n)
