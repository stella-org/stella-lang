-- | What a side answers a message it cannot take with.
-- |
-- | **A protocol error is about the message and never about a program.** It says
-- | that what arrived was not something this protocol admits where it arrived, and
-- | the session goes on to the next message. It travels as a response where the
-- | message it answers is a request whose `id` could be read, and as a
-- | notification otherwise.
module Stella.CLI.Session.ProtocolError
  ( ProtocolError(..)
  , protocolErrorKind
  , encodeProtocolError
  , decodeProtocolError
  ) where

import Prelude

import Data.Argonaut.Core (Json, caseJsonString, fromString)
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..))
import Data.Show.Generic (genericShow)
import Data.Tuple (Tuple(..))
import Foreign.Object (Object)
import Foreign.Object as Object
import Stella.CLI.Session.Envelope (EnvelopeReason(..))
import Stella.CLI.Session.Frame (PayloadProblem(..))

data ProtocolError
  -- | A frame whose payload is not a JSON object.
  = PayloadUnreadable PayloadProblem
  -- | A JSON object that is not an envelope.
  | EnvelopeInvalid EnvelopeReason
  -- | A response naming no request this side has outstanding.
  | ReplyUnexpected
  -- | A request or notification of a kind this side does not know.
  | KindUnknown String
  -- | A request or notification of a known kind where it is not admitted — before
  -- | the handshake, or a second handshake.
  | KindUnexpected String
  -- | A request whose payload is not what its kind carries, as the kind.
  | PayloadInvalid String
  -- | A request of a family whose capability the handshake did not put in force,
  -- | as its kind.
  | CapabilityNotInForce String
  -- | A request whose `id` is not above every `id` the side sending it used
  -- | before. It is not run: a request sent twice would otherwise act twice.
  | IdReused
  -- | An `invoke` whose `attempt` is not above every `attempt` admitted before. It
  -- | is not run: an attempt once begun is never begun again.
  | AttemptNotAbove

derive instance Eq ProtocolError
derive instance Generic ProtocolError _
instance Show ProtocolError where
  show = genericShow

protocolErrorKind :: String
protocolErrorKind = "protocolError"

-- | `{ code, detail }`: a machine-readable code and a description a person reads.
encodeProtocolError :: ProtocolError -> Object Json
encodeProtocolError error = Object.fromFoldable
  [ Tuple "code" (fromString code)
  , Tuple "detail" (fromString detail)
  ]
  where
  Tuple code detail = case error of
    PayloadUnreadable problem -> Tuple "payloadUnreadable" case problem of
      EmptyPayload -> "the payload is empty"
      NotUtf8 -> "the payload is not well-formed UTF-8"
      NotJson reason -> "the payload is not JSON: " <> reason
      NotAnObject -> "the payload is not a JSON object"
    EnvelopeInvalid reason -> Tuple "envelopeInvalid" case reason of
      KindMissing -> "the message has no string `kind`"
      PayloadMissing -> "the message has no object `payload`"
      IdMalformed -> "`id` is not an integer from 1 to 2147483647"
      ReplyToMalformed -> "`replyTo` is not an integer from 1 to 2147483647"
      IdAndReplyTo -> "the message has both `id` and `replyTo`"
      FieldUnknown name -> "the message has an unknown field `" <> name <> "`"
    ReplyUnexpected -> Tuple "replyUnexpected"
      "the response names no request awaiting one"
    KindUnknown kind -> Tuple "kindUnknown" ("no message has the kind `" <> kind <> "`")
    KindUnexpected kind -> Tuple "kindUnexpected"
      ("a message of the kind `" <> kind <> "` is not admitted here")
    PayloadInvalid kind -> Tuple "payloadInvalid"
      ("the payload does not have the shape `" <> kind <> "` carries")
    CapabilityNotInForce kind -> Tuple "capabilityNotInForce"
      ("the capability a `" <> kind <> "` request belongs to is not in force")
    IdReused -> Tuple "idReused"
      "the request's `id` is not above every `id` used before"
    AttemptNotAbove -> Tuple "attemptNotAbove"
      "the invocation's `attempt` is not above every `attempt` admitted before"

-- | The code a protocol error carries, and its detail. A reader keeps the code as
-- | text: a code this side does not know is still a protocol error.
decodeProtocolError :: Object Json -> Maybe { code :: String, detail :: String }
decodeProtocolError payload = do
  code <- Object.lookup "code" payload >>= caseJsonString Nothing Just
  detail <- Object.lookup "detail" payload >>= caseJsonString Nothing Just
  pure { code, detail }
