-- | The messages of a session's lifecycle, and how a handshake is decided.
-- |
-- | ```text
-- | hello  { protocol, profile, offers, requires }   → ready or refused
-- | ping   {}                                        → pong
-- | close  {}                                        → closed
-- | ```
-- |
-- | **The three requests above are the protocol itself** and every session answers
-- | them, whatever it negotiated. A capability names an optional family of requests
-- | beyond them: `offers` are the capabilities the client can use and `requires`
-- | those without which it will not open, and `ready` names those in force. **A
-- | session opens with one profile and the capabilities the handshake settled, and
-- | neither changes afterwards**; a request of a family not in force is refused.
-- | Only what is implemented is advertised: `modules`, which loads modules into the
-- | session; `invoke`, which applies a guest function to tokens; `kernel`, which a
-- | running invocation asks the client by; and `parse`, which runs a parser a loaded
-- | module declares.
-- |
-- | **A capability may need another in force beside it**: `parse` runs what
-- | `modules` loaded, so it needs `modules`. One asked for without what it needs is
-- | not put in force, and a session required to put it in force is refused as
-- | `capabilityIncomplete`.
module Stella.CLI.Session.Protocol
  ( protocolVersion
  , elaborationProfile
  , modulesCapability
  , invokeCapability
  , kernelCapability
  , parseCapability
  , supportedCapabilities
  , capabilityFor
  , Hello
  , Ready
  , Refusal
  , RefusalReason(..)
  , Supported
  , supported
  , negotiate
  , helloKind
  , readyKind
  , refusedKind
  , pingKind
  , pongKind
  , closeKind
  , closedKind
  , encodeHello
  , decodeHello
  , encodeReady
  , decodeReady
  , encodeRefusal
  , decodeRefusal
  , emptyPayload
  ) where

import Prelude

import Data.Argonaut.Core (Json, caseJsonArray, caseJsonNumber, caseJsonObject, caseJsonString, fromArray, fromNumber, fromObject, fromString)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Generic.Rep (class Generic)
import Data.Int as Int
import Data.Maybe (Maybe(..))
import Data.Show.Generic (genericShow)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Foreign.Object (Object)
import Foreign.Object as Object

protocolVersion :: Int
protocolVersion = 1

-- | The profile a compiler opens a session with to run synthesizers. It is the only
-- | one a session opens with yet.
elaborationProfile :: String
elaborationProfile = "elaboration"

-- | `load`.
modulesCapability :: String
modulesCapability = "modules"

-- | `invoke`.
invokeCapability :: String
invokeCapability = "invoke"

-- | `kernel`: a running invocation asks the client, which is the one request
-- | family the session sends rather than answers.
kernelCapability :: String
kernelCapability = "kernel"

-- | `parse`.
parseCapability :: String
parseCapability = "parse"

-- | The capabilities this side can put in force.
supportedCapabilities :: Array String
supportedCapabilities = [ modulesCapability, invokeCapability, kernelCapability, parseCapability ]

-- | The capabilities one needs in force beside it.
needs :: String -> Array String
needs = case _ of
  "parse" -> [ modulesCapability ]
  _ -> []

-- | The capability a request of that kind belongs to, where it belongs to one. The
-- | lifecycle requests belong to none, being the protocol itself.
capabilityFor :: String -> Maybe String
capabilityFor = case _ of
  "load" -> Just modulesCapability
  "invoke" -> Just invokeCapability
  "cancel" -> Just invokeCapability
  "kernel" -> Just kernelCapability
  "parse" -> Just parseCapability
  _ -> Nothing

type Hello =
  { protocol :: Int
  , profile :: String
  , offers :: Array String
  , requires :: Array String
  }

type Ready =
  { protocol :: Int
  , profile :: String
  , capabilities :: Array String
  }

data RefusalReason
  = ProtocolUnsupported
  | ProfileUnsupported
  | CapabilityUnsupported
  -- | A capability required, and what it needs not asked for.
  | CapabilityIncomplete

derive instance Eq RefusalReason
derive instance Generic RefusalReason _
instance Show RefusalReason where
  show = genericShow

-- | What a side can open a session with.
type Supported =
  { protocols :: Array Int
  , profiles :: Array String
  , capabilities :: Array String
  }

type Refusal = { reason :: RefusalReason, supported :: Supported }

supported :: Supported
supported =
  { protocols: [ protocolVersion ]
  , profiles: [ elaborationProfile ]
  , capabilities: supportedCapabilities
  }

-- | Open, or say why not. The capabilities in force are those asked for, by
-- | `offers` or `requires`, that this side has and whose needs are among them;
-- | every one required must be in force.
negotiate :: Hello -> Either Refusal Ready
negotiate hello
  | hello.protocol /= protocolVersion = refuse ProtocolUnsupported
  | hello.profile /= elaborationProfile = refuse ProfileUnsupported
  | not (Array.all (_ `Array.elem` supportedCapabilities) hello.requires) =
      refuse CapabilityUnsupported
  | otherwise =
      let
        asked = Array.filter (\c -> Array.elem c hello.offers || Array.elem c hello.requires) supportedCapabilities
        inForce = Array.filter (\c -> Array.all (_ `Array.elem` asked) (needs c)) asked
      in
        if Array.all (_ `Array.elem` inForce) hello.requires then
          Right { protocol: protocolVersion, profile: hello.profile, capabilities: inForce }
        else refuse CapabilityIncomplete

refuse :: RefusalReason -> Either Refusal Ready
refuse reason = Left { reason, supported }

helloKind :: String
helloKind = "hello"

readyKind :: String
readyKind = "ready"

refusedKind :: String
refusedKind = "refused"

pingKind :: String
pingKind = "ping"

pongKind :: String
pongKind = "pong"

closeKind :: String
closeKind = "close"

closedKind :: String
closedKind = "closed"

emptyPayload :: Object Json
emptyPayload = Object.empty

encodeHello :: Hello -> Object Json
encodeHello h = Object.fromFoldable
  [ Tuple "protocol" (int h.protocol)
  , Tuple "profile" (fromString h.profile)
  , Tuple "offers" (strings h.offers)
  , Tuple "requires" (strings h.requires)
  ]

decodeHello :: Object Json -> Maybe Hello
decodeHello o = do
  protocol <- field "protocol" o >>= intOf
  profile <- field "profile" o >>= stringOf
  offers <- field "offers" o >>= stringsOf
  requires <- field "requires" o >>= stringsOf
  pure { protocol, profile, offers, requires }

encodeReady :: Ready -> Object Json
encodeReady r = Object.fromFoldable
  [ Tuple "protocol" (int r.protocol)
  , Tuple "profile" (fromString r.profile)
  , Tuple "capabilities" (strings r.capabilities)
  ]

decodeReady :: Object Json -> Maybe Ready
decodeReady o = do
  protocol <- field "protocol" o >>= intOf
  profile <- field "profile" o >>= stringOf
  capabilities <- field "capabilities" o >>= stringsOf
  pure { protocol, profile, capabilities }

encodeRefusal :: Refusal -> Object Json
encodeRefusal r = Object.fromFoldable
  [ Tuple "reason" (fromString (reasonCode r.reason))
  , Tuple "supported" $ fromObject $ Object.fromFoldable
      [ Tuple "protocols" (fromArray (map int r.supported.protocols))
      , Tuple "profiles" (strings r.supported.profiles)
      , Tuple "capabilities" (strings r.supported.capabilities)
      ]
  ]

decodeRefusal :: Object Json -> Maybe Refusal
decodeRefusal o = do
  reason <- field "reason" o >>= stringOf >>= reasonOf
  s <- field "supported" o >>= caseJsonObject Nothing Just
  protocols <- field "protocols" s >>= caseJsonArray Nothing Just >>= traverse intOf
  profiles <- field "profiles" s >>= stringsOf
  capabilities <- field "capabilities" s >>= stringsOf
  pure { reason, supported: { protocols, profiles, capabilities } }

reasonCode :: RefusalReason -> String
reasonCode = case _ of
  ProtocolUnsupported -> "protocol"
  ProfileUnsupported -> "profile"
  CapabilityUnsupported -> "capability"
  CapabilityIncomplete -> "capabilityIncomplete"

reasonOf :: String -> Maybe RefusalReason
reasonOf = case _ of
  "protocol" -> Just ProtocolUnsupported
  "profile" -> Just ProfileUnsupported
  "capability" -> Just CapabilityUnsupported
  "capabilityIncomplete" -> Just CapabilityIncomplete
  _ -> Nothing

field :: String -> Object Json -> Maybe Json
field = Object.lookup

int :: Int -> Json
int = fromNumber <<< Int.toNumber

strings :: Array String -> Json
strings = fromArray <<< map fromString

intOf :: Json -> Maybe Int
intOf = caseJsonNumber Nothing Int.fromNumber

stringOf :: Json -> Maybe String
stringOf = caseJsonString Nothing Just

stringsOf :: Json -> Maybe (Array String)
stringsOf = caseJsonArray Nothing Just >=> traverse stringOf
