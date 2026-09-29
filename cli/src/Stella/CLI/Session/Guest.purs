-- | The requests that load modules into a session and apply guest functions.
-- |
-- | ```text
-- | load    { path }                        → loaded { module } or loadFailed { stage, detail }
-- | invoke  { global: { module, name },     → returned { token }
-- |           arguments: [ token ],           or invocationFailed { reason, detail [, class] }
-- |           attempt }
-- | ```
-- |
-- | **An `attempt` names one invocation for good.** It is an integer from 1 to
-- | 2147483647, and each `invoke` a session admits carries one above every attempt
-- | it admitted before, whatever became of those; the `kernel` requests a running
-- | invocation makes carry it back ([Kernel](Kernel.purs)).
-- |
-- | **Every payload has exactly the fields shown**: a decoder refuses a missing
-- | field, a field of another type, and a field it does not know, so one payload
-- | has one reading.
-- |
-- | **A token is a JSON object the session never reads.** It is whatever the host
-- | handed over, and what comes back is the same JSON; nothing here gives it a
-- | shape.
module Stella.CLI.Session.Guest
  ( Token
  , GlobalName
  , InvokeRequest
  , attemptOf
  , LoadStage(..)
  , LoadFailure
  , InvocationReason(..)
  , ValueClass(..)
  , InvocationFailure
  , loadKind
  , loadedKind
  , loadFailedKind
  , invokeKind
  , returnedKind
  , invocationFailedKind
  , encodeLoad
  , decodeLoad
  , encodeLoaded
  , decodeLoaded
  , encodeLoadFailed
  , decodeLoadFailed
  , encodeInvoke
  , decodeInvoke
  , encodeReturned
  , decodeReturned
  , encodeInvocationFailed
  , decodeInvocationFailed
  ) where

import Prelude

import Data.Argonaut.Core (Json, caseJsonArray, caseJsonNumber, caseJsonObject, caseJsonString, fromArray, fromNumber, fromObject, fromString)
import Data.Array as Array
import Data.Generic.Rep (class Generic)
import Data.Int as Int
import Data.Maybe (Maybe(..))
import Data.Show.Generic (genericShow)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Foreign.Object (Object)
import Foreign.Object as Object

-- | What the host handed over, carried unread.
type Token = Object Json

-- | A top-level value, by its module and its name. **Two fields and not one
-- | dotted string**: a module name has dots in it, so one string would read two
-- | ways.
type GlobalName = { module :: String, name :: String }

data LoadStage
  -- | The path could not be read.
  = Unreadable
  -- | The bytes are not a `.dmo`.
  | NotBytecode
  -- | The implementations a manifest names could not be reached, or were not what
  -- | the module's foreigns need.
  | Foreigns
  -- | The loader refused the module.
  | Refused
  -- | A global of the module faulted as it was evaluated.
  | Initialization

derive instance Eq LoadStage
derive instance Generic LoadStage _
instance Show LoadStage where
  show = genericShow

type LoadFailure = { stage :: LoadStage, detail :: String }

data InvocationReason
  = NoSuchModule
  | NoSuchGlobal
  | NotCallable
  -- | The guest program faulted.
  | Fault
  -- | What the guest returned is not a token, as the class of value it is.
  | NotAToken ValueClass
  -- | The guest asked the kernel in a session whose `kernel` capability is not in
  -- | force.
  | KernelNotInForce
  -- | The guest asked the kernel with a value the wire has no form for, as the
  -- | class of the part that has none.
  | CommandNotEncodable ValueClass
  -- | The host ended the attempt while the guest waited for an answer.
  | Abandoned

derive instance Eq InvocationReason
derive instance Generic InvocationReason _
instance Show InvocationReason where
  show = genericShow

-- | The class of a value, which is all a failure says of one: the value itself
-- | stays where it is.
data ValueClass
  = ClassInt
  | ClassNumber
  | ClassChar
  | ClassString
  | ClassBoolean
  | ClassData
  | ClassRecord
  | ClassVariant
  | ClassClosure
  | ClassPartialApplication
  | ClassContinuation
  | ClassIO
  | ClassOpaque

derive instance Eq ValueClass
derive instance Generic ValueClass _
instance Show ValueClass where
  show = genericShow

type InvocationFailure = { reason :: InvocationReason, detail :: String }

loadKind :: String
loadKind = "load"

loadedKind :: String
loadedKind = "loaded"

loadFailedKind :: String
loadFailedKind = "loadFailed"

invokeKind :: String
invokeKind = "invoke"

returnedKind :: String
returnedKind = "returned"

invocationFailedKind :: String
invocationFailedKind = "invocationFailed"

-- Load --------------------------------------------------------------------------------

encodeLoad :: String -> Object Json
encodeLoad path = Object.singleton "path" (fromString path)

decodeLoad :: Object Json -> Maybe String
decodeLoad o = exactly [ "path" ] o *> (field "path" o >>= stringOf)

encodeLoaded :: String -> Object Json
encodeLoaded m = Object.singleton "module" (fromString m)

decodeLoaded :: Object Json -> Maybe String
decodeLoaded o = exactly [ "module" ] o *> (field "module" o >>= stringOf)

encodeLoadFailed :: LoadFailure -> Object Json
encodeLoadFailed f = Object.fromFoldable
  [ Tuple "stage" (fromString (stageCode f.stage))
  , Tuple "detail" (fromString f.detail)
  ]

decodeLoadFailed :: Object Json -> Maybe LoadFailure
decodeLoadFailed o = do
  exactly [ "stage", "detail" ] o
  stage <- field "stage" o >>= stringOf >>= stageOf
  detail <- field "detail" o >>= stringOf
  pure { stage, detail }

stageCode :: LoadStage -> String
stageCode = case _ of
  Unreadable -> "unreadable"
  NotBytecode -> "notBytecode"
  Foreigns -> "foreigns"
  Refused -> "refused"
  Initialization -> "initialization"

stageOf :: String -> Maybe LoadStage
stageOf = case _ of
  "unreadable" -> Just Unreadable
  "notBytecode" -> Just NotBytecode
  "foreigns" -> Just Foreigns
  "refused" -> Just Refused
  "initialization" -> Just Initialization
  _ -> Nothing

-- Invoke ------------------------------------------------------------------------------

-- | An `invoke`: the global applied, the tokens it is applied to, and the attempt
-- | it is.
type InvokeRequest = { global :: GlobalName, arguments :: Array Token, attempt :: Int }

encodeInvoke :: InvokeRequest -> Object Json
encodeInvoke r = Object.fromFoldable
  [ Tuple "global" $ fromObject $ Object.fromFoldable
      [ Tuple "module" (fromString r.global.module)
      , Tuple "name" (fromString r.global.name)
      ]
  , Tuple "arguments" (fromArray (map fromObject r.arguments))
  , Tuple "attempt" (fromNumber (Int.toNumber r.attempt))
  ]

-- | An `invoke` whose attempt is not an integer from 1 to 2147483647 has no
-- | reading.
decodeInvoke :: Object Json -> Maybe InvokeRequest
decodeInvoke o = do
  exactly [ "global", "arguments", "attempt" ] o
  g <- field "global" o >>= objectOf
  exactly [ "module", "name" ] g
  m <- field "module" g >>= stringOf
  name <- field "name" g >>= stringOf
  arguments <- field "arguments" o >>= caseJsonArray Nothing Just >>= traverse objectOf
  attempt <- field "attempt" o >>= attemptOf
  pure { global: { module: m, name }, arguments, attempt }

encodeReturned :: Token -> Object Json
encodeReturned token = Object.singleton "token" (fromObject token)

decodeReturned :: Object Json -> Maybe Token
decodeReturned o = exactly [ "token" ] o *> (field "token" o >>= objectOf)

-- | `class` stands exactly where the reason is `notAToken` or `commandNotEncodable`,
-- | and nowhere else.
encodeInvocationFailed :: InvocationFailure -> Object Json
encodeInvocationFailed f = Object.fromFoldable $
  [ Tuple "reason" (fromString (reasonCode f.reason))
  , Tuple "detail" (fromString f.detail)
  ] <> case f.reason of
    NotAToken class' -> [ Tuple "class" (fromString (classCode class')) ]
    CommandNotEncodable class' -> [ Tuple "class" (fromString (classCode class')) ]
    _ -> []

decodeInvocationFailed :: Object Json -> Maybe InvocationFailure
decodeInvocationFailed o = do
  code <- field "reason" o >>= stringOf
  detail <- field "detail" o >>= stringOf
  reason <- case code of
    "notAToken" -> do
      exactly [ "reason", "detail", "class" ] o
      NotAToken <$> (field "class" o >>= stringOf >>= classOf)
    "commandNotEncodable" -> do
      exactly [ "reason", "detail", "class" ] o
      CommandNotEncodable <$> (field "class" o >>= stringOf >>= classOf)
    _ -> do
      exactly [ "reason", "detail" ] o
      simpleReasonOf code
  pure { reason, detail }

reasonCode :: InvocationReason -> String
reasonCode = case _ of
  NoSuchModule -> "noSuchModule"
  NoSuchGlobal -> "noSuchGlobal"
  NotCallable -> "notCallable"
  Fault -> "fault"
  NotAToken _ -> "notAToken"
  KernelNotInForce -> "kernelNotInForce"
  CommandNotEncodable _ -> "commandNotEncodable"
  Abandoned -> "abandoned"

simpleReasonOf :: String -> Maybe InvocationReason
simpleReasonOf = case _ of
  "noSuchModule" -> Just NoSuchModule
  "noSuchGlobal" -> Just NoSuchGlobal
  "notCallable" -> Just NotCallable
  "fault" -> Just Fault
  "kernelNotInForce" -> Just KernelNotInForce
  "abandoned" -> Just Abandoned
  _ -> Nothing

classCode :: ValueClass -> String
classCode = case _ of
  ClassInt -> "int"
  ClassNumber -> "number"
  ClassChar -> "char"
  ClassString -> "string"
  ClassBoolean -> "boolean"
  ClassData -> "data"
  ClassRecord -> "record"
  ClassVariant -> "variant"
  ClassClosure -> "closure"
  ClassPartialApplication -> "partialApplication"
  ClassContinuation -> "continuation"
  ClassIO -> "io"
  ClassOpaque -> "opaque"

classOf :: String -> Maybe ValueClass
classOf code = Array.find (\c -> classCode c == code) allClasses

allClasses :: Array ValueClass
allClasses =
  [ ClassInt
  , ClassNumber
  , ClassChar
  , ClassString
  , ClassBoolean
  , ClassData
  , ClassRecord
  , ClassVariant
  , ClassClosure
  , ClassPartialApplication
  , ClassContinuation
  , ClassIO
  , ClassOpaque
  ]

-- Reading ------------------------------------------------------------------------------

-- | The object has exactly these fields.
exactly :: Array String -> Object Json -> Maybe Unit
exactly names o
  | Array.sort (Object.keys o) == Array.sort names = Just unit
  | otherwise = Nothing

field :: String -> Object Json -> Maybe Json
field = Object.lookup

stringOf :: Json -> Maybe String
stringOf = caseJsonString Nothing Just

objectOf :: Json -> Maybe (Object Json)
objectOf = caseJsonObject Nothing Just

-- | An attempt: an integer from 1 to 2147483647.
attemptOf :: Json -> Maybe Int
attemptOf json = do
  n <- caseJsonNumber Nothing Just json >>= Int.fromNumber
  if n >= 1 then Just n else Nothing
