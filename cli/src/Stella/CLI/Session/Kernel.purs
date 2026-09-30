-- | The request a running invocation makes of the client, and what answers it.
-- |
-- | ```text
-- | kernel  { attempt, command }   → answered { answer } or abandoned {}
-- | ```
-- |
-- | **This is the one request the session sends rather than answers.** A guest's
-- | `perform` of `Stella.Elab.Kernel.command` stops the invocation it runs in, and
-- | the session asks the client with the command as a generic value
-- | ([Value](Value.purs)). `attempt` is the one the `invoke` carried, so the client
-- | knows whose command it is. `answered` resumes the guest with the answer;
-- | `abandoned` says the host ended the attempt, and the guest does not go on.
-- |
-- | **Every payload has exactly the fields shown.** What `command` and `answer`
-- | hold is read here as JSON and no further: whether it is a canonical value, and
-- | one of the type its place wants, is the reader's to settle, since a failure of
-- | either is a different thing from a payload of the wrong shape.
module Stella.CLI.Session.Kernel
  ( KernelCall
  , kernelKind
  , answeredKind
  , abandonedKind
  , encodeKernel
  , decodeKernel
  , encodeAnswered
  , decodeAnswered
  , encodeAbandoned
  , decodeAbandoned
  ) where

import Prelude

import Data.Argonaut.Core (Json, fromNumber)
import Data.Array as Array
import Data.Int as Int
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Foreign.Object (Object)
import Foreign.Object as Object
import Stella.CLI.Session.Guest (positiveOf)

-- | A command, and the attempt that asks it.
type KernelCall = { attempt :: Int, command :: Json }

kernelKind :: String
kernelKind = "kernel"

answeredKind :: String
answeredKind = "answered"

abandonedKind :: String
abandonedKind = "abandoned"

encodeKernel :: KernelCall -> Object Json
encodeKernel call = Object.fromFoldable
  [ Tuple "attempt" (fromNumber (Int.toNumber call.attempt))
  , Tuple "command" call.command
  ]

decodeKernel :: Object Json -> Maybe KernelCall
decodeKernel o = do
  exactly [ "attempt", "command" ] o
  attempt <- Object.lookup "attempt" o >>= positiveOf
  command <- Object.lookup "command" o
  pure { attempt, command }

encodeAnswered :: Json -> Object Json
encodeAnswered = Object.singleton "answer"

decodeAnswered :: Object Json -> Maybe Json
decodeAnswered o = exactly [ "answer" ] o *> Object.lookup "answer" o

encodeAbandoned :: Object Json
encodeAbandoned = Object.empty

decodeAbandoned :: Object Json -> Maybe Unit
decodeAbandoned = exactly []

-- | The object has exactly these fields.
exactly :: Array String -> Object Json -> Maybe Unit
exactly names o
  | Array.sort (Object.keys o) == Array.sort names = Just unit
  | otherwise = Nothing
