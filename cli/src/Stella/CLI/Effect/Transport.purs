-- | Reaching the channel a session runs over.
-- |
-- | **The operation is an effect rather than a call into the host**, as reading a
-- | file is: what a channel is — a descriptor, a pipe, something else on another
-- | target — is the handler's, and the session logic above it is the same wherever
-- | it runs.
-- |
-- | What the effect hands back is a `Channel`: operations over `Bytes` and `Aff`,
-- | which name nothing of the host. A session keeps a receiver running beside the
-- | requests it makes, so the channel is a capability it holds rather than a series
-- | of effects it performs one at a time.
module Stella.CLI.Effect.Transport
  ( Channel
  , ChannelEvent(..)
  , Transport(..)
  , TRANSPORT
  , _transport
  , interpret
  , ownChannel
  ) where

import Prelude

import Data.Either (Either)
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Effect (Effect)
import Effect.Aff (Aff)
import Prim as P
import Run (Run)
import Run as Run
import Stella.Compiler.Bytecode.Bytes (Bytes)
import Type.Proxy (Proxy(..))
import Type.Row (type (+))

-- | What `receive` answers with.
data ChannelEvent
  -- | Bytes, in the order they were written.
  = Received Bytes
  -- | The other end wrote nothing more. Every later `receive` answers this too.
  | Ended
  -- | The channel failed, as what the host said. Every later `receive` answers
  -- | this too.
  | Failed P.String

derive instance Eq ChannelEvent
derive instance Generic ChannelEvent _
instance Show ChannelEvent where
  show = genericShow

-- | A bidirectional byte channel.
-- |
-- | `send` queues bytes after every byte sent before them. `receive` waits for
-- | what arrives next, which is at most one waiter's to have. `end` sends nothing
-- | more and completes once what was queued has been handed on. `destroy` releases
-- | the channel; a `receive` waiting then answers `Ended`.
type Channel =
  { send :: Bytes -> Effect Unit
  , receive :: Aff ChannelEvent
  , end :: Aff Unit
  , destroy :: Effect Unit
  }

-- | **A failure is answered rather than thrown**: a process started without a
-- | channel is the command's to report.
data Transport a = OwnChannel (Either P.String Channel -> a)

derive instance Functor Transport

type TRANSPORT r = (transport :: Transport | r)

_transport :: Proxy "transport"
_transport = Proxy

interpret :: forall r a. (Transport ~> Run r) -> Run (TRANSPORT + r) a -> Run r a
interpret handler = Run.interpret (Run.on _transport handler Run.send)

-- | The channel this process was started with, or what the host said about not
-- | having one.
ownChannel :: forall r. Run (TRANSPORT + r) (Either P.String Channel)
ownChannel = Run.lift _transport (OwnChannel identity)
