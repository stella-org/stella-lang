-- | `steam session` started as a process a client launches, and the streams it
-- | answers on, for the tests that speak to one.
module Test.Steam.Session
  ( Streams
  , streams
  , draining
  , hello
  , node
  , open'
  , close'
  , ping'
  , request'
  , opened
  , steamChild
  ) where

import Prelude

import Data.Argonaut.Core (Json)
import Data.Either (Either(..))
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Foreign.Object as Object
import Run (AFF, EFFECT, Run, runBaseAff')
import Stella.CLI.Effect.Process (Child, Output(..), PROCESS, spawnSession)
import Stella.CLI.Effect.Process as Process
import Stella.CLI.Runner.Node (nodeProcessHandler)
import Type.Row (type (+))
import Stella.CLI.Session.Client (ClientFailure, OpenFailure, RequestFailure, Session)
import Stella.CLI.Session.Client as Client
import Stella.CLI.Session.Peer as Peer
import Stella.CLI.Session.Protocol (Hello)
import Test.Spec.Assertions (fail)

type Streams = { stdout :: Ref String, stderr :: Ref String }

streams :: Aff Streams
streams = liftEffect ({ stdout: _, stderr: _ } <$> Ref.new "" <*> Ref.new "")

draining :: Streams -> Output
draining s = Drain
  { stdout: \t -> Ref.modify_ (_ <> t) s.stdout
  , stderr: \t -> Ref.modify_ (_ <> t) s.stderr
  }

hello :: Hello
hello = { protocol: 1, profile: "elaboration", offers: [], requires: [] }

-- | Run what a client does, starting processes as this host does.
node :: forall a. Run (PROCESS + AFF + EFFECT + ()) a -> Aff a
node = runBaseAff' <<< Process.interpret nodeProcessHandler

open' :: Client.Launch -> Aff (Either OpenFailure Session)
open' = node <<< Client.open

ping' :: Session -> Aff (Either RequestFailure Unit)
ping' = node <<< Client.ping

close' :: Session -> Aff (Either ClientFailure Unit)
close' = node <<< Client.close

request' :: Session -> String -> Object.Object Json -> Aff (Either RequestFailure Peer.Reply)
request' session kind payload = node (Client.request session kind payload)

-- | `steam session`, started as a client would, without a handshake.
steamChild :: Streams -> Aff Child
steamChild s = node (spawnSession { command: "node", args: [ "steam/index.dev.js", "session" ], output: draining s })

opened :: Client.Launch -> (Session -> Aff Unit) -> Aff Unit
opened launch k = open' launch >>= case _ of
  Right session -> k session
  Left failure -> fail ("the session did not open: " <> show failure)
