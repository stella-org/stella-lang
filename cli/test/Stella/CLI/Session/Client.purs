-- | How the client judges a session that ends before it opens, over a process of
-- | the test's own: a channel answering one event, and an exit already known.
module Test.Stella.CLI.Session.Client (spec) where

import Prelude

import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Effect.Aff (Aff)
import Run (runBaseAff')
import Stella.CLI.Effect.Process (Exit, Process(..))
import Stella.CLI.Effect.Process as Process
import Stella.CLI.Effect.Transport (ChannelEvent(..))
import Stella.CLI.Session.Client (ClientFailure(..), OpenFailure(..), open)
import Stella.CLI.Session.Frame (maxPayload, u32BE)
import Stella.CLI.Session.Peer (SessionFailure(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

-- | Opening a session over a process whose channel answers `event` to every
-- | `receive`, and which ended with status 1.
openingOver :: ChannelEvent -> Aff (Either OpenFailure Unit)
openingOver event = map (map (const unit)) $ runBaseAff' $ Process.interpret handler $ open
  { command: "steam"
  , args: []
  , output: Process.Inherit
  , hello: { protocol: 1, profile: "elaboration", offers: [], requires: [] }
  }
  where
  handler :: Process ~> _
  handler (SpawnSession _ reply) = pure $ reply
    { channel: Just
        { send: \_ -> pure unit
        , receive: pure event
        , end: pure unit
        , destroy: pure unit
        }
    , exit: pure exited
    , kill: pure unit
    }

exited :: Exit
exited = { code: Just 1, signal: Nothing, error: Nothing }

spec :: Spec Unit
spec = describe "a session that ends before it opens" do
  it "is a process that ended unannounced, where the channel ended" do
    openingOver Ended >>= (_ `shouldEqual` Left (OpenFailed (ExitedUnannounced exited)))

  -- a process exiting with what was sent to it unread resets the channel on some
  -- hosts (`ECONNRESET` on Linux) where it ends it on others
  it "is a process that ended unannounced, where the host reported the channel failed" do
    openingOver (Failed "read ECONNRESET") >>= (_ `shouldEqual` Left (OpenFailed (ExitedUnannounced exited)))

  it "keeps what this side judged of the channel as the cause" do
    openingOver (Received (u32BE (maxPayload + 1))) >>= case _ of
      Left (OpenFailed (ChannelLost (FrameUnreadable _) exit)) -> exit `shouldEqual` exited
      other -> fail ("the unreadable frame was not kept: " <> show other)
