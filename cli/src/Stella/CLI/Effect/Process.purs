-- | Starting a session process.
-- |
-- | **The operation is an effect rather than a call into the host**, for the reason
-- | the channel is ([Transport](Transport.purs)): what starting a process means, and
-- | how its channel is opened, is the handler's.
-- |
-- | What comes back is a `Child`: its channel, how it ended, and a way to end it,
-- | as operations over `Aff` and `Effect` that name nothing of the host.
module Stella.CLI.Effect.Process
  ( Output(..)
  , Exit
  , Child
  , Launch
  , Process(..)
  , PROCESS
  , _process
  , interpret
  , spawnSession
  ) where

import Prelude

import Data.Maybe (Maybe)
import Effect (Effect)
import Effect.Aff (Aff)
import Prim as P
import Run (Run)
import Run as Run
import Stella.CLI.Effect.Transport (Channel)
import Type.Proxy (Proxy(..))
import Type.Row (type (+))

-- | Where the child's standard output and standard error go: inherited, or read
-- | continuously into the functions given. **Either way something reads them**: a
-- | pipe nobody reads fills up, and a child writing into a full pipe stops.
data Output
  = Inherit
  | Drain { stdout :: P.String -> Effect Unit, stderr :: P.String -> Effect Unit }

-- | How the child ended: its exit code, or the signal that ended it, or why it
-- | never started.
type Exit = { code :: Maybe P.Int, signal :: Maybe P.String, error :: Maybe P.String }

-- | A started child. `channel` is absent where it never started. `exit` completes
-- | once the child has ended and everything it wrote on its channel has arrived.
-- | `kill` ends it at once, and does nothing where it has ended.
type Child =
  { channel :: Maybe Channel
  , exit :: Aff Exit
  , kill :: Effect Unit
  }

type Launch = { command :: P.String, args :: P.Array P.String, output :: Output }

-- | **A child that does not start is still answered with a `Child`**, whose
-- | `exit` says why: the caller learns it by the one route it learns every ending
-- | by.
data Process a = SpawnSession Launch (Child -> a)

derive instance Functor Process

type PROCESS r = (process :: Process | r)

_process :: Proxy "process"
_process = Proxy

interpret :: forall r a. (Process ~> Run r) -> Run (PROCESS + r) a -> Run r a
interpret handler = Run.interpret (Run.on _process handler Run.send)

-- | Start the command with a session channel of its own.
spawnSession :: forall r. Launch -> Run (PROCESS + r) Child
spawnSession launch = Run.lift _process (SpawnSession launch identity)
