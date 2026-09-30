-- | How the interpreter is tuned where nothing it answers depends on the tuning.
-- |
-- | **A setting is asked of a handler rather than fixed in the logic**, so that a
-- | test can run the same session under another one: the command runs under the
-- | interpreter's own values, and a test hands in what it varies.
module Steam.CLI.Effect.Tuning
  ( TUNING
  , Tuning(..)
  , TuningConfig
  , _tuning
  , defaultTuningConfig
  , interpret
  , quantum
  , tuningConfigHandler
  ) where

import Prelude

import Prim as P
import Run (Run)
import Run as Run
import Type.Proxy (Proxy(..))
import Type.Row (type (+))

type TuningConfig =
  { quantum :: P.Int
  }

defaultTuningConfig :: TuningConfig
defaultTuningConfig = { quantum: 10_000 }

data Tuning a
  -- | How many steps a guest takes between two looks at the loop — a cancel, a
  -- | channel lost.
  = Quantum (P.Int -> a)

derive instance Functor Tuning

type TUNING r = (tuning :: Tuning | r)

_tuning :: Proxy "tuning"
_tuning = Proxy

interpret :: forall r a. (Tuning ~> Run r) -> Run (TUNING + r) a -> Run r a
interpret handler = Run.interpret (Run.on _tuning handler Run.send)

tuningConfigHandler :: forall r. TuningConfig -> Tuning ~> Run r
tuningConfigHandler conf = case _ of
  Quantum reply -> pure (reply conf.quantum)

quantum :: forall r. Run (TUNING + r) P.Int
quantum = Run.lift _tuning (Quantum identity)

