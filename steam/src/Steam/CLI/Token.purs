-- | Host tokens as the interpreter holds them.
-- |
-- | A token is a JSON object a session's host handed over and the interpreter never
-- | reads. It is held as an opaque value under a brand of its own, so a guest can
-- | carry it, pass it, and return it, and only a value that is one reads back as
-- | one.
module Steam.CLI.Token
  ( wrap
  , unwrap
  ) where

import Data.Maybe (Maybe(..))
import Steam.Value (Opaque)
import Stella.CLI.Session.Guest (Token)

-- | The token as an opaque value.
foreign import wrap :: Token -> Opaque

foreign import unwrapImpl :: Maybe Token -> (Token -> Maybe Token) -> Opaque -> Maybe Token

-- | The token an opaque value holds, where it is one.
unwrap :: Opaque -> Maybe Token
unwrap = unwrapImpl Nothing Just
