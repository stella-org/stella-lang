-- | The Stella sources the tests of several packages share, in
-- | `fixtures/source`.
module Test.Steam.Sources (continuationSource) where

import Effect (Effect)

foreign import readSource :: String -> Effect String

-- | `Base.Continuation` as the Modules reference writes it, its constructor
-- | elaboration-only.
continuationSource :: Effect String
continuationSource = readSource "Base/Continuation.stel"
