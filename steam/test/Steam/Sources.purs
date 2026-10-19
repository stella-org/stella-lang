-- | The Stella sources the tests read from the repository, the modules of the
-- | `Base` package.
module Test.Steam.Sources (continuationSource) where

import Effect (Effect)

-- | A file of the repository, by its path from the root.
foreign import readRepositoryFile :: String -> Effect String

-- | `Base.Continuation` as the Modules reference writes it, its constructor
-- | elaboration-only.
continuationSource :: Effect String
continuationSource = readRepositoryFile "stella-packages/base/src/Base/Continuation.stel"
