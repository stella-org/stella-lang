-- | The Stella sources the tests of several packages share, in
-- | `fixtures/source`, and the sources of the modules the compiler carries.
module Test.Stella.Compiler.Sources (continuationSource, readRepositoryFile, baseIntPath, syntaxPath) where

import Effect (Effect)

foreign import readSource :: String -> Effect String

-- | A file of the repository, by its path from the root.
foreign import readRepositoryFile :: String -> Effect String

-- | `Base.Continuation` as the Modules reference writes it, its constructor
-- | elaboration-only.
continuationSource :: Effect String
continuationSource = readSource "Base/Continuation.stel"

-- | The source of `Base.Int`.
baseIntPath :: String
baseIntPath = "stella-packages/base/src/Base/Int.stel"

-- | The source of `Stella.Syntax`.
syntaxPath :: String
syntaxPath = "stella-packages/compiler-lib/src/Stella/Syntax.stel"
