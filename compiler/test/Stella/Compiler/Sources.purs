-- | The Stella sources the tests read from the repository: the modules of the
-- | `Base` package and the modules the compiler carries.
module Test.Stella.Compiler.Sources (continuationSource, readRepositoryFile, baseIntPath, syntaxPath, elabPath) where

import Effect (Effect)

-- | A file of the repository, by its path from the root.
foreign import readRepositoryFile :: String -> Effect String

-- | `Base.Continuation` as the Modules reference writes it, its constructor
-- | elaboration-only.
continuationSource :: Effect String
continuationSource = readRepositoryFile "stella-packages/base/src/Base/Continuation.stel"

-- | The source of `Base.Int`.
baseIntPath :: String
baseIntPath = "stella-packages/base/src/Base/Int.stel"

-- | The source of `Stella.Syntax`.
syntaxPath :: String
syntaxPath = "stella-packages/compiler-lib/src/Stella/Syntax.stel"

-- | The source of `Stella.Elab`.
elabPath :: String
elabPath = "stella-packages/compiler-lib/src/Stella/Elab.stel"
