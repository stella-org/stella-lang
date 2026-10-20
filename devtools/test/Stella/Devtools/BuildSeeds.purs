-- | `stella-devtools build-seeds` run as a process, from the repository's
-- | root: what it writes against the files the compiler holds the seed modules in.
-- |
-- | It is given a Steam executable that does not exist, so a build that opened
-- | a session would fail.
module Test.Stella.Devtools.BuildSeeds (spec) where

import Prelude

import Data.Array as Array
import Data.Foldable (for_)
import Data.Tuple (Tuple(..))
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Node.Buffer as Buffer
import Node.ChildProcess.Types (Exit(..))
import Node.Encoding (Encoding(..))
import Node.FS.Aff as FS
import Node.Library.Execa (execa)
import Stella.Compiler.Bootstrap.Source as Source
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

-- | Where the command writes, removed before it runs.
dir :: String
dir = "devtools/.test-seeds"

-- | The file the compiler holds the modules it carries in.
carriedSource :: String
carriedSource = "compiler/src/Stella/Compiler/Bootstrap/Source.purs"

-- | The command run with the arguments given: its exit status and what it said
-- | on its error stream.
devtools :: Array String -> Aff { status :: Int, err :: String }
devtools args = do
  result <- execa "node" ([ "devtools/index.js" ] <> args) identity >>= _.getResult
  pure
    { status: case result.exit of
        Normally code -> code
        BySignal _ -> -1
    , err: result.stderr
    }

hexOf :: String -> Aff String
hexOf path = FS.readFile path >>= liftEffect <<< Buffer.toString Hex

spec :: Spec Unit
spec = describe "stella-devtools build-seeds" do
  it "writes each seed module as the files the compiler holds, to the byte, opening no session and changing nothing the compiler holds" do
    FS.rm' dir { force: true, maxRetries: 0, recursive: true, retryDelay: 0 }
    held <- FS.readTextFile UTF8 carriedSource
    outcome <- devtools [ "build-seeds", "--output", dir, "--steam-cmd", "no-such-steam" ]
    outcome `shouldEqual` { status: 0, err: "" }
    written <- FS.readdir dir
    Array.sort written `shouldEqual` [ "Base.Int.dmi", "Base.Int.dmo", "Stella.Elab.dmi", "Stella.Elab.dmo", "Stella.Syntax.dmi", "Stella.Syntax.dmo" ]
    for_ [ Tuple "Base.Int" Source.baseInt, Tuple "Stella.Syntax" Source.stellaSyntax, Tuple "Stella.Elab" Source.stellaElab ] \(Tuple m carried) -> do
      interface <- hexOf (dir <> "/" <> m <> ".dmi")
      bytecode <- hexOf (dir <> "/" <> m <> ".dmo")
      { module: m, interface, bytecode } `shouldEqual` { module: m, interface: carried.interface, bytecode: carried.bytecode }
    after <- FS.readTextFile UTF8 carriedSource
    (after == held) `shouldEqual` true

  it "refuses to run without an output directory" do
    outcome <- devtools [ "build-seeds" ]
    outcome.status `shouldEqual` 1
