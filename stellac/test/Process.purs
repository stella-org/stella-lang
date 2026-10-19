-- | The commands the integration tests run as processes, from the root of the
-- | repository: `stellac build`, `steam run` as its command line stands, and the
-- | script building the `Base` package. All run the development entry points,
-- | which need the packages built.
module Test.Stellac.Process
  ( Outcome
  , stellac
  , steamRun
  , buildBase
  , writeFiles
  , removeTree
  , copyArtifacts
  ) where

import Prelude

import Data.Maybe (maybe)
import Data.String (Pattern(..))
import Data.String as String
import Data.Traversable (for_)
import Effect.Aff (Aff)
import Fmt (fmt)
import Node.ChildProcess.Types (Exit(..))
import Node.Encoding (Encoding(..))
import Node.FS.Aff as FS
import Node.FS.Perms as Perms
import Node.Library.Execa (execa)

-- | What one invocation left: its exit status and its two streams.
type Outcome = { status :: Int, out :: String, err :: String }

run :: String -> Array String -> Aff Outcome
run script args = do
  result <- execa "node" ([ script ] <> args) identity >>= _.getResult
  pure
    { status: case result.exit of
        Normally code -> code
        BySignal _ -> -1
    , out: result.stdout
    , err: result.stderr
    }

-- | `stellac build` with the arguments given.
stellac :: Array String -> Aff Outcome
stellac args = run "stellac/index.dev.js" ([ "build" ] <> args)

-- | `steam run`, given the foreign manifest, the module whose `main` is the
-- | entry point, and the bytecode of every module of the program in
-- | dependency order.
steamRun :: { manifest :: String, entry :: String, modules :: Array String } -> Aff Outcome
steamRun p = run "steam/index.dev.js" ([ "run", "--manifest", p.manifest, "--entry", p.entry ] <> p.modules)

-- | `npm run build:base`, the development script building the `Base` package
-- | and writing its dependency map, with the arguments given.
buildBase :: Array String -> Aff Outcome
buildBase = run "scripts/build-base.mjs"

-- | Each file written under the directory given, with the directories above it.
writeFiles :: String -> Array { path :: String, text :: String } -> Aff Unit
writeFiles dir files = for_ files \f -> do
  let path = fmt @"{dir}/{path}" { dir, path: f.path }
  FS.mkdir' (parentOf path) { recursive: true, mode: Perms.mkPerms Perms.all Perms.all Perms.all }
  FS.writeTextFile UTF8 path f.text
  where
  parentOf path = maybe path (\i -> String.take i path) (String.lastIndexOf (Pattern "/") path)

-- | The directory removed with everything under it, where it exists.
removeTree :: String -> Aff Unit
removeTree path = FS.rm' path { force: true, maxRetries: 0, recursive: true, retryDelay: 0 }

-- | The `.dmo` and `.dmi` of each module given copied from the build directory
-- | given to the directory given, which is made where it is not there.
copyArtifacts :: { from :: String, to :: String, modules :: Array String } -> Aff Unit
copyArtifacts p = do
  FS.mkdir' p.to { recursive: true, mode: Perms.mkPerms Perms.all Perms.all Perms.all }
  for_ p.modules \m -> for_ [ "dmo", "dmi" ] \ext ->
    FS.copyFile (fmt @"{from}/{m}.{ext}" { from: p.from, m, ext }) (fmt @"{to}/{m}.{ext}" { to: p.to, m, ext })
