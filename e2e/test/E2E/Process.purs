-- | The commands the integration tests run as processes, from the root of the
-- | repository: `stellac compile` and `stellac graph`, `steam run` as its command
-- | line stands, `stella-devtools`, and the script building the `Base` package.
-- | All run from the workspace's build output, which needs the packages built.
module Test.E2E.Process
  ( Outcome
  , compile
  , graph
  , steamRun
  , devtools
  , buildBase
  , writeFiles
  , removeTree
  , copyTree
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
import Node.FS.Stats as Stats
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

-- | `stellac compile` given the `stella.json` at the path given.
compile :: String -> Aff Outcome
compile file = run "stellac/index.dev.js" [ "compile", file ]

-- | `stellac graph` given the `stella.json` at the path given.
graph :: String -> Aff Outcome
graph file = run "stellac/index.dev.js" [ "graph", file ]

-- | `steam run` given the program descriptor at the path given.
steamRun :: String -> Aff Outcome
steamRun program = run "steam/index.dev.js" [ "run", program ]

-- | `stella-devtools` with the arguments given.
devtools :: Array String -> Aff Outcome
devtools = run "devtools/index.js"

-- | `npm run build:base`, the development script building the `Base` package
-- | and writing `dependencies.json`, with the arguments given.
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

-- | The directory given, with everything under it, copied into the directory
-- | given, which is made where it is not there; what that holds already stays.
copyTree :: String -> String -> Aff Unit
copyTree from to = do
  FS.mkdir' to { recursive: true, mode: Perms.mkPerms Perms.all Perms.all Perms.all }
  names <- FS.readdir from
  for_ names \name -> do
    let
      source = fmt @"{from}/{name}" { from, name }
      target = fmt @"{to}/{name}" { to, name }
    stat <- FS.stat source
    if Stats.isDirectory stat then copyTree source target else FS.copyFile source target
