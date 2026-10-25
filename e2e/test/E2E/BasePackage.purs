-- | The `Base` package built from `stella-packages/base` by the development
-- | script, and a program built against the entries the script writes and run
-- | by `steam run`, as processes.
-- |
-- | `dependencies.json` has an entry for every module of the package, the seed
-- | module `Base.Int` among them: `stella-devtools build-seeds` wrote it, the
-- | build of the other modules got it through `dependencies`, and the compiler
-- | accepts it as the seed module it holds. `App` lists the entries as they
-- | stand. It composes actions with `Base.IO` over `Base.String` and
-- | `Base.Int`, calls `Console`, whose foreign the host implements, and handles
-- | an effect by a `reifiable full` clause, resuming with
-- | `Base.Continuation.continue`. `Lifted` runs a computation by
-- | `Base.IO.Effect.runIO`, written by hand under an annotation whose boundary
-- | an implicit handler of its own meets, lowering a greeting to a `LiftIO`
-- | carrying a `Console` action. `Entry` marks a computation `@[entrypoint]`,
-- | and is run from the global its interface names as its entry point, the
-- | stub that applies the runner, `Lifted`'s handler lowering what it
-- | performs. `dependencies` listing a seed module with another interface,
-- | `Prim`, or a module twice is refused. The cases run in order: the first
-- | builds `Base`.
module Test.E2E.BasePackage (spec) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.String (Pattern(..), contains, split)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Fmt (fmt)
import Node.Buffer as Buffer
import Node.Encoding (Encoding(..))
import Node.FS.Aff as FS
import Stella.Compiler.Bytecode.Bytes (Bytes)
import Stella.Compiler.Interface.File as Interface
import Stella.Compiler.TypedCore (Ident(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)
import Node.Process (cwd)
import Test.E2E.Process (Outcome, buildBase, compile, copyTree, removeTree, steamRun, steamRunGlobal, writeFiles)
import Test.E2E.StellaJson (Entry, entriesIn, listedAt, settings, stellaJson)

-- | Where this suite's files stand, written afresh for each run.
dir :: String
dir = "e2e/.test-integration/base-package"

-- | Where the script writes what the build of `Base` writes, and its map.
baseOutput :: String
baseOutput = dir <> "/base"

-- | `App` built by a `stella.json` written as the file given in `app`, against
-- | the modules given.
buildApp :: String -> Array Entry -> Aff Outcome
buildApp file dependencies = do
  writeFiles dir [ { path: "app/" <> file, text: stellaJson ((settings (map listedAt [ "src/Console.stel", "src/Main.stel", "src/Lifted.stel", "src/Entry.stel" ])) { dependencies = dependencies }) } ]
  compile (dir <> "/app/" <> file)

-- | The entries of `dependencies.json`, which the script wrote.
listed :: Aff (Array Entry)
listed = do
  text <- FS.readTextFile UTF8 (baseOutput <> "/dependencies.json")
  case entriesIn text of
    Left why -> fail why *> pure []
    Right entries -> pure entries

-- | The entry of the module given, of those given.
entryOf :: String -> Array Entry -> Array Entry
entryOf m = Array.filter (\e -> e.module == m)

bytesOf :: String -> Aff Bytes
bytesOf path = FS.readFile path >>= liftEffect <<< Buffer.toArray

writeBytes :: String -> Bytes -> Aff Unit
writeBytes path bytes = liftEffect (Buffer.fromArray bytes) >>= FS.writeFile path

-- | The lines a run printed, the development entry point's banner left out.
printed :: Outcome -> Array String
printed o = Array.filter (\l -> l /= "" && not (isBanner l)) (split (Pattern "\n") o.out)
  where
  isBanner = contains (Pattern "!!! This is development version of steam !!!")

-- | Whether a build failed, saying the line given.
refused :: String -> Outcome -> Aff Unit
refused line o = do
  o.status `shouldEqual` 1
  when (not (contains (Pattern line) o.err)) (fail ("the build did not say: " <> line <> "\n" <> o.err))

spec :: Spec Unit
spec = describe "the `Base` package, built from its sources and listed by `dependencies`" do
  it "builds `Base`, `Base.Int` by `stella-devtools`, and writes the entries of every module of it, each path absolute" do
    removeTree dir
    built <- buildBase [ "--output", baseOutput ]
    when (built.status /= 0) (fail ("`Base` did not build: " <> built.err))
    entries <- listed
    root <- liftEffect cwd
    map _.object entries `shouldEqual` map (\m -> fmt @"{root}/{out}/{m}.dmo" { root, out: baseOutput, m })
      [ "Base.Array", "Base.Char", "Base.Continuation", "Base.IO", "Base.IO.Effect", "seeds/Base.Int", "Base.Number", "Base.String" ]

  it "builds a program listing those entries as they stand, `Base.Int` accepted as the seed module" do
    copyTree "fixtures/source/base-package" dir
    entries <- listed
    built <- buildApp "stella.json" entries
    when (built.status /= 0) (fail ("the program did not build: " <> built.err))

  it "runs the program over the bytecode the entries name" do
    entries <- listed
    outcome <- steamRun
      { manifest: dir <> "/app/foreign.json"
      , entry: "Main"
      , modules: map _.object entries <> [ dir <> "/app/output/Console.dmo", dir <> "/app/output/Main.dmo" ]
      }
    outcome.err `shouldEqual` ""
    outcome.status `shouldEqual` 0
    printed outcome `shouldEqual` [ "built apart", "12", "6" ]

  it "runs a computation by the standard runner, an implicit handler lowering what it performs to `LiftIO`" do
    entries <- listed
    outcome <- steamRun
      { manifest: dir <> "/app/foreign.json"
      , entry: "Lifted"
      , modules: map _.object entries <> [ dir <> "/app/output/Console.dmo", dir <> "/app/output/Lifted.dmo" ]
      }
    outcome.err `shouldEqual` ""
    outcome.status `shouldEqual` 0
    printed outcome `shouldEqual` [ "hello, runner", "hello, LiftIO" ]

  it "runs a computation the attribute marks from the global its interface names, the stub that runs it" do
    stored <- bytesOf (dir <> "/app/output/Entry.dmi")
    case Interface.decode stored of
      Left err -> fail (show err)
      Right file -> case file.interface.entrypoint of
        Nothing -> fail "no entry point"
        Just (Ident global) -> do
          entries <- listed
          outcome <- steamRunGlobal
            { manifest: dir <> "/app/foreign.json"
            , entry: "Entry"
            , global
            , modules: map _.object entries <> map (\m -> dir <> "/app/output/" <> m <> ".dmo") [ "Console", "Lifted", "Entry" ]
            }
          outcome.err `shouldEqual` ""
          outcome.status `shouldEqual` 0
          printed outcome `shouldEqual` [ "hello, entry point", "hello, stub" ]

  it "refuses `dependencies` listing a seed module with another interface" do
    stored <- bytesOf (baseOutput <> "/seeds/Base.Int.dmi")
    case Interface.decode stored of
      Left err -> fail (show err)
      Right file -> do
        let
          values = Map.delete (Ident "toString") file.interface.declarations.values
          other = file.interface { declarations { values = values } }
        case Interface.encode file { interface = other } of
          Left err -> fail (show err)
          Right bytes -> writeBytes (baseOutput <> "/Other.Int.dmi") bytes
    entries <- listed
    buildApp "other.json" (entryOf "Base.String" entries <> [ { module: "Base.Int", interface: "../base/Other.Int.dmi", object: "../base/seeds/Base.Int.dmo" } ])
      >>= refused "`dependencies` lists `Base.Int` with an interface that differs from the one of the seed module the compiler holds"

  it "refuses `dependencies` listing `Prim`" do
    entries <- listed
    buildApp "prim.json" (entryOf "Base.String" entries <> [ { module: "Prim", interface: "../base/Prim.dmi", object: "../base/Prim.dmo" } ])
      >>= refused "`dependencies[1].module` is `Prim`, which the compiler provides"

  it "refuses `dependencies` listing a module twice, whether or not it is a seed module" do
    entries <- listed
    let twice = entryOf "Base.String" entries <> entryOf "Base.Int" entries
    outcome <- buildApp "twice.json" (twice <> twice)
    refused "`dependencies` lists `Base.Int` more than once" outcome
    refused "`dependencies` lists `Base.String` more than once" outcome
