-- | A seed build on the host `build-seeds` shares with `stellac compile`,
-- | against an environment that holds modules besides the seed modules: files
-- | on disk, the session a process, and the result run on the machine.
-- |
-- | Each case builds in its own directory under `devtools/.test-build`. An
-- | ordinary build first writes `Pass`, a macro importing `Base.Int` and
-- | `Stella.Syntax`, and `Main`, which calls it. Their interfaces join the
-- | environment of the seed build, which compiles `Base.Int`, `Pass`, and
-- | `Main` anew. The session refuses a second module of a name it holds, so a
-- | build that sent it the rebuilt `Base.Int` would fail.
module Test.Stella.Devtools.SeedBuild (spec, onDisk) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldM, for_)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Set as Set
import Data.String (Pattern(..), Replacement(..), contains, joinWith, replaceAll, split, stripPrefix, stripSuffix)
import Data.Traversable (for)
import Data.Tuple (Tuple(..))
import Dodo as Dodo
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Fmt (fmt)
import Node.Encoding (Encoding(..))
import Node.FS.Sync as Sync
import Run (AFF, EFFECT, Run, runBaseAff', runBaseEffect)
import Run as Run
import Run.Except (EXCEPT, throw)
import Run.Except as Except
import Steam.CLI.Elaboration as Elaboration
import Steam.Foreign (emptyTable)
import Steam.Load (emptyStore, globalNamed, load, noIdentities)
import Steam.Value (Value(..))
import Stella.CLI.Build (Built, onDisk) as Host
import Stella.CLI.Effect.FS (FS)
import Stella.CLI.Effect.FS as FS
import Stella.CLI.Effect.Log (LOG, Log(..))
import Stella.CLI.Effect.Log as Log
import Stella.CLI.Effect.Process (PROCESS, Process(..))
import Stella.CLI.Effect.Process as Process
import Stella.CLI.Runner.Node as Node
import Stella.Compiler.Build (build, buildSeeds)
import Stella.Compiler.Bytecode (decode)
import Stella.Compiler.Interface.Environment (addInterface, initialEnvironment)
import Stella.Compiler.Interface.File as Interface
import Stella.Compiler.Macro.Compiled (compiled)
import Stella.Compiler.Macro.Run (defaultSettings)
import Stella.Compiler.TypedCore (Ident(..), ModuleName(..), Qualified(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)
import Type.Row (type (+))

-- | `Base.Int` as its source of truth stands.
baseIntPath :: String
baseIntPath = "stella-packages/base/src/Base/Int.stel"

-- | `Pass`: a macro handing back what its brackets hold, its module importing
-- | the module given beside `Stella.Syntax`.
passImporting :: String -> Array String
passImporting imported =
  [ "module Pass where"
  , "import " <> imported
  , "import Stella.Syntax (List, Parser, Syntax(..), Term, TokenTree, brackets, many, map, nodesOf, tree)"
  , "asSyntax :: List TokenTree -> Syntax Term"
  , "asSyntax ts = Syntax (nodesOf ts)"
  , "@[macro]"
  , "pass :: Parser (Syntax Term)"
  , "pass = brackets (map asSyntax (many tree))"
  ]

mainModule :: Array String
mainModule = [ "module Main where", "import Pass", "import Base.Int (add)", "n :: Int", "n = pass%[add 1 2]" ]

type Ran = { result :: Either String Host.Built, said :: Array String, dir :: String }

-- | `Pass`, importing `Base.Int`, and `Main` built by an ordinary build in the
-- | directory given, under `before`; then the files given built there by a
-- | seed build, under `after`, against the seed modules and the interfaces the
-- | first build wrote, each file compiling anew the module its path from `src`
-- | names.
rebuilding :: String -> Array (Tuple String (Array String)) -> (Ran -> Aff Unit) -> Aff Unit
rebuilding name files k = do
  let dir = "devtools/.test-build/" <> name
  said <- liftEffect (Ref.new [])
  result <- onDisk said do
    seed <- either' compiled
    seedEnv <- either' (foldM (flip addInterface) initialEnvironment seed.moduleInterfaces)
    written [ Tuple "before/src/Pass.stel" (passImporting "Base.Int"), Tuple "before/src/Main.stel" mainModule ]
    let
      host env sub =
        { seed
        , environment: env
        , objects: Map.empty
        , written: \(ModuleName m) extension -> fmt @"{dir}/{sub}/{m}.{extension}" { dir, sub, m, extension }
        , steamCmd: "steam"
        , traced: []
        , emitCore: false
        , destination: dir <> "/" <> sub
        }
    _ <- FS.makeDirectory (dir <> "/before/out")
    _ <- Host.onDisk (host seedEnv "before/out") \action env ->
      build action defaultSettings env (map (\m -> { path: fmt @"{dir}/before/src/{m}.stel" { dir, m }, name: ModuleName m }) [ "Pass", "Main" ])
    before <- for [ "Pass", "Main" ] \m -> do
      bytes <- FS.readBytes (fmt @"{dir}/before/out/{m}.dmi" { dir, m }) >>= either'
      either' (Interface.decode bytes)
    env <- either' (foldM (flip addInterface) seedEnv (map _.interface before))
    written (map (\(Tuple p text) -> Tuple ("after/" <> p) text) files)
    _ <- FS.makeDirectory (dir <> "/after/out")
    Host.onDisk (host env "after/out") \action env' ->
      buildSeeds action defaultSettings env' (map (\(Tuple p _) -> { path: fmt @"{dir}/after/{p}" { dir, p }, name: nameOf p }) files)
  lines <- liftEffect (Ref.read said)
  k { result, said: lines, dir }
  where
  written fs = for_ fs \(Tuple path lines) -> do
    let full = "devtools/.test-build/" <> name <> "/" <> path
    _ <- FS.makeDirectory (directoryOf full)
    FS.writeText full (joinWith "\n" lines)
  directoryOf path = joinWith "/" (Array.dropEnd 1 (split (Pattern "/") path))
  nameOf p = ModuleName (replaceAll (Pattern "/") (Replacement ".") (dropping "src/" stripPrefix (dropping ".stel" stripSuffix p)))
  dropping s strip p = fromMaybe p (strip (Pattern s) p)

either' :: forall e a r. Show e => Either e a -> Run (EXCEPT String + r) a
either' = case _ of
  Left err -> throw (show err)
  Right a -> pure a

-- | Run on the disk and on real processes, `steam` started as the development
-- | entry point, the log collected.
onDisk :: forall a. Ref (Array String) -> Run (FS + LOG + PROCESS + EXCEPT String + EFFECT + AFF + ()) a -> Aff (Either String a)
onDisk said p = p
  # FS.interpret Node.nodeFsHandler
  # Log.interpret (\(Log _ doc next) -> next <$ Run.liftEffect (Ref.modify_ (\l -> Array.snoc l (Dodo.print Dodo.plainText Dodo.twoSpaces doc)) said))
  # Process.interpret development
  # Except.runExcept
  # runBaseAff'

-- | `steam` as `node steam/index.dev.js`.
development :: forall r. Process ~> Run (EFFECT + r)
development (SpawnSession launch reply) = Node.nodeProcessHandler
  (SpawnSession (if launch.command == "steam" then launch { command = "node", args = [ "steam/index.dev.js" ] <> launch.args } else launch) reply)

-- | `Main.n`, rendered once `Stella.Elab`, the `Base.Int` the seed build
-- | wrote, the seed `Stella.Syntax`, `Pass`, and `Main` are loaded.
valueOfN :: String -> Aff String
valueOfN dir = do
  said <- liftEffect (Ref.new [])
  read <- onDisk said (for [ "Base.Int", "Pass", "Main" ] \m -> FS.readBytes (dir <> "/after/out/" <> m <> ".dmo"))
  case Elaboration.prepare, compiled, read of
    Left why, _, _ -> pure ("no Stella.Elab: " <> why)
    _, Left why, _ -> pure ("no seed modules: " <> why)
    _, _, Left why -> pure why
    Right elab, Right seed, Right files -> case for files (\f -> f >>= \bytes -> decoded (decode bytes)) of
      Left why -> pure why
      Right dmos -> liftEffect do
        identities <- Ref.new noIdentities
        let ordered = [ elab.dmo ] <> Array.take 1 dmos <> Array.drop 1 seed.modules <> Array.drop 1 dmos
        stored <- runBaseEffect (Except.runExcept (Array.foldM load (emptyStore emptyTable identities) ordered))
        case stored of
          Left err -> pure ("load: " <> show err)
          Right store -> case globalNamed store (Qualified (ModuleName "Main") (Ident "n")) of
            Nothing -> pure "absent"
            Just slot -> Ref.read slot <#> case _ of
              Just (VInt v) -> show v
              Just _ -> "not an Int"
              Nothing -> "uninitialized"
  where
  decoded = case _ of
    Left err -> Left (show err)
    Right dmo -> Right dmo

said' :: Ran -> String -> Boolean
said' r text = Array.any (contains (Pattern text)) r.said

spec :: Spec Unit
spec = describe "a seed build on the host" do
  it "runs a macro on the seed modules the session holds where a module compiled anew has the interface the session holds, never sending the session what it wrote" do
    baseInt <- liftEffect (Sync.readTextFile UTF8 baseIntPath)
    rebuilding "matches" [ Tuple "src/Base/Int.stel" (split (Pattern "\n") baseInt), Tuple "src/Pass.stel" (passImporting "Base.Int"), Tuple "src/Main.stel" mainModule ] \r -> do
      case r.result of
        Left why -> fail (why <> "\n" <> joinWith "\n" r.said)
        Right built -> do
          map (\m -> m.name) built.modules `shouldEqual` map ModuleName [ "Base.Int", "Pass", "Main" ]
          built.loaded `shouldEqual` Set.singleton (ModuleName "Pass")
      n <- valueOfN r.dir
      n `shouldEqual` "3"

  it "fails where a macro reaches a module compiled anew whose interface differs from the one the session runs" do
    rebuilding "differs" [ Tuple "src/Stella/Elab.stel" [ "module Stella.Elab where", "n :: Int", "n = 1" ], Tuple "src/Pass.stel" (passImporting "Stella.Elab"), Tuple "src/Main.stel" mainModule ] \r -> do
      r.result `shouldEqual` Left "The build failed"
      said' r "devtools/.test-build/differs/after/src/Stella/Elab.stel: `Stella.Elab` is compiled anew with an interface that differs from the one of the seed module the macros and synthesizers of the build run on" `shouldEqual` true
