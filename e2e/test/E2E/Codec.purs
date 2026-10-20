-- | `stellac build` of a package whose synthesizer derives an encoder from the
-- | type of each goal, over the `Base` package the development script builds:
-- | the files on disk, the session a process, and the modules built then run on
-- | the machine.
-- |
-- | `Codec` writes values, `Derive` derives an encoder of `Codec` against
-- | `Stella.Elab`, and `Main` asks for one at each goal: of closed rows, of a
-- | nested one, whose inner record is a subgoal of its own, and of rows open in
-- | a tail whose fields the site passes, written by hand or derived in turn,
-- | and of a type another goal decides, `Sample` answering it once `derive`
-- | has first been asked and has waited. A
-- | `Main` of `fixtures/source/codec/cases` takes the place of the package's
-- | where a goal is to fail. Each case builds `Base` and the package afresh in
-- | a directory of its own, and reads nothing another case built.
-- |
-- | The modules loaded to read a value are those `Main` needs when it runs, of
-- | the ones the builds wrote: `Codec` and what it reaches, and not `Derive`,
-- | `Sample`, or `Stella.Elab`, which `Main` imports for its synthesizers alone.
module Test.E2E.Codec (spec) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..), isLeft)
import Data.Foldable (for_)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.String (Pattern(..), contains)
import Data.Traversable (for, sequence)
import Data.Tuple (Tuple(..))
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Ref as Ref
import Node.Buffer as Buffer
import Node.Encoding (Encoding(..))
import Node.FS.Aff as FS
import Run (runBaseEffect)
import Run.Except as Except
import Steam.Foreign (emptyTable)
import Steam.Load (emptyStore, globalNamed, load, noIdentities)
import Steam.Value (Value(..))
import Stella.CLI.Effect.Log (LogLevel(..))
import Stella.Compiler.Bytecode (Dmo, decode)
import Stella.Compiler.Macro.Compiled (compiled)
import Stella.Compiler.TypedCore (Ident(..), ModuleName(..), Qualified(..))
import Stella.Compiler.TypedCore.Domain (textOf)
import Stellac.Dependencies (parse)
import Stellac.Options (BuildOptions, Command(..))
import E2E.Build (collectedFrom)
import Stellac.Program (program)
import Test.E2E.Process (buildBase, copyTree, removeTree)
import Test.E2E.Synthesis (onDisk)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

-- | Where this suite's files stand, written afresh for each run.
dir :: String
dir = "e2e/.test-integration/codec"

options :: String -> BuildOptions
options workdir =
  { output: "output"
  , workdir
  , src: []
  , traceOpt: Nothing
  , emitCore: false
  , steamCmd: "steam"
  , dependencies: Just "../base/dependencies.json"
  }

type Ran = { result :: Either String Unit, said :: Array String }

-- | `Base` and then the package built afresh under `dir`, in the directory
-- | named, the package's `Main` the one of the case named where one is: `Base`
-- | under `base`, where the script writes it and its map, and the package under
-- | `app`.
building :: String -> Maybe String -> Aff Ran
building name replacing = do
  let workdir = dir <> "/" <> name <> "/app"
  removeTree (dir <> "/" <> name)
  built <- buildBase [ "--output", dir <> "/" <> name <> "/base" ]
  when (built.status /= 0) (fail ("`Base` did not build: " <> built.err))
  copyTree "fixtures/source/codec/src" (workdir <> "/src")
  for_ replacing \chosen ->
    FS.readTextFile UTF8 ("fixtures/source/codec/cases/" <> chosen <> "/Main.stel") >>= FS.writeTextFile UTF8 (workdir <> "/src/Main.stel")
  log <- liftEffect (Ref.new [])
  result <- onDisk log (program { logLevel: Info, monochrome: true, command: Build (options workdir) })
  lines <- liftEffect (Ref.read log)
  pure { result, said: lines }

-- | Whether a build said something holding the text given.
said :: Ran -> String -> Boolean
said r text = Array.any (contains (Pattern text)) r.said

-- | The modules `Main` needs when it runs, of the package built in the
-- | directory named: of the modules the compiler carries, the rest of `Base` as
-- | the map lists it, and the package's modules, in that order, those `Main`
-- | reaches through the imports of their bytecode.
heldOf :: String -> Aff (Either String (Array Dmo))
heldOf name = do
  let
    baseOutput = dir <> "/" <> name <> "/base"
    app = dir <> "/" <> name <> "/app"
  mapped <- FS.readTextFile UTF8 (baseOutput <> "/dependencies.json")
  case parse "dependencies.json" mapped, compiled of
    Left err, _ -> pure (Left (show err))
    _, Left why -> pure (Left ("no carried modules: " <> why))
    Right entries, Right carried -> do
      let
        carriedNames = map _.name carried.moduleInterfaces
        base = map (\e -> baseOutput <> "/" <> e.object) (Array.filter (\e -> not (Array.elem e.module carriedNames)) entries)
        own = map (\m -> app <> "/output/_build/" <> m <> ".dmo") [ "Codec", "Derive", "Sample", "Main" ]
      read <- for (base <> own) dmoAt
      pure (sequence read >>= \dmos -> collectedFrom [ ModuleName "Main" ] (carried.modules <> dmos))

-- | The string each global of `Main` named is, of the package built in the
-- | directory named, once the modules `Main` needs when it runs are loaded.
stringsOf :: String -> Array String -> Aff (Map String String)
stringsOf name globals = do
  held <- heldOf name
  case held of
    Left why -> fail why *> pure Map.empty
    Right dmos -> liftEffect do
      identities <- Ref.new noIdentities
      stored <- runBaseEffect (Except.runExcept (Array.foldM load (emptyStore emptyTable identities) dmos))
      case stored of
        Left err -> pure (Map.singleton "load" (show err))
        Right store -> Map.fromFoldable <$> for globals \global -> Tuple global <$> case globalNamed store (Qualified (ModuleName "Main") (Ident global)) of
          Nothing -> pure "absent"
          Just slot -> Ref.read slot <#> case _ of
            Just (VString s) -> textOf s
            Just _ -> "not a String"
            Nothing -> "uninitialized"

dmoAt :: String -> Aff (Either String Dmo)
dmoAt path = do
  bytes <- FS.readFile path >>= liftEffect <<< Buffer.toArray
  pure case decode bytes of
    Left err -> Left (path <> ": " <> show err)
    Right dmo -> Right dmo

spec :: Spec Unit
spec = describe "stellac build of an encoder derived from the type of each goal" do
  it "builds `Base`, then the package, `derive` solving every goal of `Main`" do
    r <- building "built" Nothing
    r.result `shouldEqual` Right unit
    said r "[4/4] Compiling Main" `shouldEqual` true

  -- `Main` imports `Derive` and `Sample` for the synthesizers its goals name,
  -- and what they answer with names `Codec` alone
  it "makes a program needing neither the synthesizers nor `Stella.Elab` when it runs" do
    r <- building "held" Nothing
    r.result `shouldEqual` Right unit
    held <- heldOf "held"
    case held of
      Left why -> fail why
      Right dmos -> do
        map _.imports (Array.find (\d -> d.name == ModuleName "Main") dmos) `shouldEqual` Just [ ModuleName "Codec" ]
        Array.filter (\m -> Array.elem m (map _.name dmos)) (map ModuleName [ "Derive", "Sample", "Stella.Elab" ]) `shouldEqual` []

  it "writes a closed row's fields in key order, a nested record's by a subgoal of its own" do
    values <- solved "closed" [ "person", "nested" ]
    values `shouldEqual` Map.fromFoldable
      [ Tuple "person" """{"admin":false,"age":30,"name":"Ann"}"""
      , Tuple "nested" """{"id":1,"owner":{"name":"Bo"}}"""
      ]

  it "writes a row open in a tail by the fields of the tail the site passes, written by hand or derived" do
    values <- solved "open" [ "opened", "derivedTail" ]
    values `shouldEqual` Map.fromFoldable
      [ Tuple "opened" """{"name":"Cy","age":4}"""
      , Tuple "derivedTail" """{"name":"Di","admin":true,"age":5}"""
      ]

  -- the goal of `encode` is queued before the goal of `sample`, so `derive`
  -- first sees the type undecided and waits; `sampled` deciding it wakes it
  it "waits for a type another goal decides, and then writes it" do
    values <- solved "waited" [ "waited" ]
    values `shouldEqual` Map.singleton "waited" """{"name":"Fay"}"""

  describe "fails where the goal stands" do
    it "for a row open in a tail the site passes no fields of" do
      r <- building "untailed" (Just "untailed")
      isLeft r.result `shouldEqual` true
      said r "src/Main.stel:10:10: A synthesizer failed here: nothing the site binds is the `Fields { ...r }` that the open tail needs" `shouldEqual` true

    it "for a type no encoder is derived for" do
      r <- building "unsupported" (Just "unsupported")
      isLeft r.result `shouldEqual` true
      said r "src/Main.stel:10:9: A synthesizer failed here: no encoder is derived for the type `Number`" `shouldEqual` true

-- | The strings of the globals named, of the package built in the directory
-- | named.
solved :: String -> Array String -> Aff (Map String String)
solved name globals = do
  r <- building name Nothing
  case r.result of
    Left why -> fail ("the package did not build: " <> why) *> pure Map.empty
    Right _ -> stringsOf name globals
