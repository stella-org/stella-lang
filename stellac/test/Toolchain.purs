-- | `stellac build --toolchain-rebuild` of a package holding a module the
-- | compiler carries, beside a macro of its own: the files on disk, the
-- | session a process, and the modules built then run on the machine.
-- |
-- | Each case builds in a directory of its own under `stellac/.test-build`.
-- | `Pass` writes a macro against `Stella.Syntax`, and imports the module the
-- | package compiles anew; `Main` calls the macro. The session refuses a second
-- | module of a name it holds, so a build that sent it the package's own would
-- | fail.
module Test.Stellac.Toolchain (spec) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.Maybe (Maybe(..))
import Data.String (Pattern(..), contains, joinWith, lastIndexOf, take)
import Data.Traversable (for)
import Data.Tuple (Tuple(..))
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Ref as Ref
import Run (runBaseEffect)
import Run.Except as Except
import Steam.CLI.Elaboration as Elaboration
import Steam.Foreign (emptyTable)
import Steam.Load (emptyStore, globalNamed, load, noIdentities)
import Steam.Value (Value(..))
import Stella.CLI.Effect.FS as FS
import Stella.CLI.Effect.Log (LogLevel(..))
import Stella.Compiler.Bytecode (decode)
import Stella.Compiler.Macro.Compiled (compiled)
import Stella.Compiler.TypedCore (Ident(..), ModuleName(..), Qualified(..))
import Stellac.Options (Command(..))
import Stellac.Program (program)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Test.Stellac.Synthesis (onDisk)

-- | `Base.Int` written in source: the entries the ABI places in it, as
-- | foreigns.
baseInt :: Array String
baseInt =
  [ "module Base.Int where"
  , "foreign add :: Int -> Int -> Int"
  , "foreign sub :: Int -> Int -> Int"
  , "foreign mul :: Int -> Int -> Int"
  , "foreign quot :: Int -> Int -> Int"
  , "foreign rem :: Int -> Int -> Int"
  , "foreign eq :: Int -> Int -> Boolean"
  , "foreign lt :: Int -> Int -> Boolean"
  , "foreign toNumber :: Int -> Number"
  , "foreign toString :: Int -> String"
  ]

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

type Ran = { result :: Either String Unit, said :: Array String, dir :: String }

-- | The files given, built in the directory given with `--toolchain-rebuild`
-- | naming the module given.
building :: String -> String -> Array (Tuple String (Array String)) -> (Ran -> Aff Unit) -> Aff Unit
building name rebuilt files k = do
  let dir = "stellac/.test-build/" <> name
  said <- liftEffect (Ref.new [])
  result <- onDisk said do
    for_ files \(Tuple path lines) -> do
      _ <- FS.makeDirectory (dir <> "/" <> directoryOf path)
      FS.writeText (dir <> "/" <> path) (joinWith "\n" lines)
    program
      { logLevel: Info
      , monochrome: true
      , command: Build
          { output: "output"
          , workdir: dir
          , src: []
          , traceOpt: Nothing
          , emitCore: false
          , steamCmd: "steam"
          , dependencies: Nothing
          , toolchainRebuild: [ ModuleName rebuilt ]
          }
      }
  lines <- liftEffect (Ref.read said)
  k { result, said: lines, dir }
  where
  directoryOf path = case lastIndexOf (Pattern "/") path of
    Just i -> take i path
    Nothing -> "."

-- | `Main.n`, rendered once `Stella.Elab`, the `Base.Int` the build wrote, the
-- | `Stella.Syntax` the compiler carries, `Pass`, and `Main` are loaded.
valueOfN :: String -> Aff String
valueOfN dir = do
  said <- liftEffect (Ref.new [])
  read <- onDisk said (for [ "Base.Int", "Pass", "Main" ] \m -> FS.readBytes (dir <> "/output/_build/" <> m <> ".dmo"))
  case Elaboration.prepare, compiled, read of
    Left why, _, _ -> pure ("no Stella.Elab: " <> why)
    _, Left why, _ -> pure ("no carried modules: " <> why)
    _, _, Left why -> pure why
    Right elab, Right carried, Right files -> case for files (\f -> f >>= \bytes -> either' (decode bytes)) of
      Left why -> pure why
      Right dmos -> liftEffect do
        identities <- Ref.new noIdentities
        let ordered = [ elab.dmo ] <> Array.take 1 dmos <> Array.drop 1 carried.modules <> Array.drop 1 dmos
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
  either' = case _ of
    Left err -> Left (show err)
    Right dmo -> Right dmo

said' :: Ran -> String -> Boolean
said' r text = Array.any (contains (Pattern text)) r.said

spec :: Spec Unit
spec = describe "stellac build --toolchain-rebuild" do
  it "compiles a module the compiler carries anew, the package's macros run on the one the compiler carries, and the program runs on the new one" do
    building "rebuilt" "Base.Int" [ Tuple "src/Base/Int.stel" baseInt, Tuple "src/Pass.stel" (passImporting "Base.Int"), Tuple "src/Main.stel" mainModule ] \r -> do
      r.result `shouldEqual` Right unit
      Array.take 3 r.said `shouldEqual`
        [ "[1/3] Compiling Base.Int (stellac/.test-build/rebuilt/src/Base/Int.stel)"
        , "[2/3] Compiling Pass (stellac/.test-build/rebuilt/src/Pass.stel)"
        , "[3/3] Compiling Main (stellac/.test-build/rebuilt/src/Main.stel)"
        ]
      n <- valueOfN r.dir
      n `shouldEqual` "3"

  it "fails where a macro of the package reaches a module compiled anew whose interface differs from the one the session runs" do
    building "differs" "Stella.Elab" [ Tuple "src/Stella/Elab.stel" [ "module Stella.Elab where", "n :: Int", "n = 1" ], Tuple "src/Pass.stel" (passImporting "Stella.Elab"), Tuple "src/Main.stel" mainModule ] \r -> do
      r.result `shouldEqual` Left "The build failed"
      said' r "stellac/.test-build/differs/src/Stella/Elab.stel: `Stella.Elab` is compiled anew with an interface that differs from the one of the module the compiler carries, which the macros and synthesizers of the build run on" `shouldEqual` true
