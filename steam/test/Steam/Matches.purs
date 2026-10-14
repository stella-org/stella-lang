-- | A module written in source whose values match with `case`, compiled and
-- | loaded, and each value read as the machine holds it once the module is
-- | initialized: the front end's decision trees and join points, run.
-- |
-- | `rank` dispatches on a data type with an or-pattern; `second` on a nested
-- | constructor with a default; `classify` on two values, a literal among
-- | them, its second alternative taken by two leaves and so a join point
-- | binding `n`; `named` on an open domain of strings; and `flip` on a
-- | `Boolean` its alternatives exhaust.
module Test.Steam.Matches (spec) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Either (Either(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Data.String (joinWith)
import Data.Tuple (Tuple(..))
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Ref as Ref
import Fmt (fmt)
import Run (runBaseEffect)
import Run.Except as Except
import Steam.Foreign (emptyTable)
import Steam.Load (emptyStore, globalNamed, load, noIdentities)
import Steam.Value (CtorId, Value(..))
import Stella.Compiler.Build (CompilerAction, compileModule, defaultHooks, printCompileError)
import Stella.Compiler.Interface.Environment (initialEnvironment)
import Stella.Compiler.Macro.Run (ParseOutcome(..), defaultSettings)
import Stella.Compiler.Macro.Tree (Position(..))
import Stella.Compiler.TypedCore (Ident(..), ModuleName(..), Qualified(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

source :: P.Array P.String
source =
  [ "module Main where"
  , "data Color = Red | Green | Blue"
  , "data Opt a = None | Some a"
  , "data List a = Nil | Cons a (List a)"
  , "rank :: Color -> Int"
  , "rank c = case c of"
  , "  Red -> 1"
  , "  Green | Blue -> 2"
  , "second :: List Int -> Opt Int"
  , "second xs = case xs of"
  , "  Cons _ (Cons y _) -> Some y"
  , "  _ -> None"
  , "classify :: Color -> Opt Int -> Int"
  , "classify c o = case c, o of"
  , "  Red, Some 0 -> 0"
  , "  _, Some n -> n"
  , "  _, None -> 9"
  , "named :: String -> Int"
  , "named s = case s of"
  , "  \"one\" -> 1"
  , "  \"two\" -> 2"
  , "  _ -> 0"
  , "flip :: Boolean -> Boolean"
  , "flip b = case b of"
  , "  true -> false"
  , "  false -> true"
  , "rankRed = rank Red"
  , "rankBlue = rank Blue"
  , "secondOfTwo = second (Cons 1 (Cons 2 Nil))"
  , "secondOfOne = second (Cons 1 Nil)"
  , "redZero = classify Red (Some 0)"
  , "redFour = classify Red (Some 4)"
  , "blueFour = classify Blue (Some 4)"
  , "greenNone = classify Green None"
  , "two = named \"two\""
  , "other = named \"three\""
  , "flipped = flip true"
  ]

-- | `Main` compiled, loaded, and each of its globals named rendered.
running :: P.Array P.String -> (Map.Map P.String P.String -> Aff Unit) -> Aff Unit
running globals k = do
  compiled <- compileModule action defaultSettings initialEnvironment Map.empty (joinWith "\n" source)
  case compiled of
    Left errors -> fail (joinWith "; " (map printCompileError (Array.fromFoldable errors)))
    Right made -> k =<< liftEffect do
      identities <- Ref.new noIdentities
      stored <- runBaseEffect (Except.runExcept (load (emptyStore emptyTable identities) made.dmo))
      case stored of
        Left err -> pure (Map.singleton "load" (show err))
        Right store -> do
          known <- Ref.read identities
          held <- Array.foldM
            ( \acc name -> case globalNamed store (Qualified (ModuleName "Main") (Ident name)) of
                Nothing -> pure (Array.snoc acc (Tuple name "absent"))
                Just slot -> Ref.read slot <#> \value -> Array.snoc acc (Tuple name (maybe "uninitialized" (render known.ctorNames) value))
            )
            []
            globals
          pure (Map.fromFoldable held)
  where
  -- no macro is called, so no parser is run
  action :: CompilerAction Aff
  action =
    { readSource: \_ -> pure (Left "no file")
    , runParser: \_ _ _ -> pure (FailedAs { position: Position 0 0, expected: Set.empty, labels: [] })
    , hooks: defaultHooks
    }
  maybe d f = case _ of
    Nothing -> d
    Just x -> f x

-- | A value as `Some(2)`, a constructor named by the store.
render :: Map.Map CtorId (Qualified Ident) -> Value -> P.String
render names = go
  where
  go = case _ of
    VInt n -> show n
    VBoolean b -> show b
    VData id fields ->
      let
        name = case Map.lookup id names of
          Just (Qualified _ (Ident c)) -> c
          Nothing -> "?"
      in
        if Array.null fields then name else fmt @"{name}({fields})" { name, fields: joinWith ", " (map go fields) }
    _ -> "…"

spec :: Spec Unit
spec = describe "Steam, a `case` compiled from source" do
  it "takes the alternative its value matches, through an or-pattern, a nested constructor, a join point, and a literal" do
    running [ "rankRed", "rankBlue", "secondOfTwo", "secondOfOne", "redZero", "redFour", "blueFour", "greenNone", "two", "other", "flipped" ] \values ->
      values `shouldEqual` Map.fromFoldable
        [ Tuple "rankRed" "1"
        , Tuple "rankBlue" "2"
        , Tuple "secondOfTwo" "Some(2)"
        , Tuple "secondOfOne" "None"
        , Tuple "redZero" "0"
        , Tuple "redFour" "4"
        , Tuple "blueFour" "4"
        , Tuple "greenNone" "9"
        , Tuple "two" "2"
        , Tuple "other" "0"
        , Tuple "flipped" "false"
        ]
