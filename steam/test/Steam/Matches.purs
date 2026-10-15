-- | A module written in source whose values match with `case`, compiled and
-- | loaded, and each value read as the machine holds it once the module is
-- | initialized: the front end's decision trees and join points, run.
-- |
-- | `rank` dispatches on a data type with an or-pattern; `second` on a nested
-- | constructor with a default; `classify` on two values, a literal among
-- | them, its second alternative taken by two leaves and so a join point
-- | binding `n`; `named` on an open domain of strings; and `flip` on a
-- | `Boolean` its alternatives exhaust. `guarded` binds a name in a guard block
-- | and falls through to the alternative after it where its guard fails, and
-- | `sizeOf` ends its block with `otherwise`; `layered` falls through two
-- | guard blocks in turn. `first` and `unwrap` match a parameter written as a
-- | pattern, `secondOf` a pattern a `let` binds, `split` one a guard block
-- | binds, and `rankOf` is a `case _ of`. `area` dispatches on the tags of a
-- | closed variant, `'Dot` carrying `()`, and `bump` hands on the variant its
-- | default holds whole, widened back by the tag it took; `temperature` writes no
-- | type, and its `case` closes the row of the variant it matches.
module Test.Steam.Matches (spec) where

import Prelude

import Prim as P

import Data.Map as Map
import Data.Tuple (Tuple(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Test.Steam.Compiled (running)

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
  , "isZero :: Int -> Boolean"
  , "isZero n = case n of"
  , "  0 -> true"
  , "  _ -> false"
  , "guarded :: Opt Int -> Int"
  , "guarded o = case o of"
  , "  Some x where"
  , "      z = isZero x"
  , "      z -> 100"
  , "  Some x -> x"
  , "  None -> 7"
  , "isOne :: Int -> Boolean"
  , "isOne n = case n of"
  , "  1 -> true"
  , "  _ -> false"
  , "layered :: Opt Int -> Int"
  , "layered o = case o of"
  , "  Some x where"
  , "      isZero x -> 0"
  , "  Some x where"
  , "      isOne x -> 1"
  , "  _ -> 2"
  , "sizeOf :: Int -> Int"
  , "sizeOf n = case n of"
  , "  m where"
  , "      isZero m -> 0"
  , "      otherwise -> 1"
  , "data Pair a b = Pair a b"
  , "newtype Wrap = Wrap Int"
  , "first :: Pair Int Int -> Int"
  , "first (Pair a _) = a"
  , "unwrap :: Wrap -> Int"
  , "unwrap (Wrap n) = n"
  , "secondOf :: Pair Int Int -> Int"
  , "secondOf p = let Pair _ b = p in b"
  , "split :: Pair Int Int -> Int"
  , "split p = case p of"
  , "  q where"
  , "      Pair a b = q"
  , "      isZero a -> b"
  , "      otherwise -> a"
  , "rankOf :: Color -> Int"
  , "rankOf = case _ of"
  , "  Red -> 10"
  , "  _ -> 20"
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
  , "guardZero = guarded (Some 0)"
  , "guardFive = guarded (Some 5)"
  , "guardNone = guarded None"
  , "sizeZero = sizeOf 0"
  , "sizeTwo = sizeOf 2"
  , "layeredZero = layered (Some 0)"
  , "layeredOne = layered (Some 1)"
  , "layeredFive = layered (Some 5)"
  , "layeredNone = layered None"
  , "firstOf = first (Pair 5 6)"
  , "unwrapped = unwrap (Wrap 7)"
  , "secondOfPair = secondOf (Pair 1 8)"
  , "splitZero = split (Pair 0 9)"
  , "splitOne = split (Pair 1 9)"
  , "rankOfRed = rankOf Red"
  , "rankOfBlue = rankOf Blue"
  , "lambda = (\\(Pair a b) -> b) (Pair 3 4)"
  , "area :: [ 'Circle :: Int, 'Square :: Int, 'Dot :: Unit ] -> Int"
  , "area s = case s of"
  , "  'Circle r -> r"
  , "  'Square n -> n"
  , "  'Dot -> 0"
  , "bump :: [ 'Up :: Int, ...r ] -> [ 'Up :: Int, ...r ]"
  , "bump v = case v of"
  , "  'Up _ -> 'Up 0"
  , "  other -> other"
  , "circle = area ('Circle 3)"
  , "dot = area 'Dot"
  , "bumped :: [ 'Up :: Int, 'Down :: Int ]"
  , "bumped = bump ('Up 5)"
  , "kept :: [ 'Up :: Int, 'Down :: Int ]"
  , "kept = bump ('Down 7)"
  , "temperature v = case v of"
  , "  'Hot -> 1"
  , "  'Cold -> 2"
  , "cold = temperature 'Cold"
  ]

spec :: Spec Unit
spec = describe "Steam, a `case` compiled from source" do
  it "tries a guard block's guards in order, falling through to the alternatives after it where every one fails" do
    running source [ "guardZero", "guardFive", "guardNone", "sizeZero", "sizeTwo" ] \values ->
      values `shouldEqual` Map.fromFoldable
        [ Tuple "guardZero" "100"
        , Tuple "guardFive" "5"
        , Tuple "guardNone" "7"
        , Tuple "sizeZero" "0"
        , Tuple "sizeTwo" "1"
        ]

  it "falls through two guard blocks in turn to the alternative after both" do
    running source [ "layeredZero", "layeredOne", "layeredFive", "layeredNone" ] \values ->
      values `shouldEqual` Map.fromFoldable
        [ Tuple "layeredZero" "0"
        , Tuple "layeredOne" "1"
        , Tuple "layeredFive" "2"
        , Tuple "layeredNone" "2"
        ]

  it "matches a pattern a parameter, a `let`, or a guard block's binding is written as, and a `case _ of` applied" do
    running source [ "firstOf", "unwrapped", "secondOfPair", "splitZero", "splitOne", "rankOfRed", "rankOfBlue", "lambda" ] \values ->
      values `shouldEqual` Map.fromFoldable
        [ Tuple "firstOf" "5"
        , Tuple "unwrapped" "7"
        , Tuple "secondOfPair" "8"
        , Tuple "splitZero" "9"
        , Tuple "splitOne" "1"
        , Tuple "rankOfRed" "10"
        , Tuple "rankOfBlue" "20"
        , Tuple "lambda" "4"
        ]

  it "takes the alternative its value matches, through an or-pattern, a nested constructor, a join point, and a literal" do
    running source [ "rankRed", "rankBlue", "secondOfTwo", "secondOfOne", "redZero", "redFour", "blueFour", "greenNone", "two", "other", "flipped" ] \values ->
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

  it "injects a tag's payload, dispatches on the tag, and hands on the variant a default holds whole" do
    running source [ "circle", "dot", "bumped", "kept" ] \values ->
      values `shouldEqual` Map.fromFoldable
        [ Tuple "circle" "3"
        , Tuple "dot" "0"
        , Tuple "bumped" "'Up(0)"
        , Tuple "kept" "'Down(7)"
        ]

  it "dispatches on a variant whose row the match itself closes" do
    running source [ "cold" ] \values ->
      values `shouldEqual` Map.fromFoldable [ Tuple "cold" "2" ]
