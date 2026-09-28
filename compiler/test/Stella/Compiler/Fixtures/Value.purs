-- | What an observed value is expected to be, written independently of any
-- | backend, and its JSON form in a fixture's manifest.
-- |
-- | | Value | JSON |
-- | | --- | --- |
-- | | an `Int` | `{"int": 6}` |
-- | | a `Number` | `{"number": "-0"}`, the text JavaScript's `Number` reads back to the value, so a negative zero, a NaN, and an infinity are writable |
-- | | a `Char` | `{"char": 98}`, its scalar value |
-- | | a `String` | `{"string": "b"}` |
-- | | a `Boolean` | `{"boolean": true}` |
-- | | a constructor | `{"data": "Main.Cons", "fields": [ … ]}` |
-- | | a record | `{"record": [ {"key": …, "value": …}, … ]}` |
-- | | a variant | `{"variant": …, "payload": …}`, the first a key |
-- | | a function | `{"function": true}`: a closure, a partial application, or a continuation |
-- |
-- | A key is `{"field": "x"}`, `{"tag": "Ok"}`, `{"position": 0}`, or
-- | `{"effect": "Mod.Eff"}`, one per kind, since a field and a tag of one spelling
-- | are two keys (D16).
module Test.Stella.Compiler.Fixtures.Value
  ( Expected(..)
  , ExpectedKey(..)
  , toJson
  , keyJson
  , jsonString
  ) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.String as String
import Data.String.CodePoints as CodePoints
import Data.Enum (fromEnum)
import Data.Int (hexadecimal, toStringAs)

data Expected
  = EInt P.Int
  | ENumber P.Number
  | EChar P.Int
  | EString P.String
  | EBoolean P.Boolean
  | EData P.String (P.Array Expected)
  | ERecord (P.Array { key :: ExpectedKey, value :: Expected })
  | EVariant ExpectedKey Expected
  | EFunction

data ExpectedKey
  = KField P.String
  | KTag P.String
  | KPosition P.Int
  | KEffect P.String

toJson :: Expected -> P.String
toJson = case _ of
  EInt n -> "{\"int\": " <> show n <> "}"
  ENumber x -> "{\"number\": " <> jsonString (numberText x) <> "}"
  EChar c -> "{\"char\": " <> show c <> "}"
  EString s -> "{\"string\": " <> jsonString s <> "}"
  EBoolean b -> "{\"boolean\": " <> (if b then "true" else "false") <> "}"
  EData c fields -> "{\"data\": " <> jsonString c <> ", \"fields\": [" <> String.joinWith ", " (map toJson fields) <> "]}"
  ERecord fields ->
    "{\"record\": [" <> String.joinWith ", " (map (\f -> "{\"key\": " <> keyJson f.key <> ", \"value\": " <> toJson f.value <> "}") fields) <> "]}"
  EVariant k v -> "{\"variant\": " <> keyJson k <> ", \"payload\": " <> toJson v <> "}"
  EFunction -> "{\"function\": true}"

keyJson :: ExpectedKey -> P.String
keyJson = case _ of
  KField s -> "{\"field\": " <> jsonString s <> "}"
  KTag s -> "{\"tag\": " <> jsonString s <> "}"
  KPosition n -> "{\"position\": " <> show n <> "}"
  KEffect s -> "{\"effect\": " <> jsonString s <> "}"

-- | The text `Number` reads back to the value, the sign of a zero included.
numberText :: P.Number -> P.String
numberText x
  | x /= x = "NaN"
  | x == 1.0 / 0.0 = "Infinity"
  | x == -1.0 / 0.0 = "-Infinity"
  | x == 0.0 && 1.0 / x < 0.0 = "-0"
  | otherwise = show x

-- | A JSON string literal holding exactly the text given.
jsonString :: P.String -> P.String
jsonString text = "\"" <> String.joinWith "" (map escape (CodePoints.toCodePointArray text)) <> "\""
  where
  escape cp
    | n == 0x22 = "\\\""
    | n == 0x5C = "\\\\"
    | n < 0x20 = "\\u" <> pad (toStringAs hexadecimal n)
    | otherwise = CodePoints.singleton cp
    where
    n = fromEnum cp

  pad s = String.joinWith "" (Array.replicate (4 - String.length s) "0") <> s
