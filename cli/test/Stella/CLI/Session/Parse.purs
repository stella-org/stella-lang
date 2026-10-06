-- | The payloads of a `parse`, and the values it carries between the host's
-- | types and the session's.
module Test.Stella.CLI.Session.Parse (spec) where

import Prelude

import Data.Argonaut.Core (fromNumber, fromObject, fromString, jsonNull, stringify)
import Data.Array as Array
import Data.Either (Either(..), isLeft, isRight)
import Data.Foldable (for_)
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Data.Tuple (Tuple(..))
import Foreign.Object as Object
import Stella.Compiler.Macro.Run (ExecutionReason(..), ParseOutcome(..))
import Stella.CLI.Session.Parse (ParseAnswer(..), decodeBudgetExceeded, decodeExecutionFailed, decodeParse, decodeParseFailed, decodeParsed, encodeBudgetExceeded, encodeExecutionFailed, encodeParse, encodeParseFailed, encodeParsed)
import Stella.CLI.Session.Syntax (inputOf, positionShape, readAnswer, treesShape)
import Stella.CLI.Session.Value (WireValue(..), decodeValue, encodeValue)
import Stella.CLI.Session.Value.Shape (conformsTo)
import Stella.Compiler.Macro.Bundle (bundle, syntaxModuleName)
import Stella.Compiler.Macro.Tree (Delimiter(..), IssuedOrigin(..), OriginRef(..), Position(..), Range(..), Syntax(..), SyntaxNode(..), Token(..), TokenKind(..), TokenTree(..), Trivia(..))
import Stella.Compiler.TypedCore.Domain (scalarString)
import Stella.Compiler.TypedCore.Name (Ident(..), Qualified(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

ctor :: String -> Array WireValue -> WireValue
ctor = WData <<< Qualified syntaxModuleName <<< Ident

text :: String -> WireValue
text s = case scalarString s of
  Just t -> WString t
  Nothing -> WInt 0

list :: Array WireValue -> WireValue
list = Array.foldr (\x rest -> ctor "Cons" [ x, rest ]) (ctor "Nil" [])

position :: Int -> Int -> WireValue
position l c = ctor "Position" [ WInt l, WInt c ]

-- | Syntax of one comma, whose origin is the value given.
commaWith :: WireValue -> WireValue
commaWith origin = ctor "Syntax" [ list [ ctor "SyntaxToken" [ ctor "Token" [ ctor "Comma" [], text ",", ctor "Range" [ position 1 1, position 1 2 ], ctor "Nil" [], origin ] ] ] ]

-- | `[ a ]`, as the lexer reads it from `m%[ a ]`.
bracketed :: Array TokenTree
bracketed =
  [ Group Bracket (tok GroupBracket "[" 3 [] 0)
      [ Leaf (tok (LowerName Nothing "a") "a" 5 [ Spaces " " (Range (Position 1 4) (Position 1 5)) ] 1) ]
      [ tok GroupBracket "]" 7 [ Spaces " " (Range (Position 1 6) (Position 1 7)) ] 2 ]
  ]
  where
  tok kind t column trivia origin = Token kind t (Range (Position 1 column) (Position 1 (column + 1))) trivia (InputOrigin (IssuedOrigin origin))

spec :: Spec Unit
spec = describe "Stella.CLI.Session.Parse" do
  describe "payloads" do
    let
      request = { parser: { module: "Parsers", name: "names" }, input: { trees: fromString "t", end: fromString "e" }, budget: 9 }
      shown r = { parser: r.parser, trees: stringify r.input.trees, end: stringify r.input.end, budget: r.budget }

    it "round-trip what they write" do
      map shown (decodeParse (encodeParse request)) `shouldEqual` Just (shown request)
      map stringify (decodeParsed (encodeParsed jsonNull)) `shouldEqual` Just "null"
      map stringify (decodeParseFailed (encodeParseFailed jsonNull)) `shouldEqual` Just "null"
      decodeBudgetExceeded encodeBudgetExceeded `shouldEqual` Just unit
      for_ [ NoSuchModule, NoSuchGlobal, NotAParser, ParserNotCallable, InputInvalid, EffectRequested, ForeignRequested, StateRequested, OperationWithheld, Fault, ResultInvalid ] \reason ->
        decodeExecutionFailed (encodeExecutionFailed { reason, detail: "d" }) `shouldEqual` Just { reason, detail: "d" }

    it "refuse a missing field, one they do not know, and a budget below one" do
      map shown (decodeParse (Object.delete "budget" (encodeParse request))) `shouldEqual` Nothing
      map shown (decodeParse (Object.insert "more" jsonNull (encodeParse request))) `shouldEqual` Nothing
      map shown (decodeParse (Object.insert "input" (fromObject (Object.singleton "trees" jsonNull)) (encodeParse request))) `shouldEqual` Nothing
      for_ [ fromNumber 0.0, fromNumber 1.5, fromString "1" ] \b ->
        map shown (decodeParse (Object.insert "budget" b (encodeParse request))) `shouldEqual` Nothing
      decodeBudgetExceeded (Object.singleton "more" jsonNull) `shouldEqual` Nothing
      decodeExecutionFailed (Object.fromFoldable [ Tuple "reason" (fromString "elsewhere"), Tuple "detail" (fromString "") ]) `shouldEqual` Nothing

  describe "values" do
    it "carry a token tree as one of List TokenTree, and where it ends as a Position" do
      case bundle, inputOf bracketed (Position 1 8) of
        Left err, _ -> fail err
        _, Left err -> fail err
        Right b, Right input -> do
          isRight (decodeValue input.trees >>= conformsTo b.descriptor treesShape) `shouldEqual` true
          isRight (decodeValue input.end >>= conformsTo b.descriptor positionShape) `shouldEqual` true

    it "read what a parser expected as a set, and an origin by the constructor it is, one of the input by the form of its token" do
      case bundle of
        Left err -> fail err
        Right b -> do
          let
            failure = ctor "Failure" [ position 1 3, list [ text "`,`" ], list [] ]
            twice = ctor "Failure" [ position 1 3, ctor "Cons" [ text "`,`", ctor "Cons" [ text "`,`", ctor "Nil" [] ] ], list [] ]
            answered w = case encodeValue w of
              Right json -> json
              Left _ -> jsonNull
            expectedOf = case _ of
              Right (FailedAs f) -> Just (Set.toUnfoldable f.expected :: Array String)
              _ -> Nothing
            forged = ctor "Syntax"
              [ ctor "Cons"
                  [ ctor "SyntaxToken"
                      [ ctor "Token"
                          [ ctor "Comma" [], text ",", ctor "Range" [ position 1 1, position 1 2 ], ctor "Nil" [], WToken (Object.singleton "made" jsonNull) ]
                      ]
                  , ctor "Nil" []
                  ]
              ]
            issued = ctor "Syntax"
              [ ctor "Cons"
                  [ ctor "SyntaxToken"
                      [ ctor "Token"
                          [ ctor "Comma" [], text ",", ctor "Range" [ position 1 1, position 1 2 ], ctor "Nil" [], ctor "InputOrigin" [ WToken (Object.singleton "origin" (fromNumber 4.0)) ] ]
                      ]
                  , ctor "Nil" []
                  ]
              ]
          expectedOf (readAnswer b.descriptor (ParseFailed (answered failure))) `shouldEqual` Just [ "`,`" ]
          expectedOf (readAnswer b.descriptor (ParseFailed (answered twice))) `shouldEqual` Just [ "`,`" ]
          isLeft (readAnswer b.descriptor (ParseFailed (answered (WInt 1)))) `shouldEqual` true
          isLeft (readAnswer b.descriptor (Parsed (answered forged))) `shouldEqual` true
          case readAnswer b.descriptor (Parsed (answered issued)) of
            Right (ParsedAs (Syntax [ SyntaxToken (Token Comma "," _ [] origin) ])) -> origin `shouldEqual` InputOrigin (IssuedOrigin 4)
            _ -> fail "not read as the one token"
          -- an origin of a quotation is read as its module and range, which the
          -- expansion checks
          case readAnswer b.descriptor (Parsed (answered (commaWith (ctor "$QuotedOrigin" [ text "Lists", position 3 7, position 3 8 ])))) of
            Right (ParsedAs (Syntax [ SyntaxToken (Token Comma "," _ [] origin) ])) -> origin `shouldEqual` QuotedOrigin "Lists" (Position 3 7) (Position 3 8)
            _ -> fail "not read as the one quoted token"