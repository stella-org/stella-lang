-- | The lexical grammar, one rule at a time.
module Test.Stella.Compiler.CST.Lexer (spec) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Effect.Aff (Aff)
import Stella.Compiler.CST.Lexer (LexError(..), LexErrorReason(..), lex)
import Stella.Compiler.CST.Layout (insertLayout)
import Stella.Compiler.CST.Types (SourceRange, SourceToken, StringStyle(..), Token(..), Trivia(..), hasLeadingTrivia, inSource, isSeparated)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

tokens :: String -> Either LexErrorReason (Array Token)
tokens src = case lex src of
  Left (LexError _ reason) -> Left reason
  Right lexed -> Right (map _.value lexed.tokens)

lexesTo :: String -> Array Token -> Aff Unit
lexesTo src expected = tokens src `shouldEqual` Right expected

failsWith :: String -> LexErrorReason -> Aff Unit
failsWith src reason = tokens src `shouldEqual` Left reason

lower :: String -> Token
lower = TokLowerName Nothing

upper :: String -> Token
upper = TokUpperName Nothing

op :: String -> Token
op = TokOperator Nothing

range :: Int -> Int -> Int -> Int -> SourceRange
range l1 c1 l2 c2 = inSource { line: l1, column: c1 } { line: l2, column: c2 }

-- | Whether each token stands apart from the one before it.
separations :: Array SourceToken -> Array Boolean
separations ts = Array.mapWithIndex (\i t -> isSeparated (if i == 0 then Nothing else Array.index ts (i - 1)) t) ts

isLayout :: Token -> Boolean
isLayout = case _ of
  TokLayoutStart _ -> true
  TokLayoutSep _ -> true
  TokLayoutEnd _ -> true
  _ -> false

int :: String -> Int -> Token
int = TokInt

spec :: Spec Unit
spec = describe "Stella.Compiler.CST.Lexer" do
  describe "space and comments" do
    it "skips line and nested block comments" do
      "a -- note\n{- {- inner -} outer -} b" `lexesTo` [ lower "a", lower "b" ]
    it "reads dashes followed by an operator character as an operator" do
      "a --> b" `lexesTo` [ lower "a", op "-->", lower "b" ]
    it "refuses a tab" do
      "a\tb" `failsWith` TabCharacter
    it "refuses an unclosed block comment" do
      "{- a" `failsWith` UnterminatedComment
    it "records whether a token stands apart from the one before it, the first one standing apart" do
      case lex "f (x)g" of
        Right lexed -> map hasLeadingTrivia lexed.tokens `shouldEqual` [ false, true, false, false, false ]
        Left e -> fail (show e)
      case lex "f (x)g" of
        Right lexed -> separations lexed.tokens `shouldEqual` [ true, true, false, false, false ]
        Left e -> fail (show e)
    it "keeps the whitespace and comments before a token as written, each line break as it is spelt" do
      case lex "a -- note\r\n{- {- inner -} outer -}\r  b" of
        Right lexed -> map _.leading (Array.index lexed.tokens 1) `shouldEqual` Just
          [ Spaces " " (range 1 2 1 3)
          , LineComment "-- note" (range 1 3 1 10)
          , Newline "\r\n" (range 1 10 2 1)
          , BlockComment "{- {- inner -} outer -}" (range 2 1 2 24)
          , Newline "\r" (range 2 24 3 1)
          , Spaces "  " (range 3 1 3 3)
          ]
        Left e -> fail (show e)
    it "keeps what follows the last token apart, with where the text ends" do
      case lex "a -- end\n" of
        Right lexed -> do
          lexed.trailing `shouldEqual` [ Spaces " " (range 1 2 1 3), LineComment "-- end" (range 1 3 1 9), Newline "\n" (range 1 9 2 1) ]
          lexed.end `shouldEqual` { line: 2, column: 1 }
        Left e -> fail (show e)
    it "gives the tokens layout inserts no trivia" do
      case lex "f = x\n  where\n  x = 1" of
        Right lexed -> Array.filter (\t -> isLayout t.value && not (Array.null t.leading)) (insertLayout lexed.tokens) `shouldEqual` []
        Left e -> fail (show e)
    it "counts lines and columns from 1" do
      case lex "a\n  bc" of
        Right lexed -> map _.range lexed.tokens `shouldEqual`
          [ (inSource { line: 1, column: 1 } { line: 1, column: 2 })
          , (inSource { line: 2, column: 3 } { line: 2, column: 5 })
          ]
        Left e -> fail (show e)

  describe "names" do
    it "reads names with primes, keywords among them" do
      "x' isn't_it _x where" `lexesTo` [ lower "x'", lower "isn't_it", lower "_x", lower "where" ]
    it "reads a lone underscore apart" do
      "_ _a" `lexesTo` [ TokUnderscore, lower "_a" ]
    it "reads qualified names" do
      "Data.Array.length Data.Maybe.Just Html5.div" `lexesTo`
        [ TokLowerName (Just "Data.Array") "length"
        , TokUpperName (Just "Data.Maybe") "Just"
        , TokLowerName (Just "Html5") "div"
        ]
    it "reads a discriminator" do
      "Just? M.Nothing?" `lexesTo` [ TokDiscriminator Nothing "Just", TokDiscriminator (Just "M") "Nothing" ]
    it "refuses `?` ending a lower case name" do
      "empty? x" `failsWith` QuestionMarkInName
    it "reads a name followed by a hole" do
      "x?y" `lexesTo` [ lower "x", TokHole "y" ]
    it "reads holes" do
      "?todo ?_ ?Foo" `lexesTo` [ TokHole "todo", TokHole "_", TokHole "Foo" ]
    it "reads a field access" do
      "r.name" `lexesTo` [ lower "r", op ".", lower "name" ]

  describe "quotations and antiquotations" do
    it "opens a quotation at `%` apart from what stands before it, a category and `{` following" do
      "%term{ x }" `lexesTo` [ TokQuote "term", lower "x", TokRightBrace ]
      "f %term{x}" `lexesTo` [ lower "f", TokQuote "term", lower "x", TokRightBrace ]
      "(%term{x})" `lexesTo` [ TokLeftParen, TokQuote "term", lower "x", TokRightBrace, TokRightParen ]
      -- after a name, `%` stands with it: a macro call where an opener follows
      "m%{x}" `lexesTo` [ TokMacro Nothing "m", TokLeftBrace, lower "x", TokRightBrace ]
      "f%term{x}" `failsWith` LoneReserved "%"
      "% term{x}" `failsWith` LoneReserved "%"
    it "begins an antiquotation at `$` apart from what stands before it, a name or `(` following" do
      "f $x" `lexesTo` [ lower "f", TokAntiquote, lower "x" ]
      "f $(g x)" `lexesTo` [ lower "f", TokAntiquote, TokLeftParen, lower "g", lower "x", TokRightParen ]
      "%term{$x}" `lexesTo` [ TokQuote "term", TokAntiquote, lower "x", TokRightBrace ]
      "($x, $y)" `lexesTo` [ TokLeftParen, TokAntiquote, lower "x", TokComma, TokAntiquote, lower "y", TokRightParen ]
    it "reads `$` as an operator otherwise" do
      "f $ x" `lexesTo` [ lower "f", op "$", lower "x" ]
      "f$x" `lexesTo` [ lower "f", op "$", lower "x" ]
      "f $$x" `lexesTo` [ lower "f", op "$$", lower "x" ]
      "f $X" `lexesTo` [ lower "f", op "$", upper "X" ]

  describe "operators" do
    it "reads a run of operator characters" do
      "a <$> b .? c .. d" `lexesTo` [ lower "a", op "<$>", lower "b", op ".?", lower "c", op "..", lower "d" ]
    it "reads a lone `?` and `-` as operators" do
      "a ? b - c" `lexesTo` [ lower "a", op "?", lower "b", op "-", lower "c" ]
    it "reads an operator as a value" do
      "(++) M.(<>)" `lexesTo` [ TokOperatorValue Nothing "++", TokOperatorValue (Just "M") "<>" ]
    it "reads a spaced operator in parentheses as three tokens" do
      "( ++ )" `lexesTo` [ TokLeftParen, op "++", TokRightParen ]
    it "reads a qualified operator" do
      "a DA.++ b" `lexesTo` [ lower "a", TokOperator (Just "DA") "++", lower "b" ]
    it "reads a local open" do
      "DA.( x )" `lexesTo` [ TokLocalOpen "DA", lower "x", TokRightParen ]
    it "reads `\\` as an operator character, a lone one being the lambda's" do
      "a /\\ b \\/ c" `lexesTo` [ lower "a", op "/\\", lower "b", op "\\/", lower "c" ]
      "\\x -> x" `lexesTo` [ TokBackslash, lower "x", op "->", lower "x" ]
      "(\\_ -> 1)" `lexesTo` [ TokLeftParen, TokBackslash, TokUnderscore, op "->", int "1" 1, TokRightParen ]
      "f $\\x -> x" `lexesTo` [ lower "f", op "$\\", lower "x", op "->", lower "x" ]
    it "refuses a reserved operator as a value" do
      "(=)" `failsWith` ReservedOperatorValue "="
      "(\\)" `failsWith` ReservedOperatorValue "\\"
      "M.\\ x" `failsWith` ReservedOperatorValue "\\"
    it "reads an infix name" do
      "n `rem` 3 `M.mod` 2" `lexesTo` [ lower "n", TokInfixName Nothing "rem", int "3" 3, TokInfixName (Just "M") "mod", int "2" 2 ]
    it "refuses a lone `%` and `#`" do
      "x % y" `failsWith` LoneReserved "%"
      "x # y" `failsWith` LoneReserved "#"
    it "reads `@` with nothing on either side" do
      "get@cache mb@(Just x)" `lexesTo`
        [ lower "get", op "@", lower "cache", lower "mb", op "@", TokLeftParen, upper "Just", lower "x", TokRightParen ]
    it "refuses `@` with space beside it" do
      "f @Int" `failsWith` AtNotAdjacent
    it "reads a cell read" do
      "n! + 1" `lexesTo` [ lower "n", op "!", op "+", int "1" 1 ]
      "n!=m" `lexesTo` [ lower "n", op "!=", lower "m" ]
    it "refuses `!` apart from a name" do
      "n ! x" `failsWith` BangNotAfterName

  describe "brackets" do
    it "reads effect rows, synthesized arguments and attributes" do
      "{| e |} {{ x }} @[test]" `lexesTo`
        [ TokLeftBar, lower "e", TokRightBar, TokLeftSynth, lower "x", TokRightBrace, TokRightBrace, TokLeftAttribute, lower "test", TokRightSquare ]
    it "reads an empty effect row" do
      "{||}" `lexesTo` [ TokLeftBar, TokRightBar ]
    it "reads `@@[` as an operator and a bracket" do
      "x @@[" `lexesTo` [ lower "x", op "@@", TokLeftSquare ]

  describe "numbers" do
    it "reads integers with separators and leading zeros" do
      "1_000_000 007" `lexesTo` [ int "1_000_000" 1000000, int "007" 7 ]
    it "reads numbers" do
      "3.14 6.02e23 1e-3 1_000.000_1" `lexesTo`
        [ TokNumber "3.14" 3.14, TokNumber "6.02e23" 6.02e23, TokNumber "1e-3" 1.0e-3, TokNumber "1_000.000_1" 1000.0001 ]
    it "reads a negative literal after space, an opening bracket or a comma" do
      "f -1 (-2) [3,-4]" `lexesTo`
        [ lower "f"
        , int "-1" (-1)
        , TokLeftParen
        , int "-2" (-2)
        , TokRightParen
        , TokLeftSquare
        , int "3" 3
        , TokComma
        , int "-4" (-4)
        , TokRightSquare
        ]
    it "reads `-` after operator characters as part of the operator" do
      "a==-5" `lexesTo` [ lower "a", op "==-", int "5" 5 ]
    it "reads `-` after a name with no space as subtraction" do
      "x-1 x - 1" `lexesTo` [ lower "x", op "-", int "1" 1, lower "x", op "-", int "1" 1 ]
    it "reads a range" do
      "1..5" `lexesTo` [ int "1" 1, op "..", int "5" 5 ]
    it "reads binary and hexadecimal as 32-bit patterns" do
      "0b1010 0xFF_FF 0xFFFFFFFF 0x80000000" `lexesTo`
        [ int "0b1010" 10, int "0xFF_FF" 65535, int "0xFFFFFFFF" (-1), int "0x80000000" (-2147483648) ]
    it "reads a negative decimal at the edge of Int" do
      "-2147483648" `lexesTo` [ int "-2147483648" (-2147483648) ]
    it "refuses what is out of range" do
      "2147483648" `failsWith` IntOutOfRange
      "0x100000000" `failsWith` IntOutOfRange
      "1e999" `failsWith` NumberOutOfRange
    it "refuses a malformed literal" do
      "1abc" `failsWith` MalformedNumber
      "1_" `failsWith` MalformedNumber
      "0x_FF" `failsWith` MalformedNumber

  describe "strings and characters" do
    it "reads escapes" do
      "\"a\\n\\u0041\\u{1F600}\\/\"" `lexesTo` [ TokString Quoted "\"a\\n\\u0041\\u{1F600}\\/\"" "a\nA😀/" ]
    it "refuses a surrogate escape and one beyond U+10FFFF" do
      "\"\\uD83D\"" `failsWith` SurrogateEscape
      "\"\\u{110000}\"" `failsWith` EscapeOutOfRange
    it "refuses an unpaired surrogate written raw in a literal, and keeps a pair" do
      "\"a\xD800z\"" `failsWith` UnpairedSurrogate
      "\"\"\"a\xDE00\"\"\"" `failsWith` UnpairedSurrogate
      "'\xD83D'" `failsWith` UnpairedSurrogate
      "\"\xD83D\xDE00\"" `lexesTo` [ TokString Quoted "\"\xD83D\xDE00\"" "\xD83D\xDE00" ]
      "'\xD83D\xDE00'" `lexesTo` [ TokChar "'\xD83D\xDE00'" "\xD83D\xDE00" ]
    it "refuses a line break in a quoted string" do
      "\"a\nb\"" `failsWith` UnterminatedString
    it "reads a block string, removing the common indentation" do
      "\"\"\"\n    Hello,\n      World!\n\n    \\\"\"\" end\n  \"\"\"" `lexesTo`
        [ TokString Block "\"\"\"\n    Hello,\n      World!\n\n    \\\"\"\" end\n  \"\"\"" "Hello,\n  World!\n\n\"\"\" end" ]
    it "reads characters" do
      "'a' '\\'' '😀' 'A'" `lexesTo` [ TokChar "'a'" "a", TokChar "'\\''" "'", TokChar "'😀'" "😀", TokChar "'A'" "A" ]
    it "refuses a character literal holding more than one scalar value" do
      "'ab'" `failsWith` CharNotOneScalar

  describe "tags, directives and macros" do
    it "reads tags" do
      "'Ok 'A" `lexesTo` [ TokTag "Ok", TokTag "A" ]
    it "refuses a tag closed by a quote" do
      "'Ok'" `failsWith` QuotedTagName
    it "reads directives, noting an argument list" do
      "#inline #observ(none)" `lexesTo` [ TokDirective "inline" false, TokDirective "observ" true, TokLeftParen, lower "none", TokRightParen ]
    it "reads `#` inside an operator" do
      "a <#> b" `lexesTo` [ lower "a", op "<#>", lower "b" ]
    it "reads a macro call on a bracket or a string" do
      "format%\"hi\" Fmt.class%{ }" `lexesTo`
        [ TokMacro Nothing "format", TokString Quoted "\"hi\"" "hi", TokMacro (Just "Fmt") "class", TokLeftBrace, TokRightBrace ]
    it "reads `%%` as an operator" do
      "x%%(y)" `lexesTo` [ lower "x", op "%%", TokLeftParen, lower "y", TokRightParen ]
