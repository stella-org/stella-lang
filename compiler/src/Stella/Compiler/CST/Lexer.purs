-- | Turning source text into tokens.
-- |
-- | The lexer reads the whole text at once and hands back every token or the
-- | first error. Comments and whitespace do not become tokens: they are the
-- | trivia a token keeps before it, as written, and what follows the last token
-- | is kept apart, so that no character of the text is lost.
module Stella.Compiler.CST.Lexer
  ( LexError(..)
  , LexErrorReason(..)
  , Lexed
  , Ahead
  , lex
  , lexWhile
  , printLexErrorReason
  ) where

import Prelude

import Control.Monad.Rec.Class (Step(..), tailRec)
import Data.Array as Array
import Data.Char (toCharCode)
import Data.Either (Either(..))
import Data.Enum (toEnum)
import Data.Int as Int
import Data.List (List(..), (:))
import Data.List as List
import Data.Maybe (Maybe(..), fromMaybe, isJust, isNothing)
import Data.Number as Number
import Data.String (joinWith)
import Data.String as String
import Data.String.CodeUnits as SCU
import Data.String.Regex (split) as Regex
import Data.String.Regex.Flags (global) as Regex
import Data.String.Regex.Unsafe (unsafeRegex) as Regex
import Stella.Compiler.CST.Types (SourcePos, SourceToken, StringStyle(..), Token(..), Trivia(..), inSource)

data LexError = LexError SourcePos LexErrorReason

derive instance Eq LexError

instance Show LexError where
  show (LexError pos reason) =
    "LexError " <> show pos.line <> ":" <> show pos.column <> " " <> printLexErrorReason reason

data LexErrorReason
  = UnexpectedCharacter Char
  | TabCharacter
  | UnterminatedComment
  | UnterminatedString
  | UnterminatedChar
  | InvalidEscape
  | SurrogateEscape
  | UnpairedSurrogate
  | EscapeOutOfRange
  | CharNotOneScalar
  | QuotedTagName
  | MalformedNumber
  | IntOutOfRange
  | NumberOutOfRange
  | QuestionMarkInName
  | ReservedOperatorValue String
  | LoneReserved String
  | AtNotAdjacent
  | BangNotAfterName

derive instance Eq LexErrorReason

instance Show LexErrorReason where
  show reason = "(LexErrorReason " <> show (printLexErrorReason reason) <> ")"

printLexErrorReason :: LexErrorReason -> String
printLexErrorReason = case _ of
  UnexpectedCharacter c -> "unexpected character " <> show c
  TabCharacter -> "a tab character; indentation is written with spaces"
  UnterminatedComment -> "a block comment is not closed"
  UnterminatedString -> "a string literal is not closed on its line"
  UnterminatedChar -> "a character literal is not closed"
  InvalidEscape -> "an unknown escape sequence"
  SurrogateEscape -> "an escape naming a surrogate, which is no Unicode scalar value"
  UnpairedSurrogate -> "an unpaired surrogate, which is no Unicode scalar value"
  EscapeOutOfRange -> "an escape beyond U+10FFFF"
  CharNotOneScalar -> "a character literal holds exactly one scalar value"
  QuotedTagName -> "a variant tag contains no `'`"
  MalformedNumber -> "a malformed numeric literal"
  IntOutOfRange -> "an integer literal outside the range of Int"
  NumberOutOfRange -> "a numeric literal too large for Number"
  QuestionMarkInName -> "`?` ends only a name beginning with an upper case letter"
  ReservedOperatorValue op -> "`" <> op <> "` is reserved and is not an operator"
  LoneReserved op -> "`" <> op <> "` alone is reserved and is not an operator"
  AtNotAdjacent -> "`@` stands with no space on either side"
  BangNotAfterName -> "`!` reads a cell, and follows a name with no space"

type Cursor = { index :: Int, line :: Int, column :: Int }

type State s =
  { cursor :: Cursor
  , previous :: Maybe Token
  , tokens :: List SourceToken
  , going :: s
  }

-- | The tokens of a text, the trivia after the last of them, and where the text
-- | ends.
type Lexed =
  { tokens :: Array SourceToken
  , trailing :: Array Trivia
  , end :: SourcePos
  }

-- | What the lexer sees before it reads a token: the token before it, whether
-- | a line break stands between the two, where the token begins, and whether
-- | the text there begins with the word given.
type Ahead =
  { previous :: Maybe Token
  , onNewLine :: Boolean
  , at :: SourcePos
  , startsWithWord :: String -> Boolean
  }

lex :: String -> Either LexError Lexed
lex = lexWhile unit (\_ _ -> Just unit)

-- | Lex a text up to the first token the function given stops before, read off
-- | what stands ahead and a state it carries from token to token; what follows
-- | that token is not lexed, and the text ends there.
lexWhile :: forall s. s -> (s -> Ahead -> Maybe s) -> String -> Either LexError Lexed
lexWhile seed continue src = tailRec step initial
  where
  len = SCU.length src

  initial :: State s
  initial =
    { cursor: skipBom { index: 0, line: 1, column: 1 }
    , previous: Nothing
    , tokens: Nil
    , going: seed
    }

  skipBom cur = if charAt cur.index == Just '\xFEFF' then cur { index = 1 } else cur

  charAt :: Int -> Maybe Char
  charAt i = SCU.charAt i src

  is :: Int -> Char -> Boolean
  is i c = charAt i == Just c

  test :: Int -> (Char -> Boolean) -> Boolean
  test i p = maybe false p (charAt i)

  maybe :: forall a b. b -> (a -> b) -> Maybe a -> b
  maybe b f = case _ of
    Nothing -> b
    Just a -> f a

  slice :: Int -> Int -> String
  slice from to = SCU.slice from to src

  -- Moves the cursor to `to`, counting the lines and columns passed over.
  move :: Cursor -> Int -> Cursor
  move cur to = tailRec go cur
    where
    go c
      | c.index >= to = Done c
      | otherwise = case charAt c.index of
          Just '\r'
            | is (c.index + 1) '\n' -> Loop { index: c.index + 2, line: c.line + 1, column: 1 }
            | otherwise -> Loop { index: c.index + 1, line: c.line + 1, column: 1 }
          Just '\n' -> Loop { index: c.index + 1, line: c.line + 1, column: 1 }
          _ -> Loop c { index = c.index + 1, column = c.column + 1 }

  pos :: Cursor -> SourcePos
  pos cur = { line: cur.line, column: cur.column }

  step :: State s -> Step (State s) (Either LexError Lexed)
  step st = case skipSpace st.cursor of
    Left e -> Done (Left e)
    Right { cursor, trivia } ->
      let
        ended = Done (Right { tokens: Array.fromFoldable (List.reverse st.tokens), trailing: trivia, end: pos cursor })
      in
        if cursor.index >= len then ended
        else case continue st.going (ahead st cursor) of
          Nothing -> ended
          Just going ->
            let
              -- the first token stands apart, there being nothing before it
              space = isNothing st.previous || not (Array.null trivia)
            in
              case token st.previous space cursor of
                Left e -> Done (Left e)
                Right { value, end } ->
                  let
                    endCursor = move cursor end
                    tok = { range: inSource (pos cursor) (pos endCursor), leading: trivia, value }
                  in
                    Loop { cursor: endCursor, previous: Just value, tokens: tok : st.tokens, going }

  -- a line break stands before the token where the trivia passed over one,
  -- a comment's among them
  ahead st cursor =
    { previous: st.previous
    , onNewLine: cursor.line > st.cursor.line
    , at: pos cursor
    , startsWithWord: \w ->
        let
          after = cursor.index + SCU.length w
        in
          slice cursor.index after == w && not (test after isIdentChar)
    }

  -- Whitespace and comments, each kept as written.
  skipSpace :: Cursor -> Either LexError { cursor :: Cursor, trivia :: Array Trivia }
  skipSpace start = tailRec go { cursor: start, trivia: [] }
    where
    go { cursor, trivia } = case charAt cursor.index of
      Just ' ' -> piece Spaces (cursor.index + runOf cursor.index (_ == ' '))
      Just '\n' -> piece Newline (cursor.index + 1)
      Just '\r' -> piece Newline (cursor.index + if is (cursor.index + 1) '\n' then 2 else 1)
      Just '\t' -> Done (Left (LexError (pos cursor) TabCharacter))
      Just '-' | isLineComment cursor.index -> piece LineComment (lineEnd cursor.index)
      Just '{' | is (cursor.index + 1) '-' -> case blockCommentEnd (cursor.index + 2) 1 of
        Nothing -> Done (Left (LexError (pos cursor) UnterminatedComment))
        Just end -> piece BlockComment end
      _ -> Done (Right { cursor, trivia })
      where
      piece kind end =
        let
          next = move cursor end
        in
          Loop { cursor: next, trivia: Array.snoc trivia (kind (slice cursor.index end) (inSource (pos cursor) (pos next))) }

  -- `--` and any further dashes, not followed by another operator character.
  isLineComment :: Int -> Boolean
  isLineComment i =
    let
      dashes = runOf i (_ == '-')
    in
      dashes >= 2 && not (test (i + dashes) isOpChar)

  lineEnd :: Int -> Int
  lineEnd i = tailRec go i
    where
    go j = case charAt j of
      Nothing -> Done j
      Just '\n' -> Done j
      Just '\r' -> Done j
      _ -> Loop (j + 1)

  blockCommentEnd :: Int -> Int -> Maybe Int
  blockCommentEnd from depth0 = tailRec go { i: from, depth: depth0 }
    where
    go { i, depth } = case charAt i of
      Nothing -> Done Nothing
      Just '-' | is (i + 1) '}' ->
        if depth == 1 then Done (Just (i + 2)) else Loop { i: i + 2, depth: depth - 1 }
      Just '{' | is (i + 1) '-' -> Loop { i: i + 2, depth: depth + 1 }
      _ -> Loop { i: i + 1, depth }

  runOf :: Int -> (Char -> Boolean) -> Int
  runOf i p = tailRec go 0
    where
    go n = if test (i + n) p then Loop (n + 1) else Done n

  ok :: Token -> Int -> Either LexError { value :: Token, end :: Int }
  ok value end = Right { value, end }

  err :: forall a. Cursor -> LexErrorReason -> Either LexError a
  err cur reason = Left (LexError (pos cur) reason)

  errAt :: forall a. Cursor -> Int -> LexErrorReason -> Either LexError a
  errAt cur i reason = err (move cur i) reason

  token :: Maybe Token -> Boolean -> Cursor -> Either LexError { value :: Token, end :: Int }
  token previous space cur = case charAt i of
    Nothing -> err cur (UnexpectedCharacter ' ')
    Just c
      | c == '(' -> openParen cur Nothing i
      | c == ')' -> ok TokRightParen (i + 1)
      | c == '[' -> ok TokLeftSquare (i + 1)
      | c == ']' -> ok TokRightSquare (i + 1)
      | c == ',' -> ok TokComma (i + 1)
      | c == '\\' && runOf i isOpChar == 1 -> ok TokBackslash (i + 1)
      | c == '{' && is (i + 1) '|' -> ok TokLeftBar (i + 2)
      | c == '{' && is (i + 1) '{' -> ok TokLeftSynth (i + 2)
      | c == '{' -> ok TokLeftBrace (i + 1)
      | c == '}' -> ok TokRightBrace (i + 1)
      | c == '`' -> infixName cur
      | c == '"' -> stringLiteral cur
      | c == '\'' -> quote cur
      | c == '?' && test (i + 1) isIdentStart -> hole cur
      -- `%term{` apart from what stands before it opens a quotation, and `$`
      -- apart from it, a name or `(` following, begins an antiquotation
      | c == '%' && apart && test (i + 1) isLower && is quoteOpen '{' -> ok (TokQuote (slice (i + 1) quoteOpen)) (quoteOpen + 1)
      | c == '$' && apart && runOf i isOpChar == 1 && (test (i + 1) isLower || is (i + 1) '(') -> ok TokAntiquote (i + 1)
      | c == '#' && test (i + 1) isLower && not (is (i + 1) '_') -> directive cur
      | c == '-' && test (i + 1) isDigit && apart -> number cur true
      | isDigit c -> number cur false
      | isUpper c -> name cur i Nothing
      | isIdentStart c -> lowerName cur i Nothing
      | isOpChar c -> operator cur previous space Nothing i
      | otherwise -> err cur (UnexpectedCharacter c)
    where
    i = cur.index

    -- apart from the token before: after trivia, at the start, or after what
    -- opens or separates
    apart = space || case previous of
      Nothing -> true
      Just tok -> opensOrSeparates tok

    quoteOpen = i + 1 + runOf (i + 1) isIdentChar

  opensOrSeparates :: Token -> Boolean
  opensOrSeparates = case _ of
    TokLeftParen -> true
    TokLeftSquare -> true
    TokLeftBrace -> true
    TokLeftBar -> true
    TokLeftSynth -> true
    TokLeftAttribute -> true
    TokLocalOpen _ -> true
    TokQuote _ -> true
    TokComma -> true
    TokOperator _ _ -> true
    _ -> false

  -- `(`, or an operator as a value `(++)`, or with a qualifier `M.(++)` or a
  -- local open `M.(`.
  openParen :: Cursor -> Maybe String -> Int -> Either LexError { value :: Token, end :: Int }
  openParen cur qualifier at =
    let
      opLen = runOf (at + 1) isOpChar
      op = slice (at + 1) (at + 1 + opLen)
    in
      if opLen > 0 && is (at + 1 + opLen) ')' && not (isDashes op) then
        if isReservedAlone op then errAt cur (at + 1) (ReservedOperatorValue op)
        else ok (TokOperatorValue qualifier op) (at + 2 + opLen)
      else case qualifier of
        Nothing -> ok TokLeftParen (at + 1)
        Just q -> ok (TokLocalOpen q) (at + 1)

  isDashes :: String -> Boolean
  isDashes op = SCU.length op >= 2 && SCU.toCharArray op == Array.replicate (SCU.length op) '-'

  -- An upper case name, possibly the start of a qualified one.
  name :: Cursor -> Int -> Maybe String -> Either LexError { value :: Token, end :: Int }
  name cur start qualifier =
    let
      end = start + 1 + runOf (start + 1) isIdentChar
      segment = slice start end
      q = Just (qualify qualifier segment)
    in
      if is end '.' then
        if test (end + 1) isUpper then name cur (end + 1) q
        else if test (end + 1) isIdentStart then lowerName cur (end + 1) q
        else if is (end + 1) '(' then openParen cur q (end + 1)
        else if test (end + 1) isOpChar then operator cur Nothing false q (end + 1)
        else upper segment end
      else upper segment end
    where
    upper segment end
      | is end '?' = ok (TokDiscriminator qualifier segment) (end + 1)
      | otherwise = ok (TokUpperName qualifier segment) end

  qualify :: Maybe String -> String -> String
  qualify = case _ of
    Nothing -> identity
    Just q -> \segment -> q <> "." <> segment

  lowerName :: Cursor -> Int -> Maybe String -> Either LexError { value :: Token, end :: Int }
  lowerName cur start qualifier =
    let
      end = start + 1 + runOf (start + 1) isIdentChar
      segment = slice start end
    in
      if segment == "_" && qualifier == Nothing then ok TokUnderscore end
      else if is end '%' && test (end + 1) isMacroOpener && runOf end isOpChar == 1 then
        ok (TokMacro qualifier segment) (end + 1)
      else if is end '?' && runOf end isOpChar == 1 && not (test (end + 1) isIdentStart) then
        errAt cur end QuestionMarkInName
      else ok (TokLowerName qualifier segment) end

  isMacroOpener :: Char -> Boolean
  isMacroOpener c = c == '(' || c == '[' || c == '{' || c == '"'

  infixName :: Cursor -> Either LexError { value :: Token, end :: Int }
  infixName cur = case scanName (cur.index + 1) Nothing of
    Just { qualifier, segment, end } | is end '`' -> ok (TokInfixName qualifier segment) (end + 1)
    _ -> err cur (UnexpectedCharacter '`')

  -- A possibly qualified lower case name, for an infix use.
  scanName :: Int -> Maybe String -> Maybe { qualifier :: Maybe String, segment :: String, end :: Int }
  scanName start qualifier
    | test start isUpper =
        let
          end = start + 1 + runOf (start + 1) isIdentChar
          segment = slice start end
        in
          if is end '.' then scanName (end + 1) (Just (qualify qualifier segment)) else Nothing
    | test start isIdentStart =
        let
          end = start + 1 + runOf (start + 1) isIdentChar
        in
          Just { qualifier, segment: slice start end, end }
    | otherwise = Nothing

  hole :: Cursor -> Either LexError { value :: Token, end :: Int }
  hole cur =
    let
      start = cur.index + 1
      end = start + 1 + runOf (start + 1) isIdentChar
    in
      ok (TokHole (slice start end)) end

  directive :: Cursor -> Either LexError { value :: Token, end :: Int }
  directive cur =
    let
      start = cur.index + 1
      end = start + 1 + runOf (start + 1) isIdentChar
    in
      ok (TokDirective (slice start end) (is end '(')) end

  operator
    :: Cursor
    -> Maybe Token
    -> Boolean
    -> Maybe String
    -> Int
    -> Either LexError { value :: Token, end :: Int }
  operator cur previous space qualifier start =
    let
      end = start + runOf start isOpChar
      op = slice start end
    in
      if qualifier == Nothing && op == "@" && is end '[' then ok TokLeftAttribute (end + 1)
      else if qualifier == Nothing && op == "|" && is end '}' then ok TokRightBar (end + 1)
      else if qualifier /= Nothing && isReservedAlone op then errAt cur start (ReservedOperatorValue op)
      else case op of
        "@" | space || not (test end isAdjacentStart) -> err cur AtNotAdjacent
        "!" | space || not (afterName previous) -> err cur BangNotAfterName
        "%" -> err cur (LoneReserved op)
        "#" -> err cur (LoneReserved op)
        _ -> ok (TokOperator qualifier op) end

  afterName :: Maybe Token -> Boolean
  afterName = case _ of
    Just (TokLowerName _ _) -> true
    _ -> false

  isAdjacentStart :: Char -> Boolean
  isAdjacentStart c = isIdentStart c || isUpper c || c == '(' || c == '{' || c == '[' || c == '\'' || c == '"' || isDigit c

  -- A string literal, quoted or block.
  stringLiteral :: Cursor -> Either LexError { value :: Token, end :: Int }
  stringLiteral cur
    | is (cur.index + 1) '"' && is (cur.index + 2) '"' = blockString cur
    | otherwise = tailRec go { i: cur.index + 1, acc: Nil }
        where
        go { i, acc } = case charAt i of
          Nothing -> Done (err cur UnterminatedString)
          Just '\n' -> Done (err cur UnterminatedString)
          Just '\r' -> Done (err cur UnterminatedString)
          Just '"' ->
            Done (ok (TokString Quoted (slice cur.index (i + 1)) (joinWith "" (Array.fromFoldable (List.reverse acc)))) (i + 1))
          Just '\\' -> case escape cur i false of
            Left e -> Done (Left e)
            Right r -> Loop { i: r.end, acc: r.value : acc }
          Just _ -> case scalarWidth i of
            Just w -> Loop { i: i + w, acc: slice i (i + w) : acc }
            Nothing -> Done (errAt cur i UnpairedSurrogate)

  -- The width in code units of the scalar value starting at `i`. A surrogate
  -- that is not the first half of a pair is no scalar value.
  scalarWidth :: Int -> Maybe Int
  scalarWidth i = case charAt i of
    Just c
      | isHighSurrogate c && test (i + 1) isLowSurrogate -> Just 2
      | isHighSurrogate c || isLowSurrogate c -> Nothing
    _ -> Just 1

  -- An escape sequence starting at the backslash at `i`.
  escape :: Cursor -> Int -> Boolean -> Either LexError { value :: String, end :: Int }
  escape cur i inChar = case charAt (i + 1) of
    Just '"' -> Right { value: "\"", end: i + 2 }
    Just '\\' -> Right { value: "\\", end: i + 2 }
    Just '/' -> Right { value: "/", end: i + 2 }
    Just 'b' -> Right { value: "\x08", end: i + 2 }
    Just 'f' -> Right { value: "\x0C", end: i + 2 }
    Just 'n' -> Right { value: "\n", end: i + 2 }
    Just 'r' -> Right { value: "\r", end: i + 2 }
    Just 't' -> Right { value: "\t", end: i + 2 }
    Just '\'' | inChar -> Right { value: "'", end: i + 2 }
    Just 'u'
      | is (i + 2) '{' ->
          let
            digits = runOf (i + 3) isHexDigit
          in
            if digits > 0 && is (i + 3 + digits) '}' then
              scalar (slice (i + 3) (i + 3 + digits)) (i + 4 + digits)
            else errAt cur i InvalidEscape
      | runOf (i + 2) isHexDigit >= 4 -> scalar (slice (i + 2) (i + 6)) (i + 6)
    _ -> errAt cur i InvalidEscape
    where
    scalar hex end =
      let
        n = hexValue hex
      in
        if n > 1114111.0 then errAt cur i EscapeOutOfRange
        else if n >= 55296.0 && n <= 57343.0 then errAt cur i SurrogateEscape
        else case toEnum (fromMaybe 0 (Int.fromNumber n)) of
          Just cp -> Right { value: String.singleton cp, end }
          Nothing -> errAt cur i EscapeOutOfRange

  -- A block string, whose value is GraphQL's BlockStringValue of its raw text.
  blockString :: Cursor -> Either LexError { value :: Token, end :: Int }
  blockString cur = tailRec go { i: cur.index + 3, acc: Nil }
    where
    go { i, acc } = case charAt i of
      Nothing -> Done (err cur UnterminatedString)
      Just '\\'
        | is (i + 1) '"' && is (i + 2) '"' && is (i + 3) '"' -> Loop { i: i + 4, acc: "\"\"\"" : acc }
      Just '"'
        | is (i + 1) '"' && is (i + 2) '"' ->
            Done
              ( ok
                  (TokString Block (slice cur.index (i + 3)) (blockStringValue (joinWith "" (Array.fromFoldable (List.reverse acc)))))
                  (i + 3)
              )
      Just _ -> case scalarWidth i of
        Just w -> Loop { i: i + w, acc: slice i (i + w) : acc }
        Nothing -> Done (errAt cur i UnpairedSurrogate)

  -- A character literal, or a variant tag.
  quote :: Cursor -> Either LexError { value :: Token, end :: Int }
  quote cur = quoteAt cur cur.index

  quoteAt :: Cursor -> Int -> Either LexError { value :: Token, end :: Int }
  quoteAt cur i
    | test (i + 1) isUpper =
        let
          end = i + 2 + runOf (i + 2) isTagChar
        in
          if is end '\'' then
            if end == i + 2 then ok (TokChar (slice i (end + 1)) (slice (i + 1) end)) (end + 1)
            else errAt cur end QuotedTagName
          else if is end '?' then errAt cur end QuestionMarkInName
          else ok (TokTag (slice (i + 1) end)) end
    | is (i + 1) '\\' = case escape cur (i + 1) true of
        Left e -> Left e
        Right r ->
          if is r.end '\'' then ok (TokChar (slice i (r.end + 1)) r.value) (r.end + 1)
          else err cur UnterminatedChar
    | otherwise = case charAt (i + 1) of
        Nothing -> err cur UnterminatedChar
        Just '\n' -> err cur UnterminatedChar
        Just '\'' -> err cur CharNotOneScalar
        Just _ -> case scalarWidth (i + 1) of
          Nothing -> errAt cur (i + 1) UnpairedSurrogate
          Just width ->
            if is (i + 1 + width) '\'' then
              ok (TokChar (slice i (i + 2 + width)) (slice (i + 1) (i + 1 + width))) (i + 2 + width)
            else if test (i + 1 + width) (_ /= '\n') then err cur CharNotOneScalar
            else err cur UnterminatedChar

  number :: Cursor -> Boolean -> Either LexError { value :: Token, end :: Int }
  number cur negative
    | not negative && is cur.index '0' && is (cur.index + 1) 'x' = radix cur 16.0 isHexDigit
    | not negative && is cur.index '0' && is (cur.index + 1) 'b' = radix cur 2.0 (\c -> c == '0' || c == '1')
    | otherwise =
        let
          start = if negative then cur.index + 1 else cur.index
        in
          case digitRun start isDigit of
            Nothing -> err cur MalformedNumber
            Just intEnd ->
              let
                fraction =
                  if is intEnd '.' && test (intEnd + 1) isDigit then digitRun (intEnd + 1) isDigit
                  else Nothing
                afterFraction = fromMaybe intEnd fraction
                exponentStart = afterFraction + 1 + (if is (afterFraction + 1) '+' || is (afterFraction + 1) '-' then 1 else 0)
                exponent =
                  if (is afterFraction 'e' || is afterFraction 'E') && test exponentStart isDigit then digitRun exponentStart isDigit
                  else Nothing
                end = fromMaybe afterFraction exponent
                raw = slice cur.index end
                clean = String.replaceAll (String.Pattern "_") (String.Replacement "") raw
              in
                if test end isIdentChar then errAt cur end MalformedNumber
                else if isJust fraction || isJust exponent then case Number.fromString clean of
                  Just n | Number.isFinite n -> ok (TokNumber raw n) end
                  _ -> err cur NumberOutOfRange
                else case Int.fromString clean of
                  Just n -> ok (TokInt raw n) end
                  Nothing -> err cur IntOutOfRange

  -- A binary or hexadecimal literal: a 32-bit pattern read as two's complement.
  radix :: Cursor -> Number -> (Char -> Boolean) -> Either LexError { value :: Token, end :: Int }
  radix cur base isRadixDigit = case digitRun (cur.index + 2) isRadixDigit of
    Nothing -> err cur MalformedNumber
    Just end ->
      let
        raw = slice cur.index end
        digits = String.replaceAll (String.Pattern "_") (String.Replacement "") (SCU.drop 2 raw)
        n = Array.foldl (\acc c -> acc * base + digitValue c) 0.0 (SCU.toCharArray digits)
      in
        if test end isIdentChar then errAt cur end MalformedNumber
        else if n > 4294967295.0 then err cur IntOutOfRange
        else case Int.fromNumber (if n >= 2147483648.0 then n - 4294967296.0 else n) of
          Just v -> ok (TokInt raw v) end
          Nothing -> err cur IntOutOfRange

  -- Digits with single `_` between two of them.
  digitRun :: Int -> (Char -> Boolean) -> Maybe Int
  digitRun start isD
    | test start isD = Just (tailRec go (start + 1))
        where
        go j
          | test j isD = Loop (j + 1)
          | is j '_' && test (j + 1) isD = Loop (j + 2)
          | otherwise = Done j
    | otherwise = Nothing

-- The characters of the lexical grammar.

isDigit :: Char -> Boolean
isDigit c = c >= '0' && c <= '9'

isUpper :: Char -> Boolean
isUpper c = c >= 'A' && c <= 'Z'

isLower :: Char -> Boolean
isLower c = c >= 'a' && c <= 'z' || c == '_'

isIdentStart :: Char -> Boolean
isIdentStart c = isLower c || isUpper c

isIdentChar :: Char -> Boolean
isIdentChar c = isLower c || isUpper c || isDigit c || c == '\''

isTagChar :: Char -> Boolean
isTagChar c = isLower c || isUpper c || isDigit c

isHexDigit :: Char -> Boolean
isHexDigit c = isDigit c || c >= 'a' && c <= 'f' || c >= 'A' && c <= 'F'

isOpChar :: Char -> Boolean
isOpChar c = String.contains (String.Pattern (SCU.singleton c)) "!#$%&*+-/:.<=>?@\\^|~"

isHighSurrogate :: Char -> Boolean
isHighSurrogate c = toCharCode c >= 0xD800 && toCharCode c <= 0xDBFF

isLowSurrogate :: Char -> Boolean
isLowSurrogate c = toCharCode c >= 0xDC00 && toCharCode c <= 0xDFFF

-- | The operators that are reserved when written alone.
isReservedAlone :: String -> Boolean
isReservedAlone op = Array.elem op [ "\\", ".", "...", "=", "|", "@", "%", "#", "!", ":", "::", "->", "->*", "=>", "<-", ":=", "~>" ]

digitValue :: Char -> Number
digitValue c
  | isDigit c = Int.toNumber (toCharCode c - toCharCode '0')
  | c >= 'a' && c <= 'f' = Int.toNumber (toCharCode c - toCharCode 'a' + 10)
  | otherwise = Int.toNumber (toCharCode c - toCharCode 'A' + 10)

hexValue :: String -> Number
hexValue = Array.foldl (\acc c -> acc * 16.0 + digitValue c) 0.0 <<< SCU.toCharArray

-- | GraphQL's BlockStringValue: line terminators become `\n`, the indentation
-- | common to every line after the first that is not blank is removed, and
-- | blank lines at the start and the end are dropped.
blockStringValue :: String -> String
blockStringValue raw =
  let
    lines = Regex.split (Regex.unsafeRegex "\\r\\n|\\r|\\n" Regex.global) raw
    indentOf line = SCU.length (SCU.takeWhile (\c -> c == ' ' || c == '\t') line)
    common = Array.foldl min top
      (map indentOf (Array.filter (not <<< isBlank) (Array.drop 1 lines)))
    strip = Array.mapWithIndex (\ix line -> if ix == 0 || common == top then line else SCU.drop common line) lines
    trimmed = Array.reverse (Array.dropWhile isBlank (Array.reverse (Array.dropWhile isBlank strip)))
  in
    joinWith "\n" trimmed
  where
  top = 2147483647
  isBlank line = String.trim line == ""
