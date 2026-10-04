-- | The values a `parse` carries, between the host's types and the session's
-- | generic values ([Parse](Parse.purs)).
-- |
-- | **The host's types mirror those of `Stella.Syntax` constructor for
-- | constructor** ([Tree](../../../../../compiler/src/Stella/Compiler/Macro/Tree.purs)),
-- | so a value crosses as the constructor it is. A list is `Stella.Syntax.List`
-- | and an optional value `Stella.Syntax.Maybe`, and an origin is a token the
-- | session carries unread, `{ "origin": n }`.
-- |
-- | **What comes back is checked before it is read**: it is a canonical value,
-- | and one of the type its place wants by the descriptor of `Stella.Syntax`.
-- | Only then is it taken into the host's types, and what a parser expected is
-- | taken as a set there.
module Stella.CLI.Session.Syntax
  ( inputOf
  , treesShape
  , positionShape
  , resultShape
  , readAnswer
  ) where

import Prelude

import Control.Monad.Rec.Class (Step(..), tailRec)
import Data.Argonaut.Core (Json, caseJsonNumber, fromNumber)
import Data.Array as Array
import Data.Either (Either(..), note)
import Data.Int as Int
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Data.Traversable (traverse)
import Foreign.Object as Object
import Stella.CLI.Session.Parse (ParseAnswer(..))
import Stella.Compiler.Macro.Run (ParseFailure, ParseOutcome(..))
import Stella.CLI.Session.Value (WireValue(..), decodeValue, encodeValue, renderPath)
import Stella.CLI.Session.Value.Shape (conformsTo)
import Stella.Compiler.Elaborate.Protocol.Guest.Shape (Descriptor, Shape(..))
import Stella.Compiler.Macro.Bundle (syntaxModuleName)
import Stella.Compiler.Macro.Tree (Delimiter(..), OriginRef(..), Position(..), Range(..), Syntax(..), SyntaxItem(..), SyntaxNode(..), Term, Token(..), TokenKind(..), TokenTree(..), Trivia(..))
import Stella.Compiler.TypedCore.Domain (scalarString, textOf)
import Stella.Compiler.TypedCore.Name (Ident(..), Qualified(..), TyName(..))

-- The input ------------------------------------------------------------------------------

-- | The trees a parser reads and the position they end at, as JSON. A text
-- | holding an unpaired surrogate has no value; no token the lexer reads does.
inputOf :: Array TokenTree -> Position -> Either String { trees :: Json, end :: Json }
inputOf trees end = do
  t <- traverse treeValue trees
  treesJson <- encode (listValue t)
  endJson <- encode (positionValue end)
  pure { trees: treesJson, end: endJson }
  where
  encode value = case encodeValue value of
    Right json -> Right json
    Left problem -> Left ("the input" <> renderPath problem.path <> ": " <> problem.problem)

treeValue :: TokenTree -> Either String WireValue
treeValue = case _ of
  Leaf t -> ctor "Leaf" <<< pure <$> tokenValue t
  Group d open inner closes -> do
    o <- tokenValue open
    i <- traverse treeValue inner
    c <- traverse tokenValue closes
    d' <- delimiterValue d
    pure (ctor "Group" [ d', o, listValue i, listValue c ])

tokenValue :: Token -> Either String WireValue
tokenValue (Token kind text range trivia origin) = do
  k <- kindValue kind
  t <- textValue text
  tr <- traverse triviaValue trivia
  pure (ctor "Token" [ k, t, rangeValue range, listValue tr, originValue origin ])

kindValue :: TokenKind -> Either String WireValue
kindValue = case _ of
  GroupBracket -> pure (ctor "GroupBracket" [])
  Comma -> pure (ctor "Comma" [])
  Backslash -> pure (ctor "Backslash" [])
  Underscore -> pure (ctor "Underscore" [])
  LowerName q n -> named "LowerName" q n
  UpperName q n -> named "UpperName" q n
  DiscriminatorName q n -> named "DiscriminatorName" q n
  OperatorName q n -> named "OperatorName" q n
  OperatorValue q n -> named "OperatorValue" q n
  InfixName q n -> named "InfixName" q n
  HoleName n -> ctor "HoleName" <<< pure <$> textValue n
  TagName n -> ctor "TagName" <<< pure <$> textValue n
  DirectiveName n -> ctor "DirectiveName" <<< pure <$> textValue n
  MacroName q n -> named "MacroName" q n
  IntLiteral n -> pure (ctor "IntLiteral" [ WInt n ])
  NumberLiteral n -> pure (ctor "NumberLiteral" [ WNumber n ])
  CharLiteral c -> ctor "CharLiteral" <<< pure <$> textValue c
  StringLiteral s -> ctor "StringLiteral" <<< pure <$> textValue s
  where
  named c q n = do
    q' <- case q of
      Nothing -> pure (ctor "Nothing" [])
      Just m -> ctor "Just" <<< pure <$> textValue m
    n' <- textValue n
    pure (ctor c [ q', n' ])

delimiterValue :: Delimiter -> Either String WireValue
delimiterValue = case _ of
  Paren -> pure (ctor "Paren" [])
  Bracket -> pure (ctor "Bracket" [])
  Brace -> pure (ctor "Brace" [])
  EffectRow -> pure (ctor "EffectRow" [])
  Synthesized -> pure (ctor "Synthesized" [])
  AttributeBracket -> pure (ctor "AttributeBracket" [])
  LocalOpen m -> ctor "LocalOpen" <<< pure <$> textValue m

triviaValue :: Trivia -> Either String WireValue
triviaValue = case _ of
  Spaces s r -> piece "Spaces" s r
  Newline s r -> piece "Newline" s r
  LineComment s r -> piece "LineComment" s r
  BlockComment s r -> piece "BlockComment" s r
  where
  piece c s r = textValue s <#> \t -> ctor c [ t, rangeValue r ]

rangeValue :: Range -> WireValue
rangeValue (Range s e) = ctor "Range" [ positionValue s, positionValue e ]

positionValue :: Position -> WireValue
positionValue (Position line column) = ctor "Position" [ WInt line, WInt column ]

originValue :: OriginRef -> WireValue
originValue (OriginRef n) = WToken (Object.singleton "origin" (fromNumber (Int.toNumber n)))

textValue :: String -> Either String WireValue
textValue s = WString <$> note ("a text holding an unpaired surrogate: " <> show s) (scalarString s)

listValue :: Array WireValue -> WireValue
listValue = Array.foldr (\x rest -> ctor "Cons" [ x, rest ]) (ctor "Nil" [])

ctor :: String -> Array WireValue -> WireValue
ctor = WData <<< Qualified syntaxModuleName <<< Ident

-- The shapes ------------------------------------------------------------------------------

syntaxType :: String -> Array Shape -> Shape
syntaxType = ShapeData <<< Qualified syntaxModuleName <<< TyName

-- | `List TokenTree`.
treesShape :: Shape
treesShape = syntaxType "List" [ syntaxType "TokenTree" [] ]

positionShape :: Shape
positionShape = syntaxType "Position" []

-- | `Result (Syntax Term)`.
resultShape :: Shape
resultShape = syntaxType "Result" [ syntaxType "Syntax" [ syntaxType "Term" [] ] ]

-- The answer ------------------------------------------------------------------------------

-- | A `parse`'s answer in the host's types, or why what it carries is not what
-- | its place wants: the session answering with that breaks the protocol.
readAnswer :: Descriptor -> ParseAnswer -> Either String ParseOutcome
readAnswer descriptor = case _ of
  Parsed json -> ParsedAs <$> (checked (syntaxType "Syntax" [ syntaxType "Term" [] ]) json >>= syntaxOf)
  ParseFailed json -> FailedAs <$> (checked (syntaxType "Failure" []) json >>= failureOf)
  ExecutionFailed f -> pure (ExecutionFailedAs f)
  BudgetExceeded -> pure BudgetExceededAs
  where
  checked shape json = do
    value <- case decodeValue json of
      Left problem -> Left ("not a canonical value" <> at problem)
      Right value -> Right value
    case conformsTo descriptor shape value of
      Left problem -> Left ("not of the type its place wants" <> at problem)
      Right _ -> Right value
  at problem = ", at " <> renderPath problem.path <> ": " <> problem.problem

syntaxOf :: WireValue -> Either String (Syntax Term)
syntaxOf = case _ of
  WData _ [ nodes ] -> Syntax <$> listOf nodeOf nodes
  _ -> unread

nodeOf :: WireValue -> Either String SyntaxNode
nodeOf = case _ of
  WData (Qualified _ (Ident "SyntaxToken")) [ t ] -> SyntaxToken <$> tokenOf t
  WData (Qualified _ (Ident "SyntaxGroup")) [ o, d, open, inner, closes ] ->
    SyntaxGroup <$> originOf o <*> delimiterOf d <*> tokenOf open <*> listOf nodeOf inner <*> listOf tokenOf closes
  WData (Qualified _ (Ident "SyntaxLayout")) [ o, items ] -> SyntaxLayout <$> originOf o <*> listOf itemOf items
  _ -> unread

itemOf :: WireValue -> Either String SyntaxItem
itemOf = case _ of
  WData _ [ o, nodes ] -> SyntaxItem <$> originOf o <*> listOf nodeOf nodes
  _ -> unread

tokenOf :: WireValue -> Either String Token
tokenOf = case _ of
  WData _ [ kind, text, range, trivia, origin ] ->
    Token <$> kindOf kind <*> stringOf text <*> rangeOf range <*> listOf triviaOf trivia <*> originOf origin
  _ -> unread

kindOf :: WireValue -> Either String TokenKind
kindOf = case _ of
  WData (Qualified _ (Ident c)) fields -> case c, fields of
    "GroupBracket", [] -> pure GroupBracket
    "Comma", [] -> pure Comma
    "Backslash", [] -> pure Backslash
    "Underscore", [] -> pure Underscore
    "LowerName", [ q, n ] -> LowerName <$> maybeOf stringOf q <*> stringOf n
    "UpperName", [ q, n ] -> UpperName <$> maybeOf stringOf q <*> stringOf n
    "DiscriminatorName", [ q, n ] -> DiscriminatorName <$> maybeOf stringOf q <*> stringOf n
    "OperatorName", [ q, n ] -> OperatorName <$> maybeOf stringOf q <*> stringOf n
    "OperatorValue", [ q, n ] -> OperatorValue <$> maybeOf stringOf q <*> stringOf n
    "InfixName", [ q, n ] -> InfixName <$> maybeOf stringOf q <*> stringOf n
    "HoleName", [ n ] -> HoleName <$> stringOf n
    "TagName", [ n ] -> TagName <$> stringOf n
    "DirectiveName", [ n ] -> DirectiveName <$> stringOf n
    "MacroName", [ q, n ] -> MacroName <$> maybeOf stringOf q <*> stringOf n
    "IntLiteral", [ WInt n ] -> pure (IntLiteral n)
    "NumberLiteral", [ WNumber n ] -> pure (NumberLiteral n)
    "CharLiteral", [ s ] -> CharLiteral <$> stringOf s
    "StringLiteral", [ s ] -> StringLiteral <$> stringOf s
    _, _ -> unread
  _ -> unread

delimiterOf :: WireValue -> Either String Delimiter
delimiterOf = case _ of
  WData (Qualified _ (Ident c)) fields -> case c, fields of
    "Paren", [] -> pure Paren
    "Bracket", [] -> pure Bracket
    "Brace", [] -> pure Brace
    "EffectRow", [] -> pure EffectRow
    "Synthesized", [] -> pure Synthesized
    "AttributeBracket", [] -> pure AttributeBracket
    "LocalOpen", [ m ] -> LocalOpen <$> stringOf m
    _, _ -> unread
  _ -> unread

triviaOf :: WireValue -> Either String Trivia
triviaOf = case _ of
  WData (Qualified _ (Ident c)) [ s, r ] -> case c of
    "Spaces" -> Spaces <$> stringOf s <*> rangeOf r
    "Newline" -> Newline <$> stringOf s <*> rangeOf r
    "LineComment" -> LineComment <$> stringOf s <*> rangeOf r
    "BlockComment" -> BlockComment <$> stringOf s <*> rangeOf r
    _ -> unread
  _ -> unread

failureOf :: WireValue -> Either String ParseFailure
failureOf = case _ of
  WData _ [ p, expected, labels ] -> do
    position <- positionOf p
    e <- listOf stringOf expected
    l <- listOf stringOf labels
    pure { position, expected: Set.fromFoldable e, labels: l }
  _ -> unread

rangeOf :: WireValue -> Either String Range
rangeOf = case _ of
  WData _ [ s, e ] -> Range <$> positionOf s <*> positionOf e
  _ -> unread

positionOf :: WireValue -> Either String Position
positionOf = case _ of
  WData _ [ WInt line, WInt column ] -> pure (Position line column)
  _ -> unread

-- | An origin read from the token it crosses as, `{ "origin": n }`. Only the
-- | form is checked here: whether the host issued that origin for the call is
-- | the expansion's to check, against what it issued.
originOf :: WireValue -> Either String OriginRef
originOf = case _ of
  WToken o
    | [ "origin" ] <- Object.keys o
    , Just n <- Object.lookup "origin" o >>= caseJsonNumber Nothing Int.fromNumber -> pure (OriginRef n)
  _ -> Left "a token that is not of the form of an origin"

stringOf :: WireValue -> Either String String
stringOf = case _ of
  WString s -> pure (textOf s)
  _ -> unread

maybeOf :: forall a. (WireValue -> Either String a) -> WireValue -> Either String (Maybe a)
maybeOf f = case _ of
  WData (Qualified _ (Ident "Nothing")) [] -> pure Nothing
  WData (Qualified _ (Ident "Just")) [ x ] -> Just <$> f x
  _ -> unread

-- | A list, walked without recursing on the host's stack.
listOf :: forall a. (WireValue -> Either String a) -> WireValue -> Either String (Array a)
listOf f = tailRec go <<< { acc: [], rest: _ }
  where
  go { acc, rest } = case rest of
    WData (Qualified _ (Ident "Nil")) [] -> Done (Right acc)
    WData (Qualified _ (Ident "Cons")) [ x, more ] -> case f x of
      Right y -> Loop { acc: Array.snoc acc y, rest: more }
      Left why -> Done (Left why)
    _ -> Done unread

-- | A value the descriptor admitted and this reading does not, which is the two
-- | disagreeing.
unread :: forall a. Either String a
unread = Left "a value the descriptor admits and the host's types do not"
