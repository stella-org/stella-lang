-- | Printing a snapshot as plain text.
-- |
-- | This is the layer above the snapshot, and the only one that decides what
-- | anything looks like ([Structural](Structural.purs)). It reads no value of the
-- | interpreter and no type: **printing by a type is the front end's**, which holds
-- | the type it checked, and this is what a session can say without one
-- | ([Abstract Machine](../../../docs/technical-references/07-Runtime/01-Abstract-Machine.md)).
-- |
-- | What it writes is one line, and it is meant to be read rather than parsed: a
-- | consumer that needs the structure takes the snapshot.
module Steam.Render
  ( render
  , renderKey
  ) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.CodePoint.Unicode (GeneralCategory(..), generalCategory)
import Data.Enum (toEnum)
import Data.Int as Int
import Data.Maybe (Maybe(..))
import Data.String as String
import Data.String.CodePoints (CodePoint)
import Steam.Structural (Cut, NumberAtom(..), StructuralValue(..))
import Stella.Compiler.TypedCore.Domain (ScalarString, ScalarValue, codePointOf, scalarStringOf, scalarsOf, textOf)
import Stella.Compiler.TypedCore.Name (EffName(..), Ident(..), ModuleName(..), Qualified(..), RegionName(..), Symbol(..), Tag(..))
import Stella.Compiler.TypedCore.Type (RowKey(..))

-- | What a snapshot reads as.
-- |
-- | | The value | Written |
-- | | --- | --- |
-- | | a scalar | as itself: `42`, `1.5`, `'a'`, `"text"`, `true` |
-- | | a constructor | its qualified name, and its fields after it in parentheses |
-- | | a record | `{ key: value, … }`, its keys in the snapshot's order |
-- | | a variant | `[key value]` |
-- | | anything applying is the only use of | `<closure>`, `<partial-application>`, `<continuation>` |
-- | | an action, or a value only a foreign observes | `<io>`, `<opaque>` |
-- | | what the limits cut short | `…` |
-- |
-- | A character and a string are written as literals of one, the delimiter escaped
-- | and every character a line cannot carry standing as its code point.
render :: StructuralValue -> P.String
render = case _ of
  SInt n -> show n
  SNumber (NumberAtom n) -> number n
  SChar c -> "'" <> escapedIn apostrophe c <> "'"
  SString s
    | s.complete -> "\"" <> escapedText s.text <> "\""
    | otherwise -> "\"" <> escapedText s.text <> "…\""
  SBoolean b -> if b then "true" else "false"

  SData name fields
    | Array.null fields.items && fields.complete -> renderName name
    | otherwise -> "(" <> renderName name <> " " <> spaced (map render fields.items) fields <> ")"

  SRecord fields
    | Array.null fields.items && fields.complete -> "{}"
    | otherwise -> "{ " <> commas (map field fields.items) fields <> " }"

  SVariant key value -> "[" <> renderKey key <> " " <> render value <> "]"

  SClosure -> "<closure>"
  SPartialApplication -> "<partial-application>"
  SContinuation -> "<continuation>"
  SIO -> "<io>"
  SOpaque -> "<opaque>"
  STruncated -> "…"
  where
  field one = renderKey one.key <> ": " <> render one.value

-- | A key, with the kind it stands at kept: a field and a tag of one spelling are
-- | two keys (D16), so nothing here writes them alike.
-- |
-- | | The key | Written |
-- | | --- | --- |
-- | | a field or an instance name | `name` |
-- | | a variant's tag | `@Tag` |
-- | | a tuple's component | `_0` |
-- | | an effect | `!Module.Effect` |
-- | | a handler's region | `%region`, which no value carries (D36) |
renderKey :: RowKey -> P.String
renderKey = case _ of
  SymbolKey (Symbol name) -> name
  TagKey (Tag tag) -> "@" <> tag
  PositionKey i -> "_" <> show i
  EffectKey (Qualified (ModuleName moduleName) (EffName name)) -> "!" <> moduleName <> "." <> name
  RegionKey (RegionName name) -> "%" <> name

renderName :: Qualified Ident -> P.String
renderName (Qualified (ModuleName moduleName) (Ident name)) = moduleName <> "." <> name

-- | A `Number` as text, **with a negative zero written as one**. The two zeros are
-- | different literals (D37) and a snapshot keeps them apart, so a line that wrote
-- | both as `0.0` would lose a difference the value has.
number :: P.Number -> P.String
number n
  | n == 0.0 && 1.0 / n < 0.0 = "-0.0"
  | otherwise = show n

-- | The text a scalar value spells, which is the text of the one-scalar string it
-- | makes.
scalarText :: ScalarValue -> P.String
scalarText c = textOf (scalarStringOf [ c ])

-- | The text of a string, written between double quotes.
escapedText :: ScalarString -> P.String
escapedText s = String.joinWith "" (map (escapedIn quote) (scalarsOf s))

-- | One scalar value, written so that it neither ends the literal it stands in nor
-- | disappears into the line.
-- |
-- | **The delimiter escaped is the one of the literal it is written in**: an
-- | apostrophe stands for itself in a string and a double quote in a character. A
-- | character no line carries is written by the name it has or else by its code
-- | point, so that every character of the line is one a reader sees.
escapedIn :: P.Int -> ScalarValue -> P.String
escapedIn delimiter c = case codePointOf c of
  code
    | code == delimiter -> "\\" <> scalarText c
    | code == backslash -> "\\\\"
    | code == newline -> "\\n"
    | code == tab -> "\\t"
    | code == carriageReturn -> "\\r"
    | hidden code -> "\\u{" <> hex code <> "}"
    | otherwise -> scalarText c

-- | A character no line carries, which is one of four Unicode categories: a control
-- | (`Cc`), a format character (`Cf`), and a line or paragraph separator (`Zl`,
-- | `Zp`).
-- |
-- | **A format character shows nothing and still acts**, which is why the category
-- | and not a list of the ones a reader has met decides: an override reorders what
-- | follows it, a zero-width space parts a word where nothing is seen, and a tag
-- | character carries text a display never shows. A joiner inside a sequence of
-- | emoji stands as its code point for the same reason.
hidden :: P.Int -> P.Boolean
hidden code = case generalCategory =<< (toEnum code :: Maybe CodePoint) of
  Just Control -> true
  Just Format -> true
  Just LineSeparator -> true
  Just ParagraphSeparator -> true
  _ -> false

-- | A code point, as the digits that name it.
hex :: P.Int -> P.String
hex code = String.toUpper (Int.toStringAs Int.hexadecimal code)

apostrophe :: P.Int
apostrophe = 0x27

quote :: P.Int
quote = 0x22

backslash :: P.Int
backslash = 0x5C

newline :: P.Int
newline = 0x0A

tab :: P.Int
tab = 0x09

carriageReturn :: P.Int
carriageReturn = 0x0D

spaced :: forall a. P.Array P.String -> Cut a -> P.String
spaced parts cut = joined " " parts cut

commas :: forall a. P.Array P.String -> Cut a -> P.String
commas parts cut = joined ", " parts cut

joined :: forall a. P.String -> P.Array P.String -> Cut a -> P.String
joined separator parts cut =
  String.joinWith separator (if cut.complete then parts else Array.snoc parts "…")
