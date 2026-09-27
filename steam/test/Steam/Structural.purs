-- | `inspect` and `render`, the two layers a session's answer passes through.
-- |
-- | What the snapshot holds is checked apart from what the text says, which is the
-- | point of the split: a consumer that needs the structure takes the snapshot, and
-- | one that needs a line takes the text.
module Test.Steam.Structural (spec) where

import Prelude

import Prim as P

import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Class (liftEffect)
import Effect.Ref as Ref
import Effect.Uncurried (runEffectFn1, runEffectFn3)
import Steam.Array as Arr
import Steam.Render (render, renderKey)
import Steam.Structural (NumberAtom(..), SnapshotLimits, RuntimeNames, StructuralValue(..), compareKeys, defaultLimits, inspect)
import Steam.Value (Continuation(..), CtorId(..), IOValue(..), KeyId(..), ModuleId(..), OpId(..), Value(..))
import Stella.Compiler.Bytecode.Instr (FuncIx(..))
import Stella.Compiler.Bytecode.Module (Key(..))
import Stella.Compiler.TypedCore.Domain (ScalarString, ScalarValue, scalarString, scalarValue)
import Stella.Compiler.TypedCore.Name (EffName(..), Ident(..), ModuleName(..), OpName(..), Qualified(..), Symbol(..), Tag(..))
import Stella.Compiler.TypedCore.Type (RowKey(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

-- The names a registry would have assigned ------------------------------------------

pairCtor :: CtorId
pairCtor = CtorId 0

nilCtor :: CtorId
nilCtor = CtorId 1

-- | The key spelled `b`, under the **lower** identity: an order by identity would put
-- | it first, and the order of a snapshot's fields is the keys' own.
keyB :: KeyId
keyB = KeyId 2

keyA :: KeyId
keyA = KeyId 3

keyLeft :: KeyId
keyLeft = KeyId 4

pairName :: Qualified Ident
pairName = Qualified (ModuleName "Main") (Ident "Pair")

nilName :: Qualified Ident
nilName = Qualified (ModuleName "Main") (Ident "Nil")

names :: RuntimeNames
names =
  { ctors: Map.fromFoldable [ Tuple pairCtor pairName, Tuple nilCtor nilName ]
  , keys: Map.fromFoldable
      [ Tuple keyB (KSymbol (Symbol "b"))
      , Tuple keyA (KSymbol (Symbol "a"))
      , Tuple keyLeft (KTag (Tag "Left"))
      ]
  , ops: Map.fromFoldable [ Tuple (OpId 5) (OpName "next") ]
  }

snapshot :: Value -> StructuralValue
snapshot = inspect defaultLimits names

within :: SnapshotLimits -> Value -> StructuralValue
within limits = inspect limits names

text :: P.String -> Maybe ScalarString
text = scalarString

scalar :: P.Int -> Maybe ScalarValue
scalar = scalarValue

record :: P.Array (Tuple KeyId Value) -> Value
record = VRecord <<< (Map.fromFoldable :: P.Array (Tuple KeyId Value) -> Map KeyId Value)

-- | The line a character literal of a code reads as, where the code stands for a
-- | scalar value.
charLine :: P.Int -> Maybe P.String
charLine code = map (\c -> render (snapshot (VChar c))) (scalar code)

-- | The line a string literal of some text reads as.
stringLine :: P.String -> Maybe P.String
stringLine s = map (\value -> render (snapshot (VString value))) (text s)

-- | A closure, which nothing takes apart.
closureValue :: Effect Value
closureValue = do
  captures <- Ref.new Map.empty
  pure (VClos { func: { module: ModuleId 0, func: FuncIx 0 }, captures })

-- | A nesting of one constructor around itself, as deep as asked.
nested :: P.Int -> Value
nested n
  | n <= 0 = VData nilCtor []
  | otherwise = VData pairCtor [ nested (n - 1) ]

spec :: Spec Unit
spec = describe "Steam.Structural" do

  describe "a scalar stands for itself" do
    it "carries an Int and a Boolean" do
      snapshot (VInt 42) `shouldEqual` SInt 42
      render (snapshot (VInt (-1))) `shouldEqual` "-1"
      render (snapshot (VBoolean true)) `shouldEqual` "true"

    it "carries a Number under the identity of a literal" do
      -- `0.0` and `-0.0` are different literals and a NaN is one literal (D37), and
      -- the snapshot compares them that way rather than as the host does
      snapshot (VNumber 0.0) `shouldEqual` SNumber (NumberAtom 0.0)
      (snapshot (VNumber 0.0) == snapshot (VNumber (-0.0))) `shouldEqual` false
      (snapshot (VNumber nan) == snapshot (VNumber nan)) `shouldEqual` true

    it "writes a negative zero as one" do
      -- the snapshot keeps the two zeros apart, and so does the line
      render (snapshot (VNumber (-0.0))) `shouldEqual` "-0.0"
      render (snapshot (VNumber 0.0)) `shouldEqual` "0.0"
      render (snapshot (VNumber nan)) `shouldEqual` "NaN"

    it "carries a Char and a String, escaping what a line would swallow" do
      case scalar 0x61, text "a\nb" of
        Just c, Just s -> do
          snapshot (VChar c) `shouldEqual` SChar c
          render (snapshot (VChar c)) `shouldEqual` "'a'"
          render (snapshot (VString s)) `shouldEqual` "\"a\\nb\""
        _, _ -> fail "the fixtures are scalar values"

    it "escapes the delimiter of the literal it writes, and only that one" do
      -- an apostrophe ends a character and a quote a string, so each is escaped
      -- where it stands in one and left alone where it stands in the other
      charLine 0x27 `shouldEqual` Just "'\\''"
      charLine 0x22 `shouldEqual` Just "'\"'"
      charLine 0x5C `shouldEqual` Just "'\\\\'"
      stringLine "a'b" `shouldEqual` Just "\"a'b\""

    it "writes a character no line would carry as its code point" do
      charLine 0x00 `shouldEqual` Just "'\\u{0}'"
      charLine 0x7F `shouldEqual` Just "'\\u{7F}'"
      charLine 0x9F `shouldEqual` Just "'\\u{9F}'"
      -- the ones with a name keep it
      charLine 0x0A `shouldEqual` Just "'\\n'"
      stringLine "ab\x0" `shouldEqual` Just "\"ab\\u{0}\""

    it "writes a character that shows nothing and still acts" do
      -- a format character is invisible and not inert, so what a display would have
      -- acted on stands in the line: an override reorders what follows it, a zero
      -- width space parts a word, and a tag character carries text nothing shows
      charLine 0x202E `shouldEqual` Just "'\\u{202E}'"
      charLine 0x200B `shouldEqual` Just "'\\u{200B}'"
      charLine 0x00AD `shouldEqual` Just "'\\u{AD}'"
      charLine 0xE0041 `shouldEqual` Just "'\\u{E0041}'"
      stringLine "a\x202Ez" `shouldEqual` Just "\"a\\u{202E}z\""

    it "leaves a character a reader sees alone" do
      -- the category is what decides, and a letter, a mark, or a space is carried
      charLine 0x61 `shouldEqual` Just "'a'"
      charLine 0x20 `shouldEqual` Just "' '"
      charLine 0x1F600 `shouldEqual` Just "'😀'"
      charLine 0x3042 `shouldEqual` Just "'あ'"

    it "writes the separators a display would end the line at" do
      -- neither is a control character, and both end a line where something shows
      -- the text
      charLine 0x2028 `shouldEqual` Just "'\\u{2028}'"
      charLine 0x2029 `shouldEqual` Just "'\\u{2029}'"
      stringLine "a\x2028z" `shouldEqual` Just "\"a\\u{2028}z\""
      stringLine "a\x2029z" `shouldEqual` Just "\"a\\u{2029}z\""

  describe "a constructor" do
    it "carries the name its declaration gave it" do
      snapshot (VData pairCtor [ VInt 1, VInt 2 ])
        `shouldEqual` SData pairName { items: [ SInt 1, SInt 2 ], complete: true }
      render (snapshot (VData pairCtor [ VInt 1, VInt 2 ])) `shouldEqual` "(Main.Pair 1 2)"

    it "is written alone where it has no fields" do
      render (snapshot (VData nilCtor [])) `shouldEqual` "Main.Nil"

    it "is truncated where the registry holds no name for it" do
      -- a value of a module that was never loaded, which nothing can name
      snapshot (VData (CtorId 99) []) `shouldEqual` STruncated

  describe "a record" do
    it "orders its fields by their keys and not by their identities" do
      let value = record [ Tuple keyB (VInt 2), Tuple keyA (VInt 1) ]
      snapshot value
        `shouldEqual` SRecord
          { items:
              [ { key: SymbolKey (Symbol "a"), value: SInt 1 }
              , { key: SymbolKey (Symbol "b"), value: SInt 2 }
              ]
          , complete: true
          }
      render (snapshot value) `shouldEqual` "{ a: 1, b: 2 }"

    it "is written empty where it carries nothing" do
      render (snapshot (record [])) `shouldEqual` "{}"

  describe "a variant" do
    it "keeps the kind of its key" do
      snapshot (VVariant keyLeft (VInt 1))
        `shouldEqual` SVariant (TagKey (Tag "Left")) (SInt 1)
      render (snapshot (VVariant keyLeft (VInt 1))) `shouldEqual` "[@Left 1]"

    it "orders keys by kind, and a spelling by scalar value" do
      -- a kind decides first, so a field stands before a tag whatever the spellings
      compareKeys (SymbolKey (Symbol "z")) (TagKey (Tag "a")) `shouldEqual` LT
      compareKeys (PositionKey 2) (PositionKey 10) `shouldEqual` LT
      compareKeys (EffectKey (Qualified (ModuleName "A") (EffName "E")))
        (EffectKey (Qualified (ModuleName "B") (EffName "E")))
        `shouldEqual` LT
      -- `U+E000` stands below an astral character by scalar value, and above it by
      -- the code units a host holds text in
      compareKeys (SymbolKey (Symbol privateUse)) (SymbolKey (Symbol astral))
        `shouldEqual` LT

    it "writes a field and a tag of one spelling differently" do
      -- a `SymbolKey` and a `TagKey` are two keys (D16), so nothing collapses them
      renderKey (SymbolKey (Symbol "X")) `shouldEqual` "X"
      renderKey (TagKey (Tag "X")) `shouldEqual` "@X"
      renderKey (PositionKey 0) `shouldEqual` "_0"

  describe "what applying is the only use of" do
    it "is what it is and nothing more" do
      value <- liftEffect closureValue
      snapshot value `shouldEqual` SClosure
      render (snapshot value) `shouldEqual` "<closure>"

    it "reaches nothing under a continuation or an action" do
      snapshot (VCont (Continuation [])) `shouldEqual` SContinuation
      render (snapshot (VIO (IOPure (VInt 1)))) `shouldEqual` "<io>"

    -- an array is an `intrinsic opaque`, so a snapshot stops at it as it stops at
    -- those: what the payload holds belongs to the interpreter and to no report
    it "stops at an array, whatever its slots hold" do
      array <- liftEffect do
        allocated <- runEffectFn1 Arr.allocate 2
        runEffectFn3 Arr.write allocated 0 (VInt 1)
        pure (VOpaque (Arr.toOpaque allocated))
      snapshot array `shouldEqual` SOpaque
      render (snapshot array) `shouldEqual` "<opaque>"

  describe "the limits, which a snapshot always stops within" do
    it "stops at the depth it is given" do
      -- two levels of nesting, and a marker where the third would stand
      within (defaultLimits { maxDepth = 2 }) (nested 5)
        `shouldEqual` SData pairName
          { items: [ SData pairName { items: [ STruncated ], complete: true } ]
          , complete: true
          }

    it "stops the sequence where the nodes run out, and the sequence says so" do
      -- what the budget runs out on is a tail: the elements taken are carried, and
      -- nothing stands in the place of the ones that are not
      within (defaultLimits { maxNodes = 2 }) (VData pairCtor [ VInt 1, VInt 2 ])
        `shouldEqual` SData pairName { items: [ SInt 1 ], complete: false }

    it "keeps a marker the budget had no room for, the depth having stopped it" do
      -- a marker costs nothing, so the elements of the sequence are there and the
      -- sequence is all of what the value held
      within (defaultLimits { maxDepth = 1, maxNodes = 1 })
        (VData pairCtor [ VInt 1, VInt 2 ])
        `shouldEqual` SData pairName { items: [ STruncated, STruncated ], complete: true }

    it "keeps a marker for an identity it cannot name, whatever the budget" do
      within (defaultLimits { maxNodes = 1 })
        (VData pairCtor [ VData (CtorId 99) [], VData (CtorId 99) [] ])
        `shouldEqual` SData pairName { items: [ STruncated, STruncated ], complete: true }

    it "answers with a marker alone where it may carry no node at all" do
      within (defaultLimits { maxNodes = 0 }) (VInt 1) `shouldEqual` STruncated

    it "leaves a sequence complete where only its elements were cut short" do
      -- the depth is a place and not a budget: at the limit every value under it is a
      -- marker, and the sequence is still all of what the value held
      within (defaultLimits { maxDepth = 1 }) (VData pairCtor [ nested 3, nested 3 ])
        `shouldEqual` SData pairName { items: [ STruncated, STruncated ], complete: true }

    it "says where it stopped short of a collection" do
      let value = VData pairCtor [ VInt 1, VInt 2, VInt 3 ]
      within (defaultLimits { maxItems = 2 }) value
        `shouldEqual` SData pairName { items: [ SInt 1, SInt 2 ], complete: false }
      render (within (defaultLimits { maxItems = 2 }) value)
        `shouldEqual` "(Main.Pair 1 2 …)"

    it "reads a limit below none as none" do
      -- a request carries the limits, and a count is never negative
      within (defaultLimits { maxItems = -1 }) (VData pairCtor [ VInt 1 ])
        `shouldEqual` SData pairName { items: [], complete: false }

    it "carries the prefix of a string longer than it allows" do
      case text "abcdef" of
        Nothing -> fail "the fixture is a scalar string"
        Just s -> do
          let taken = within (defaultLimits { maxTextUnits = 3 }) (VString s)
          render taken `shouldEqual` "\"abc…\""

-- | Two spellings whose order by scalar value is the reverse of their order by the
-- | code units a host holds them in.
astral :: P.String
astral = "\x1F600"

privateUse :: P.String
privateUse = "\xE000"

nan :: P.Number
nan = 0.0 / 0.0
