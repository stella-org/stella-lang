-- | Values as a session carries them: the generic JSON a guest's command and the
-- | answer to it cross in.
-- |
-- | ```text
-- | value = { "int": n }
-- |       | { "number": hex16 }
-- |       | { "char": codePoint }
-- |       | { "string": s }
-- |       | { "boolean": b }
-- |       | { "data": { "module", "name" }, "fields": [ value ] }
-- |       | { "record": [ { "key": key, "value": value } ] }
-- |       | { "variant": { "key": key, "value": value } }
-- |       | { "token": object }
-- | key   = { "symbol": s } | { "tag": s } | { "position": n } | { "effect": { "module", "name" } }
-- | ```
-- |
-- | **The encoding is generic and knows no type.** A constructor is named, a record
-- | lists its keys, and nothing says what type a value is of; which values a place
-- | admits is a descriptor's to say ([Shape](Value/Shape.purs)).
-- |
-- | **One value has one encoding: an encoder writes only it and a decoder accepts
-- | only it.** Every object has exactly the members shown; an `int` is an integer
-- | in the 32-bit range; a `number` is the sixteen lowercase hex digits of its
-- | binary64 bit pattern, high nibble first, every NaN written as
-- | `7ff8000000000000` and any NaN pattern read as NaN (D37); a `char` is a Unicode
-- | scalar value and no text holds an unpaired surrogate (D27); a `position` is not
-- | negative; and a record's keys stand once each, in the canonical order of
-- | `compareKeys`. JSON does not tell `0` from `-0` or `0.0`, so an `int` of any of
-- | them is 0.
-- |
-- | **Nothing here recurses on the host's stack.** A `List` is a chain of `Cons`,
-- | so a value is as deep as it is long, and the frame's size is the only bound on
-- | either: decoding and encoding each walk the value with a stack of their own.
module Stella.CLI.Session.Value
  ( WireValue(..)
  , WireField
  , Step(..)
  , ValueProblem
  , renderPath
  , compareKeys
  , encodeValue
  , decodeValue
  ) where

import Prelude

import Control.Monad.Rec.Class as Rec
import Data.Argonaut.Core (Json, fromArray, fromBoolean, fromNumber, fromObject, fromString, toArray, toBoolean, toNumber, toObject, toString)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (all, traverse_)
import Data.Int as Int
import Data.Int.Bits as Bits
import Data.List (List(..), (:))
import Data.List as List
import Data.Maybe (Maybe(..))
import Data.Number (isNaN)
import Data.String (joinWith)
import Data.String.CodeUnits as CodeUnits
import Data.Traversable (sequence)
import Data.Tuple (Tuple(..))
import Foreign.Object (Object)
import Foreign.Object as Object
import Partial.Unsafe (unsafeCrashWith)
import Stella.CLI.Session.Frame (renderJson)
import Stella.CLI.Session.Guest (Token)
import Stella.Compiler.Bytecode.Float (halvesOfNumber, numberOfHalves, quietNaN)
import Stella.Compiler.Bytecode.Module (Key(..))
import Stella.Compiler.TypedCore.Domain (ScalarString, ScalarValue, codePointOf, compareByScalar, sameNumber, scalarString, scalarValue, textOf)
import Stella.Compiler.TypedCore.Name (EffName(..), Ident(..), ModuleName(..), Qualified(..), Symbol(..), Tag(..))

data WireValue
  = WInt Int
  | WNumber Number
  | WChar ScalarValue
  | WString ScalarString
  | WBoolean Boolean
  -- | A constructor by its qualified name, with its fields in order.
  | WData (Qualified Ident) (Array WireValue)
  -- | A record's fields, in the canonical order of their keys.
  | WRecord (Array WireField)
  | WVariant Key WireValue
  -- | A host token, carried unread.
  | WToken Token

type WireField = { key :: Key, value :: WireValue }

-- | One step from a value to a part of it: a member of an object, or an element
-- | of an array. A path is the JSON location, so it reads against what was sent.
data Step
  = Member String
  | Index Int

-- | Why a value was refused, and where in it.
type ValueProblem = { path :: Array Step, problem :: String }

-- | A path as text, `.fields[0].record[2].value`; the root is the empty text.
renderPath :: Array Step -> String
renderPath = joinWith "" <<< map case _ of
  Member name -> "." <> name
  Index i -> "[" <> show i <> "]"

-- | The canonical order of keys. **A kind decides first** — symbol, tag, position,
-- | effect — and within one kind the payload does: text by scalar value, a
-- | position by its number, an effect by its module and then its name.
compareKeys :: Key -> Key -> Ordering
compareKeys a b = case compare (kind a) (kind b) of
  EQ -> within a b
  other -> other
  where
  kind :: Key -> Int
  kind = case _ of
    KSymbol _ -> 0
    KTag _ -> 1
    KPosition _ -> 2
    KEffect _ -> 3

  within x y = case x, y of
    KSymbol (Symbol l), KSymbol (Symbol r) -> compareByScalar l r
    KTag (Tag l), KTag (Tag r) -> compareByScalar l r
    KPosition l, KPosition r -> compare l r
    KEffect (Qualified (ModuleName lm) (EffName l)), KEffect (Qualified (ModuleName rm) (EffName r)) ->
      compareByScalar lm rm <> compareByScalar l r
    _, _ -> EQ

-- Encoding ------------------------------------------------------------------------------

data Emit
  = Emit (List Step) WireValue
  | MakeData (Qualified Ident) Int
  | MakeRecord (Array Key)
  | MakeVariant Key

-- | The value's canonical encoding, or why it has none.
-- |
-- | **A value is held to the rules a decoder holds it to**, so what is sent is
-- | what the other side accepts: a record's keys stand once each and in order, a
-- | position is not negative, and no name or key holds an unpaired surrogate. A
-- | value built by hand can break any of them, and none reaches the wire.
encodeValue :: WireValue -> Either ValueProblem Json
encodeValue value = Rec.tailRec go { work: Emit Nil value : Nil, built: Nil }
  where
  go { work, built } = case work of
    Nil -> Rec.Done (Right (only built))
    task : rest -> case task of
      Emit path v -> case emit path v of
        Left problem -> Rec.Done (Left problem)
        Right (Left json) -> Rec.Loop { work: rest, built: json : built }
        Right (Right parts) -> Rec.Loop { work: List.fromFoldable parts <> rest, built }
      MakeData name n ->
        let
          taken = pop n built
          made = fromObject $ Object.fromFoldable
            [ Tuple "data" (nameJson (\(Ident x) -> x) name), Tuple "fields" (fromArray taken.values) ]
        in
          Rec.Loop { work: rest, built: made : taken.left }
      MakeRecord keys ->
        let
          taken = pop (Array.length keys) built
          entry key v = fromObject (Object.fromFoldable [ Tuple "key" (keyJson key), Tuple "value" v ])
        in
          Rec.Loop { work: rest, built: tagged "record" (fromArray (Array.zipWith entry keys taken.values)) : taken.left }
      MakeVariant key -> case built of
        payload : left ->
          let
            made = tagged "variant" (fromObject (Object.fromFoldable [ Tuple "key" (keyJson key), Tuple "value" payload ]))
          in
            Rec.Loop { work: rest, built: made : left }
        Nil -> unbalanced unit

  -- a value whole, or its parts to encode first and what to make of them
  emit :: List Step -> WireValue -> Either ValueProblem (Either Json (Array Emit))
  emit path = case _ of
    WInt n -> Right (Left (tagged "int" (fromNumber (Int.toNumber n))))
    WNumber n -> Right (Left (tagged "number" (fromString (hexOfNumber n))))
    WChar c -> Right (Left (tagged "char" (fromNumber (Int.toNumber (codePointOf c)))))
    WString s -> Right (Left (tagged "string" (fromString (textOf s))))
    WBoolean b -> Right (Left (tagged "boolean" (fromBoolean b)))
    WToken t -> Right (Left (tagged "token" (fromObject t)))
    WData name@(Qualified (ModuleName m) (Ident c)) fields -> do
      let here = Member "data" : path
      plainText (Member "module" : here) m
      plainText (Member "name" : here) c
      pure $ Right $
        Array.mapWithIndex (\i f -> Emit (Index i : Member "fields" : path) f) fields
          <> [ MakeData name (Array.length fields) ]
    WRecord fields -> do
      let here = Member "record" : path
      traverse_ (\(Tuple i f) -> validKey (Member "key" : Index i : here) f.key)
        (Array.mapWithIndex Tuple fields)
      ascending here (map _.key fields)
      pure $ Right $
        Array.mapWithIndex (\i f -> Emit (Member "value" : Index i : here) f.value) fields
          <> [ MakeRecord (map _.key fields) ]
    WVariant key payload -> do
      let here = Member "variant" : path
      validKey (Member "key" : here) key
      pure (Right [ Emit (Member "value" : here) payload, MakeVariant key ])

  tagged name json = fromObject (Object.singleton name json)

-- | That a key has an encoding a decoder accepts: its text holds no unpaired
-- | surrogate and a position is not negative.
validKey :: List Step -> Key -> Either ValueProblem Unit
validKey path = case _ of
  KSymbol (Symbol s) -> plainText (Member "symbol" : path) s
  KTag (Tag s) -> plainText (Member "tag" : path) s
  KPosition i -> if i < 0 then refuse (Member "position" : path) "a position is not negative" else Right unit
  KEffect (Qualified (ModuleName m) (EffName e)) -> do
    let here = Member "effect" : path
    plainText (Member "module" : here) m
    plainText (Member "name" : here) e

-- | That a name holds no unpaired surrogate.
plainText :: List Step -> String -> Either ValueProblem Unit
plainText path s = case scalarString s of
  Just _ -> Right unit
  Nothing -> refuse path "text holds no unpaired surrogate"

nameJson :: forall a. (a -> String) -> Qualified a -> Json
nameJson unName (Qualified (ModuleName m) x) = fromObject $ Object.fromFoldable
  [ Tuple "module" (fromString m), Tuple "name" (fromString (unName x)) ]

keyJson :: Key -> Json
keyJson = case _ of
  KSymbol (Symbol s) -> fromObject (Object.singleton "symbol" (fromString s))
  KTag (Tag s) -> fromObject (Object.singleton "tag" (fromString s))
  KPosition i -> fromObject (Object.singleton "position" (fromNumber (Int.toNumber i)))
  KEffect name -> fromObject (Object.singleton "effect" (nameJson (\(EffName e) -> e) name))

-- | The binary64 bit pattern as sixteen lowercase hex digits, every NaN as the one
-- | quiet NaN.
hexOfNumber :: Number -> String
hexOfNumber n = word halves.hi <> word halves.lo
  where
  halves = if isNaN n then quietNaN else halvesOfNumber n
  word w = quad (Bits.zshr w 16) <> quad (Bits.and w 0xFFFF)
  quad q =
    let
      digits = Int.toStringAs Int.hexadecimal q
    in
      CodeUnits.fromCharArray (Array.replicate (4 - CodeUnits.length digits) '0') <> digits

-- Decoding ------------------------------------------------------------------------------

data Task
  = Visit (List Step) Json
  | BuildData (Qualified Ident) Int
  | BuildRecord (Array Key)
  | BuildVariant Key

-- | What one visit finds: a value whole, or a composite still to be built from
-- | the values its parts decode to.
data Visited
  = Leaf WireValue
  | Parts Task (Array Task)

-- | The value a JSON text's canonical encoding stands for, or why it is not one.
decodeValue :: Json -> Either ValueProblem WireValue
decodeValue json = Rec.tailRec go { work: Visit Nil json : Nil, built: Nil }
  where
  go { work, built } = case work of
    Nil -> Rec.Done (Right (only built))
    task : rest -> case task of
      Visit path j -> case visit path j of
        Left p -> Rec.Done (Left p)
        Right (Leaf v) -> Rec.Loop { work: rest, built: v : built }
        Right (Parts build parts) -> Rec.Loop { work: List.fromFoldable parts <> (build : rest), built }
      BuildData name n ->
        let
          taken = pop n built
        in
          Rec.Loop { work: rest, built: WData name taken.values : taken.left }
      BuildRecord keys ->
        let
          taken = pop (Array.length keys) built
        in
          Rec.Loop
            { work: rest
            , built: WRecord (Array.zipWith (\key value -> { key, value }) keys taken.values) : taken.left
            }
      BuildVariant key -> case built of
        payload : left -> Rec.Loop { work: rest, built: WVariant key payload : left }
        Nil -> unbalanced unit

visit :: List Step -> Json -> Either ValueProblem Visited
visit path json = do
  o <- objectAt path json
  case Array.sort (Object.keys o) of
    [ "int" ] -> Leaf <<< WInt <$> (member path "int" o >>= intAt (Member "int" : path))
    [ "number" ] -> Leaf <<< WNumber <$> do
      let here = Member "number" : path
      text <- member path "number" o >>= stringAt here
      case numberOfHex text of
        Just n -> Right n
        Nothing -> refuse here "a number is sixteen lowercase hex digits"
    [ "char" ] -> Leaf <<< WChar <$> do
      let here = Member "char" : path
      n <- member path "char" o >>= intAt here
      case scalarValue n of
        Just c -> Right c
        Nothing -> refuse here "a char is a Unicode scalar value"
    [ "string" ] -> Leaf <<< WString <$> do
      let here = Member "string" : path
      member path "string" o >>= textAt here
    [ "boolean" ] -> Leaf <<< WBoolean <$> do
      let here = Member "boolean" : path
      member path "boolean" o >>= \b -> present here "a boolean is true or false" (toBoolean b)
    [ "token" ] -> Leaf <<< WToken <$> (member path "token" o >>= objectAt (Member "token" : path))
    [ "data", "fields" ] -> do
      name <- member path "data" o >>= qualifiedAt (Member "data" : path) Ident
      let here = Member "fields" : path
      fields <- member path "fields" o >>= arrayAt here
      pure $ Parts (BuildData name (Array.length fields))
        (Array.mapWithIndex (\i field -> Visit (Index i : here) field) fields)
    [ "record" ] -> do
      let here = Member "record" : path
      entries <- member path "record" o >>= arrayAt here
      fields <- sequence $ Array.mapWithIndex (\i entry -> keyed (Index i : here) entry) entries
      ascending here (map _.key fields)
      pure $ Parts (BuildRecord (map _.key fields)) (map (\f -> Visit f.at f.value) fields)
    [ "variant" ] -> do
      field <- member path "variant" o >>= keyed (Member "variant" : path)
      pure (Parts (BuildVariant field.key) [ Visit field.at field.value ])
    _ -> refuse path "a value is one of int, number, char, string, boolean, data, record, variant, and token, with exactly its members"

-- | `{ "key": key, "value": value }`: the key, and the value still to decode.
keyed :: List Step -> Json -> Either ValueProblem { key :: Key, value :: Json, at :: List Step }
keyed path json = do
  o <- objectAt path json
  exactly path [ "key", "value" ] o
  key <- member path "key" o >>= keyAt (Member "key" : path)
  value <- member path "value" o
  pure { key, value, at: Member "value" : path }

-- | That each key stands after the one before it, which rules out a key twice.
ascending :: List Step -> Array Key -> Either ValueProblem Unit
ascending path keys = case Array.findIndex out (Array.zip keys (Array.drop 1 keys)) of
  Nothing -> Right unit
  Just i -> refuse (Member "key" : Index (i + 1) : path) "a record's keys stand once each, in ascending order"
  where
  out (Tuple before after) = compareKeys before after /= LT

keyAt :: List Step -> Json -> Either ValueProblem Key
keyAt path json = do
  o <- objectAt path json
  case Object.keys o of
    [ "symbol" ] -> KSymbol <<< Symbol <$> (member path "symbol" o >>= plainTextAt (Member "symbol" : path))
    [ "tag" ] -> KTag <<< Tag <$> (member path "tag" o >>= plainTextAt (Member "tag" : path))
    [ "position" ] -> do
      let here = Member "position" : path
      i <- member path "position" o >>= intAt here
      if i < 0 then refuse here "a position is not negative" else Right (KPosition i)
    [ "effect" ] -> KEffect <$> (member path "effect" o >>= qualifiedAt (Member "effect" : path) EffName)
    _ -> refuse path "a key is one of symbol, tag, position, and effect"

qualifiedAt :: forall a. List Step -> (String -> a) -> Json -> Either ValueProblem (Qualified a)
qualifiedAt path make json = do
  o <- objectAt path json
  exactly path [ "module", "name" ] o
  m <- member path "module" o >>= plainTextAt (Member "module" : path)
  name <- member path "name" o >>= plainTextAt (Member "name" : path)
  pure (Qualified (ModuleName m) (make name))

-- | The sixteen hex digits of a binary64, any NaN pattern read as NaN.
numberOfHex :: String -> Maybe Number
numberOfHex text =
  if CodeUnits.length text /= 16 || not (all hexDigit (CodeUnits.toCharArray text)) then Nothing
  else do
    a <- quad 0
    b <- quad 4
    c <- quad 8
    d <- quad 12
    let n = numberOfHalves (Bits.or (Bits.shl a 16) b) (Bits.or (Bits.shl c 16) d)
    pure if isNaN n then numberOfHalves quietNaN.hi quietNaN.lo else n
  where
  hexDigit ch = (ch >= '0' && ch <= '9') || (ch >= 'a' && ch <= 'f')
  quad at = Int.fromStringAs Int.hexadecimal (CodeUnits.take 4 (CodeUnits.drop at text))

-- Reading ------------------------------------------------------------------------------

refuse :: forall a. List Step -> String -> Either ValueProblem a
refuse path problem = Left { path: Array.reverse (Array.fromFoldable path), problem }

-- | What was found, or a refusal. **The refusal is built only where nothing was**:
-- | a path is as long as the value is deep, so building one for every value read
-- | would make reading a long list quadratic.
present :: forall a. List Step -> String -> Maybe a -> Either ValueProblem a
present path problem = case _ of
  Just a -> Right a
  Nothing -> refuse path problem

exactly :: List Step -> Array String -> Object Json -> Either ValueProblem Unit
exactly path names o
  | Array.sort (Object.keys o) == Array.sort names = Right unit
  | otherwise = refuse path ("an object with exactly the members " <> joinWith ", " names)

member :: List Step -> String -> Object Json -> Either ValueProblem Json
member path name o = case Object.lookup name o of
  Just json -> Right json
  Nothing -> refuse path ("an object with the member " <> name)

objectAt :: List Step -> Json -> Either ValueProblem (Object Json)
objectAt path = present path "an object" <<< toObject

arrayAt :: List Step -> Json -> Either ValueProblem (Array Json)
arrayAt path = present path "an array" <<< toArray

stringAt :: List Step -> Json -> Either ValueProblem String
stringAt path = present path "a string" <<< toString

-- | Text holding no unpaired surrogate.
textAt :: List Step -> Json -> Either ValueProblem ScalarString
textAt path json = do
  s <- stringAt path json
  case scalarString s of
    Just text -> Right text
    Nothing -> refuse path "text holds no unpaired surrogate"

plainTextAt :: List Step -> Json -> Either ValueProblem String
plainTextAt path json = textOf <$> textAt path json

intAt :: List Step -> Json -> Either ValueProblem Int
intAt path json = do
  n <- present path "a number" (toNumber json)
  case Int.fromNumber n of
    Just i -> Right i
    Nothing -> refuse path "an integer in the 32-bit range"

-- The stacks ------------------------------------------------------------------------------

-- | The last `n` values built, in the order they were built, and what is below them.
pop :: forall a. Int -> List a -> { values :: Array a, left :: List a }
pop n built =
  { values: Array.reverse (Array.fromFoldable (List.take n built))
  , left: List.drop n built
  }

-- | The one value a walk ends with. Each composite takes what its parts built and
-- | leaves one value, so a walk of one value leaves one.
only :: forall a. List a -> a
only = case _ of
  value : Nil -> value
  _ -> unbalanced unit

unbalanced :: forall a. Unit -> a
unbalanced _ = unsafeCrashWith "a walk of one value left other than one value"

-- Instances --------------------------------------------------------------------------------

-- | Structural equality, a number by its identity as a literal (D37). It walks the
-- | two values with a stack of its own, as everything here does.
instance Eq WireValue where
  eq a b = Rec.tailRec go (Tuple a b : Nil)
    where
    go = case _ of
      Nil -> Rec.Done true
      Tuple x y : rest -> case x, y of
        WInt l, WInt r | l == r -> Rec.Loop rest
        WNumber l, WNumber r | sameNumber l r -> Rec.Loop rest
        WChar l, WChar r | l == r -> Rec.Loop rest
        WString l, WString r | l == r -> Rec.Loop rest
        WBoolean l, WBoolean r | l == r -> Rec.Loop rest
        WToken l, WToken r | renderJson (fromObject l) == renderJson (fromObject r) -> Rec.Loop rest
        WData ln lf, WData rn rf | ln == rn && Array.length lf == Array.length rf ->
          Rec.Loop (List.fromFoldable (Array.zip lf rf) <> rest)
        WRecord lf, WRecord rf | map _.key lf == map _.key rf ->
          Rec.Loop (List.fromFoldable (Array.zip (map _.value lf) (map _.value rf)) <> rest)
        WVariant lk lv, WVariant rk rv | lk == rk -> Rec.Loop (Tuple lv rv : rest)
        _, _ -> Rec.Done false

-- | The value's canonical encoding, or where it has none.
instance Show WireValue where
  show v = case encodeValue v of
    Right json -> renderJson json
    Left p -> "(no canonical encoding: " <> renderPath p.path <> ": " <> p.problem <> ")"

derive instance Eq Step

instance Show Step where
  show = case _ of
    Member name -> "Member " <> show name
    Index i -> "Index " <> show i
