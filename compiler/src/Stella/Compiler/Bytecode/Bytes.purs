-- | The primitives of the `.dmo` encoding, in both directions
-- | ([Encoding](../../../../docs/technical-references/05-Backend/02-Encoding.md)).
-- |
-- | A `uvar` carries at most 32 bits and is written in its shortest form; a
-- | structural value — a count, an index, a register, an arity, and their kin —
-- | is at most `0x7FFFFFFF` besides. A `svar` is a zigzag over a 32-bit signed
-- | integer, which is what the wider carrier exists for.
-- |
-- | **One error type covers both the bytes and the forms above them.** A file a
-- | reader cannot read is one failure whichever layer notices it, and a decoder
-- | reports it rather than producing a module the encoder did not write.
module Stella.Compiler.Bytecode.Bytes
  ( Bytes
  , EncodeError(..)
  , Fault(..)
  , u8
  , uvar
  , svar
  , f64
  , utf8
  , TagKind(..)
  , TableKind(..)
  , DecodeError(..)
  , R
  , runR
  , throwR
  , byte
  , expect
  , uvarR
  , structuralR
  , svarR
  , f64R
  , utf8R
  , vecR
  , remainingR
  , takeR
  , skipR
  , atEndR
  , positionR
  ) where

import Prelude

import Prim as P

import Stella.Compiler.Primitive (PrimOp)
import Stella.Compiler.Bytecode.Float as Float
import Stella.Compiler.TypedCore.Domain (ScalarString, scalarStringOf, scalarValue)
import Stella.Compiler.TypedCore.Name (Ident)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Enum (fromEnum)
import Data.Generic.Rep (class Generic)
import Data.Int.Bits as Bits
import Data.Maybe (Maybe(..))
import Data.Show.Generic (genericShow)
import Data.String.CodePoints (toCodePointArray)
import Data.Traversable (sequence, traverse)
import Data.Tuple (Tuple(..))

type Bytes = P.Array P.Int

-- | What a module holds that neither an encoder may write nor a reader may read.
-- |
-- | **One vocabulary, because one walk finds them**: an encoder refuses to write a
-- | module carrying one of these, and a decoder refuses to hand one back, so the
-- | two agree on which modules a file may carry
-- | ([Validate](Validate.purs)).
data Fault
  -- | A structural value below zero, which no count, index, register, or arity
  -- | is. A negative would be written as its 32-bit pattern and read back as a
  -- | value no module holds.
  = NegativeValue P.Int
  | IndexOutOfTable TableKind P.Int
  -- | A register a function's own file does not hold.
  | RegisterOutOfFile P.Int
  -- | A capture a function does not take, read by a `CAPT` of its own body.
  | CaptureOutOfRange P.Int
  -- | A `JMP` naming a join point the function does not declare.
  | JoinNotDeclared P.Int

-- | What an encoder refuses.
data EncodeError
  -- | Text no reader may read. A `String` and a `Char` literal carry their
  -- | invariant in their types, so what is left is a name, whose spelling belongs
  -- | to a lexer that does not exist yet.
  = NotScalarText P.String
  -- | A callee naming an operation the module's `PRIMS` does not hold. The
  -- | callee is written as an index into that table, so there is nothing to
  -- | write.
  | OperationNotInPrims PrimOp
  -- | A module this encoder cannot write faithfully, as the version it claims.
  -- | What a byte means is this format's, and what an operation's code means is
  -- | this ABI version's.
  | NotThisFormatVersion P.Int
  | NotThisAbiVersion P.String
  -- | A module no reader would read back. **What an encoder writes, a decoder
  -- | returns**, so what would break that is refused here rather than written.
  | Unwritable Fault
  -- | An arity below one, as the name it stands under. A definitional arity counts
  -- | leading lambdas, so a value with none is absent from an interface rather than
  -- | present at zero.
  | ArityBelowOne Ident P.Int
  -- | A precedence or a row position below zero, which a count is never.
  | CountBelowZero P.Int

-- Writing ------------------------------------------------------------------------

u8 :: P.Int -> Bytes
u8 n = [ Bits.and n 0xFF ]

-- | LEB128, in its shortest form: seven bits per byte, least significant first,
-- | the high bit set on every byte but the last.
-- |
-- | A negative carries its 32-bit pattern, which is what a zigzag needs of the
-- | least `Int`; every structural value is non-negative and takes the short
-- | branch below `0x80`.
uvar :: P.Int -> Bytes
uvar n
  | n >= 0 && n < 0x80 = [ n ]
  | otherwise = Array.cons (Bits.or 0x80 (Bits.and n 0x7F)) (uvar (Bits.zshr n 7))

-- | A zigzag: `n ≥ 0` becomes `2n` and `n < 0` becomes `-2n-1`, so a small
-- | magnitude of either sign is a short varint.
svar :: P.Int -> Bytes
svar n = uvar (Bits.xor (Bits.shl n 1) (Bits.shr n 31))

-- | Eight bytes of IEEE 754 binary64, least significant first.
-- |
-- | **Every NaN is written as the one quiet NaN**: all of them are one literal
-- | (D37), so a payload would carry a distinction the language does not make and
-- | leave one module two files.
f64 :: P.Number -> Bytes
f64 x = u32 halves.lo <> u32 halves.hi
  where
  halves = if x /= x then Float.quietNaN else Float.halvesOfNumber x

u32 :: P.Int -> Bytes
u32 n =
  [ Bits.and n 0xFF
  , Bits.and (Bits.zshr n 8) 0xFF
  , Bits.and (Bits.zshr n 16) 0xFF
  , Bits.and (Bits.zshr n 24) 0xFF
  ]

-- | UTF-8, refusing text that carries an unpaired surrogate. A Stella `String`
-- | holds none (D27), so what this rejects is a name.
utf8 :: P.String -> Either EncodeError Bytes
utf8 text = map Array.concat (traverse scalar (map fromEnum (toCodePointArray text)))
  where
  scalar code
    | code >= 0xD800 && code <= 0xDFFF = Left (NotScalarText text)
    | code < 0x80 = Right [ code ]
    | code < 0x800 = Right
        [ Bits.or 0xC0 (Bits.zshr code 6)
        , continuation code 0
        ]
    | code < 0x10000 = Right
        [ Bits.or 0xE0 (Bits.zshr code 12)
        , continuation code 6
        , continuation code 0
        ]
    | otherwise = Right
        [ Bits.or 0xF0 (Bits.zshr code 18)
        , continuation code 12
        , continuation code 6
        , continuation code 0
        ]

  continuation code shift = Bits.or 0x80 (Bits.and (Bits.zshr code shift) 0x3F)

-- Reading ------------------------------------------------------------------------

-- | What was being read where an unknown byte stood.
data TagKind
  = ConstantTag
  | KeyTag
  | CalleeTag
  | GlobalKind
  | ClauseFormTag
  | RepTag
  | InstrOpcode
  | TailOpcode
  | DefaultTag
  | BooleanByte
  | NewtypeByte
  -- What an interface holds.
  | KindTag
  | RowKindTag
  | TypeTag
  | RowEntryTag
  | RowKeyTag
  | ConstraintTag
  | SchemeTag
  | OptionByte
  | ViaTag
  | EntityTag
  | ValueSortTag
  | ObservationTag
  | TypeSortTag
  | CanonicalClassTag
  | AssociativityTag
  | FixityTargetTag
  | LiteralTag
  | AttributeConstantTag

-- | What an index was an index into.
data TableKind
  = StringTable
  | ConstantTable
  | KeyTable
  | OpTable
  | CtorRefTable
  | ForeignRefTable
  | GlobalRefTable
  | CalleeTable
  | PrimTable
  | HandlerTable
  | FunctionTable

data DecodeError
  = BadMagic
  | UnsupportedFormatVersion P.Int
  | UnknownFlags P.Int
  | UnknownAbiVersion P.String
  -- | A required section the file does not hold, by its id. A missing section is
  -- | not an empty one.
  | SectionMissing P.Int
  -- | Two sections out of order, as the id before and the id read. The ids
  -- | ascend strictly, so this rejects a repeat as well.
  | SectionOutOfOrder P.Int P.Int
  -- | A section whose payload did not end where its length said, by its id.
  | SectionLengthMismatch P.Int
  -- | An unknown id below the boundary, which bears on what a module computes.
  | UnknownSection P.Int
  | UnknownTag TagKind P.Int
  -- | A code the ABI version this reader holds does not name.
  | UnknownOperationCode P.Int
  | VarTooLong
  | VarOverflow
  | VarNotMinimal
  -- | A count, an index, a register, or their kin above `0x7FFFFFFF`.
  | StructuralOutOfRange P.Int
  | BadUtf8
  -- | A code point no scalar value holds, in text or in a `Char` constant.
  | NotAScalarValue P.Int
  | IndexOutOfRange TableKind P.Int
  -- | A module the bytes carry that no module may be: a negative where a count
  -- | stands, or an index naming nothing. What an encoder refuses to write, a
  -- | decoder refuses to return ([Validate](Validate.purs)).
  | Malformed Fault
  -- | An interface entry whose arity is not positive.
  | ArityNotPositive P.Int
  -- | Interface entries that do not ascend strictly by name, a repeated name among
  -- | them. The order is the format's, and one module has one file.
  | EntriesOutOfOrder
  -- | A byte after what the file holds. A longer file is a later format, not this
  -- | one with something ignorable at the end.
  | TrailingBytes
  | UnexpectedEnd

type State =
  { bytes :: Bytes
  , pos :: P.Int
  }

newtype R a = R (State -> Either DecodeError (Tuple a State))

runR :: forall a. Bytes -> R a -> Either DecodeError a
runR bytes (R f) = map (\(Tuple a _) -> a) (f { bytes, pos: 0 })

instance Functor R where
  map f (R g) = R \s -> case g s of
    Left err -> Left err
    Right (Tuple a s') -> Right (Tuple (f a) s')

instance Apply R where
  apply = ap

instance Applicative R where
  pure a = R \s -> Right (Tuple a s)

instance Bind R where
  bind (R g) f = R \s -> case g s of
    Left err -> Left err
    Right (Tuple a s') -> case f a of R h -> h s'

instance Monad R

throwR :: forall a. DecodeError -> R a
throwR err = R \_ -> Left err

byte :: R P.Int
byte = R \s -> case Array.index s.bytes s.pos of
  Nothing -> Left UnexpectedEnd
  Just b -> Right (Tuple b (s { pos = s.pos + 1 }))

-- | One byte that must be what it is, which is how the magic is read.
expect :: P.Int -> DecodeError -> R Unit
expect wanted err = do
  b <- byte
  if b == wanted then pure unit else throwR err

positionR :: R P.Int
positionR = R \s -> Right (Tuple s.pos s)

atEndR :: R P.Boolean
atEndR = R \s -> Right (Tuple (s.pos >= Array.length s.bytes) s)

skipR :: P.Int -> R Unit
skipR n = R \s -> case advance s n of
  Left err -> Left err
  Right next -> Right (Tuple unit (s { pos = next }))

-- | The position `n` bytes on, where the input reaches it.
-- |
-- | **The comparison comes before the addition.** A sum of two positive `Int`s
-- | wraps at 32 bits, so a length a few bytes claimed would pass a test made
-- | after it: the subtraction cannot wrap, and is what the count is compared
-- | against.
advance :: State -> P.Int -> Either DecodeError P.Int
advance s n
  | n < 0 = Left UnexpectedEnd
  | n > Array.length s.bytes - s.pos = Left UnexpectedEnd
  | otherwise = Right (s.pos + n)

-- | LEB128, rejecting a sixth byte, a fifth carrying more than 32 bits, and a
-- | form longer than the shortest that carries the value.
uvarR :: R P.Int
uvarR = go 0 0 0
  where
  go acc shift count = do
    b <- byte
    let chunk = Bits.and b 0x7F
    let more = Bits.and b 0x80 /= 0
    if count == 4 && chunk > 0x0F then throwR VarOverflow
    else if count > 0 && chunk == 0 && not more then throwR VarNotMinimal
    else do
      let acc' = Bits.or acc (Bits.shl chunk shift)
      if not more then pure acc'
      else if count == 4 then throwR VarTooLong
      else go acc' (shift + 7) (count + 1)

-- | A count, an index, a register, an arity, and their kin, which are at most
-- | `0x7FFFFFFF`. A 32-bit value above that comes back negative, which is what
-- | the test reads.
structuralR :: R P.Int
structuralR = do
  n <- uvarR
  if n < 0 then throwR (StructuralOutOfRange n) else pure n

svarR :: R P.Int
svarR = do
  n <- uvarR
  pure (Bits.xor (Bits.zshr n 1) (negate (Bits.and n 1)))

f64R :: R P.Number
f64R = do
  lo <- u32R
  hi <- u32R
  pure (Float.numberOfHalves hi lo)

u32R :: R P.Int
u32R = do
  b0 <- byte
  b1 <- byte
  b2 <- byte
  b3 <- byte
  pure
    ( Bits.or (Bits.or b0 (Bits.shl b1 8))
        (Bits.or (Bits.shl b2 16) (Bits.shl b3 24))
    )

-- | `n` bytes of UTF-8, rejecting what is not well formed: an overlong
-- | sequence, a truncated one, a byte no sequence begins, a code point above
-- | `0x10FFFF`, and a surrogate. Nothing is replaced — text a reader cannot
-- | read is a file it cannot read.
utf8R :: P.Int -> R ScalarString
utf8R n = do
  bytes <- takeR n
  case scalars 0 bytes [] of
    Left err -> throwR err
    Right values -> pure (scalarStringOf values)
  where
  scalars i bytes acc = case Array.index bytes i of
    Nothing -> Right acc
    Just b
      | b < 0x80 -> keep 1 b i bytes acc
      | b < 0xC2 -> Left BadUtf8
      | b < 0xE0 -> sequenceOf 2 (Bits.and b 0x1F) 0x80 i bytes acc
      | b < 0xF0 -> sequenceOf 3 (Bits.and b 0x0F) 0x800 i bytes acc
      | b < 0xF5 -> sequenceOf 4 (Bits.and b 0x07) 0x10000 i bytes acc
      | otherwise -> Left BadUtf8

  sequenceOf width lead least i bytes acc =
    case continuations (i + 1) (width - 1) bytes lead of
      Left err -> Left err
      Right code
        | code < least -> Left BadUtf8
        | otherwise -> keep width code i bytes acc

  -- the one place a code becomes a scalar value, so the surrogates and the
  -- range are refused once and in one way
  keep width code i bytes acc = case scalarValue code of
    Nothing -> Left (NotAScalarValue code)
    Just value -> scalars (i + width) bytes (Array.snoc acc value)

  continuations i remaining bytes acc
    | remaining == 0 = Right acc
    | otherwise = case Array.index bytes i of
        Nothing -> Left BadUtf8
        Just b
          | Bits.and b 0xC0 /= 0x80 -> Left BadUtf8
          | otherwise ->
              continuations (i + 1) (remaining - 1) bytes
                (Bits.or (Bits.shl acc 6) (Bits.and b 0x3F))

-- | A count, then that many of what follows it.
-- |
-- | **The count is checked against the input before anything is reserved for
-- | it.** Every item takes at least one byte, so a count above what is left is a
-- | file that ends inside the vector, and a reader says so rather than reserving
-- | room for a count a few bytes claimed.
vecR :: forall a. R a -> R (P.Array a)
vecR item = do
  n <- structuralR
  left <- remainingR
  if n > left then throwR UnexpectedEnd
  else sequence (Array.replicate n item)

-- | How many bytes are left, which is the bound on every count and length a file
-- | states.
remainingR :: R P.Int
remainingR = R \s -> Right (Tuple (Array.length s.bytes - s.pos) s)

-- | The next `n` bytes, where the input holds them.
takeR :: P.Int -> R Bytes
takeR n = R \s -> case advance s n of
  Left err -> Left err
  Right next -> Right (Tuple (Array.slice s.pos next s.bytes) (s { pos = next }))

derive instance Eq EncodeError
derive instance Generic EncodeError _

instance Show EncodeError where
  show = genericShow

derive instance Eq TagKind
derive instance Generic TagKind _

instance Show TagKind where
  show = genericShow

derive instance Eq TableKind
derive instance Generic TableKind _

instance Show TableKind where
  show = genericShow

derive instance Eq DecodeError
derive instance Generic DecodeError _

instance Show DecodeError where
  show x = genericShow x

derive instance Eq Fault
derive instance Generic Fault _

instance Show Fault where
  show = genericShow
