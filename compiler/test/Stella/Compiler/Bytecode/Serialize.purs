-- | `encode` and `decode`, over the bytes of a `.dmo`.
-- |
-- | **The round trip is the assertion.** A module written and read again is the
-- | module it was, which is what an encoder and a decoder that each carry their
-- | own operand order would fail; the two slices and the effect fixtures carry
-- | every form a lowering produces between them.
-- |
-- | The cases after it are the ones the format fixes in its own right: the bytes
-- | of the header, that one module has one encoding, that a section above the
-- | boundary is passed over, and what a reader refuses.
module Test.Stella.Compiler.Bytecode.Serialize (spec) where

import Prelude

import Prim as P

import Stella.Compiler.Bytecode (Bytes, Constant(..), DecodeError(..), Dmo, EncodeError(..), Fault(..), Function, Instr(..), JoinName(..), Key(..), Node, Reg(..), Tail(..), abiVersion, decode, encode, formatVersion, lower, validate)
import Stella.Compiler.Bytecode.Bytes (byte, runR, skipR, structuralR, svar, svarR, utf8, utf8R, uvar, uvarR, vecR)
import Stella.Compiler.Interface (noImports)
import Stella.Compiler.MiddleEnd (Rep(..), translate)
import Stella.Compiler.TypedCore (Module, ModuleName(..), declare, declareAnnotated, primSignature, scalarString, scalarValue, textOf)
import Data.Array as Array
import Data.Char as Char
import Data.Either (Either(..), isLeft)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String.CodeUnits as CodeUnits
import Test.Stella.Compiler.Fixtures.Effects (effectsModule)
import Test.Stella.Compiler.Fixtures.Programs as Programs
import Test.Stella.Compiler.TypedCore.HandlerSlice (handlerSlice)
import Test.Stella.Compiler.TypedCore.VerticalSlice (intModule, verticalSlice)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

-- | A NaN, which is the one value unequal to itself.
notANumber :: P.Number
notANumber = 0.0 / 0.0

-- | A slice, carried through checking, translation, and lowering to the module
-- | object these cases encode.
loweredOf :: Module P.Int -> Either P.String Dmo
loweredOf = loweredAgainst intModule

-- | The same, against the `Base.Int` given.
loweredAgainst :: Module P.Int -> Module P.Int -> Either P.String Dmo
loweredAgainst base m = case declare primSignature base of
  Left _ -> Left "Base.Int did not declare"
  Right s1 -> case declareAnnotated s1 m of
    Left _ -> Left "the slice did not declare"
    Right declared -> case translate noImports m declared of
      Left err -> Left (show err)
      Right mid -> case lower mid of
        Left err -> Left (show err)
        Right out -> Right out.dmo

-- | A module of no declarations, which is what the cases about the container
-- | itself stand on.
bare :: Dmo
bare =
  { formatVersion
  , abiVersion
  , name: ModuleName "Main"
  , imports: []
  , constants: []
  , keys: []
  , ops: []
  , ctors: []
  , effects: []
  , foreigns: []
  , ctorRefs: []
  , foreignRefs: []
  , globalRefs: []
  , callees: []
  , prims: []
  , handlers: []
  , regions: []
  , functions: []
  , globals: []
  , exports: []
  }

withConstants :: P.Array Constant -> Dmo
withConstants constants = bare { constants = constants }

-- | One constant of every kind, both zeros among them, and the ends of the range
-- | an `Int` holds.
everyConstant :: Maybe Dmo
everyConstant = do
  smile <- scalarValue 0x1F600
  text <- scalarString "hi 😀"
  pure
    ( withConstants
        [ CInt 0
        , CInt (-1)
        , CInt 2147483647
        , CInt (-2147483648)
        , CNumber 1.5
        , CNumber 0.0
        , CNumber (-0.0)
        , CString text
        , CChar smile
        , CBoolean true
        , CBoolean false
        ]
    )

-- | A module written and read again.
roundTrip :: Dmo -> Either P.String Dmo
roundTrip dmo = case encode dmo of
  Left err -> Left (show (err :: EncodeError))
  Right bytes -> case decode bytes of
    Left err -> Left (show err)
    Right back -> Right back

bytesOf :: Dmo -> Bytes
bytesOf dmo = case encode dmo of
  Left _ -> []
  Right bytes -> bytes

-- | The bytes with one of them replaced, which is how a header a reader must
-- | refuse is written.
mutated :: P.Int -> P.Int -> Bytes -> Bytes
mutated at value bytes = fromMaybe bytes (Array.updateAt at value bytes)

-- | A section of two bytes at an id of this reader's choosing, appended where
-- | the ids still ascend.
appended :: P.Int -> Dmo -> Bytes
appended id dmo = bytesOf dmo <> [ id, 0x02, 0xAA, 0xBB ]

spec :: Spec Unit
spec = describe "Stella.Compiler.Bytecode.Serialize" do

  describe "the round trip" do
    it "carries the vertical slice through the bytes unchanged" do
      case loweredOf verticalSlice of
        Left err -> fail err
        Right dmo -> roundTrip dmo `shouldEqual` Right dmo

    it "carries the handler slice, performs and regions and cells and all" do
      -- `PERF`, `HNDL`, `TAILHNDL`, `RGN`, `TAILRGN`, `CGET`, and `CSET` are
      -- here and nowhere in the vertical slice
      case loweredOf handlerSlice of
        Left err -> fail err
        Right dmo -> roundTrip dmo `shouldEqual` Right dmo

    it "carries the effect fixtures, a HNDL whose value is consumed among them" do
      case loweredAgainst Programs.intModule effectsModule of
        Left err -> fail err
        Right dmo -> roundTrip dmo `shouldEqual` Right dmo

    it "carries a constant of every kind, the two zeros apart" do
      case everyConstant of
        Nothing -> fail "the fixture is not a scalar value"
        Just dmo -> roundTrip dmo `shouldEqual` Right dmo

    it "keeps the sign of a zero, which literal identity reads" do
      roundTrip (withConstants [ CNumber (-0.0) ])
        `shouldEqual` Right (withConstants [ CNumber (-0.0) ])
      (roundTrip (withConstants [ CNumber (-0.0) ]) == Right (withConstants [ CNumber 0.0 ]))
        `shouldEqual` false

    it "writes one NaN and reads it as the one literal it is" do
      -- every NaN is one literal (D37), so a payload is not carried and the
      -- comparison is the identity Core decides
      roundTrip (withConstants [ CNumber notANumber ])
        `shouldEqual` Right (withConstants [ CNumber notANumber ])

    it "carries an astral character in a name" do
      roundTrip (bare { name = ModuleName "Main.😀" })
        `shouldEqual` Right (bare { name = ModuleName "Main.😀" })

  describe "the container" do
    it "begins with the magic, the format version, the flags, and the ABI length" do
      -- `stella-base-0.1` is fifteen bytes, which the length says before them
      Array.take 7 (bytesOf bare) `shouldEqual` [ 0x44, 0x4D, 0x4F, 0x00, 0x00, 0x00, 0x0F ]

    it "leaves one module one encoding" do
      case loweredOf handlerSlice of
        Left err -> fail err
        Right dmo -> case decode (bytesOf dmo) of
          Left err -> fail (show err)
          Right back -> encode back `shouldEqual` encode dmo

    it "passes over a section above the boundary" do
      -- `DEBUG` is the one a reader may discard, and an id it does not know at
      -- all is passed over on the same rule
      decode (appended 0x7F bare) `shouldEqual` Right bare
      decode (appended 0x71 bare) `shouldEqual` Right bare

  describe "what a reader refuses" do
    it "other magic" do
      decode [ 0x00, 0x00, 0x00, 0x00 ] `shouldEqual` Left BadMagic

    it "a format version it does not implement" do
      decode (mutated 4 0x01 (bytesOf bare)) `shouldEqual` Left (UnsupportedFormatVersion 1)

    it "a flag it does not know" do
      decode (mutated 5 0x01 (bytesOf bare)) `shouldEqual` Left (UnknownFlags 1)

    it "an ABI version it does not hold" do
      decode (mutated 7 0x58 (bytesOf bare))
        `shouldEqual` Left (UnknownAbiVersion "Xtella-base-0.1")

    it "an unknown section below the boundary" do
      decode (appended 0x14 bare) `shouldEqual` Left (UnknownSection 0x14)

    it "a section twice, the ids ascending strictly" do
      decode (appended 0x13 bare) `shouldEqual` Left (SectionOutOfOrder 0x13 0x13)

    it "a file that ends inside a form" do
      isLeft (decode (Array.take 9 (bytesOf bare))) `shouldEqual` true

    it "a section above the boundary whose length runs past the file" do
      -- an id a reader passes over is still read by its length, and a length the
      -- file does not hold is a file that ends inside the section
      decode (bytesOf bare <> [ 0x7F ] <> uvar 2147483647)
        `shouldEqual` Left UnexpectedEnd

    it "a truncated module, whatever it truncates" do
      case loweredOf handlerSlice of
        Left err -> fail err
        Right dmo -> isLeft (decode (Array.dropEnd 1 (bytesOf dmo))) `shouldEqual` true

  describe "what an encoder refuses" do
    it "a structural value below zero, which reads back as no value at all" do
      -- a `uvar` carries no sign, so a negative would be written as its 32-bit
      -- pattern and refused on the way back in
      encode (bare { keys = [ KPosition (-1) ] })
        `shouldEqual` Left (Unwritable (NegativeValue (-1)))

    it "a register the function's own file does not hold" do
      encode (withFunction (returning { regs = [] }))
        `shouldEqual` Left (Unwritable (RegisterOutOfFile 0))

    it "a capture the function does not take" do
      -- a `CAPT` reads a capture of the activation it stands in, so the
      -- function's own list is the bound. A decoder refuses the same file: the
      -- walk is one and both directions read it
      encode (withFunction (withBody { code: [ CAPT (Reg 0) 0 ], tail: RET (Reg 0) }))
        `shouldEqual` Left (Unwritable (CaptureOutOfRange 0))
      validate (withFunction (withBody { code: [ CAPT (Reg 0) 0 ], tail: RET (Reg 0) }))
        `shouldEqual` Left (CaptureOutOfRange 0)

    it "a jump naming a join point the function does not declare" do
      encode (withFunction (withBody { code: [], tail: JMP (JoinName 0) [] }))
        `shouldEqual` Left (Unwritable (JoinNotDeclared 0))

    it "a module of another format or another ABI version" do
      -- what a byte means is this format's, and what an operation's code means is
      -- this ABI version's
      encode (bare { formatVersion = 1 }) `shouldEqual` Left (NotThisFormatVersion 1)
      encode (bare { abiVersion = "stella-base-0.2" })
        `shouldEqual` Left (NotThisAbiVersion "stella-base-0.2")

    it "a name carrying an unpaired surrogate" do
      -- a `String` and a `Char` literal carry the invariant in their types; a
      -- name is what is left, and the lexer that would settle its spelling does
      -- not exist yet
      case loneSurrogate of
        Nothing -> fail "a code unit is the only way to write one"
        Just text ->
          encode (bare { name = ModuleName text }) `shouldEqual` Left (NotScalarText text)

  describe "the varints" do
    it "reads back what it writes, at either end of the range" do
      runR (uvar 0) uvarR `shouldEqual` Right 0
      runR (uvar 0x7F) uvarR `shouldEqual` Right 0x7F
      runR (uvar 0x80) uvarR `shouldEqual` Right 0x80
      runR (uvar 2147483647) uvarR `shouldEqual` Right 2147483647
      runR (svar 0) svarR `shouldEqual` Right 0
      runR (svar (-1)) svarR `shouldEqual` Right (-1)
      runR (svar 2147483647) svarR `shouldEqual` Right 2147483647
      runR (svar (-2147483648)) svarR `shouldEqual` Right (-2147483648)

    it "refuses a form longer than the shortest that carries the value" do
      -- an overlong varint is otherwise a second spelling of a value in every
      -- position a varint stands
      runR [ 0x80, 0x00 ] uvarR `shouldEqual` Left VarNotMinimal

    it "refuses more than five bytes, and a fifth carrying more than 32 bits" do
      runR [ 0x80, 0x80, 0x80, 0x80, 0x80, 0x01 ] uvarR `shouldEqual` Left VarTooLong
      runR [ 0x80, 0x80, 0x80, 0x80, 0x10 ] uvarR `shouldEqual` Left VarOverflow

    it "refuses a count above what is left to read" do
      -- a few bytes claiming a count of every register a machine could have must
      -- not reserve room for it: every item takes a byte, so the input is the
      -- bound
      runR (uvar 5 <> [ 0x01, 0x02 ]) (vecR byte) `shouldEqual` Left UnexpectedEnd
      runR (uvar 2147483647) (vecR byte) `shouldEqual` Left UnexpectedEnd
      runR (uvar 2 <> [ 0x01, 0x02 ]) (vecR byte) `shouldEqual` Right [ 0x01, 0x02 ]

    it "reads text of any length, in a stack of one frame" do
      let text = Array.fold (Array.replicate 30_000 "a\x3b1\x1F600")
      case utf8 text of
        Left err -> fail (show err)
        Right bytes -> map textOf (runR bytes (utf8R (Array.length bytes))) `shouldEqual` Right text

    it "refuses a length of text above what is left to read" do
      isLeft (runR [ 0x61 ] (utf8R 5)) `shouldEqual` true

    it "refuses a length that would wrap the position it is added to" do
      -- the comparison comes before the addition: a sum of two positive `Int`s
      -- wraps at 32 bits, and a length a few bytes claimed would pass a test made
      -- after it
      isLeft (runR (uvar 2147483647) (structuralR >>= utf8R)) `shouldEqual` true
      isLeft (runR (uvar 2147483647) (structuralR >>= skipR)) `shouldEqual` true

    it "refuses a structural value above 0x7FFFFFFF" do
      -- a count, an index, a register, and their kin are what a consumer counts
      -- with; the carrier is wider only for a zigzag
      runR (uvar (-1)) structuralR `shouldEqual` Left (StructuralOutOfRange (-1))
      runR (uvar 2147483647) structuralR `shouldEqual` Right 2147483647

-- | Text holding one unpaired surrogate, which a host's string type admits and a
-- | Stella `String` does not. A code unit is the only way to write one: a scalar
-- | value cannot be a surrogate.
loneSurrogate :: Maybe P.String
loneSurrogate = map CodeUnits.singleton (Char.fromCharCode 0xD800)

-- | A module of one function, which is what the cases about a function's own
-- | scope stand on.
withFunction :: Function -> Dmo
withFunction f = bare { functions = [ f ] }

-- | A function that returns the one register it holds, and the shape every case
-- | below varies by one field.
returning :: Function
returning =
  { nparams: 0
  , regs: [ RepVal ]
  , captures: []
  , joins: []
  , body: { code: [], tail: RET (Reg 0) }
  }

-- | The same function with another body.
withBody :: Node -> Function
withBody body = returning { body = body }
