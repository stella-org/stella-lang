-- | The numbers of the `.dmo` encoding: the magic, the id of every section, the
-- | tag of every form, and the opcode of every instruction
-- | ([Encoding](../../../../docs/technical-references/05-Backend/02-Encoding.md)).
-- |
-- | **They are written once and read by both directions.** An encoder and a
-- | decoder that each carried their own copy could disagree over one byte and
-- | nothing would say so; the round trip is what keeps the operand order of the
-- | two in step, and this module is what keeps the numbers in step.
module Stella.Compiler.Bytecode.Format
  ( magic
  , sectionStrings
  , sectionModule
  , sectionImports
  , sectionConstants
  , sectionKeys
  , sectionOps
  , sectionCtors
  , sectionEffects
  , sectionForeigns
  , sectionCtorRefs
  , sectionForeignRefs
  , sectionGlobalRefs
  , sectionPrims
  , sectionCallees
  , sectionHandlers
  , sectionRegions
  , sectionFunctions
  , sectionGlobals
  , sectionExports
  , sectionDebug
  , skippableFrom
  , requiredSections
  , constInt
  , constNumber
  , constString
  , constChar
  , constBoolean
  , keySymbol
  , keyTag
  , keyPosition
  , keyEffect
  , calleeValue
  , calleeForeign
  , calleeCtor
  , calleePrim
  , globalRun
  , globalFunc
  , formFull
  , formFast
  , repInt
  , repNumber
  , repChar
  , repString
  , repBoolean
  , repClos
  , repRec
  , repVariant
  , repData
  , repOpaque
  , repVal
  , opLoadK
  , opLoadG
  , opLoadC
  , opMove
  , opCapt
  , opClos
  , opClosN
  , opSetCap
  , opPap
  , opCtor
  , opCallK
  , opCallU
  , opFfi
  , opPrim
  , opField
  , opRNew
  , opRExt
  , opRSel
  , opRRes
  , opRUpd
  , opRMrg
  , opVInj
  , opVPay
  , opVAbs
  , opPerf
  , opHndl
  , opCGet
  , opCSet
  , opRgn
  , tailFrom
  , tailRet
  , tailTailK
  , tailTailU
  , tailTailFfi
  , tailJmp
  , tailBrIf
  , tailBrC
  , tailBrL
  , tailBrK
  , tailTailHndl
  , tailTailRgn
  , noDefault
  , someDefault
  ) where

import Prim as P

-- | `"DMO\0"`, the four bytes a `.dmo` begins with.
magic :: P.Array P.Int
magic = [ 0x44, 0x4D, 0x4F, 0x00 ]

-- Sections ---------------------------------------------------------------------

-- | The ids ascend strictly through a file, so this order is the order a decoder
-- | reads them and the order in which one table is resolved before another uses
-- | it: `STRINGS` first, `OPS` before `EFFECTS` and `HANDLERS`, `PRIMS` before
-- | `CALLEES`.
sectionStrings :: P.Int
sectionStrings = 0x01

sectionModule :: P.Int
sectionModule = 0x02

sectionImports :: P.Int
sectionImports = 0x03

sectionConstants :: P.Int
sectionConstants = 0x04

sectionKeys :: P.Int
sectionKeys = 0x05

sectionOps :: P.Int
sectionOps = 0x06

sectionCtors :: P.Int
sectionCtors = 0x07

sectionEffects :: P.Int
sectionEffects = 0x08

sectionForeigns :: P.Int
sectionForeigns = 0x09

sectionCtorRefs :: P.Int
sectionCtorRefs = 0x0A

sectionForeignRefs :: P.Int
sectionForeignRefs = 0x0B

sectionGlobalRefs :: P.Int
sectionGlobalRefs = 0x0C

sectionPrims :: P.Int
sectionPrims = 0x0D

sectionCallees :: P.Int
sectionCallees = 0x0E

sectionHandlers :: P.Int
sectionHandlers = 0x0F

sectionRegions :: P.Int
sectionRegions = 0x10

sectionFunctions :: P.Int
sectionFunctions = 0x11

sectionGlobals :: P.Int
sectionGlobals = 0x12

sectionExports :: P.Int
sectionExports = 0x13

sectionDebug :: P.Int
sectionDebug = 0x7F

-- | **An id at or above this carries no meaning and a reader may skip one it
-- | does not know**; an id below it bears on what a module computes, so a reader
-- | that does not know it rejects the file rather than running the module
-- | without what it says.
skippableFrom :: P.Int
skippableFrom = 0x70

-- | The sections a file holds, empty or not, in the order it holds them.
requiredSections :: P.Array P.Int
requiredSections =
  [ sectionStrings
  , sectionModule
  , sectionImports
  , sectionConstants
  , sectionKeys
  , sectionOps
  , sectionCtors
  , sectionEffects
  , sectionForeigns
  , sectionCtorRefs
  , sectionForeignRefs
  , sectionGlobalRefs
  , sectionPrims
  , sectionCallees
  , sectionHandlers
  , sectionRegions
  , sectionFunctions
  , sectionGlobals
  , sectionExports
  ]

-- Tags -------------------------------------------------------------------------

constInt :: P.Int
constInt = 0x01

constNumber :: P.Int
constNumber = 0x02

constString :: P.Int
constString = 0x03

constChar :: P.Int
constChar = 0x04

constBoolean :: P.Int
constBoolean = 0x05

keySymbol :: P.Int
keySymbol = 0x01

keyTag :: P.Int
keyTag = 0x02

keyPosition :: P.Int
keyPosition = 0x03

keyEffect :: P.Int
keyEffect = 0x04

calleeValue :: P.Int
calleeValue = 0x01

calleeForeign :: P.Int
calleeForeign = 0x02

calleeCtor :: P.Int
calleeCtor = 0x03

-- | An operation, by its index into `PRIMS` rather than by its code: a partial
-- | application of an operation and the instruction that saturates it then
-- | cannot name two different operations.
calleePrim :: P.Int
calleePrim = 0x04

globalRun :: P.Int
globalRun = 0x01

globalFunc :: P.Int
globalFunc = 0x02

formFull :: P.Int
formFull = 0x00

formFast :: P.Int
formFast = 0x01

repInt :: P.Int
repInt = 0x01

repNumber :: P.Int
repNumber = 0x02

repChar :: P.Int
repChar = 0x03

repString :: P.Int
repString = 0x04

repBoolean :: P.Int
repBoolean = 0x05

repClos :: P.Int
repClos = 0x06

repRec :: P.Int
repRec = 0x07

repVariant :: P.Int
repVariant = 0x08

repData :: P.Int
repData = 0x09

repOpaque :: P.Int
repOpaque = 0x0A

repVal :: P.Int
repVal = 0x0B

-- | `0x00` where a dispatch has no default and `0x01` where it has one.
noDefault :: P.Int
noDefault = 0x00

someDefault :: P.Int
someDefault = 0x01

-- Opcodes ------------------------------------------------------------------------

-- | An opcode below `tailFrom` is an instruction and one at or above it is a
-- | `Tail`, so a `Node` is read until a `Tail` ends it and carries no count.
tailFrom :: P.Int
tailFrom = 0x80

opLoadK :: P.Int
opLoadK = 0x01

opLoadG :: P.Int
opLoadG = 0x02

opLoadC :: P.Int
opLoadC = 0x03

opMove :: P.Int
opMove = 0x04

opCapt :: P.Int
opCapt = 0x05

opClos :: P.Int
opClos = 0x06

opClosN :: P.Int
opClosN = 0x07

opSetCap :: P.Int
opSetCap = 0x08

opPap :: P.Int
opPap = 0x09

opCtor :: P.Int
opCtor = 0x0A

opCallK :: P.Int
opCallK = 0x0B

opCallU :: P.Int
opCallU = 0x0C

opFfi :: P.Int
opFfi = 0x0D

opPrim :: P.Int
opPrim = 0x0E

opField :: P.Int
opField = 0x10

opRNew :: P.Int
opRNew = 0x11

opRExt :: P.Int
opRExt = 0x12

opRSel :: P.Int
opRSel = 0x13

opRRes :: P.Int
opRRes = 0x14

opRUpd :: P.Int
opRUpd = 0x15

opRMrg :: P.Int
opRMrg = 0x16

opVInj :: P.Int
opVInj = 0x17

opVPay :: P.Int
opVPay = 0x18

opVAbs :: P.Int
opVAbs = 0x19

opPerf :: P.Int
opPerf = 0x20

opHndl :: P.Int
opHndl = 0x21

opCGet :: P.Int
opCGet = 0x22

opCSet :: P.Int
opCSet = 0x23

opRgn :: P.Int
opRgn = 0x24

tailRet :: P.Int
tailRet = 0x80

tailTailK :: P.Int
tailTailK = 0x81

tailTailU :: P.Int
tailTailU = 0x82

tailTailFfi :: P.Int
tailTailFfi = 0x83

tailJmp :: P.Int
tailJmp = 0x84

tailBrIf :: P.Int
tailBrIf = 0x88

tailBrC :: P.Int
tailBrC = 0x89

tailBrL :: P.Int
tailBrL = 0x8A

tailBrK :: P.Int
tailBrK = 0x8B

tailTailHndl :: P.Int
tailTailHndl = 0x8C

tailTailRgn :: P.Int
tailTailRgn = 0x8D
