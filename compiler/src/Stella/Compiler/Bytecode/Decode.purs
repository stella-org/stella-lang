-- | `decode`, from the bytes of a `.dmo` to the module they carry
-- | ([Encoding](../../../../docs/technical-references/05-Backend/02-Encoding.md)).
-- |
-- | **A decoder returns a module, not a file.** It reports what it cannot read
-- | rather than producing a module the encoder did not write, and what it can read
-- | it hands on: a string table in another order, a NaN of another pattern, and a
-- | section above the boundary all reach the same module.
-- |
-- | What it does not check is what a loader and a verifier check. Whether a
-- | qualified name belongs to this module or one of its imports, whether a
-- | register is bound where it is read, and whether a call supplies a declared
-- | arity are not properties of the bytes ([Bytecode](../../../../docs/technical-references/05-Backend/01-Bytecode.md)).
module Stella.Compiler.Bytecode.Decode
  ( decode
  ) where

import Prelude

import Prim as P

import Stella.Compiler.Primitive (PrimOp, opOfCode)
import Stella.Compiler.Bytecode.Bytes (Bytes, DecodeError(..), R, TableKind(..), TagKind(..), byte, expect, f64R, runR, structuralR, svarR, throwR, uvarR, vecR)
import Stella.Compiler.Bytecode.Container (Strings, qnameR, strR, text)
import Stella.Compiler.Bytecode.Container as C
import Stella.Compiler.Bytecode.Format as F
import Stella.Compiler.Bytecode.Validate (validate)
import Stella.Compiler.Bytecode.Instr (CalleeIx(..), ConstIx(..), CtorIx(..), ForeignIx(..), FuncIx(..), GlobalIx(..), HandlerIx(..), Instr(..), Join, JoinName(..), KeyIx(..), Node, OpIx(..), PrimIx(..), Reg(..), Tail(..))
import Stella.Compiler.Bytecode.Instr as B
import Stella.Compiler.Bytecode.Module (CalleeEntry(..), Constant(..), Dmo, GlobalInit(..), Key(..), abiVersion, formatVersion)
import Stella.Compiler.Bytecode.Module as BM
import Stella.Compiler.MiddleEnd.Rep (Rep(..))
import Stella.Compiler.MiddleEnd.IR (ClauseForm(..))
import Stella.Compiler.TypedCore.Domain (scalarString, scalarValue, textOf)
import Stella.Compiler.TypedCore.Name (EffName(..), Ident(..), ModuleName(..), OpName(..), Symbol(..), Tag(..), TyName(..))
import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (traverse_)
import Data.Maybe (Maybe(..))

decode :: Bytes -> Either DecodeError Dmo
decode bytes = do
  dmo <- runR bytes dmoR
  -- the bytes may describe a module no module may be: the walk both directions
  -- read is what says so, and an encoder refuses to write what it refuses here
  case validate dmo of
    Left fault -> Left (Malformed fault)
    Right _ -> Right unit
  pure dmo

dmoR :: R Dmo
dmoR = do
  head <- headerR
  strings <- sectionR 0 F.sectionStrings (vecR (map textOf text))
  let ss = strings.value
  name <- sectionR strings.previous F.sectionModule (map ModuleName (strR ss))
  imports <- sectionR name.previous F.sectionImports (vecR (map ModuleName (strR ss)))
  constants <- sectionR imports.previous F.sectionConstants (vecR (constantR ss))
  keys <- sectionR constants.previous F.sectionKeys (vecR (keyR ss))
  ops <- sectionR keys.previous F.sectionOps (vecR (map OpName (strR ss)))
  ctors <- sectionR ops.previous F.sectionCtors (vecR (ctorR ss))
  effects <- sectionR ctors.previous F.sectionEffects (vecR (effectR ss))
  foreigns <- sectionR effects.previous F.sectionForeigns (vecR (foreignR ss))
  ctorRefs <- sectionR foreigns.previous F.sectionCtorRefs (vecR (qnameR ss Ident))
  foreignRefs <- sectionR ctorRefs.previous F.sectionForeignRefs (vecR (qnameR ss Ident))
  globalRefs <- sectionR foreignRefs.previous F.sectionGlobalRefs (vecR (qnameR ss Ident))
  prims <- sectionR globalRefs.previous F.sectionPrims (vecR primR)
  callees <- sectionR prims.previous F.sectionCallees (vecR (calleeR ss prims.value))
  handlers <- sectionR callees.previous F.sectionHandlers (vecR handlerR)
  functions <- sectionR handlers.previous F.sectionFunctions (vecR (functionR ss))
  globals <- sectionR functions.previous F.sectionGlobals (vecR (globalR ss))
  exports <- sectionR globals.previous F.sectionExports (vecR (qnameR ss Ident))
  trailingR exports.previous
  pure
    { formatVersion: head.formatVersion
    , abiVersion: head.abiVersion
    , name: name.value
    , imports: imports.value
    , constants: constants.value
    , keys: keys.value
    , ops: ops.value
    , ctors: ctors.value
    , effects: effects.value
    , foreigns: foreigns.value
    , ctorRefs: ctorRefs.value
    , foreignRefs: foreignRefs.value
    , globalRefs: globalRefs.value
    , callees: callees.value
    , prims: prims.value
    , handlers: handlers.value
    , functions: functions.value
    , globals: globals.value
    , exports: exports.value
    }

-- | The magic, the version of the format, the flags, and the ABI version the
-- | module was compiled against.
-- |
-- | **A reader rejects a version it does not implement.** An operation's code is
-- | the ABI manifest's to fix, so a version this reader does not hold leaves
-- | every `PRIMS` entry without a meaning.
headerR :: R { formatVersion :: P.Int, abiVersion :: P.String }
headerR = do
  traverse_ (\b -> expect b BadMagic) F.magic
  format <- uvarR
  when (format /= formatVersion) (throwR (UnsupportedFormatVersion format))
  flags <- uvarR
  when (flags /= 0) (throwR (UnknownFlags flags))
  abi <- map textOf text
  when (abi /= abiVersion) (throwR (UnknownAbiVersion abi))
  pure { formatVersion: format, abiVersion: abi }

-- | What the `.dmo` says of its sections.
layout :: C.Layout
layout = { skippableFrom: F.skippableFrom, required: F.requiredSections }

sectionR :: forall a. P.Int -> P.Int -> R a -> R (C.Read a)
sectionR = C.sectionR layout

-- | What stands after the last required section: anything above the boundary, in
-- | ascending order, and nothing else.
trailingR :: P.Int -> R Unit
trailingR previous = void (C.trailingR layout (const (Nothing :: Maybe (R Unit))) previous)

constantR :: Strings -> R Constant
constantR strings = do
  tag <- byte
  if tag == F.constInt then map CInt svarR
  else if tag == F.constNumber then map CNumber f64R
  else if tag == F.constString then do
    i <- structuralR
    case Array.index strings i of
      Nothing -> throwR (IndexOutOfRange StringTable i)
      Just s -> case scalarString s of
        Nothing -> throwR BadUtf8
        Just v -> pure (CString v)
  else if tag == F.constChar then do
    code <- structuralR
    case scalarValue code of
      Nothing -> throwR (NotAScalarValue code)
      Just v -> pure (CChar v)
  else if tag == F.constBoolean then do
    b <- byte
    if b == 0 then pure (CBoolean false)
    else if b == 1 then pure (CBoolean true)
    else throwR (UnknownTag BooleanByte b)
  else throwR (UnknownTag ConstantTag tag)

keyR :: Strings -> R Key
keyR strings = do
  tag <- byte
  if tag == F.keySymbol then map (KSymbol <<< Symbol) (strR strings)
  else if tag == F.keyTag then map (KTag <<< Tag) (strR strings)
  else if tag == F.keyPosition then map KPosition structuralR
  else if tag == F.keyEffect then map KEffect (qnameR strings EffName)
  else throwR (UnknownTag KeyTag tag)

ctorR :: Strings -> R BM.CtorEntry
ctorR strings = do
  name <- qnameR strings Ident
  owner <- qnameR strings TyName
  tag <- structuralR
  arity <- structuralR
  flag <- byte
  isNewtype <-
    if flag == 0 then pure false
    else if flag == 1 then pure true
    else throwR (UnknownTag NewtypeByte flag)
  pure { name, owner, tag, arity, isNewtype }

effectR :: Strings -> R BM.EffectEntry
effectR strings = do
  name <- qnameR strings EffName
  ops <- vecR (map OpName (strR strings))
  pure { name, ops }

foreignR :: Strings -> R BM.ForeignEntry
foreignR strings = do
  name <- qnameR strings Ident
  arity <- structuralR
  pure { name, arity }

primR :: R PrimOp
primR = do
  code <- structuralR
  case opOfCode code of
    Nothing -> throwR (UnknownOperationCode code)
    Just op -> pure op

calleeR :: Strings -> P.Array PrimOp -> R CalleeEntry
calleeR strings prims = do
  tag <- byte
  if tag == F.calleeValue then map CalleeValue (qnameR strings Ident)
  else if tag == F.calleeForeign then map CalleeForeign (qnameR strings Ident)
  else if tag == F.calleeCtor then map CalleeCtor (qnameR strings Ident)
  else if tag == F.calleePrim then do
    i <- structuralR
    case Array.index prims i of
      Nothing -> throwR (IndexOutOfRange PrimTable i)
      Just op -> pure (CalleePrim op)
  else throwR (UnknownTag CalleeTag tag)

handlerR :: R BM.HandlerEntry
handlerR = do
  key <- map KeyIx structuralR
  cells <- vecR (map KeyIx structuralR)
  opClauses <- vecR clauseR
  pure { key, cells, opClauses }

clauseR :: R BM.ClauseEntry
clauseR = do
  op <- map OpIx structuralR
  tag <- byte
  form <-
    if tag == F.formFull then pure ClauseFull
    else if tag == F.formFast then pure ClauseFast
    else throwR (UnknownTag ClauseFormTag tag)
  pure { op, form }

globalR :: Strings -> R BM.GlobalEntry
globalR strings = do
  name <- qnameR strings Ident
  tag <- byte
  init <-
    if tag == F.globalRun then map GRun funcIxR
    else if tag == F.globalFunc then map GFunc funcIxR
    else throwR (UnknownTag GlobalKind tag)
  pure { name, init }

functionR :: Strings -> R B.Function
functionR strings = do
  nparams <- structuralR
  regs <- vecR (repR strings)
  captures <- vecR (repR strings)
  joins <- vecR joinR
  body <- nodeR
  pure { nparams, regs, captures, joins, body }

repR :: Strings -> R Rep
repR strings = do
  tag <- byte
  if tag == F.repInt then pure RepInt
  else if tag == F.repNumber then pure RepNumber
  else if tag == F.repChar then pure RepChar
  else if tag == F.repString then pure RepString
  else if tag == F.repBoolean then pure RepBoolean
  else if tag == F.repClos then pure RepClos
  else if tag == F.repRec then pure RepRec
  else if tag == F.repVariant then pure RepVariant
  else if tag == F.repData then map RepData (qnameR strings TyName)
  else if tag == F.repOpaque then pure RepOpaque
  else if tag == F.repVal then pure RepVal
  else throwR (UnknownTag RepTag tag)

joinR :: R Join
joinR = do
  name <- map JoinName structuralR
  params <- vecR regR
  body <- nodeR
  pure { name, params, body }

-- | Instructions until a `Tail` ends them: an opcode at or above `tailFrom` is a
-- | `Tail`, so a `Node` carries no count and holds exactly one.
nodeR :: R Node
nodeR = go []
  where
  go code = do
    opcode <- byte
    if opcode >= F.tailFrom then do
      t <- tailR opcode
      pure { code, tail: t }
    else do
      i <- instrR opcode
      go (Array.snoc code i)

instrR :: P.Int -> R Instr
instrR opcode
  | opcode == F.opLoadK = LOADK <$> regR <*> constIxR
  | opcode == F.opLoadG = LOADG <$> regR <*> globalIxR
  | opcode == F.opLoadC = LOADC <$> regR <*> ctorIxR
  | opcode == F.opMove = MOVE <$> regR <*> regR
  | opcode == F.opCapt = CAPT <$> regR <*> structuralR
  | opcode == F.opClos = CLOS <$> regR <*> funcIxR <*> vecR regR
  | opcode == F.opClosN = CLOSN <$> regR <*> funcIxR <*> structuralR
  | opcode == F.opSetCap = SETCAP <$> regR <*> structuralR <*> regR
  | opcode == F.opPap = PAP <$> regR <*> calleeIxR <*> vecR regR
  | opcode == F.opCtor = CTOR <$> regR <*> ctorIxR <*> vecR regR
  | opcode == F.opCallK = CALLK <$> regR <*> globalIxR <*> vecR regR
  | opcode == F.opCallU = CALLU <$> regR <*> regR <*> vecR regR
  | opcode == F.opFfi = FFI <$> regR <*> foreignIxR <*> vecR regR
  | opcode == F.opPrim = PRIM <$> regR <*> primIxR <*> vecR regR
  | opcode == F.opField = FIELD <$> regR <*> regR <*> ctorIxR <*> structuralR
  | opcode == F.opRNew = RNEW <$> regR
  | opcode == F.opRExt = REXT <$> regR <*> keyIxR <*> regR <*> regR
  | opcode == F.opRSel = RSEL <$> regR <*> keyIxR <*> regR
  | opcode == F.opRRes = RRES <$> regR <*> keyIxR <*> regR
  | opcode == F.opRUpd = RUPD <$> regR <*> keyIxR <*> regR <*> regR
  | opcode == F.opRMrg = RMRG <$> regR <*> regR <*> regR
  | opcode == F.opVInj = VINJ <$> regR <*> keyIxR <*> regR
  | opcode == F.opVPay = VPAY <$> regR <*> keyIxR <*> regR
  | opcode == F.opVAbs = VABS <$> regR <*> regR
  | opcode == F.opPerf = PERF <$> regR <*> keyIxR <*> opIxR <*> regR
  | opcode == F.opHndl =
      HNDL <$> regR <*> handlerIxR <*> regR <*> regR <*> vecR regR <*> vecR regR
  | opcode == F.opCGet = CGET <$> regR <*> keyIxR
  | opcode == F.opCSet = CSET <$> regR <*> keyIxR <*> regR
  | otherwise = throwR (UnknownTag InstrOpcode opcode)

tailR :: P.Int -> R Tail
tailR opcode
  | opcode == F.tailRet = RET <$> regR
  | opcode == F.tailTailK = TAILK <$> globalIxR <*> vecR regR
  | opcode == F.tailTailU = TAILU <$> regR <*> vecR regR
  | opcode == F.tailTailFfi = TAILFFI <$> foreignIxR <*> vecR regR
  | opcode == F.tailJmp = JMP <$> map JoinName structuralR <*> vecR regR
  | opcode == F.tailBrIf = BRIF <$> regR <*> nodeR <*> nodeR
  | opcode == F.tailBrC = BRC <$> regR <*> vecR ctorCaseR <*> optionalR
  | opcode == F.tailBrL = BRL <$> regR <*> vecR litCaseR <*> nodeR
  | opcode == F.tailBrK = BRK <$> regR <*> vecR keyCaseR <*> optionalR
  | opcode == F.tailTailHndl =
      TAILHNDL <$> handlerIxR <*> regR <*> regR <*> vecR regR <*> vecR regR
  | otherwise = throwR (UnknownTag TailOpcode opcode)

ctorCaseR :: R B.CtorCase
ctorCaseR = do
  ctor <- ctorIxR
  body <- nodeR
  pure { ctor, body }

litCaseR :: R B.LitCase
litCaseR = do
  lit <- constIxR
  body <- nodeR
  pure { lit, body }

keyCaseR :: R B.KeyCase
keyCaseR = do
  key <- keyIxR
  body <- nodeR
  pure { key, body }

optionalR :: R (Maybe Node)
optionalR = do
  tag <- byte
  if tag == F.noDefault then pure Nothing
  else if tag == F.someDefault then map Just nodeR
  else throwR (UnknownTag DefaultTag tag)

regR :: R Reg
regR = map Reg structuralR

constIxR :: R ConstIx
constIxR = map ConstIx structuralR

keyIxR :: R KeyIx
keyIxR = map KeyIx structuralR

opIxR :: R OpIx
opIxR = map OpIx structuralR

ctorIxR :: R CtorIx
ctorIxR = map CtorIx structuralR

globalIxR :: R GlobalIx
globalIxR = map GlobalIx structuralR

foreignIxR :: R ForeignIx
foreignIxR = map ForeignIx structuralR

calleeIxR :: R CalleeIx
calleeIxR = map CalleeIx structuralR

primIxR :: R PrimIx
primIxR = map PrimIx structuralR

funcIxR :: R FuncIx
funcIxR = map FuncIx structuralR

handlerIxR :: R HandlerIx
handlerIxR = map HandlerIx structuralR

