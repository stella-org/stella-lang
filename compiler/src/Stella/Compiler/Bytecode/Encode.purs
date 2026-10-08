-- | `encode`, from a `.dmo` to its bytes
-- | ([Encoding](../../../../docs/technical-references/05-Backend/02-Encoding.md)).
-- |
-- | **The encoding is canonical**: every varint is minimal, every table is
-- | written in the order the module holds it, every NaN is the one quiet NaN, and
-- | the string table is in order of first use with no string twice. Two encoders
-- | handed one module write one file, and a build may cache it by its bytes.
-- |
-- | The string table is what makes this a fold rather than a walk: a section is
-- | written first and the strings it interned are written before it, the
-- | sections being what decides the order of first use.
module Stella.Compiler.Bytecode.Encode
  ( encode
  ) where

import Prelude

import Prim as P

import Stella.Compiler.Primitive (PrimOp, codeOfOp)
import Stella.Compiler.Bytecode.Bytes (Bytes, EncodeError(..), f64, svar, u8, utf8, uvar)
import Stella.Compiler.Bytecode.Container (E, qname, runE, section, str, strings, throwE, vec, vecOf)
import Stella.Compiler.Bytecode.Format as F
import Stella.Compiler.Bytecode.Validate (validate)
import Stella.Compiler.Bytecode.Instr (CalleeIx(..), ConstIx(..), CtorIx(..), ForeignIx(..), FuncIx(..), GlobalIx(..), HandlerIx(..), Instr(..), Join, JoinName(..), KeyIx(..), Node, OpIx(..), PrimIx(..), Reg(..), RegionIx(..), Tail(..))
import Stella.Compiler.Bytecode.Instr as B
import Stella.Compiler.Bytecode.Module (CalleeEntry(..), Constant(..), Dmo, GlobalInit(..), Key(..), abiVersion, formatVersion)
import Stella.Compiler.Bytecode.Module as BM
import Stella.Compiler.MiddleEnd.Rep (Rep(..))
import Stella.Compiler.MiddleEnd.IR (ClauseForm(..))
import Stella.Compiler.TypedCore.Domain (codePointOf, textOf)
import Stella.Compiler.TypedCore.Name (EffName(..), Ident(..), ModuleName(..), OpName(..), Symbol(..), Tag(..), TyName(..))
import Data.Array as Array
import Data.Either (Either(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))

-- | **What this writes, a decoder returns.** A module claiming another format or
-- | another ABI version cannot be written faithfully — what a byte means is this
-- | format's and what an operation's code means is that version's — and a module
-- | no reader would read back is refused rather than written, by the walk both
-- | directions read ([Validate](Validate.purs)).
encode :: Dmo -> Either EncodeError Bytes
encode dmo = do
  when (dmo.formatVersion /= formatVersion)
    (Left (NotThisFormatVersion dmo.formatVersion))
  when (dmo.abiVersion /= abiVersion)
    (Left (NotThisAbiVersion dmo.abiVersion))
  case validate dmo of
    Left fault -> Left (Unwritable fault)
    Right _ -> Right unit
  Tuple sections table <- runE { indices: Map.empty, strings: [] } (body dmo)
  head <- header dmo
  stringTable <- strings table.strings
  pure (head <> section F.sectionStrings stringTable <> sections)

header :: Dmo -> Either EncodeError Bytes
header dmo = do
  abi <- utf8 dmo.abiVersion
  pure
    ( F.magic
        <> uvar dmo.formatVersion
        <> uvar 0
        <> uvar (Array.length abi)
        <> abi
    )

-- | Every section but `STRINGS`, in the order their ids ascend. That order is
-- | what decides which string is reached first, so it is the canonical order and
-- | not a convenience.
body :: Dmo -> E Bytes
body dmo = do
  moduleName <- str (case dmo.name of ModuleName m -> m)
  imports <- vec (\(ModuleName m) -> str m) dmo.imports
  constants <- vec constant dmo.constants
  keys <- vec key dmo.keys
  ops <- vec (\(OpName o) -> str o) dmo.ops
  ctors <- vec ctor dmo.ctors
  effects <- vec effect dmo.effects
  foreigns <- vec foreignEntry dmo.foreigns
  ctorRefs <- vec (qname identOf) dmo.ctorRefs
  foreignRefs <- vec (qname identOf) dmo.foreignRefs
  globalRefs <- vec (qname identOf) dmo.globalRefs
  callees <- vec (callee dmo.prims) dmo.callees
  functions <- vec function dmo.functions
  globals <- vec global dmo.globals
  exports <- vec (qname identOf) dmo.exports
  pure
    ( section F.sectionModule moduleName
        <> section F.sectionImports imports
        <> section F.sectionConstants constants
        <> section F.sectionKeys keys
        <> section F.sectionOps ops
        <> section F.sectionCtors ctors
        <> section F.sectionEffects effects
        <> section F.sectionForeigns foreigns
        <> section F.sectionCtorRefs ctorRefs
        <> section F.sectionForeignRefs foreignRefs
        <> section F.sectionGlobalRefs globalRefs
        <> section F.sectionPrims (vecOf (uvar <<< codeOfOp) dmo.prims)
        <> section F.sectionCallees callees
        <> section F.sectionHandlers (vecOf handler dmo.handlers)
        <> section F.sectionRegions (vecOf region dmo.regions)
        <> section F.sectionFunctions functions
        <> section F.sectionGlobals globals
        <> section F.sectionExports exports
    )

identOf :: Ident -> P.String
identOf (Ident name) = name

constant :: Constant -> E Bytes
constant = case _ of
  CInt n -> pure (u8 F.constInt <> svar n)
  CNumber x -> pure (u8 F.constNumber <> f64 x)
  CString s -> do
    i <- str (textOf s)
    pure (u8 F.constString <> i)
  CChar c -> pure (u8 F.constChar <> uvar (codePointOf c))
  CBoolean b -> pure (u8 F.constBoolean <> u8 (if b then 1 else 0))

key :: Key -> E Bytes
key = case _ of
  KSymbol (Symbol s) -> do
    i <- str s
    pure (u8 F.keySymbol <> i)
  KTag (Tag t) -> do
    i <- str t
    pure (u8 F.keyTag <> i)
  KPosition n -> pure (u8 F.keyPosition <> uvar n)
  KEffect name -> do
    written <- qname (\(EffName e) -> e) name
    pure (u8 F.keyEffect <> written)

ctor :: BM.CtorEntry -> E Bytes
ctor entry = do
  name <- qname identOf entry.name
  owner <- qname (\(TyName t) -> t) entry.owner
  pure
    ( name
        <> owner
        <> uvar entry.tag
        <> uvar entry.arity
        <> u8 (if entry.isNewtype then 1 else 0)
    )

-- | An effect's operations are string indices rather than indices into `OPS`:
-- | an effect may declare an operation no code of this module names, and adding
-- | one to `OPS` would renumber the indices its instructions already carry.
effect :: BM.EffectEntry -> E Bytes
effect entry = do
  name <- qname (\(EffName e) -> e) entry.name
  ops <- vec (\(OpName o) -> str o) entry.ops
  pure (name <> ops)

foreignEntry :: BM.ForeignEntry -> E Bytes
foreignEntry entry = do
  name <- qname identOf entry.name
  pure (name <> uvar entry.arity)

-- | A callee, an operation among them by its index into `PRIMS`: a partial
-- | application of an operation and the instruction that saturates it then
-- | cannot name two different operations.
callee :: P.Array PrimOp -> CalleeEntry -> E Bytes
callee prims = case _ of
  CalleeValue name -> tagged F.calleeValue (qname identOf name)
  CalleeForeign name -> tagged F.calleeForeign (qname identOf name)
  CalleeCtor name -> tagged F.calleeCtor (qname identOf name)
  CalleePrim op -> case Array.elemIndex op prims of
    Nothing -> throwE (OperationNotInPrims op)
    Just i -> pure (u8 F.calleePrim <> uvar i)
  where
  tagged tag written = do
    w <- written
    pure (u8 tag <> w)

region :: BM.RegionEntry -> Bytes
region entry = vecOf keyIx entry.cells

handler :: BM.HandlerEntry -> Bytes
handler entry =
  keyIx entry.key
    <> vecOf clause entry.opClauses
  where
  clause c = opIx c.op <> u8 (form c.form)

  form = case _ of
    ClauseFull -> F.formFull
    ClauseFast -> F.formFast

global :: BM.GlobalEntry -> E Bytes
global entry = do
  name <- qname identOf entry.name
  pure
    ( name <> case entry.init of
        GRun f -> u8 F.globalRun <> funcIx f
        GFunc f -> u8 F.globalFunc <> funcIx f
    )

function :: B.Function -> E Bytes
function f = do
  regs <- vec rep f.regs
  captures <- vec rep f.captures
  pure
    ( uvar f.nparams
        <> regs
        <> captures
        <> vecOf joinPoint f.joins
        <> node f.body
    )

rep :: Rep -> E Bytes
rep = case _ of
  RepInt -> pure (u8 F.repInt)
  RepNumber -> pure (u8 F.repNumber)
  RepChar -> pure (u8 F.repChar)
  RepString -> pure (u8 F.repString)
  RepBoolean -> pure (u8 F.repBoolean)
  RepClos -> pure (u8 F.repClos)
  RepRec -> pure (u8 F.repRec)
  RepVariant -> pure (u8 F.repVariant)
  RepData name -> do
    written <- qname (\(TyName t) -> t) name
    pure (u8 F.repData <> written)
  RepOpaque -> pure (u8 F.repOpaque)
  RepVal -> pure (u8 F.repVal)

joinPoint :: Join -> Bytes
joinPoint j = joinName j.name <> vecOf reg j.params <> node j.body

-- | A run of instructions and the `Tail` that ends it. An opcode at or above
-- | `tailFrom` is a `Tail`, so nothing counts the instructions.
node :: Node -> Bytes
node n = Array.concatMap instr n.code <> tail n.tail

instr :: Instr -> Bytes
instr = case _ of
  LOADK d c -> u8 F.opLoadK <> reg d <> constIx c
  LOADG d g -> u8 F.opLoadG <> reg d <> globalIx g
  LOADC d c -> u8 F.opLoadC <> reg d <> ctorIx c
  MOVE d s -> u8 F.opMove <> reg d <> reg s
  CAPT d i -> u8 F.opCapt <> reg d <> uvar i
  CLOS d f rs -> u8 F.opClos <> reg d <> funcIx f <> vecOf reg rs
  CLOSN d f n -> u8 F.opClosN <> reg d <> funcIx f <> uvar n
  SETCAP d i s -> u8 F.opSetCap <> reg d <> uvar i <> reg s
  PAP d c rs -> u8 F.opPap <> reg d <> calleeIx c <> vecOf reg rs
  CTOR d c rs -> u8 F.opCtor <> reg d <> ctorIx c <> vecOf reg rs
  CALLK d g rs -> u8 F.opCallK <> reg d <> globalIx g <> vecOf reg rs
  CALLU d s rs -> u8 F.opCallU <> reg d <> reg s <> vecOf reg rs
  FFI d f rs -> u8 F.opFfi <> reg d <> foreignIx f <> vecOf reg rs
  PRIM d p rs -> u8 F.opPrim <> reg d <> primIx p <> vecOf reg rs
  FIELD d s c i -> u8 F.opField <> reg d <> reg s <> ctorIx c <> uvar i
  RNEW d -> u8 F.opRNew <> reg d
  REXT d k v r -> u8 F.opRExt <> reg d <> keyIx k <> reg v <> reg r
  RSEL d k s -> u8 F.opRSel <> reg d <> keyIx k <> reg s
  RRES d k s -> u8 F.opRRes <> reg d <> keyIx k <> reg s
  RUPD d k r v -> u8 F.opRUpd <> reg d <> keyIx k <> reg r <> reg v
  RMRG d a b -> u8 F.opRMrg <> reg d <> reg a <> reg b
  VINJ d k s -> u8 F.opVInj <> reg d <> keyIx k <> reg s
  VPAY d k s -> u8 F.opVPay <> reg d <> keyIx k <> reg s
  VABS d s -> u8 F.opVAbs <> reg d <> reg s
  PERF d k o s -> u8 F.opPerf <> reg d <> keyIx k <> opIx o <> reg s
  HNDL d h b r cs ->
    u8 F.opHndl <> reg d <> handlerIx h <> reg b <> reg r <> vecOf reg cs
  RGN d g b vs -> u8 F.opRgn <> reg d <> regionIx g <> reg b <> vecOf reg vs
  CGET d g i -> u8 F.opCGet <> reg d <> reg g <> uvar i
  CSET d g i s -> u8 F.opCSet <> reg d <> reg g <> uvar i <> reg s

tail :: Tail -> Bytes
tail = case _ of
  RET s -> u8 F.tailRet <> reg s
  TAILK g rs -> u8 F.tailTailK <> globalIx g <> vecOf reg rs
  TAILU s rs -> u8 F.tailTailU <> reg s <> vecOf reg rs
  TAILFFI f rs -> u8 F.tailTailFfi <> foreignIx f <> vecOf reg rs
  JMP j rs -> u8 F.tailJmp <> joinName j <> vecOf reg rs
  BRIF s c a -> u8 F.tailBrIf <> reg s <> node c <> node a
  BRC s cases def ->
    u8 F.tailBrC <> reg s
      <> vecOf (\c -> ctorIx c.ctor <> node c.body) cases
      <> optional def
  BRL s cases def ->
    u8 F.tailBrL <> reg s
      <> vecOf (\c -> constIx c.lit <> node c.body) cases
      <> node def
  BRK s cases def ->
    u8 F.tailBrK <> reg s
      <> vecOf (\c -> keyIx c.key <> node c.body) cases
      <> optional def
  TAILHNDL h b r cs ->
    u8 F.tailTailHndl <> handlerIx h <> reg b <> reg r <> vecOf reg cs
  TAILRGN g b vs -> u8 F.tailTailRgn <> regionIx g <> reg b <> vecOf reg vs

-- | A default where there is one, which `BRL` never needs: literals cannot be
-- | exhausted, so its default is not optional.
optional :: Maybe Node -> Bytes
optional = case _ of
  Nothing -> u8 F.noDefault
  Just n -> u8 F.someDefault <> node n

reg :: Reg -> Bytes
reg (Reg n) = uvar n

constIx :: ConstIx -> Bytes
constIx (ConstIx n) = uvar n

keyIx :: KeyIx -> Bytes
keyIx (KeyIx n) = uvar n

opIx :: OpIx -> Bytes
opIx (OpIx n) = uvar n

ctorIx :: CtorIx -> Bytes
ctorIx (CtorIx n) = uvar n

globalIx :: GlobalIx -> Bytes
globalIx (GlobalIx n) = uvar n

foreignIx :: ForeignIx -> Bytes
foreignIx (ForeignIx n) = uvar n

calleeIx :: CalleeIx -> Bytes
calleeIx (CalleeIx n) = uvar n

primIx :: PrimIx -> Bytes
primIx (PrimIx n) = uvar n

funcIx :: FuncIx -> Bytes
funcIx (FuncIx n) = uvar n

handlerIx :: HandlerIx -> Bytes
handlerIx (HandlerIx n) = uvar n

regionIx :: RegionIx -> Bytes
regionIx (RegionIx n) = uvar n

joinName :: JoinName -> Bytes
joinName (JoinName n) = uvar n
