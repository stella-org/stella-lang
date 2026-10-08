-- | What a module must hold for its bytes to carry it
-- | ([Encoding](../../../../docs/technical-references/05-Backend/02-Encoding.md)).
-- |
-- | **Both directions read this walk**, which is what makes the round trip a
-- | contract rather than a hope: an encoder refuses a module a reader would not
-- | read back, and a decoder refuses to return one the bytes happen to describe.
-- | Two walks could disagree about a module and each be satisfied with itself.
-- |
-- | Three kinds of thing are checked, and each is a property of the module alone:
-- | that no structural value is negative, since a `uvar` carries no sign; that
-- | every index names an entry of the table it indexes; and that every register,
-- | capture, and join point a function's body names belongs to that function.
-- |
-- | What is **not** here is what a loader and a verifier check: whether a
-- | qualified name belongs to this module or one of its imports, whether a local
-- | is bound where it is read, and whether a call supplies a declared arity
-- | ([Bytecode](../../../../docs/technical-references/05-Backend/01-Bytecode.md),
-- | [Mid IR](../../../../docs/technical-references/04-MiddleEnd/01-Mid-IR.md)).
module Stella.Compiler.Bytecode.Validate
  ( validate
  ) where

import Prelude

import Prim as P

import Stella.Compiler.Bytecode.Bytes (Fault(..), TableKind(..))
import Stella.Compiler.Bytecode.Instr (CalleeIx(..), ConstIx(..), CtorIx(..), ForeignIx(..), FuncIx(..), GlobalIx(..), HandlerIx(..), Instr(..), JoinName(..), KeyIx(..), Node, OpIx(..), PrimIx(..), Reg(..), RegionIx(..), Tail(..))
import Stella.Compiler.Bytecode.Instr as B
import Stella.Compiler.Bytecode.Module (Dmo, GlobalInit(..), Key(..))
import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (traverse_)

validate :: Dmo -> Either Fault Unit
validate dmo = do
  traverse_ keyEntry dmo.keys
  traverse_ ctorEntry dmo.ctors
  traverse_ foreignEntry dmo.foreigns
  traverse_ handlerEntry dmo.handlers
  traverse_ regionEntry dmo.regions
  traverse_ globalEntry dmo.globals
  traverse_ functionEntry dmo.functions
  where
  -- Values ---------------------------------------------------------------------

  nonNegative n = if n >= 0 then Right unit else Left (NegativeValue n)

  index kind size i =
    if i >= 0 && i < size then Right unit else Left (IndexOutOfTable kind i)

  keyIx (KeyIx i) = index KeyTable (Array.length dmo.keys) i
  opIx (OpIx i) = index OpTable (Array.length dmo.ops) i
  constIx (ConstIx i) = index ConstantTable (Array.length dmo.constants) i
  ctorIx (CtorIx i) = index CtorRefTable (Array.length dmo.ctorRefs) i
  foreignIx (ForeignIx i) = index ForeignRefTable (Array.length dmo.foreignRefs) i
  globalIx (GlobalIx i) = index GlobalRefTable (Array.length dmo.globalRefs) i
  calleeIx (CalleeIx i) = index CalleeTable (Array.length dmo.callees) i
  primIx (PrimIx i) = index PrimTable (Array.length dmo.prims) i
  handlerIx (HandlerIx i) = index HandlerTable (Array.length dmo.handlers) i
  regionIx (RegionIx i) = index RegionTable (Array.length dmo.regions) i
  funcIx (FuncIx i) = index FunctionTable (Array.length dmo.functions) i

  -- Tables ---------------------------------------------------------------------

  keyEntry = case _ of
    KPosition n -> nonNegative n
    _ -> Right unit

  ctorEntry entry = nonNegative entry.tag *> nonNegative entry.arity

  foreignEntry entry = nonNegative entry.arity

  handlerEntry entry = do
    keyIx entry.key
    traverse_ (\c -> opIx c.op) entry.opClauses

  regionEntry entry = traverse_ keyIx entry.cells

  globalEntry entry = case entry.init of
    GRun f -> funcIx f
    GFunc f -> funcIx f

  -- Functions ------------------------------------------------------------------

  functionEntry f = do
    nonNegative f.nparams
    traverse_ (joinDeclared scope) f.joins
    traverse_ (\j -> traverse_ (register scope) j.params) f.joins
    traverse_ (\j -> node scope j.body) f.joins
    node scope f.body
    where
    scope =
      { registers: Array.length f.regs
      , captures: Array.length f.captures
      , joins: map _.name f.joins
      }

  joinDeclared _ j = case j.name of JoinName i -> nonNegative i

  register scope (Reg i) =
    if i >= 0 && i < scope.registers then Right unit else Left (RegisterOutOfFile i)

  -- | A `CAPT` reads a capture of the activation it stands in, so the function's
  -- | own capture list is the bound. **A `SETCAP` fills a capture of a closure in
  -- | a register**, whose function this instruction does not name, so nothing
  -- | here bounds its index.
  capture scope i =
    if i >= 0 && i < scope.captures then Right unit else Left (CaptureOutOfRange i)

  joinNamed scope name =
    if Array.elem name scope.joins then Right unit
    else case name of JoinName i -> Left (JoinNotDeclared i)

  node :: _ -> Node -> Either Fault Unit
  node scope n = do
    traverse_ (instr scope) n.code
    tail scope n.tail

  instr scope = case _ of
    LOADK d c -> register scope d *> constIx c
    LOADG d g -> register scope d *> globalIx g
    LOADC d c -> register scope d *> ctorIx c
    MOVE d s -> register scope d *> register scope s
    CAPT d i -> register scope d *> capture scope i
    CLOS d f rs -> register scope d *> funcIx f *> traverse_ (register scope) rs
    CLOSN d f n -> register scope d *> funcIx f *> nonNegative n
    SETCAP d i s -> register scope d *> nonNegative i *> register scope s
    PAP d c rs -> register scope d *> calleeIx c *> traverse_ (register scope) rs
    CTOR d c rs -> register scope d *> ctorIx c *> traverse_ (register scope) rs
    CALLK d g rs -> register scope d *> globalIx g *> traverse_ (register scope) rs
    CALLU d s rs -> register scope d *> register scope s *> traverse_ (register scope) rs
    FFI d f rs -> register scope d *> foreignIx f *> traverse_ (register scope) rs
    PRIM d p rs -> register scope d *> primIx p *> traverse_ (register scope) rs
    FIELD d s c j -> register scope d *> register scope s *> ctorIx c *> nonNegative j
    RNEW d -> register scope d
    REXT d k v r ->
      register scope d *> keyIx k *> register scope v *> register scope r
    RSEL d k s -> register scope d *> keyIx k *> register scope s
    RRES d k s -> register scope d *> keyIx k *> register scope s
    RUPD d k r v ->
      register scope d *> keyIx k *> register scope r *> register scope v
    RMRG d a b -> register scope d *> register scope a *> register scope b
    VINJ d k s -> register scope d *> keyIx k *> register scope s
    VPAY d k s -> register scope d *> keyIx k *> register scope s
    VABS d s -> register scope d *> register scope s
    PERF d k o s -> register scope d *> keyIx k *> opIx o *> register scope s
    HNDL d h b r cs ->
      register scope d *> handlerIx h *> register scope b *> register scope r
        *> traverse_ (register scope) cs
    RGN d g b vs ->
      register scope d *> regionIx g *> register scope b *> traverse_ (register scope) vs
    CGET d g i -> register scope d *> register scope g *> nonNegative i
    CSET d g i s -> register scope d *> register scope g *> nonNegative i *> register scope s

  tail scope = case _ of
    RET s -> register scope s
    TAILK g rs -> globalIx g *> traverse_ (register scope) rs
    TAILU s rs -> register scope s *> traverse_ (register scope) rs
    TAILFFI f rs -> foreignIx f *> traverse_ (register scope) rs
    JMP j rs -> joinNamed scope j *> traverse_ (register scope) rs
    BRIF s c a -> register scope s *> node scope c *> node scope a
    BRC s cases def ->
      register scope s
        *> traverse_ (ctorCase scope) cases
        *> traverse_ (node scope) def
    BRL s cases def ->
      register scope s
        *> traverse_ (litCase scope) cases
        *> node scope def
    BRK s cases def ->
      register scope s
        *> traverse_ (keyCase scope) cases
        *> traverse_ (node scope) def
    TAILHNDL h b r cs ->
      handlerIx h *> register scope b *> register scope r
        *> traverse_ (register scope) cs
    TAILRGN g b vs -> regionIx g *> register scope b *> traverse_ (register scope) vs

  ctorCase :: _ -> B.CtorCase -> Either Fault Unit
  ctorCase scope c = ctorIx c.ctor *> node scope c.body

  litCase :: _ -> B.LitCase -> Either Fault Unit
  litCase scope c = constIx c.lit *> node scope c.body

  keyCase :: _ -> B.KeyCase -> Either Fault Unit
  keyCase scope c = keyIx c.key *> node scope c.body
