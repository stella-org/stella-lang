-- | What a loader establishes of one module, established before code is generated.
-- |
-- | A decoder hands on every module whose bytes it can read; whether the module's
-- | declarations are its own, whether its globals are installable, whether a
-- | foreign the ABI fixes is declared as that entry, and whether its handlers and
-- | their installations agree are properties of the module and not of its bytes
-- | ([Encoding](../../../../../docs/technical-references/05-Backend/02-Encoding.md)).
-- | Steam checks them where a module is loaded. Generated code has no such moment
-- | for what one module decides alone, so this checks it here, and what another
-- | module declares is checked where the generated modules are linked and loaded.
module Stella.Backend.JavaScript.Check
  ( check
  ) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.Maybe (Maybe(..))
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Stella.Compiler.Bytecode.Instr (FuncIx(..), Function, HandlerIx(..), Instr(..), KeyIx(..), Node, OpIx(..), Tail(..))
import Stella.Compiler.Bytecode.Module (Dmo, GlobalInit(..))
import Stella.Backend.JavaScript.Error (JsError(..))
import Stella.Backend.JavaScript.ToFrame (keyString, runtimeEntry)
import Stella.Compiler.TypedCore.Name (ModuleName(..), OpName(..), Qualified(..))

check :: Dmo -> Either JsError Unit
check dmo = do
  when (dmo.name == ModuleName "Prim") (Left (ReservedModuleName dmo.name))

  -- `CTORS`, `EFFECTS`, `FOREIGNS`, and `GLOBALS` are what this module declares
  for_ dmo.ctors \c -> do
    unless (own c.name) (Left (NotThisModule c.name))
    unless (qualifier c.owner == dmo.name) (Left (OwnerNotThisModule c.name))
  for_ dmo.effects \e -> unless (qualifier e.name == dmo.name) (Left (EffectNotThisModule e.name))
  for_ dmo.foreigns \f -> unless (own f.name) (Left (NotThisModule f.name))
  for_ dmo.globals \g -> unless (own g.name) (Left (NotThisModule g.name))

  -- one name is one declaration within a namespace
  firstTwice (map _.name dmo.ctors) DeclaredTwice
  firstTwice (map _.name dmo.effects) EffectDeclaredTwice
  firstTwice values DeclaredTwice

  for_ dmo.exports \x -> unless (Array.elem x values) (Left (ExportNotDeclared x))

  -- a global is installed over an empty capture list: a `func` global as a
  -- function of at least one parameter, a `run` global entered with none
  for_ dmo.globals \g -> case g.init of
    GFunc (FuncIx i) -> for_ (Array.index dmo.functions i) \f -> do
      when (f.nparams == 0) (Left (FunctionGlobalWithoutParameters g.name))
      noCaptures g.name f
    GRun (FuncIx i) -> for_ (Array.index dmo.functions i) \f -> do
      when (f.nparams /= 0) (Left (RunGlobalWithParameters g.name f.nparams))
      noCaptures g.name f

  -- a foreign whose name the ABI fixes as an entry the runtime carries out is that
  -- entry, and a declaration of it at another arity is not a declaration of it
  for_ dmo.foreigns \f -> case runtimeEntry f.name of
    Just entry | entry.arity /= f.arity -> Left (EntryDeclaredAtWrongArity f.name entry.arity f.arity)
    _ -> Right unit

  -- a cell is found by its key and a clause by its operation, so either standing
  -- twice would leave which one a cell access or a perform means to the order of a
  -- table
  for_ dmo.handlers \h -> do
    cells <- traverse keyText h.cells
    firstTwice cells CellKeyTwice
    ops <- traverse (\c -> opText c.op) h.opClauses
    firstTwice ops ClauseTwice

  -- every installation supplies one clause per clause of its handler entry and one
  -- initial value per cell, wherever in a function it stands
  for_ dmo.functions \f -> for_ (nodesOf f) \node -> do
    for_ node.code case _ of
      HNDL _ ix _ _ clauses cells -> operands ix clauses cells
      _ -> Right unit
    case node.tail of
      TAILHNDL ix _ _ clauses cells -> operands ix clauses cells
      _ -> Right unit

  where
  keyText (KeyIx i) = case Array.index dmo.keys i of
    Just key -> Right (keyString key)
    Nothing -> Left (NoSuchIndex "KEYS" i)

  opText (OpIx i) = case Array.index dmo.ops i of
    Just (OpName op) -> Right op
    Nothing -> Left (NoSuchIndex "OPS" i)

  operands :: forall a b. HandlerIx -> P.Array a -> P.Array b -> Either JsError Unit
  operands (HandlerIx i) clauses cells = case Array.index dmo.handlers i of
    Nothing -> Left (NoSuchIndex "HANDLERS" i)
    Just h -> do
      key <- keyText h.key
      when (Array.length clauses /= Array.length h.opClauses)
        (Left (HandlerClausesDisagree key (Array.length h.opClauses) (Array.length clauses)))
      when (Array.length cells /= Array.length h.cells)
        (Left (HandlerCellsDisagree key (Array.length h.cells) (Array.length cells)))

  own :: forall a. Qualified a -> P.Boolean
  own q = qualifier q == dmo.name

  qualifier :: forall a. Qualified a -> ModuleName
  qualifier (Qualified m _) = m

  values = map _.name dmo.globals <> map _.name dmo.foreigns

  noCaptures name f =
    let
      n = Array.length f.captures
    in
      when (n /= 0) (Left (GlobalExpectsCaptures name n))

  firstTwice :: forall a. Eq a => P.Array a -> (a -> JsError) -> Either JsError Unit
  firstTwice xs refusal =
    case Array.find (\(Tuple i x) -> Array.elemIndex x xs /= Just i) (Array.mapWithIndex Tuple xs) of
      Just (Tuple _ x) -> Left (refusal x)
      Nothing -> Right unit

-- | Every node of a function: its body, the body of each join point, and the nodes
-- | a branch holds inline.
nodesOf :: Function -> P.Array Node
nodesOf f = Array.concatMap expand ([ f.body ] <> map _.body f.joins)
  where
  expand node = [ node ] <> Array.concatMap expand (inline node.tail)

  inline = case _ of
    BRIF _ a b -> [ a, b ]
    BRC _ cases fallback -> map _.body cases <> Array.fromFoldable fallback
    BRL _ cases fallback -> map _.body cases <> [ fallback ]
    BRK _ cases fallback -> map _.body cases <> Array.fromFoldable fallback
    _ -> []
