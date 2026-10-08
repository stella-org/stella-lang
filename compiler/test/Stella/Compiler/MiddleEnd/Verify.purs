-- | The invariants a lowering rests on, and the modules that break them.
-- |
-- | Each fixture is a Mid IR module written by hand with one thing wrong. A
-- | translation produces none of them; what is asserted is that a consumer says
-- | so rather than lowering a module whose registers do not line up.
module Test.Stella.Compiler.MiddleEnd.Verify (spec) where

import Prelude

import Prim as P

import Stella.Compiler.Bytecode (lower)
import Stella.Compiler.Bytecode as B
import Stella.Compiler.Primitive (PrimOp(..))
import Stella.Compiler.MiddleEnd (Rep(..), VerifyError(..), emptyDebug, verify)
import Stella.Compiler.MiddleEnd as M
import Stella.Compiler.TypedCore (Ident(..), Literal(..), ModuleName(..), OpName(..), Qualified(..), RowKey(..), Symbol(..), TyName(..))
import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

main :: ModuleName
main = ModuleName "Main"

-- | A module of one function, which is all any of these needs.
moduleOf :: M.Function -> M.Module
moduleOf f =
  { name: main
  , imports: []
  , ctors: []
  , effects: []
  , foreigns: []
  , functions: [ f ]
  -- the checks on a global are their own cases below, so these fixtures
  -- declare none and stand on the function alone
  , globals: []
  , exports: []
  }

withGlobal :: M.GlobalInit -> M.Module -> M.Module
withGlobal init m = m { globals = [ { ref: Qualified main (Ident "f"), init } ] }

globalName :: Qualified Ident
globalName = Qualified main (Ident "f")

listName :: Qualified TyName
listName = Qualified main (TyName "List")

nilName :: Qualified Ident
nilName = Qualified main (Ident "Nil")

consName :: Qualified Ident
consName = Qualified main (Ident "Cons")

foreignName :: Qualified Ident
foreignName = Qualified main (Ident "trace")

nameKey :: RowKey
nameKey = SymbolKey (Symbol "name")

-- | The fixture with a list type and a foreign of one argument declared, which
-- | is what makes their arities this module's to check.
withList :: M.Module -> M.Module
withList m = m
  { ctors =
      [ { ref: nilName, owner: listName, tag: 0, arity: 0, isNewtype: false }
      , { ref: consName, owner: listName, tag: 1, arity: 2, isNewtype: false }
      ]
  , foreigns = [ { ref: foreignName, arity: 1 } ]
  }

binder :: P.Int -> M.Binder
binder n = { local: M.Local n, rep: RepInt }

-- | One parameter, and a body binding the local the case calls for.
functionOf :: P.Array M.Binder -> P.Array M.Binder -> M.Expr -> M.Function
functionOf params captures body = { id: M.FuncId 0, params, captures, body }

ret :: M.Local -> M.Expr
ret local = M.ERet (M.ALocal local)

-- | `let l = 1 in l`.
bindThen :: P.Int -> M.Expr
bindThen n =
  M.ELet (M.Local n) RepInt (M.CPure (M.ALit (LitInt 1))) (ret (M.Local n))

-- | A module opening a region of the keys and initial values given, whose body
-- | is what the cases on a region vary: the identity is its parameter.
regionWith :: P.Array RowKey -> P.Array M.Atom -> M.Expr -> M.Module
regionWith keys initial inner = (moduleOf site) { functions = [ site, body ] }
  where
  site =
    { id: M.FuncId 0
    , params: [ binder 0 ]
    , captures: []
    , body: M.ETail (M.CRegion keys (M.FuncId 1) [] initial)
    }

  body = { id: M.FuncId 1, params: [ { local: M.Local 0, rep: RepVal } ], captures: [], body: inner }

-- | A region of the cells given whose body reads its first cell.
opening :: P.Array RowKey -> P.Array M.Atom -> M.Module
opening keys initial =
  regionWith keys initial (M.ETail (M.CReadCell (M.ALocal (M.Local 0)) 0))

spec :: Spec Unit
spec = describe "Stella.Compiler.MiddleEnd.Verify » modules a lowering must not accept" do

  it "accepts a function whose locals run from zero without a gap" do
    verify (moduleOf (functionOf [ binder 0 ] [] (bindThen 1))) `shouldEqual` Right unit

  it "rejects a hole in the locals, naming the number nothing bound" do
    -- a lowering takes a local's number for a register, so a gap displaces every
    -- slot after it and a `Rep` array would carry a slot nothing wrote
    verify (moduleOf (functionOf [ binder 0 ] [] (bindThen 2)))
      `shouldEqual` Left (LocalsNotDense (M.FuncId 0) 1)

  it "rejects a local bound twice" do
    verify (moduleOf (functionOf [ binder 0 ] [] (bindThen 0)))
      `shouldEqual` Left (DuplicateLocal (M.FuncId 0) (M.Local 0))

  it "rejects a parameter outside the slots a caller writes" do
    -- the caller places its argument in slot 0 and the body would read slot 1
    verify (moduleOf (functionOf [ binder 1 ] [] (bindThen 0)))
      `shouldEqual` Left (ParameterOutOfPlace (M.FuncId 0) (M.Local 1))

  it "rejects a capture outside the slots after the parameters" do
    verify (moduleOf (functionOf [ binder 0 ] [ binder 2 ] (bindThen 1)))
      `shouldEqual` Left (CaptureOutOfPlace (M.FuncId 0) (M.Local 2))

  it "rejects a closure over a function the module does not hold" do
    let
      body =
        M.ELet (M.Local 1) RepClos (M.CClosure (M.FuncId 7) []) (ret (M.Local 1))
    verify (moduleOf (functionOf [ binder 0 ] [] body))
      `shouldEqual` Left (UnknownFunction (M.FuncId 0) (M.FuncId 7))

  it "rejects a closure supplying captures the function does not take" do
    let
      body =
        M.ELet (M.Local 1) RepClos (M.CClosure (M.FuncId 0) [ M.ALit (LitInt 1) ])
          (ret (M.Local 1))
    verify (moduleOf (functionOf [ binder 0 ] [] body))
      `shouldEqual` Left (CaptureCount (M.FuncId 0) (M.FuncId 0) 0 1)

  it "is what a lowering reports, rather than lowering the module anyway" do
    let
      broken = { module: moduleOf (functionOf [ binder 0 ] [] (bindThen 2)), debug: emptyDebug }
    map _.dmo (lower (broken :: { module :: M.Module, debug :: M.Debug P.Int }))
      `shouldEqual` Left (B.Unverified (LocalsNotDense (M.FuncId 0) 1))

  it "accepts a global that evaluates a function of no parameters" do
    let thunk = functionOf [] [] (bindThen 0)
    verify (withGlobal (M.GRun (M.FuncId 0)) (moduleOf thunk)) `shouldEqual` Right unit

  it "rejects a global naming a function the table does not hold" do
    let thunk = functionOf [] [] (bindThen 0)
    verify (withGlobal (M.GRun (M.FuncId 3)) (moduleOf thunk))
      `shouldEqual` Left (GlobalFunctionMissing globalName (M.FuncId 3))

  it "rejects a global that evaluates a function taking parameters" do
    -- initialization supplies no argument, so there is nowhere for one to come
    -- from
    verify (withGlobal (M.GRun (M.FuncId 0)) (moduleOf (functionOf [ binder 0 ] [] (bindThen 1))))
      `shouldEqual` Left (RunTakesParameters globalName (M.FuncId 0))

  it "rejects a global whose function captures something" do
    -- a global is installed over an empty capture list, there being nothing yet
    -- to capture
    let capturing = functionOf [ binder 0 ] [ binder 1 ] (bindThen 2)
    verify (withGlobal (M.GFunc (M.FuncId 0)) (moduleOf capturing))
      `shouldEqual` Left (GlobalTakesCaptures globalName (M.FuncId 0))

  it "rejects a function table whose entries are not at their own identifiers" do
    -- a consumer reaches a function by index, so `[id 1, id 0]` has every
    -- reference arrive at the other function
    let
      swapped = (moduleOf (functionOf [ binder 0 ] [] (bindThen 1)))
        { functions =
            [ { id: M.FuncId 1, params: [ binder 0 ], captures: [], body: bindThen 1 }
            , { id: M.FuncId 0, params: [ binder 0 ], captures: [], body: bindThen 1 }
            ]
        }
    verify swapped `shouldEqual` Left (FunctionOutOfPlace 0 (M.FuncId 1))

  it "rejects a function table holding one identifier twice" do
    let
      f = { id: M.FuncId 0, params: [ binder 0 ], captures: [], body: bindThen 1 }
      repeated = (moduleOf f) { functions = [ f, f ] }
    verify repeated `shouldEqual` Left (FunctionOutOfPlace 1 (M.FuncId 0))

  it "rejects a read of a local nothing binds" do
    -- the function has one register and the body would read the eighth
    verify (moduleOf (functionOf [ binder 0 ] [] (ret (M.Local 7))))
      `shouldEqual` Left (LocalNotInScope (M.FuncId 0) (M.Local 7))

  it "rejects a read of a local bound in a sibling branch" do
    -- binding is dense and unique across the function, so a sibling's local
    -- passes every layout check while standing in no enclosing scope
    let
      body =
        M.EIf (M.ALit (LitBoolean true))
          (M.ELet (M.Local 1) RepInt (M.CPure (M.ALit (LitInt 1))) (ret (M.Local 1)))
          (ret (M.Local 1))
    verify (moduleOf (functionOf [ binder 0 ] [] body))
      `shouldEqual` Left (LocalNotInScope (M.FuncId 0) (M.Local 1))

  it "accepts a join point jumped to from inside its own definition" do
    let
      body =
        M.ELetJoin (M.JoinId 0) [ binder 1 ]
          (M.EJump (M.JoinId 0) [ M.ALocal (M.Local 1) ])
          (M.EJump (M.JoinId 0) [ M.ALocal (M.Local 0) ])
    verify (moduleOf (functionOf [ binder 0 ] [] body)) `shouldEqual` Right unit

  it "rejects a jump to a join point no enclosing scope declares" do
    verify (moduleOf (functionOf [ binder 0 ] [] (M.EJump (M.JoinId 2) [])))
      `shouldEqual` Left (JoinNotInScope (M.FuncId 0) (M.JoinId 2))

  it "rejects a jump supplying the wrong number of arguments" do
    let
      body =
        M.ELetJoin (M.JoinId 0) [ binder 1 ]
          (ret (M.Local 1))
          (M.EJump (M.JoinId 0) [])
    verify (moduleOf (functionOf [ binder 0 ] [] body))
      `shouldEqual` Left (JoinArity (M.FuncId 0) (M.JoinId 0) 1 0)

  it "rejects a saturated operation given the wrong number of operands" do
    -- the manifest fixes the arity, so this needs no declaration to check
    let body = M.ETail (M.CPrim IntAdd [ M.ALocal (M.Local 0) ])
    verify (moduleOf (functionOf [ binder 0 ] [] body))
      `shouldEqual` Left (PrimArity (M.FuncId 0) IntAdd 2 1)

  it "rejects a partial application that is not partial" do
    let body = M.ETail (M.CPap (M.CalleePrim IntAdd) [ M.ALocal (M.Local 0), M.ALocal (M.Local 0) ])
    verify (moduleOf (functionOf [ binder 0 ] [] body))
      `shouldEqual` Left (PapSaturated (M.FuncId 0) 2 2)

  it "rejects a join point declared twice in one function" do
    -- scope alone would let the inner one shadow the outer, but a lowering puts
    -- the join points of a function in one flat table
    let
      body =
        M.ELetJoin (M.JoinId 0) []
          (M.ELetJoin (M.JoinId 0) [] (ret (M.Local 0)) (M.EJump (M.JoinId 0) []))
          (M.EJump (M.JoinId 0) [])
    verify (moduleOf (functionOf [ binder 0 ] [] body))
      `shouldEqual` Left (DuplicateJoin (M.FuncId 0) (M.JoinId 0))

  it "rejects a known call to a global that is evaluated rather than installed" do
    -- what it stores is a value of its own arity, and absent is not zero
    let
      thunk = functionOf [] [] (bindThen 0)
      body = M.ETail (M.CCallKnown globalName [ M.ALit (LitInt 1) ])
      caller = { id: M.FuncId 1, params: [], captures: [], body }
      m = (withGlobal (M.GRun (M.FuncId 0)) (moduleOf thunk))
        { functions = [ thunk, caller ] }
    verify m `shouldEqual` Left (NoDefinitionalArity (M.FuncId 1) globalName)

  it "accepts a known call to a global installed as a function of that arity" do
    let
      callee = functionOf [ binder 0 ] [] (ret (M.Local 0))
      body = M.ETail (M.CCallKnown globalName [ M.ALit (LitInt 1) ])
      caller = { id: M.FuncId 1, params: [], captures: [], body }
      m = (withGlobal (M.GFunc (M.FuncId 0)) (moduleOf callee))
        { functions = [ callee, caller ] }
    verify m `shouldEqual` Right unit

  it "rejects a known call supplying the wrong number of arguments" do
    let
      callee = functionOf [ binder 0 ] [] (ret (M.Local 0))
      body = M.ETail (M.CCallKnown globalName [])
      caller = { id: M.FuncId 1, params: [], captures: [], body }
      m = (withGlobal (M.GFunc (M.FuncId 0)) (moduleOf callee))
        { functions = [ callee, caller ] }
    verify m `shouldEqual` Left (CallArity (M.FuncId 1) globalName 1 0)

  it "rejects a saturated constructor of this module given the wrong arity" do
    let body = M.ETail (M.CCtor consName [ M.ALocal (M.Local 0) ])
    verify (withList (moduleOf (functionOf [ binder 0 ] [] body)))
      `shouldEqual` Left (CtorArity (M.FuncId 0) consName 2 1)

  it "rejects a saturated foreign of this module given the wrong arity" do
    let body = M.ETail (M.CForeign foreignName [])
    verify (withList (moduleOf (functionOf [ binder 0 ] [] body)))
      `shouldEqual` Left (ForeignArity (M.FuncId 0) foreignName 1 0)

  it "rejects a projection of a field the constructor does not have" do
    let body = M.ETail (M.CField (M.ALocal (M.Local 0)) consName 2)
    verify (withList (moduleOf (functionOf [ binder 0 ] [] body)))
      `shouldEqual` Left (FieldOutOfRange (M.FuncId 0) consName 2)

  it "rejects a dispatch with no default that misses a constructor" do
    let
      body =
        M.ESwitchCtor (M.ALocal (M.Local 0))
          [ { ctor: nilName, body: ret (M.Local 0) } ]
          Nothing
    verify (withList (moduleOf (functionOf [ binder 0 ] [] body)))
      `shouldEqual` Left (BranchesNotExhaustive (M.FuncId 0) listName)

  it "accepts that dispatch once every constructor has a destination" do
    let
      body =
        M.ESwitchCtor (M.ALocal (M.Local 0))
          [ { ctor: nilName, body: ret (M.Local 0) }
          , { ctor: consName, body: ret (M.Local 0) }
          ]
          Nothing
    verify (withList (moduleOf (functionOf [ binder 0 ] [] body))) `shouldEqual` Right unit

  it "rejects a dispatch naming one constructor twice" do
    let
      body =
        M.ESwitchCtor (M.ALocal (M.Local 0))
          [ { ctor: nilName, body: ret (M.Local 0) }
          , { ctor: nilName, body: ret (M.Local 0) }
          ]
          (Just (ret (M.Local 0)))
    verify (withList (moduleOf (functionOf [ binder 0 ] [] body)))
      `shouldEqual` Left (DuplicateBranch (M.FuncId 0) nilName)

  it "rejects a handler clause reached at the wrong arity" do
    -- a `full` clause takes the operation's argument and the continuation
    let
      clause = { id: M.FuncId 1, params: [ binder 0 ], captures: [], body: ret (M.Local 0) }
      handler =
        { key: nameKey
        , returnClause: { func: M.FuncId 1, captures: [] }
        , opClauses:
            [ { op: OpName "next"
              , form: M.ClauseFull
              , clause: { func: M.FuncId 1, captures: [] }
              }
            ]
        }
      body = M.ETail (M.CHandle handler (M.FuncId 2) [])
      site = { id: M.FuncId 0, params: [ binder 0 ], captures: [], body }
      inner = { id: M.FuncId 2, params: [], captures: [], body: ret (M.Local 0) }
    verify ((moduleOf site) { functions = [ site, clause, inner ] })
      `shouldEqual` Left (ClauseArity (M.FuncId 0) (M.FuncId 1) 2 1)

  it "accepts a region of one initial value per key, its body reading a cell" do
    verify (opening [ nameKey ] [ M.ALit (LitInt 0) ]) `shouldEqual` Right unit

  it "rejects a region supplying more initial values than it has keys" do
    -- a cell takes the initial value at its own position, so a disagreement
    -- leaves a value with no cell
    verify (opening [ nameKey ] [ M.ALit (LitInt 0), M.ALit (LitInt 1) ])
      `shouldEqual` Left (CellCount (M.FuncId 0) 1 2)

  it "rejects a region naming one cell key twice" do
    verify (opening [ nameKey, nameKey ] [ M.ALit (LitInt 0), M.ALit (LitInt 1) ])
      `shouldEqual` Left (DuplicateCell (M.FuncId 0) nameKey)

  it "rejects a region whose body takes no identity" do
    let
      m = opening [ nameKey ] [ M.ALit (LitInt 0) ]
      body = { id: M.FuncId 1, params: [], captures: [], body: bindThen 0 }
    verify (m { functions = Array.take 1 m.functions <> [ body ] })
      `shouldEqual` Left (ClauseArity (M.FuncId 0) (M.FuncId 1) 1 0)

  it "rejects a cell reached through an identity not in scope" do
    verify (regionWith [ nameKey ] [ M.ALit (LitInt 0) ] (M.ETail (M.CReadCell (M.ALocal (M.Local 1)) 0)))
      `shouldEqual` Left (LocalNotInScope (M.FuncId 1) (M.Local 1))

  it "rejects a cell named by a negative position" do
    verify
      ( regionWith [ nameKey ] [ M.ALit (LitInt 0) ]
          ( M.ELet (M.Local 1) RepVal
              (M.CWriteCell (M.ALocal (M.Local 0)) (-1) (M.ALit (LitInt 1)))
              (ret (M.Local 1))
          )
      )
      `shouldEqual` Left (NegativeCell (M.FuncId 1) (-1))
