-- | `lower`, over the vertical slice.
-- |
-- | The slice is carried through checking, translation, and lowering, and what
-- | comes out is written down in full: a difference from the Bytecode document
-- | is a defect in one of the two.
module Test.Stella.Compiler.Bytecode.Lower (spec) where

import Prelude

import Prim as P

-- Everything the bytecode offers is reached through the facade, which is what a
-- machine imports. A member missing from its re-export list fails this module
-- rather than going unnoticed.
import Stella.Compiler.Primitive (PrimOp(..), entryOfOp)
import Stella.Compiler.Bytecode (ConstIx(..), Constant(..), CtorIx(..), Debug, Dmo, FuncIx(..), Function, FunctionDebug, GlobalIx(..), GlobalInit(..), Instr(..), LowerError, PrimIx(..), Reg(..), Tail(..), lower)
import Stella.Compiler.Interface (aritiesOf, importsOf, noImports)
import Stella.Compiler.MiddleEnd (Rep(..), translate)
import Stella.Compiler.TypedCore (Ident(..), ModuleName(..), Qualified(..), TyName(..), declare, declareAnnotated, primSignature)
import Data.Array as Array
import Data.Either (Either(..), either)
import Data.Foldable (foldM)
import Data.String (Pattern(..))
import Data.String as String
import Test.Stella.Compiler.Fixtures.Programs as Programs
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Test.Stella.Compiler.TypedCore.VerticalSlice (intModule, verticalSlice)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

mainModuleName :: ModuleName
mainModuleName = ModuleName "Main"

value :: P.String -> Qualified Ident
value name = Qualified mainModuleName (Ident name)

listTy :: Qualified TyName
listTy = Qualified mainModuleName (TyName "List")

nil :: Qualified Ident
nil = Qualified mainModuleName (Ident "Nil")

cons :: Qualified Ident
cons = Qualified mainModuleName (Ident "Cons")

intAdd :: Qualified Ident
intAdd = Qualified (ModuleName "Base.Int") (Ident "add")

-- | The slice, checked, translated, and lowered. The debug table travels
-- | beside the module through both stages.
loweredWithDebug :: Either P.String { dmo :: Dmo, debug :: Debug P.Int }
loweredWithDebug = case declare primSignature intModule of
  Left _ -> Left "Base.Int did not declare"
  Right s1 -> case declareAnnotated s1 verticalSlice of
    Left _ -> Left "the slice did not declare"
    Right declared -> case translate noImports verticalSlice declared of
      Left err -> Left (show err)
      Right mid -> case lower mid of
        Left err -> Left (show (err :: LowerError))
        Right out -> Right out

lowered :: Either P.String Dmo
lowered = map _.dmo loweredWithDebug

functionOf :: P.Int -> Either P.String Function
functionOf i = do
  dmo <- lowered
  case Array.index dmo.functions i of
    Just f -> Right f
    Nothing -> Left ("no function #" <> show i)

-- | The programs' `Main`, each module declared against those before it,
-- | translated against their interfaces, and lowered.
programsMain :: Either P.String Dmo
programsMain = do
  done <- foldM step { signature: Programs.abiSignature, dmis: [], dmos: [] } [ Programs.intModule, Programs.libModule, Programs.mainModule ]
  case Array.last done.dmos of
    Just dmo -> Right dmo
    Nothing -> Left "no module"
  where
  step acc m = do
    declared <- either (Left <<< show) Right (declareAnnotated acc.signature m)
    imports <- either (Left <<< show) Right (importsOf acc.dmis)
    mid <- either (Left <<< show) Right (translate imports m declared)
    out <- either (Left <<< show) Right (lower mid)
    pure
      { signature: declared.signature
      , dmis: Array.snoc acc.dmis { name: mid.module.name, imports: mid.module.imports, arities: aritiesOf mid.module }
      , dmos: Array.snoc acc.dmos out.dmo
      }

-- | What an instruction is, by its opcode's name.
opcodeOf :: Instr -> P.String
opcodeOf i = case String.indexOf (Pattern " ") (show i) of
  Just n -> String.take n (show i)
  Nothing -> show i

spec :: Spec Unit
spec = describe "Stella.Compiler.Bytecode.Lower » the vertical slice" do

  it "lowers `sum` to one dispatch whose branches hold their own code" do
    -- `BRC`'s branches are `Node`s and not names: the `FIELD`s that take `Cons`
    -- apart stand inside the branch that selected it, which is the only place
    -- the fields exist
    map _.body (functionOf 0) `shouldEqual` Right
      { code: []
      , tail:
          BRC (Reg 0)
            [ { ctor: CtorIx 0
              , body:
                  { code: [ LOADK (Reg 4) (ConstIx 0) ]
                  , tail: RET (Reg 4)
                  }
              }
            , { ctor: CtorIx 1
              , body:
                  { code:
                      [ FIELD (Reg 1) (Reg 0) (CtorIx 1) 0
                      , FIELD (Reg 2) (Reg 0) (CtorIx 1) 1
                      , CALLK (Reg 3) (GlobalIx 0) [ Reg 2 ]
                      , PRIM (Reg 5) (PrimIx 0) [ Reg 1, Reg 3 ]
                      ]
                  , tail: RET (Reg 5)
                  }
              }
            ]
            Nothing
      }

  it "gives `sum` one parameter, no captures, and no join points" do
    map (\f -> { nparams: f.nparams, captures: f.captures, joins: f.joins }) (functionOf 0)
      `shouldEqual` Right { nparams: 1, captures: [], joins: [] }

  it "carries a `Rep` per register, the parameter's first" do
    -- the literal `0` of the `Nil` branch took a register of its own, which is
    -- where the fourth comes from
    map _.regs (functionOf 0) `shouldEqual` Right
      [ RepData listTy, RepInt, RepData listTy, RepInt, RepInt, RepVal ]

  it "returns from an operation rather than tail-calling it" do
    -- an operation is not a transfer of control, so it is the instruction
    -- followed by a `RET`. Only a call has a `Tail` of its own
    let
      consTail = do
        f <- functionOf 0
        case f.body.tail of
          BRC _ branches _ -> case Array.index branches 1 of
            Just branch -> Right branch.body.tail
            Nothing -> Left "no Cons branch"
          _ -> Left "not a dispatch"
    consTail `shouldEqual` Right (RET (Reg 5))

  it "loads the nullary constructor rather than building one" do
    map _.body (functionOf 1) `shouldEqual` Right
      { code:
          [ LOADK (Reg 3) (ConstIx 1)
          , LOADC (Reg 4) (CtorIx 0)
          , CTOR (Reg 0) (CtorIx 1) [ Reg 3, Reg 4 ]
          , LOADK (Reg 5) (ConstIx 2)
          , CTOR (Reg 1) (CtorIx 1) [ Reg 5, Reg 0 ]
          , LOADK (Reg 6) (ConstIx 3)
          , CTOR (Reg 2) (CtorIx 1) [ Reg 6, Reg 1 ]
          ]
      , tail: TAILK (GlobalIx 0) [ Reg 2 ]
      }

  it "interns a constant once, however often it is named" do
    -- `0` appears in the `Nil` branch and again as the last `Cons` argument
    map _.constants lowered `shouldEqual` Right
      [ CInt 0, CInt 3, CInt 2, CInt 1 ]

  it "names what the code refers to, its own and what it imports" do
    let
      refs = do
        dmo <- lowered
        Right { ctors: dmo.ctorRefs, foreigns: dmo.foreignRefs, globals: dmo.globalRefs }
    refs `shouldEqual` Right
      { ctors: [ nil, cons ]
      , foreigns: []
      , globals: [ value "sum" ]
      }

  it "names the operations the module carries out" do
    -- the table holds operations alone. The `Base` entry each realizes is the
    -- ABI version's to say, so target validation reads `Base.Int.add` off the
    -- manifest rather than off a copy here
    map _.prims lowered `shouldEqual` Right [ IntAdd ]
    map entryOfOp [ IntAdd ] `shouldEqual` [ intAdd ]

  it "keeps the declarations of the module apart from those references" do
    -- `Base.Int.add` is referred to and not declared here
    map _.foreigns lowered `shouldEqual` Right []

  it "installs the group member as a closure and runs the nonrec" do
    map _.globals lowered `shouldEqual` Right
      [ { name: value "sum", init: GFunc (FuncIx 0) }
      , { name: value "result", init: GRun (FuncIx 1) }
      ]

  it "carries the constructor table with its tags and arities" do
    map _.ctors lowered `shouldEqual` Right
      [ { name: nil, owner: listTy, tag: 0, arity: 0, isNewtype: false }
      , { name: cons, owner: listTy, tag: 1, arity: 2, isNewtype: false }
      ]

  it "records the format and the contract it was compiled against" do
    let
      header = do
        dmo <- lowered
        Right { formatVersion: dmo.formatVersion, abiVersion: dmo.abiVersion, imports: dmo.imports }
    header `shouldEqual` Right
      { formatVersion: 0, abiVersion: "stella-base-0.1", imports: [ ModuleName "Base.Int" ] }

  it "names neither a key, an operation, a callee, nor a handler" do
    -- the slice has no record, no variant, and no effect
    let
      empties = do
        dmo <- lowered
        Right
          { keys: Array.length dmo.keys
          , ops: Array.length dmo.ops
          , callees: Array.length dmo.callees
          , handlers: Array.length dmo.handlers
          }
    empties `shouldEqual` Right { keys: 0, ops: 0, callees: 0, handlers: 0 }

  it "carries the debug table across, under the indices a `.dmo` names things by" do
    -- `lower` is where a `FuncId` becomes a `FuncIx` and a `Local` a `Reg`. A
    -- consumer may discard the section, and nothing may drop it for them
    let
      names = do
        out <- loweredWithDebug
        Right (map (\(Tuple _ d) -> d.name) (Map.toUnfoldable out.debug.functions :: P.Array (Tuple FuncIx (FunctionDebug P.Int))))
    names `shouldEqual` Right [ Just (value "sum"), Just (value "result") ]

  it "keeps a local's name against the register it became" do
    -- `xs` is `sum`'s parameter, which took slot 0, and the fields the dispatch
    -- bound took the two after it. The literal and the call's result were
    -- created for no name and appear nowhere
    let
      locals = do
        out <- loweredWithDebug
        Right
          ( map (\(Tuple f m) -> Tuple f (Map.toUnfoldable m :: P.Array (Tuple Reg Ident)))
              (Map.toUnfoldable out.debug.locals :: P.Array (Tuple FuncIx (Map.Map Reg Ident)))
          )
    locals `shouldEqual` Right
      [ Tuple (FuncIx 0)
          [ Tuple (Reg 0) (Ident "xs")
          , Tuple (Reg 1) (Ident "x")
          , Tuple (Reg 2) (Ident "ys")
          ]
      ]

  describe "a local recursive group" do
    it "allocates its closures and cells before filling any capture, and forces each cell in order before the body" do
      case programsMain of
        Left err -> fail err
        Right dmo -> case Array.find (\g -> g.name == value "localMixed") dmo.globals of
          Just { init: GRun (FuncIx i) } -> case Array.index dmo.functions i of
            -- `go` and the initializer of `table` allocated, the cell over the
            -- latter, each capture list filled, and `table` forced by its group
            -- before the body forces it again to select from it
            Just f -> map opcodeOf (Array.take 8 f.body.code) `shouldEqual` [ "(CLOSN", "(CLOSN", "(NEED", "(SETCAP", "(SETCAP", "(FORCE", "(FORCE", "(RSEL" ]
            Nothing -> fail "no function"
          _ -> fail "no run named localMixed"
