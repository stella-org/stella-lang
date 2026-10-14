-- | `translate`, over the vertical slice.
-- |
-- | The slice is the program the Translation document works through, so what it
-- | lowers to is written out in full here: a difference from the document is a
-- | defect in one of the two.
-- |
-- | The cases after it are the entries the Implementation Plan singles out, each
-- | one where a plausible translation gives the wrong answer.
module Test.Stella.Compiler.MiddleEnd.Translate (spec) where

import Prelude

import Prim as P

-- Everything Mid IR offers is reached through the facade, which is what a
-- lowering imports. A member missing from its re-export list fails this module
-- rather than going unnoticed.
import Stella.Compiler.Primitive (PrimOp(..))
import Stella.Compiler.Interface (aritiesOf, importsOf, noImports)
import Stella.Compiler.MiddleEnd (Rep(..), TranslateError, translate)
import Stella.Compiler.MiddleEnd as M
import Stella.Compiler.TypedCore (Ident(..), Literal(..), ModuleName(..), Qualified(..), TyName(..), declare, declareAnnotated, primSignature)
import Data.Array as Array
import Data.Either (Either(..), either)
import Data.Foldable (foldM)
import Data.Maybe (Maybe(..))
import Data.String (Pattern(..))
import Data.String as String
import Test.Stella.Compiler.Fixtures.Programs as Programs
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

-- | The slice, checked and lowered.
lowered :: Either P.String M.Module
lowered = case declare primSignature intModule of
  Left _ -> Left "Base.Int did not declare"
  Right s1 -> case declareAnnotated s1 verticalSlice of
    Left _ -> Left "the slice did not declare"
    Right declared -> case translate noImports verticalSlice declared of
      Left err -> Left (show (err :: TranslateError))
      Right result -> Right result.module

-- | `Base.Int`, which the slice imports. It declares one foreign and no value.
loweredInt :: Either P.String M.Module
loweredInt = case declareAnnotated primSignature intModule of
  Left _ -> Left "Base.Int did not declare"
  Right declared -> case translate noImports intModule declared of
    Left err -> Left (show (err :: TranslateError))
    Right result -> Right result.module

functionOf :: P.Int -> Either P.String M.Function
functionOf i = do
  m <- lowered
  case Array.find (\f -> f.id == M.FuncId i) m.functions of
    Just f -> Right f
    Nothing -> Left ("no function #" <> show i)

-- | The programs' modules, each declared against those before it and translated
-- | against their interfaces; the last of them, `Main`.
programsMain :: Either P.String M.Module
programsMain = do
  done <- foldM step { signature: Programs.abiSignature, dmis: [], modules: [] } [ Programs.intModule, Programs.libModule, Programs.mainModule ]
  case Array.last done.modules of
    Just m -> Right m
    Nothing -> Left "no module"
  where
  step acc m = do
    declared <- either (Left <<< show) Right (declareAnnotated acc.signature m)
    imports <- either (Left <<< show) Right (importsOf acc.dmis)
    mid <- either (Left <<< show) Right (translate imports m declared)
    pure
      { signature: declared.signature
      , dmis: Array.snoc acc.dmis { name: mid.module.name, imports: mid.module.imports, arities: aritiesOf mid.module }
      , modules: Array.snoc acc.modules mid.module
      }

-- | The function a global of `Main` is evaluated by, and the module.
runOf :: P.String -> M.Module -> Either P.String M.Function
runOf name m = case Array.find (\g -> g.ref == value name) m.globals of
  Just { init: M.GRun func } -> case Array.find (\f -> f.id == func) m.functions of
    Just f -> Right f
    Nothing -> Left "no function"
  _ -> Left ("no run named " <> name)

functionIn :: M.Module -> M.FuncId -> Maybe M.Function
functionIn m func = Array.find (\f -> f.id == func) m.functions

spec :: Spec Unit
spec = describe "Stella.Compiler.MiddleEnd.Translate » the vertical slice" do

  it "lowers `sum` to one dispatch over the scrutinee" do
    -- `λ (xs : List Int). case (xs) of switchCtor s0 { Nil -> 0 ; Cons -> … }`
    map _.body (functionOf 0) `shouldEqual` Right
      ( M.ESwitchCtor (M.ALocal (M.Local 0))
          [ { ctor: nil, body: M.ERet (M.ALit (LitInt 0)) }
          , { ctor: cons
            , body:
                M.ELet (M.Local 1) RepInt (M.CField (M.ALocal (M.Local 0)) cons 0)
                  ( M.ELet (M.Local 2) (RepData listTy) (M.CField (M.ALocal (M.Local 0)) cons 1)
                      ( M.ELet (M.Local 3) RepInt (M.CCallKnown (value "sum") [ M.ALocal (M.Local 2) ])
                          (M.ETail (M.CPrim IntAdd [ M.ALocal (M.Local 1), M.ALocal (M.Local 3) ]))
                      )
                  )
            }
          ]
          Nothing
      )

  it "gives `sum` one parameter and no captures" do
    -- a top-level recursive group refers to itself by global name, so nothing
    -- is captured
    map (\f -> { params: f.params, captures: f.captures }) (functionOf 0) `shouldEqual` Right
      { params: [ { local: M.Local 0, rep: RepData listTy } ], captures: [] }

  it "projects a constructor's fields inside the branch that selected it" do
    -- the two `CField`s stand under `Cons` and nowhere else: the fields exist
    -- only there
    let
      nilBranchBinds = do
        f <- functionOf 0
        case f.body of
          M.ESwitchCtor _ branches _ -> case Array.head branches of
            Just branch -> Right branch.body
            Nothing -> Left "no branches"
          _ -> Left "not a dispatch"
    nilBranchBinds `shouldEqual` Right (M.ERet (M.ALit (LitInt 0)))

  it "makes the addition an operation and the recursion an ordinary call" do
    -- `Base.Int.add` is a `Base` entry the ABI fixes the meaning of, so it is an
    -- operation carried out directly rather than a call to an implementation
    let
      tails = do
        f <- functionOf 0
        case f.body of
          M.ESwitchCtor _ branches _ -> case Array.index branches 1 of
            Just branch -> Right (spine branch.body)
            Nothing -> Left "no Cons branch"
          _ -> Left "not a dispatch"
    tails `shouldEqual` Right (M.ETail (M.CPrim IntAdd [ M.ALocal (M.Local 1), M.ALocal (M.Local 3) ]))

  it "folds the spine of `result` into saturated constructor calls" do
    -- `Main.Nil [Int]` erased to a constant, and each `Cons` is one `CCtor`.
    -- The locals start from zero again: a `Local` is unique within a function
    -- and not beyond one
    map _.body (functionOf 1) `shouldEqual` Right
      ( M.ELet (M.Local 0) (RepData listTy) (M.CCtor cons [ M.ALit (LitInt 3), M.ACtor nil ])
          ( M.ELet (M.Local 1) (RepData listTy) (M.CCtor cons [ M.ALit (LitInt 2), M.ALocal (M.Local 0) ])
              ( M.ELet (M.Local 2) (RepData listTy) (M.CCtor cons [ M.ALit (LitInt 1), M.ALocal (M.Local 1) ])
                  (M.ETail (M.CCallKnown (value "sum") [ M.ALocal (M.Local 2) ]))
              )
          )
      )

  it "installs the group member as a closure and runs the nonrec" do
    -- `rec` installs without evaluating; `nonrec` is evaluated once, in order
    map _.globals lowered `shouldEqual` Right
      [ { ref: value "sum", init: M.GFunc (M.FuncId 0) }
      , { ref: value "result", init: M.GRun (M.FuncId 1) }
      ]

  it "carries the constructor table, tags and arities together" do
    map _.ctors lowered `shouldEqual` Right
      [ { ref: nil, owner: listTy, tag: 0, arity: 0, isNewtype: false }
      , { ref: cons, owner: listTy, tag: 1, arity: 2, isNewtype: false }
      ]

  it "declares no foreign of its own" do
    -- `Base.Int.add` belongs to the module that declares it
    map _.foreigns lowered `shouldEqual` Right []

  it "counts a foreign's arity off its declared spine" do
    -- `add : Int -> Int -> Int` takes two, and no instantiation changes that
    map _.foreigns loweredInt `shouldEqual` Right [ { ref: intAdd, arity: 2 } ]

  it "emits exactly the two functions the module needs" do
    map (\m -> map _.id m.functions) lowered `shouldEqual` Right [ M.FuncId 0, M.FuncId 1 ]

  describe "a local recursive group" do
    it "binds a member that is a function as a closure, and one that is none as a by-need cell, in the order written" do
      case programsMain of
        Left err -> fail err
        Right m -> case runOf "localMixed" m of
          Left err -> fail err
          Right f -> case f.body of
            M.ELetRec [ M.RecClosure go, M.RecNeed table ] rest -> do
              table.holds `shouldEqual` RepRec
              -- the initializer is the member's whole right-hand side, entered with nothing
              map _.params (functionIn m table.func) `shouldEqual` Just []
              -- `go` captures the cell itself, at `Val`, saying what it holds
              map (map (\c -> { rep: c.rep, holds: c.holds }) <<< _.captures) (functionIn m go.func) `shouldEqual` Just [ { rep: RepVal, holds: Just RepRec } ]
              -- and a reference to `table` in the body forces it
              String.contains (Pattern "CForce") (show rest) `shouldEqual` true
            other -> fail ("not a group of a closure and a cell: " <> show other)

-- | The tail of a chain of `let`s.
spine :: M.Expr -> M.Expr
spine = case _ of
  M.ELet _ _ _ rest -> spine rest
  other -> other
