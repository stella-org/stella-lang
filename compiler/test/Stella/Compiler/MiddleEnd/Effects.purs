-- | `translate`, over the handler slice and over regions.
-- |
-- | The slice is the effectful counterpart of the vertical slice: it performs an
-- | operation and interprets it twice over, once with a handler inside a region
-- | of cells. What each construct lowers to is written out in full, so that a
-- | difference from the Translation document is a defect in one of the two.
module Test.Stella.Compiler.MiddleEnd.Effects (spec) where

import Prelude

import Prim as P

-- Everything Mid IR offers is reached through the facade, which is what a
-- lowering imports. A member missing from its re-export list fails this module
-- rather than going unnoticed.
import Stella.Compiler.Primitive (PrimOp(..))
import Stella.Compiler.Interface (noImports)
import Stella.Compiler.MiddleEnd (Rep(..), TranslateError, translate, verify)
import Stella.Compiler.MiddleEnd as M
import Stella.Compiler.TypedCore (Decl(..), Export(..), Expr(..), Ident(..), Literal(..), Module, RegionName(..), RowEntry(..), RowKey(..), Symbol(..), Type(..), declare, declareAnnotated, monoScheme, primSignature)
import Stella.Compiler.TypedCore.Prim (fn, intTy, unitCtor, unitTy)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Test.Stella.Compiler.Fixtures.Programs (inInt, intName, mainName)
import Test.Stella.Compiler.TypedCore.HandlerSlice (always0Name, cellKey, counterEff, counterKey, counterName, handlerSlice, nextOp, seededSlice, twiceCountedName, twiceName)
import Test.Stella.Compiler.TypedCore.VerticalSlice (intModule)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

-- | The slice, checked and translated. `Base.Int` stands behind it for the
-- | arithmetic, as it does behind the vertical slice.
translated :: Module P.Int -> Either P.String M.Module
translated m = case declare primSignature intModule of
  Left _ -> Left "Base.Int did not declare"
  Right s1 -> case declareAnnotated s1 m of
    Left _ -> Left "the slice did not declare"
    Right declared -> case translate noImports m declared of
      Left err -> Left (show (err :: TranslateError))
      Right result -> Right result.module

functionOf :: Module P.Int -> P.Int -> Either P.String M.Function
functionOf m i = do
  mid <- translated m
  case Array.find (\f -> f.id == M.FuncId i) mid.functions of
    Just f -> Right f
    Nothing -> Left ("no function #" <> show i)

-- | `Prim.Unit`, which every operation of the slice takes and which the fast
-- | clause's write produces.
unit' :: Rep
unit' = RepData unitTy

performNext :: M.Comp
performNext = M.CPerform counterKey nextOp (M.ACtor unitCtor)

-- | The handler of the slice's one cell, whose clause is `fast` and captures
-- | what it is given: the identity of the region around the handler. The slice
-- | installs two of these, which differ in the functions they name and in the
-- | local the identity stands in.
countingHandler :: P.Int -> P.Int -> P.Array M.Atom -> M.Handler
countingHandler returnClause clause captures =
  { key: counterKey
  , returnClause: { func: M.FuncId returnClause, captures: [] }
  , opClauses:
      [ { op: nextOp
        , form: M.ClauseFast
        , clause: { func: M.FuncId clause, captures }
        }
      ]
  }

-- | The handler of `always0`: one `full` clause, and no region at all.
always0Handler :: M.Handler
always0Handler =
  { key: counterKey
  , returnClause: { func: M.FuncId 8, captures: [] }
  , opClauses:
      [ { op: nextOp, form: M.ClauseFull, clause: { func: M.FuncId 9, captures: [] } } ]
  }

-- Regions apart from handlers ---------------------------------------------------

-- | `( n : Int )`, the layout of every region of `regionModule`.
n :: RowKey
n = SymbolKey (Symbol "n")

int :: Type
int = TCon intTy []

unitType :: Type
unitType = TCon unitTy []

-- | `( region r | rest )`.
regionRow :: P.String -> Type -> Type
regionRow name rest = TRowExtend (RowRegionEntry (RegionName name)) rest

readN :: P.String -> Expr P.Int
readN name = ReadCell 0 (RegionName name) n

-- | `Base.Int.add x y` at `row`, each application widened to it.
addAt :: Type -> Expr P.Int -> Expr P.Int -> Expr P.Int
addAt row x y =
  App 0 (OpenEff 0 row (App 0 (OpenEff 0 row (Global 0 (inInt "add") [])) x)) y

regionOf :: P.String -> P.Int -> Expr P.Int -> Expr P.Int
regionOf name initial = Region 0 (RegionName name) [ { key: n, ty: int } ] [ Lit 0 (LitInt initial) ]

-- | Two values, each a region and nothing else of effects:
-- |
-- | - `nested`: `region [r] ( n : Int ) @ ( 1 ) in region [s] ( n : Int ) @ ( 2 ) in
-- |   readCell r.n + readCell s.n`. The two regions declare one key, and a read
-- |   names its region.
-- | - `closed`: `region [r] ( n : Int ) @ ( 3 ) in let f = λu. readCell r.n in f ()`.
regionModule :: Module P.Int
regionModule =
  { annotation: 0
  , name: mainName
  , imports: [ intName ]
  , exports: [ ExportValue (Ident "nested"), ExportValue (Ident "closed") ]
  , decls:
      [ value 1 "nested"
          ( regionOf "r" 1
              $ regionOf "s" 2
              $ addAt (regionRow "s" (regionRow "r" TRowEmpty)) (readN "r") (readN "s")
          )
      , value 2 "closed"
          ( regionOf "r" 3
              $ Let 0 (Ident "f") (fn unitType (regionRow "r" TRowEmpty) int)
                  (Lam 0 (Ident "u") unitType (readN "r"))
              $ App 0 (Var 0 (Ident "f")) (Global 0 unitCtor [])
          )
      ]
  }
  where
  value at name body =
    DeclNonRec at { name: Ident name, scheme: monoScheme int, value: body, attributes: [] }

spec :: Spec Unit
spec = describe "Stella.Compiler.MiddleEnd.Effects » the handler slice" do

  it "names each performed operation by its own name and its element's key" do
    -- nothing consults the ambient effect row, which is erased: a `perform`
    -- finds its handler by key, and the operation is looked up among the
    -- clauses of the one handler that key selected
    map _.body (functionOf handlerSlice 0) `shouldEqual` Right
      ( M.ELet (M.Local 1) RepInt performNext
          ( M.ELet (M.Local 2) RepInt performNext
              (M.ETail (M.CPrim IntAdd [ M.ALocal (M.Local 1), M.ALocal (M.Local 2) ]))
          )
      )

  it "opens a region with its keys and initial values, and enters its body" do
    -- the region's name and the cells' types were annotations the checker
    -- used; the keys give the cells their positions
    map _.body (functionOf handlerSlice 1) `shouldEqual` Right
      ( M.ETail
          ( M.CRegion [ cellKey ] (M.FuncId 2)
              [ M.ALocal (M.Local 0) ]
              [ M.ALit (LitInt 0) ]
          )
      )

  it "lifts a region's body into a function of the region's identity" do
    -- the handler's clause uses the region's cell, so it captures the identity
    functionOf handlerSlice 2 `shouldEqual` Right
      { id: M.FuncId 2
      , params: [ { local: M.Local 0, rep: RepVal } ]
      , captures: [ { local: M.Local 1, rep: RepClos } ]
      , body:
          M.ETail
            ( M.CHandle (countingHandler 4 5 [ M.ALocal (M.Local 0) ]) (M.FuncId 3)
                [ M.ALocal (M.Local 1) ]
            )
      }

  it "lifts the handled computation into a function of no parameters" do
    -- it is entered from the `handle` rather than run where it was written, so
    -- what it names it captures
    functionOf handlerSlice 3 `shouldEqual` Right
      { id: M.FuncId 3
      , params: []
      , captures: [ { local: M.Local 0, rep: RepClos } ]
      , body: M.ETail (M.CCallUnknown (M.ALocal (M.Local 0)) [ M.ACtor unitCtor ])
      }

  it "gives a fast clause one parameter and reaches a cell through the captured identity" do
    -- a `fast` clause binds the operation's argument alone, so implementing one
    -- asks nothing of a backend beyond an ordinary call (D28)
    functionOf handlerSlice 5 `shouldEqual` Right
      { id: M.FuncId 5
      , params: [ { local: M.Local 0, rep: unit' } ]
      , captures: [ { local: M.Local 1, rep: RepVal } ]
      , body:
          M.ELet (M.Local 2) RepInt (M.CReadCell (M.ALocal (M.Local 1)) 0)
            ( M.ELet (M.Local 3) RepInt
                (M.CPrim IntAdd [ M.ALocal (M.Local 2), M.ALit (LitInt 1) ])
                ( M.ELet (M.Local 4) unit' (M.CWriteCell (M.ALocal (M.Local 1)) 0 (M.ALocal (M.Local 3)))
                    (M.ERet (M.ALocal (M.Local 2)))
                )
            )
      }

  it "gives a full clause the argument and the continuation" do
    -- the continuation is an ordinary value of `Rep Clos`, applied by an
    -- ordinary unknown call, and nothing bounds how often
    functionOf handlerSlice 9 `shouldEqual` Right
      { id: M.FuncId 9
      , params:
          [ { local: M.Local 0, rep: unit' }
          , { local: M.Local 1, rep: RepClos }
          ]
      , captures: []
      , body: M.ETail (M.CCallUnknown (M.ALocal (M.Local 1)) [ M.ALit (LitInt 0) ])
      }

  it "installs a handler outside any region with nothing of one" do
    map _.body (functionOf handlerSlice 6) `shouldEqual` Right
      (M.ETail (M.CHandle always0Handler (M.FuncId 7) [ M.ALocal (M.Local 0) ]))

  it "binds an initial value that is a computation ahead of the region" do
    -- an initial value is evaluated before the region opens, so its binding
    -- stands outside the `region`
    map _.body (functionOf seededSlice 1) `shouldEqual` Right
      ( M.ELet (M.Local 1) RepInt
          (M.CPrim IntAdd [ M.ALit (LitInt 1), M.ALit (LitInt 2) ])
          ( M.ETail
              ( M.CRegion [ cellKey ] (M.FuncId 2)
                  [ M.ALocal (M.Local 0) ]
                  [ M.ALocal (M.Local 1) ]
              )
          )
      )

  it "binds a region whose value the rest of the body reads" do
    -- a `region` is a computation, so a `let` binds it like any other and
    -- whatever consumes the value is reached in the ordinary way
    map _.body (functionOf handlerSlice 10) `shouldEqual` Right
      ( M.ELet (M.Local 1) RepInt
          (M.CRegion [ cellKey ] (M.FuncId 11) [] [ M.ALit (LitInt 0) ])
          (M.ERet (M.ALocal (M.Local 1)))
      )
    map _.body (functionOf handlerSlice 11) `shouldEqual` Right
      ( M.ETail
          (M.CHandle (countingHandler 13 14 [ M.ALocal (M.Local 0) ]) (M.FuncId 12) [])
      )

  it "records the operations each effect declares, and no signature" do
    -- an operation's argument and resume types were consumed by type checking
    map _.effects (translated handlerSlice) `shouldEqual` Right
      [ { ref: counterEff, ops: [ nextOp ] } ]

  it "installs every value of the slice as a function, each a handler or not" do
    map _.globals (translated handlerSlice) `shouldEqual` Right
      [ { ref: twiceName, init: M.GFunc (M.FuncId 0) }
      , { ref: counterName, init: M.GFunc (M.FuncId 1) }
      , { ref: always0Name, init: M.GFunc (M.FuncId 6) }
      , { ref: twiceCountedName, init: M.GFunc (M.FuncId 10) }
      ]

  describe "regions" do
    it "names a cell by the identity of its region and its position there" do
      -- the inner region's body captures the outer's identity; the two declare
      -- one key, and which cell a read reaches is the identity it names. The
      -- argument is evaluated before the function (D35), so `s` is read first
      map _.body (functionOf regionModule 1) `shouldEqual` Right
        (M.ETail (M.CRegion [ n ] (M.FuncId 2) [ M.ALocal (M.Local 0) ] [ M.ALit (LitInt 2) ]))
      functionOf regionModule 2 `shouldEqual` Right
        { id: M.FuncId 2
        , params: [ { local: M.Local 0, rep: RepVal } ]
        , captures: [ { local: M.Local 1, rep: RepVal } ]
        , body:
            M.ELet (M.Local 2) RepInt (M.CReadCell (M.ALocal (M.Local 0)) 0)
              ( M.ELet (M.Local 3) RepInt (M.CReadCell (M.ALocal (M.Local 1)) 0)
                  (M.ETail (M.CPrim IntAdd [ M.ALocal (M.Local 3), M.ALocal (M.Local 2) ]))
              )
        }

    it "captures a region's identity in a closure over its cells" do
      functionOf regionModule 4 `shouldEqual` Right
        { id: M.FuncId 4
        , params: [ { local: M.Local 0, rep: RepVal } ]
        , captures: []
        , body:
            M.ELet (M.Local 1) RepClos (M.CClosure (M.FuncId 5) [ M.ALocal (M.Local 0) ])
              (M.ETail (M.CCallUnknown (M.ALocal (M.Local 1)) [ M.ACtor unitCtor ]))
        }
      functionOf regionModule 5 `shouldEqual` Right
        { id: M.FuncId 5
        , params: [ { local: M.Local 0, rep: unit' } ]
        , captures: [ { local: M.Local 1, rep: RepVal } ]
        , body: M.ETail (M.CReadCell (M.ALocal (M.Local 1)) 0)
        }

    it "leaves a module the verifier accepts" do
      map verify (translated regionModule) `shouldEqual` Right (Right unit)
      map verify (translated handlerSlice) `shouldEqual` Right (Right unit)
