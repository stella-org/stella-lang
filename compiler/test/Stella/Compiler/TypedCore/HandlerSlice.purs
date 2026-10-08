-- | The effectful counterpart of the vertical slice: a program that performs an
-- | operation, and two handlers that interpret it, written in Core by hand.
-- |
-- | `Base.Int` stands behind it for the arithmetic, as it does behind the
-- | vertical slice. `Main` declares one effect and four values.
-- |
-- | | Value | What it holds |
-- | | --- | --- |
-- | | `twice` | two `perform`s of one operation, under a Lacks constraint |
-- | | `counter` | a handler inside a region of cells, whose `fast` clause reads and writes one (D36) |
-- | | `always0` | a handler whose clause is `full`, so it binds the continuation (D28) |
-- | | `twiceCounted` | the two brought together, and the one `region` whose value a binding takes |
-- |
-- | The slice is carried through checking, translation, and lowering, and what
-- | each stage makes of it is written out where that stage is tested.
module Test.Stella.Compiler.TypedCore.HandlerSlice
  ( spec
  , handlerSlice
  , seededSlice
  , counterEff
  , counterKey
  , cellKey
  , nextOp
  , twiceName
  , counterName
  , always0Name
  , twiceCountedName
  ) where

import Prelude

import Prim as P

import Stella.Compiler.TypedCore (Cell, Constraint(..), DecisionTree(..), Decl(..), EffName(..), Expr(..), Handler, Ident(..), Kind(..), KindError(..), Literal(..), Module, ModuleName(..), OpClause(..), OpName(..), Qualified(..), RegionName(..), RowElemKind(..), RowEntry(..), RowKey(..), Symbol(..), TyVar(..), Type(..), TypeScheme, monoScheme)
import Stella.Compiler.TypedCore.Check (CheckError(..))
import Stella.Compiler.TypedCore.Declare (DeclError(..), DeclFailure, declare)
import Stella.Compiler.TypedCore.Prim (fn, intTy, primSignature, unitCtor, unitTy)
import Stella.Compiler.TypedCore.Signature (Signature, lookupValue)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Test.Stella.Compiler.TypedCore.VerticalSlice (intModule)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

-- Names -----------------------------------------------------------------------

mainModuleName :: ModuleName
mainModuleName = ModuleName "Main"

intModuleName :: ModuleName
intModuleName = ModuleName "Base.Int"

counterEff :: Qualified EffName
counterEff = Qualified mainModuleName (EffName "Counter")

-- | The key of the element a handler of `Counter` removes, derived from the
-- | effect at the head of the payload (D16).
counterKey :: RowKey
counterKey = EffectKey counterEff

-- | The key of the one cell the region declares, which is the name the surface
-- | wrote its `var` under.
cellKey :: RowKey
cellKey = SymbolKey (Symbol "n")

nextOp :: OpName
nextOp = OpName "next"

twiceName :: Qualified Ident
twiceName = Qualified mainModuleName (Ident "twice")

counterName :: Qualified Ident
counterName = Qualified mainModuleName (Ident "counter")

always0Name :: Qualified Ident
always0Name = Qualified mainModuleName (Ident "always0")

twiceCountedName :: Qualified Ident
twiceCountedName = Qualified mainModuleName (Ident "twiceCounted")

intAdd :: Qualified Ident
intAdd = Qualified intModuleName (Ident "add")

-- Types -----------------------------------------------------------------------

int :: Type
int = TCon intTy []

unit' :: Type
unit' = TCon unitTy []

-- | `e`, the residual row every signature here leaves open.
rowVar :: Type
rowVar = TVar (TyVar "e")

tyVarA :: Type
tyVarA = TVar (TyVar "a")

-- | `r`, the name of the region `counter` opens.
regionName :: RegionName
regionName = RegionName "r"

-- | `( Counter | e )`
counterRow :: Type
counterRow = TRowExtend (RowEffectEntry counterEff []) rowVar

-- | `( region r | e )`, the row everything inside the region stands at: the
-- | handled computation, and the clauses and the return clause of the handler.
clauseRow :: Type
clauseRow = TRowExtend (RowRegionEntry regionName) rowVar

-- | `( region r )`, what the thunk is widened by.
regionAlone :: Type
regionAlone = TRowExtend (RowRegionEntry regionName) TRowEmpty

counterLacks :: Constraint
counterLacks = Lacks counterKey rowVar

-- The module ------------------------------------------------------------------

handlerSlice :: Module P.Int
handlerSlice = sliceWith counterDecl

-- | The slice with the cell seeded by an application rather than a literal. An
-- | initial value is evaluated at each application of the handler, before the
-- | region is opened, so it stands at `e` and is widened like any other pure
-- | function called there (D8).
seededSlice :: Module P.Int
seededSlice = sliceWith (counterDeclOf seededInitial)

sliceWith :: Decl P.Int -> Module P.Int
sliceWith counter =
  { annotation: 0
  , name: mainModuleName
  , imports: [ intModuleName ]
  , exports: []
  , decls: [ counterEffectDecl, twiceDecl, counter, always0Decl, twiceCountedDecl ]
  }

-- | `effect Counter where next : Unit ->* Int`.
counterEffectDecl :: Decl P.Int
counterEffectDecl = DeclEffect 1
  { name: EffName "Counter"
  , params: []
  , operations:
      [ { name: nextOp, tyBinders: [], argument: unit', resumesWith: int } ]
  , attributes: []
  }

-- twice -----------------------------------------------------------------------

-- | `forall (e : Row Effect). Counter ∉ e => Unit -{ ( Counter | e ) }-> Int`
twiceScheme :: TypeScheme
twiceScheme = monoScheme
  ( TForall (TyVar "e") (KRow RowEffect)
      (TConstrained counterLacks (fn unit' counterRow int))
  )

-- | Two performs, then their sum. Nothing installs a handler: what `perform`
-- | requires is the key in the ambient row, and an unhandled effect is an
-- | obligation a caller takes on.
twiceDecl :: Decl P.Int
twiceDecl = DeclNonRec 2
  { name: Ident "twice"
  , scheme: twiceScheme
  , value:
      TyLam 0 (TyVar "e") (KRow RowEffect)
        $ ConstraintLam 0 counterLacks
        $ Lam 0 (Ident "u") unit'
        $ Let 0 (Ident "a") int performNext
        $ Let 0 (Ident "b") int performNext
        $ added counterRow (Var 0 (Ident "a")) (Var 0 (Ident "b"))
  , attributes: []
  }

performNext :: Expr P.Int
performNext = Perform 0 counterKey nextOp [] (Global 0 unitCtor [])

-- | `Base.Int.add x y` at an ambient row that is not empty. The arrows of a
-- | foreign are pure, and containment is never inserted, so each argument the
-- | application consumes carries a widening of its own (D8).
added :: Type -> Expr P.Int -> Expr P.Int -> Expr P.Int
added row x y =
  App 0 (OpenEff 0 row (App 0 (OpenEff 0 row (Global 0 intAdd [])) x)) y

-- counter ---------------------------------------------------------------------

-- | `forall (e : Row Effect). forall (a : Type). Counter ∉ e =>`
-- | `( Unit -{ ( Counter | e ) }-> a ) -{ e }-> a`
-- |
-- | The scheme says nothing of regions. The region `counter` opens is bound in
-- | its own body, so no row of the caller's can hold it, and `counter` applies
-- | wherever its residual row allows, inside another region included (D36).
counterScheme :: TypeScheme
counterScheme = monoScheme
  ( TForall (TyVar "e") (KRow RowEffect)
      ( TForall (TyVar "a") KType
          (TConstrained counterLacks (fn (fn unit' counterRow tyVarA) rowVar tyVarA))
      )
  )

counterDecl :: Decl P.Int
counterDecl = counterDeclOf (Lit 0 (LitInt 0))

counterDeclOf :: Expr P.Int -> Decl P.Int
counterDeclOf initial = DeclNonRec 3
  { name: Ident "counter"
  , scheme: counterScheme
  , value: counterValue initial
  , attributes: []
  }

-- | The initial value as an application, which is what puts a binding ahead of
-- | the `region` it belongs to.
seededInitial :: Expr P.Int
seededInitial = added rowVar (Lit 0 (LitInt 1)) (Lit 0 (LitInt 2))

-- | `region [r] ( n : Int ) @ ( initial ) in handle (openEff [( region r )] thunk)
-- | () with …`. The thunk's row does not hold the region, which is opened inside
-- | `counter`, so it is widened to the row the handled computation stands at.
counterValue :: Expr P.Int -> Expr P.Int
counterValue initial =
  TyLam 0 (TyVar "e") (KRow RowEffect)
    $ TyLam 0 (TyVar "a") KType
    $ ConstraintLam 0 counterLacks
    $ Lam 0 (Ident "thunk") (fn unit' counterRow tyVarA)
    $ Region 0 regionName cellLayout [ initial ]
    $ Handle 0
        (App 0 (OpenEff 0 regionAlone (Var 0 (Ident "thunk"))) (Global 0 unitCtor []))
        counterHandler

-- | `( n : Int )`. The layout is a written sequence and therefore closed, which
-- | is what lets one initial value be given per key.
cellLayout :: P.Array Cell
cellLayout = [ { key: cellKey, ty: int } ]

-- | The handler of `counter`: a `fast` clause that hands back the count and
-- | leaves the cell one higher.
-- |
-- | A `fast` clause binds no continuation and its body has the type the
-- | operation resumes with, so handling an operation captures nothing (D28).
counterHandler :: Handler P.Int
counterHandler =
  { element: RowEffectEntry counterEff []
  , returnClause: { binder: Ident "x", ty: tyVarA, body: Var 0 (Ident "x") }
  , opClauses:
      [ FastClause
          { op: nextOp
          , tyBinders: []
          , argBinder: { name: Ident "u", ty: unit' }
          , body:
              Let 0 (Ident "v") int (ReadCell 0 regionName cellKey)
                $ Let 0 (Ident "w") unit'
                    (WriteCell 0 regionName cellKey (added clauseRow (Var 0 (Ident "v")) (Lit 0 (LitInt 1))))
                $ Var 0 (Ident "v")
          }
      ]
  }

-- always0 ---------------------------------------------------------------------

-- | `forall (e : Row Effect). Counter ∉ e => forall (a : Type).`
-- | `( Unit -{ ( Counter | e ) }-> a ) -{ e }-> a`
always0Scheme :: TypeScheme
always0Scheme = monoScheme
  ( TForall (TyVar "e") (KRow RowEffect)
      ( TConstrained counterLacks
          (TForall (TyVar "a") KType (fn (fn unit' counterRow tyVarA) rowVar tyVarA))
      )
  )

-- | A handler that resumes with a fixed value. The clause is `full`, so it binds
-- | the continuation `Int -{e}-> a`: resuming returns under the same handler,
-- | which is what makes handlers deep (D15).
always0Decl :: Decl P.Int
always0Decl = DeclNonRec 4
  { name: Ident "always0"
  , scheme: always0Scheme
  , value:
      TyLam 0 (TyVar "e") (KRow RowEffect)
        $ ConstraintLam 0 counterLacks
        $ TyLam 0 (TyVar "a") KType
        $ Lam 0 (Ident "thunk") (fn unit' counterRow tyVarA)
        $ Handle 0 (App 0 (Var 0 (Ident "thunk")) (Global 0 unitCtor []))
            { element: RowEffectEntry counterEff []
            , returnClause: { binder: Ident "x", ty: tyVarA, body: Var 0 (Ident "x") }
            , opClauses:
                [ FullClause
                    { op: nextOp
                    , tyBinders: []
                    , argBinder: { name: Ident "u", ty: unit' }
                    , contBinder: { name: Ident "k", ty: fn int rowVar tyVarA }
                    , body: App 0 (Var 0 (Ident "k")) (Lit 0 (LitInt 0))
                    }
                ]
            }
  , attributes: []
  }

-- twiceCounted ----------------------------------------------------------------

-- | `forall (e : Row Effect). Counter ∉ e => Unit -{ e }-> Int`
twiceCountedScheme :: TypeScheme
twiceCountedScheme = monoScheme
  ( TForall (TyVar "e") (KRow RowEffect)
      (TConstrained counterLacks (fn unit' rowVar int))
  )

-- | The one value that binds a `region` rather than standing at one: the count
-- | `twice` produces is what the rest of the body reads. `twice` is instantiated
-- | at a row holding the region, which its own row variable admits: a row
-- | variable bound outside the region is known to lack its key.
twiceCountedDecl :: Decl P.Int
twiceCountedDecl = DeclNonRec 5
  { name: Ident "twiceCounted"
  , scheme: twiceCountedScheme
  , value:
      TyLam 0 (TyVar "e") (KRow RowEffect)
        $ ConstraintLam 0 counterLacks
        $ Lam 0 (Ident "u") unit'
        $ Let 0 (Ident "n") int
            ( Region 0 regionName cellLayout [ Lit 0 (LitInt 0) ]
                ( Handle 0
                    ( App 0
                        (ConstraintApp 0 (TyApp 0 (Global 0 twiceName []) clauseRow))
                        (Global 0 unitCtor [])
                    )
                    (countingHandler int)
                )
            )
        $ Var 0 (Ident "n")
  , attributes: []
  }

-- | The handler of `counter` at an answer type of its own.
countingHandler :: Type -> Handler P.Int
countingHandler answer =
  counterHandler { returnClause = { binder: Ident "x", ty: answer, body: Var 0 (Ident "x") } }

-- Running the checker ---------------------------------------------------------

checkedSignature :: Module P.Int -> Either (DeclFailure P.Int) Signature
checkedSignature m = do
  imported <- declare primSignature intModule
  declare imported m

verdict :: Module P.Int -> Either DeclError Unit
verdict m = case checkedSignature m of
  Left failure -> Left failure.error
  Right _ -> Right unit

valueScheme :: Qualified Ident -> Maybe TypeScheme
valueScheme name = case checkedSignature handlerSlice of
  Left _ -> Nothing
  Right sig -> map _.scheme (lookupValue sig name)

-- Mutations -------------------------------------------------------------------

-- | `counter` with its `region` dropped and its clause left as it was. The
-- | clause names a region no binder in scope opens.
withoutRegion :: Module P.Int
withoutRegion = sliceWith
  ( DeclNonRec 3
      { name: Ident "counter"
      , scheme: counterScheme
      , value:
          TyLam 0 (TyVar "e") (KRow RowEffect)
            $ TyLam 0 (TyVar "a") KType
            $ ConstraintLam 0 counterLacks
            $ Lam 0 (Ident "thunk") (fn unit' counterRow tyVarA)
            $ Handle 0 (App 0 (Var 0 (Ident "thunk")) (Global 0 unitCtor []))
                counterHandler
      , attributes: []
      }
  )

-- | `counter` with the thunk not widened by the region: the handled computation
-- | stands at a row the thunk's arrow does not equal.
withoutWidening :: Module P.Int
withoutWidening = sliceWith
  ( DeclNonRec 3
      { name: Ident "counter"
      , scheme: counterScheme
      , value:
          TyLam 0 (TyVar "e") (KRow RowEffect)
            $ TyLam 0 (TyVar "a") KType
            $ ConstraintLam 0 counterLacks
            $ Lam 0 (Ident "thunk") (fn unit' counterRow tyVarA)
            $ Region 0 regionName cellLayout [ Lit 0 (LitInt 0) ]
            $ Handle 0 (App 0 (Var 0 (Ident "thunk")) (Global 0 unitCtor []))
                counterHandler
      , attributes: []
      }
  )

-- | A value whose own declaration opens a region and hands out a function over
-- | its cell: the function's arrow carries the region, which may not outlive it.
withEscape :: Module P.Int
withEscape = sliceWith
  ( DeclNonRec 3
      { name: Ident "counter"
      , scheme: counterScheme
      , value:
          TyLam 0 (TyVar "e") (KRow RowEffect)
            $ TyLam 0 (TyVar "a") KType
            $ ConstraintLam 0 counterLacks
            $ Lam 0 (Ident "thunk") (fn unit' counterRow tyVarA)
            $ Case 0
                [ Region 0 regionName cellLayout [ Lit 0 (LitInt 0) ]
                    (Lam 0 (Ident "y") unit' (ReadCell 0 regionName cellKey))
                ]
            $ Leaf (Var 0 (Ident "thunk"))
      , attributes: []
      }
  )

-- | `counter` with a second region of the same name opened inside the first.
withShadowingRegion :: Module P.Int
withShadowingRegion = sliceWith
  ( DeclNonRec 3
      { name: Ident "counter"
      , scheme: counterScheme
      , value:
          TyLam 0 (TyVar "e") (KRow RowEffect)
            $ TyLam 0 (TyVar "a") KType
            $ ConstraintLam 0 counterLacks
            $ Lam 0 (Ident "thunk") (fn unit' counterRow tyVarA)
            $ Region 0 regionName cellLayout [ Lit 0 (LitInt 0) ]
            $ Region 0 regionName cellLayout [ Lit 0 (LitInt 0) ]
            $ Handle 0
                (App 0 (OpenEff 0 regionAlone (Var 0 (Ident "thunk"))) (Global 0 unitCtor []))
                counterHandler
      , attributes: []
      }
  )

-- | A function bound inside the region, polymorphic in a row it extends with the
-- | region. Its row variable is bound inside the region, so the region's key is
-- | not known to be absent from it: the function must assume it, and is refused
-- | where it does not.
withInnerRowVariable :: P.Boolean -> Module P.Int
withInnerRowVariable assumes = sliceWith
  ( DeclNonRec 3
      { name: Ident "counter"
      , scheme: counterScheme
      , value:
          TyLam 0 (TyVar "e") (KRow RowEffect)
            $ TyLam 0 (TyVar "a") KType
            $ ConstraintLam 0 counterLacks
            $ Lam 0 (Ident "thunk") (fn unit' counterRow tyVarA)
            $ Region 0 regionName cellLayout [ Lit 0 (LitInt 0) ]
            $ Let 0 (Ident "peek") peekType peek
            $ Handle 0
                (App 0 (OpenEff 0 regionAlone (Var 0 (Ident "thunk"))) (Global 0 unitCtor []))
                counterHandler
      , attributes: []
      }
  )
  where
  innerRow = TRowExtend (RowRegionEntry regionName) (TVar (TyVar "t"))
  innerLacks = Lacks (RegionKey regionName) (TVar (TyVar "t"))
  peekArrow = fn unit' innerRow int
  peekType =
    TForall (TyVar "t") (KRow RowEffect)
      (if assumes then TConstrained innerLacks peekArrow else peekArrow)
  peekBody = Lam 0 (Ident "q") unit' (ReadCell 0 regionName cellKey)
  peek =
    TyLam 0 (TyVar "t") (KRow RowEffect)
      (if assumes then ConstraintLam 0 innerLacks peekBody else peekBody)

-- The specification -----------------------------------------------------------

spec :: Spec Unit
spec = describe "Stella.Compiler.TypedCore.HandlerSlice" do
  describe "the slice" do
    it "passes declaration checking, handlers and regions together" do
      verdict handlerSlice `shouldEqual` Right unit

    it "passes it with the cell seeded by an application" do
      verdict seededSlice `shouldEqual` Right unit

    it "records the performing function at the row its operation stands in" do
      valueScheme twiceName `shouldEqual` Just twiceScheme

    it "records each handler as a function of a thunk, its effect removed and no region in its type" do
      valueScheme counterName `shouldEqual` Just counterScheme
      valueScheme always0Name `shouldEqual` Just always0Scheme

  describe "mutations of it" do
    it "refuses a readCell naming a region no binder in scope opens" do
      verdict withoutRegion `shouldEqual` Left (IllTyped (IllKindedType (UnboundRegion regionName)))

    it "refuses a handled computation whose row lacks the region it stands in" do
      case verdict withoutWidening of
        Left (IllTyped (RowMismatch _ _)) -> pure unit
        other -> fail ("expected a row mismatch: " <> show other)

    it "refuses a function over a cell outliving its region" do
      verdict withEscape `shouldEqual` Left (IllTyped (RegionEscapes regionName))

    it "refuses a region binder of a name already bound" do
      verdict withShadowingRegion `shouldEqual` Left (IllTyped (RegionBinderShadows regionName))

    it "refuses a row variable bound inside the region extended by it, and accepts one assumed to lack it" do
      case verdict (withInnerRowVariable false) of
        Left (IllTyped (IllKindedType (NotSharp (RegionKey name) _))) -> name `shouldEqual` regionName
        other -> fail ("expected the row to be refused: " <> show other)
      verdict (withInnerRowVariable true) `shouldEqual` Right unit
