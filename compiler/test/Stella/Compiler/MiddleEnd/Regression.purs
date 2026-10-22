-- | Cases in which a plausible translation gives the wrong answer.
-- |
-- | Each fixture is a module written in Core by hand, checked, and lowered. What
-- | is asserted is the Mid IR, so a translation that computes the right value by
-- | a different route still fails.
module Test.Stella.Compiler.MiddleEnd.Regression (spec) where

import Prelude

import Prim as P

import Stella.Compiler.Interface (noImports)
import Stella.Compiler.MiddleEnd (Rep(..), TranslateError, translate)
import Stella.Compiler.MiddleEnd as M
import Stella.Compiler.TypedCore (Constraint(..), Decl(..), Expr(..), Ident(..), JoinName(..), Kind(..), Literal(..), Module, ModuleName(..), Qualified(..), RowElemKind(..), RowEntry(..), RowKey(..), Symbol(..), TyVar(..), Type(..), declareAnnotated, intTy, monoScheme, primSignature, pureFn, recordTy, variantTy)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

main :: ModuleName
main = ModuleName "Main"

value :: P.String -> Qualified Ident
value name = Qualified main (Ident name)

int :: Type
int = TCon intTy []

record :: Type -> Type
record row = TApp (TCon recordTy []) row

nameKey :: RowKey
nameKey = SymbolKey (Symbol "name")

aKey :: RowKey
aKey = SymbolKey (Symbol "a")

-- | Check a module and lower it.
lower :: Module P.Int -> Either P.String { module :: M.Module, debug :: M.Debug P.Int }
lower m = case declareAnnotated primSignature m of
  Left _ -> Left "the fixture did not declare"
  Right declared -> case translate noImports m declared of
    Left err -> Left (show (err :: TranslateError))
    Right result -> Right result

bodyOf :: Module P.Int -> P.Int -> Either P.String M.Expr
bodyOf m i = do
  result <- lower m
  case Array.find (\f -> f.id == M.FuncId i) result.module.functions of
    Just f -> Right f.body
    Nothing -> Left ("no function #" <> show i)

moduleOf :: P.Array (Decl P.Int) -> Module P.Int
moduleOf decls = { annotation: 0, name: main, imports: [], exports: [], decls }

-- The update fixture ----------------------------------------------------------

-- | `nonrec Main.upd : Record ( name : Record ( a : Int ) )
-- |    = update name (extend name 1 {}) (extend a 2 {})`
-- |
-- | Both operands are computations, so which is emitted first is visible.
updateModule :: Module P.Int
updateModule = moduleOf
  [ DeclNonRec 1
      { name: Ident "upd"
      , scheme: monoScheme (record (TRowExtend (RowTypeEntry nameKey inner) TRowEmpty))
      , value:
          RecordUpdate 0 nameKey
            (RecordExtend 0 nameKey (Lit 0 (LitInt 1)) (RecordEmpty 0))
            (RecordExtend 0 aKey (Lit 0 (LitInt 2)) (RecordEmpty 0))
      , attributes: []
      }
  ]
  where
  inner = record (TRowExtend (RowTypeEntry aKey int) TRowEmpty)

-- The wrapper fixture ---------------------------------------------------------

identity' :: Expr P.Int
identity' = Lam 0 (Ident "x") int TRowEmpty (Var 0 (Ident "x"))

-- | Three definitions of `Int -> Int`, each a lambda under a wrapper erasure
-- | removes, and one call site for each.
wrapperModule :: Module P.Int
wrapperModule = moduleOf
  [ DeclNonRec 1
      { name: Ident "viaTyApp"
      , scheme: monoScheme (pureFn int int)
      , value: TyApp 0 (TyLam 0 (TyVar "a") KType (Lam 0 (Ident "x") (TVar (TyVar "a")) TRowEmpty (Var 0 (Ident "x")))) int
      , attributes: []
      }
  , DeclNonRec 2
      { name: Ident "viaOpen"
      , scheme: monoScheme (pureFn int int)
      , value: OpenEff 0 TRowEmpty identity'
      , attributes: []
      }
  , DeclNonRec 3
      { name: Ident "viaCon"
      , scheme: monoScheme (pureFn int int)
      , value: ConstraintApp 0 (ConstraintLam 0 (Lacks nameKey TRowEmpty) identity')
      , attributes: []
      }
  , DeclNonRec 4
      { name: Ident "calls"
      , scheme: monoScheme int
      , value:
          App 0 (Global 0 (value "viaCon") [])
            ( App 0 (Global 0 (value "viaOpen") [])
                (App 0 (Global 0 (value "viaTyApp") []) (Lit 0 (LitInt 1)))
            )
      , attributes: []
      }
  ]

-- The join point fixture -------------------------------------------------------

-- | `nonrec Main.id : Int -> Int = λx. x` and
-- | `nonrec Main.joined : Int = Main.id (letjoin j (n : Int) : Int = n in jump j 1)`.
-- |
-- | The join point is bound in argument position and jumped to from its
-- | continuation, which relative scoping of join points admits (D50).
joinModule :: Module P.Int
joinModule = moduleOf
  [ DeclNonRec 1
      { name: Ident "id", scheme: monoScheme (pureFn int int), value: identity', attributes: [] }
  , DeclNonRec 2
      { name: Ident "joined"
      , scheme: monoScheme int
      , value:
          App 0 (Global 0 (value "id") [])
            ( LetJoin 0 (JoinName "j") [ { name: Ident "n", ty: int } ] int (Var 0 (Ident "n"))
                (Jump 0 (JoinName "j") [ Lit 0 (LitInt 1) ])
            )
      , attributes: []
      }
  ]

-- The debug fixture ------------------------------------------------------------

-- | Annotations chosen so that the lambda node and its body differ: the lambda
-- | is `10` and the `Var` beneath it `11`.
-- |
-- | `letName` binds a computation to `y` and then aliases it to `z`, so the two
-- | paths a name can take are both present.
debugModule :: Module P.Int
debugModule = moduleOf
  [ DeclNonRec 1
      { name: Ident "named"
      , scheme: monoScheme (pureFn int int)
      , value: Lam 10 (Ident "x") int TRowEmpty (Var 11 (Ident "x"))
      , attributes: []
      }
  , DeclNonRec 2
      { name: Ident "letName"
      , scheme: monoScheme int
      , value:
          Let 20 (Ident "y") int
            (RecordSelect 0 aKey (RecordExtend 0 aKey (Lit 0 (LitInt 1)) (RecordEmpty 0)))
            (Let 0 (Ident "z") int (Var 0 (Ident "y")) (Var 0 (Ident "z")))
      , attributes: []
      }
  -- a lambda that is not the head of a run, so the wrapper over it is the
  -- outermost node of its own run and its annotation is the one at issue
  , DeclNonRec 3
      { name: Ident "wrapped"
      , scheme: monoScheme (record (TRowExtend (RowTypeEntry aKey (pureFn int int)) TRowEmpty))
      , value:
          RecordExtend 40 aKey
            (OpenEff 30 TRowEmpty (Lam 10 (Ident "y") int TRowEmpty (Var 11 (Ident "y"))))
            (RecordEmpty 0)
      , attributes: []
      }
  ]

-- The foreign instance fixture ------------------------------------------------

-- | `foreign Main.pick : forall (r : Row Type). (name ∉ r) => Int -> forall a. a -> a`
-- | and `nonrec Main.picked : Int = Main.pick [()] [•] 1 [Int] 2`.
-- |
-- | The chain carries a type and a constraint argument before its first value
-- | and a type argument between its values; only the values reach the call.
foreignModule :: Module P.Int
foreignModule = moduleOf
  [ DeclForeign 1
      { name: Ident "pick"
      , scheme:
          monoScheme
            ( TForall r (KRow RowType)
                (TConstrained (Lacks nameKey (TVar r)) (pureFn int (TForall a KType (pureFn (TVar a) (TVar a)))))
            )
      , attributes: []
      }
  , DeclNonRec 2
      { name: Ident "picked"
      , scheme: monoScheme int
      , value:
          App 0
            (TyApp 0 (App 0 (ConstraintApp 0 (TyApp 0 (Global 0 (value "pick") []) TRowEmpty)) (Lit 0 (LitInt 1))) int)
            (Lit 0 (LitInt 2))
      , attributes: []
      }
  ]
  where
  r = TyVar "r"
  a = TyVar "a"

-- The weaken fixture ----------------------------------------------------------

bKey :: RowKey
bKey = SymbolKey (Symbol "b")

cKey :: RowKey
cKey = SymbolKey (Symbol "c")

variant :: Type -> Type
variant row = TApp (TCon variantTy []) row

-- | `weaken k [τ] (f x)` — an application under a wrapper that produces a
-- | variant rather than a function, so nothing else in the term strips it.
weakenModule :: Module P.Int
weakenModule = moduleOf
  [ DeclNonRec 1
      { name: Ident "mkVariant"
      , scheme: monoScheme (pureFn int (variant (TRowExtend (RowTypeEntry bKey int) TRowEmpty)))
      , value: Lam 0 (Ident "x") int TRowEmpty (VariantInject 0 bKey TRowEmpty (Var 0 (Ident "x")))
      , attributes: []
      }
  , DeclNonRec 2
      { name: Ident "weakened"
      , scheme:
          monoScheme
            ( variant
                (TRowExtend (RowTypeEntry cKey int) (TRowExtend (RowTypeEntry bKey int) TRowEmpty))
            )
      , value:
          VariantWeaken 0 cKey int
            (App 0 (Global 0 (value "mkVariant") []) (Lit 0 (LitInt 1)))
      , attributes: []
      }
  ]

spec :: Spec Unit
spec = describe "Stella.Compiler.MiddleEnd.Translate » cases a plausible translation gets wrong" do

  describe "the operands of an update" do

    it "emits the record before the value, and passes them in that order" do
      -- `update k e1 e2` takes the record first, so it is what reaches a value
      -- first. Swapping the two reverses both the bindings and the arguments
      bodyOf updateModule 0 `shouldEqual` Right
        ( M.ELet (M.Local 0) RepRec M.CRecordEmpty
            ( M.ELet (M.Local 1) RepRec (M.CRecordExtend nameKey (M.ALit (LitInt 1)) (M.ALocal (M.Local 0)))
                ( M.ELet (M.Local 2) RepRec M.CRecordEmpty
                    ( M.ELet (M.Local 3) RepRec (M.CRecordExtend aKey (M.ALit (LitInt 2)) (M.ALocal (M.Local 2)))
                        (M.ETail (M.CRecordUpdate nameKey (M.ALocal (M.Local 1)) (M.ALocal (M.Local 3))))
                    )
                )
            )
        )

  describe "the definitional arity of a wrapped right-hand side" do

    it "sees through every wrapper erasure removes, so each call is known" do
      -- a run stopping at `openEff`, `[τ]`, or `[•]` reads the definition as
      -- taking no argument, and every call to it degrades to `CCallUnknown`
      bodyOf wrapperModule 3 `shouldEqual` Right
        ( M.ELet (M.Local 0) RepInt (M.CCallKnown (value "viaTyApp") [ M.ALit (LitInt 1) ])
            ( M.ELet (M.Local 1) RepInt (M.CCallKnown (value "viaOpen") [ M.ALocal (M.Local 0) ])
                (M.ETail (M.CCallKnown (value "viaCon") [ M.ALocal (M.Local 1) ]))
            )
        )

    it "installs the lambda under the wrapper as the function itself" do
      -- what a global holds is decided by the shape of its right-hand side and
      -- not by the form of its declaration, so the arity a known call supplies
      -- is the arity of the function the global was installed from
      bodyOf wrapperModule 0 `shouldEqual` Right (M.ERet (M.ALocal (M.Local 0)))
      let inits = map (map _.init <<< _.module.globals) (lower wrapperModule)
      inits `shouldEqual` Right
        [ M.GFunc (M.FuncId 0)
        , M.GFunc (M.FuncId 1)
        , M.GFunc (M.FuncId 2)
        , M.GRun (M.FuncId 3)
        ]

  describe "an application under a wrapper" do

    it "peels the spine through the wrapper rather than handing the term back" do
      -- `weaken` produces a variant rather than a function, so nothing but the
      -- peel strips it. A peel that stopped there would return the term it was
      -- given with no arguments taken off, and the head would be atomized into
      -- the same term again
      bodyOf weakenModule 1 `shouldEqual` Right
        (M.ETail (M.CCallKnown (value "mkVariant") [ M.ALit (LitInt 1) ]))

  describe "the numbering of locals" do

    it "starts from zero in each function" do
      -- a `Local` is unique within a function and not beyond one, so a backend
      -- maps one onto a frame slot without renaming
      let
        firstParams = do
          result <- lower wrapperModule
          Right (map (\f -> map _.local f.params) result.module.functions)
      firstParams `shouldEqual` Right
        [ [ M.Local 0 ], [ M.Local 0 ], [ M.Local 0 ], [] ]

  describe "a join point in argument position" do
    it "binds the call as a join point the inner one jumps to" do
      let
        found = do
          result <- lower joinModule
          Right (Array.find isJoin (map _.body result.module.functions))
        isJoin = case _ of
          M.ELetJoin _ _ _ _ -> true
          _ -> false
      -- the definition receives the inner join point's result and makes the call;
      -- the inner join point, from its continuation, jumps to it
      found `shouldEqual` Right
        ( Just
            ( M.ELetJoin (M.JoinId 0) [ { local: M.Local 0, rep: RepInt } ]
                (M.ETail (M.CCallKnown (value "id") [ M.ALocal (M.Local 0) ]))
                ( M.ELetJoin (M.JoinId 1) [ { local: M.Local 1, rep: RepInt } ]
                    (M.EJump (M.JoinId 0) [ M.ALocal (M.Local 1) ])
                    (M.EJump (M.JoinId 1) [ M.ALit (LitInt 1) ])
                )
            )
        )

  describe "a polymorphic foreign's chain" do
    it "passes the value arguments alone, the instance staying behind" do
      -- the instance is what the typed semantics hands a foreign's adapter, and
      -- erasure removes it: the implementation is called with the two values
      let
        calls = do
          result <- lower foreignModule
          Right (Array.filter isForeignCall (map _.body result.module.functions))
        isForeignCall = case _ of
          M.ETail (M.CForeign _ _) -> true
          _ -> false
      calls `shouldEqual` Right
        [ M.ETail (M.CForeign (value "pick") [ M.ALit (LitInt 1), M.ALit (LitInt 2) ]) ]

  describe "the debug table" do

    it "names the function each global is installed from, and no other" do
      let
        names m = do
          result <- lower m
          Right (map _.name (Array.fromFoldable (Map.values result.debug.functions)))
      -- every function of the wrapper fixture is a global's
      names wrapperModule `shouldEqual` Right
        [ Just (value "viaTyApp")
        , Just (value "viaOpen")
        , Just (value "viaCon")
        , Just (value "calls")
        ]
      -- `wrapped` holds a lambda inside a record, which is lifted out of a body
      -- rather than installed from a global and so has no name
      names debugModule `shouldEqual` Right
        [ Just (value "named")
        , Just (value "letName")
        , Just (value "wrapped")
        , Nothing
        ]

    it "records the annotation of the term the function was made from" do
      -- the outermost node of the run, not the body left after the lambdas come
      -- off, and not the lambda left after the wrappers come off:
      --   #0 `named`, from a `Lam` annotated 10 over a `Var` annotated 11
      --   #1 `letName`, from a `Let` annotated 20
      --   #2 `wrapped`, from a `RecordExtend` annotated 40
      --   #3 the lambda inside it, from an `openEff` annotated 30 over a `Lam`
      --      annotated 10
      let
        sources = do
          result <- lower debugModule
          Right (map _.source (Array.fromFoldable (Map.values result.debug.functions)))
      sources `shouldEqual` Right [ Just 10, Just 20, Just 40, Just 30 ]

    it "names a local per function, and only where one was created for a name" do
      -- `x` is a parameter of #0; `y` is the local the `let` created in #1, and
      -- `z` aliases it rather than making one of its own. The two records `y`
      -- is built from were created for no name and appear nowhere. #3 binds a
      -- `y` of its own, a local being named within the function it belongs to
      let
        locals = do
          result <- lower debugModule
          Right
            ( map (\(Tuple f m) -> Tuple f (Map.toUnfoldable m :: P.Array (Tuple M.Local Ident)))
                (Map.toUnfoldable result.debug.locals :: P.Array (Tuple M.FuncId (Map.Map M.Local Ident)))
            )
      locals `shouldEqual` Right
        [ Tuple (M.FuncId 0) [ Tuple (M.Local 0) (Ident "x") ]
        , Tuple (M.FuncId 1) [ Tuple (M.Local 2) (Ident "y") ]
        , Tuple (M.FuncId 3) [ Tuple (M.Local 0) (Ident "y") ]
        ]

    it "leaves the aliased binding out, and the intermediates with it" do
      bodyOf debugModule 1 `shouldEqual` Right
        ( M.ELet (M.Local 0) RepRec M.CRecordEmpty
            ( M.ELet (M.Local 1) RepRec (M.CRecordExtend aKey (M.ALit (LitInt 1)) (M.ALocal (M.Local 0)))
                ( M.ELet (M.Local 2) RepInt (M.CRecordSelect aKey (M.ALocal (M.Local 1)))
                    (M.ERet (M.ALocal (M.Local 2)))
                )
            )
        )
