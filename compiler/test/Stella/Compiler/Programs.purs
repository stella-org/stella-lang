-- | The hand-written Core `Lib` and `Main` the middle end's and lowering's tests
-- | compile, with the `Base.Int` the compiler carries behind them.
-- |
-- | | Value of `Main` | What it exercises |
-- | | --- | --- |
-- | | `summed` | a recursive function, a constructor dispatch, a field, an operation |
-- | | `deepSum` | a non-tail recursion as deep as its list |
-- | | `counted` | a self tail call |
-- | | `listValue` | a list built by tail calls |
-- | | `overApplied` | a known call of the callee's arity, then an application of the partial application it returns |
-- | | `overAppliedU` | an unknown call supplying two arguments to a function of arity one |
-- | | `papApplied` | a partial application of a global, then saturated |
-- | | `ctorPap` | a partial application of a constructor |
-- | | `captured` | a closure over a computed local |
-- | | `evenOdd` | a recursive group of closures capturing each other |
-- | | `joined` | a join point two leaves share |
-- | | `looped` | a join point jumping to itself |
-- | | `recordShape`, `recordArith` | the record operations |
-- | | `variantCase` | an injection and a dispatch on its key |
-- | | `negZero`, `posZero`, `nanCase` | a `Number` dispatch by literal identity |
-- | | `stringCase`, `charCase` | a `String` and a `Char` dispatch |
-- | | `unitValue` | `Prim.Unit`, which no module declares |
-- | | `unboxed`, `boxMatched`, `addCalled`, `addPartial` | a known call, a constructor, a dispatch, and a partial application reaching into another module |
-- | | `dictTwice`, `mutualPair` | recursive groups of records whose closures read the group, one member and two |
-- | | `localDict`, `localPair`, `localMixed` | the same groups bound locally, by-need cells, and a function and a cell capturing each other |
module Test.Stella.Compiler.Programs
  ( intName
  , mainName
  , inInt
  , libModule
  , mainModule
  , baseInt
  ) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Bifunctor (lmap)
import Data.Either (Either, note)
import Data.Foldable (foldM)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Tuple (Tuple(..))
import Stella.Compiler.Elaborate.Environment.Imported (importedSignature)
import Stella.Compiler.Interface.Environment (addInterface, initialEnvironment, viewFor)
import Stella.Compiler.Macro.Compiled (Interface, compiled)
import Stella.Compiler.TypedCore (CtorBranch, DecisionTree(..), Decl(..), Export(..), Expr(..), Ident(..), JoinName(..), Kind(..), LitBranch, Literal(..), Module, ModuleName(..), Occurrence(..), Qualified(..), RowEntry(..), RowKey(..), Symbol(..), Tag(..), TyName(..), TyVar(..), Type(..), ValueBinding, monoScheme, scalarString, scalarStringOf, scalarValue)
import Stella.Compiler.TypedCore.Prim (booleanTy, intTy, pureFn, recordTy, unitCtor, unitTy, variantTy)
import Stella.Compiler.TypedCore.Signature (Signature)

-- Names --------------------------------------------------------------------------------

intName :: ModuleName
intName = ModuleName "Base.Int"

libName :: ModuleName
libName = ModuleName "Lib"

mainName :: ModuleName
mainName = ModuleName "Main"

inInt :: P.String -> Qualified Ident
inInt = Qualified intName <<< Ident

inLib :: P.String -> Qualified Ident
inLib = Qualified libName <<< Ident

inMain :: P.String -> Qualified Ident
inMain = Qualified mainName <<< Ident

int :: Type
int = TCon intTy []

bool :: Type
bool = TCon booleanTy []

listOf :: Type -> Type
listOf a = TApp (TCon (Qualified mainName (TyName "List")) []) a

boxTy :: Type
boxTy = TCon (Qualified libName (TyName "Box")) []

symbolKey :: P.String -> RowKey
symbolKey = SymbolKey <<< Symbol

tagKey :: P.String -> RowKey
tagKey = TagKey <<< Tag

rowOf :: P.Array (Tuple RowKey Type) -> Type
rowOf = Array.foldr (\(Tuple k t) rest -> TRowExtend (RowTypeEntry k t) rest) TRowEmpty

recordOf :: P.Array (Tuple RowKey Type) -> Type
recordOf fields = TApp (TCon recordTy []) (rowOf fields)

variantOf :: P.Array (Tuple RowKey Type) -> Type
variantOf fields = TApp (TCon variantTy []) (rowOf fields)

-- Terms --------------------------------------------------------------------------------

var :: P.String -> Expr P.Int
var = Var 0 <<< Ident

global :: Qualified Ident -> Expr P.Int
global q = Global 0 q []

app :: Expr P.Int -> P.Array (Expr P.Int) -> Expr P.Int
app = Array.foldl (App 0)

lit :: P.Int -> Expr P.Int
lit = Lit 0 <<< LitInt

num :: P.Number -> Expr P.Int
num = Lit 0 <<< LitNumber

str :: P.String -> Literal
str s = LitString (fromMaybe (scalarStringOf []) (scalarString s))

char :: P.Int -> Literal
char c = case scalarValue c of
  Just v -> LitChar v
  Nothing -> LitInt c

intOp :: P.String -> Expr P.Int -> Expr P.Int -> Expr P.Int
intOp name a b = app (global (inInt name)) [ a, b ]

-- | A pure λ.
lam :: P.String -> Type -> Expr P.Int -> Expr P.Int
lam name ty = Lam 0 (Ident name) ty TRowEmpty

let' :: P.String -> Type -> Expr P.Int -> Expr P.Int -> Expr P.Int
let' name = Let 0 (Ident name)

nilOf :: Expr P.Int
nilOf = TyApp 0 (global (inMain "Nil")) int

consOf :: Expr P.Int -> Expr P.Int -> Expr P.Int
consOf x xs = app (TyApp 0 (global (inMain "Cons")) int) [ x, xs ]

-- | `case (scrutinee) of lit_i -> e_i ; _ -> default`.
litCase :: Expr P.Int -> P.Array (Tuple Literal (Expr P.Int)) -> Expr P.Int -> Expr P.Int
litCase scrutinee branches default =
  Case 0 [ scrutinee ]
    ( SwitchLit (OccScrutinee 0)
        (map (\(Tuple l e) -> { lit: l, tree: Leaf e } :: LitBranch P.Int) branches)
        (Leaf default)
    )

-- The modules ----------------------------------------------------------------------------

-- | `data Box = Box Int`, `unbox`, and `addTo`, whose definitional arity is two.
libModule :: Module P.Int
libModule =
  { annotation: 0
  , name: libName
  , imports: [ intName ]
  , exports: [ ExportType (TyName "Box"), ExportCtor (Ident "Box"), ExportValue (Ident "unbox"), ExportValue (Ident "addTo") ]
  , decls:
      [ DeclData 1
          { name: TyName "Box"
          , kindVars: []
          , params: []
          , constructors: [ { name: Ident "Box", tag: 0, fields: [ int ] } ]
          , isNewtype: false
          , attributes: []
          }
      , nonrec 2 "unbox" (pureFn boxTy int) $ lam "b" boxTy $
          Case 0 [ var "b" ]
            ( SwitchCtor (OccScrutinee 0)
                [ { ctor: inLib "Box", tree: Bind (Ident "x") (OccField (OccScrutinee 0) (inLib "Box") 0) (Leaf (var "x")) } ]
                Nothing
            )
      , nonrec 3 "addTo" (pureFn int (pureFn int int)) $ lam "n" int $ lam "m" int $ intOp "add" (var "n") (var "m")
      ]
  }

nonrec :: P.Int -> P.String -> Type -> Expr P.Int -> Decl P.Int
nonrec at name ty value = DeclNonRec at { name: Ident name, scheme: monoScheme ty, value, attributes: [] }

rec1 :: P.Int -> P.String -> Type -> Expr P.Int -> Decl P.Int
rec1 at name ty value = DeclRec at [ { name: Ident name, scheme: monoScheme ty, value, attributes: [] } ]

tested :: P.Array P.String
tested =
  [ "summed"
  , "deepSum"
  , "counted"
  , "listValue"
  , "overApplied"
  , "papApplied"
  , "ctorPap"
  , "captured"
  , "evenOdd"
  , "joined"
  , "looped"
  , "recordShape"
  , "recordArith"
  , "variantCase"
  , "negZero"
  , "posZero"
  , "nanCase"
  , "stringCase"
  , "charCase"
  , "unitValue"
  , "unboxed"
  , "boxMatched"
  , "addCalled"
  , "overAppliedU"
  , "addPartial"
  , "dictTwice"
  , "mutualPair"
  , "localDict"
  , "localPair"
  , "localMixed"
  ]

-- | How far the values that recurse, loop, and jump go, and what each comes to.
type Scale =
  { list :: P.Int
  , listSum :: P.Int
  , count :: P.Int
  , parity :: P.Int
  , loop :: P.Int
  , loopSum :: P.Int
  }

-- | The scale `Main` is written at.
usual :: Scale
usual = { list: 100, listSum: 5050, count: 1000, parity: 101, loop: 100, loopSum: 5050 }

mainModule :: Module P.Int
mainModule = mainModuleAt usual

mainModuleAt :: Scale -> Module P.Int
mainModuleAt scale =
  { annotation: 0
  , name: mainName
  , imports: [ intName, libName ]
  , exports: map (ExportValue <<< Ident) tested
  , decls:
      [ DeclData 1
          { name: TyName "List"
          , kindVars: []
          , params: [ { name: TyVar "a", kind: KType } ]
          , constructors:
              [ { name: Ident "Nil", tag: 0, fields: [] }
              , { name: Ident "Cons", tag: 1, fields: [ TVar (TyVar "a"), listOf (TVar (TyVar "a")) ] }
              ]
          , isNewtype: false
          , attributes: []
          }
      , rec1 2 "sum" (pureFn (listOf int) int) sumBody
      , rec1 3 "build" (pureFn int (pureFn (listOf int) (listOf int))) buildBody
      , rec1 4 "count" (pureFn int (pureFn int int)) countBody
      , nonrec 5 "subtract" (pureFn int (pureFn int int)) $ lam "n" int $ lam "y" int $ intOp "sub" (var "y") (var "n")
      , nonrec 6 "curried" (pureFn int (pureFn int int)) $ lam "n" int $ app (global (inMain "subtract")) [ var "n" ]
      , nonrec 7 "summed" int $ app (global (inMain "sum")) [ consOf (lit 1) (consOf (lit 2) (consOf (lit 3) nilOf)) ]
      , nonrec 8 "deepSum" int $ app (global (inMain "sum")) [ app (global (inMain "build")) [ lit scale.list, nilOf ] ]
      , nonrec 9 "counted" int $ app (global (inMain "count")) [ lit scale.count, lit 0 ]
      , nonrec 10 "listValue" (listOf int) $ app (global (inMain "build")) [ lit 3, nilOf ]
      , nonrec 11 "overApplied" int $ app (global (inMain "curried")) [ lit 10, lit 3 ]
      , nonrec 12 "papApplied" int $ let' "p" (pureFn int int) (app (global (inMain "subtract")) [ lit 1 ]) (app (var "p") [ lit 10 ])
      , nonrec 13 "ctorPap" int $ let' "c" (pureFn (listOf int) (listOf int)) (app (TyApp 0 (global (inMain "Cons")) int) [ lit 1 ])
          (app (global (inMain "sum")) [ app (var "c") [ nilOf ] ])
      -- `k` is computed rather than a literal, so the lambda captures it: a literal
      -- would be an atom the lifted body names directly, and no capture would be made
      , nonrec 14 "captured" int $ let' "k" int (intOp "add" (lit 2) (lit 3)) $ let' "add5" (pureFn int int) (lam "x" int (intOp "add" (var "x") (var "k"))) (app (var "add5") [ lit 3 ])
      , nonrec 15 "evenOdd" bool (evenOddBody scale.parity)
      , nonrec 16 "joined" int joinedBody
      , nonrec 17 "looped" int (loopedBody scale.loop)
      , nonrec 18 "recordShape" (recordOf [ Tuple (symbolKey "y") bool ]) $
          RecordRestrict 0 (symbolKey "x")
            (RecordMerge 0 (RecordExtend 0 (symbolKey "x") (lit 1) (RecordEmpty 0)) (RecordExtend 0 (symbolKey "y") (Lit 0 (LitBoolean true)) (RecordEmpty 0)))
      , nonrec 19 "recordArith" int $
          let' "r" (recordOf [ Tuple (symbolKey "x") int, Tuple (symbolKey "y") int ])
            (RecordExtend 0 (symbolKey "x") (lit 1) (RecordExtend 0 (symbolKey "y") (lit 2) (RecordEmpty 0)))
            ( intOp "add"
                (RecordSelect 0 (symbolKey "y") (RecordUpdate 0 (symbolKey "y") (var "r") (lit 5)))
                (RecordSelect 0 (symbolKey "x") (var "r"))
            )
      , nonrec 20 "variantCase" int variantBody
      , nonrec 21 "negZero" int $ litCase (num (-0.0)) [ Tuple (LitNumber 0.0) (lit 1), Tuple (LitNumber (-0.0)) (lit 2) ] (lit 3)
      , nonrec 22 "posZero" int $ litCase (num 0.0) [ Tuple (LitNumber (-0.0)) (lit 1) ] (lit 2)
      , nonrec 23 "nanCase" int $ litCase (num (0.0 / 0.0)) [ Tuple (LitNumber (0.0 / 0.0)) (lit 1) ] (lit 2)
      , nonrec 24 "stringCase" int $ litCase (Lit 0 (str "b")) [ Tuple (str "a") (lit 1), Tuple (str "b") (lit 2) ] (lit 3)
      , nonrec 25 "charCase" int $ litCase (Lit 0 (char 0x62)) [ Tuple (char 0x61) (lit 1), Tuple (char 0x62) (lit 2) ] (lit 3)
      , nonrec 26 "unitValue" (TCon unitTy []) (global unitCtor)
      , nonrec 27 "unboxed" int $ app (global (inLib "unbox")) [ app (global (inLib "Box")) [ lit 7 ] ]
      , nonrec 28 "boxMatched" int $
          Case 0 [ app (global (inLib "Box")) [ lit 9 ] ]
            ( SwitchCtor (OccScrutinee 0)
                [ { ctor: inLib "Box", tree: Bind (Ident "x") (OccField (OccScrutinee 0) (inLib "Box") 0) (Leaf (var "x")) } ]
                Nothing
            )
      , nonrec 29 "addPartial" int $ let' "p" (pureFn int int) (app (global (inLib "addTo")) [ lit 1 ]) (app (var "p") [ lit 41 ])
      , nonrec 30 "addCalled" int $ app (global (inLib "addTo")) [ lit 1, lit 2 ]
      , nonrec 31 "apply2" (pureFn (pureFn int (pureFn int int)) int) $ lam "f" (pureFn int (pureFn int int)) $ app (var "f") [ lit 10, lit 3 ]
      -- `apply2` hands both arguments to whatever it is given at once, and `curried`
      -- takes one: 10 enters it, and 3 waits on the partial application it returns
      , nonrec 32 "overAppliedU" int $ app (global (inMain "apply2")) [ global (inMain "curried") ]
      -- a recursive group of records whose closures read the group, which
      -- initializing them does not
      , rec1 33 "dict" dictTy dictBody
      , nonrec 34 "dictTwice" int $ app (RecordSelect 0 (symbolKey "twice") (global (inMain "dict"))) [ lit 5 ]
      , DeclRec 35 [ pairMember "first" 1 "second", pairMember "second" 2 "first" ]
      , nonrec 36 "mutualPair" int $ intOp "add" (app (RecordSelect 0 (symbolKey "other") (global (inMain "first"))) [ lit 10 ]) (app (RecordSelect 0 (symbolKey "other") (global (inMain "second"))) [ lit 20 ])
      -- the same groups bound locally, each member that is no function a by-need
      -- cell, and a group of a function and a cell capturing each other
      , nonrec 37 "localDict" int $ LetRec 0 [ { name: Ident "dict", ty: dictTy, value: dictOver (var "dict") } ]
          (app (RecordSelect 0 (symbolKey "twice") (var "dict")) [ lit 5 ])
      , nonrec 38 "localPair" int $ LetRec 0 [ pairOver "first" 1 (var "second"), pairOver "second" 2 (var "first") ]
          (intOp "add" (app (RecordSelect 0 (symbolKey "other") (var "first")) [ lit 10 ]) (app (RecordSelect 0 (symbolKey "other") (var "second")) [ lit 20 ]))
      , nonrec 39 "localMixed" int $ LetRec 0
          [ { name: Ident "go", ty: pureFn int int, value: lam "n" int (intOp "add" (RecordSelect 0 (symbolKey "base") (var "table")) (var "n")) }
          , { name: Ident "table", ty: tableTy, value: RecordExtend 0 (symbolKey "base") (lit 40) (RecordExtend 0 (symbolKey "step") (var "go") (RecordEmpty 0)) }
          ]
          (app (RecordSelect 0 (symbolKey "step") (var "table")) [ lit 2 ])
      ]
  }

-- | `{ twice: λn. dict.once (dict.once n), once: λn. n + 1 }`.
dictTy :: Type
dictTy = recordOf [ Tuple (symbolKey "twice") (pureFn int int), Tuple (symbolKey "once") (pureFn int int) ]

dictBody :: Expr P.Int
dictBody = dictOver (global (inMain "dict"))

-- | The record, reaching itself through the reference given.
dictOver :: Expr P.Int -> Expr P.Int
dictOver self =
  RecordExtend 0 (symbolKey "twice") (lam "n" int (app once [ app once [ var "n" ] ]))
    (RecordExtend 0 (symbolKey "once") (lam "n" int (intOp "add" (var "n") (lit 1))) (RecordEmpty 0))
  where
  once = RecordSelect 0 (symbolKey "once") self

-- | A local `{ k: k, other: λn. n + peer.k }`, reaching its peer through the
-- | reference given.
pairOver :: P.String -> P.Int -> Expr P.Int -> { name :: Ident, ty :: Type, value :: Expr P.Int }
pairOver name k peer =
  { name: Ident name
  , ty: pairTy
  , value: RecordExtend 0 (symbolKey "k") (lit k)
      (RecordExtend 0 (symbolKey "other") (lam "n" int (intOp "add" (var "n") (RecordSelect 0 (symbolKey "k") peer))) (RecordEmpty 0))
  }

-- | `{ base: Int, step: Int -> Int }`.
tableTy :: Type
tableTy = recordOf [ Tuple (symbolKey "base") int, Tuple (symbolKey "step") (pureFn int int) ]

-- | `{ k: k, other: λn. n + peer.k }`, a member of a group of two reading the
-- | other only under its λ.
pairMember :: P.String -> P.Int -> P.String -> ValueBinding P.Int
pairMember name k peer =
  { name: Ident name
  , scheme: monoScheme pairTy
  , value: RecordExtend 0 (symbolKey "k") (lit k)
      (RecordExtend 0 (symbolKey "other") (lam "n" int (intOp "add" (var "n") (RecordSelect 0 (symbolKey "k") (global (inMain peer))))) (RecordEmpty 0))
  , attributes: []
  }

pairTy :: Type
pairTy = recordOf [ Tuple (symbolKey "k") int, Tuple (symbolKey "other") (pureFn int int) ]

-- | `λxs. case (xs) of Nil -> 0 ; Cons -> x + sum ys`.
sumBody :: Expr P.Int
sumBody = lam "xs" (listOf int) $
  Case 0 [ var "xs" ] (SwitchCtor (OccScrutinee 0) [ nilBranch, consBranch ] Nothing)
  where
  nilBranch = { ctor: inMain "Nil", tree: Leaf (lit 0) } :: CtorBranch P.Int
  consBranch =
    { ctor: inMain "Cons"
    , tree:
        Bind (Ident "x") (OccField (OccScrutinee 0) (inMain "Cons") 0)
          $ Bind (Ident "ys") (OccField (OccScrutinee 0) (inMain "Cons") 1)
          $ Leaf (intOp "add" (var "x") (app (global (inMain "sum")) [ var "ys" ]))
    } :: CtorBranch P.Int

-- | `λn acc. case (n) of 0 -> acc ; _ -> build (n - 1) (Cons n acc)`, a self tail
-- | call.
buildBody :: Expr P.Int
buildBody = lam "n" int $ lam "acc" (listOf int) $
  litCase (var "n") [ Tuple (LitInt 0) (var "acc") ]
    (app (global (inMain "build")) [ intOp "sub" (var "n") (lit 1), consOf (var "n") (var "acc") ])

-- | `λn acc. case (n) of 0 -> acc ; _ -> count (n - 1) (acc + 1)`.
countBody :: Expr P.Int
countBody = lam "n" int $ lam "acc" int $
  litCase (var "n") [ Tuple (LitInt 0) (var "acc") ]
    (app (global (inMain "count")) [ intOp "sub" (var "n") (lit 1), intOp "add" (var "acc") (lit 1) ])

-- | `letrec { even = λn. …odd…, odd = λn. …even… } in even n`.
evenOddBody :: P.Int -> Expr P.Int
evenOddBody n =
  LetRec 0
    [ { name: Ident "even", ty: pureFn int bool, value: step true "odd" }
    , { name: Ident "odd", ty: pureFn int bool, value: step false "even" }
    ]
    (app (var "even") [ lit n ])
  where
  step atZero other = lam "n" int $
    litCase (var "n") [ Tuple (LitInt 0) (Lit 0 (LitBoolean atZero)) ]
      (app (var other) [ intOp "sub" (var "n") (lit 1) ])

-- | `letjoin j (x : Int) : Int = x + 100 in case (true) of true -> jump j 1 ; _ -> jump j 2`.
joinedBody :: Expr P.Int
joinedBody =
  LetJoin 0 (JoinName "j") [ { name: Ident "x", ty: int } ] int (intOp "add" (var "x") (lit 100))
    (litCase (Lit 0 (LitBoolean true)) [ Tuple (LitBoolean true) (Jump 0 (JoinName "j") [ lit 1 ]) ] (Jump 0 (JoinName "j") [ lit 2 ]))

-- | `letjoin loop (i, acc) = case (i) of 0 -> acc ; _ -> jump loop (i - 1) (acc + i)
-- | in jump loop n 0`.
loopedBody :: P.Int -> Expr P.Int
loopedBody n =
  LetJoin 0 (JoinName "loop") [ { name: Ident "i", ty: int }, { name: Ident "acc", ty: int } ] int
    ( litCase (var "i") [ Tuple (LitInt 0) (var "acc") ]
        (Jump 0 (JoinName "loop") [ intOp "sub" (var "i") (lit 1), intOp "add" (var "acc") (var "i") ])
    )
    (Jump 0 (JoinName "loop") [ lit n, lit 0 ])

-- | `let v : Variant ( #Ok : Int, #Err : Int ) = inject #Ok [( #Err : Int )] 5 in
-- | case (v) of #Ok -> p + 1 ; #Err -> q`.
variantBody :: Expr P.Int
variantBody =
  let' "v" (variantOf [ Tuple (tagKey "Ok") int, Tuple (tagKey "Err") int ]) (VariantInject 0 (tagKey "Ok") (rowOf [ Tuple (tagKey "Err") int ]) (lit 5)) $
    Case 0 [ var "v" ]
      ( SwitchKey (OccScrutinee 0)
          [ { key: tagKey "Ok", tree: Bind (Ident "p") (OccVariantPayload (OccScrutinee 0) (tagKey "Ok")) (Leaf (intOp "add" (var "p") (lit 1))) }
          , { key: tagKey "Err", tree: Bind (Ident "q") (OccVariantPayload (OccScrutinee 0) (tagKey "Err")) (Leaf (var "q")) }
          ]
          Nothing
      )

-- `Base.Int` ----------------------------------------------------------------------------------

-- | What `Lib` and `Main` are compiled against: `Base.Int` as the compiler carries
-- | it, its signature read off its interface as an importer reads it, and the
-- | arities a translation reads of it. `Base.Int` is not compiled here.
baseInt :: Either P.String { signature :: Signature, interface :: Interface }
baseInt = do
  carried <- compiled
  env <- lmap show (foldM (flip addInterface) initialEnvironment carried.moduleInterfaces)
  view <- lmap show (viewFor [ intName ] env)
  signature <- lmap show (importedSignature env view)
  interface <- note "the compiler carries no Base.Int" (Array.find (\i -> i.name == intName) carried.interfaces)
  pure { signature, interface }
