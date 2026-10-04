-- | The hand-written Core the bytecode fixtures are compiled from.
-- |
-- | Lowering Core is the compiler's work and no backend's, so the source of every
-- | fixture lives here and the backends read only the `.dmo` it compiles to
-- | ([Fixtures](../Fixtures.purs)).
-- |
-- | | Value of `Main` | What it exercises |
-- | | --- | --- |
-- | | `summed` | a recursive function, a constructor dispatch, a field, an operation |
-- | | `deepSum` | a non-tail recursion 100 000 deep |
-- | | `counted` | a self tail call a million times over |
-- | | `listValue` | a list built by tail calls, observed as a structure |
-- | | `overApplied` | a known call of the callee's arity, then an application of the partial application it returns |
-- | | `overAppliedU` | an unknown call supplying two arguments to a function of arity one |
-- | | `papApplied` | a partial application of a global, then saturated |
-- | | `ctorPap` | a partial application of a constructor |
-- | | `captured` | a closure over a computed local |
-- | | `evenOdd` | a recursive group of closures capturing each other, tail calling 100 001 deep |
-- | | `joined` | a join point two leaves share |
-- | | `looped` | a join point jumping to itself 100 000 times |
-- | | `recordShape`, `recordArith` | the record operations |
-- | | `variantCase` | an injection and a dispatch on its key |
-- | | `negZero`, `posZero`, `nanCase` | a `Number` dispatch by literal identity |
-- | | `stringCase`, `charCase` | a `String` and a `Char` dispatch |
-- | | `unitValue` | `Prim.Unit`, which no module declares |
-- | | `unboxed`, `boxMatched`, `addCalled`, `addPartial` | a known call, a constructor, a dispatch, and a partial application reaching into another module |
module Test.Stella.Compiler.Fixtures.Programs
  ( intName
  , libName
  , mainName
  , inInt
  , inLib
  , inMain
  , intModule
  , libModule
  , libShrunk
  , libUnexported
  , libRenamed
  , mainModule
  , without
  , refsOnly
  , expected
  , abiSignature
  , baseModules
  , opsModule
  , opsExpected
  , FaultCase
  , faultCases
  , faultModule
  ) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Enum (toEnum)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String.CodePoints as CodePoints
import Data.Tuple (Tuple(..))
import Stella.Compiler.Primitive (arrayTy, baseModule, withBaseTypes)
import Stella.Compiler.TypedCore (CtorBranch, Decl(..), DecisionTree(..), Export(..), Expr(..), Ident(..), JoinName(..), Kind(..), LitBranch, Literal(..), Module, ModuleName(..), Occurrence(..), Qualified(..), RowEntry(..), RowKey(..), Symbol(..), Tag(..), TyName(..), TyVar(..), Type(..), monoScheme, primSignature, scalarString, scalarStringOf, scalarValue)
import Stella.Compiler.TypedCore.Prim (booleanTy, charTy, intTy, numberTy, pureFn, recordTy, stringTy, unitCtor, unitTy, variantTy)
import Stella.Compiler.TypedCore.Signature (Signature)
import Test.Stella.Compiler.Fixtures.Value (Expected(..), ExpectedKey(..))

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

lam :: P.String -> Type -> Expr P.Int -> Expr P.Int
lam name = Lam 0 (Ident name)

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

-- | `Base.Int`, every entry of `stella-base-0.1`. Each is an operation, so what
-- | carries it out is settled by its name where the module is used.
intModule :: Module P.Int
intModule = baseModule 0 intName

fn2 :: Type -> Type -> Type -> Type
fn2 a b r = pureFn a (pureFn b r)

-- | `data Box = Box Int`, `unbox`, and `addTo`, whose definitional arity is two.
libModule :: Module P.Int
libModule = libWith (lam "n" int $ lam "m" int $ intOp "add" (var "n") (var "m"))

-- | The same module with `addTo` of definitional arity **one**: its body is a
-- | partial application, so a module compiled against the first interface calls it
-- | with a count its entry does not admit.
libShrunk :: Module P.Int
libShrunk = libWith (lam "n" int $ app (global (inInt "add")) [ var "n" ])

libWith :: Expr P.Int -> Module P.Int
libWith addTo =
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
      , nonrec 3 "addTo" (pureFn int (pureFn int int)) addTo
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
  ]

mainModule :: Module P.Int
mainModule =
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
      , nonrec 8 "deepSum" int $ app (global (inMain "sum")) [ app (global (inMain "build")) [ lit 100000, nilOf ] ]
      , nonrec 9 "counted" int $ app (global (inMain "count")) [ lit 1000000, lit 0 ]
      , nonrec 10 "listValue" (listOf int) $ app (global (inMain "build")) [ lit 3, nilOf ]
      , nonrec 11 "overApplied" int $ app (global (inMain "curried")) [ lit 10, lit 3 ]
      , nonrec 12 "papApplied" int $ let' "p" (pureFn int int) (app (global (inMain "subtract")) [ lit 1 ]) (app (var "p") [ lit 10 ])
      , nonrec 13 "ctorPap" int $ let' "c" (pureFn (listOf int) (listOf int)) (app (TyApp 0 (global (inMain "Cons")) int) [ lit 1 ])
          (app (global (inMain "sum")) [ app (var "c") [ nilOf ] ])
      -- `k` is computed rather than a literal, so the lambda captures it: a literal
      -- would be an atom the lifted body names directly, and no capture would be made
      , nonrec 14 "captured" int $ let' "k" int (intOp "add" (lit 2) (lit 3)) $ let' "add5" (pureFn int int) (lam "x" int (intOp "add" (var "x") (var "k"))) (app (var "add5") [ lit 3 ])
      , nonrec 15 "evenOdd" bool evenOddBody
      , nonrec 16 "joined" int joinedBody
      , nonrec 17 "looped" int loopedBody
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
      ]
  }

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

-- | `letrec { even = λn. …odd…, odd = λn. …even… } in even 100001`.
evenOddBody :: Expr P.Int
evenOddBody =
  LetRec 0
    [ { name: Ident "even", ty: pureFn int bool, value: step true "odd" }
    , { name: Ident "odd", ty: pureFn int bool, value: step false "even" }
    ]
    (app (var "even") [ lit 100001 ])
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
-- | in jump loop 100000 0`.
loopedBody :: Expr P.Int
loopedBody =
  LetJoin 0 (JoinName "loop") [ { name: Ident "i", ty: int }, { name: Ident "acc", ty: int } ] int
    ( litCase (var "i") [ Tuple (LitInt 0) (var "acc") ]
        (Jump 0 (JoinName "loop") [ intOp "sub" (var "i") (lit 1), intOp "add" (var "acc") (var "i") ])
    )
    (Jump 0 (JoinName "loop") [ lit 100000, lit 0 ])

-- | `let v : Variant ( #Ok : Int, #Err : Int ) = inject #Ok 5 in
-- | case (v) of #Ok -> p + 1 ; #Err -> q`.
variantBody :: Expr P.Int
variantBody =
  let' "v" (variantOf [ Tuple (tagKey "Ok") int, Tuple (tagKey "Err") int ]) (VariantInject 0 (tagKey "Ok") (lit 5)) $
    Case 0 [ var "v" ]
      ( SwitchKey (OccScrutinee 0)
          [ { key: tagKey "Ok", tree: Bind (Ident "p") (OccVariantPayload (OccScrutinee 0) (tagKey "Ok")) (Leaf (intOp "add" (var "p") (lit 1))) }
          , { key: tagKey "Err", tree: Bind (Ident "q") (OccVariantPayload (OccScrutinee 0) (tagKey "Err")) (Leaf (var "q")) }
          ]
          Nothing
      )

-- | `Main` with one of its values left out, from its declarations and its exports.
without :: P.String -> Module P.Int
without name = mainModule
  { exports = Array.filter (_ /= ExportValue (Ident name)) mainModule.exports
  , decls = Array.filter (not <<< declares) mainModule.decls
  }
  where
  declares = case _ of
    DeclNonRec _ b -> b.name == Ident name
    _ -> false

-- | Load `main`, translated against `Lib`'s interface, beside `Lib` compiled with
-- | `addTo` of arity one, and check that loading is refused naming `Lib.addTo` and

refsOnly :: Module P.Int
refsOnly =
  { annotation: 0
  , name: mainName
  , imports: [ intName, libName ]
  , exports: map (ExportValue <<< Ident) [ "held", "peek" ]
  , decls:
      [ nonrec 1 "held" (pureFn boxTy int) (global (inLib "unbox"))
      , nonrec 2 "peek" (pureFn boxTy int) $ lam "b" boxTy $
          Case 0 [ var "b" ]
            ( SwitchCtor (OccScrutinee 0)
                [ { ctor: inLib "Box", tree: Bind (Ident "x") (OccField (OccScrutinee 0) (inLib "Box") 0) (Leaf (var "x")) } ]
                Nothing
            )
      ]
  }

-- The operations ----------------------------------------------------------------------------

numberName :: ModuleName
numberName = ModuleName "Base.Number"

stringName :: ModuleName
stringName = ModuleName "Base.String"

charName :: ModuleName
charName = ModuleName "Base.Char"

arrayName :: ModuleName
arrayName = ModuleName "Base.Array"

number :: Type
number = TCon numberTy []

string :: Type
string = TCon stringTy []

char' :: Type
char' = TCon charTy []

unitType :: Type
unitType = TCon unitTy []

arrayTyName :: Qualified TyName
arrayTyName = arrayTy

arrayOf :: Type -> Type
arrayOf t = TApp (TCon arrayTyName []) t

-- | `Σ_Prim` with the types the ABI supplies.
abiSignature :: Signature
abiSignature = withBaseTypes primSignature

numberModule :: Module P.Int
numberModule = baseModule 0 numberName

stringModule :: Module P.Int
stringModule = baseModule 0 stringName

charModule :: Module P.Int
charModule = baseModule 0 charName

arrayModule :: Module P.Int
arrayModule = baseModule 0 arrayName

baseModules :: P.Array (Module P.Int)
baseModules = [ intModule, numberModule, stringModule, charModule, arrayModule ]

call :: ModuleName -> P.String -> P.Array (Expr P.Int) -> Expr P.Int
call m x = app (global (Qualified m (Ident x)))

-- | An entry of `Base.Array` at `Int`.
arrayCall :: P.String -> P.Array (Expr P.Int) -> Expr P.Int
arrayCall x = app (TyApp 0 (global (Qualified arrayName (Ident x))) int)

text :: P.String -> Expr P.Int
text = Lit 0 <<< str

-- | The string of one scalar value, written by its code rather than in the source.
scalar :: P.Int -> P.String
scalar c = fromMaybe "" (CodePoints.singleton <$> toEnum c)

minInt :: P.Int
minInt = -2147483648

maxInt :: P.Int
maxInt = 2147483647

nan :: P.Number
nan = 0.0 / 0.0

-- | One value of `Main` over the operations: its name, type, right-hand side, and
-- | what it holds, fixed from the ABI's meaning by hand
-- | ([Prim and Base](../../../../../docs/technical-references/06-Modules/02-Prim-and-Base.md)).
type OpValue = { name :: P.String, ty :: Type, value :: Expr P.Int, holds :: Expected }

opValues :: P.Array OpValue
opValues =
  [ v "intAddWraps" int (call intName "add" [ lit maxInt, lit 1 ]) (EInt minInt)
  , v "intSubWraps" int (call intName "sub" [ lit minInt, lit 1 ]) (EInt maxInt)
  , v "intMulWraps" int (call intName "mul" [ lit 65536, lit 65536 ]) (EInt 0)
  -- the exact product needs more than 53 bits; `(a * b) | 0` would give 0
  , v "intMulWide" int (call intName "mul" [ lit maxInt, lit maxInt ]) (EInt 1)
  , v "quotOverflows" int (call intName "quot" [ lit minInt, lit (-1) ]) (EInt minInt)
  , v "remOverflows" int (call intName "rem" [ lit minInt, lit (-1) ]) (EInt 0)
  , v "quotTruncates" int (call intName "quot" [ lit 7, lit (-2) ]) (EInt (-3))
  , v "remTakesDividendSign" int (call intName "rem" [ lit (-7), lit 2 ]) (EInt (-1))
  , v "intEq" bool (call intName "eq" [ lit 3, lit 3 ]) (EBoolean true)
  , v "intLt" bool (call intName "lt" [ lit 3, lit 2 ]) (EBoolean false)
  , v "intToNumber" number (call intName "toNumber" [ lit (-5) ]) (ENumber (-5.0))
  -- negating first would overflow and print a second minus sign or none
  , v "intToStringMin" string (call intName "toString" [ lit minInt ]) (EString "-2147483648")
  , v "numberAdd" number (call numberName "add" [ num 0.1, num 0.2 ]) (ENumber (0.1 + 0.2))
  , v "subZero" number (call numberName "sub" [ num 0.0, num 0.0 ]) (ENumber 0.0)
  , v "negateZero" number (call numberName "negate" [ num 0.0 ]) (ENumber (-0.0))
  , v "divideByZero" number (call numberName "divide" [ num 1.0, num 0.0 ]) (ENumber (1.0 / 0.0))
  , v "numberMul" number (call numberName "mul" [ num 0.1, num 3.0 ]) (ENumber (0.1 * 3.0))
  , v "eqNaN" bool (call numberName "eq" [ num nan, num nan ]) (EBoolean false)
  , v "eqZeros" bool (call numberName "eq" [ num 0.0, num (-0.0) ]) (EBoolean true)
  , v "ltNaN" bool (call numberName "lt" [ num nan, num 1.0 ]) (EBoolean false)
  , v "floorNegative" number (call numberName "floor" [ num (-0.5) ]) (ENumber (-1.0))
  , v "ceilPositive" number (call numberName "ceil" [ num 0.2 ]) (ENumber 1.0)
  , v "truncNegative" number (call numberName "trunc" [ num (-0.5) ]) (ENumber (-0.0))
  , v "toIntNaN" int (call numberName "toInt" [ num nan ]) (EInt 0)
  -- saturating; a conversion by `| 0` gives 1410065408
  , v "toIntLarge" int (call numberName "toInt" [ num 1.0e10 ]) (EInt maxInt)
  , v "toIntNegative" int (call numberName "toInt" [ num (-2.9) ]) (EInt (-2))
  , v "toStringExponent" string (call numberName "toString" [ num 1.0e21 ]) (EString "1e+21")
  , v "toStringPositional" string (call numberName "toString" [ num 1.0e20 ]) (EString "100000000000000000000")
  , v "toStringSmall" string (call numberName "toString" [ num 1.0e-7 ]) (EString "1e-7")
  , v "toStringTenth" string (call numberName "toString" [ num 0.1 ]) (EString "0.1")
  , v "toStringNegativeZero" string (call numberName "toString" [ num (-0.0) ]) (EString "0")
  , v "stringLength" int (call stringName "length" [ text ("a" <> smile <> "bc") ]) (EInt 4)
  , v "codePointAtAstral" char' (call stringName "codePointAt" [ lit 1, text ("a" <> smile <> "bc") ]) (EChar 0x1F600)
  , v "appendStrings" string (call stringName "append" [ text "ab", text "c" ]) (EString "abc")
  , v "sliceScalars" string (call stringName "slice" [ lit 1, lit 3, text ("a" <> smile <> "bc") ]) (EString (smile <> "b"))
  , v "singletonAstral" string (call stringName "singleton" [ call charName "fromCodePoint" [ lit 0x1F600 ] ]) (EString smile)
  , v "stringEq" bool (call stringName "eq" [ text "a", text "a" ]) (EBoolean true)
  -- by scalar value; JavaScript's `<` over code units says false
  , v "ltAstral" bool (call stringName "lt" [ text (scalar 0xE000), text smile ]) (EBoolean true)
  , v "ltPrefix" bool (call stringName "lt" [ text "ab", text "abc" ]) (EBoolean true)
  , v "ltSame" bool (call stringName "lt" [ text "abc", text "abc" ]) (EBoolean false)
  , v "charRoundTrip" int (call charName "toCodePoint" [ call charName "fromCodePoint" [ lit 0x1F600 ] ]) (EInt 0x1F600)
  -- every slot written before one is read, so the precondition of `unsafeIndex`
  -- holds (D42)
  , v "arrayReadBack" int
      ( let' "xs" (arrayOf int) (arrayCall "unsafeNew" [ lit 2 ])
          $ let' "w0" unitType (arrayCall "unsafeSet" [ lit 0, lit 10, var "xs" ])
          $ let' "w1" unitType (arrayCall "unsafeSet" [ lit 1, lit 20, var "xs" ])
          $ arrayCall "unsafeIndex" [ var "xs", lit 1 ]
      )
      (EInt 20)
  , v "arrayLength" int (arrayCall "length" [ arrayCall "unsafeNew" [ lit 3 ] ]) (EInt 3)
  -- an operation applied short of its arity is carried out once, when the last
  -- argument arrives
  , v "arraySetLater" int
      ( let' "setFirst" (fn2 int (arrayOf int) unitType) (arrayCall "unsafeSet" [ lit 0 ])
          $ let' "xs" (arrayOf int) (arrayCall "unsafeNew" [ lit 1 ])
          $ let' "w" unitType (app (var "setFirst") [ lit 7, var "xs" ])
          $ arrayCall "unsafeIndex" [ var "xs", lit 0 ]
      )
      (EInt 7)
  , v "numberAddLater" number
      (let' "plus" (pureFn number number) (call numberName "add" [ num 1.5 ]) (app (var "plus") [ num 1.0 ]))
      (ENumber 2.5)
  ]
  where
  v name ty value holds = { name, ty, value, holds }
  smile = scalar 0x1F600

-- | `Main` over every operation, each value computing one from literals.
opsModule :: Module P.Int
opsModule =
  { annotation: 0
  , name: mainName
  , imports: map _.name baseModules
  , exports: map (\o -> ExportValue (Ident o.name)) opValues
  , decls: Array.mapWithIndex (\i o -> nonrec (i + 1) o.name o.ty o.value) opValues
  }

opsExpected :: P.Array (Tuple P.String Expected)
opsExpected = map (\o -> Tuple o.name o.holds) opValues

-- | One way an operation faults: a `Main` whose one global carries it out on
-- | inputs the ABI says it faults on, so initializing that global is where the
-- | fault must end loading.
type FaultCase = { name :: P.String, description :: P.String, ty :: Type, value :: Expr P.Int }

faultCases :: P.Array FaultCase
faultCases =
  [ f "fault-quot-zero" "Base.Int.quot by zero" int (call intName "quot" [ lit 1, lit 0 ])
  , f "fault-rem-zero" "Base.Int.rem by zero" int (call intName "rem" [ lit 1, lit 0 ])
  , f "fault-code-point-at-outside" "Base.String.codePointAt at an index past the last scalar value" char'
      (call stringName "codePointAt" [ lit 4, text ("a" <> scalar 0x1F600 <> "bc") ])
  , f "fault-slice-reversed" "Base.String.slice with its start past its end" string (call stringName "slice" [ lit 2, lit 1, text "abc" ])
  , f "fault-slice-past-end" "Base.String.slice with its end past the length" string (call stringName "slice" [ lit 0, lit 4, text "abc" ])
  , f "fault-slice-negative" "Base.String.slice with a negative start, which is not counted from the end" string (call stringName "slice" [ lit (-1), lit 2, text "abc" ])
  , f "fault-from-code-point-surrogate" "Base.Char.fromCodePoint of a surrogate" char' (call charName "fromCodePoint" [ lit 0xD800 ])
  , f "fault-from-code-point-above" "Base.Char.fromCodePoint past 0x10FFFF" char' (call charName "fromCodePoint" [ lit 0x110000 ])
  , f "fault-from-code-point-negative" "Base.Char.fromCodePoint of a negative number" char' (call charName "fromCodePoint" [ lit (-1) ])
  , f "fault-array-new-negative" "Base.Array.unsafeNew with a negative count" (arrayOf int) (arrayCall "unsafeNew" [ lit (-1) ])
  , f "fault-array-set-outside" "Base.Array.unsafeSet at an index outside the array" unitType
      (let' "xs" (arrayOf int) (arrayCall "unsafeNew" [ lit 1 ]) (arrayCall "unsafeSet" [ lit 1, lit 5, var "xs" ]))
  , f "fault-array-index-outside" "Base.Array.unsafeIndex at an index outside the array" int
      ( let' "xs" (arrayOf int) (arrayCall "unsafeNew" [ lit 1 ])
          $ let' "w" unitType (arrayCall "unsafeSet" [ lit 0, lit 5, var "xs" ])
          $ arrayCall "unsafeIndex" [ var "xs", lit 1 ]
      )
  ]
  where
  f name description ty value = { name, description, ty, value }

-- | The `Main` of a fault case: the one global, called `faulted`.
faultModule :: FaultCase -> Module P.Int
faultModule c =
  { annotation: 0
  , name: mainName
  , imports: map _.name baseModules
  , exports: []
  , decls: [ nonrec 1 "faulted" c.ty c.value ]
  }

-- | `Lib` exporting everything but `unbox`.
libUnexported :: Module P.Int
libUnexported = libModule { exports = Array.filter (_ /= ExportValue (Ident "unbox")) libModule.exports }

-- | `Lib` whose one constructor is called `Crate`: a module importing `Lib.Box`
-- | reaches a constructor no module declares.
libRenamed :: Module P.Int
libRenamed =
  { annotation: 0
  , name: libName
  , imports: [ intName ]
  , exports: [ ExportType (TyName "Box"), ExportCtor (Ident "Crate"), ExportValue (Ident "unbox"), ExportValue (Ident "addTo") ]
  , decls:
      [ DeclData 1
          { name: TyName "Box"
          , kindVars: []
          , params: []
          , constructors: [ { name: Ident "Crate", tag: 0, fields: [ int ] } ]
          , isNewtype: false
          , attributes: []
          }
      , nonrec 2 "unbox" (pureFn boxTy int) $ lam "b" boxTy $
          Case 0 [ var "b" ]
            ( SwitchCtor (OccScrutinee 0)
                [ { ctor: inLib "Crate", tree: Bind (Ident "x") (OccField (OccScrutinee 0) (inLib "Crate") 0) (Leaf (var "x")) } ]
                Nothing
            )
      , nonrec 3 "addTo" (pureFn int (pureFn int int)) $ lam "n" int $ lam "m" int $ intOp "add" (var "n") (var "m")
      ]
  }

-- | What each value of `Main` holds, fixed from the program by hand.
expected :: P.Array (Tuple P.String Expected)
expected =
  [ Tuple "summed" (EInt 6)
  -- 1 + … + 100000 is 5000050000, which wraps modulo 2³² to 705082704
  , Tuple "deepSum" (EInt 705082704)
  , Tuple "counted" (EInt 1000000)
  , Tuple "listValue" (cons 1 (cons 2 (cons 3 nil)))
  -- curried 10 3 = subtract 10 3 = 3 - 10
  , Tuple "overApplied" (EInt (-7))
  , Tuple "papApplied" (EInt 9)
  , Tuple "ctorPap" (EInt 1)
  , Tuple "captured" (EInt 8)
  -- 100001 is odd
  , Tuple "evenOdd" (EBoolean false)
  , Tuple "joined" (EInt 101)
  , Tuple "looped" (EInt 705082704)
  , Tuple "recordShape" (ERecord [ { key: KField "y", value: EBoolean true } ])
  , Tuple "recordArith" (EInt 6)
  , Tuple "variantCase" (EInt 6)
  , Tuple "negZero" (EInt 2)
  , Tuple "posZero" (EInt 2)
  , Tuple "nanCase" (EInt 1)
  , Tuple "stringCase" (EInt 2)
  , Tuple "charCase" (EInt 2)
  , Tuple "unitValue" (EData "Prim.Unit" [])
  , Tuple "unboxed" (EInt 7)
  , Tuple "boxMatched" (EInt 9)
  , Tuple "addPartial" (EInt 42)
  , Tuple "addCalled" (EInt 3)
  -- subtract 10 3 = 3 - 10; the pending argument applied first would give 10 - 3
  , Tuple "overAppliedU" (EInt (-7))
  ]
  where
  cons x xs = EData "Main.Cons" [ EInt x, xs ]
  nil = EData "Main.Nil" []
