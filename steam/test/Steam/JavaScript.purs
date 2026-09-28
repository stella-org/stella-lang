-- | The JavaScript backend, carried the whole way: Typed Core, checked,
-- | translated against the interfaces of its imports, lowered, encoded, decoded,
-- | generated, written out, and imported in Node.
-- |
-- | Each value is held to two things: a result fixed from the program by hand,
-- | and what Steam computes from the same `.dmo`. The first is what catches a
-- | defect the two share — both read what lowering produced — and the second is
-- | what catches one only the backend has.
-- |
-- | | Value | What it exercises |
-- | | --- | --- |
-- | | `summed` | a recursive function, a constructor dispatch, a field, an operation |
-- | | `deepSum` | a non-tail recursion 100 000 deep, which runs in bounded host stack |
-- | | `counted` | a self tail call a million times over |
-- | | `listValue` | a list built by tail calls, compared as a structure |
-- | | `overApplied` | a known call of the callee's arity, then an application of the partial application it returns |
-- | | `overAppliedU` | an unknown call supplying two arguments to a function of arity one: the run loop keeps the second pending and applies what comes back to it |
-- | | `papApplied` | a partial application of a global, then saturated |
-- | | `ctorPap` | a partial application of a constructor |
-- | | `captured` | a closure over a computed local, read through `CAPT` |
-- | | `evenOdd` | a recursive group of closures capturing each other, tail calling 100 001 deep |
-- | | `joined` | a join point two leaves share |
-- | | `looped` | a join point jumping to itself 100 000 times |
-- | | `recordShape`, `recordArith` | the record operations |
-- | | `variantCase` | an injection and a dispatch on its key |
-- | | `negZero`, `posZero`, `nanCase` | a `Number` dispatch by literal identity |
-- | | `stringCase`, `charCase` | a `String` and a `Char` dispatch |
-- | | `unitValue` | `Prim.Unit`, which no module declares |
-- | | `unboxed`, `boxMatched`, `addCalled`, `addPartial` | a known call, a constructor, a dispatch, and a partial application reaching into another module |
module Test.Steam.JavaScript (spec) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldM)
import Data.Int (toNumber)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String as String
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Effect.Aff (Aff)
import Effect.Aff.Compat (EffectFnAff, fromEffectFnAff)
import Effect.Class (liftEffect)
import Effect.Exception (throw)
import Effect.Ref as Ref
import Run (runBaseEffect)
import Run.Except as Except
import Steam.Foreign (emptyTable)
import Steam.Load (Store, emptyStore, globalNamed, load, namesOf, noIdentities)
import Steam.Structural (NumberAtom(..), StructuralValue(..), defaultLimits, inspect)
import Stella.Compiler.Bytecode (CalleeEntry(..), CalleeIx(..), Dmo, EncodeError(..), FuncIx(..), GlobalInit(..), Instr(..), decode, encode, lower)
import Stella.Compiler.Bytecode as B
import Stella.Compiler.Interface (Dmi, importsOf, interfaceOf)
import Stella.Compiler.JavaScript (JsError(..), fileName, generate)
import Stella.Compiler.Primitive (PrimOp(..))
import Stella.Compiler.MiddleEnd (translate)
import Stella.Compiler.TypedCore (CtorBranch, Decl(..), DecisionTree(..), EffName(..), Export(..), Expr(..), Ident(..), JoinName(..), Kind(..), LitBranch, Literal(..), Module, ModuleName(..), Occurrence(..), Qualified(..), RowEntry(..), RowKey(..), Symbol(..), Tag(..), TyName(..), TyVar(..), Type(..), declareAnnotated, monoScheme, primSignature, scalarString, scalarStringOf, scalarValue, textOf, codePointOf)
import Stella.Compiler.TypedCore.Prim (booleanTy, intTy, numberTy, pureFn, recordTy, unitCtor, unitTy, variantTy)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

-- Running generated code ---------------------------------------------------------------

-- | The namespace of an imported module, which only the functions below read.
foreign import data Namespace :: P.Type

foreign import runtimeSpecifier :: P.String

foreign import importGeneratedImpl
  :: P.Array { name :: P.String, source :: P.String } -> P.String -> EffectFnAff Namespace

foreign import importFailureImpl
  :: P.Array { name :: P.String, source :: P.String } -> P.String -> EffectFnAff P.String

foreign import shapeOfImpl
  :: { number :: P.Number -> Shape
     , string :: P.String -> Shape
     , boolean :: P.Boolean -> Shape
     , data :: P.String -> P.Array Shape -> Shape
     , variant :: P.String -> Shape -> Shape
     , record :: P.Array { key :: P.String, value :: Shape } -> Shape
     , fn :: Shape
     , other :: P.String -> Shape
     }
  -> Namespace
  -> P.String
  -> Shape

-- | What a value is, as either side can say it. Every number is one kind here,
-- | JavaScript holding an `Int`, a `Number`, and a `Char` alike; they compare by
-- | literal identity, so a negative zero is not a zero.
data Shape
  = SNum P.Number
  | SStr P.String
  | SBool P.Boolean
  | SDat P.String (P.Array Shape)
  | SVar P.String Shape
  | SRec (P.Array (Tuple P.String Shape))
  | SFn
  | SOther P.String

instance Eq Shape where
  eq a b = case a, b of
    SNum x, SNum y -> if x /= x then y /= y else x == y && (1.0 / x) == (1.0 / y)
    SStr x, SStr y -> x == y
    SBool x, SBool y -> x == y
    SDat c xs, SDat d ys -> c == d && xs == ys
    SVar k x, SVar l y -> k == l && x == y
    SRec xs, SRec ys -> xs == ys
    SFn, SFn -> true
    SOther x, SOther y -> x == y
    _, _ -> false

instance Show Shape where
  show = case _ of
    SNum x -> show x
    SStr s -> show s
    SBool b -> show b
    SDat c xs -> "(" <> c <> String.joinWith "" (map (\x -> " " <> show x) xs) <> ")"
    SVar k x -> "<" <> k <> " " <> show x <> ">"
    SRec xs -> "{" <> String.joinWith ", " (map (\(Tuple k v) -> k <> ": " <> show v) xs) <> "}"
    SFn -> "<function>"
    SOther s -> "<" <> s <> ">"

jsShape :: Namespace -> P.String -> Shape
jsShape = shapeOfImpl
  { number: SNum
  , string: SStr
  , boolean: SBool
  , data: SDat
  , variant: SVar
  , record: \fields -> SRec (sortFields (map (\f -> Tuple f.key f.value) fields))
  , fn: SFn
  , other: SOther
  }

sortFields :: P.Array (Tuple P.String Shape) -> P.Array (Tuple P.String Shape)
sortFields = Array.sortWith (\(Tuple k _) -> k)

-- | A key as the backend writes it, so the two sides' records compare field by
-- | field.
keyText :: RowKey -> P.String
keyText = case _ of
  SymbolKey (Symbol s) -> "s:" <> s
  TagKey (Tag t) -> "t:" <> t
  PositionKey n -> "p:" <> show n
  EffectKey (Qualified (ModuleName m) (EffName e)) -> "e:" <> m <> ":" <> e
  _ -> "region"

steamShape :: StructuralValue -> Shape
steamShape = case _ of
  SInt n -> SNum (toNumber n)
  SNumber (NumberAtom x) -> SNum x
  SChar c -> SNum (toNumber (codePointOf c))
  SString s -> SStr (textOf s.text)
  SBoolean b -> SBool b
  SData (Qualified (ModuleName m) (Ident c)) fields -> SDat (m <> "." <> c) (map steamShape fields.items)
  SRecord fields -> SRec (sortFields (map (\f -> Tuple (keyText f.key) (steamShape f.value)) fields.items))
  SVariant k v -> SVar (keyText k) (steamShape v)
  SClosure -> SFn
  SPartialApplication -> SFn
  _ -> SOther "not comparable"

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

intModule :: Module P.Int
intModule =
  { annotation: 0
  , name: intName
  , imports: []
  , exports: map (ExportValue <<< Ident) [ "add", "sub", "mul", "eq", "lt" ]
  , decls:
      [ op 1 "add" int, op 2 "sub" int, op 3 "mul" int, op 4 "eq" bool, op 5 "lt" bool ]
  }
  where
  op at name result = DeclForeign at
    { name: Ident name, scheme: monoScheme (pureFn int (pureFn int result)), attributes: [] }

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

-- | What each value holds, fixed from the program by hand.
expected :: P.Array (Tuple P.String Shape)
expected =
  [ Tuple "summed" (SNum 6.0)
  -- 1 + … + 100000 is 5000050000, which wraps modulo 2³² to 705082704
  , Tuple "deepSum" (SNum 705082704.0)
  , Tuple "counted" (SNum 1000000.0)
  , Tuple "listValue" (cons 1.0 (cons 2.0 (cons 3.0 nil)))
  -- curried 10 3 = subtract 10 3 = 3 - 10
  , Tuple "overApplied" (SNum (-7.0))
  , Tuple "papApplied" (SNum 9.0)
  , Tuple "ctorPap" (SNum 1.0)
  , Tuple "captured" (SNum 8.0)
  -- 100001 is odd
  , Tuple "evenOdd" (SBool false)
  , Tuple "joined" (SNum 101.0)
  , Tuple "looped" (SNum 705082704.0)
  , Tuple "recordShape" (SRec [ Tuple "s:y" (SBool true) ])
  , Tuple "recordArith" (SNum 6.0)
  , Tuple "variantCase" (SNum 6.0)
  , Tuple "negZero" (SNum 2.0)
  , Tuple "posZero" (SNum 2.0)
  , Tuple "nanCase" (SNum 1.0)
  , Tuple "stringCase" (SNum 2.0)
  , Tuple "charCase" (SNum 2.0)
  , Tuple "unitValue" (SDat "Prim.Unit" [])
  , Tuple "unboxed" (SNum 7.0)
  , Tuple "boxMatched" (SNum 9.0)
  , Tuple "addPartial" (SNum 42.0)
  , Tuple "addCalled" (SNum 3.0)
  -- subtract 10 3 = 3 - 10; the pending argument applied first would give 10 - 3
  , Tuple "overAppliedU" (SNum (-7.0))
  ]
  where
  cons x xs = SDat "Main.Cons" [ SNum x, xs ]
  nil = SDat "Main.Nil" []

-- Compiling ---------------------------------------------------------------------------------

type Compiled = { dmo :: Dmo, dmi :: Dmi }

-- | Each module checked against the signatures before it and translated against
-- | the interfaces of those it imports, then carried through the container.
compileAll :: P.Array (Module P.Int) -> Either P.String (P.Array Compiled)
compileAll modules = _.out <$> foldM step { signature: primSignature, dmis: [], out: [] } modules
  where
  step acc m = do
    declared <- lmap' "declare" (declareAnnotated acc.signature m)
    imports <- lmap' "interfaces" (importsOf acc.dmis)
    mid <- lmap' "translate" (translate imports m declared)
    lowered <- lmap' "lower" (lower mid)
    bytes <- lmap' "encode" (encode lowered.dmo)
    dmo <- lmap' "decode" (decode bytes)
    let dmi = interfaceOf mid.module
    pure { signature: declared.signature, dmis: Array.snoc acc.dmis dmi, out: Array.snoc acc.out { dmo, dmi } }

lmap' :: forall e a. Show e => P.String -> Either e a -> Either P.String a
lmap' stage = case _ of
  Left e -> Left (stage <> ": " <> show e)
  Right a -> Right a

generated :: P.Array Dmo -> Either P.String (P.Array { name :: P.String, source :: P.String })
generated = traverse \dmo -> case generate { runtime: runtimeSpecifier } dmo of
  Left e -> Left (show e)
  Right source -> Right { name: fileName dmo.name, source }

-- Both sides ----------------------------------------------------------------------------------

type Both = { js :: Namespace, steam :: Store }

loadBoth :: Aff Both
loadBoth = case compileAll [ intModule, libModule, mainModule ] of
  Left err -> liftEffect (throw err)
  Right compiled -> do
    let dmos = map _.dmo compiled
    files <- either' (generated dmos)
    js <- fromEffectFnAff (importGeneratedImpl files (fileName mainName))
    steam <- liftEffect do
      store <- map (emptyStore emptyTable) (Ref.new noIdentities)
      runBaseEffect (Except.runExcept (Array.foldM load store dmos))
    case steam of
      Left err -> liftEffect (throw ("Steam did not load: " <> show err))
      Right store -> pure { js, steam: store }
  where
  either' = case _ of
    Left err -> liftEffect (throw err)
    Right a -> pure a

-- | Where a value disagrees with the program, or with Steam, what each side held.
mismatchOf :: Both -> Tuple P.String Shape -> Aff (Maybe P.String)
mismatchOf both (Tuple name value) = do
  let js = jsShape both.js name
  steam <- steamValue both.steam name
  pure
    if js == value && steam == value then Nothing
    else Just (name <> ": expected " <> show value <> ", JavaScript " <> show js <> ", Steam " <> show steam)

steamValue :: Store -> P.String -> Aff Shape
steamValue store name = liftEffect do
  names <- namesOf store
  case globalNamed store (inMain name) of
    Nothing -> pure (SOther "no such global")
    Just slot -> do
      held <- Ref.read slot
      pure case held of
        Just value -> steamShape (inspect defaultLimits names value)
        Nothing -> SOther "uninitialized"

spec :: Spec Unit
spec = describe "the JavaScript backend" do
  -- every value is checked in one case, since loading runs every one of them
  it "computes every value as the program says, and as Steam does" do
    both <- loadBoth
    mismatches <- traverse (mismatchOf both) expected
    Array.catMaybes mismatches `shouldEqual` []

  describe "what the generated code holds" do
    it "captures a computed local, and the closure reads it through CAPT" do
      case compileAll [ intModule, libModule, mainModule ] of
        Left err -> fail err
        Right compiled -> case Array.last compiled of
          Nothing -> fail "nothing compiled"
          Just main -> case capturingClosure main.dmo "captured" of
            Nothing -> fail "the value builds no closure with a capture"
            Just f -> do
              -- the closure's function takes a capture and reads it
              readsCapture main.dmo f `shouldEqual` true
              -- and the segment generated for it reads the frame's capture slot
              case generated [ main.dmo ] of
                Left err -> fail err
                Right files -> case Array.head files of
                  Nothing -> fail "nothing generated"
                  Just file -> String.contains (String.Pattern "f.caps[0]") (segmentOf f file.source) `shouldEqual` true

  describe "what a loader establishes, before code is generated" do
    it "refuses each module a loader refuses, for the reason a loader gives" do
      case compileAll [ intModule, libModule, mainModule ] of
        Right [ intCompiled, _, mainCompiled ] ->
          Array.mapMaybe (unrefused intCompiled.dmo mainCompiled.dmo) loaderRefusals `shouldEqual` []
        Right _ -> fail "not three modules"
        Left err -> fail err

    it "refuses, as a bug, each structural operation handed what its precondition excludes" do
      map _.name (Array.filter (not <<< _.refused) runtimeRefusals) `shouldEqual` []

  describe "what the encoder refuses" do
    it "refuses a module whose name the encoder would not write, as the encoder does" do
      case compileAll [ intModule, libModule, mainModule ] of
        Right [ _, _, mainCompiled ] -> do
          let
            dmo = mainCompiled.dmo
            -- `sum` is exported nowhere, so nothing but its spelling changes
            lone = dmo { globals = map (\g -> if g.name == inMain "sum" then g { name = inMain "s\xD800um" } else g) dmo.globals }
          case encode lone, generate { runtime: runtimeSpecifier } lone of
            Left (NotScalarText _), Left (NotEncodable (NotScalarText _)) -> pure unit
            byEncoder, byBackend -> fail ("the encoder gave " <> show (map (const unit) byEncoder) <> " and the backend " <> show (map (const unit) byBackend))
        Right _ -> fail "not three modules"
        Left err -> fail err

  describe "what the backend does not carry out yet" do
    it "refuses an operation a partial application waits on, where nothing saturates it" do
      case compileAll [ numberModule, papOnly ] of
        Right [ _, main ] -> do
          -- the module really holds a partial application of the operation
          papOfNumberAdd main.dmo `shouldEqual` true
          case generate { runtime: runtimeSpecifier } main.dmo of
            Left (OperationNotImplemented NumberAdd) -> pure unit
            other -> fail ("expected the operation to be refused, got " <> show (map (const unit) other))
        Right _ -> fail "not two modules"
        Left err -> fail err

  describe "what linking the generated modules refuses" do
    it "refuses a global the declaring module does not export" do
      linkRefused refsOnly (const (compileLib (libModule { exports = Array.filter (_ /= ExportValue (Ident "unbox")) libModule.exports }))) "unbox" lib0

    it "refuses a constructor the declaring module does not declare" do
      linkRefused refsOnly (const (renamedBox lib0)) "ctor Box" lib0

  describe "what a module cannot decide alone" do
    -- `Main` is translated against the interface that gives `addTo` arity two, and the
    -- `Lib` it is loaded with gives it one. Each case keeps one use of `addTo` alone,
    -- so what refuses the load is the check that use calls for.
    it "refuses, where it is loaded, a known call an imported entry does not admit" do
      refused (without "addPartial") "called with 2"

    it "refuses, where it is loaded, a partial application an imported entry does not admit" do
      refused (without "addCalled") "partially applied to 1"

    it "refuses a foreign it does not yet reach" do
      let
        withForeign = libModule
          { decls = libModule.decls <> [ DeclForeign 9 { name: Ident "now", scheme: monoScheme (pureFn int int), attributes: [] } ] }
      case compileAll [ intModule, withForeign ] of
        Right compiled -> case Array.last compiled of
          Just lib -> case generate { runtime: runtimeSpecifier } lib.dmo of
            Left (Unsupported _) -> pure unit
            other -> fail ("expected the foreign to be refused, got " <> show (map (const unit) other))
          Nothing -> fail "nothing compiled"
        Left err -> fail err

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
-- | saying what the call supplied.
refused :: Module P.Int -> P.String -> Aff Unit
refused main saying =
  case compileAll [ intModule, libModule, main ], compileAll [ intModule, libShrunk ] of
    Right against, Right shrunk -> do
      let dmos = map _.dmo shrunk <> Array.drop 2 (map _.dmo against)
      case generated dmos of
        Left err -> fail err
        Right files -> do
          message <- fromEffectFnAff (importFailureImpl files (fileName mainName))
          (String.contains (String.Pattern "Lib.addTo") message && String.contains (String.Pattern saying) message)
            `shouldEqual` true
    _, _ -> fail "the modules did not compile"

-- | The function of the first closure with a capture that the initializer of the
-- | named global builds.
capturingClosure :: Dmo -> P.String -> Maybe P.Int
capturingClosure dmo name = do
  g <- Array.find (\g -> g.name == inMain name) dmo.globals
  f <- case g.init of
    GRun (FuncIx i) -> Array.index dmo.functions i
    GFunc (FuncIx i) -> Array.index dmo.functions i
  Array.findMap
    ( case _ of
        CLOS _ (FuncIx c) captures | not (Array.null captures) -> Just c
        _ -> Nothing
    )
    f.body.code

-- | Whether a function takes a capture and its entry node reads one with `CAPT`.
readsCapture :: Dmo -> P.Int -> P.Boolean
readsCapture dmo index = case Array.index dmo.functions index of
  Nothing -> false
  Just f ->
    not (Array.null f.captures)
      && Array.any
        ( case _ of
            CAPT _ _ -> true
            _ -> false
        )
        f.body.code

-- | The entry segment of a function, as the generated source writes it.
segmentOf :: P.Int -> P.String -> P.String
segmentOf index source =
  case String.indexOf (String.Pattern ("function f" <> show index <> "_s0(")) source of
    Nothing -> ""
    Just start ->
      let
        rest = String.drop start source
      in
        case String.indexOf (String.Pattern "\n}\n") rest of
          Just end -> String.take end rest
          Nothing -> rest

foreign import runtimeRefusals :: P.Array { name :: P.String, refused :: P.Boolean }

-- | One thing a loader refuses, as a change to one module, and the refusal it gives.
type LoaderRefusal =
  { name :: P.String
  , change :: { int :: Dmo, main :: Dmo } -> Dmo
  , refusal :: JsError -> P.Boolean
  }

-- | Where the changed module is generated anyway, or refused for another reason,
-- | what happened.
unrefused :: Dmo -> Dmo -> LoaderRefusal -> Maybe P.String
unrefused intDmo mainDmo r = case generate { runtime: runtimeSpecifier } (r.change { int: intDmo, main: mainDmo }) of
  Left e | r.refusal e -> Nothing
  Left e -> Just (r.name <> ": refused as " <> show e)
  Right _ -> Just (r.name <> ": generated")

loaderRefusals :: P.Array LoaderRefusal
loaderRefusals =
  [ { name: "a module named Prim"
    , change: \m -> m.main { name = ModuleName "Prim" }
    , refusal: case _ of
        ReservedModuleName _ -> true
        _ -> false
    }
  , { name: "a constructor another module declares"
    , change: \m -> m.main { ctors = Array.modifyAtIndices [ 0 ] (\c -> c { name = Qualified (ModuleName "Other") (Ident "Nil") }) m.main.ctors }
    , refusal: case _ of
        NotThisModule _ -> true
        _ -> false
    }
  , { name: "a constructor whose owner another module declares"
    , change: \m -> m.main { ctors = Array.modifyAtIndices [ 0 ] (\c -> c { owner = Qualified (ModuleName "Other") (TyName "List") }) m.main.ctors }
    , refusal: case _ of
        OwnerNotThisModule _ -> true
        _ -> false
    }
  , { name: "a global declared twice"
    , change: \m -> m.main { globals = m.main.globals <> Array.take 1 m.main.globals }
    , refusal: case _ of
        DeclaredTwice _ -> true
        _ -> false
    }
  , { name: "an export naming no declaration"
    , change: \m -> m.main { exports = m.main.exports <> [ inMain "nowhere" ] }
    , refusal: case _ of
        ExportNotDeclared _ -> true
        _ -> false
    }
  , { name: "a run global over a function of parameters"
    , change: \m -> installing "summed" (GRun <<< FuncIx) (\f -> f.nparams > 0) m.main
    , refusal: case _ of
        RunGlobalWithParameters _ _ -> true
        _ -> false
    }
  , { name: "a function global over a function of no parameters"
    , change: \m -> installing "sum" (GFunc <<< FuncIx) (\f -> f.nparams == 0) m.main
    , refusal: case _ of
        FunctionGlobalWithoutParameters _ -> true
        _ -> false
    }
  , { name: "a global over a function expecting captures"
    , change: \m -> installing "sum" (GFunc <<< FuncIx) (\f -> f.nparams > 0 && not (Array.null f.captures)) m.main
    , refusal: case _ of
        GlobalExpectsCaptures _ _ -> true
        _ -> false
    }
  , { name: "an unimplemented operation only PRIMS holds"
    , change: \m -> m.main { prims = m.main.prims <> [ NumberAdd ] }
    , refusal: case _ of
        OperationNotImplemented NumberAdd -> true
        _ -> false
    }
  , { name: "an operation declared at another arity"
    , change: \m -> m.int { foreigns = map (\f -> if f.name == inInt "add" then f { arity = 3 } else f) m.int.foreigns }
    , refusal: case _ of
        OperationDeclaredAtWrongArity _ 2 3 -> true
        _ -> false
    }
  ]

-- | The module with the named global installed over the first function `which`
-- | admits, as `how` installs one.
installing :: P.String -> (P.Int -> GlobalInit) -> (B.Function -> P.Boolean) -> Dmo -> Dmo
installing name how which dmo = case Array.findIndex which dmo.functions of
  Nothing -> dmo
  Just i -> dmo { globals = map (\g -> if g.name == inMain name then g { init = how i } else g) dmo.globals }

-- Linking --------------------------------------------------------------------------------

type LibBuild = Either P.String (P.Array Dmo)

lib0 :: LibBuild
lib0 = map (map _.dmo) (compileAll [ intModule, libModule ])

compileLib :: Module P.Int -> LibBuild
compileLib lib = map (map _.dmo) (compileAll [ intModule, lib ])

-- | `Lib` with its constructor renamed where it is declared and where its own code
-- | names it, so what `Main` imports as `ctor Box` exists nowhere.
renamedBox :: LibBuild -> LibBuild
renamedBox = map \dmos -> map rename dmos
  where
  rename dmo
    | dmo.name == libName =
        dmo
          { ctors = map (\c -> if c.name == inLib "Box" then c { name = inLib "Crate" } else c) dmo.ctors
          , ctorRefs = map (\q -> if q == inLib "Box" then inLib "Crate" else q) dmo.ctorRefs
          }
    | otherwise = dmo

-- | `main`, compiled against `Lib` as written, linked beside the `Lib` that `change`
-- | makes, and refused naming what `saying` names.
linkRefused :: Module P.Int -> (LibBuild -> LibBuild) -> P.String -> LibBuild -> Aff Unit
linkRefused main change saying base =
  case compileAll [ intModule, libModule, main ], change base of
    Right against, Right changed -> do
      let dmos = changed <> Array.drop 2 (map _.dmo against)
      case generated dmos of
        Left err -> fail err
        Right files -> do
          message <- fromEffectFnAff (importFailureImpl files (fileName mainName))
          String.contains (String.Pattern saying) message `shouldEqual` true
    Left err, _ -> fail err
    _, Left err -> fail err

-- | A `Main` naming `Lib` only where no arity check reaches: `held` reads a global
-- | as a value, and `peek` dispatches on a constructor and reads its field without
-- | building one. What refuses a missing export here is linking, and only that.
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

-- | `module Base.Number where foreign add : Number -> Number -> Number`, which the
-- | ABI fixes as an operation this backend does not carry out yet.
numberModule :: Module P.Int
numberModule =
  { annotation: 0
  , name: ModuleName "Base.Number"
  , imports: []
  , exports: [ ExportValue (Ident "add") ]
  , decls:
      [ DeclForeign 1
          { name: Ident "add", scheme: monoScheme (pureFn number (pureFn number number)), attributes: [] }
      ]
  }

number :: Type
number = TCon numberTy []

-- | `plusOne = Base.Number.add 1.0`: the operation applied short of its arity, and
-- | saturated nowhere in the module.
papOnly :: Module P.Int
papOnly =
  { annotation: 0
  , name: mainName
  , imports: [ ModuleName "Base.Number" ]
  , exports: [ ExportValue (Ident "plusOne") ]
  , decls:
      [ nonrec 1 "plusOne" (pureFn number number) $
          app (global (Qualified (ModuleName "Base.Number") (Ident "add"))) [ num 1.0 ]
      ]
  }

-- | Whether some function of the module builds a partial application whose callee
-- | is `Base.Number.add`'s operation.
papOfNumberAdd :: Dmo -> P.Boolean
papOfNumberAdd dmo = Array.any (\f -> Array.any isPap f.body.code) dmo.functions
  where
  isPap = case _ of
    PAP _ (CalleeIx i) _ -> Array.index dmo.callees i == Just (CalleePrim NumberAdd)
    _ -> false
