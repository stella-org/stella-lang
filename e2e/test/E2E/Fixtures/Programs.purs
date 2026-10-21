-- | The Core of `programs-core`, and what the values of the source-built
-- | `programs`, `operations`, and fault fixtures hold
-- | ([Fixtures](../Fixtures.purs)).
-- |
-- | **What `Main` holds depends on a scale**: how far the values that recurse,
-- | loop, and jump go. `programs` is built at a scale every suite affords and
-- | `programs-deep` at the depths stack safety is tested at, observing those
-- | values alone.
module Test.E2E.Fixtures.Programs
  ( intName
  , mainName
  , inInt
  , baseInt
  , opsExpected
  , FaultCase
  , faultCases
  , coreOnlyModule
  , coreOnlyExpected
  , sourceExpected
  , sourceDeepExpected
  ) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Bifunctor (lmap)
import Data.Either (Either, note)
import Data.Foldable (foldM)
import Data.Enum (toEnum)
import Data.Maybe (fromMaybe)
import Data.String.CodePoints as CodePoints
import Data.Tuple (Tuple(..))
import Stella.Compiler.Elaborate.Environment.Imported (importedSignature)
import Stella.Compiler.Interface.Environment (addInterface, initialEnvironment, viewFor)
import Stella.Compiler.Macro.Compiled (Interface, compiled)
import Stella.Compiler.TypedCore (DecisionTree(..), Decl(..), Export(..), Expr(..), Ident(..), JoinName(..), LitBranch, Literal(..), Module, ModuleName(..), Occurrence(..), Qualified(..), RowEntry(..), RowKey(..), Symbol(..), Type(..), monoScheme)
import Stella.Compiler.TypedCore.Prim (booleanTy, intTy, recordTy)
import Stella.Compiler.TypedCore.Signature (Signature)
import Test.E2E.Fixtures.Value (Expected(..), ExpectedKey(..))

-- Names --------------------------------------------------------------------------------

intName :: ModuleName
intName = ModuleName "Base.Int"

mainName :: ModuleName
mainName = ModuleName "Main"

inInt :: P.String -> Qualified Ident
inInt = Qualified intName <<< Ident

int :: Type
int = TCon intTy []

bool :: Type
bool = TCon booleanTy []

symbolKey :: P.String -> RowKey
symbolKey = SymbolKey <<< Symbol

rowOf :: P.Array (Tuple RowKey Type) -> Type
rowOf = Array.foldr (\(Tuple k t) rest -> TRowExtend (RowTypeEntry k t) rest) TRowEmpty

recordOf :: P.Array (Tuple RowKey Type) -> Type
recordOf fields = TApp (TCon recordTy []) (rowOf fields)

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

intOp :: P.String -> Expr P.Int -> Expr P.Int -> Expr P.Int
intOp name a b = app (global (inInt name)) [ a, b ]

-- | `case (scrutinee) of lit_i -> e_i ; _ -> default`.
litCase :: Expr P.Int -> P.Array (Tuple Literal (Expr P.Int)) -> Expr P.Int -> Expr P.Int
litCase scrutinee branches default =
  Case 0 [ scrutinee ]
    ( SwitchLit (OccScrutinee 0)
        (map (\(Tuple l e) -> { lit: l, tree: Leaf e } :: LitBranch P.Int) branches)
        (Leaf default)
    )

-- The modules ----------------------------------------------------------------------------

nonrec :: P.Int -> P.String -> Type -> Expr P.Int -> Decl P.Int
nonrec at name ty value = DeclNonRec at { name: Ident name, scheme: monoScheme ty, value, attributes: [] }

-- | How far the values that recurse, loop, and jump go, and what each comes to.
type Scale =
  { list :: P.Int
  , listSum :: P.Int
  , count :: P.Int
  , parity :: P.Int
  , loop :: P.Int
  , loopSum :: P.Int
  }

-- | The scale every suite runs `programs` at.
usual :: Scale
usual = { list: 100, listSum: 5050, count: 1000, parity: 101, loop: 100, loopSum: 5050 }

-- | The scale stack safety is tested at, `programs-deep`'s. 1 + … + 100000 is
-- | 5000050000, which wraps modulo 2³² to 705082704.
deep :: Scale
deep = { list: 100000, listSum: 705082704, count: 1000000, parity: 100001, loop: 100000, loopSum: 705082704 }

-- | The values a scale reaches.
scaled :: P.Array P.String
scaled = [ "deepSum", "counted", "evenOdd", "looped" ]

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

-- The operations ----------------------------------------------------------------------------

-- | What the Core of a fixture is compiled against: `Base.Int` as the compiler
-- | carries it, its signature read off its interface as an importer reads it,
-- | and the arities a translation reads of it. `Base.Int` is not compiled here:
-- | a fixture holds `Base.Int.dmo` as its source builds it, the bytes the
-- | compiler carries.
baseInt :: Either P.String { signature :: Signature, interface :: Interface }
baseInt = do
  carried <- compiled
  env <- lmap show (foldM (flip addInterface) initialEnvironment carried.moduleInterfaces)
  view <- lmap show (viewFor [ intName ] env)
  signature <- lmap show (importedSignature env view)
  interface <- note "the compiler carries no Base.Int" (Array.find (\i -> i.name == intName) carried.interfaces)
  pure { signature, interface }

-- | The string of one scalar value, written by its code rather than in the source.
scalar :: P.Int -> P.String
scalar c = fromMaybe "" (CodePoints.singleton <$> toEnum c)

minInt :: P.Int
minInt = -2147483648

maxInt :: P.Int
maxInt = 2147483647

-- | What each value of the `operations` fixture's `Main` holds, fixed from the
-- | ABI's meaning by hand
-- | ([Prim and Base](../../../../docs/technical-references/06-Modules/02-Prim-and-Base.md)).
opsExpected :: P.Array (Tuple P.String Expected)
opsExpected =
  [ Tuple "intAddWraps" (EInt minInt)
  , Tuple "intSubWraps" (EInt maxInt)
  , Tuple "intMulWraps" (EInt 0)
  , Tuple "intMulWide" (EInt 1)
  , Tuple "quotOverflows" (EInt minInt)
  , Tuple "remOverflows" (EInt 0)
  , Tuple "quotTruncates" (EInt (-3))
  , Tuple "remTakesDividendSign" (EInt (-1))
  , Tuple "intEq" (EBoolean true)
  , Tuple "intLt" (EBoolean false)
  , Tuple "intToNumber" (ENumber (-5.0))
  , Tuple "intToStringMin" (EString "-2147483648")
  , Tuple "numberAdd" (ENumber (0.1 + 0.2))
  , Tuple "subZero" (ENumber 0.0)
  , Tuple "negateZero" (ENumber (-0.0))
  , Tuple "divideByZero" (ENumber (1.0 / 0.0))
  , Tuple "numberMul" (ENumber (0.1 * 3.0))
  , Tuple "eqNaN" (EBoolean false)
  , Tuple "eqZeros" (EBoolean true)
  , Tuple "ltNaN" (EBoolean false)
  , Tuple "floorNegative" (ENumber (-1.0))
  , Tuple "ceilPositive" (ENumber 1.0)
  , Tuple "truncNegative" (ENumber (-0.0))
  , Tuple "toIntNaN" (EInt 0)
  , Tuple "toIntLarge" (EInt maxInt)
  , Tuple "toIntNegative" (EInt (-2))
  , Tuple "toStringExponent" (EString "1e+21")
  , Tuple "toStringPositional" (EString "100000000000000000000")
  , Tuple "toStringSmall" (EString "1e-7")
  , Tuple "toStringTenth" (EString "0.1")
  , Tuple "toStringNegativeZero" (EString "0")
  , Tuple "stringLength" (EInt 4)
  , Tuple "codePointAtAstral" (EChar 0x1F600)
  , Tuple "appendStrings" (EString "abc")
  , Tuple "sliceScalars" (EString (smile <> "b"))
  , Tuple "singletonAstral" (EString smile)
  , Tuple "stringEq" (EBoolean true)
  , Tuple "ltAstral" (EBoolean true)
  , Tuple "ltPrefix" (EBoolean true)
  , Tuple "ltSame" (EBoolean false)
  , Tuple "charRoundTrip" (EInt 0x1F600)
  , Tuple "arrayReadBack" (EInt 20)
  , Tuple "arrayLength" (EInt 3)
  , Tuple "arraySetLater" (EInt 7)
  , Tuple "numberAddLater" (ENumber 2.5)
  ]
  where
  smile = scalar 0x1F600

-- | One way an operation faults: a fixture whose `Main` carries it out on inputs
-- | the ABI says it faults on as `Main.faulted` is initialized, so that is where
-- | the fault must end loading. Its source is `fixtures/source/<name>`.
type FaultCase = { name :: P.String, description :: P.String }

faultCases :: P.Array FaultCase
faultCases =
  [ f "fault-quot-zero" "Base.Int.quot by zero"
  , f "fault-rem-zero" "Base.Int.rem by zero"
  , f "fault-code-point-at-outside" "Base.String.codePointAt at an index past the last scalar value"
  , f "fault-slice-reversed" "Base.String.slice with its start past its end"
  , f "fault-slice-past-end" "Base.String.slice with its end past the length"
  , f "fault-slice-negative" "Base.String.slice with a negative start, which is not counted from the end"
  , f "fault-from-code-point-surrogate" "Base.Char.fromCodePoint of a surrogate"
  , f "fault-from-code-point-above" "Base.Char.fromCodePoint past 0x10FFFF"
  , f "fault-from-code-point-negative" "Base.Char.fromCodePoint of a negative number"
  , f "fault-array-new-negative" "Base.Array.unsafeNew with a negative count"
  , f "fault-array-set-outside" "Base.Array.unsafeSet at an index outside the array"
  , f "fault-array-index-outside" "Base.Array.unsafeIndex at an index outside the array"
  , f "fault-recursive-initializer" "Base.Int.quot by zero initializing a recursive group nothing refers to"
  , f "fault-local-recursive-initializer" "Base.Int.quot by zero initializing a local recursive group its body does not read"
  ]
  where
  f name description = { name, description }

-- | What each value of the Core `Main` holds at a scale, fixed from the program
-- | by hand.
expectedAt :: Scale -> P.Array (Tuple P.String Expected)
expectedAt scale =
  [ Tuple "summed" (EInt 6)
  , Tuple "deepSum" (EInt scale.listSum)
  , Tuple "counted" (EInt scale.count)
  , Tuple "listValue" (cons 1 (cons 2 (cons 3 nil)))
  -- curried 10 3 = subtract 10 3 = 3 - 10
  , Tuple "overApplied" (EInt (-7))
  , Tuple "papApplied" (EInt 9)
  , Tuple "ctorPap" (EInt 1)
  , Tuple "captured" (EInt 8)
  -- each scale's parity is odd
  , Tuple "evenOdd" (EBoolean false)
  , Tuple "joined" (EInt 101)
  , Tuple "looped" (EInt scale.loopSum)
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
  -- once (once 5)
  , Tuple "dictTwice" (EInt 7)
  -- (10 + 2) + (20 + 1)
  , Tuple "mutualPair" (EInt 33)
  , Tuple "localDict" (EInt 7)
  , Tuple "localPair" (EInt 33)
  -- 40 + 2, `go` reading the cell `table` it was allocated before
  , Tuple "localMixed" (EInt 42)
  ]
  where
  cons x xs = EData "Main.Cons" [ EInt x, xs ]
  nil = EData "Main.Nil" []

-- The values no source writes ------------------------------------------------------------

-- | The `Main` of `programs-core`: the values whose Core no source elaborates
-- | to, kept in Core so that what they exercise stays exercised. A join point
-- | two leaves share and one jumping to itself, at the usual scale and at the
-- | depth stack safety is tested at; `merge`, which no form of the surface
-- | writes; and a `Number` dispatch by literal identity, which the surface
-- | leaves to a guard.
coreOnlyModule :: Module P.Int
coreOnlyModule =
  { annotation: 0
  , name: mainName
  , imports: [ intName ]
  , exports: map (ExportValue <<< Ident) (map (\(Tuple n _) -> n) coreOnlyExpected)
  , decls:
      [ nonrec 1 "joined" int joinedBody
      , nonrec 2 "looped" int (loopedBody usual.loop)
      , nonrec 3 "loopedDeep" int (loopedBody deep.loop)
      , nonrec 4 "recordShape" (recordOf [ Tuple (symbolKey "y") bool ]) $
          RecordRestrict 0 (symbolKey "x")
            (RecordMerge 0 (RecordExtend 0 (symbolKey "x") (lit 1) (RecordEmpty 0)) (RecordExtend 0 (symbolKey "y") (Lit 0 (LitBoolean true)) (RecordEmpty 0)))
      , nonrec 5 "negZero" int $ litCase (num (-0.0)) [ Tuple (LitNumber 0.0) (lit 1), Tuple (LitNumber (-0.0)) (lit 2) ] (lit 3)
      , nonrec 6 "posZero" int $ litCase (num 0.0) [ Tuple (LitNumber (-0.0)) (lit 1) ] (lit 2)
      , nonrec 7 "nanCase" int $ litCase (num (0.0 / 0.0)) [ Tuple (LitNumber (0.0 / 0.0)) (lit 1) ] (lit 2)
      ]
  }

-- | What each value of `programs-core`'s `Main` holds.
coreOnlyExpected :: P.Array (Tuple P.String Expected)
coreOnlyExpected =
  [ Tuple "joined" (EInt 101)
  , Tuple "looped" (EInt usual.loopSum)
  , Tuple "loopedDeep" (EInt deep.loopSum)
  , Tuple "recordShape" (ERecord [ { key: KField "y", value: EBoolean true } ])
  , Tuple "negZero" (EInt 2)
  , Tuple "posZero" (EInt 2)
  , Tuple "nanCase" (EInt 1)
  ]

-- | What each value of the source-built `Main` of `programs` holds, at the
-- | scale given: every value of the Core `Main` but those `programs-core`
-- | holds, a list's constructors being `Data.List`'s, a record a pattern's rest
-- | binds, and the values over the functions of `Data.List` and `Data.Maybe`.
sourceExpected :: P.Array (Tuple P.String Expected)
sourceExpected = sourceExpectedAt usual

-- | `sourceExpected` at the depth stack safety is tested at, the values a scale
-- | reaches alone.
sourceDeepExpected :: P.Array (Tuple P.String Expected)
sourceDeepExpected = Array.filter (\(Tuple name _) -> Array.elem name scaled) (sourceExpectedAt deep)

sourceExpectedAt :: Scale -> P.Array (Tuple P.String Expected)
sourceExpectedAt scale = map listsFromData (Array.filter (\(Tuple name _) -> not (Array.elem name coreOnly)) (expectedAt scale)) <> libraries
  where
  libraries =
    [ Tuple "restricted" (ERecord [ { key: KField "y", value: EBoolean true } ])
    , Tuple "listMapped" (list [ 30, 20, 10 ])
    , Tuple "listFoldedLeft" (EInt 40)
    , Tuple "listFoldedRight" (EInt 20)
    , Tuple "listLength" (EInt 3)
    , Tuple "maybeJust" (EInt 42)
    , Tuple "maybeNothing" (EInt 7)
    ]
  list = Array.foldr (\x rest -> EData "Data.List.Cons" [ EInt x, rest ]) (EData "Data.List.Nil" [])
  coreOnly = [ "joined", "looped", "recordShape", "negZero", "posZero", "nanCase" ]
  listsFromData (Tuple name e) = Tuple name (relist e)
  relist = case _ of
    EData "Main.Cons" fields -> EData "Data.List.Cons" (map relist fields)
    EData "Main.Nil" fields -> EData "Data.List.Nil" (map relist fields)
    other -> other
