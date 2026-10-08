-- | The hand-written Core of the region fixtures: which frame a cell reaches, and
-- | which cells a resumption shares or copies.
-- |
-- | A region opened inside the computation a `full` clause captures is part of the
-- | captured segment, so every resumption starts from a copy of its cells as they
-- | were at the capture; a region opened outside it is not, and every resumption
-- | shares it. A cell is reached by the identity of the opening its code was
-- | written under, and the innermost frame of that identity is the copy running.
-- |
-- | Every expected value is what Core's rules give
-- | ([Semantics](../../../../../docs/technical-references/03-Typed-Core/06-Semantics.md)),
-- | worked out beside each value together with what reaching the wrong frame, or
-- | sharing what is copied, gives instead.
-- |
-- | | Value of `Main` | What it exercises |
-- | | --- | --- |
-- | | `sharedGroups` | two handlers inside one region, each reading the other's write |
-- | | `choiceState`, `stateChoice` | a region inside and outside a handler resuming twice: per resumption, and shared |
-- | | `localClosure` | a clause building a function over the region's cell and calling it |
-- | | `declaredApart` | a function opening a region of its own, applied inside another region declaring the same key |
-- | | `recursed` | a function opening a region applied inside its own clause, a closure over the outer region called in the inner clause |
-- | | `nestedCopy` | a continuation resumed while a copy of it is running |
-- | | `closureBefore` | a closure made before a capture, run in two copies |
-- | | `stashed` | a closure carried out through an operation's type parameter and handed back to two copies |
module Test.Stella.Compiler.Fixtures.Regions
  ( regionsModule
  , regionsExpected
  ) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Tuple (Tuple(..))
import Stella.Compiler.TypedCore (Constraint(..), DecisionTree(..), Decl(..), EffName(..), Export(..), Expr(..), Ident(..), Kind(..), Literal(..), Module, Occurrence(..), OpClause(..), OpDecl, OpName(..), Qualified(..), RegionName(..), RowElemKind(..), RowEntry(..), RowKey(..), Symbol(..), TyVar(..), Type(..), TypeScheme, monoScheme)
import Stella.Compiler.TypedCore.Prim (fn, intTy, pureFn, unitCtor, unitTy)
import Test.Stella.Compiler.Fixtures.Programs (inInt, intName, mainName)
import Test.Stella.Compiler.Fixtures.Value (Expected(..))

-- Names and types ------------------------------------------------------------------------

inMain :: P.String -> Qualified Ident
inMain = Qualified mainName <<< Ident

effect :: P.String -> Qualified EffName
effect = Qualified mainName <<< EffName

int :: Type
int = TCon intTy []

unit' :: Type
unit' = TCon unitTy []

intToInt :: Type
intToInt = pureFn int int

-- | `( e₁, …, eₙ | rest )`.
rowWith :: P.Array (Qualified EffName) -> Type -> Type
rowWith effs rest = Array.foldr (\eff r -> TRowExtend (RowEffectEntry eff []) r) rest effs

-- | `( region r | rest )`.
regionRow :: P.String -> Type -> Type
regionRow name rest = TRowExtend (RowRegionEntry (RegionName name)) rest

-- | The key of every region's one cell. Regions apart declare it alike, which is
-- | what makes reaching the wrong one observable.
n :: RowKey
n = SymbolKey (Symbol "n")

-- Terms ------------------------------------------------------------------------------------

var :: P.String -> Expr P.Int
var = Var 0 <<< Ident

lit :: P.Int -> Expr P.Int
lit = Lit 0 <<< LitInt

let' :: P.String -> Type -> Expr P.Int -> Expr P.Int -> Expr P.Int
let' name = Let 0 (Ident name)

lam :: P.String -> Type -> Expr P.Int -> Expr P.Int
lam name = Lam 0 (Ident name)

app :: Expr P.Int -> P.Array (Expr P.Int) -> Expr P.Int
app = Array.foldl (App 0)

unitValue :: Expr P.Int
unitValue = Global 0 unitCtor []

perform :: Qualified EffName -> P.String -> Expr P.Int
perform eff op = Perform 0 (EffectKey eff) (OpName op) [] unitValue

-- | `f ()` for a function whose row is the ambient one.
call :: Expr P.Int -> Expr P.Int
call f = App 0 f unitValue

-- | `Base.Int.name x y` at `row`. The arrows of a foreign are pure and containment
-- | is never inserted, so each application is widened to the row unless it is
-- | empty (D8).
intOpAt :: Type -> P.String -> Expr P.Int -> Expr P.Int -> Expr P.Int
intOpAt row name x y = case row of
  TRowEmpty -> app (Global 0 (inInt name) []) [ x, y ]
  _ -> App 0 (OpenEff 0 row (App 0 (OpenEff 0 row (Global 0 (inInt name) [])) x)) y

-- | `region [name] ( n : Int ) @ ( initial ) in body`.
region :: P.String -> Expr P.Int -> Expr P.Int -> Expr P.Int
region name initial = Region 0 (RegionName name) [ { key: n, ty: int } ] [ initial ]

readN :: P.String -> Expr P.Int
readN name = ReadCell 0 (RegionName name) n

writeN :: P.String -> Expr P.Int -> Expr P.Int
writeN name = WriteCell 0 (RegionName name) n

-- | `let _ = writeCell r.n (readCell r.n + by) in rest`, at `row`.
bumpBy :: P.String -> Type -> Expr P.Int -> Expr P.Int -> Expr P.Int
bumpBy name row by rest =
  let' ("w" <> name) unit' (writeN name (intOpAt row "add" (readN name) by)) rest

identityReturn :: { binder :: Ident, ty :: Type, body :: Expr P.Int }
identityReturn = { binder: Ident "x", ty: int, body: var "x" }

handle :: Qualified EffName -> P.Array (OpClause P.Int) -> Expr P.Int -> Expr P.Int
handle eff opClauses handled =
  Handle 0 handled { element: RowEffectEntry eff [], returnClause: identityReturn, opClauses }

fast :: P.String -> Expr P.Int -> OpClause P.Int
fast op body = FastClause
  { op: OpName op, tyBinders: [], argBinder: { name: Ident "u", ty: unit' }, body }

-- | A `full` clause taking `Unit`, whose continuation `k` resumes with `resumesWith`
-- | at `row` and answers with `Int`.
full :: P.String -> Type -> Type -> Expr P.Int -> OpClause P.Int
full op resumesWith row body = FullClause
  { op: OpName op
  , tyBinders: []
  , argBinder: { name: Ident "u", ty: unit' }
  , contBinder: { name: Ident "k", ty: fn resumesWith row int }
  , body
  }

-- The effects --------------------------------------------------------------------------------

effA :: Qualified EffName
effA = effect "A"

effB :: Qualified EffName
effB = effect "B"

flipEff :: Qualified EffName
flipEff = effect "Flip"

bumpEff :: Qualified EffName
bumpEff = effect "Bump"

counter :: Qualified EffName
counter = effect "Counter"

ask :: Qualified EffName
ask = effect "Ask"

tick :: Qualified EffName
tick = effect "Tick"

branch :: Qualified EffName
branch = effect "Branch"

split :: Qualified EffName
split = effect "Split"

stash :: Qualified EffName
stash = effect "Stash"

-- | `Unit ->* τ`.
operation :: P.String -> Type -> OpDecl
operation name resumesWith = { name: OpName name, tyBinders: [], argument: unit', resumesWith }

effectDecl :: P.Int -> P.String -> P.Array OpDecl -> Decl P.Int
effectDecl at name operations = DeclEffect at { name: EffName name, params: [], operations, attributes: [] }

-- The module -----------------------------------------------------------------------------------

regionsModule :: Module P.Int
regionsModule =
  { annotation: 0
  , name: mainName
  , imports: [ intName ]
  , exports: map (\(Tuple name _) -> ExportValue (Ident name)) regionsExpected
  , decls:
      [ effectDecl 1 "A" [ operation "a" int ]
      , effectDecl 2 "B" [ operation "b" int ]
      , effectDecl 3 "Flip" [ operation "flip" int ]
      , effectDecl 4 "Bump" [ operation "bump" int ]
      , effectDecl 5 "Counter" [ operation "next" int ]
      , effectDecl 6 "Ask" [ operation "ask" int ]
      , effectDecl 7 "Tick" [ operation "tick" int ]
      , effectDecl 8 "Branch" [ operation "branch" intToInt ]
      , effectDecl 9 "Split" [ operation "split" int ]
      , effectDecl 10 "Stash"
          [ { name: OpName "stash"
            , tyBinders: [ { name: TyVar "a", kind: KType } ]
            , argument: TVar (TyVar "a")
            , resumesWith: TVar (TyVar "a")
            }
          ]
      , nonrec 20 "sharedGroups" int sharedGroups
      , nonrec 21 "choiceState" int choiceState
      , nonrec 22 "stateChoice" int stateChoice
      , nonrec 23 "localClosure" int localClosure
      , nonrec 24 "counting" countingScheme counting
      , nonrec 25 "declaredApart" int declaredApart
      , DeclRec 26 [ { name: Ident "nest", scheme: nestScheme, value: nest, attributes: [] } ]
      , nonrec 27 "recursed" int recursed
      , nonrec 28 "nestedCopy" int nestedCopy
      , nonrec 29 "closureBefore" int closureBefore
      , nonrec 30 "stashed" int stashed
      ]
  }

nonrec :: P.Int -> P.String -> Type -> Expr P.Int -> Decl P.Int
nonrec at name ty value = DeclNonRec at { name: Ident name, scheme: monoScheme ty, value, attributes: [] }

regionsExpected :: P.Array (Tuple P.String Expected)
regionsExpected =
  [ Tuple "sharedGroups" (EInt 1011)
  , Tuple "choiceState" (EInt 111)
  , Tuple "stateChoice" (EInt 112)
  , Tuple "localClosure" (EInt 607)
  , Tuple "declaredApart" (EInt 10010)
  , Tuple "recursed" (EInt 21)
  , Tuple "nestedCopy" (EInt 1023)
  , Tuple "closureBefore" (EInt 102)
  , Tuple "stashed" (EInt 101)
  ]

-- One region, two handlers ---------------------------------------------------------------------

-- | `region [r] ( n : Int ) @ ( 0 ) in handle (handle (let x = a () in let y = b () in
-- | let z = a () in y * 100 + z) with { fast a u -> n += 1 ; n }) with
-- | { fast b u -> n *= 10 ; n }`.
-- |
-- | Both clauses reach the one cell: `a` makes it 1, `b` 10, and `a` 11, so
-- | 10 * 100 + 11. Cells of each handler's own give 1, 0, and 2.
sharedGroups :: Expr P.Int
sharedGroups =
  region "r" (lit 0)
    $ handle effB
        [ fast "b"
            ( let' "v" int (intOpAt rowB "mul" (readN "r") (lit 10))
                $ let' "w" unit' (writeN "r" (var "v"))
                $ var "v"
            )
        ]
    $ handle effA
        [ fast "a"
            ( let' "v" int (intOpAt rowA "add" (readN "r") (lit 1))
                $ let' "w" unit' (writeN "r" (var "v"))
                $ var "v"
            )
        ]
    $ let' "x" int (perform effA "a")
    $ let' "y" int (perform effB "b")
    $ let' "z" int (perform effA "a")
    $ intOpAt rowBody "add" (intOpAt rowBody "mul" (var "y") (lit 100)) (var "z")
  where
  -- the row each clause stands at, which is the row around its handler
  rowB = regionRow "r" TRowEmpty
  rowA = rowWith [ effB ] rowB
  rowBody = rowWith [ effA ] rowA

-- A region inside and outside a handler resuming twice ------------------------------------------

-- | `handle body with { full flip u k -> let x = k 0 in let y = k 1 in x * 100 + y }`,
-- | at the row the handler stands at.
flipping :: Type -> Expr P.Int -> Expr P.Int
flipping row =
  handle flipEff [ full "flip" int row (twice row (lit 0) (lit 1)) ]

-- | `let x = k first in let y = k second in x * 100 + y`, at `row`. The `let`s are
-- | what orders the two resumptions: an application evaluates its argument first
-- | (D35).
twice :: Type -> Expr P.Int -> Expr P.Int -> Expr P.Int
twice row first second =
  let' "x" int (app (var "k") [ first ])
    $ let' "y" int (app (var "k") [ second ])
    $ intOpAt row "add" (intOpAt row "mul" (var "x") (lit 100)) (var "y")

-- | `let b = flip () in n += 1 ; b * 10 + n`, at the row it stands at, which holds the
-- | region and `Flip`.
flipBody :: Type -> Expr P.Int
flipBody row =
  let' "b" int (perform flipEff "flip")
    $ bumpBy "r" row (lit 1)
    $ intOpAt row "add" (intOpAt row "mul" (var "b") (lit 10)) (readN "r")

-- | `handle (region [r] ( n : Int ) @ ( 0 ) in flipBody) with flipping`.
-- |
-- | The region is opened inside the computation the clause captures, so each
-- | resumption starts from the cell at 0: 1 and 11, so 111. Sharing the cell gives
-- | 1 and 12, so 112 (Hoop's fixture 26, and Koka's `choice(state)`).
choiceState :: Expr P.Int
choiceState =
  flipping TRowEmpty
    $ region "r" (lit 0)
    $ flipBody (regionRow "r" (rowWith [ flipEff ] TRowEmpty))

-- | `region [r] ( n : Int ) @ ( 0 ) in handle flipBody with flipping`.
-- |
-- | The region stands below the handler, outside what the clause captures, so the
-- | second resumption sees the first's write: 1 and 12, so 112. Copying the cell
-- | gives 111 (Hoop's fixture 27, and Koka's `state(choice)`).
stateChoice :: Expr P.Int
stateChoice =
  region "r" (lit 0)
    $ flipping (regionRow "r" TRowEmpty)
    $ flipBody (rowWith [ flipEff ] (regionRow "r" TRowEmpty))

-- A clause's own function over the cell ---------------------------------------------------------

-- | `region [r] ( n : Int ) @ ( 5 ) in handle (let a = bump () in let b = bump () in
-- | a * 100 + b) with { fast bump u -> let f = λw. n in let _ = n := f () + 1 in f () }`.
-- |
-- | The function the clause builds reads the cell it was built over: 6 and 7, so 607.
localClosure :: Expr P.Int
localClosure =
  region "r" (lit 5)
    $ handle bumpEff
        [ fast "bump"
            ( let' "f" (fn unit' clauseRow int) (lam "w" unit' (readN "r"))
                $ let' "w" unit' (writeN "r" (intOpAt clauseRow "add" (call (var "f")) (lit 1)))
                $ call (var "f")
            )
        ]
    $ let' "a" int (perform bumpEff "bump")
    $ let' "b" int (perform bumpEff "bump")
    $ intOpAt bodyRow "add" (intOpAt bodyRow "mul" (var "a") (lit 100)) (var "b")
  where
  clauseRow = regionRow "r" TRowEmpty
  bodyRow = rowWith [ bumpEff ] clauseRow

-- A function opening a region of its own ---------------------------------------------------------

-- | `( Unit -{ ( Counter, Ask ) }-> Int ) -{ ( Ask ) }-> Int`
countingScheme :: Type
countingScheme = fn (fn unit' (rowWith [ counter, ask ] TRowEmpty) int) (rowWith [ ask ] TRowEmpty) int

-- | `λthunk. region [r] ( n : Int ) @ ( 0 ) in handle (thunk ()) with
-- | { fast next u -> let v = n in let _ = n := v + 1 in v }`, what a handler
-- | declaration with a cell is a function of a thunk to.
counting :: Expr P.Int
counting =
  lam "thunk" (fn unit' (rowWith [ counter, ask ] TRowEmpty) int)
    $ region "r" (lit 0)
    $ handle counter
        [ fast "next"
            ( let' "v" int (readN "r")
                $ bumpBy "r" clauseRow (lit 1)
                $ var "v"
            )
        ]
    $ call (OpenEff 0 (regionRow "r" TRowEmpty) (var "thunk"))
  where
  clauseRow = regionRow "r" (rowWith [ ask ] TRowEmpty)

-- | `region [s] ( n : Int ) @ ( 100 ) in handle (counting (λu. let a = next () in
-- | let b = next () in let c = ask () in a + b * 10 + c * 100)) with
-- | { fast ask u -> let v = n in let _ = n := v + 1 in v }`.
-- |
-- | `counting` opens a region declaring `n` too, and each clause reaches its own:
-- | 0, 1, and 100, so 10010. A clause reaching the other's cell gives anything else.
declaredApart :: Expr P.Int
declaredApart =
  region "s" (lit 100)
    $ handle ask
        [ fast "ask"
            ( let' "v" int (readN "s")
                $ bumpBy "s" clauseRow (lit 1)
                $ var "v"
            )
        ]
    $ App 0 (OpenEff 0 (regionRow "s" TRowEmpty) (Global 0 (inMain "counting") []))
        ( lam "u" unit'
            $ let' "a" int (perform counter "next")
            $ let' "b" int (perform counter "next")
            $ let' "c" int (perform ask "ask")
            $ intOpAt thunkRow "add"
                (intOpAt thunkRow "add" (var "a") (intOpAt thunkRow "mul" (var "b") (lit 10)))
                (intOpAt thunkRow "mul" (var "c") (lit 100))
        )
  where
  clauseRow = regionRow "s" TRowEmpty
  thunkRow = rowWith [ counter, ask ] TRowEmpty

-- The same function applied inside its own clause --------------------------------------------------

rowVar :: Type
rowVar = TVar (TyVar "e")

tickLacks :: Constraint
tickLacks = Lacks (EffectKey tick) rowVar

-- | `forall (e : Row Effect). Tick ∉ e =>`
-- | `Int -> ( Unit -{ e }-> Int ) -> ( Unit -{ ( Tick | e ) }-> Int ) -{ e }-> Int`
nestScheme :: TypeScheme
nestScheme = monoScheme
  ( TForall (TyVar "e") (KRow RowEffect)
      ( TConstrained tickLacks
          ( pureFn int
              (pureFn (fn unit' rowVar int) (fn (fn unit' (rowWith [ tick ] rowVar) int) rowVar int))
          )
      )
  )

-- | `λinit probe thunk. region [r] ( n : Int ) @ ( init ) in handle (thunk ()) with
-- | { fast tick u -> case n of 1 -> nest 2 (λw. n) (λw. tick ()) ; m -> m * 10 + probe () }`.
-- |
-- | Applied with 1, the clause applies `nest` again inside itself, with a probe over
-- | its own region. That opens a second region of the same name and declaring the
-- | same key, whose clause runs inside the first's.
nest :: Expr P.Int
nest =
  TyLam 0 (TyVar "e") (KRow RowEffect)
    $ ConstraintLam 0 tickLacks
    $ lam "init" int
    $ lam "probe" (fn unit' rowVar int)
    $ lam "thunk" (fn unit' (rowWith [ tick ] rowVar) int)
    $ region "r" (var "init")
    $ handle tick
        [ fast "tick"
            ( Case 0 [ readN "r" ]
                ( SwitchLit (OccScrutinee 0)
                    [ { lit: LitInt 1, tree: Leaf again } ]
                    ( Bind (Ident "m") (OccScrutinee 0)
                        ( Leaf
                            ( intOpAt clauseRow "add"
                                (intOpAt clauseRow "mul" (var "m") (lit 10))
                                (call (OpenEff 0 (regionRow "r" TRowEmpty) (var "probe")))
                            )
                        )
                    )
                )
            )
        ]
    $ call (OpenEff 0 (regionRow "r" TRowEmpty) (var "thunk"))
  where
  clauseRow = regionRow "r" rowVar
  -- `nest` at the clause's row: its two pure arrows are widened to it, and the
  -- last arrow already stands at it
  again =
    app
      ( OpenEff 0 clauseRow
          ( App 0
              (OpenEff 0 clauseRow (ConstraintApp 0 (TyApp 0 (Global 0 (inMain "nest") []) clauseRow)))
              (lit 2)
          )
      )
      [ lam "w" unit' (readN "r")
      , lam "w" unit' (perform tick "tick")
      ]

-- | `nest 1 (λu. 0) (λu. tick ())`.
-- |
-- | The first `tick` reaches the outer clause, which reads 1 and applies `nest 2`
-- | with a probe over the outer region. The inner `tick` reaches the inner clause,
-- | which reads its own 2 and calls the probe, which reads the outer region's 1:
-- | 2 * 10 + 1, so 21. A probe reaching the innermost region of its name reads 2,
-- | so 22.
recursed :: Expr P.Int
recursed =
  app (ConstraintApp 0 (TyApp 0 (Global 0 (inMain "nest") []) TRowEmpty))
    [ lit 1
    , lam "u" unit' (lit 0)
    , lam "u" unit' (perform tick "tick")
    ]

-- A continuation resumed while a copy of it runs ----------------------------------------------------

-- | `handle (region [r] ( n : Int ) @ ( 0 ) in let f = branch () in n += 1 ;
-- | let x = f n in n += 10 ; x + n) with
-- | { full branch u k -> k (λv. k (λw. 1000 * v + w)) }`.
-- |
-- | The first copy calls `f 1`, which resumes the continuation again, so a second
-- | copy runs on top of the first. Each copy's code reaches its own region: the
-- | second makes `n` 1, then 11, and gives 1001 + 11; the first, its `n` at 1,
-- | makes it 11 and gives 1012 + 11, so 1023. The second copy reaching the first
-- | one's region gives 1036.
nestedCopy :: Expr P.Int
nestedCopy =
  handle branch
    [ full "branch" intToInt TRowEmpty
        ( app (var "k")
            [ lam "v" int
                ( app (var "k")
                    [ lam "w" int (intOpAt TRowEmpty "add" (intOpAt TRowEmpty "mul" (lit 1000) (var "v")) (var "w")) ]
                )
            ]
        )
    ]
    $ region "r" (lit 0)
    $ let' "f" intToInt (perform branch "branch")
    $ bumpBy "r" row (lit 1)
    $ let' "x" int (App 0 (OpenEff 0 row (var "f")) (readN "r"))
    $ bumpBy "r" row (lit 10)
    $ intOpAt row "add" (var "x") (readN "r")
  where
  row = regionRow "r" (rowWith [ branch ] TRowEmpty)

-- A closure made before a capture -------------------------------------------------------------------

-- | `handle (region [r] ( n : Int ) @ ( 0 ) in let g = λu. n in let s = split () in
-- | n += s ; g ()) with { full split u k -> let x = k 1 in let y = k 2 in x * 100 + y }`.
-- |
-- | `g` was made before the capture, and each copy running it reaches that copy's
-- | region: 1 and 2, so 102. Sharing the region gives 1 and 3, so 103.
closureBefore :: Expr P.Int
closureBefore =
  handle split
    [ full "split" int TRowEmpty (twice TRowEmpty (lit 1) (lit 2)) ]
    $ region "r" (lit 0)
    $ let' "g" (fn unit' row int) (lam "u" unit' (readN "r"))
    $ let' "s" int (perform split "split")
    $ bumpBy "r" row (var "s")
    $ call (var "g")
  where
  row = regionRow "r" (rowWith [ split ] TRowEmpty)

-- | `handle (region [r] ( n : Int ) @ ( 0 ) in let g = λu. n in let h = stash g in
-- | n += 1 ; h ()) with { full stash [a] v k -> let x = k v in let y = k v in
-- | x * 100 + y }`.
-- |
-- | The closure leaves through the operation's type parameter, which the clause
-- | knows nothing of, and comes back into both copies; each runs it against its
-- | own region: 1 and 1, so 101. Sharing the region gives 1 and 2, so 102.
stashed :: Expr P.Int
stashed =
  handle stash
    [ FullClause
        { op: OpName "stash"
        , tyBinders: [ { name: TyVar "a", kind: KType } ]
        , argBinder: { name: Ident "v", ty: TVar (TyVar "a") }
        , contBinder: { name: Ident "k", ty: fn (TVar (TyVar "a")) TRowEmpty int }
        , body: twice TRowEmpty (var "v") (var "v")
        }
    ]
    $ region "r" (lit 0)
    $ let' "g" closure (lam "u" unit' (readN "r"))
    $ let' "h" closure (Perform 0 (EffectKey stash) (OpName "stash") [ closure ] (var "g"))
    $ bumpBy "r" row (lit 1)
    $ call (var "h")
  where
  row = regionRow "r" (rowWith [ stash ] TRowEmpty)
  closure = fn unit' row int
