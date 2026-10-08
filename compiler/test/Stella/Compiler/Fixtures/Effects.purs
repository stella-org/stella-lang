-- | The hand-written Core of the effect fixtures: handlers, `perform` in both
-- | clause forms, continuations, and regions.
-- |
-- | Every expected value is what Core's rules give
-- | ([Semantics](../../../../../docs/technical-references/03-Typed-Core/06-Semantics.md)),
-- | worked out beside each value. Where a value guards a property of how a
-- | continuation is re-entered, its comment says what an implementation lacking
-- | that property gives instead.
-- |
-- | | Value of `Main` | What it exercises |
-- | | --- | --- |
-- | | `counted` | a `fast` clause reading and writing the region around its handler |
-- | | `resumedTwice` | a `full` clause applying its continuation twice |
-- | | `resumedOnce`, `abandoned` | a `full` clause resuming in tail position, and one answering without resuming, which skips the return clause |
-- | | `innermost`, `forwarded` | the innermost marker of a key answers; an operation an inner handler does not handle reaches the outer one |
-- | | `contOverApplied` | a continuation applied to two arguments |
-- | | `foldedOrder`, `chainedOrder` | an argument is evaluated before the function (D35), whether or not the spine folds into one call (D30) |
-- | | `regionForked` | a region inside a continuation, each resumption starting from the cells as captured |
-- | | `ownedFork` | a `full` clause of a handler inside a region, resuming twice and using the region's cells between |
-- | | `interleaved` | one resumption held captured while a second runs through the same activation |
-- | | `askedOutside`, `readOutside`, `writtenOutside`, `installedByBody`, `forkedTwice` | a `fast` clause's body runs outside the handler and outside `Ev_k` |
module Test.Stella.Compiler.Fixtures.Effects
  ( effectsModule
  , effectsExpected
  , meterModule
  ) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Stella.Compiler.TypedCore (Cell, DecisionTree(..), Decl(..), EffName(..), Export(..), Expr(..), Ident(..), Literal(..), Module, Occurrence(..), OpClause(..), OpDecl, OpName(..), Qualified(..), RegionName(..), RowEntry(..), RowKey(..), Symbol(..), Type(..), monoScheme)
import Stella.Compiler.TypedCore.Prim (booleanTy, fn, intTy, pureFn, unitCtor, unitTy)
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

bool :: Type
bool = TCon booleanTy []

rowOf :: P.Array (Qualified EffName) -> Type
rowOf = Array.foldr (\eff rest -> TRowExtend (RowEffectEntry eff []) rest) TRowEmpty

-- | `( region r | residual )`, the row everything inside the region named stands
-- | at.
regionRow :: P.String -> Type -> Type
regionRow region residual = TRowExtend (RowRegionEntry (RegionName region)) residual

cell :: RowKey
cell = SymbolKey (Symbol "n")

-- | `( n : Int )`, the layout of every region here.
cellLayout :: P.Array Cell
cellLayout = [ { key: cell, ty: int } ]

-- | `readCell r.n` and `writeCell r.n e`, for the region named.
readN :: P.String -> Expr P.Int
readN region = ReadCell 0 (RegionName region) cell

writeN :: P.String -> Expr P.Int -> Expr P.Int
writeN region = WriteCell 0 (RegionName region) cell

-- | `Unit ->* τ`, an operation of that argument and resumption type.
operation :: P.String -> Type -> OpDecl
operation name resumesWith = { name: OpName name, tyBinders: [], argument: unit', resumesWith }

effectDecl :: P.Int -> P.String -> P.Array OpDecl -> Decl P.Int
effectDecl at name operations = DeclEffect at { name: EffName name, params: [], operations, attributes: [] }

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

-- | `Base.Int.name x y` at the empty row.
intOp :: P.String -> Expr P.Int -> Expr P.Int -> Expr P.Int
intOp name x y = app (Global 0 (inInt name) []) [ x, y ]

-- | `Base.Int.name x y` at a row that is not empty. The arrows of a foreign are pure
-- | and containment is never inserted, so each application carries a widening of
-- | its own (D8).
intOpAt :: Type -> P.String -> Expr P.Int -> Expr P.Int -> Expr P.Int
intOpAt row name x y =
  App 0 (OpenEff 0 row (App 0 (OpenEff 0 row (Global 0 (inInt name) [])) x)) y

-- | `Main.name ()` at the empty row, and widened to `row`.
call :: P.String -> Expr P.Int
call name = App 0 (Global 0 (inMain name) []) unitValue

callWidened :: Type -> P.String -> Expr P.Int
callWidened row name = App 0 (OpenEff 0 row (Global 0 (inMain name) [])) unitValue

identityReturn :: { binder :: Ident, ty :: Type, body :: Expr P.Int }
identityReturn = { binder: Ident "x", ty: int, body: var "x" }

fast :: P.String -> Expr P.Int -> OpClause P.Int
fast op body = FastClause
  { op: OpName op, tyBinders: [], argBinder: { name: Ident "u", ty: unit' }, body }

-- | A `full` clause whose continuation `k` resumes with `resumesWith` at `row` and
-- | answers with `answer`.
full :: P.String -> Type -> Type -> Type -> Expr P.Int -> OpClause P.Int
full op resumesWith row answer body = FullClause
  { op: OpName op
  , tyBinders: []
  , argBinder: { name: Ident "u", ty: unit' }
  , contBinder: { name: Ident "k", ty: fn resumesWith row answer }
  , body
  }

-- | `handle handled with { handles eff ; clauses ; return }`, inside a region of the
-- | cell `n` where one is given: `region [r] ( n : Int ) @ ( initial ) in handle …`.
handle
  :: Qualified EffName
  -> Maybe { region :: P.String, initial :: P.Int }
  -> { binder :: Ident, ty :: Type, body :: Expr P.Int }
  -> P.Array (OpClause P.Int)
  -> Expr P.Int
  -> Expr P.Int
handle eff region returnClause opClauses handled = case region of
  Nothing -> handled'
  Just r -> Region 0 (RegionName r.region) cellLayout [ lit r.initial ] handled'
  where
  handled' = Handle 0 handled { element: RowEffectEntry eff [], returnClause, opClauses }

-- | A handler of one operation answering it with a `fast` clause.
handleFast :: Qualified EffName -> P.String -> Maybe { region :: P.String, initial :: P.Int } -> Expr P.Int -> Expr P.Int -> Expr P.Int
handleFast eff op region body = handle eff region identityReturn [ fast op body ]

-- | `let v = readCell r.n + 1 in let _ = writeCell r.n v in v` at `row`: the cell's
-- | next value, left in the cell.
bump :: P.String -> Type -> Expr P.Int
bump region row =
  let' "v" int (intOpAt row "add" (readN region) (lit 1))
    $ let' "w" unit' (writeN region (var "v"))
    $ var "v"

-- The effects --------------------------------------------------------------------------------

counter :: Qualified EffName
counter = effect "Counter"

ask :: Qualified EffName
ask = effect "Ask"

trigger :: Qualified EffName
trigger = effect "Trigger"

fork :: Qualified EffName
fork = effect "Fork"

-- | `fork` resumes with an `Int` and `yield` with `Unit`: one effect of two
-- | operations, so that a handler of it answers both.
suspend :: Qualified EffName
suspend = effect "Suspend"

-- The module -----------------------------------------------------------------------------------

effectsModule :: Module P.Int
effectsModule =
  { annotation: 0
  , name: mainName
  , imports: [ intName ]
  , exports: map (ExportValue <<< Ident <<< fst') effectsExpected
  , decls:
      [ effectDecl 1 "Counter" [ operation "next" int ]
      , effectDecl 2 "Ask" [ operation "ask" int ]
      , effectDecl 3 "Trigger" [ operation "go" int ]
      , effectDecl 4 "Fork" [ operation "fork" int ]
      , effectDecl 5 "Suspend" [ operation "fork" int, operation "yield" unit' ]
      , nonrec 10 "counted" int counted
      , nonrec 11 "resumedTwice" int resumedTwice
      , nonrec 12 "resumedOnce" int resumedOnce
      , nonrec 13 "abandoned" int abandoned
      , nonrec 14 "innerAsk" (fn unit' TRowEmpty int) innerAsk
      , nonrec 15 "innermost" int innermost
      , nonrec 16 "forwarded" int forwarded
      , nonrec 17 "contOverApplied" int contOverApplied
      , nonrec 18 "subtract" (pureFn int (pureFn int int)) subtract
      , nonrec 19 "curried" (pureFn int (pureFn int int)) curried
      , nonrec 20 "foldedOrder" int (counting (spine "subtract"))
      , nonrec 21 "chainedOrder" int (counting (spine "curried"))
      , nonrec 22 "regionForked" int regionForked
      , nonrec 23 "ownedFork" int ownedFork
      , nonrec 24 "interleaved" int interleaved
      , nonrec 30 "shadowAsk" shadowType shadowAsk
      , nonrec 31 "shadowCell" shadowType shadowCell
      , nonrec 32 "shadowWrite" shadowType shadowWrite
      , nonrec 33 "askedOutside" int askedOutside
      , nonrec 34 "readOutside" int readOutside
      , nonrec 35 "writtenOutside" int writtenOutside
      , nonrec 36 "installedByBody" int installedByBody
      , nonrec 37 "forkedTwice" int forkedTwice
      ]
  }
  where
  fst' (Tuple a _) = a

nonrec :: P.Int -> P.String -> Type -> Expr P.Int -> Decl P.Int
nonrec at name ty value = DeclNonRec at { name: Ident name, scheme: monoScheme ty, value, attributes: [] }

effectsExpected :: P.Array (Tuple P.String Expected)
effectsExpected =
  [ Tuple "counted" (EInt 1)
  , Tuple "resumedTwice" (EInt 3)
  , Tuple "resumedOnce" (EInt 1006)
  , Tuple "abandoned" (EInt 42)
  , Tuple "innermost" (EInt 3)
  , Tuple "forwarded" (EInt 11)
  , Tuple "contOverApplied" (EInt 34)
  , Tuple "foldedOrder" (EInt (-1))
  , Tuple "chainedOrder" (EInt (-1))
  , Tuple "regionForked" (EInt 27)
  , Tuple "ownedFork" (EInt 223)
  , Tuple "interleaved" (EInt 3)
  , Tuple "askedOutside" (EInt 1)
  , Tuple "readOutside" (EInt 7)
  , Tuple "writtenOutside" (EInt 47)
  , Tuple "installedByBody" (EInt 9)
  , Tuple "forkedTwice" (EInt 17)
  ]

-- Handlers and continuations ---------------------------------------------------------------------

-- | The counting handler: its `fast` clause answers with the cell and leaves it one
-- | higher, the cell starting at 0.
counting :: Expr P.Int -> Expr P.Int
counting = handle counter (Just { region: "r", initial: 0 }) identityReturn
  [ fast "next"
      ( let' "v" int (readN "r")
          $ let' "w" unit' (writeN "r" (intOpAt (regionRow "r" TRowEmpty) "add" (var "v") (lit 1)))
          $ var "v"
      )
  ]

-- | `let a = next () in let b = next () in a + b` under the counting handler: the
-- | first gives 0 and the second 1, so 1.
counted :: Expr P.Int
counted = counting
  ( let' "a" int (perform counter "next")
      $ let' "b" int (perform counter "next")
      $ intOpAt (TRowExtend (RowEffectEntry counter []) (regionRow "r" TRowEmpty)) "add" (var "a") (var "b")
  )

-- | `handle (fork ()) with { full fork u k -> let first = k 1 in let second = k 2 in
-- | first + second }`: each application resumes from the `perform`, so 1 + 2 = 3
-- | (D33).
resumedTwice :: Expr P.Int
resumedTwice =
  handle fork Nothing identityReturn
    [ full "fork" int TRowEmpty int
        ( let' "first" int (app (var "k") [ lit 1 ])
            $ let' "second" int (app (var "k") [ lit 2 ])
            $ intOp "add" (var "first") (var "second")
        )
    ]
    (perform fork "fork")

-- | `fork () + 1` under a handler whose return clause adds 1000.
forkPlusOne :: P.Array (OpClause P.Int) -> Expr P.Int
forkPlusOne =
  \clauses -> handle fork Nothing plusThousand clauses
    (intOpAt (rowOf [ fork ]) "add" (perform fork "fork") (lit 1))
  where
  plusThousand = { binder: Ident "x", ty: int, body: intOp "add" (var "x") (lit 1000) }

-- | `full fork u k -> k 5`, a resumption in tail position: the body gives 6 and the
-- | return clause 1006, which is what the clause returns.
resumedOnce :: Expr P.Int
resumedOnce = forkPlusOne [ full "fork" int TRowEmpty int (app (var "k") [ lit 5 ]) ]

-- | `full fork u k -> 42`: the clause's value is the whole `handle`'s, and the return
-- | clause, which only a value of the body reaches, never runs. 42, where running it
-- | gives 1042.
abandoned :: Expr P.Int
abandoned = forkPlusOne [ full "fork" int TRowEmpty int (lit 42) ]

-- | `λu. handle (ask ()) with { fast ask u -> 2 }`, which handles `Ask` itself and is
-- | pure to its caller.
innerAsk :: Expr P.Int
innerAsk = lam "u" unit' (handleFast ask "ask" Nothing (lit 2) (perform ask "ask"))

-- | `handle (openEff [( Ask )] innerAsk () + ask ()) with { fast ask u -> 1 }`: the
-- | `ask` inside `innerAsk` reaches the marker `innerAsk` put above this one, 2, and
-- | the one after it this handler, 1. So 3; answering the first at the outer
-- | marker gives 2.
innermost :: Expr P.Int
innermost =
  handleFast ask "ask" Nothing (lit 1)
    ( let' "a" int (callWidened (rowOf [ ask ]) "innerAsk")
        $ let' "b" int (perform ask "ask")
        $ intOpAt (rowOf [ ask ]) "add" (var "a") (var "b")
    )

-- | `handle (handle (ask () + go ()) with { fast go u -> 10 }) with
-- | { fast ask u -> 1 }`: the inner handler does not handle `Ask`, so its `perform`
-- | reaches the outer one: 1 + 10 = 11.
forwarded :: Expr P.Int
forwarded =
  handleFast ask "ask" Nothing (lit 1)
    $ handleFast trigger "go" Nothing (lit 10)
        ( let' "a" int (perform ask "ask")
            $ let' "b" int (perform trigger "go")
            $ intOpAt (rowOf [ trigger, ask ]) "add" (var "a") (var "b")
        )

-- | `(handle (fork ()) with { full fork u k -> λz. k 3 4 + z ; return x -> λy. x * 10 + y }) 0`.
-- |
-- | The answer is a function, so the continuation is applied to its resumption
-- | value and to what the answer then takes: the body gives 3, the return clause
-- | `λy. 30 + y`, and that applied to 4 gives 34, to which the clause adds 0.
contOverApplied :: Expr P.Int
contOverApplied = flip (App 0) (lit 0) $
  handle fork Nothing
    { binder: Ident "x"
    , ty: int
    , body: lam "y" int (intOp "add" (intOp "mul" (var "x") (lit 10)) (var "y"))
    }
    [ full "fork" int TRowEmpty intToInt
        (lam "z" int (intOp "add" (app (var "k") [ lit 3, lit 4 ]) (var "z")))
    ]
    (perform fork "fork")
  where
  intToInt = fn int TRowEmpty int

-- Evaluation order -------------------------------------------------------------------------------

-- | `subtract n y = y - n`, a function of two parameters: its definitional arity is
-- | two, so a saturated application of it folds into one call (D30).
subtract :: Expr P.Int
subtract = lam "n" int $ lam "y" int $ intOp "sub" (var "y") (var "n")

-- | The same function with a definitional arity of **one**: applying it to two
-- | arguments is a call of one and then an application of what comes back.
curried :: Expr P.Int
curried = lam "n" int $ App 0 (Global 0 (inMain "subtract") []) (var "n")

-- | `f (next ()) (next ())` under the counting handler, with nothing between the two
-- | `perform`s to sequence them.
-- |
-- | **An application evaluates its argument before its function** (D35), so the
-- | second argument performs first and gets 0, the first gets 1, and `y - n` is
-- | `0 - 1`: -1, where the other order gives 1. Folding the spine into one call
-- | moves no effect, so both functions give -1 (D30).
spine :: P.String -> Expr P.Int
spine f =
  App 0
    (OpenEff 0 counterRow (App 0 (OpenEff 0 counterRow (Global 0 (inMain f) [])) (perform counter "next")))
    (perform counter "next")
  where
  counterRow = TRowExtend (RowEffectEntry counter []) (regionRow "r" TRowEmpty)

-- Re-entering a continuation ---------------------------------------------------------------------

-- | `handle (region [r] ( n : Int ) @ ( 10 ) in handle (let a = next () in
-- | let b = fork () in let c = next () in c + b) with { handles Counter ;
-- | fast next u -> bump }) with { full fork u k -> k 1 + k 2 }`.
-- |
-- | The continuation of `fork` holds the `Counter` handler and the region, whose
-- | cell holds 11 at the capture. Each resumption starts from that cell: `c` is 12
-- | both times, so 13 + 14 = 27. A region the two resumptions shared gives 12 and
-- | 13, so 28.
regionForked :: Expr P.Int
regionForked =
  handle fork Nothing identityReturn
    [ full "fork" int TRowEmpty int
        (intOp "add" (app (var "k") [ lit 1 ]) (app (var "k") [ lit 2 ]))
    ]
    $ handleFast counter "next" (Just { region: "r", initial: 10 }) (bump "r" (regionRow "r" forkRow))
        ( let' "a" int (perform counter "next")
            $ let' "b" int (perform fork "fork")
            $ let' "c" int (perform counter "next")
            $ intOpAt innerRow "add" (var "c") (var "b")
        )
  where
  forkRow = rowOf [ fork ]
  innerRow = TRowExtend (RowEffectEntry counter []) (regionRow "r" forkRow)

-- | `region [r] ( n : Int ) @ ( 0 ) in handle (fork () + 100) with { handles Fork ;
-- |   full fork u k -> let _ = writeCell r.n (readCell r.n + 1) in
-- |     let a = k (readCell r.n) in let _ = writeCell r.n (readCell r.n + 10) in
-- |     let b = k (readCell r.n) in a + b + readCell r.n }`.
-- |
-- | The region stands below the handler's marker and stays behind when the
-- | continuation is taken, so the clause's writes persist between the resumptions:
-- | `k 1` gives 101, `k 11` gives 111, and the cell ends at 11, so 223.
ownedFork :: Expr P.Int
ownedFork =
  handle fork (Just { region: "r", initial: 0 }) identityReturn
    [ full "fork" int clauseRow int
        ( let' "w1" unit' (writeN "r" (plus (readN "r") (lit 1)))
            $ let' "a" int (app (var "k") [ readN "r" ])
            $ let' "w2" unit' (writeN "r" (plus (readN "r") (lit 10)))
            $ let' "b" int (app (var "k") [ readN "r" ])
            $ plus (plus (var "a") (var "b")) (readN "r")
        )
    ]
    (intOpAt (TRowExtend (RowEffectEntry fork []) clauseRow) "add" (perform fork "fork") (lit 100))
  where
  clauseRow = regionRow "r" TRowEmpty
  plus = intOpAt clauseRow "add"

-- | `handle (let b = fork () in let _ = yield () in b) with
-- |   { full fork u k -> let f = k 1 in let g = k 2 in λv. f v + g v
-- |   ; full yield u k -> λv. k () v
-- |   ; return x -> λv. x } ()`.
-- |
-- | `k 1` runs the body on with `b = 1` until `yield`, whose clause takes the rest —
-- | the activation holding `b` among it — and answers with a function that resumes
-- | it: that is `f`. `k 2` then runs the same activation again with `b = 2`, which
-- | is `g`. Applying `f` resumes the first run, which reads its own `b`: 1 + 2 = 3.
-- | Had the two runs been one activation rather than two copies of the captured
-- | one, the second would have overwritten the first's `b`: 2 + 2 = 4.
interleaved :: Expr P.Int
interleaved =
  App 0
    ( handle suspend Nothing
        { binder: Ident "x", ty: int, body: lam "v" unit' (var "x") }
        [ full "fork" int TRowEmpty answer
            ( let' "f" answer (app (var "k") [ lit 1 ])
                $ let' "g" answer (app (var "k") [ lit 2 ])
                $ lam "v" unit' (intOp "add" (app (var "f") [ var "v" ]) (app (var "g") [ var "v" ]))
            )
        , full "yield" unit' TRowEmpty answer
            (lam "v" unit' (app (var "k") [ unitValue, var "v" ]))
        ]
        ( let' "b" int (perform suspend "fork")
            $ let' "y" unit' (perform suspend "yield")
            $ var "b"
        )
    )
    unitValue
  where
  answer = fn unit' TRowEmpty int

-- Where a fast clause's body runs --------------------------------------------------------------

-- | Core's `fast` rule binds the clause body **outside** the handler and outside the
-- | evaluation context `Ev_k` between the handler and the `perform`. That is
-- | observable only where `Ev_k` installs something the body could reach, so each
-- | value below puts one there: a handler of another effect, or a region declaring
-- | the same cell key, installed by a function the handled computation calls.

-- | `Unit -{ ( Trigger ) }-> Int`, the type of every function that installs something
-- | inside `Ev_k`.
shadowType :: Type
shadowType = fn unit' (rowOf [ trigger ]) int

-- | `λu. handle (go ()) with { handles Ask ; fast ask u -> 100 }`.
shadowAsk :: Expr P.Int
shadowAsk = lam "u" unit' $ handleFast ask "ask" Nothing (lit 100) (perform trigger "go")

-- | `λu. region [r2] ( n : Int ) @ ( 42 ) in handle (go ()) with { handles Ask ;
-- | fast ask u -> readCell r2.n }`: a region declaring the cell key the region
-- | around the `Trigger` handler declares.
shadowCell :: Expr P.Int
shadowCell = lam "u" unit'
  $ handleFast ask "ask" (Just { region: "r2", initial: 42 }) (readN "r2") (perform trigger "go")

-- | The same, asking its own region what `n` holds after `go`.
shadowWrite :: Expr P.Int
shadowWrite = lam "u" unit'
  $ handleFast ask "ask" (Just { region: "r2", initial: 42 }) (readN "r2")
      (let' "ignored" int (perform trigger "go") (perform ask "ask"))

-- | `handle (handle (openEff [( Ask )] shadowAsk ()) with { fast go u -> ask () })
-- | with { fast ask u -> 1 }`: the `Trigger` clause's `ask` reaches the `Ask`
-- | handler outside, 1, and not the one `shadowAsk` installed, 100.
askedOutside :: Expr P.Int
askedOutside =
  handleFast ask "ask" Nothing (lit 1)
    $ handleFast trigger "go" Nothing (perform ask "ask")
    $ callWidened (rowOf [ ask ]) "shadowAsk"

-- | `region [r] ( n : Int ) @ ( 7 ) in handle (shadowCell ()) with
-- | { fast go u -> readCell r.n }`: the clause reads the region it names, 7, and
-- | not `shadowCell`'s, 42.
readOutside :: Expr P.Int
readOutside =
  handleFast trigger "go" (Just { region: "r", initial: 7 }) (readN "r") (callWidened (regionRow "r" TRowEmpty) "shadowCell")

-- | `region [r] ( n : Int ) @ ( 7 ) in handle (let a = shadowWrite () in
-- | let b = go () in a + b) with { fast go u -> let old = readCell r.n in
-- |   let _ = writeCell r.n 5 in old }`.
-- |
-- | Inside `shadowWrite` the clause sets region `r`'s `n` to 5 and leaves the
-- | inner one at 42, so `a = 42`; the second `go` reads the 5 the first wrote, so
-- | `b = 5`: 47. A write reaching the inner region gives 5 + 7 = 12.
writtenOutside :: Expr P.Int
writtenOutside =
  handleFast trigger "go" (Just { region: "r", initial: 7 }) swap
    $ let' "a" int (callWidened (regionRow "r" TRowEmpty) "shadowWrite")
    $ let' "b" int (perform trigger "go")
    $ intOpAt (TRowExtend (RowEffectEntry trigger []) (regionRow "r" TRowEmpty)) "add" (var "a") (var "b")
  where
  swap =
    let' "old" int (readN "r")
      $ let' "w" unit' (writeN "r" (lit 5))
      $ var "old"

-- | `handle (shadowCell ()) with { fast go u -> region [r3] ( n : Int ) @ ( 9 ) in
-- |   handle (ask ()) with { fast ask u -> readCell r3.n } }`: what the body
-- | installs stands above its boundary and is found as usual, 9.
installedByBody :: Expr P.Int
installedByBody =
  handleFast trigger "go" Nothing
    (handleFast ask "ask" (Just { region: "r3", initial: 9 }) (readN "r3") (perform ask "ask"))
    (call "shadowCell")

-- | `handle (region [r] ( n : Int ) @ ( 7 ) in handle (openEff [( region r, Fork )]
-- |   shadowCell ()) with { fast go u -> let f = fork () in f + readCell r.n }) with
-- | { full fork u k -> k 1 + k 2 }`.
-- |
-- | The continuation of `fork` carries the `Trigger` clause's boundary, the `Trigger`
-- | handler, and what `shadowCell` installed, and re-pushes them twice. Each
-- | resumption continues the clause, which reads region `r`: 1 + 7 and 2 + 7,
-- | so 17. Reading the region inside gives 43 + 44, so 87.
forkedTwice :: Expr P.Int
forkedTwice =
  handle fork Nothing identityReturn
    [ full "fork" int TRowEmpty int
        (intOp "add" (app (var "k") [ lit 1 ]) (app (var "k") [ lit 2 ]))
    ]
    $ handleFast trigger "go" (Just { region: "r", initial: 7 }) forkThenRead
        (callWidened (regionRow "r" (rowOf [ fork ])) "shadowCell")
  where
  forkThenRead =
    let' "f" int (perform fork "fork")
      $ intOpAt (regionRow "r" (rowOf [ fork ])) "add" (var "f") (readN "r")

-- The refusal fixtures' source -------------------------------------------------------------------

-- | A module the handler refusals are made from by changing what it lowers to.
-- |
-- | `Meter` has two operations and a region of two cells around its handler, `reading` and
-- | `spare`, so a handler entry has a second clause and a second cell to turn into a
-- | repeat of the first, and one of each to leave out. `installed` installs it where
-- | something waits for the answer, a `HNDL`; `inBranch` installs it in tail
-- | position inside a branch, a `TAILHNDL` in a node the function's body holds
-- | inline.
meterModule :: Module P.Int
meterModule =
  { annotation: 0
  , name: mainName
  , imports: [ intName ]
  , exports: [ ExportValue (Ident "installed"), ExportValue (Ident "inBranch") ]
  , decls:
      [ effectDecl 1 "Meter" [ operation "bump" int, operation "peek" int ]
      , nonrec 2 "installed" int (intOp "add" metered (lit 1))
      , nonrec 3 "inBranch" (fn bool TRowEmpty int)
          ( lam "b" bool
              $ Case 0 [ var "b" ]
                  (SwitchLit (OccScrutinee 0) [ { lit: LitBoolean true, tree: Leaf metered } ] (Leaf (lit 0)))
          )
      ]
  }
  where
  meter = effect "Meter"
  reading = SymbolKey (Symbol "reading")
  spare = SymbolKey (Symbol "spare")
  cells = [ { key: reading, ty: int }, { key: spare, ty: int } ]
  region = RegionName "m"
  meterRow = TRowExtend (RowRegionEntry region) TRowEmpty
  metered =
    Region 0 region cells [ lit 0, lit 0 ]
      ( Handle 0 (perform meter "bump")
          { element: RowEffectEntry meter []
          , returnClause: identityReturn
          , opClauses:
              [ fast "bump"
                  ( let' "v" int (intOpAt meterRow "add" (ReadCell 0 region reading) (lit 1))
                      $ let' "w" unit' (WriteCell 0 region reading (var "v"))
                      $ var "v"
                  )
              , fast "peek" (ReadCell 0 region spare)
              ]
          }
      )
