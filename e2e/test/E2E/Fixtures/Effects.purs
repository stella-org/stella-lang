-- | What the values of the effect fixtures hold, and the hand-written Core of
-- | `effects-core`: handlers, `perform` in both clause forms, continuations, and
-- | regions. `contOverApplied` and `interleaved` are the Core below; the others
-- | are built from source, in `effects`.
-- |
-- | Every expected value is what Core's rules give
-- | ([Semantics](../../../../docs/technical-references/03-Typed-Core/06-Semantics.md)),
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
module Test.E2E.Fixtures.Effects
  ( effectsCoreModule
  , effectsCoreExpected
  , effectsSourceExpected
  ) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Stella.Compiler.TypedCore (Cell, Decl(..), EffName(..), Export(..), Expr(..), Ident(..), Literal(..), Module, OpClause(..), OpDecl, OpName(..), Qualified(..), RegionName(..), RowEntry(..), RowKey(..), Symbol(..), Type(..), monoScheme)
import Stella.Compiler.TypedCore.Prim (fn, intTy, unitCtor, unitTy)
import Test.E2E.Fixtures.Programs (inInt, intName, mainName)
import Test.E2E.Fixtures.Value (Expected(..))

-- Names and types ------------------------------------------------------------------------

effect :: P.String -> Qualified EffName
effect = Qualified mainName <<< EffName

int :: Type
int = TCon intTy []

unit' :: Type
unit' = TCon unitTy []

cell :: RowKey
cell = SymbolKey (Symbol "n")

-- | `( n : Int )`, the layout of every region here.
cellLayout :: P.Array Cell
cellLayout = [ { key: cell, ty: int } ]

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

-- | A pure λ.
lam :: P.String -> Type -> Expr P.Int -> Expr P.Int
lam name ty = Lam 0 (Ident name) ty TRowEmpty

app :: Expr P.Int -> P.Array (Expr P.Int) -> Expr P.Int
app = Array.foldl (App 0)

unitValue :: Expr P.Int
unitValue = Global 0 unitCtor []

perform :: Qualified EffName -> P.String -> Expr P.Int
perform eff op = Perform 0 (EffectKey eff) (OpName op) [] unitValue

-- | `Base.Int.name x y` at the empty row.
intOp :: P.String -> Expr P.Int -> Expr P.Int -> Expr P.Int
intOp name x y = app (Global 0 (inInt name) []) [ x, y ]

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

-- The effects --------------------------------------------------------------------------------

fork :: Qualified EffName
fork = effect "Fork"

-- | `fork` resumes with an `Int` and `yield` with `Unit`: one effect of two
-- | operations, so that a handler of it answers both.
suspend :: Qualified EffName
suspend = effect "Suspend"

-- What the values hold -------------------------------------------------------------------------

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

-- Re-entering a continuation ---------------------------------------------------------------------

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

-- The values no source writes -------------------------------------------------------------------

-- | The `Main` of `effects-core`: the continuations a clause keeps beyond itself
-- | as a plain continuation, which the surface keeps only inside a reifiable
-- | clause, and so as no continuation applied directly. A continuation applied
-- | to two arguments, and one held captured while a second resumption runs
-- | through the same activation.
effectsCoreModule :: Module P.Int
effectsCoreModule =
  { annotation: 0
  , name: mainName
  , imports: [ intName ]
  , exports: map (ExportValue <<< Ident <<< fst') effectsCoreExpected
  , decls:
      [ effectDecl 4 "Fork" [ operation "fork" int ]
      , effectDecl 5 "Suspend" [ operation "fork" int, operation "yield" unit' ]
      , nonrec 17 "contOverApplied" int contOverApplied
      , nonrec 24 "interleaved" int interleaved
      ]
  }
  where
  fst' (Tuple a _) = a

effectsCoreExpected :: P.Array (Tuple P.String Expected)
effectsCoreExpected = Array.filter (\(Tuple name _) -> Array.elem name coreOnly) effectsExpected
  where
  coreOnly = [ "contOverApplied", "interleaved" ]

-- | What each value of the source-built `Main` of `effects` holds: every value
-- | of the Core `Main` but those `effects-core` holds.
effectsSourceExpected :: P.Array (Tuple P.String Expected)
effectsSourceExpected = Array.filter (\(Tuple name _) -> not (Array.elem name (map (\(Tuple n _) -> n) effectsCoreExpected))) effectsExpected
