-- | Where a `fast` clause's body runs, carried the whole way: Typed Core, checked,
-- | translated, lowered, encoded, decoded, loaded, and run.
-- |
-- | Core's `fast` rule binds the clause body **outside** the handler and outside
-- | the evaluation context `Ev_k` between the handler and the `perform`
-- | ([Semantics](../../../docs/technical-references/03-Typed-Core/06-Semantics.md)).
-- | What that decides is observable only where `Ev_k` itself installs something
-- | the body could reach, so each value here puts one there: a handler of another
-- | effect, or a region declaring the same cell key, installed by a function that
-- | the handled computation calls. The expected value is the one the rule gives.
-- |
-- | | Value | What it shows | Rule's answer | Reaching into `Ev_k` |
-- | | --- | --- | --- | --- |
-- | | `askedOutside` | an operation the body performs reaches the handler outside | 1 | 100, from the `Ask` handler inside |
-- | | `readOutside` | `readCell` reaches the handler's own region | 7 | 42, from the region inside |
-- | | `writtenOutside` | `writeCell` sets the handler's own region and leaves the inner one alone | 47 | 12 |
-- | | `installedByBody` | what the body installs itself is found as usual | 9 | — |
-- | | `forkedTwice` | a `full` operation the body performs, resumed twice, leaves the body still outside `Ev_k` | 17 | 87 |
module Test.Steam.FastClause (spec) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Ref as Ref
import Run (runBaseEffect)
import Run.Except as Except
import Steam.Foreign (emptyTable)
import Steam.Load (LoadError, Store, emptyStore, globalNamed, load, noIdentities)
import Steam.Value (Value(..))
import Stella.Compiler.Bytecode (Dmo, decode, encode, lower)
import Stella.Compiler.Interface (noImports)
import Stella.Compiler.MiddleEnd (translate)
import Stella.Compiler.TypedCore (Decl(..), EffName(..), Export(..), Expr(..), Ident(..), Layout, Literal(..), Module, ModuleName(..), OpClause(..), OpName(..), Qualified(..), RowEntry(..), RowKey(..), Symbol(..), TyVar(..), Type(..), declareAnnotated, monoScheme, primSignature)
import Stella.Compiler.TypedCore.Prim (fn, intTy, pureFn, unitCtor, unitTy)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

-- Names ------------------------------------------------------------------------------

intModuleName :: ModuleName
intModuleName = ModuleName "Base.Int"

mainModuleName :: ModuleName
mainModuleName = ModuleName "Main"

intAdd :: Qualified Ident
intAdd = Qualified intModuleName (Ident "add")

askEff :: Qualified EffName
askEff = Qualified mainModuleName (EffName "Ask")

triggerEff :: Qualified EffName
triggerEff = Qualified mainModuleName (EffName "Trigger")

forkEff :: Qualified EffName
forkEff = Qualified mainModuleName (EffName "Fork")

askOp :: OpName
askOp = OpName "ask"

goOp :: OpName
goOp = OpName "go"

forkOp :: OpName
forkOp = OpName "fork"

cellKey :: RowKey
cellKey = SymbolKey (Symbol "n")

inMain :: P.String -> Qualified Ident
inMain name = Qualified mainModuleName (Ident name)

-- Types ------------------------------------------------------------------------------

int :: Type
int = TCon intTy []

unit' :: Type
unit' = TCon unitTy []

effectRow :: Qualified EffName -> Type
effectRow eff = TRowExtend (RowEffectEntry eff []) TRowEmpty

askRow :: Type
askRow = effectRow askEff

triggerRow :: Type
triggerRow = effectRow triggerEff

forkRow :: Type
forkRow = effectRow forkEff

layoutRow :: Type
layoutRow = TRowExtend (RowTypeEntry cellKey int) TRowEmpty

layoutOver :: P.String -> Layout
layoutOver var = { var: TyVar var, cells: [ { key: cellKey, ty: int } ] }

-- | `( region r ( n : Int ) | residual )`, the row a clause of a handler owning a
-- | region stands at.
clauseRowOver :: P.String -> Type -> Type
clauseRowOver var residual =
  TRowExtend (RowRegionEntry (TVar (TyVar var)) layoutRow) residual

-- | `Unit -{ ( Trigger ) }-> Int`, the type of every function that installs
-- | something inside `Ev_k`.
shadowType :: Type
shadowType = fn unit' triggerRow int

-- Terms ------------------------------------------------------------------------------

unitValue :: Expr P.Int
unitValue = Global 0 unitCtor []

perform :: Qualified EffName -> OpName -> Expr P.Int
perform eff op = Perform 0 (EffectKey eff) op [] unitValue

var :: P.String -> Expr P.Int
var name = Var 0 (Ident name)

int' :: P.Int -> Expr P.Int
int' n = Lit 0 (LitInt n)

call :: P.String -> Expr P.Int
call name = App 0 (Global 0 (inMain name) []) unitValue

-- | `openEff [row] f ()`.
callWidened :: Type -> P.String -> Expr P.Int
callWidened row name = App 0 (OpenEff 0 row (Global 0 (inMain name) [])) unitValue

-- | `Base.Int.add x y` at a row that is not empty, each application carrying a
-- | widening of its own (D8).
added :: Type -> Expr P.Int -> Expr P.Int -> Expr P.Int
added row x y =
  App 0 (OpenEff 0 row (App 0 (OpenEff 0 row (Global 0 intAdd [])) x)) y

identityReturn :: { binder :: Ident, ty :: Type, body :: Expr P.Int }
identityReturn = { binder: Ident "x", ty: int, body: var "x" }

fastClause :: OpName -> Expr P.Int -> OpClause P.Int
fastClause op body = FastClause
  { op
  , tyBinders: []
  , argBinder: { name: Ident "u", ty: unit' }
  , body
  }

-- | A handler of one operation answering it with `body`, owning a region over
-- | the cell `n` where `region` names one.
handling
  :: Qualified EffName
  -> OpName
  -> Maybe { var :: P.String, initial :: P.Int }
  -> Expr P.Int
  -> Expr P.Int
  -> Expr P.Int
handling eff op region clauseBody handled =
  Handle 0 handled
    { element: RowEffectEntry eff []
    , cells: map (\r -> layoutOver r.var) region
    , returnClause: identityReturn
    , opClauses: [ fastClause op clauseBody ]
    }
    (Array.fromFoldable (map (\r -> int' r.initial) region))

-- The modules --------------------------------------------------------------------------

intModule :: Module P.Int
intModule =
  { annotation: 0
  , name: intModuleName
  , imports: []
  , exports: [ ExportValue (Ident "add") ]
  , decls:
      [ DeclForeign 1
          { name: Ident "add"
          , scheme: monoScheme (pureFn int (pureFn int int))
          , attributes: []
          }
      ]
  }

mainModule :: Module P.Int
mainModule =
  { annotation: 0
  , name: mainModuleName
  , imports: [ intModuleName ]
  , exports: []
  , decls:
      [ effectDecl 1 "Ask" askOp
      , effectDecl 2 "Trigger" goOp
      , effectDecl 3 "Fork" forkOp
      , nonrec 4 "shadowAsk" shadowType shadowAsk
      , nonrec 5 "shadowCell" shadowType shadowCell
      , nonrec 6 "shadowWrite" shadowType shadowWrite
      , nonrec 7 "askedOutside" int askedOutside
      , nonrec 8 "readOutside" int readOutside
      , nonrec 9 "writtenOutside" int writtenOutside
      , nonrec 10 "installedByBody" int installedByBody
      , nonrec 11 "forkedTwice" int forkedTwice
      ]
  }

-- | `effect E where op : Unit ->* Int`.
effectDecl :: P.Int -> P.String -> OpName -> Decl P.Int
effectDecl at name op = DeclEffect at
  { name: EffName name
  , params: []
  , operations: [ { name: op, tyBinders: [], argument: unit', resumesWith: int } ]
  , attributes: []
  }

nonrec :: P.Int -> P.String -> Type -> Expr P.Int -> Decl P.Int
nonrec at name ty value = DeclNonRec at
  { name: Ident name, scheme: monoScheme ty, value, attributes: [] }

-- | `λu. handle (perform Trigger.go ()) with { handles Ask ; fast ask u -> 100 }`.
-- |
-- | Handling `Ask` inside leaves `( Trigger )` as its row, so a caller whose row
-- | already holds `Ask` reaches it through `openEff` and puts a second `Ask` marker
-- | above its own handlers at run time.
shadowAsk :: Expr P.Int
shadowAsk = Lam 0 (Ident "u") unit'
  $ handling askEff askOp Nothing (int' 100) (perform triggerEff goOp)

-- | `λu. handle (perform Trigger.go ()) with { handles Ask ; cells [r2] ( n : Int ) ;
-- | fast ask u -> readCell n } @ ( 42 )`: a region inside whatever calls it,
-- | declaring the cell key the `Trigger` handler's region declares.
shadowCell :: Expr P.Int
shadowCell = Lam 0 (Ident "u") unit'
  $ handling askEff askOp (Just { var: "r2", initial: 42 }) (ReadCell 0 cellKey)
      (perform triggerEff goOp)

-- | `λu. handle ( let _ = perform Trigger.go () in perform Ask.ask () ) with
-- | { handles Ask ; cells [r2] ( n : Int ) ; fast ask u -> readCell n } @ ( 42 )`:
-- | after `Trigger.go`, asks its own region what `n` holds.
shadowWrite :: Expr P.Int
shadowWrite = Lam 0 (Ident "u") unit'
  $ handling askEff askOp (Just { var: "r2", initial: 42 }) (ReadCell 0 cellKey)
      (Let 0 (Ident "ignored") int (perform triggerEff goOp) (perform askEff askOp))

-- | `handle ( handle ( openEff [( Ask )] shadowAsk () ) with { handles Trigger ;
-- | fast go u -> perform Ask.ask () } ) with { handles Ask ; fast ask u -> 1 }`.
-- |
-- | The `Trigger` clause stands at `( Ask )`, what its handler leaves, so its
-- | `perform Ask.ask` reaches the `Ask` handler outside: 1.
askedOutside :: Expr P.Int
askedOutside =
  handling askEff askOp Nothing (int' 1)
    $ handling triggerEff goOp Nothing (perform askEff askOp)
    $ callWidened askRow "shadowAsk"

-- | `handle ( shadowCell () ) with { handles Trigger ; cells [r] ( n : Int ) ;
-- | fast go u -> readCell n } @ ( 7 )`: the clause reads its own region, 7.
readOutside :: Expr P.Int
readOutside =
  handling triggerEff goOp (Just { var: "r", initial: 7 }) (ReadCell 0 cellKey)
    (call "shadowCell")

-- | `handle ( let a = shadowWrite () in let b = perform Trigger.go () in a + b ) with
-- | { handles Trigger ; cells [r] ( n : Int ) ;
-- |   fast go u -> let old = readCell n in let _ = writeCell n 5 in old } @ ( 7 )`.
-- |
-- | Inside `shadowWrite` the clause sets its own region's `n` to 5 and leaves the
-- | inner region's at 42, so the inner `ask` gives `a = 42`; the second `go`,
-- | outside, reads the 5 the first one wrote, so `b = 5`: 47. A write reaching the
-- | inner region instead gives `a = 5` and `b = 7`: 12.
writtenOutside :: Expr P.Int
writtenOutside =
  handling triggerEff goOp (Just { var: "r", initial: 7 }) swap
    $ Let 0 (Ident "a") int (call "shadowWrite")
    $ Let 0 (Ident "b") int (perform triggerEff goOp)
    $ added triggerRow (var "a") (var "b")
  where
  swap =
    Let 0 (Ident "old") int (ReadCell 0 cellKey)
      $ Let 0 (Ident "w") unit' (WriteCell 0 cellKey (int' 5))
      $ var "old"

-- | `handle ( shadowCell () ) with { handles Trigger ;
-- |   fast go u -> handle ( perform Ask.ask () ) with
-- |     { handles Ask ; cells [r3] ( n : Int ) ; fast ask u -> readCell n } @ ( 9 ) }`.
-- |
-- | What the body installs stands above its boundary and is found as usual: the
-- | `Ask` it performs reaches the handler it installed, whose own `fast` clause
-- | reads that handler's region, 9 — past the `Ask` handler and the region that
-- | `shadowCell` put inside `Ev_k`.
installedByBody :: Expr P.Int
installedByBody =
  handling triggerEff goOp Nothing
    ( handling askEff askOp (Just { var: "r3", initial: 9 }) (ReadCell 0 cellKey)
        (perform askEff askOp)
    )
    (call "shadowCell")

-- | `handle ( handle ( openEff [( Fork )] shadowCell () ) with
-- |   { handles Trigger ; cells [r] ( n : Int ) ;
-- |     fast go u -> let f = perform Fork.fork () in f + readCell n } @ ( 7 ) )
-- | with { handles Fork ; full fork u k -> k 1 + k 2 }`.
-- |
-- | The `fork` is answered by a `full` clause below the `Trigger` handler, so its
-- | continuation carries the `Trigger` clause's boundary, the `Trigger` handler,
-- | and everything `shadowCell` installed, and re-pushes them twice. Each
-- | resumption continues the `Trigger` clause, which reads its own region: 1 + 7
-- | and 2 + 7, so 17. Reading the region inside instead gives 43 + 44, so 87.
forkedTwice :: Expr P.Int
forkedTwice =
  Handle 0 triggered
    { element: RowEffectEntry forkEff []
    , cells: Nothing
    , returnClause: identityReturn
    , opClauses:
        [ FullClause
            { op: forkOp
            , tyBinders: []
            , argBinder: { name: Ident "u", ty: unit' }
            , contBinder: { name: Ident "k", ty: fn int TRowEmpty int }
            , body:
                added TRowEmpty
                  (App 0 (var "k") (int' 1))
                  (App 0 (var "k") (int' 2))
            }
        ]
    }
    []
  where
  triggered =
    handling triggerEff goOp (Just { var: "r", initial: 7 }) forkThenRead
      (callWidened forkRow "shadowCell")
  forkThenRead =
    Let 0 (Ident "f") int (perform forkEff forkOp)
      $ added (clauseRowOver "r" forkRow) (var "f") (ReadCell 0 cellKey)

-- Compiling and loading ------------------------------------------------------------------

-- | The two modules checked, lowered, and carried through the container.
-- | Checking is what shows each scenario is a well-typed program rather than one
-- | only a hand-built `.dmo` could hold.
compiled :: Either P.String (P.Array Dmo)
compiled = case declareAnnotated primSignature intModule of
  Left err -> Left ("Base.Int did not declare: " <> show err)
  Right intDeclared -> do
    intDmo <- through intModule intDeclared
    case declareAnnotated intDeclared.signature mainModule of
      Left err -> Left ("Main did not declare: " <> show err)
      Right mainDeclared -> do
        mainDmo <- through mainModule mainDeclared
        pure [ intDmo, mainDmo ]
  where
  through m declared = case translate noImports m declared of
    Left err -> Left (show err)
    Right mid -> case lower mid of
      Left err -> Left (show err)
      Right out -> case encode out.dmo of
        Left err -> Left (show err)
        Right bytes -> case decode bytes of
          Left err -> Left (show err)
          Right dmo -> Right dmo

fresh :: Effect Store
fresh = map (emptyStore emptyTable) (Ref.new noIdentities)

loading :: P.Array Dmo -> Aff (Either LoadError Store)
loading modules = liftEffect do
  store <- fresh
  runBaseEffect (Except.runExcept (Array.foldM load store modules))

held :: Maybe Value -> Maybe P.Int
held = case _ of
  Just (VInt n) -> Just n
  _ -> Nothing

heldBy :: P.String -> Aff (Maybe P.Int)
heldBy name = case compiled of
  Left err -> fail err *> pure Nothing
  Right dmos -> do
    outcome <- loading dmos
    case outcome of
      Left err -> fail (show err) *> pure Nothing
      Right store -> liftEffect case globalNamed store (inMain name) of
        Nothing -> pure Nothing
        Just slot -> map held (Ref.read slot)

spec :: Spec Unit
spec = describe "Steam, where a fast clause's body runs" do

  it "sends an operation the body performs past the handlers Ev_k installed" do
    value <- heldBy "askedOutside"
    value `shouldEqual` Just 1

  it "reads a cell of the handler's own region past the regions Ev_k opened" do
    value <- heldBy "readOutside"
    value `shouldEqual` Just 7

  it "writes a cell of the handler's own region and leaves the one Ev_k opened" do
    value <- heldBy "writtenOutside"
    value `shouldEqual` Just 47

  it "finds what the body installs itself, above its boundary" do
    value <- heldBy "installedByBody"
    value `shouldEqual` Just 9

  it "keeps the body outside Ev_k across a full operation resumed twice" do
    value <- heldBy "forkedTwice"
    value `shouldEqual` Just 17
