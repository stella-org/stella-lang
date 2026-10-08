-- | The effect examples of the Examples document, written in Core by hand and
-- | run through declaration checking.
-- |
-- | Modules stand behind them, one per layer they draw on.
-- |
-- | | Module | Layer | What it holds |
-- | | --- | --- | --- |
-- | | `Prelude` | the default portable environment | `Partial` and `Maybe`, whose identities it owns |
-- | | `Effect.State` | a portable library | `State`, which needs nothing of the ABI |
-- | | `Base.Int`, `Base.IO` | ABI entries | arithmetic, and the common `IO` operations |
-- | | `Base.Effect.Console`, `Base.Effect.LiftIO` | ABI protocols | capabilities no backend implements |
-- | | `Js.Console` | a target namespace | the native leaf building an `IO` value on one target |
-- | | `Js.Effect.Console` | a target namespace | the adapter joining that leaf to the capability |
-- | | `Example` | ordinary code | the three values, and nothing else |
-- |
-- | `tick` puts an effect row on an arrow and performs two operations under a
-- | Lacks constraint. `toMaybe` handles `Partial` by abandoning its
-- | continuation, interpreting an effect into a pure type. `runConsoleIO` is a
-- | terminal interpreter, sequencing a native action before resuming, which is
-- | what obliges it to take a closed row. `lowerConsole` is an adapter, which
-- | translates one capability into another and so is written with a `fast`
-- | clause (D28).
-- |
-- | Each mutation below is one of them with one thing changed, and each must be
-- | rejected.
module Test.Stella.Compiler.TypedCore.EffectSlice
  ( spec
  , exampleModule
  ) where

import Prelude

import Prim as P

import Stella.Compiler.TypedCore (Constraint(..), Decl(..), EffName(..), Export(..), Expr(..), Handler, Ident(..), Kind(..), Literal(..), Module, ModuleName(..), OpClause(..), OpName(..), Qualified(..), RowElemKind(..), RowEntry(..), RowKey(..), TyName(..), TyVar(..), Type(..), TypeScheme, monoScheme)
import Stella.Compiler.TypedCore.Check (CheckError(..))
import Stella.Compiler.TypedCore.Declare (DeclError(..), DeclFailure, declare)
import Stella.Compiler.TypedCore.Prim (fn, intTy, ioTy, primSignature, pureFn, stringTy, unitCtor, unitTy)
import Stella.Compiler.TypedCore.Signature (Signature, lookupValue)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Test.Stella.Compiler.TypedCore.VerticalSlice (intModule)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

-- Names -----------------------------------------------------------------------

preludeModuleName :: ModuleName
preludeModuleName = ModuleName "Prelude"

stateModuleName :: ModuleName
stateModuleName = ModuleName "Effect.State"

baseIOModuleName :: ModuleName
baseIOModuleName = ModuleName "Base.IO"

baseIntModuleName :: ModuleName
baseIntModuleName = ModuleName "Base.Int"

baseConsoleModuleName :: ModuleName
baseConsoleModuleName = ModuleName "Base.Effect.Console"

jsConsoleModuleName :: ModuleName
jsConsoleModuleName = ModuleName "Js.Console"

baseLiftIOModuleName :: ModuleName
baseLiftIOModuleName = ModuleName "Base.Effect.LiftIO"

jsEffectConsoleModuleName :: ModuleName
jsEffectConsoleModuleName = ModuleName "Js.Effect.Console"

exampleModuleName :: ModuleName
exampleModuleName = ModuleName "Example"

partialEff :: Qualified EffName
partialEff = Qualified preludeModuleName (EffName "Partial")

stateEff :: Qualified EffName
stateEff = Qualified stateModuleName (EffName "State")

consoleEff :: Qualified EffName
consoleEff = Qualified baseConsoleModuleName (EffName "Console")

liftIOEff :: Qualified EffName
liftIOEff = Qualified baseLiftIOModuleName (EffName "LiftIO")

intAdd :: Qualified Ident
intAdd = Qualified baseIntModuleName (Ident "add")

ioPure :: Qualified Ident
ioPure = Qualified baseIOModuleName (Ident "pure")

ioBind :: Qualified Ident
ioBind = Qualified baseIOModuleName (Ident "bind")

jsConsoleLog :: Qualified Ident
jsConsoleLog = Qualified jsConsoleModuleName (Ident "log")

nothingCtor :: Qualified Ident
nothingCtor = Qualified preludeModuleName (Ident "Nothing")

justCtor :: Qualified Ident
justCtor = Qualified preludeModuleName (Ident "Just")

tickName :: Qualified Ident
tickName = Qualified exampleModuleName (Ident "tick")

toMaybeName :: Qualified Ident
toMaybeName = Qualified exampleModuleName (Ident "toMaybe")

runConsoleIOName :: Qualified Ident
runConsoleIOName = Qualified exampleModuleName (Ident "runConsoleIO")

lowerConsoleName :: Qualified Ident
lowerConsoleName = Qualified jsEffectConsoleModuleName (Ident "lowerConsole")

-- Types -----------------------------------------------------------------------

int :: Type
int = TCon intTy []

string :: Type
string = TCon stringTy []

unit' :: Type
unit' = TCon unitTy []

io :: Type -> Type
io ty = TApp (TCon ioTy []) ty

maybeOf :: Type -> Type
maybeOf ty = TApp (TCon (Qualified preludeModuleName (TyName "Maybe")) []) ty

-- | `e`, the residual effect row an effect-polymorphic signature leaves open.
rowVar :: Type
rowVar = TVar (TyVar "e")

tyVarA :: Type
tyVarA = TVar (TyVar "a")

tyVarB :: Type
tyVarB = TVar (TyVar "b")

-- | `( State Int | e )`
tickRow :: Type
tickRow = TRowExtend (RowEffectEntry stateEff [ int ]) rowVar

-- | `( Partial | e )`
partialRow :: Type
partialRow = TRowExtend (RowEffectEntry partialEff []) rowVar

-- | `( Console )`, closed: a terminal interpreter sequencing a native action
-- | before its continuation admits no residual row.
consoleRow :: Type
consoleRow = TRowExtend (RowEffectEntry consoleEff []) TRowEmpty

-- | `( LiftIO | e )`
liftIORow :: Type
liftIORow = TRowExtend (RowEffectEntry liftIOEff []) rowVar

-- The supporting modules --------------------------------------------------------

-- | `Prelude`, which owns the identity of the foundational types and of
-- | `Partial`. Elaboration emits `perform Partial.abort` for a non-exhaustive
-- | match, so the name is resolved through an ordinary import rather than by a
-- | privilege.
preludeModule :: Module P.Int
preludeModule =
  { annotation: 0
  , name: preludeModuleName
  , imports: []
  , exports:
      [ ExportEffect (EffName "Partial")
      , ExportType (TyName "Maybe")
      , ExportCtor (Ident "Nothing")
      , ExportCtor (Ident "Just")
      ]
  , decls:
      [ DeclEffect 1
          { name: EffName "Partial"
          , params: []
          , operations:
              [ { name: OpName "abort"
                , tyBinders: [ { name: TyVar "b", kind: KType } ]
                , argument: unit'
                , resumesWith: tyVarB
                }
              ]
          , attributes: []
          }
      , DeclData 2
          { name: TyName "Maybe"
          , kindVars: []
          , params: [ { name: TyVar "a", kind: KType } ]
          , constructors:
              [ { name: Ident "Nothing", tag: 0, fields: [] }
              , { name: Ident "Just", tag: 1, fields: [ tyVarA ] }
              ]
          , isNewtype: false
          , attributes: []
          }
      ]
  }

-- | `Effect.State`, an ordinary portable library declaring an effect. Nothing
-- | of the ABI is needed to write one.
stateModule :: Module P.Int
stateModule =
  { annotation: 0
  , name: stateModuleName
  , imports: []
  , exports: [ ExportEffect (EffName "State") ]
  , decls:
      [ DeclEffect 1
          { name: EffName "State"
          , params: [ { name: TyVar "s", kind: KType } ]
          , operations:
              [ { name: OpName "get", tyBinders: [], argument: unit', resumesWith: TVar (TyVar "s") }
              , { name: OpName "put", tyBinders: [], argument: TVar (TyVar "s"), resumesWith: unit' }
              ]
          , attributes: []
          }
      ]
  }

-- | `Base.IO`, the `core-runtime` profile of the ABI surface. The continuation
-- | of `bind` is a pure arrow: every arrow of a foreign type is (D23), and
-- | deferring it behind an unhandled effect would run that effect outside the
-- | dynamic context of the handler that installed it.
baseIOModule :: Module P.Int
baseIOModule =
  { annotation: 0
  , name: baseIOModuleName
  , imports: []
  , exports: [ ExportValue (Ident "pure"), ExportValue (Ident "bind") ]
  , decls:
      [ DeclForeign 1
          { name: Ident "pure"
          , scheme: monoScheme (TForall (TyVar "a") KType (pureFn tyVarA (io tyVarA)))
          , attributes: []
          }
      , DeclForeign 2
          { name: Ident "bind"
          , scheme: monoScheme
              ( TForall (TyVar "a") KType
                  ( TForall (TyVar "b") KType
                      (pureFn (io tyVarA) (pureFn (pureFn tyVarA (io tyVarB)) (io tyVarB)))
                  )
              )
          , attributes: []
          }
      ]
  }

-- | `Base.Effect.Console`, a protocol rather than an ABI entry. An effect
-- | declares operations without implementations, so a backend supplies nothing
-- | here and what interprets it is ordinary Stella code.
baseConsoleModule :: Module P.Int
baseConsoleModule =
  { annotation: 0
  , name: baseConsoleModuleName
  , imports: []
  , exports: [ ExportEffect (EffName "Console") ]
  , decls:
      [ DeclEffect 1
          { name: EffName "Console"
          , params: []
          , operations:
              [ { name: OpName "log", tyBinders: [], argument: string, resumesWith: unit' } ]
          , attributes: []
          }
      ]
  }

-- | `Js.Console`, the native leaf on one target. It constructs an `IO` value
-- | and performs nothing, which is what lets a handler stand between the
-- | capability and it.
jsConsoleModule :: Module P.Int
jsConsoleModule =
  { annotation: 0
  , name: jsConsoleModuleName
  , imports: []
  , exports: [ ExportValue (Ident "log") ]
  , decls:
      [ DeclForeign 1
          { name: Ident "log"
          , scheme: monoScheme (pureFn string (io unit'))
          , attributes: []
          }
      ]
  }

-- The adapter -------------------------------------------------------------------

-- | `effect LiftIO where liftIO : forall a. IO a ->* a`. Operation polymorphism
-- | lets one key serve every `a`; an effect parameter would need a key and a
-- | handler per type lifted.
baseLiftIOModule :: Module P.Int
baseLiftIOModule =
  { annotation: 0
  , name: baseLiftIOModuleName
  , imports: []
  , exports: [ ExportEffect (EffName "LiftIO") ]
  , decls:
      [ DeclEffect 1
          { name: EffName "LiftIO"
          , params: []
          , operations:
              [ { name: OpName "liftIO"
                , tyBinders: [ { name: TyVar "a", kind: KType } ]
                , argument: io tyVarA
                , resumesWith: tyVarA
                }
              ]
          , attributes: []
          }
      ]
  }

-- | `Js.Effect.Console`, where the `Console` capability meets one target. The
-- | adapter removes `Console` and performs `LiftIO` in its place, carrying the
-- | `IO` value the native leaf built. It executes nothing, so it stays
-- | effect-polymorphic where a terminal interpreter cannot.
jsEffectConsoleModule :: Module P.Int
jsEffectConsoleModule = jsEffectConsoleOf lowerConsoleClause

jsEffectConsoleOf :: OpClause P.Int -> Module P.Int
jsEffectConsoleOf = jsEffectConsoleWith adapterSourceRow

jsEffectConsoleWith :: Type -> OpClause P.Int -> Module P.Int
jsEffectConsoleWith source clause =
  { annotation: 0
  , name: jsEffectConsoleModuleName
  , imports: [ baseConsoleModuleName, baseLiftIOModuleName, jsConsoleModuleName ]
  , exports: [ ExportValue (Ident "lowerConsole") ]
  , decls:
      [ DeclNonRec 1
          { name: Ident "lowerConsole"
          , scheme: lowerConsoleSchemeOf source
          , value: lowerConsoleOf source clause
          , attributes: []
          }
      ]
  }

-- | `( Console | ( LiftIO | e ) )`, the row an adapter takes its computation at.
-- | The target stands beside the source so that a second adapter into the same
-- | target can follow this one; `( Console | e )` could not, `LiftIO ∉ e`
-- | failing where the row already carries it.
adapterSourceRow :: Type
adapterSourceRow = TRowExtend (RowEffectEntry consoleEff []) liftIORow

-- | `forall (e : Row Effect) (a : Type). Console ∉ e => LiftIO ∉ e =>`
-- | `( Unit -{ source }-> a ) -{ ( LiftIO | e ) }-> a`
lowerConsoleScheme :: TypeScheme
lowerConsoleScheme = lowerConsoleSchemeOf adapterSourceRow

lowerConsoleSchemeOf :: Type -> TypeScheme
lowerConsoleSchemeOf source = monoScheme
  ( TForall (TyVar "e") (KRow RowEffect)
      ( TForall (TyVar "a") KType
          ( TConstrained (Lacks (EffectKey consoleEff) rowVar)
              ( TConstrained (Lacks (EffectKey liftIOEff) rowVar)
                  (fn (fn unit' source tyVarA) liftIORow tyVarA)
              )
          )
      )
  )

-- | The thunk is applied as it arrives, the source row already carrying the
-- | target. One widening remains inside the clause, on the native leaf.
lowerConsoleOf :: Type -> OpClause P.Int -> Expr P.Int
lowerConsoleOf source clause =
  TyLam 0 (TyVar "e") (KRow RowEffect)
    $ TyLam 0 (TyVar "a") KType
    $ ConstraintLam 0 (Lacks (EffectKey consoleEff) rowVar)
    $ ConstraintLam 0 (Lacks (EffectKey liftIOEff) rowVar)
    $ Lam 0 (Ident "thunk") (fn unit' source tyVarA)
    $ Handle 0 (App 0 (Var 0 (Ident "thunk")) (Global 0 unitCtor []))
        { element: RowEffectEntry consoleEff []
        , returnClause: { binder: Ident "x", ty: tyVarA, body: Var 0 (Ident "x") }
        , opClauses: [ clause ]
        }

-- | The clause translates `log` into a `LiftIO` and gives control back, which
-- | is what a `fast` clause expresses: it binds no continuation, and its body
-- | has the type `log` resumes with, `Unit`.
lowerConsoleClause :: OpClause P.Int
lowerConsoleClause = lowerConsoleClauseOf (OpenEff 0 liftIORow (Global 0 jsConsoleLog []))

lowerConsoleClauseOf :: Expr P.Int -> OpClause P.Int
lowerConsoleClauseOf leaf =
  FastClause
    { op: OpName "log"
    , tyBinders: []
    , argBinder: { name: Ident "msg", ty: string }
    , body:
        Perform 0 (EffectKey liftIOEff) (OpName "liftIO") [ unit' ]
          (App 0 leaf (Var 0 (Ident "msg")))
    }

-- | The same clause with the widening dropped from the native leaf.
bareLeafClause :: OpClause P.Int
bareLeafClause = lowerConsoleClauseOf (Global 0 jsConsoleLog [])

-- | The same body in a `full` clause, which owes the answer type rather than
-- | the type `log` resumes with.
fullLogClause :: OpClause P.Int
fullLogClause =
  FullClause
    { op: OpName "log"
    , tyBinders: []
    , argBinder: { name: Ident "msg", ty: string }
    , contBinder: { name: Ident "k", ty: fn unit' liftIORow tyVarA }
    , body:
        Perform 0 (EffectKey liftIOEff) (OpName "liftIO") [ unit' ]
          (App 0 (OpenEff 0 liftIORow (Global 0 jsConsoleLog [])) (Var 0 (Ident "msg")))
    }

-- The example module ------------------------------------------------------------

exampleModule :: Module P.Int
exampleModule = exampleOf tickValue toMaybeValue closedConsole

-- | The interpreter varies in its scheme as well as its body, so it is passed
-- | as a binding rather than as a term.
type Interpreter =
  { scheme :: TypeScheme
  , value :: Expr P.Int
  }

closedConsole :: Interpreter
closedConsole = { scheme: runConsoleIOScheme, value: runConsoleIOValue }

-- | `Example` declares nothing of its own beyond the three values: `Maybe` and
-- | `Partial` belong to `Prelude`, `Console` to `Base.Effect.Console`, and the
-- | native leaf to `Js.Console`. What the header names is what it uses.
exampleOf :: Expr P.Int -> Expr P.Int -> Interpreter -> Module P.Int
exampleOf tick toMaybe runConsoleIO =
  { annotation: 0
  , name: exampleModuleName
  , imports:
      [ preludeModuleName
      , stateModuleName
      , baseIntModuleName
      , baseIOModuleName
      , baseConsoleModuleName
      , jsConsoleModuleName
      ]
  , exports:
      [ ExportValue (Ident "tick")
      , ExportValue (Ident "toMaybe")
      , ExportValue (Ident "runConsoleIO")
      ]
  , decls:
      [ DeclNonRec 1 { name: Ident "tick", scheme: tickScheme, value: tick, attributes: [] }
      , DeclNonRec 2 { name: Ident "toMaybe", scheme: toMaybeScheme, value: toMaybe, attributes: [] }
      , DeclNonRec 3
          { name: Ident "runConsoleIO"
          , scheme: runConsoleIO.scheme
          , value: runConsoleIO.value
          , attributes: []
          }
      ]
  }

-- tick --------------------------------------------------------------------------

-- | `forall (e : Row Effect). State ∉ e => Unit -{ ( State Int | e ) }-> Int`
tickScheme :: TypeScheme
tickScheme = monoScheme
  ( TForall (TyVar "e") (KRow RowEffect)
      ( TConstrained (Lacks (EffectKey stateEff) rowVar)
          (fn unit' tickRow int)
      )
  )

tickValue :: Expr P.Int
tickValue = tickOf widenedAdd

tickOf :: Expr P.Int -> Expr P.Int
tickOf addExpr =
  TyLam 0 (TyVar "e") (KRow RowEffect)
    $ ConstraintLam 0 (Lacks (EffectKey stateEff) rowVar)
    $ Lam 0 (Ident "u") unit'
    $ Let 0 (Ident "n") int
        (Perform 0 (EffectKey stateEff) (OpName "get") [] (Global 0 unitCtor []))
    $ Let 0 (Ident "w") unit'
        (Perform 0 (EffectKey stateEff) (OpName "put") [] addExpr)
    $ Var 0 (Ident "n")

-- | `Base.Int.add n 1`, with each arrow the application consumes widened to the
-- | ambient row first. Containment is never inserted (D8), so a pure function
-- | called where effects may occur carries an `openEff` per argument.
widenedAdd :: Expr P.Int
widenedAdd =
  App 0
    ( OpenEff 0 tickRow
        (App 0 (OpenEff 0 tickRow (Global 0 intAdd [])) (Var 0 (Ident "n")))
    )
    (Lit 0 (LitInt 1))

-- | The same application with the widening left out.
bareAdd :: Expr P.Int
bareAdd =
  App 0 (App 0 (Global 0 intAdd []) (Var 0 (Ident "n"))) (Lit 0 (LitInt 1))

-- toMaybe -----------------------------------------------------------------------

-- | `forall (e : Row Effect). Partial ∉ e => forall (a : Type).
-- |  ( Unit -{ ( Partial | e ) }-> a ) -{e}-> Maybe a`
toMaybeScheme :: TypeScheme
toMaybeScheme = monoScheme
  ( TForall (TyVar "e") (KRow RowEffect)
      ( TConstrained (Lacks (EffectKey partialEff) rowVar)
          ( TForall (TyVar "a") KType
              (fn (fn unit' partialRow tyVarA) rowVar (maybeOf tyVarA))
          )
      )
  )

toMaybeValue :: Expr P.Int
toMaybeValue = toMaybeOf [ abortClause rowVar ]

toMaybeOf :: P.Array (OpClause P.Int) -> Expr P.Int
toMaybeOf clauses =
  TyLam 0 (TyVar "e") (KRow RowEffect)
    $ ConstraintLam 0 (Lacks (EffectKey partialEff) rowVar)
    $ TyLam 0 (TyVar "a") KType
    $ Lam 0 (Ident "thunk") (fn unit' partialRow tyVarA)
    $ Handle 0 (App 0 (Var 0 (Ident "thunk")) (Global 0 unitCtor []))
        { element: RowEffectEntry partialEff []
        , returnClause:
            { binder: Ident "x"
            , ty: tyVarA
            -- `Just` has pure arrows, as every constructor does, so calling it
            -- at the row outside the handle widens it first.
            , body: App 0 (OpenEff 0 rowVar (TyApp 0 (Global 0 justCtor []) tyVarA)) (Var 0 (Ident "x"))
            }
        , opClauses: clauses
        }

-- | Abandoning the continuation is what realizes the abortion. `contRow` is the
-- | row the continuation carries: `ρ`, outside the handle, is what D15 calls for.
abortClause :: Type -> OpClause P.Int
abortClause contRow =
  FullClause
    { op: OpName "abort"
    , tyBinders: [ { name: TyVar "b", kind: KType } ]
    , argBinder: { name: Ident "arg", ty: unit' }
    , contBinder: { name: Ident "k", ty: fn tyVarB contRow (maybeOf tyVarA) }
    , body: TyApp 0 (Global 0 nothingCtor []) tyVarA
    }

-- runConsoleIO ------------------------------------------------------------------

-- | `forall (a : Type). ( Unit -{ ( Console ) }-> a ) -> IO a`
runConsoleIOScheme :: TypeScheme
runConsoleIOScheme = monoScheme
  (TForall (TyVar "a") KType (pureFn (fn unit' consoleRow tyVarA) (io tyVarA)))

runConsoleIOValue :: Expr P.Int
runConsoleIOValue =
  TyLam 0 (TyVar "a") KType
    $ Lam 0 (Ident "thunk") (fn unit' consoleRow tyVarA)
    $ Handle 0 (App 0 (Var 0 (Ident "thunk")) (Global 0 unitCtor [])) consoleHandler

-- | Every arrow here is pure, the row outside the handle being `()`, so nothing
-- | is widened and `Base.IO.bind` composes directly.
consoleHandler :: Handler P.Int
consoleHandler =
  { element: RowEffectEntry consoleEff []
  , returnClause:
      { binder: Ident "x"
      , ty: tyVarA
      , body: App 0 (TyApp 0 (Global 0 ioPure []) tyVarA) (Var 0 (Ident "x"))
      }
  , opClauses:
      [ FullClause
          { op: OpName "log"
          , tyBinders: []
          , argBinder: { name: Ident "s", ty: string }
          , contBinder: { name: Ident "k", ty: fn unit' TRowEmpty (io tyVarA) }
          , body:
              App 0
                ( App 0
                    (TyApp 0 (TyApp 0 (Global 0 ioBind []) unit') tyVarA)
                    (App 0 (Global 0 jsConsoleLog []) (Var 0 (Ident "s")))
                )
                (Lam 0 (Ident "w") unit' (App 0 (Var 0 (Ident "k")) (Global 0 unitCtor [])))
          }
      ]
  }

-- Running the checker -----------------------------------------------------------

-- | `Σ` the six supporting modules contribute, each checked against what
-- | precedes it.
checkedSignature :: Module P.Int -> Either (DeclFailure P.Int) Signature
checkedSignature m = do
  s6 <- supporting
  declare s6 m

supporting :: Either (DeclFailure P.Int) Signature
supporting = do
  s1 <- declare primSignature intModule
  s2 <- declare s1 preludeModule
  s3 <- declare s2 stateModule
  s4 <- declare s3 baseIOModule
  s5 <- declare s4 baseConsoleModule
  declare s5 jsConsoleModule

-- | `Σ` for the adapter, which needs `LiftIO` beside the six above.
checkedAdapter :: Module P.Int -> Either (DeclFailure P.Int) Signature
checkedAdapter m = do
  s6 <- supporting
  s7 <- declare s6 baseLiftIOModule
  declare s7 m

verdict :: Module P.Int -> Either DeclError Unit
verdict m = case checkedSignature m of
  Left failure -> Left failure.error
  Right _ -> Right unit

valueScheme :: Qualified Ident -> Maybe TypeScheme
valueScheme name = case checkedSignature exampleModule of
  Left _ -> Nothing
  Right sig -> map _.scheme (lookupValue sig name)

adapterVerdict :: Module P.Int -> Either DeclError Unit
adapterVerdict m = case checkedAdapter m of
  Left failure -> Left failure.error
  Right _ -> Right unit

adapterScheme :: Qualified Ident -> Maybe TypeScheme
adapterScheme name = case checkedAdapter jsEffectConsoleModule of
  Left _ -> Nothing
  Right sig -> map _.scheme (lookupValue sig name)

-- Mutations ---------------------------------------------------------------------

-- | `tick` with the widening left out of its arithmetic.
withBareAdd :: Module P.Int
withBareAdd = exampleOf (tickOf bareAdd) toMaybeValue closedConsole

-- | `toMaybe` whose continuation carries the row inside the handle. Handlers
-- | are deep (D15): resuming returns under the same handler, so the row is the
-- | one outside it.
withShallowContinuation :: Module P.Int
withShallowContinuation =
  exampleOf tickValue (toMaybeOf [ abortClause partialRow ]) closedConsole

-- | `toMaybe` with no clause for `abort`. A `handle` removes the keyed element,
-- | so an operation without a clause would have nowhere to go.
withoutAbortClause :: Module P.Int
withoutAbortClause = exampleOf tickValue (toMaybeOf []) closedConsole

-- | `runConsoleIO` left effect-polymorphic. Sequencing a native action before
-- | the continuation hands that continuation to `Base.IO.bind`, whose argument
-- | is a pure arrow, so the residual row has to be empty for it to fit.
withOpenResidualRow :: Module P.Int
withOpenResidualRow =
  exampleOf tickValue toMaybeValue { scheme: openConsoleScheme, value: openConsoleValue }

openConsoleScheme :: TypeScheme
openConsoleScheme = monoScheme
  ( TForall (TyVar "a") KType
      ( TForall (TyVar "e") (KRow RowEffect)
          ( TConstrained (Lacks (EffectKey consoleEff) rowVar)
              (fn (fn unit' openConsoleRow tyVarA) rowVar (io tyVarA))
          )
      )
  )

-- | `( Console | e )`
openConsoleRow :: Type
openConsoleRow = TRowExtend (RowEffectEntry consoleEff []) rowVar

-- | The same interpreter over that row, with every pure arrow it applies
-- | widened so that the continuation is the one thing left that does not fit.
openConsoleValue :: Expr P.Int
openConsoleValue =
  TyLam 0 (TyVar "a") KType
    $ TyLam 0 (TyVar "e") (KRow RowEffect)
    $ ConstraintLam 0 (Lacks (EffectKey consoleEff) rowVar)
    $ Lam 0 (Ident "thunk") (fn unit' openConsoleRow tyVarA)
    $ Handle 0 (App 0 (Var 0 (Ident "thunk")) (Global 0 unitCtor []))
        { element: RowEffectEntry consoleEff []
        , returnClause:
            { binder: Ident "x"
            , ty: tyVarA
            , body: App 0 (OpenEff 0 rowVar (TyApp 0 (Global 0 ioPure []) tyVarA)) (Var 0 (Ident "x"))
            }
        , opClauses:
            [ FullClause
                { op: OpName "log"
                , tyBinders: []
                , argBinder: { name: Ident "s", ty: string }
                , contBinder: { name: Ident "k", ty: fn unit' rowVar (io tyVarA) }
                , body:
                    App 0
                      ( OpenEff 0 rowVar
                          ( App 0
                              (OpenEff 0 rowVar (TyApp 0 (TyApp 0 (Global 0 ioBind []) unit') tyVarA))
                              (App 0 (OpenEff 0 rowVar (Global 0 jsConsoleLog [])) (Var 0 (Ident "s")))
                          )
                      )
                      (Lam 0 (Ident "w") unit' (App 0 (Var 0 (Ident "k")) (Global 0 unitCtor [])))
                }
            ]
        }

-- | `toMaybe` whose return clause applies `Just` without widening it. A data
-- | constructor has pure arrows by declaration, so calling one where the
-- | ambient row is not empty needs `openEff` exactly as a foreign does.
withBareJust :: Module P.Int
withBareJust = exampleOf tickValue bareJustToMaybe closedConsole

bareJustToMaybe :: Expr P.Int
bareJustToMaybe =
  TyLam 0 (TyVar "e") (KRow RowEffect)
    $ ConstraintLam 0 (Lacks (EffectKey partialEff) rowVar)
    $ TyLam 0 (TyVar "a") KType
    $ Lam 0 (Ident "thunk") (fn unit' partialRow tyVarA)
    $ Handle 0 (App 0 (Var 0 (Ident "thunk")) (Global 0 unitCtor []))
        { element: RowEffectEntry partialEff []
        , returnClause:
            { binder: Ident "x"
            , ty: tyVarA
            , body: App 0 (TyApp 0 (Global 0 justCtor []) tyVarA) (Var 0 (Ident "x"))
            }
        , opClauses: [ abortClause rowVar ]
        }

-- The specification ---------------------------------------------------------------

spec :: Spec Unit
spec = describe "Stella.Compiler.TypedCore.EffectSlice" do
  describe "the effect examples" do
    it "pass declaration checking across the seven modules" do
      verdict exampleModule `shouldEqual` Right unit

    it "record the effect row of each on its arrow" do
      valueScheme tickName `shouldEqual` Just tickScheme
      valueScheme toMaybeName `shouldEqual` Just toMaybeScheme

    it "leave the terminal interpreter pure, its effects having been removed" do
      valueScheme runConsoleIOName `shouldEqual` Just runConsoleIOScheme

  describe "mutations of them" do
    it "refuses a pure function applied at an effectful row without openEff" do
      verdict withBareAdd `shouldEqual` Left (IllTyped (RowMismatch tickRow TRowEmpty))

    it "refuses a continuation carrying the row inside the handle" do
      verdict withShallowContinuation `shouldEqual`
        Left
          ( IllTyped
              ( TypeMismatch (fn tyVarB rowVar (maybeOf tyVarA))
                  (fn tyVarB partialRow (maybeOf tyVarA))
              )
          )

    it "refuses a handler that omits an operation of the effect it removes" do
      verdict withoutAbortClause `shouldEqual`
        Left (IllTyped (MissingClause partialEff (OpName "abort")))

    it "refuses an interpreter that sequences a native action behind an open row" do
      verdict withOpenResidualRow `shouldEqual`
        Left (IllTyped (RowMismatch TRowEmpty rowVar))

    it "refuses a data constructor applied at an effectful row without openEff" do
      verdict withBareJust `shouldEqual`
        Left (IllTyped (RowMismatch rowVar TRowEmpty))

  describe "the adapter" do
    it "passes declaration checking, its clause being fast" do
      adapterVerdict jsEffectConsoleModule `shouldEqual` Right unit

    it "keeps the effect-polymorphic scheme, no native action being sequenced" do
      adapterScheme lowerConsoleName `shouldEqual` Just lowerConsoleScheme

    it "refuses a source row that does not carry the target" do
      -- the handle stands at `( LiftIO | e )` and removes `Console`, so its
      -- body is at `( Console, LiftIO | e )`; a thunk declared `( Console | e )`
      -- cannot be applied there, which is why the narrow shape does not compose
      adapterVerdict (jsEffectConsoleWith openConsoleRow lowerConsoleClause)
        `shouldEqual` Left (IllTyped (RowMismatch adapterSourceRow openConsoleRow))

    it "refuses the native leaf applied without openEff" do
      -- the clause is typed at `( LiftIO | e )` while `Js.Console.log` has pure
      -- arrows, so the widening is owed whichever form the clause takes
      adapterVerdict (jsEffectConsoleOf bareLeafClause)
        `shouldEqual` Left (IllTyped (RowMismatch liftIORow TRowEmpty))

    it "refuses the same body in a full clause, which owes the answer type" do
      -- a full clause supplies what the handle returns, so its body is `a`
      -- rather than the `Unit` that `log` resumes with
      adapterVerdict (jsEffectConsoleOf fullLogClause)
        `shouldEqual` Left (IllTyped (TypeMismatch tyVarA unit'))
