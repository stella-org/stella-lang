-- | Term typing.
-- |
-- | The cases the Implementation Plan singles out are here: an arrow's row
-- | against the ambient row, the value restriction, what a `perform` reads its
-- | signature from, which type a clause body is checked at given its form, and
-- | the local totality of a dispatch.
module Test.Stella.Compiler.TypedCore.Check (spec) where

import Prelude

import Prim as P

import Stella.Compiler.TypedCore (Cell, Decl(..), DecisionTree(..), EffName(..), Expr(..), Handler, Ident(..), JoinName(..), Kind(..), Literal(..), Module, ModuleName(..), OpClause(..), Occurrence(..), OpName(..), Qualified(..), RegionName(..), RowElemKind(..), RowEntry(..), RowKey(..), Symbol(..), TyName(..), TyVar(..), Type(..))
import Stella.Compiler.TypedCore.Check (CheckError(..), Env, check, envOf, infer, typeOf)
import Stella.Compiler.TypedCore.Kinding (KindError(..))
import Stella.Compiler.TypedCore.Context (assume, bindTyVar, bindVar, emptyContext)
import Stella.Compiler.TypedCore.Declare (declare)
import Stella.Compiler.TypedCore.Prim (fn, intTy, numberTy, primSignature, pureFn, stringTy, unitTy)
import Stella.Compiler.TypedCore.Domain (scalarString)
import Stella.Compiler.TypedCore.Signature (Signature)
import Stella.Compiler.TypedCore.Type (Constraint(..))
import Data.Either (Either(..), either)
import Data.Maybe (Maybe(..), fromMaybe)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

main :: ModuleName
main = ModuleName "Main"

value :: P.String -> Qualified Ident
value name = Qualified main (Ident name)

consoleEff :: Qualified EffName
consoleEff = Qualified main (EffName "Console")

stateEff :: Qualified EffName
stateEff = Qualified main (EffName "State")

maybeTy :: Qualified TyName
maybeTy = Qualified main (TyName "Maybe")

number :: Type
number = TCon numberTy []

-- | A NaN, which is the one value unequal to itself.
notANumber :: P.Number
notANumber = 0.0 / 0.0

int :: Type
int = TCon intTy []

string :: Type
string = TCon stringTy []

unitT :: Type
unitT = TCon unitTy []

maybeOf :: Type -> Type
maybeOf ty = TApp (TCon maybeTy []) ty

record :: Type -> Type
record row = TApp (TCon (Qualified (ModuleName "Prim") (TyName "Record")) []) row

variant :: Type -> Type
variant row = TApp (TCon (Qualified (ModuleName "Prim") (TyName "Variant")) []) row

-- | `( Console )`
consoleRow :: Type
consoleRow = TRowExtend (RowEffectEntry consoleEff []) TRowEmpty

-- | `( cache : State Int )`, one effect under a written key.
cacheRow :: Type
cacheRow = TRowExtend (RowLabelledEffectEntry (Symbol "cache") stateEff [ int ]) TRowEmpty

cacheKey :: RowKey
cacheKey = SymbolKey (Symbol "cache")

nameKey :: RowKey
nameKey = SymbolKey (Symbol "name")

sizeKey :: RowKey
sizeKey = SymbolKey (Symbol "size")

-- | The declarations these cases are checked against.
fixtures :: Module Unit
fixtures =
  { annotation: unit
  , name: main
  , imports: []
  , exports: []
  , decls:
      [ DeclEffect unit
          { name: EffName "Console"
          , params: []
          , operations: [ { name: OpName "log", tyBinders: [], argument: string, resumesWith: unitT } ]
          , attributes: []
          }
      , DeclEffect unit
          { name: EffName "State"
          , params: [ { name: TyVar "s", kind: KType } ]
          , operations:
              [ { name: OpName "get", tyBinders: [], argument: unitT, resumesWith: TVar (TyVar "s") }
              , { name: OpName "put", tyBinders: [], argument: TVar (TyVar "s"), resumesWith: unitT }
              ]
          , attributes: []
          }
      , DeclEffect unit
          { name: EffName "Fail"
          , params: []
          , operations:
              [ { name: OpName "abort"
                , tyBinders: [ { name: TyVar "a", kind: KType } ]
                , argument: unitT
                , resumesWith: TVar (TyVar "a")
                }
              ]
          , attributes: []
          }
      -- an effect whose one operation resumes with a value, so that a clause
      -- standing in a region has something to answer a `readCell` with
      , DeclEffect unit
          { name: EffName "Counter"
          , params: []
          , operations: [ { name: OpName "next", tyBinders: [], argument: unitT, resumesWith: int } ]
          , attributes: []
          }
      -- a second abort-shaped effect, so that one can be translated into the
      -- other by a clause that resumes at neither
      , DeclEffect unit
          { name: EffName "Fail2"
          , params: []
          , operations:
              [ { name: OpName "abort"
                , tyBinders: [ { name: TyVar "a", kind: KType } ]
                , argument: unitT
                , resumesWith: TVar (TyVar "a")
                }
              ]
          , attributes: []
          }
      , DeclData unit
          { name: TyName "Void"
          , kindVars: []
          , params: []
          , constructors: []
          , isNewtype: false
          , attributes: []
          }
      , DeclData unit
          { name: TyName "Wrap"
          , kindVars: []
          , params: []
          , constructors:
              [ { name: Ident "Absurd", tag: 0, fields: [ TCon (Qualified main (TyName "Void")) [] ] }
              , { name: Ident "Plain", tag: 1, fields: [] }
              ]
          , isNewtype: false
          , attributes: []
          }
      , DeclData unit
          { name: TyName "Maybe"
          , kindVars: []
          , params: [ { name: TyVar "a", kind: KType } ]
          , constructors:
              [ { name: Ident "Nothing", tag: 0, fields: [] }
              , { name: Ident "Just", tag: 1, fields: [ TVar (TyVar "a") ] }
              ]
          , isNewtype: false
          , attributes: []
          }
      ]
  }

sig :: Signature
sig = either (const primSignature) identity (declare primSignature fixtures)

env :: Env
env = envOf sig emptyContext

-- | `Γ` with `f : Int -> Int` and `x : Int`.
applied :: Env
applied = env
  { context = bindVar (bindVar emptyContext (Ident "f") (pureFn int int)) (Ident "x") int }

inferAt :: Type -> Expr Unit -> Either CheckError Type
inferAt rho expr = case infer env rho expr of
  Left failure -> Left failure.error
  Right checked -> Right (typeOf checked)

inferIn :: Env -> Type -> Expr Unit -> Either CheckError Type
inferIn e rho expr = case infer e rho expr of
  Left failure -> Left failure.error
  Right checked -> Right (typeOf checked)

checkAt :: Type -> Type -> Expr Unit -> Either CheckError Unit
checkAt rho expected expr = case check env rho expected expr of
  Left failure -> Left failure.error
  Right _ -> Right unit

lam :: P.String -> Type -> Expr Unit -> Expr Unit
lam name ty body = Lam unit (Ident name) ty body

var :: P.String -> Expr Unit
var name = Var unit (Ident name)

primUnit :: Expr Unit
primUnit = Global unit (Qualified (ModuleName "Prim") (Ident "Unit")) []

-- | A string literal. Every one these fixtures write is ordinary text, so the
-- | scalar check cannot fail; the empty string stands where it cannot arise.
strLit :: P.String -> Literal
strLit text = LitString (fromMaybe mempty (scalarString text))

oneLit :: Expr Unit
oneLit = Lit unit (LitInt 1)

emptyRecord :: Expr Unit
emptyRecord = RecordEmpty unit

failEff :: Qualified EffName
failEff = Qualified main (EffName "Fail")

fail2Eff :: Qualified EffName
fail2Eff = Qualified main (EffName "Fail2")

-- | `( Fail2 )`
fail2Row :: Type
fail2Row = TRowExtend (RowEffectEntry fail2Eff []) TRowEmpty

-- | `handle (perform Fail.abort [Int] ()) with { handles Fail ; … }`, with the
-- | binders and the continuation type of the clause supplied.
aborting :: P.Array { name :: TyVar, kind :: Kind } -> Type -> Expr Unit
aborting tyBinders contType =
  Handle unit (Perform unit (EffectKey failEff) (OpName "abort") [ int ] primUnit)
    { element: RowEffectEntry failEff []
    , returnClause: { binder: Ident "x", ty: int, body: oneLit }
    , opClauses:
        [ FullClause
            { op: OpName "abort"
            , tyBinders
            , argBinder: { name: Ident "u", ty: unitT }
            , contBinder: { name: Ident "k", ty: contType }
            , body: oneLit
            }
        ]
    }

-- | `{ handles Console ; return (x : α) -> e ; full log (s, k) -> 1 }`, with the
-- | return type, the return body, and the continuation type supplied.
consoleHandler :: Type -> Expr Unit -> Type -> Handler Unit
consoleHandler alpha returned contType =
  { element: RowEffectEntry consoleEff []
  , returnClause: { binder: Ident "x", ty: alpha, body: returned }
  , opClauses:
      [ FullClause
          { op: OpName "log"
          , tyBinders: []
          , argBinder: { name: Ident "s", ty: string }
          , contBinder: { name: Ident "k", ty: contType }
          , body: returned
          }
      ]
  }

-- | `handle (perform Console.log "x") with { handles Console ; return (x : Unit) -> 1 ; … }`,
-- | with the clause supplied. The handle stands at `Int`.
logging :: OpClause Unit -> Expr Unit
logging clause =
  Handle unit (Perform unit (EffectKey consoleEff) (OpName "log") [] (Lit unit (strLit "x")))
    { element: RowEffectEntry consoleEff []
    , returnClause: { binder: Ident "x", ty: unitT, body: oneLit }
    , opClauses: [ clause ]
    }

counterEff :: Qualified EffName
counterEff = Qualified main (EffName "Counter")

-- | `r` and `s`, the names of two regions.
regionName :: RegionName
regionName = RegionName "r"

otherRegion :: RegionName
otherRegion = RegionName "s"

-- | `( region r | ρ )`
regionRow :: Type -> Type
regionRow rest = TRowExtend (RowRegionEntry regionName) rest

nKey :: RowKey
nKey = SymbolKey (Symbol "n")

-- | `( n : Int )`, one cell holding an `Int`.
oneCell :: P.Array Cell
oneCell = [ { key: nKey, ty: int } ]

-- | `region [r] ( n : Int ) @ ( ē ) in handle (perform Counter.next ()) with
-- | { handles Counter ; … }`, with the initial values, the return clause's body,
-- | and the clause supplied. Both the handled computation and the answer are
-- | `Int`.
counting
  :: P.Array (Expr Unit)
  -> Expr Unit
  -> OpClause Unit
  -> Expr Unit
counting initial returned clause =
  Region unit regionName oneCell initial
    ( Handle unit (Perform unit (EffectKey counterEff) (OpName "next") [] primUnit)
        { element: RowEffectEntry counterEff []
        , returnClause: { binder: Ident "x", ty: int, body: returned }
        , opClauses: [ clause ]
        }
    )

-- | `fast next (_ : Unit) -> e`, whose body must have the type `next` resumes
-- | with, `Int`.
fastNext :: Expr Unit -> OpClause Unit
fastNext body =
  FastClause
    { op: OpName "next"
    , tyBinders: []
    , argBinder: { name: Ident "u", ty: unitT }
    , body
    }

-- | `fast log (msg : String) -> e`, with the body supplied. `log` resumes with
-- | `Unit`, so that is the type the body is checked at.
fastLog :: Expr Unit -> OpClause Unit
fastLog body =
  FastClause
    { op: OpName "log"
    , tyBinders: []
    , argBinder: { name: Ident "s", ty: string }
    , body
    }

-- | `full log (s : String, k : Unit -{()}-> Int) -> e`, over the same handler.
fullLog :: Expr Unit -> OpClause Unit
fullLog body =
  FullClause
    { op: OpName "log"
    , tyBinders: []
    , argBinder: { name: Ident "s", ty: string }
    , contBinder: { name: Ident "k", ty: pureFn unitT int }
    , body
    }

spec :: Spec Unit
spec = describe "TypedCore.Check" do
  it "declares the fixtures" do
    map (const unit) (declare primSignature fixtures) `shouldEqual` Right unit

  describe "basic rules" do
    it "gives a literal its type under any ambient row" do
      inferAt consoleRow oneLit `shouldEqual` Right int

    it "refuses a variable no binder introduced" do
      inferAt TRowEmpty (var "x") `shouldEqual` Left (UnboundVar (Ident "x"))

    it "reads a constructor's type from the declaration" do
      inferAt TRowEmpty (Global unit (value "Just") [])
        `shouldEqual` Right
          (TForall (TyVar "a") KType (pureFn (TVar (TyVar "a")) (maybeOf (TVar (TyVar "a")))))

    it "refuses a global instantiated at a number of kinds its scheme does not bind" do
      -- `Main.Just` binds none, so `[[Type]]` is an arity error
      inferAt TRowEmpty (Global unit (value "Just") [ KType ])
        `shouldEqual` Left (GlobalKindArgCount (value "Just") 0 1)

    it "synthesizes a lambda at the ambient row" do
      inferAt consoleRow (lam "n" int (var "n"))
        `shouldEqual` Right (fn int consoleRow int)

    it "checks one against the row its type writes" do
      checkAt consoleRow (pureFn int int) (lam "n" int (var "n"))
        `shouldEqual` Right unit

    it "requires an arrow's row to be the ambient row" do
      -- containment is never inserted, so a pure function is not applicable
      -- where effects may occur
      inferIn applied consoleRow (App unit (var "f") (var "x"))
        `shouldEqual` Left (RowMismatch consoleRow TRowEmpty)

    it "lets openEff widen it" do
      inferIn applied consoleRow
        (App unit (OpenEff unit consoleRow (var "f")) (var "x"))
        `shouldEqual` Right int

    it "substitutes at a type application" do
      inferAt TRowEmpty
        (TyApp unit (TyLam unit (TyVar "a") KType (lam "n" (TVar (TyVar "a")) (var "n"))) int)
        `shouldEqual` Right (pureFn int int)

    it "requires the body of a type abstraction to be a value form" do
      inferAt TRowEmpty
        (TyLam unit (TyVar "a") KType (App unit (lam "n" int (var "n")) oneLit))
        `shouldEqual` Left NotAValueForm

    it "re-derives a constraint at its elimination" do
      let constraint = Lacks nameKey TRowEmpty
      inferAt TRowEmpty
        (ConstraintApp unit (ConstraintLam unit constraint (lam "n" int (var "n"))))
        `shouldEqual` Right (pureFn int int)

    it "refuses a global the signature does not declare" do
      inferAt TRowEmpty (Global unit (value "ghost") [])
        `shouldEqual` Left (UndeclaredGlobal (value "ghost"))

    it "refuses an application of something that is not a function" do
      inferAt TRowEmpty (App unit oneLit oneLit) `shouldEqual` Left (NotAFunction int)

    it "refuses a type application of something that is not a forall" do
      inferAt TRowEmpty (TyApp unit oneLit int) `shouldEqual` Left (NotAForall int)

    it "refuses a constraint application of something that carries no constraint" do
      inferAt TRowEmpty (ConstraintApp unit oneLit) `shouldEqual` Left (NotConstrained int)

    it "refuses a selection from something that is not a record" do
      inferAt TRowEmpty (RecordSelect unit nameKey oneLit) `shouldEqual` Left (NotARecord int)

    it "refuses a weakening of something that is not a variant" do
      inferAt TRowEmpty (VariantWeaken unit nameKey int oneLit)
        `shouldEqual` Left (NotAVariant int)

    it "refuses a constraint abstraction checked against another constraint" do
      let
        assumed = Lacks nameKey TRowEmpty
        expected = Lacks cacheKey TRowEmpty
        abstraction = ConstraintLam unit assumed oneLit
      checkAt TRowEmpty (TConstrained expected int) abstraction
        `shouldEqual` Left (ConstraintMismatch expected assumed)

  describe "records" do
    it "selects what was extended" do
      inferAt TRowEmpty
        (RecordSelect unit nameKey (RecordExtend unit nameKey oneLit emptyRecord))
        `shouldEqual` Right int

    it "refuses a key the row already carries" do
      let inner = RecordExtend unit nameKey oneLit emptyRecord
      inferAt TRowEmpty (RecordExtend unit nameKey oneLit inner)
        `shouldEqual` Left (NotEntailed (Lacks nameKey (TRowExtend (RowTypeEntry nameKey int) TRowEmpty)))

    it "refuses a selection the row has no element for" do
      inferAt TRowEmpty (RecordSelect unit sizeKey emptyRecord)
        `shouldEqual` Left (NoElementAt sizeKey TRowEmpty)

    it "removes an element at a restriction" do
      inferAt TRowEmpty
        (RecordRestrict unit nameKey (RecordExtend unit nameKey oneLit emptyRecord))
        `shouldEqual` Right (record TRowEmpty)

    it "lets an update change the type of an element" do
      inferAt TRowEmpty
        ( RecordUpdate unit nameKey
            (RecordExtend unit nameKey oneLit emptyRecord)
            (Lit unit (strLit "s"))
        )
        `shouldEqual` Right (record (TRowExtend (RowTypeEntry nameKey string) TRowEmpty))

    it "requires the two sides of a merge to be disjoint" do
      let left = RecordExtend unit nameKey oneLit emptyRecord
      inferAt TRowEmpty (RecordMerge unit left left)
        `shouldEqual` Left
          ( NotEntailed
              ( Disjoint (TRowExtend (RowTypeEntry nameKey int) TRowEmpty)
                  (TRowExtend (RowTypeEntry nameKey int) TRowEmpty)
              )
          )

  describe "variants" do
    it "synthesizes the variant of the key alone" do
      inferAt TRowEmpty (VariantInject unit nameKey oneLit)
        `shouldEqual` Right (variant (TRowExtend (RowTypeEntry nameKey int) TRowEmpty))

    it "checks an injection against a wider variant" do
      let wide = variant (TRowExtend (RowTypeEntry nameKey int) (TRowExtend (RowTypeEntry sizeKey string) TRowEmpty))
      checkAt TRowEmpty wide (VariantInject unit nameKey oneLit) `shouldEqual` Right unit

    it "widens one with weaken" do
      inferAt TRowEmpty (VariantWeaken unit sizeKey string (VariantInject unit nameKey oneLit))
        `shouldEqual` Right
          ( variant
              (TRowExtend (RowTypeEntry sizeKey string) (TRowExtend (RowTypeEntry nameKey int) TRowEmpty))
          )

  describe "perform" do
    it "takes the element the key names" do
      inferAt consoleRow (Perform unit (EffectKey consoleEff) (OpName "log") [] (Lit unit (strLit "x")))
        `shouldEqual` Right unitT

    it "requires the ambient row to carry the key" do
      inferAt TRowEmpty (Perform unit (EffectKey consoleEff) (OpName "log") [] (Lit unit (strLit "x")))
        `shouldEqual` Left (NoElementAt (EffectKey consoleEff) TRowEmpty)

    it "reads the signature from the effect the payload names" do
      -- the key `cache` selects the element; `Σ(State)` with `s := Int` is what
      -- says the operation resumes with an `Int`
      inferAt cacheRow (Perform unit cacheKey (OpName "get") [] primUnit)
        `shouldEqual` Right int

    it "refuses an operation the effect does not declare" do
      inferAt consoleRow (Perform unit (EffectKey consoleEff) (OpName "shout") [] primUnit)
        `shouldEqual` Left (UnknownOperation consoleEff (OpName "shout"))

    it "refuses a number of type arguments the operation does not bind" do
      -- `Console.log` binds none, so supplying one is an arity error
      inferAt consoleRow
        (Perform unit (EffectKey consoleEff) (OpName "log") [ int ] (Lit unit (strLit "x")))
        `shouldEqual` Left (OperationTypeArgCount (OpName "log") 0 1)

  describe "handlers" do
    it "removes the element the handler writes" do
      -- effect safety is not "no operation is performed": the row outside the
      -- handle carries nothing
      inferAt TRowEmpty (logging (fullLog oneLit)) `shouldEqual` Right int

    it "requires a clause for every operation of the effect" do
      inferAt TRowEmpty
        ( Handle unit (Perform unit (EffectKey consoleEff) (OpName "log") [] (Lit unit (strLit "x")))
            { element: RowEffectEntry consoleEff []
            , returnClause: { binder: Ident "x", ty: unitT, body: oneLit }
            , opClauses: []
            }
        )
        `shouldEqual` Left (MissingClause consoleEff (OpName "log"))

    it "gives the continuation the row outside the handle and the result of it" do
      -- a shallow handler would resume at the inner row and the inner result
      inferAt TRowEmpty
        ( logging
            ( FullClause
                { op: OpName "log"
                , tyBinders: []
                , argBinder: { name: Ident "s", ty: string }
                , contBinder: { name: Ident "k", ty: pureFn unitT string }
                , body: oneLit
                }
            )
        )
        `shouldEqual` Left (TypeMismatch (pureFn unitT int) (pureFn unitT string))

    it "lets a performance at another key pass through" do
      -- `Ev_k` matches on the key, and `counter` is not `cache`
      let
        counterRow = TRowExtend (RowLabelledEffectEntry (Symbol "counter") stateEff [ int ]) TRowEmpty
        counterKey = SymbolKey (Symbol "counter")
      inferAt counterRow
        ( Handle unit (Perform unit counterKey (OpName "get") [] primUnit)
            { element: RowLabelledEffectEntry (Symbol "cache") stateEff [ int ]
            , returnClause: { binder: Ident "x", ty: int, body: oneLit }
            , opClauses:
                [ FullClause
                    { op: OpName "get"
                    , tyBinders: []
                    , argBinder: { name: Ident "u", ty: unitT }
                    , contBinder: { name: Ident "k", ty: fn int counterRow int }
                    , body: oneLit
                    }
                , FullClause
                    { op: OpName "put"
                    , tyBinders: []
                    , argBinder: { name: Ident "v", ty: int }
                    , contBinder: { name: Ident "k", ty: fn unitT counterRow int }
                    , body: oneLit
                    }
                ]
            }
        )
        `shouldEqual` Right int

  describe "clause forms" do
    it "checks a full clause's body at the answer type" do
      -- `β` is `Int` here, from the return clause; `Unit` is what `log` resumes
      -- with, and a full clause is not checked at that
      inferAt TRowEmpty (logging (fullLog primUnit))
        `shouldEqual` Left (TypeMismatch int unitT)

    it "checks a fast clause's body at the type the operation resumes with" do
      inferAt TRowEmpty (logging (fastLog primUnit)) `shouldEqual` Right int

    it "refuses a fast clause's body at the answer type instead" do
      inferAt TRowEmpty (logging (fastLog oneLit))
        `shouldEqual` Left (TypeMismatch unitT int)

    it "binds no continuation in a fast clause" do
      inferAt TRowEmpty (logging (fastLog (var "k")))
        `shouldEqual` Left (UnboundVar (Ident "k"))

    it "accepts a handler mixing the two forms" do
      -- the form is written per clause, so one effect's operations may differ
      inferAt TRowEmpty
        ( Handle unit (Perform unit cacheKey (OpName "get") [] primUnit)
            { element: RowLabelledEffectEntry (Symbol "cache") stateEff [ int ]
            , returnClause: { binder: Ident "x", ty: int, body: oneLit }
            , opClauses:
                [ FastClause
                    { op: OpName "get"
                    , tyBinders: []
                    , argBinder: { name: Ident "u", ty: unitT }
                    , body: oneLit
                    }
                , FullClause
                    { op: OpName "put"
                    , tyBinders: []
                    , argBinder: { name: Ident "v", ty: int }
                    , contBinder: { name: Ident "k", ty: pureFn unitT int }
                    , body: oneLit
                    }
                ]
            }
        )
        `shouldEqual` Right int

    it "accepts a fast clause translating a polymorphic resume type into another effect" do
      -- `abort : forall a. Unit ->* a` admits no pure terminating body, but
      -- performing an operation that resumes at `a` has that type. A fast
      -- clause is therefore available wherever a capability, not a pure type,
      -- is the target
      inferAt fail2Row
        ( Handle unit (Perform unit (EffectKey failEff) (OpName "abort") [ int ] primUnit)
            { element: RowEffectEntry failEff []
            , returnClause: { binder: Ident "x", ty: int, body: oneLit }
            , opClauses:
                [ FastClause
                    { op: OpName "abort"
                    , tyBinders: [ { name: TyVar "b", kind: KType } ]
                    , argBinder: { name: Ident "u", ty: unitT }
                    , body:
                        Perform unit (EffectKey fail2Eff) (OpName "abort")
                          [ TVar (TyVar "b") ]
                          primUnit
                    }
                ]
            }
        )
        `shouldEqual` Right int

  describe "regions of cells" do
    it "checks a fast clause against the cell the layout declares" do
      inferAt TRowEmpty
        (counting [ oneLit ] (var "x") (fastNext (ReadCell unit regionName nKey)))
        `shouldEqual` Right int

    it "gives a writeCell the Unit type rather than the cell's" do
      -- a write is done for its effect on the region and hands back nothing of
      -- its own; reading back what was set takes a readCell
      inferAt TRowEmpty
        ( counting [ oneLit ] (var "x")
            ( fastNext
                (Let unit (Ident "w") unitT (WriteCell unit regionName nKey oneLit) (ReadCell unit regionName nKey))
            )
        )
        `shouldEqual` Right int

    it "refuses a writeCell bound at the cell's type" do
      inferAt TRowEmpty
        ( counting [ oneLit ] (var "x")
            ( fastNext
                (Let unit (Ident "w") int (WriteCell unit regionName nKey oneLit) (ReadCell unit regionName nKey))
            )
        )
        `shouldEqual` Left (TypeMismatch int unitT)

    it "admits a readCell in the handled computation and in the return clause, the region standing around both" do
      -- the surface does not write either; Core admits both, a region and a
      -- handler being separate binders
      inferAt TRowEmpty
        ( Region unit regionName oneCell [ oneLit ]
            ( Handle unit (ReadCell unit regionName nKey)
                { element: RowEffectEntry counterEff []
                , returnClause: { binder: Ident "x", ty: int, body: ReadCell unit regionName nKey }
                , opClauses: [ fastNext oneLit ]
                }
            )
        )
        `shouldEqual` Right int

    it "refuses a readCell for a key the layout does not declare" do
      inferAt TRowEmpty
        (counting [ oneLit ] (var "x") (fastNext (ReadCell unit regionName sizeKey)))
        `shouldEqual` Left (NoCellAt regionName sizeKey)

    it "refuses a readCell outside the region" do
      inferAt TRowEmpty (ReadCell unit regionName nKey)
        `shouldEqual` Left (IllKindedType (UnboundRegion regionName))

    it "refuses a readCell where the region is in scope and not in the row" do
      -- the function is pure by its annotation, so its body stands at `()`
      inferAt TRowEmpty
        ( Region unit regionName oneCell [ oneLit ]
            (Let unit (Ident "f") (pureFn unitT int) (lam "u" unitT (ReadCell unit regionName nKey)) oneLit)
        )
        `shouldEqual` Left (RegionNotAmbient regionName TRowEmpty)

    it "refuses an initial value of the wrong type" do
      inferAt TRowEmpty
        (counting [ primUnit ] (var "x") (fastNext (ReadCell unit regionName nKey)))
        `shouldEqual` Left (TypeMismatch int unitT)

    it "refuses a layout and a list of initial values of different lengths" do
      inferAt TRowEmpty
        (counting [] (var "x") (fastNext (ReadCell unit regionName nKey)))
        `shouldEqual` Left (CellCount 1 0)

    it "refuses an initial value reaching a cell of its own region" do
      -- the initial values are evaluated before the region opens, outside its
      -- binder
      inferAt TRowEmpty
        (Region unit regionName oneCell [ ReadCell unit regionName nKey ] oneLit)
        `shouldEqual` Left (IllKindedType (UnboundRegion regionName))

    it "refuses a layout declaring one key twice" do
      -- kinding the layout is what rejects it: a row extension requires the key
      -- absent from the rest, which a repeat cannot discharge
      inferAt TRowEmpty
        ( Region unit regionName [ { key: nKey, ty: int }, { key: nKey, ty: int } ] [ oneLit, oneLit ]
            (ReadCell unit regionName nKey)
        )
        `shouldEqual` Left (IllKindedType (NotSharp nKey (TRowExtend (RowTypeEntry nKey int) TRowEmpty)))

    it "refuses a body whose type mentions the region" do
      -- the body is a closure carrying `( region r )` in its own arrow, so it
      -- mentions `r`, which is what `r ∉ frn(β)` rejects
      inferAt TRowEmpty
        (Region unit regionName oneCell [ oneLit ] (lam "u" unitT (ReadCell unit regionName nKey)))
        `shouldEqual` Left (RegionEscapes regionName)

    it "refuses a handler's answer closing over a cell of the region around it" do
      -- the return clause hands back a function over the cell, which the region's
      -- answer type then mentions
      inferAt TRowEmpty
        ( Region unit regionName oneCell [ oneLit ]
            ( Handle unit oneLit
                { element: RowEffectEntry counterEff []
                , returnClause: { binder: Ident "x", ty: int, body: lam "u" unitT (ReadCell unit regionName nKey) }
                , opClauses: [ fastNext oneLit ]
                }
            )
        )
        `shouldEqual` Left (RegionEscapes regionName)

    it "refuses a region whose residual row mentions it" do
      -- the row the region stands at holds `State (Unit -{ region r }-> Int)`,
      -- which is what `r ∉ frn(ρ)` rejects
      inferAt (TRowExtend (RowEffectEntry stateEff [ fn unitT (regionRow TRowEmpty) int ]) TRowEmpty)
        (Region unit regionName oneCell [ oneLit ] oneLit)
        `shouldEqual` Left (RegionEscapes regionName)

    it "accepts regions nested, an inner one reaching the outer's cells beside its own" do
      inferAt TRowEmpty
        ( Region unit regionName oneCell [ oneLit ]
            ( Region unit otherRegion oneCell [ oneLit ]
                (Let unit (Ident "a") int (ReadCell unit regionName nKey) (ReadCell unit otherRegion nKey))
            )
        )
        `shouldEqual` Right int

    it "refuses a region binder of a name already bound" do
      -- the checker's input follows the unique-binder convention
      inferAt TRowEmpty
        (Region unit regionName oneCell [ oneLit ] (Region unit regionName oneCell [ oneLit ] oneLit))
        `shouldEqual` Left (RegionBinderShadows regionName)

    it "checks the function a handler declaration with cells desugars to" do
      -- the scheme says nothing of regions: a row variable bound outside the
      -- region is known to lack its key, which is what lets the thunk be widened
      -- by it
      let
        e = TyVar "e"
        rowE = TVar e
        a = TyVar "a"
        tyA = TVar a
        thunkTy = fn unitT (TRowExtend (RowEffectEntry counterEff []) rowE) tyA
        -- the row everything inside the region stands at, which is what the
        -- widenings below name
        clauseRow = regionRow rowE
        -- `add` is pure and curried, so each stage that consumes an argument is
        -- widened to the clause's row: containment is written, never implied
        added =
          App unit
            (OpenEff unit clauseRow (App unit (OpenEff unit clauseRow (var "add")) (var "v")))
            oneLit
        body =
          Let unit (Ident "add") (pureFn int (pureFn int int))
            (lam "p" int (lam "q" int (var "p")))
            ( Let unit (Ident "v") int (ReadCell unit regionName nKey)
                (Let unit (Ident "w") unitT (WriteCell unit regionName nKey added) (var "v"))
            )
        term =
          TyLam unit e (KRow RowEffect)
            $ TyLam unit a KType
            $ ConstraintLam unit (Lacks (EffectKey counterEff) rowE)
            $ lam "thunk" thunkTy
            $ Region unit regionName oneCell [ oneLit ]
            $ Handle unit (App unit (OpenEff unit (regionRow TRowEmpty) (var "thunk")) primUnit)
                { element: RowEffectEntry counterEff []
                , returnClause: { binder: Ident "x", ty: tyA, body: var "x" }
                , opClauses: [ fastNext body ]
                }
        scheme =
          TForall e (KRow RowEffect)
            ( TForall a KType
                (TConstrained (Lacks (EffectKey counterEff) rowE) (fn thunkTy rowE tyA))
            )
      checkAt TRowEmpty scheme term `shouldEqual` Right unit

    it "accepts a region opened in a clause standing inside another region" do
      let
        inner =
          Region unit otherRegion oneCell [ oneLit ]
            ( Handle unit (Perform unit (EffectKey counterEff) (OpName "next") [] primUnit)
                { element: RowEffectEntry counterEff []
                , returnClause: { binder: Ident "y", ty: int, body: var "y" }
                , opClauses: [ fastNext (ReadCell unit otherRegion nKey) ]
                }
            )
        outer =
          Region unit regionName [ { key: sizeKey, ty: int } ] [ oneLit ]
            ( Handle unit (Perform unit (EffectKey consoleEff) (OpName "log") [] (Lit unit (strLit "x")))
                { element: RowEffectEntry consoleEff []
                , returnClause: { binder: Ident "x", ty: unitT, body: oneLit }
                , opClauses:
                    [ FastClause
                        { op: OpName "log"
                        , tyBinders: []
                        , argBinder: { name: Ident "m", ty: string }
                        , body: Let unit (Ident "c") int inner (Let unit (Ident "d") int (ReadCell unit regionName sizeKey) primUnit)
                        }
                    ]
                }
            )
      inferAt TRowEmpty outer `shouldEqual` Right int

    it "refuses a handler naming a region as the element it handles" do
      -- `handles` reads an effect application out of the payload, and a region
      -- carries none
      inferAt TRowEmpty
        ( Region unit regionName oneCell [ oneLit ]
            ( Let unit (Ident "f") (pureFn unitT int)
                ( lam "u" unitT
                    ( Handle unit oneLit
                        { element: RowRegionEntry regionName
                        , returnClause: { binder: Ident "x", ty: int, body: var "x" }
                        , opClauses: []
                        }
                    )
                )
                oneLit
            )
        )
        `shouldEqual` Left (WrongPayload (RegionKey regionName))

  describe "binders of types" do
    it "refuses a type abstraction binding a name already bound" do
      -- read as written, `Λ b. λ (x : b). x` checked at `forall a. a -> b` would
      -- identify its own `b` with the outer one
      let
        b = TyVar "b"
        withB = env { context = bindTyVar emptyContext b KType }
        expected = TForall (TyVar "a") KType (pureFn (TVar (TyVar "a")) (TVar b))
        term = TyLam unit b KType (lam "x" (TVar b) (var "x"))
      either (Left <<< _.error) (const (Right unit)) (check withB TRowEmpty expected term)
        `shouldEqual` Left (TypeBinderShadows b)
      inferIn withB TRowEmpty term `shouldEqual` Left (TypeBinderShadows b)

    it "refuses a clause's type binder of a name already bound" do
      let
        b = TyVar "b"
        withB = env { context = bindTyVar emptyContext b KType }
      inferIn withB TRowEmpty (aborting [ { name: b, kind: KType } ] (fn (TVar b) TRowEmpty int))
        `shouldEqual` Left (TypeBinderShadows b)

    it "keeps what is assumed of a row variable from a forall rebinding its name" do
      -- `x ∉ r` holds of the outer `r`; the `forall` binds another
      let
        r = TyVar "r"
        withFact =
          either (const env) (\context -> env { context = context })
            (assume (bindTyVar emptyContext r (KRow RowType)) (Lacks sizeKey (TVar r)))
        annotation =
          TForall r (KRow RowType)
            (pureFn (record (TVar r)) (record (TRowExtend (RowTypeEntry sizeKey int) (TVar r))))
      case inferIn withFact TRowEmpty (Let unit (Ident "f") annotation (var "f") oneLit) of
        Left (IllKindedType (NotSharp key _)) -> key `shouldEqual` sizeKey
        other -> show other `shouldEqual` "Left (IllKindedType (NotSharp …))"

  describe "handlers of one key" do
    it "refuses two of them nested directly" do
      -- the inner one would stand at `( Console | ( Console ) )`
      let
        inner = Handle unit (Perform unit (EffectKey consoleEff) (OpName "log") [] (Lit unit (strLit "x")))
          (consoleHandler unitT primUnit (pureFn unitT unitT))
      inferAt TRowEmpty (Handle unit inner (consoleHandler unitT primUnit (pureFn unitT unitT)))
        `shouldEqual` Left (IllKindedType (NotSharp (EffectKey consoleEff) consoleRow))

    it "accepts a pure function handling the effect within itself" do
      -- no row carries `Console` twice; the two handlers meet only in the
      -- run-time stack, which `openEff` is what lets them do
      let
        handled = Handle unit (Perform unit (EffectKey consoleEff) (OpName "log") [] (Lit unit (strLit "x")))
          (consoleHandler unitT primUnit (pureFn unitT unitT))
        f = lam "u" unitT handled
        call = App unit (OpenEff unit consoleRow (var "f")) primUnit
      inferAt TRowEmpty
        ( Let unit (Ident "f") (pureFn unitT unitT) f
            (Handle unit call (consoleHandler unitT oneLit (fn unitT TRowEmpty int)))
        )
        `shouldEqual` Right int

  describe "an operation's own polymorphism" do
    it "aligns a clause's binders with those the declaration writes" do
      -- the declaration binds `a` and the clause binds `b`; a handler must
      -- respect the polymorphism, not the spelling
      inferAt TRowEmpty (aborting [ { name: TyVar "b", kind: KType } ] (fn (TVar (TyVar "b")) TRowEmpty int))
        `shouldEqual` Right int

    it "refuses a clause binding none where the operation binds one" do
      inferAt TRowEmpty (aborting [] (fn int TRowEmpty int))
        `shouldEqual` Left (ClauseTypeBinders (OpName "abort"))

    it "refuses a clause binding one at another kind" do
      inferAt TRowEmpty
        (aborting [ { name: TyVar "b", kind: KRow RowType } ] (fn (TVar (TyVar "b")) TRowEmpty int))
        `shouldEqual` Left (ClauseTypeBinders (OpName "abort"))

  describe "polymorphism" do
    it "checks a type abstraction against the type it is given" do
      -- the body of the abstraction is checked against the arrow the expected
      -- type writes, row and all
      let expected = TForall (TyVar "a") KType (fn int consoleRow unitT)
      checkAt TRowEmpty expected
        ( TyLam unit (TyVar "b") KType
            (lam "n" int (Perform unit (EffectKey consoleEff) (OpName "log") [] (Lit unit (strLit "x"))))
        )
        `shouldEqual` Right unit

    it "refuses a binder introduced at another kind" do
      let expected = TForall (TyVar "a") KType (pureFn int int)
      checkAt TRowEmpty expected
        (TyLam unit (TyVar "b") (KRow RowType) (lam "n" int (var "n")))
        `shouldEqual` Left (BinderKindMismatch KType (KRow RowType))

  describe "join points" do
    it "types a jump from the definition of the join point it names" do
      inferAt TRowEmpty
        (LetJoin unit (JoinName "j") [ { name: Ident "n", ty: int } ] int (var "n") (Jump unit (JoinName "j") [ oneLit ]))
        `shouldEqual` Right int

    it "puts the root of a definition in tail position wherever the letjoin stands" do
      inferIn applied TRowEmpty
        ( App unit (var "f")
            ( LetJoin unit (JoinName "j") [ { name: Ident "n", ty: int } ] int
                (Jump unit (JoinName "j") [ var "n" ])
                oneLit
            )
        )
        `shouldEqual` Right int

    it "refuses a jump to a name no letjoin bound" do
      inferAt TRowEmpty (Jump unit (JoinName "j") [ oneLit ])
        `shouldEqual` Left (UnboundJoin (JoinName "j"))

    it "refuses a jump supplying the wrong number of arguments" do
      inferAt TRowEmpty
        ( LetJoin unit (JoinName "j") [ { name: Ident "n", ty: int } ] int (var "n")
            (Jump unit (JoinName "j") [ oneLit, oneLit ])
        )
        `shouldEqual` Left (JoinArity (JoinName "j") 1 2)

    it "refuses a jump outside tail position" do
      -- the argument of an application is not a tail position, and a jump is a
      -- transfer of control rather than something that returns a value
      inferIn applied TRowEmpty
        ( LetJoin unit (JoinName "j") [] int oneLit
            (App unit (var "f") (Jump unit (JoinName "j") []))
        )
        `shouldEqual` Left (JumpNotInTail (JoinName "j"))

    it "refuses a jump from under a lambda, the join context being discarded there" do
      -- a join point is a transfer within one function activation, so it does
      -- not cross a function boundary
      inferAt TRowEmpty
        ( LetJoin unit (JoinName "j") [] int oneLit
            (App unit (lam "u" unitT (Jump unit (JoinName "j") [])) primUnit)
        )
        `shouldEqual` Left (UnboundJoin (JoinName "j"))

  describe "recursive bindings" do
    it "refuses a right-hand side that is not a function value" do
      -- under strict evaluation `letrec x = x` has no meaning
      inferAt TRowEmpty
        (LetRec unit [ { name: Ident "x", ty: int, value: oneLit } ] (var "x"))
        `shouldEqual` Left (NotAFunctionValue (Ident "x"))

    it "accepts one that is" do
      inferAt TRowEmpty
        ( LetRec unit
            [ { name: Ident "loop", ty: pureFn int int, value: lam "n" int (var "n") } ]
            (var "loop")
        )
        `shouldEqual` Right (pureFn int int)

  describe "decision trees" do
    it "types the element of a record at a key" do
      -- a record carries one at every key of its row, so no branch establishes it
      let
        row = TRowExtend (RowTypeEntry nameKey int) TRowEmpty
        tree = Bind (Ident "y") (OccRecordField (OccScrutinee 0) nameKey) (Leaf (var "y"))
      inferIn (env { context = bindVar emptyContext (Ident "r") (record row) }) TRowEmpty
        (Case unit [ var "r" ] tree)
        `shouldEqual` Right int

    it "does not take the type of a dispatch from where a branch is written" do
      -- the first branch reaches no leaf, the second gives the type
      let
        tree = SwitchCtor (OccScrutinee 0)
          [ { ctor: value "Absurd"
            , tree: SwitchCtor (OccField (OccScrutinee 0) (value "Absurd") 0) [] Nothing
            }
          , { ctor: value "Plain", tree: Leaf oneLit }
          ]
          Nothing
      inferIn (env { context = bindVar emptyContext (Ident "w") (TCon (Qualified main (TyName "Wrap")) []) }) TRowEmpty
        (Case unit [ var "w" ] tree)
        `shouldEqual` Right int
    it "types the field of a constructor from the type of the occurrence" do
      let
        tree = SwitchCtor (OccScrutinee 0)
          [ { ctor: value "Nothing", tree: Leaf oneLit }
          , { ctor: value "Just"
            , tree: Bind (Ident "y") (OccField (OccScrutinee 0) (value "Just") 0) (Leaf (var "y"))
            }
          ]
          Nothing
      inferIn (env { context = bindVar emptyContext (Ident "m") (maybeOf int) }) TRowEmpty
        (Case unit [ var "m" ] tree)
        `shouldEqual` Right int

    it "refuses an occurrence no dispatch established" do
      -- what a constructor carries is known only under the dispatch that
      -- selected it, so the path reaches `Ω` through `switchCtor` and nowhere
      -- else
      let
        occurrence = OccField (OccScrutinee 0) (value "Just") 0
        tree = Bind (Ident "y") occurrence (Leaf (var "y"))
      inferIn (env { context = bindVar emptyContext (Ident "m") (maybeOf int) }) TRowEmpty
        (Case unit [ var "m" ] tree)
        `shouldEqual` Left (UnknownOccurrence occurrence)

    it "refuses a branch naming a constructor of another type" do
      let
        tree = SwitchCtor (OccScrutinee 0) [ { ctor: value "Plain", tree: Leaf oneLit } ] Nothing
      inferIn (env { context = bindVar emptyContext (Ident "m") (maybeOf int) }) TRowEmpty
        (Case unit [ var "m" ] tree)
        `shouldEqual` Left (NotAConstructorOf maybeTy (value "Plain"))

    it "refuses a dispatch naming one branch twice" do
      let
        branch = { ctor: value "Nothing", tree: Leaf oneLit }
        tree = SwitchCtor (OccScrutinee 0) [ branch, branch ] (Just (Leaf oneLit))
      inferIn (env { context = bindVar emptyContext (Ident "m") (maybeOf int) }) TRowEmpty
        (Case unit [ var "m" ] tree)
        `shouldEqual` Left DuplicateBranch

    it "accepts a literal dispatch that tells the two zeros apart" do
      -- literal identity is not IEEE equality: `0.0` and `-0.0` are different
      -- literals, so a dispatch may name both (D37)
      let
        tree = SwitchLit (OccScrutinee 0)
          [ { lit: LitNumber 0.0, tree: Leaf oneLit }
          , { lit: LitNumber (-0.0), tree: Leaf oneLit }
          ]
          (Leaf oneLit)
      inferIn (env { context = bindVar emptyContext (Ident "d") number }) TRowEmpty
        (Case unit [ var "d" ] tree)
        `shouldEqual` Right int

    it "refuses a literal dispatch naming one NaN twice" do
      -- every NaN is one literal, so two branches on one are two branches on one
      -- literal, which IEEE equality would have admitted
      let
        branch = { lit: LitNumber notANumber, tree: Leaf oneLit }
        tree = SwitchLit (OccScrutinee 0) [ branch, branch ] (Leaf oneLit)
      inferIn (env { context = bindVar emptyContext (Ident "d") number }) TRowEmpty
        (Case unit [ var "d" ] tree)
        `shouldEqual` Left DuplicateBranch

    it "refuses a literal dispatch over a type whose values are not literals" do
      let tree = SwitchLit (OccScrutinee 0) [] (Leaf oneLit)
      inferIn (env { context = bindVar emptyContext (Ident "m") (maybeOf int) }) TRowEmpty
        (Case unit [ var "m" ] tree)
        `shouldEqual` Left (NotALiteralType (maybeOf int))

    it "refuses a dispatch over an occurrence with no constructor at its head" do
      -- a scrutinee at a quantified type variable is the case: nothing says
      -- which constructors it has
      let tree = SwitchCtor (OccScrutinee 0) [] (Just (Leaf oneLit))
      inferIn (env { context = bindVar emptyContext (Ident "z") (TVar (TyVar "a")) }) TRowEmpty
        (Case unit [ var "z" ] tree)
        `shouldEqual` Left (UndispatchableOccurrence (OccScrutinee 0) (TVar (TyVar "a")))

    it "refuses a synthesized tree that reaches no leaf" do
      -- a type with no constructors exhausts vacuously, so the dispatch is
      -- locally total and has no leaf to take a type from. Checking the same
      -- tree against a type given from outside would succeed: this is a limit
      -- of synthesis rather than a rule of the system
      let tree = SwitchCtor (OccScrutinee 0) [] Nothing
      inferIn (env { context = bindVar emptyContext (Ident "v") (TCon (Qualified main (TyName "Void")) []) })
        TRowEmpty
        (Case unit [ var "v" ] tree)
        `shouldEqual` Left NoLeaf

    it "refuses a dispatch that is not locally total" do
      let
        tree = SwitchCtor (OccScrutinee 0) [ { ctor: value "Nothing", tree: Leaf oneLit } ] Nothing
      inferIn (env { context = bindVar emptyContext (Ident "m") (maybeOf int) }) TRowEmpty
        (Case unit [ var "m" ] tree)
        `shouldEqual` Left NotExhaustive

    it "refuses a constructor dispatch over an intrinsic type" do
      -- a type with no constructors would exhaust vacuously
      let tree = SwitchCtor (OccScrutinee 0) [] (Just (Leaf oneLit))
      inferIn (env { context = bindVar emptyContext (Ident "n") int }) TRowEmpty
        (Case unit [ var "n" ] tree)
        `shouldEqual` Left (NotADataType intTy)

    it "refines the occurrence in a default branch" do
      -- the default sees the residual variant, not the type the occurrence had
      let
        row = TRowExtend (RowTypeEntry nameKey int) (TRowExtend (RowTypeEntry sizeKey string) TRowEmpty)
        tree = SwitchKey (OccScrutinee 0)
          [ { key: nameKey, tree: Leaf (VariantInject unit nameKey oneLit) } ]
          (Just (Leaf (var "v")))
      inferIn (env { context = bindVar emptyContext (Ident "v") (variant row) }) TRowEmpty
        (Case unit [ var "v" ] tree)
        `shouldEqual` Left
          ( TypeMismatch (variant (TRowExtend (RowTypeEntry nameKey int) TRowEmpty))
              (variant row)
          )

    it "does not take the type of a guard from the branch written first" do
      -- the consequent reaches no leaf, and the alternative is what gives the
      -- type; a guard is no more ordered in this than a dispatch is
      let
        tree = SwitchCtor (OccScrutinee 0)
          [ { ctor: value "Absurd"
            , tree: Guard (Lit unit (LitBoolean true))
                (SwitchCtor (OccField (OccScrutinee 0) (value "Absurd") 0) [] Nothing)
                (Leaf oneLit)
            }
          , { ctor: value "Plain", tree: Leaf oneLit }
          ]
          Nothing
      inferIn (env { context = bindVar emptyContext (Ident "w") (TCon (Qualified main (TyName "Wrap")) []) }) TRowEmpty
        (Case unit [ var "w" ] tree)
        `shouldEqual` Right int

    it "requires a guard's condition to be a Boolean" do
      let tree = Guard oneLit (Leaf oneLit) (Leaf oneLit)
      inferIn (env { context = bindVar emptyContext (Ident "n") int }) TRowEmpty
        (Case unit [ var "n" ] tree)
        `shouldEqual` Left (TypeMismatch (TCon (Qualified (ModuleName "Prim") (TyName "Boolean")) []) int)
