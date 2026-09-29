-- | The hand-written Core of the foreign fixtures, the host implementations each
-- | fixture's manifest points at, and what running each must give.
-- |
-- | A host implementation records every call it takes, and every action it returns
-- | as that action is performed, in a log its module exports as `events`. A runner
-- | imports the same module the program reached, so the log it reads is the
-- | sequence of effects the run had, in order.
-- |
-- | | Step of `io`'s `main` | What it exercises |
-- | | --- | --- |
-- | | `say "start"` | an action a foreign returns, performed where the chain reaches it |
-- | | `say (toString (tick ()))` | an argument evaluated before the function, a `unit` parameter the host sees as `undefined` |
-- | | `chain 20000 (pure 0)` | a left-nested chain of `bind` 20 000 deep, executed within a bounded host stack |
-- | | `readInt (parse "7")` … `readHandle ()` | an action of each kind, its result crossing by that kind |
-- | | `open 3`, `same` | an opaque value handed back to the host as the same object, whether it came from a call or an action |
-- | | `add 1`, then applied to 2 | a partial application of a foreign another module declares |
-- | | `twice 5` | a foreign the entry module declares itself |
-- | | `half`, `nextChar`, `shout`, `flip`, `note` | each value kind crossing in and out; an astral `char` both ways; a whole number owed as a `number` staying one; a `unit` result whatever the host returned |
module Test.Stella.Compiler.Fixtures.Foreigns
  ( Result(..)
  , Signature
  , HostForeign
  , ManifestModule
  , RunFault(..)
  , RunCase
  , ioName
  , hostName
  , ioModule
  , ioModulePureArity
  , ioModuleBindArity
  , ioHostModule
  , ioMainModule
  , ioManifest
  , ioHostSource
  , ioResult
  , ioEffects
  , pureMainModule
  , runCases
  , runHostModule
  , runMainModule
  , runManifest
  , runHostSource
  , runEffects
  , startMainModule
  , greetHostModule
  , greetMainModule
  , greetManifest
  , greetSource
  , addHostModule
  , addHostShrunk
  , addCallMain
  , addPartialMain
  , addShrunkManifest
  , addShrunkSource
  ) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String as String
import Data.Tuple (Tuple(..))
import Stella.Compiler.TypedCore (DecisionTree(..), Decl(..), Export(..), Expr(..), Ident(..), Kind(..), Literal(..), Module, ModuleName(..), Occurrence(..), Qualified(..), RowEntry(..), RowKey(..), Symbol(..), TyName(..), TyVar(..), Type(..), monoScheme, scalarString, scalarStringOf, scalarValue)
import Stella.Compiler.TypedCore.Prim (booleanTy, charTy, intTy, ioTy, numberTy, pureFn, recordTy, stringTy, unitCtor, unitTy)
import Test.Stella.Compiler.Fixtures.Programs (inInt, intName, mainName)
import Test.Stella.Compiler.Fixtures.Value (Expected(..), ExpectedKey(..))

-- The manifest's signatures ---------------------------------------------------------------

-- | How a foreign's result crosses: a value of a kind, or an action producing one.
data Result
  = Value P.String
  | Action P.String

-- | One foreign as a manifest entry describes it, the kinds spelled as the manifest
-- | spells them.
type Signature = { name :: P.String, params :: P.Array P.String, result :: Result }

-- | One entry of a foreign manifest.
type ManifestModule = { module :: ModuleName, specifier :: P.String, foreigns :: P.Array Signature }

-- | A foreign a fixture declares: its type, and the signature a manifest gives it.
type HostForeign = { name :: P.String, ty :: Type, params :: P.Array P.String, result :: Result }

signatureOf :: HostForeign -> Signature
signatureOf f = { name: f.name, params: f.params, result: f.result }

-- Names and types -------------------------------------------------------------------------

ioName :: ModuleName
ioName = ModuleName "Base.IO"

hostName :: ModuleName
hostName = ModuleName "Host"

inIO :: P.String -> Qualified Ident
inIO = Qualified ioName <<< Ident

inHost :: P.String -> Qualified Ident
inHost = Qualified hostName <<< Ident

inMain :: P.String -> Qualified Ident
inMain = Qualified mainName <<< Ident

int :: Type
int = TCon intTy []

number :: Type
number = TCon numberTy []

char :: Type
char = TCon charTy []

string :: Type
string = TCon stringTy []

bool :: Type
bool = TCon booleanTy []

unit' :: Type
unit' = TCon unitTy []

ioOf :: Type -> Type
ioOf t = TApp (TCon ioTy []) t

-- | `Host.Handle`, a type of no constructors: its values are the host's, crossing as
-- | `opaque`.
handle :: Type
handle = TCon (Qualified hostName (TyName "Handle")) []

recordOf :: P.Array (Tuple P.String Type) -> Type
recordOf fields =
  TApp (TCon recordTy [])
    (Array.foldr (\(Tuple k t) rest -> TRowExtend (RowTypeEntry (SymbolKey (Symbol k)) t) rest) TRowEmpty fields)

-- Terms ------------------------------------------------------------------------------------

var :: P.String -> Expr P.Int
var = Var 0 <<< Ident

global :: Qualified Ident -> Expr P.Int
global q = Global 0 q []

app :: Expr P.Int -> P.Array (Expr P.Int) -> Expr P.Int
app = Array.foldl (App 0)

lam :: P.String -> Type -> Expr P.Int -> Expr P.Int
lam name = Lam 0 (Ident name)

lit :: P.Int -> Expr P.Int
lit = Lit 0 <<< LitInt

num :: P.Number -> Expr P.Int
num = Lit 0 <<< LitNumber

text :: P.String -> Expr P.Int
text s = Lit 0 (LitString (fromMaybe (scalarStringOf []) (scalarString s)))

charLit :: P.Int -> Expr P.Int
charLit c = case scalarValue c of
  Just v -> Lit 0 (LitChar v)
  Nothing -> lit c

boolLit :: P.Boolean -> Expr P.Int
boolLit = Lit 0 <<< LitBoolean

unitValue :: Expr P.Int
unitValue = global unitCtor

intOp :: P.String -> Expr P.Int -> Expr P.Int -> Expr P.Int
intOp name a b = app (global (inInt name)) [ a, b ]

-- | `Base.IO.pure` at `t`.
pureAt :: Type -> Expr P.Int -> Expr P.Int
pureAt t x = app (TyApp 0 (global (inIO "pure")) t) [ x ]

-- | `Base.IO.bind` at `a` and `b`.
bindAt :: Type -> Type -> Expr P.Int -> Expr P.Int -> Expr P.Int
bindAt a b m k = app (TyApp 0 (TyApp 0 (global (inIO "bind")) a) b) [ m, k ]

-- | One step of a chain of actions: bind what an action produces, or a value.
data Step
  = Do P.String Type (Expr P.Int)
  | Be P.String Type (Expr P.Int)

-- | The steps in order and then `last`, an action producing `b`.
chainOf :: Type -> P.Array Step -> Expr P.Int -> Expr P.Int
chainOf b steps last = Array.foldr step last steps
  where
  step s rest = case s of
    Do x a m -> bindAt a b m (lam x a rest)
    Be x t e -> Let 0 (Ident x) t e rest

nonrec :: P.Int -> P.String -> Type -> Expr P.Int -> Decl P.Int
nonrec at name ty value = DeclNonRec at { name: Ident name, scheme: monoScheme ty, value, attributes: [] }

foreignDecl :: P.Int -> P.String -> Type -> Decl P.Int
foreignDecl at name ty = DeclForeign at { name: Ident name, scheme: monoScheme ty, attributes: [] }

-- Base.IO -----------------------------------------------------------------------------------

-- | `Base.IO`, whose two entries the runtime carries out itself.
ioModule :: Module P.Int
ioModule = ioModuleWith (pureFn tyA (ioOf tyA)) (pureFn (ioOf tyA) (pureFn (pureFn tyA (ioOf tyB)) (ioOf tyB)))

-- | `Base.IO` with `pure` declared at arity two, which no runtime carries out.
ioModulePureArity :: Module P.Int
ioModulePureArity = ioModuleWith (pureFn tyA (pureFn unit' (ioOf tyA))) (pureFn (ioOf tyA) (pureFn (pureFn tyA (ioOf tyB)) (ioOf tyB)))

-- | `Base.IO` with `bind` declared at arity three, which no runtime carries out.
ioModuleBindArity :: Module P.Int
ioModuleBindArity = ioModuleWith (pureFn tyA (ioOf tyA)) (pureFn (ioOf tyA) (pureFn (pureFn tyA (ioOf tyB)) (pureFn unit' (ioOf tyB))))

-- | `Base.IO` declaring `pure` and `bind` at these types, over `a` and `b`.
ioModuleWith :: Type -> Type -> Module P.Int
ioModuleWith pureTy bindTy =
  { annotation: 0
  , name: ioName
  , imports: []
  , exports: [ ExportValue (Ident "pure"), ExportValue (Ident "bind") ]
  , decls:
      [ foreignDecl 1 "pure" (TForall (TyVar "a") KType pureTy)
      , foreignDecl 2 "bind" (TForall (TyVar "a") KType (TForall (TyVar "b") KType bindTy))
      ]
  }

tyA :: Type
tyA = TVar (TyVar "a")

tyB :: Type
tyB = TVar (TyVar "b")

-- | A module declaring these foreigns, and the data types given, all exported.
hostModuleOf :: ModuleName -> P.Array P.String -> P.Array HostForeign -> Module P.Int
hostModuleOf name types foreigns =
  { annotation: 0
  , name
  , imports: []
  , exports: map (ExportType <<< TyName) types <> map (\f -> ExportValue (Ident f.name)) foreigns
  , decls:
      map dataDecl types
        <> Array.mapWithIndex (\i f -> foreignDecl (i + 1 + Array.length types) f.name f.ty) foreigns
  }
  where
  dataDecl t = DeclData 0
    { name: TyName t, kindVars: [], params: [], constructors: [], isNewtype: false, attributes: [] }

-- The io fixture ------------------------------------------------------------------------------

-- | `Host`'s foreigns in `io`.
ioForeigns :: P.Array HostForeign
ioForeigns =
  [ f "say" (pureFn string (ioOf unit')) [ "string" ] (Action "unit")
  , f "tick" (pureFn unit' int) [ "unit" ] (Value "int")
  , f "parse" (pureFn string int) [ "string" ] (Value "int")
  , f "add" (pureFn int (pureFn int int)) [ "int", "int" ] (Value "int")
  , f "half" (pureFn number number) [ "number" ] (Value "number")
  , f "nextChar" (pureFn char char) [ "char" ] (Value "char")
  , f "shout" (pureFn string string) [ "string" ] (Value "string")
  , f "flip" (pureFn bool bool) [ "boolean" ] (Value "boolean")
  , f "note" (pureFn int unit') [ "int" ] (Value "unit")
  , f "open" (pureFn int handle) [ "int" ] (Value "opaque")
  , f "same" (pureFn handle bool) [ "opaque" ] (Value "boolean")
  , f "readInt" (pureFn int (ioOf int)) [ "int" ] (Action "int")
  , f "readNumber" (pureFn unit' (ioOf number)) [ "unit" ] (Action "number")
  , f "readChar" (pureFn unit' (ioOf char)) [ "unit" ] (Action "char")
  , f "readString" (pureFn unit' (ioOf string)) [ "unit" ] (Action "string")
  , f "readBool" (pureFn unit' (ioOf bool)) [ "unit" ] (Action "boolean")
  , f "readHandle" (pureFn unit' (ioOf handle)) [ "unit" ] (Action "opaque")
  ]
  where
  f name ty params result = { name, ty, params, result }

-- | The foreign `Main` declares itself in `io`.
twiceForeign :: HostForeign
twiceForeign = { name: "twice", ty: pureFn int int, params: [ "int" ], result: Value "int" }

ioHostModule :: Module P.Int
ioHostModule = hostModuleOf hostName [ "Handle" ] ioForeigns

ioManifest :: P.Array ManifestModule
ioManifest =
  [ { module: hostName, specifier: "./host.mjs", foreigns: map signatureOf ioForeigns }
  , { module: mainName, specifier: "./host.mjs", foreigns: [ signatureOf twiceForeign ] }
  ]

ioHostSource :: P.String
ioHostSource =
  """import { refuse } from "@stella-lang/runtime/foreign";

const log = [];
let ticks = 0;
let opened;

export const events = () => log.slice();

export const say = (s) => () => {
  log.push(`say:${s}`);
};
export const tick = (u) => {
  ticks += 1;
  log.push(`tick:${typeof u}:${ticks}`);
  return ticks;
};
export const parse = (s) => {
  log.push(`parse:${s}`);
  return /^-?[0-9]+$/.test(s) ? Number(s) : refuse(`not a number: ${s}`);
};
export const add = (a, b) => {
  log.push(`add:${a}:${b}`);
  return a + b;
};
export const half = (x) => {
  log.push(`half:${typeof x}:${x}`);
  return x / 2;
};
export const nextChar = (c) => {
  log.push(`nextChar:${typeof c}:${c.length}:${c.codePointAt(0)}`);
  return String.fromCodePoint(c.codePointAt(0) + 1);
};
export const shout = (s) => {
  log.push(`shout:${s}`);
  return `${s}!`;
};
export const flip = (b) => {
  log.push(`flip:${typeof b}:${b}`);
  return !b;
};
export const note = (n) => {
  log.push(`note:${n}`);
  return 42;
};
export const open = (n) => {
  opened = { n };
  log.push(`open:${n}`);
  return opened;
};
export const same = (h) => {
  log.push(`same:${h === opened}`);
  return h === opened;
};
export const readInt = (n) => () => {
  log.push(`readInt:${n}`);
  return n * 10;
};
export const readNumber = (u) => () => {
  log.push(`readNumber:${typeof u}`);
  return 2;
};
export const readChar = (u) => () => {
  log.push(`readChar:${typeof u}`);
  return "\u{1F600}";
};
export const readString = (u) => () => {
  log.push(`readString:${typeof u}`);
  return "ok";
};
export const readBool = (u) => () => {
  log.push(`readBool:${typeof u}`);
  return true;
};
export const readHandle = (u) => () => {
  log.push(`readHandle:${typeof u}`);
  return opened;
};
export const twice = (n) => {
  log.push(`twice:${n}`);
  return 2 * n;
};
"""

-- | The fields of what `io`'s `main` produces, in the order it builds them.
ioFields :: P.Array { name :: P.String, ty :: Type, holds :: Expected }
ioFields =
  [ field "deep" int (EInt 20000)
  , field "read" int (EInt 70)
  -- the host returned 2, a whole number owed as a `number`
  , field "number" number (ENumber 2.0)
  , field "char" char (EChar 0x1F600)
  , field "string" string (EString "ok")
  , field "boolean" bool (EBoolean true)
  , field "added" int (EInt 3)
  , field "doubled" int (EInt 10)
  , field "halved" number (ENumber 2.0)
  , field "next" char (EChar 0x1F601)
  , field "shouted" string (EString ("a" <> smile <> "!"))
  , field "flipped" bool (EBoolean false)
  -- the host returned 42, and a `unit` result reads nothing of it
  , field "noted" unit' (EData "Prim.Unit" [])
  , field "sameGiven" bool (EBoolean true)
  , field "sameBack" bool (EBoolean true)
  ]
  where
  field name ty holds = { name, ty, holds }

smile :: P.String
smile = "\x1F600"

ioRecord :: Type
ioRecord = recordOf (map (\f -> Tuple f.name f.ty) ioFields)

ioMainModule :: Module P.Int
ioMainModule =
  { annotation: 0
  , name: mainName
  , imports: [ intName, ioName, hostName ]
  , exports: []
  , decls:
      [ foreignDecl 1 twiceForeign.name twiceForeign.ty
      , nonrec 2 "step" (pureFn int (ioOf int)) $ lam "x" int $ pureAt int (intOp "add" (var "x") (lit 1))
      , DeclRec 3
          [ { name: Ident "chain"
            , scheme: monoScheme (pureFn int (pureFn (ioOf int) (ioOf int)))
            , value: chainBody
            , attributes: []
            }
          ]
      , nonrec 4 "main" (ioOf ioRecord) mainBody
      ]
  }
  where
  host = global <<< inHost

  -- `λn acc. case (n) of 0 -> acc ; _ -> chain (n - 1) (bind acc step)`, each round
  -- nesting the chain built so far on the left
  chainBody = lam "n" int $ lam "acc" (ioOf int) $
    Case 0 [ var "n" ]
      ( SwitchLit (OccScrutinee 0)
          [ { lit: LitInt 0, tree: Leaf (var "acc") } ]
          ( Leaf
              ( app (global (inMain "chain"))
                  [ intOp "sub" (var "n") (lit 1), bindAt int int (var "acc") (global (inMain "step")) ]
              )
          )
      )

  mainBody = chainOf ioRecord
    [ Do "u0" unit' (app (host "say") [ text "start" ])
    , Do "u1" unit' (app (host "say") [ app (global (inInt "toString")) [ app (host "tick") [ unitValue ] ] ])
    , Do "deep" int (app (global (inMain "chain")) [ lit 20000, pureAt int (lit 0) ])
    , Do "read" int (app (host "readInt") [ app (host "parse") [ text "7" ] ])
    , Do "number" number (app (host "readNumber") [ unitValue ])
    , Do "char" char (app (host "readChar") [ unitValue ])
    , Do "string" string (app (host "readString") [ unitValue ])
    , Do "boolean" bool (app (host "readBool") [ unitValue ])
    , Be "given" handle (app (host "open") [ lit 3 ])
    , Do "back" handle (app (host "readHandle") [ unitValue ])
    , Be "partial" (pureFn int int) (app (host "add") [ lit 1 ])
    , Be "added" int (app (var "partial") [ lit 2 ])
    , Be "doubled" int (app (global (inMain "twice")) [ lit 5 ])
    , Be "halved" number (app (host "half") [ num 4.0 ])
    , Be "next" char (app (host "nextChar") [ charLit 0x1F600 ])
    , Be "shouted" string (app (host "shout") [ text ("a" <> smile) ])
    , Be "flipped" bool (app (host "flip") [ boolLit true ])
    , Be "noted" unit' (app (host "note") [ lit 1 ])
    , Be "sameGiven" bool (app (host "same") [ var "given" ])
    , Be "sameBack" bool (app (host "same") [ var "back" ])
    ]
    ( pureAt ioRecord
        (Array.foldr (\f rest -> RecordExtend 0 (SymbolKey (Symbol f.name)) (var f.name) rest) (RecordEmpty 0) ioFields)
    )

ioResult :: Expected
ioResult = ERecord (map (\f -> { key: KField f.name, value: f.holds }) ioFields)

-- | What the host saw, in order. Nothing is logged while `main` is initialized: the
-- | first call builds an action, and the log is written when that action runs.
ioEffects :: P.Array P.String
ioEffects =
  [ "say:start"
  , "tick:undefined:1"
  , "say:1"
  , "parse:7"
  , "readInt:7"
  , "readNumber:undefined"
  , "readChar:undefined"
  , "readString:undefined"
  , "readBool:undefined"
  , "open:3"
  , "readHandle:undefined"
  , "add:1:2"
  , "twice:5"
  , "half:number:4"
  -- an astral character is two UTF-16 code units in a host string
  , "nextChar:string:2:128512"
  , "shout:a" <> smile
  , "flip:boolean:true"
  , "note:1"
  , "same:true"
  , "same:true"
  ]

-- | `Main` whose `main` is `let later = bind (pure 7) in later pure`, touching no
-- | host: `Base.IO.bind` applied short of its arity and saturated afterwards, with
-- | `Base.IO.pure` handed over unapplied as the function it binds.
pureMainModule :: Module P.Int
pureMainModule =
  { annotation: 0
  , name: mainName
  , imports: [ ioName ]
  , exports: []
  , decls:
      [ nonrec 1 "main" (ioOf int)
          ( Let 0 (Ident "later") (pureFn (pureFn int (ioOf int)) (ioOf int))
              (app (TyApp 0 (TyApp 0 (global (inIO "bind")) int) int) [ pureAt int (lit 7) ])
              (app (var "later") [ TyApp 0 (global (inIO "pure")) int ])
          )
      ]
  }

-- Faults while running -------------------------------------------------------------------------

-- | How a run ends in a fault, with what both runtimes observe of it.
data RunFault
  -- | A foreign refused, as the foreign and the reason.
  = Refused P.String P.String
  -- | A foreign's host function threw, as the foreign and the message.
  | Threw P.String P.String
  -- | A foreign's result was not of its kind, as the foreign.
  | Breached P.String
  -- | An action refused, as the reason.
  | ActionRefused P.String
  -- | An action threw, as the message.
  | ActionThrew P.String
  -- | What an action produced was not of its kind, as the foreign that returned it.
  | ActionBreached P.String

-- | One way a run faults: `Host.culprit`, of this type and implementation, reached
-- | after `say "before"` has run.
type RunCase =
  { name :: P.String
  , description :: P.String
  , culprit :: HostForeign
  , produces :: Type
  , imports :: P.String
  , implementation :: P.String
  , fault :: RunFault
  }

runCases :: P.Array RunCase
runCases =
  [ value "run-refused" "a foreign refusing" "int" int refusing """(_u) => refuse("nothing to give")"""
      (Refused culprit "nothing to give")
  , value "run-threw" "a foreign's host function throwing an Error" "int" int ""
      """(_u) => {
  throw new Error("thrown by the host");
}"""
      (Threw culprit "thrown by the host")
  , value "run-threw-fault" "a foreign's host function throwing the runtime's own Fault" "int" int faultClass
      """(_u) => {
  throw new Fault("a fault the host made");
}"""
      (Threw culprit "a fault the host made")
  , value "run-threw-bug" "a foreign's host function throwing the runtime's own Bug" "int" int bugClass
      """(_u) => {
  throw new Bug("a bug the host made");
}"""
      (Threw culprit "a bug the host made")
  , value "run-breach-int-fraction" "a foreign owing an int returning 1.5" "int" int "" "(_u) => 1.5" (Breached culprit)
  , value "run-breach-int-wide" "a foreign owing an int returning 2 ** 31" "int" int "" "(_u) => 2 ** 31" (Breached culprit)
  , value "run-breach-int-string" "a foreign owing an int returning the string \"3\"" "int" int "" """(_u) => "3"""" (Breached culprit)
  , value "run-breach-number-string" "a foreign owing a number returning a string" "number" number "" """(_u) => "1.5"""" (Breached culprit)
  , value "run-breach-char-two" "a foreign owing a char returning two characters" "char" char "" """(_u) => "ab"""" (Breached culprit)
  , value "run-breach-char-surrogate" "a foreign owing a char returning a lone surrogate" "char" char "" """(_u) => "\uD800"""" (Breached culprit)
  , value "run-breach-string-surrogate" "a foreign owing a string returning one holding a lone surrogate" "string" string "" """(_u) => "a\uD800"""" (Breached culprit)
  , value "run-breach-boolean-number" "a foreign owing a boolean returning 0" "boolean" bool "" "(_u) => 0" (Breached culprit)
  , action "run-breach-action-not-callable" "a foreign owing an action returning 42" "" "(_u) => 42" (Breached culprit)
  , action "run-action-refused" "an action refusing" refusing """(_u) => () => refuse("nothing to give")"""
      (ActionRefused "nothing to give")
  , action "run-action-threw" "an action throwing an Error" ""
      """(_u) => () => {
  throw new Error("thrown by the action");
}"""
      (ActionThrew "thrown by the action")
  , action "run-action-threw-fault" "an action throwing the runtime's own Fault" faultClass
      """(_u) => () => {
  throw new Fault("a fault the action made");
}"""
      (ActionThrew "a fault the action made")
  , action "run-action-threw-bug" "an action throwing the runtime's own Bug" bugClass
      """(_u) => () => {
  throw new Bug("a bug the action made");
}"""
      (ActionThrew "a bug the action made")
  , action "run-action-breached" "an action owing an int producing the string \"3\"" "" """(_u) => () => "3"""" (ActionBreached culprit)
  ]
  where
  culprit = "Host.culprit"

  value name description kind ty imports implementation fault =
    { name
    , description
    , culprit: { name: "culprit", ty: pureFn unit' ty, params: [ "unit" ], result: Value kind }
    , produces: ty
    , imports
    , implementation
    , fault
    }

  action name description imports implementation fault =
    { name
    , description
    , culprit: { name: "culprit", ty: pureFn unit' (ioOf int), params: [ "unit" ], result: Action "int" }
    , produces: int
    , imports
    , implementation
    , fault
    }

  refusing = """import { refuse } from "@stella-lang/runtime/foreign";"""
  faultClass = """import { Fault } from "@stella-lang/runtime/backend";"""
  bugClass = """import { Bug } from "@stella-lang/runtime/backend";"""

sayForeign :: HostForeign
sayForeign = { name: "say", ty: pureFn string (ioOf unit'), params: [ "string" ], result: Action "unit" }

runHostModule :: RunCase -> Module P.Int
runHostModule c = hostModuleOf hostName [] [ sayForeign, c.culprit ]

runManifest :: RunCase -> P.Array ManifestModule
runManifest c = [ { module: hostName, specifier: "./host.mjs", foreigns: map signatureOf [ sayForeign, c.culprit ] } ]

-- | `main = bind (say "before") (λ_. culprit)`, where the culprit is the action
-- | `Host.culprit ()` returns, or `pure (Host.culprit ())`.
runMainModule :: RunCase -> Module P.Int
runMainModule c =
  { annotation: 0
  , name: mainName
  , imports: [ ioName, hostName ]
  , exports: []
  , decls: [ nonrec 1 "main" (ioOf c.produces) (bindAt unit' c.produces (app (global (inHost "say")) [ text "before" ]) (lam "u" unit' reached)) ]
  }
  where
  called = app (global (inHost "culprit")) [ unitValue ]
  reached = case c.culprit.result of
    Action _ -> called
    Value _ -> pureAt c.produces called

runHostSource :: RunCase -> P.String
runHostSource c =
  String.joinWith "\n"
    ( (if c.imports == "" then [] else [ c.imports, "" ])
        <>
          [ "const log = [];"
          , ""
          , "export const events = () => log.slice();"
          , ""
          , "export const say = (s) => () => {"
          , "  log.push(`say:${s}`);"
          , "};"
          , "export const culprit = " <> c.implementation <> ";"
          , ""
          ]
    )

runEffects :: P.Array P.String
runEffects = [ "say:before" ]

-- Failing to start -----------------------------------------------------------------------------

-- | `Main` with an action `main` and an `answer` that is not one.
startMainModule :: Module P.Int
startMainModule =
  { annotation: 0
  , name: mainName
  , imports: [ ioName ]
  , exports: []
  , decls:
      [ nonrec 1 "main" (ioOf unit') (pureAt unit' unitValue)
      , nonrec 2 "answer" int (lit 42)
      ]
  }

-- Refusals where the modules load --------------------------------------------------------------

greetForeign :: HostForeign
greetForeign = { name: "greet", ty: pureFn int int, params: [ "int" ], result: Value "int" }

-- | `module Host where foreign greet : Int -> Int`.
greetHostModule :: Module P.Int
greetHostModule = hostModuleOf hostName [] [ greetForeign ]

-- | `Main` calling `Host.greet 1` as its one global is initialized.
greetMainModule :: Module P.Int
greetMainModule =
  { annotation: 0
  , name: mainName
  , imports: [ hostName ]
  , exports: []
  , decls: [ nonrec 1 "greeted" int (app (global (inHost "greet")) [ lit 1 ]) ]
  }

-- | A manifest pointing `Host` at `specifier`, with the signatures given.
greetManifest :: P.String -> P.Array Signature -> P.Array ManifestModule
greetManifest specifier foreigns = [ { module: hostName, specifier, foreigns } ]

-- | An implementation module exporting these, each as it is written.
greetSource :: P.Array (Tuple P.String P.String) -> P.String
greetSource exports = String.joinWith "" (map (\(Tuple name value) -> "export const " <> name <> " = " <> value <> ";\n") exports)

-- | `module Host where foreign add : Int -> Int -> Int`.
addHostModule :: Module P.Int
addHostModule = hostModuleOf hostName [] [ { name: "add", ty: pureFn int (pureFn int int), params: [ "int", "int" ], result: Value "int" } ]

addShrunkForeign :: HostForeign
addShrunkForeign = { name: "add", ty: pureFn int int, params: [ "int" ], result: Value "int" }

-- | The same with `add` declared at arity **one**: a module compiled against the
-- | first calls it with a count its declaration does not admit.
addHostShrunk :: Module P.Int
addHostShrunk = hostModuleOf hostName [] [ addShrunkForeign ]

addShrunkManifest :: P.Array ManifestModule
addShrunkManifest = [ { module: hostName, specifier: "./host.mjs", foreigns: [ signatureOf addShrunkForeign ] } ]

addShrunkSource :: P.String
addShrunkSource = "export const add = (a) => a;\n"

-- | `Main` calling `Host.add 1 2`.
addCallMain :: Module P.Int
addCallMain = addMain (app (global (inHost "add")) [ lit 1, lit 2 ])

-- | `Main` applying `Host.add` to one argument, and the result to another.
addPartialMain :: Module P.Int
addPartialMain = addMain (Let 0 (Ident "p") (pureFn int int) (app (global (inHost "add")) [ lit 1 ]) (app (var "p") [ lit 2 ]))

addMain :: Expr P.Int -> Module P.Int
addMain value =
  { annotation: 0
  , name: mainName
  , imports: [ hostName ]
  , exports: []
  , decls: [ nonrec 1 "added" int value ]
  }
