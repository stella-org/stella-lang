-- | The foreign fixtures' manifests and the host implementations each points at,
-- | what running each must give, and the hand-written Core of the `Base.IO` the
-- | entry-arity refusals compile.
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
-- | | `chain n (pure 0)` | a left-nested chain of `bind` `n` deep, executed within a bounded host stack: 200 in `io`, and 20 000 in `io-deep`, the depth stack safety is tested at |
-- | | `readInt (parse "7")` … `readHandle ()` | an action of each kind, its result crossing by that kind |
-- | | `open 3`, `same` | an opaque value handed back to the host as the same object, whether it came from a call or an action |
-- | | `add 1`, then applied to 2 | a partial application of a foreign another module declares |
-- | | `twice 5` | a foreign the entry module declares itself |
-- | | `half`, `nextChar`, `shout`, `flip`, `note` | each value kind crossing in and out; an astral `char` both ways; a whole number owed as a `number` staying one; a `unit` result whatever the host returned |
module Test.E2E.Fixtures.Foreigns
  ( Result(..)
  , Signature
  , ManifestModule
  , RunFault(..)
  , RunCase
  , ioName
  , hostName
  , ioModulePureArity
  , ioModuleBindArity
  , ioManifest
  , ioHostSource
  , ioResult
  , deepIoResult
  , ioEffects
  , runCases
  , runManifest
  , runHostSource
  , runEffects
  , greetManifest
  , greetSource
  , addShrunkManifest
  , addShrunkSource
  ) where

import Prelude

import Prim as P

import Data.String as String
import Data.Tuple (Tuple(..))
import Stella.Compiler.TypedCore (Decl(..), Export(..), Ident(..), Kind(..), Module, ModuleName(..), TyVar(..), Type(..), monoScheme)
import Stella.Compiler.TypedCore.Prim (ioTy, pureFn, unitTy)
import Test.E2E.Fixtures.Programs (mainName)
import Test.E2E.Fixtures.Value (Expected(..), ExpectedKey(..))

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

-- Names ------------------------------------------------------------------------------------

ioName :: ModuleName
ioName = ModuleName "Base.IO"

hostName :: ModuleName
hostName = ModuleName "Host"

-- Base.IO -----------------------------------------------------------------------------------

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

unit' :: Type
unit' = TCon unitTy []

ioOf :: Type -> Type
ioOf t = TApp (TCon ioTy []) t

foreignDecl :: P.Int -> P.String -> Type -> Decl P.Int
foreignDecl at name ty = DeclForeign at { name: Ident name, scheme: monoScheme ty, attributes: [] }

-- The io fixture ------------------------------------------------------------------------------

-- | `Host`'s foreigns in `io`.
ioForeigns :: P.Array Signature
ioForeigns =
  [ f "say" [ "string" ] (Action "unit")
  , f "tick" [ "unit" ] (Value "int")
  , f "parse" [ "string" ] (Value "int")
  , f "add" [ "int", "int" ] (Value "int")
  , f "half" [ "number" ] (Value "number")
  , f "nextChar" [ "char" ] (Value "char")
  , f "shout" [ "string" ] (Value "string")
  , f "flip" [ "boolean" ] (Value "boolean")
  , f "note" [ "int" ] (Value "unit")
  , f "negZero" [ "unit" ] (Value "int")
  , f "open" [ "int" ] (Value "opaque")
  , f "same" [ "opaque" ] (Value "boolean")
  , f "readInt" [ "int" ] (Action "int")
  , f "readNumber" [ "unit" ] (Action "number")
  , f "readChar" [ "unit" ] (Action "char")
  , f "readString" [ "unit" ] (Action "string")
  , f "readBool" [ "unit" ] (Action "boolean")
  , f "readHandle" [ "unit" ] (Action "opaque")
  ]
  where
  f name params result = { name, params, result }

-- | The foreign `Main` declares itself in `io`.
twiceForeign :: Signature
twiceForeign = { name: "twice", params: [ "int" ], result: Value "int" }

ioManifest :: P.Array ManifestModule
ioManifest =
  [ { module: hostName, specifier: "./host.mjs", foreigns: ioForeigns }
  , { module: mainName, specifier: "./host.mjs", foreigns: [ twiceForeign ] }
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
export const negZero = (_u) => {
  log.push("negZero");
  return -0;
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

-- | The fields of what `io`'s `main` produces, in the order it builds them, at
-- | the depth its chain of `bind` goes.
ioFieldsAt :: P.Int -> P.Array { name :: P.String, holds :: Expected }
ioFieldsAt depth =
  [ field "deep" (EInt depth)
  , field "read" (EInt 70)
  -- the host returned 2, a whole number owed as a `number`
  , field "number" (ENumber 2.0)
  , field "char" (EChar 0x1F600)
  , field "string" (EString "ok")
  , field "boolean" (EBoolean true)
  , field "added" (EInt 3)
  , field "doubled" (EInt 10)
  , field "halved" (ENumber 2.0)
  , field "next" (EChar 0x1F601)
  , field "shouted" (EString ("a" <> smile <> "!"))
  , field "flipped" (EBoolean false)
  -- the host returned 42, and a `unit` result reads nothing of it
  , field "noted" (EData "Prim.Unit" [])
  -- the host returned -0, and an `Int` has one zero: `toNumber` of it is +0
  , field "zero" (ENumber 0.0)
  , field "sameGiven" (EBoolean true)
  , field "sameBack" (EBoolean true)
  ]
  where
  field name holds = { name, holds }

smile :: P.String
smile = "\x1F600"

-- | What `io`'s `main` produces, its chain 200 deep, and `io-deep`'s, 20 000
-- | deep.
ioResult :: Expected
ioResult = ioResultAt 200

deepIoResult :: Expected
deepIoResult = ioResultAt 20000

ioResultAt :: P.Int -> Expected
ioResultAt depth = ERecord (map (\f -> { key: KField f.name, value: f.holds }) (ioFieldsAt depth))

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
  , "negZero"
  , "same:true"
  , "same:true"
  ]

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

-- | One way a run faults: `Host.culprit`, of this signature and implementation,
-- | reached after `say "before"` has run.
type RunCase =
  { name :: P.String
  , description :: P.String
  , culprit :: Signature
  , imports :: P.String
  , implementation :: P.String
  , fault :: RunFault
  }

runCases :: P.Array RunCase
runCases =
  [ value "run-refused" "a foreign refusing" "int" refusing """(_u) => refuse("nothing to give")"""
      (Refused culprit "nothing to give")
  , value "run-threw" "a foreign's host function throwing an Error" "int" ""
      """(_u) => {
  throw new Error("thrown by the host");
}"""
      (Threw culprit "thrown by the host")
  , value "run-threw-fault" "a foreign's host function throwing the runtime's own Fault" "int" faultClass
      """(_u) => {
  throw new Fault("a fault the host made");
}"""
      (Threw culprit "a fault the host made")
  , value "run-threw-bug" "a foreign's host function throwing the runtime's own Bug" "int" bugClass
      """(_u) => {
  throw new Bug("a bug the host made");
}"""
      (Threw culprit "a bug the host made")
  , value "run-breach-int-fraction" "a foreign owing an int returning 1.5" "int" "" "(_u) => 1.5" (Breached culprit)
  , value "run-breach-int-wide" "a foreign owing an int returning 2 ** 31" "int" "" "(_u) => 2 ** 31" (Breached culprit)
  , value "run-breach-int-string" "a foreign owing an int returning the string \"3\"" "int" "" """(_u) => "3"""" (Breached culprit)
  , value "run-breach-number-string" "a foreign owing a number returning a string" "number" "" """(_u) => "1.5"""" (Breached culprit)
  , value "run-breach-char-two" "a foreign owing a char returning two characters" "char" "" """(_u) => "ab"""" (Breached culprit)
  , value "run-breach-char-surrogate" "a foreign owing a char returning a lone surrogate" "char" "" """(_u) => "\uD800"""" (Breached culprit)
  , value "run-breach-string-surrogate" "a foreign owing a string returning one holding a lone surrogate" "string" "" """(_u) => "a\uD800"""" (Breached culprit)
  , value "run-breach-boolean-number" "a foreign owing a boolean returning 0" "boolean" "" "(_u) => 0" (Breached culprit)
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

  value name description kind imports implementation fault =
    { name
    , description
    , culprit: { name: "culprit", params: [ "unit" ], result: Value kind }
    , imports
    , implementation
    , fault
    }

  action name description imports implementation fault =
    { name
    , description
    , culprit: { name: "culprit", params: [ "unit" ], result: Action "int" }
    , imports
    , implementation
    , fault
    }

  refusing = """import { refuse } from "@stella-lang/runtime/foreign";"""
  faultClass = """import { Fault } from "@stella-lang/runtime/backend";"""
  bugClass = """import { Bug } from "@stella-lang/runtime/backend";"""

sayForeign :: Signature
sayForeign = { name: "say", params: [ "string" ], result: Action "unit" }

runManifest :: RunCase -> P.Array ManifestModule
runManifest c = [ { module: hostName, specifier: "./host.mjs", foreigns: [ sayForeign, c.culprit ] } ]

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

-- Refusals where the modules load --------------------------------------------------------------

-- | A manifest pointing `Host` at `specifier`, with the signatures given.
greetManifest :: P.String -> P.Array Signature -> P.Array ManifestModule
greetManifest specifier foreigns = [ { module: hostName, specifier, foreigns } ]

-- | An implementation module exporting these, each as it is written.
greetSource :: P.Array (Tuple P.String P.String) -> P.String
greetSource exports = String.joinWith "" (map (\(Tuple name value) -> "export const " <> name <> " = " <> value <> ";\n") exports)

-- | The manifest of `Host` with `add` declared at arity **one**: a module
-- | compiled against `add` of arity two calls it with a count its declaration
-- | does not admit.
addShrunkManifest :: P.Array ManifestModule
addShrunkManifest = [ { module: hostName, specifier: "./host.mjs", foreigns: [ { name: "add", params: [ "int" ], result: Value "int" } ] } ]

addShrunkSource :: P.String
addShrunkSource = "export const add = (a) => a;\n"
