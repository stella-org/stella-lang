-- | The modules, files, and foreign manifests the session and guest tests load,
-- | written to `steam/.test-dmo`: Core modules compiled here, and `Bug` and
-- | `BugInit`, states no compiler produces, written as `.dmo` directly.
module Test.Steam.Command
  ( writeModules
  , modulesCompiled
  , requiring
  , dir
  , pathOf
  , manifestPath
  , ioModule
  , stringModule
  , stringModuleName
  , outOfRange
  , bugModule
  ) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Node.FS.Perms as Perms
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Node.Buffer as Buffer
import Node.Encoding (Encoding(..))
import Node.FS.Aff as FS
import Node.Process as Process
import Stella.Compiler.Bytecode (Dmo, encode, lower)
import Stella.Compiler.Bytecode.Instr (ConstIx(..), ForeignIx(..), FuncIx(..), Instr(..), Reg(..), Tail(..))
import Stella.Compiler.Bytecode.Module (Constant(..), GlobalInit(..))
import Stella.Compiler.MiddleEnd.Rep (Rep(..))
import Stella.Compiler.Interface (noImports)
import Stella.Compiler.MiddleEnd (translate)
import Stella.Compiler.TypedCore (Decl(..), Export(..), Expr(..), Ident(..), Kind(..), Literal(..), Module, ModuleName(..), Qualified(..), TyVar(..), Type(..), declareAnnotated, monoScheme, primSignature)
import Partial.Unsafe (unsafeCrashWith)
import Stella.Compiler.TypedCore.Domain (ScalarString, scalarString)
import Stella.Compiler.TypedCore.Prim (charTy, intTy, ioTy, pureFn, stringTy, unitCtor, unitTy)
import Test.Spec (Spec, it)
import Test.Spec.Assertions (fail)

-- The Core modules -------------------------------------------------------------------

ioModuleName :: ModuleName
ioModuleName = ModuleName "Base.IO"

mainModuleName :: ModuleName
mainModuleName = ModuleName "Main"

unit' :: Type
unit' = TCon unitTy []

-- | `IO τ`.
ioOf :: Type -> Type
ioOf t = TApp (TCon ioTy []) t

-- | `module Base.IO where foreign pure`, the half of `core-runtime` a program of
-- | no effects needs.
ioModule :: Module P.Int
ioModule =
  { annotation: 0
  , name: ioModuleName
  , imports: []
  , exports: [ ExportValue (Ident "pure"), ExportValue (Ident "bind") ]
  , decls:
      [ DeclForeign 1
          { name: Ident "pure"
          , scheme: monoScheme
              (TForall (TyVar "a") KType (pureFn (TVar (TyVar "a")) (ioOf (TVar (TyVar "a")))))
          , attributes: []
          }
      , DeclForeign 2
          { name: Ident "bind"
          , scheme: monoScheme
              ( TForall (TyVar "a") KType
                  ( TForall (TyVar "b") KType
                      ( pureFn (ioOf (TVar (TyVar "a")))
                          ( pureFn (pureFn (TVar (TyVar "a")) (ioOf (TVar (TyVar "b"))))
                              (ioOf (TVar (TyVar "b")))
                          )
                      )
                  )
              )
          , attributes: []
          }
      ]
  }

-- | `Main`, whose `main` is an action that produces `Prim.Unit`, and whose `other`
-- | is not an action at all.
mainModule :: Module P.Int
mainModule =
  { annotation: 0
  , name: mainModuleName
  , imports: [ ioModuleName ]
  , exports: []
  , decls:
      [ DeclNonRec 1
          { name: Ident "main"
          , scheme: monoScheme (ioOf unit')
          , value: App 0 (pureAt unit') (Global 0 unitCtor [])
          , attributes: []
          }
      , DeclNonRec 2
          { name: Ident "second"
          , scheme: monoScheme (ioOf unit')
          , value: App 0 (pureAt unit') (Global 0 unitCtor [])
          , attributes: []
          }
      , DeclNonRec 3
          { name: Ident "notAnAction"
          , scheme: monoScheme unit'
          , value: Global 0 unitCtor []
          , attributes: []
          }
      -- an action that faults once it is executed, and not before: the fault is
      -- inside the function a `bind` holds, which the drive loop is what applies
      , DeclNonRec 4
          { name: Ident "faulting"
          , scheme: monoScheme (ioOf (TCon charTy []))
          , value:
              App 0
                ( App 0
                    (TyApp 0 (TyApp 0 (bindAt) unit') (TCon charTy []))
                    (App 0 (pureAt unit') (Global 0 unitCtor []))
                )
                ( Lam 0 (Ident "_") unit' TRowEmpty
                    (App 0 (pureAt (TCon charTy [])) outOfRange)
                )
          , attributes: []
          }
      ]
  }
  where
  pureAt t = TyApp 0 (Global 0 (Qualified ioModuleName (Ident "pure")) []) t

  bindAt = Global 0 (Qualified ioModuleName (Ident "bind")) []

stringModuleName :: ModuleName
stringModuleName = ModuleName "Base.String"

-- | `module Base.String where foreign codePointAt`, an entry that faults outside
-- | its range, which is how a program here reaches a fault at all.
stringModule :: Module P.Int
stringModule =
  { annotation: 0
  , name: stringModuleName
  , imports: []
  , exports: [ ExportValue (Ident "codePointAt") ]
  , decls:
      [ DeclForeign 1
          { name: Ident "codePointAt"
          , scheme: monoScheme
              (pureFn (TCon intTy []) (pureFn (TCon stringTy []) (TCon charTy [])))
          , attributes: []
          }
      ]
  }

-- | A module whose global faults as it is evaluated, so the module does not load
-- | and the program never starts.
badInitModule :: Module P.Int
badInitModule =
  { annotation: 0
  , name: ModuleName "BadInit"
  , imports: [ stringModuleName ]
  , exports: []
  , decls:
      [ DeclNonRec 1
          { name: Ident "boom"
          , scheme: monoScheme (TCon charTy [])
          , value: outOfRange
          , attributes: []
          }
      ]
  }

-- | `Base.String.codePointAt 5 ""`, which faults.
outOfRange :: Expr P.Int
outOfRange =
  App 0
    ( App 0 (Global 0 (Qualified stringModuleName (Ident "codePointAt")) [])
        (Lit 0 (LitInt 5))
    )
    (Lit 0 (LitString emptyText))

-- | The empty string, which every index is outside of.
emptyText :: ScalarString
emptyText = case scalarString "" of
  Just s -> s
  Nothing -> unsafeCrashWith "the empty string is a scalar string"

-- | A module that also declares a `main`, which nothing may pick up: the entry
-- | module is named, so this one is not a competitor.
otherModule :: Module P.Int
otherModule =
  { annotation: 0
  , name: ModuleName "Other"
  , imports: [ ioModuleName ]
  , exports: []
  , decls:
      [ DeclNonRec 1
          { name: Ident "main"
          , scheme: monoScheme (ioOf unit')
          , value: App 0
              (TyApp 0 (Global 0 (Qualified ioModuleName (Ident "pure")) []) unit')
              (Global 0 unitCtor [])
          , attributes: []
          }
      ]
  }

-- Compiling them ------------------------------------------------------------------------

-- | A module written directly as a `.dmo`, holding a state no compiler produces: a
-- | `bind` whose function hands back what is not an `IO`.
-- |
-- | **It has to be written this way.** The checker rejects the Core that would
-- | produce it, which is the point — the defect is above the program, and reaching
-- | it is what the third exit status is for. Loading accepts it because loading
-- | checks arities and not types.
bugModule :: Dmo
bugModule =
  { formatVersion: 0
  , abiVersion: "stella-base-0.1"
  , name: ModuleName "Bug"
  , imports: [ ioModuleName ]
  , constants: [ CInt 1 ]
  , keys: []
  , ops: []
  , ctors: []
  , effects: []
  , foreigns: []
  , ctorRefs: []
  , foreignRefs:
      [ Qualified ioModuleName (Ident "pure")
      , Qualified ioModuleName (Ident "bind")
      ]
  , globalRefs: []
  , callees: []
  , prims: []
  , handlers: []
  , regions: []
  , functions:
      [ { nparams: 0
        , regs: Array.replicate 4 RepVal
        , captures: []
        , joins: []
        , body:
            { code:
                [ LOADK (Reg 0) (ConstIx 0)
                , FFI (Reg 1) (ForeignIx 0) [ Reg 0 ]
                , CLOS (Reg 2) (FuncIx 1) []
                , FFI (Reg 3) (ForeignIx 1) [ Reg 1, Reg 2 ]
                ]
            , tail: RET (Reg 3)
            }
        }
      -- hands back its argument, which is an `Int`
      , { nparams: 1
        , regs: [ RepVal ]
        , captures: []
        , joins: []
        , body: { code: [], tail: RET (Reg 0) }
        }
      ]
  , globals: [ { name: Qualified (ModuleName "Bug") (Ident "main"), init: GRun (FuncIx 0) } ]
  , exports: []
  }

-- | The same state, reached while a module initializes rather than while the entry
-- | point runs.
-- |
-- | **This is the case that separates the two questions.** A fault here exits `1`,
-- | the program never having started; a bug here exits `3`, because what is asked
-- | first is whose the defect is and not when it happened. A wiring that wrapped
-- | every refusal alike would collapse the second into the first.
bugInitModule :: Dmo
bugInitModule = bugModule
  { name = ModuleName "BugInit"
  , functions =
      [ { nparams: 0
        , regs: Array.replicate 3 RepVal
        , captures: []
        , joins: []
        , body:
            { code:
                [ LOADK (Reg 0) (ConstIx 0)
                , CLOS (Reg 1) (FuncIx 1) []
                -- a `bind` whose first argument is an `Int`, which no `.dmo` a
                -- compiler produced would hold
                , FFI (Reg 2) (ForeignIx 1) [ Reg 0, Reg 1 ]
                ]
            , tail: RET (Reg 2)
            }
        }
      , { nparams: 1
        , regs: [ RepVal ]
        , captures: []
        , joins: []
        , body: { code: [], tail: RET (Reg 0) }
        }
      ]
  , globals =
      [ { name: Qualified (ModuleName "BugInit") (Ident "boom"), init: GRun (FuncIx 0) } ]
  }

type Fixture =
  { io :: Dmo
  , string :: Dmo
  , main :: Dmo
  , other :: Dmo
  , badInit :: Dmo
  , host :: Dmo
  , speaker :: Dmo
  }

compiled :: Either P.String Fixture
compiled = case declareAnnotated primSignature ioModule of
  Left err -> Left ("Base.IO did not declare: " <> show err.error)
  Right ioDeclared -> case declareAnnotated ioDeclared.signature stringModule of
    Left err -> Left ("Base.String did not declare: " <> show err.error)
    Right stringDeclared -> do
      io <- lowered =<< translated ioModule ioDeclared
      string <- lowered =<< translated stringModule stringDeclared
      case declareAnnotated stringDeclared.signature mainModule of
        Left err -> Left ("Main did not declare: " <> show err.error)
        Right mainDeclared -> do
          main <- lowered =<< translated mainModule mainDeclared
          case declareAnnotated stringDeclared.signature otherModule of
            Left err -> Left ("Other did not declare: " <> show err.error)
            Right otherDeclared -> do
              other <- lowered =<< translated otherModule otherDeclared
              case declareAnnotated stringDeclared.signature badInitModule of
                Left err -> Left ("BadInit did not declare: " <> show err.error)
                Right badDeclared -> do
                  badInit <- lowered =<< translated badInitModule badDeclared
                  case declareAnnotated primSignature hostModule of
                    Left err -> Left ("Host did not declare: " <> show err.error)
                    Right hostDeclared -> do
                      host <- lowered =<< translated hostModule hostDeclared
                      case declareAnnotated primSignature speakerModule of
                        Left err -> Left ("Speaker did not declare: " <> show err.error)
                        Right speakerDeclared -> do
                          speaker <- lowered =<< translated speakerModule speakerDeclared
                          pure { io, string, main, other, badInit, host, speaker }
  where
  translated m declared = case translate noImports m declared of
    Left err -> Left (show err)
    Right mid -> Right mid

  lowered mid = case lower mid of
    Left err -> Left (show err)
    Right out -> Right out.dmo

-- Running the command ----------------------------------------------------------------

-- | What one invocation left.
type Outcome =
  { status :: P.Int
  , err :: P.String
  }

-- | Where this suite's files stand. One directory, written once.
dir :: P.String
dir = "steam/.test-dmo"

-- | The path a module was written to.
pathOf :: P.String -> P.String
pathOf name = dir <> "/" <> name <> ".dmo"

-- | Whether the modules `writeModules` writes compile, and why not.
modulesCompiled :: Either P.String Unit
modulesCompiled = map (const unit) compiled

-- | The cases given where the fixture they read compiles, and otherwise one
-- | case failing with why: no case is left to read a file the fixture did not
-- | write, or one an earlier run left.
requiring :: forall a. Either P.String a -> (a -> Spec Unit) -> Spec Unit
requiring fixture cases = case fixture of
  Left err -> it "compiles the fixture" (fail err)
  Right made -> cases made

writeModules :: Aff Unit
writeModules = case compiled of
  Left err -> fail err
  Right dmos -> do
    FS.mkdir' dir { recursive: true, mode: Perms.mkPerms Perms.all Perms.all Perms.all }
    write "Base.IO" dmos.io
    write "Base.String" dmos.string
    write "Main" dmos.main
    write "Other" dmos.other
    write "BadInit" dmos.badInit
    write "Bug" bugModule
    write "BugInit" bugInitModule
    write "Host" dmos.host
    write "Speaker" dmos.speaker
    writeText (dir <> "/impl.mjs") implementations
    writeText (dir <> "/speaking.mjs") speakingImpl
    writeText (dir <> "/silent.mjs") silentImpl
    writeText (manifestPath "speaking") (speakerManifestFor "./speaking.mjs")
    writeText (manifestPath "silent") (speakerManifestFor "./silent.mjs")
    writeText (manifestPath "two-params") (manifestWith "./impl.mjs" """[ "int", "int" ]""")
    writeText (manifestPath "no-signature")
      """{ "formatVersion": 1, "target": "javascript",
           "modules": [ { "module": "Host", "specifier": "./impl.mjs", "foreigns": [] } ] }"""
    FS.mkdir' (dir <> "/node_modules/stella-fixture-host")
      { recursive: true, mode: Perms.mkPerms Perms.all Perms.all Perms.all }
    writeText (dir <> "/node_modules/stella-fixture-host/package.json")
      """{ "name": "stella-fixture-host", "type": "module", "main": "index.mjs" }"""
    writeText (dir <> "/node_modules/stella-fixture-host/index.mjs") implementations
    writeText (manifestPath "bare") (manifestFor "stella-fixture-host")
    writeText (manifestPath "node-url") (manifestFor "node:fs")
    here <- liftEffect Process.cwd
    writeText (manifestPath "file-url")
      (manifestFor ("file://" <> here <> "/" <> dir <> "/impl.mjs"))
    writeText (manifestPath "absolute-path")
      (manifestFor (here <> "/" <> dir <> "/impl.mjs"))
    -- entries for names the interpreter claims, pointing nowhere and giving no
    -- signature: an entry the interpreter would consult fails on either
    writeText (manifestPath "claimed")
      """{ "formatVersion": 1, "target": "javascript",
           "modules": [ { "module": "Base.IO", "specifier": "./nowhere.mjs", "foreigns": [] }
                      , { "module": "Base.String", "specifier": "./nowhere.mjs", "foreigns": [] } ] }"""
    writeText (dir <> "/refusing.mjs") refusingImpl
    writeText (manifestPath "refusing") (manifestFor "./refusing.mjs")
    writeText (dir <> "/not-a-function.mjs") notAFunction
    writeText (dir <> "/wrong-export.mjs") wrongExport
    writeText (manifestPath "good") (manifestFor "./impl.mjs")
    writeText (manifestPath "missing-module") (manifestFor "./nowhere.mjs")
    writeText (manifestPath "not-a-function") (manifestFor "./not-a-function.mjs")
    writeText (manifestPath "wrong-export") (manifestFor "./wrong-export.mjs")
    writeText (manifestPath "twice")
      """{ "formatVersion": 1, "target": "javascript",
           "modules": [ { "module": "Host", "specifier": "./impl.mjs", "foreigns": [] }
                      , { "module": "Host", "specifier": "./impl.mjs", "foreigns": [] } ] }"""
    writeText (manifestPath "other-target")
      """{ "formatVersion": 1, "target": "wasm", "modules": [] }"""
    writeText (manifestPath "later-version")
      """{ "formatVersion": 2, "target": "javascript", "modules": [] }"""
    writeText (manifestPath "garbage") "{ not json"
    -- a file that is not bytecode, which is a different thing to be told
    buffer <- liftEffect (Buffer.fromString "not a dmo" UTF8)
    FS.writeFile (pathOf "Garbage") buffer
  where
  write name dmo = case encode dmo of
    Left err -> fail ("could not encode " <> name <> ": " <> show err)
    Right bytes -> do
      buffer <- liftEffect (Buffer.fromArray bytes)
      FS.writeFile (pathOf name) buffer

-- Manifests --------------------------------------------------------------------------

-- | `module Host where foreign greet : Int -> Int`, a module whose foreign nothing
-- | but a manifest can supply.
hostModuleName :: ModuleName
hostModuleName = ModuleName "Host"

hostModule :: Module P.Int
hostModule =
  { annotation: 0
  , name: hostModuleName
  , imports: []
  , exports: []
  , decls:
      [ DeclForeign 1
          { name: Ident "greet"
          , scheme: monoScheme (pureFn (TCon intTy []) (TCon intTy []))
          , attributes: []
          }
      , DeclNonRec 2
          { name: Ident "greeted"
          , scheme: monoScheme (TCon intTy [])
          , value: App 0 (Global 0 (Qualified hostModuleName (Ident "greet")) [])
              (Lit 0 (LitInt 1))
          , attributes: []
          }
      ]
  }

-- | The implementations that module's manifest points at, written where a manifest
-- | would point at them.
-- |
-- | It refuses unless it was handed `1`, as a host number: the argument arrives as an
-- | argument and not inside an array, and unwrapped by its kind.
implementations :: P.String
implementations =
  "import { refuse } from '@stella-lang/runtime/foreign';\n\
  \export const greet = (n) => n === 1 ? n : refuse('wrong argument');\n"

-- | One that refuses, which is what an implementation does where it cannot produce a
-- | value.
refusingImpl :: P.String
refusingImpl =
  "import { refuse } from '@stella-lang/runtime/foreign';\n\
  \export const greet = (_n) => refuse('nothing to give');\n"

-- | An export that is reached and is not a function.
notAFunction :: P.String
notAFunction = "export const greet = 41;\n"

-- | An export that is not there.
wrongExport :: P.String
wrongExport = "export const hello = (n) => n;\n"

-- | A manifest for `Host`, giving `greet` the signature its declaration has.
manifestFor :: P.String -> P.String
manifestFor specifier = manifestWith specifier """[ "int" ]"""

-- | The same, with the `params` given.
manifestWith :: P.String -> P.String -> P.String
manifestWith specifier params =
  """{ "formatVersion": 1, "target": "javascript",
       "modules": [ { "module": "Host", "specifier": """"
    <> specifier
    <> """", "foreigns": [ { "name": "greet", "params": """
    <> params
    <> """, "result": "int" } ] } ] }"""

-- | `module Speaker where foreign say : Int -> IO Unit ; main = say 7`, a program whose
-- | entry point is an action a host constructs.
speakerModuleName :: ModuleName
speakerModuleName = ModuleName "Speaker"

speakerModule :: Module P.Int
speakerModule =
  { annotation: 0
  , name: speakerModuleName
  , imports: []
  , exports: []
  , decls:
      [ DeclForeign 1
          { name: Ident "say"
          , scheme: monoScheme (pureFn (TCon intTy []) (ioOf unit'))
          , attributes: []
          }
      , DeclNonRec 2
          { name: Ident "main"
          , scheme: monoScheme (ioOf unit')
          , value: App 0 (Global 0 (Qualified speakerModuleName (Ident "say")) [])
              (Lit 0 (LitInt 7))
          , attributes: []
          }
      ]
  }

-- | An implementation that returns the action rather than performing it. What the
-- | action writes is what shows it ran, and ran once the entry point was executed.
speakingImpl :: P.String
speakingImpl =
  "export const say = (n) => () => { process.stderr.write(`said ${n}\\n`); };\n"

-- | One whose action refuses, which ends a run that had begun.
silentImpl :: P.String
silentImpl =
  "import { refuse } from '@stella-lang/runtime/foreign';\n\
  \export const say = (_n) => () => refuse('nothing to say');\n"

speakerManifestFor :: P.String -> P.String
speakerManifestFor specifier =
  """{ "formatVersion": 1, "target": "javascript",
       "modules": [ { "module": "Speaker", "specifier": """"
    <> specifier
    <>
      """", "foreigns":
            [ { "name": "say", "params": [ "int" ], "result": { "action": "unit" } } ] } ] }"""

writeText :: P.String -> P.String -> Aff Unit
writeText path text = do
  buffer <- liftEffect (Buffer.fromString text UTF8)
  FS.writeFile path buffer

manifestPath :: P.String -> P.String
manifestPath name = dir <> "/" <> name <> ".json"
