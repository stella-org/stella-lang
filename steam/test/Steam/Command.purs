-- | The `run` command, as a process.
-- |
-- | **What is asserted is the exit status and the streams**, because that is what
-- | the command answers with: the value the entry point produced is deliberately
-- | not reported, so a case reading it would be reading what the command does not
-- | say.
-- |
-- | **Totality is the property these are for.** Two questions decide the status —
-- | was it an interpreter bug, and had the entry point begun to run — and a case
-- | per leaf is what shows nothing falls between them. A path left unclassified
-- | would exit `0`, which is the worst of the four answers.
module Test.Steam.Command (spec) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Traversable (traverse)
import Node.FS.Perms as Perms
import Node.FS.Stats as Stats
import Data.String as String
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Node.Buffer as Buffer
import Node.ChildProcess.Types (Exit(..))
import Node.Encoding (Encoding(..))
import Node.FS.Aff as FS
import Node.Library.Execa (execa)
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
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

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
                ( Lam 0 (Ident "_") unit'
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
                  pure { io, string, main, other, badInit }
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

-- | The command reached as a process, which is the whole point: what it answers
-- | with is a status and a stream, and neither is visible from the functions below
-- | it.
invoke :: P.Array P.String -> Aff Outcome
invoke = invokeCommand "run"

invokeCommand :: P.String -> P.Array P.String -> Aff Outcome
invokeCommand command args = do
  result <- execa "node" ([ "steam/index.dev.js", command ] <> args) identity
    >>= _.getResult
  pure
    { status: case result.exit of
        Normally code -> code
        BySignal _ -> -1
    , err: result.stderr
    }

-- | Where this suite's files stand. One directory, written once.
dir :: P.String
dir = "steam/.test-dmo"

-- | The path a module was written to.
pathOf :: P.String -> P.String
pathOf name = dir <> "/" <> name <> ".dmo"

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
    -- a file that is not bytecode, which is a different thing to be told
    buffer <- liftEffect (Buffer.fromString "not a dmo" UTF8)
    FS.writeFile (pathOf "Garbage") buffer
  where
  write name dmo = case encode dmo of
    Left err -> fail ("could not encode " <> name <> ": " <> show err)
    Right bytes -> do
      buffer <- liftEffect (Buffer.fromArray bytes)
      FS.writeFile (pathOf name) buffer

-- | The modules in the order an import admits.
inOrder :: P.Array P.String
inOrder = [ pathOf "Base.IO", pathOf "Base.String", pathOf "Main" ]

spec :: Spec Unit
spec = describe "the steam run command" do

  it "writes the fixture" do
    writeModules
    stat <- FS.stat (pathOf "Main")
    Stats.isFile stat `shouldEqual` true

  describe "a run that finishes" do

    it "exits 0, and says nothing of what the entry point produced" do
      outcome <- invoke inOrder
      outcome.status `shouldEqual` 0
      outcome.err `shouldEqual` ""

    it "takes the entry point named by --entry-global" do
      outcome <- invoke (inOrder <> [ "--entry-global", "second" ])
      outcome.status `shouldEqual` 0

    -- the entry module is named, so another module's `main` is not a competitor
    it "ignores a main in a module that is not the entry module" do
      outcome <- invoke
        ([ pathOf "Base.IO", pathOf "Other", pathOf "Main" ] <> [ "--entry", "Main" ])
      outcome.status `shouldEqual` 0

  describe "a refusal before the entry point runs" do

    it "exits 1 where the order an import needs is not the order given" do
      outcome <- invoke [ pathOf "Main", pathOf "Base.IO" ]
      outcome.status `shouldEqual` 1

    it "exits 1 where a file is not there" do
      outcome <- invoke [ pathOf "Missing" ]
      outcome.status `shouldEqual` 1
      String.contains (String.Pattern "Cannot read") outcome.err
        `shouldEqual` true

    -- told apart from a file that is not there, which is a different thing to act on
    it "exits 1 where a file is not bytecode, and says so" do
      outcome <- invoke [ pathOf "Garbage" ]
      outcome.status `shouldEqual` 1
      String.contains (String.Pattern "Not readable as bytecode") outcome.err
        `shouldEqual` true

    it "exits 1 where no module of the entry name was given" do
      outcome <- invoke (inOrder <> [ "--entry", "Nowhere" ])
      outcome.status `shouldEqual` 1
      String.contains (String.Pattern "--entry") outcome.err `shouldEqual` true

    it "exits 1 where the entry module holds no such global" do
      outcome <- invoke (inOrder <> [ "--entry-global", "absent" ])
      outcome.status `shouldEqual` 1
      String.contains (String.Pattern "--entry-global") outcome.err
        `shouldEqual` true

    it "exits 1 where the entry point is not an action" do
      outcome <- invoke (inOrder <> [ "--entry-global", "notAnAction" ])
      outcome.status `shouldEqual` 1
      String.contains (String.Pattern "not an action") outcome.err
        `shouldEqual` true

    -- the module did not load, so the program never started — which is what a
    -- caller acts on, and is why this is `1` and not the `2` of a fault at run
    it "exits 1 where a module faults while it initializes" do
      outcome <- invoke
        [ pathOf "Base.IO", pathOf "Base.String", pathOf "BadInit", pathOf "Main" ]
      outcome.status `shouldEqual` 1

  describe "a failure after the entry point begins" do

    it "exits 2 where the program faults" do
      outcome <- invoke (inOrder <> [ "--entry-global", "faulting" ])
      outcome.status `shouldEqual` 2

    -- **the two are told apart by when, not by what**: the same fault reached
    -- while a module initialized is `1`, and here it is `2`
    it "tells that apart from the same fault reached before the run" do
      during <- invoke (inOrder <> [ "--entry-global", "faulting" ])
      before <- invoke
        [ pathOf "Base.IO", pathOf "Base.String", pathOf "BadInit", pathOf "Main" ]
      during.status `shouldEqual` 2
      before.status `shouldEqual` 1

    -- **the question asked first is whose the defect is**, not when it happened,
    -- so this is `3` and not the `2` of a program that faulted
    it "exits 3 where the interpreter reaches a state no .dmo admits" do
      outcome <- invoke [ pathOf "Base.IO", pathOf "Bug", "--entry", "Bug" ]
      outcome.status `shouldEqual` 3

    -- a reader acting on this should not take it for their own program failing
    it "says that a bug is a defect above the program" do
      outcome <- invoke [ pathOf "Base.IO", pathOf "Bug", "--entry", "Bug" ]
      String.contains (String.Pattern "Internal error") outcome.err
        `shouldEqual` true

    -- **the question asked first is whose the defect is**, so a bug reached while a
    -- module initialized is `3` and not the `1` of a module that did not load. A
    -- wiring that wrapped every refusal alike would answer `1` here
    it "exits 3 for a bug reached while a module initializes" do
      outcome <- invoke [ pathOf "Base.IO", pathOf "BugInit" ]
      outcome.status `shouldEqual` 3
      String.contains (String.Pattern "Internal error") outcome.err
        `shouldEqual` true

    it "tells that apart from a fault reached in the same place" do
      bug <- invoke [ pathOf "Base.IO", pathOf "BugInit" ]
      fault <- invoke
        [ pathOf "Base.IO", pathOf "Base.String", pathOf "BadInit", pathOf "Main" ]
      bug.status `shouldEqual` 3
      fault.status `shouldEqual` 1

  describe "the session mode" do

    -- printing a failure and exiting zero would tell a reader one thing and a
    -- shell another
    it "refuses rather than reporting success" do
      outcome <- invokeCommand "session" []
      outcome.status `shouldEqual` 1
      String.contains (String.Pattern "not built yet") outcome.err
        `shouldEqual` true

  describe "what a message may not do" do

    -- the technical references are for whoever works on the compiler, and a user
    -- reading a failure has no use for a path into them
    it "points at no internal document" do
      outcomes <- traverse invoke
        [ [ pathOf "Missing" ]
        , [ pathOf "Garbage" ]
        , inOrder <> [ "--entry", "Nowhere" ]
        , inOrder <> [ "--entry-global", "notAnAction" ]
        , [ pathOf "Main", pathOf "Base.IO" ]
        ]
      let
        mentions pattern = Array.any
          (\o -> String.contains (String.Pattern pattern) o.err)
          outcomes
      mentions "technical-references" `shouldEqual` false
      mentions "docs/" `shouldEqual` false
      mentions ".md" `shouldEqual` false
