-- | `Base.Array` and a module over it, carried the whole way.
-- |
-- | Two Core modules are written by hand and taken through every stage: checked,
-- | translated, lowered, encoded, decoded, and loaded. What a global slot holds
-- | after that is the assertion, so what is exercised is the chain rather than any
-- | one link — the manifest supplying an `intrinsic opaque`, a `foreign` the
-- | interpreter claims lowering to a `PRIM`, an array reaching a register as an
-- | opaque value, and the write being seen by the read.
-- |
-- | | Module | What it holds |
-- | | --- | --- |
-- | | `Base.Array` | the four entries, checked against a manifest that supplies `Array` |
-- | | `Main` | `result`, which allocates, writes two slots, and reads one back |
-- |
-- | **The loop a `mapArray` would be written as is not here**, and cannot be:
-- | `stella-base-0.1` holds no comparison on `Int`, so nothing decides `i < n`
-- | ([Implementation Plan](../../../docs/technical-references/01-Introduction/04-Implementation-Plan.md)).
-- | The writes are unrolled instead, which reaches the same entries by the same
-- | route.
module Test.Steam.Arrays (spec) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Either (Either(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Ref as Ref
import Run (runBaseEffect)
import Run.Except as Except
import Steam.Foreign (emptyTable)
import Steam.Load (LoadError, Store, emptyStore, globalNamed, load, namesOf, noIdentities)
import Steam.Value (Value(..))
import Stella.Compiler.Bytecode (Dmo, decode, encode, lower)
import Stella.Compiler.Interface (importsOf, interfaceOf, noImports)
import Stella.Compiler.MiddleEnd (translate)
import Stella.Compiler.TypedCore (Decl(..), Export(..), Expr(..), Ident(..), Kind(..), Literal(..), Module, ModuleName(..), Qualified(..), TyName(..), TyVar(..), Type(..), declareAnnotated, monoScheme, primSignature)
import Stella.Compiler.TypedCore.Prim (intTy, pureFn, unitCtor, unitTy)
import Stella.Compiler.TypedCore.Signature (CanonicalClass(..), Signature, TyConInfo(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

-- Names --------------------------------------------------------------------------

arrayModuleName :: ModuleName
arrayModuleName = ModuleName "Base.Array"

mainModuleName :: ModuleName
mainModuleName = ModuleName "Main"

arrayTy :: Qualified TyName
arrayTy = Qualified arrayModuleName (TyName "Array")

entry :: P.String -> Qualified Ident
entry name = Qualified arrayModuleName (Ident name)

mainResult :: Qualified Ident
mainResult = Qualified mainModuleName (Ident "result")

mainSize :: Qualified Ident
mainSize = Qualified mainModuleName (Ident "size")

mainWrote :: Qualified Ident
mainWrote = Qualified mainModuleName (Ident "wrote")

int :: Type
int = TCon intTy []

-- | `Array τ`.
arrayOf :: Type -> Type
arrayOf t = TApp (TCon arrayTy []) t

tyA :: Type
tyA = TVar (TyVar "a")

-- The manifest ---------------------------------------------------------------------

-- | What the ABI manifest supplies to `Base.Array`, which is a type constructor and
-- | nothing else.
-- |
-- | **No declaration produces this entry.** `Array` is a manifest intrinsic of the
-- | **opaque** canonical class, so nothing takes a value of it apart and a
-- | `switchCtor` over it is ill-formed
-- | ([Prim and Base](../../../docs/technical-references/06-Modules/02-Prim-and-Base.md)).
manifest :: Signature
manifest = primSignature
  { types = Map.insert arrayTy
      (IntrinsicTyCon (monoScheme (KFun KType KType)) CanonicalOpaque)
      primSignature.types
  }

-- The Core modules -------------------------------------------------------------------

-- | `Base.Array`, whose four entries are the operations of this version. They are
-- | ordinary `foreign` declarations: that the machine carries each one out itself is
-- | settled by the name where the module is loaded, and nothing here says so.
arrayModule :: Module P.Int
arrayModule =
  { annotation: 0
  , name: arrayModuleName
  , imports: []
  , exports:
      [ ExportValue (Ident "length")
      , ExportValue (Ident "unsafeNew")
      , ExportValue (Ident "unsafeSet")
      , ExportValue (Ident "unsafeIndex")
      ]
  , decls:
      [ foreign' 1 "length" (forallA (pureFn (arrayOf tyA) int))
      , foreign' 2 "unsafeNew" (forallA (pureFn int (arrayOf tyA)))
      , foreign' 3 "unsafeSet"
          (forallA (pureFn int (pureFn tyA (pureFn (arrayOf tyA) (TCon unitTy [])))))
      , foreign' 4 "unsafeIndex" (forallA (pureFn (arrayOf tyA) (pureFn int tyA)))
      ]
  }
  where
  foreign' at name scheme = DeclForeign at { name: Ident name, scheme, attributes: [] }

  -- a kind scheme binds kind variables only (D3); a type-level `forall` is part
  -- of the type
  forallA body = monoScheme (TForall (TyVar "a") KType body)

-- | `Main`, a module over `Base.Array` and nothing else.
-- |
-- | `result` allocates an array of two, writes both slots, and reads the second
-- | back. **Every slot is written before one is read**, which is the precondition of
-- | `unsafeIndex` discharged where a library would discharge it (D42).
mainModule :: Module P.Int
mainModule =
  { annotation: 0
  , name: mainModuleName
  , imports: [ arrayModuleName ]
  , exports: []
  , decls:
      [ DeclNonRec 1
          { name: Ident "result"
          , scheme: monoScheme int
          , value:
              Let 0 (Ident "xs") (arrayOf int) (App 0 (at "unsafeNew") (Lit 0 (LitInt 2)))
                ( Let 0 (Ident "_0") (TCon unitTy [])
                    (setting 0 7)
                    ( Let 0 (Ident "_1") (TCon unitTy [])
                        (setting 1 9)
                        (App 0 (App 0 (at "unsafeIndex") (Var 0 (Ident "xs"))) (Lit 0 (LitInt 1)))
                    )
                )
          , attributes: []
          }
      , DeclNonRec 2
          { name: Ident "size"
          , scheme: monoScheme int
          , value:
              Let 0 (Ident "xs") (arrayOf int) (App 0 (at "unsafeNew") (Lit 0 (LitInt 3)))
                (App 0 (at "length") (Var 0 (Ident "xs")))
          , attributes: []
          }
      -- what a write answers with, kept rather than discarded: the value is
      -- `Prim.Unit` under the identity the registry assigned, and a constructor of
      -- no fields under any other identity would be a different value
      , DeclNonRec 3
          { name: Ident "wrote"
          , scheme: monoScheme (TCon unitTy [])
          , value:
              Let 0 (Ident "xs") (arrayOf int) (App 0 (at "unsafeNew") (Lit 0 (LitInt 1)))
                (setting 0 1)
          , attributes: []
          }
      ]
  }
  where
  -- every entry is `forall a.`, and Core instantiates explicitly (D8)
  at name = TyApp 0 (Global 0 (entry name) []) int

  setting i v =
    App 0 (App 0 (App 0 (at "unsafeSet") (Lit 0 (LitInt i))) (Lit 0 (LitInt v)))
      (Var 0 (Ident "xs"))

-- Compiling them ----------------------------------------------------------------------

-- | The two modules lowered, each carried through the container: what a loader is
-- | given is a decoded file and not what a lowering happened to hold.
compiled :: Either P.String { array :: Dmo, main :: Dmo }
compiled = case declareAnnotated manifest arrayModule of
  Left err -> Left ("Base.Array did not declare: " <> show err.error)
  Right arrayDeclared -> do
    arrayDmo <- lowered =<< translated arrayModule noImports arrayDeclared
    case declareAnnotated arrayDeclared.signature mainModule of
      Left err -> Left ("Main did not declare: " <> show err.error)
      Right mainDeclared -> do
        mainMid <- translated mainModule noImports mainDeclared
        imports <- case importsOf [ interfaceOf mainMid.module ] of
          Left err -> Left (show err)
          Right imports -> Right imports
        mainMid2 <- translated mainModule imports mainDeclared
        mainDmo <- lowered mainMid2
        pure { array: arrayDmo, main: mainDmo }
  where
  translated m imports declared = case translate imports m declared of
    Left err -> Left (show err)
    Right mid -> Right mid

  lowered mid = case lower mid of
    Left err -> Left (show err)
    Right out -> case encode out.dmo of
      Left err -> Left (show err)
      Right bytes -> case decode bytes of
        Left err -> Left (show err)
        Right dmo -> Right dmo

-- Loading them ------------------------------------------------------------------------

fresh :: Effect Store
fresh = map (emptyStore emptyTable) (Ref.new noIdentities)

loading :: P.Array Dmo -> Aff (Either LoadError Store)
loading modules = liftEffect do
  store <- fresh
  runBaseEffect (Except.runExcept (Array.foldM load store modules))

valueOf :: Store -> Qualified Ident -> Aff (Maybe Value)
valueOf store name = liftEffect case globalNamed store name of
  Nothing -> pure Nothing
  Just slot -> Ref.read slot

held :: Maybe Value -> Maybe P.Int
held = case _ of
  Just (VInt n) -> Just n
  _ -> Nothing

spec :: Spec Unit
spec = describe "Steam, over Base.Array and a module on top of it" do

  it "compiles both modules the whole way" do
    case compiled of
      Left err -> fail err
      Right _ -> pure unit

  -- a saturated call to a `Base` entry the ABI fixes the meaning of is a `prim`
  -- and not an `ffi`, and the two would be indistinguishable downstream: the
  -- loader resolves such a name to the interpreter either way
  it "lowers the calls to operations rather than to foreign references" do
    case compiled of
      Left err -> fail err
      Right dmos -> do
        Array.null dmos.main.prims `shouldEqual` false
        Array.null dmos.main.foreignRefs `shouldEqual` true

  -- the chain end to end: the manifest's intrinsic, four `foreign` declarations the
  -- loader resolves to the interpreter, and a program that allocates, writes, and
  -- reads back
  it "reads back what it wrote, through the whole pipeline" do
    case compiled of
      Left err -> fail err
      Right dmos -> do
        outcome <- loading [ dmos.array, dmos.main ]
        case outcome of
          Left err -> fail (show err)
          Right store -> do
            value <- valueOf store mainResult
            held value `shouldEqual` Just 9

  it "reports the slot count an allocation was asked for" do
    case compiled of
      Left err -> fail err
      Right dmos -> do
        outcome <- loading [ dmos.array, dmos.main ]
        case outcome of
          Left err -> fail (show err)
          Right store -> do
            value <- valueOf store mainSize
            held value `shouldEqual` Just 3

  -- the write answers with the registry's own `Prim.Unit`, which is what makes it
  -- the same value every other `Prim.Unit` in the program is
  it "answers a write with the Prim.Unit the registry assigned" do
    case compiled of
      Left err -> fail err
      Right dmos -> do
        outcome <- loading [ dmos.array, dmos.main ]
        case outcome of
          Left err -> fail (show err)
          Right store -> do
            value <- valueOf store mainWrote
            names <- liftEffect (namesOf store)
            case value of
              Just (VData ctor []) ->
                Map.lookup ctor names.ctors `shouldEqual` Just unitCtor
              _ -> fail "the write did not answer with a constructor of no fields"
