-- | The arities an interface carries, and what they buy: a saturated call to an
-- | imported value.
-- |
-- | Two modules stand behind these cases. `Lib` exports a function of two
-- | arguments and a value that is not a function; `Main` calls the first,
-- | saturated. **With the interface of `Lib` the call is a `callk` and without it
-- | the same call is a `callu`**, which is the whole of what the file is for.
-- |
-- | The cases after that are the environment's: what it holds, and what it
-- | refuses. The bytes are [Interface.File](Interface/File.purs)'s.
module Test.Stella.Compiler.Interface (spec) where

import Prelude

import Prim as P

import Stella.Compiler.Interface (InterfaceError(..), aritiesOf, importedArities, importsOf, noImports)
import Stella.Compiler.MiddleEnd as M
import Stella.Compiler.TypedCore (Decl(..), Export(..), Expr(..), Ident(..), Literal(..), Module, ModuleName(..), Qualified(..), Type(..), monoScheme)
import Stella.Compiler.TypedCore.Declare (declare, declareAnnotated)
import Stella.Compiler.TypedCore.Prim (intTy, primSignature, pureFn)
import Stella.Compiler.TypedCore.Signature (Signature)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Test.Stella.Compiler.TypedCore.VerticalSlice (intModule)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

-- Names -------------------------------------------------------------------------

libModuleName :: ModuleName
libModuleName = ModuleName "Lib"

mainModuleName :: ModuleName
mainModuleName = ModuleName "Main"

intModuleName :: ModuleName
intModuleName = ModuleName "Base.Int"

intAdd :: Qualified Ident
intAdd = Qualified intModuleName (Ident "add")

add2 :: Qualified Ident
add2 = Qualified libModuleName (Ident "add2")

int :: Type
int = TCon intTy []

-- The modules -------------------------------------------------------------------

-- | `Lib` exports a function of two arguments and a value that is not a
-- | function, and keeps one function to itself.
libModule :: Module P.Int
libModule =
  { annotation: 0
  , name: libModuleName
  , imports: [ intModuleName ]
  , exports: [ ExportValue (Ident "add2"), ExportValue (Ident "one") ]
  , decls:
      [ DeclNonRec 1
          { name: Ident "add2"
          , scheme: monoScheme (pureFn int (pureFn int int))
          , value:
              Lam 0 (Ident "a") int
                ( Lam 0 (Ident "b") int
                    ( App 0 (App 0 (Global 0 intAdd []) (Var 0 (Ident "a")))
                        (Var 0 (Ident "b"))
                    )
                )
          , attributes: []
          }
      , DeclNonRec 2
          { name: Ident "one"
          , scheme: monoScheme int
          , value: Lit 0 (LitInt 1)
          , attributes: []
          }
      , DeclNonRec 3
          { name: Ident "hidden"
          , scheme: monoScheme (pureFn int int)
          , value: Lam 0 (Ident "x") int (Var 0 (Ident "x"))
          , attributes: []
          }
      ]
  }

-- | `Main` calls the exported function of two arguments with two.
mainModule :: Module P.Int
mainModule =
  { annotation: 0
  , name: mainModuleName
  , imports: [ libModuleName ]
  , exports: []
  , decls:
      [ DeclNonRec 1
          { name: Ident "result"
          , scheme: monoScheme int
          , value:
              App 0 (App 0 (Global 0 add2 []) (Lit 0 (LitInt 1))) (Lit 0 (LitInt 2))
          , attributes: []
          }
      ]
  }

mainAlias :: Qualified Ident
mainAlias = Qualified mainModuleName (Ident "alias")

-- | `Main` with the call going through a value that holds the function rather
-- | than naming it. `alias` is evaluated when the module is initialized, so it has
-- | no definitional arity and a call to it is a `callu`; an interface claiming an
-- | arity for it claims one for a right-hand side that has none.
aliasModule :: Module P.Int
aliasModule =
  { annotation: 0
  , name: mainModuleName
  , imports: [ libModuleName ]
  , exports: []
  , decls:
      [ DeclNonRec 1
          { name: Ident "alias"
          , scheme: monoScheme (pureFn int (pureFn int int))
          , value: Global 0 add2 []
          , attributes: []
          }
      , DeclNonRec 2
          { name: Ident "result"
          , scheme: monoScheme int
          , value:
              App 0 (App 0 (Global 0 mainAlias []) (Lit 0 (LitInt 1)))
                (Lit 0 (LitInt 2))
          , attributes: []
          }
      ]
  }

-- Running the pipeline ------------------------------------------------------------

-- | `Lib` declared and translated, with the signature `Main` is checked against.
library :: Either P.String { signature :: Signature, mid :: M.Module }
library = case declare primSignature intModule of
  Left _ -> Left "Base.Int did not declare"
  Right s1 -> case declareAnnotated s1 libModule of
    Left _ -> Left "Lib did not declare"
    Right declared -> case M.translate noImports libModule declared of
      Left err -> Left (show err)
      Right out -> Right { signature: declared.signature, mid: out.module }

-- | The body of the function the last declaration of a version of `Main` becomes,
-- | translated against the interfaces given.
bodyOf :: P.Array Arities -> Module P.Int -> Either P.String M.Expr
bodyOf interfaces m = do
  lib <- library
  case importsOf interfaces of
    Left err -> Left (show err)
    Right imports -> case declareAnnotated lib.signature m of
      Left _ -> Left "Main did not declare"
      Right declared -> case M.translate imports m declared of
        Left err -> Left (show err)
        Right out -> case Array.last out.module.functions of
          Nothing -> Left "Main holds no function"
          Just f -> Right f.body

-- | What translation reads of an interface: the module, and its arities.
type Arities = { name :: ModuleName, imports :: P.Array ModuleName, arities :: Map Ident P.Int }

libInterface :: Either P.String Arities
libInterface = map (\l -> { name: l.mid.name, imports: l.mid.imports, arities: aritiesOf l.mid }) library

-- Fixtures ---------------------------------------------------------------------------

-- | An interface of one module and one entry.
oneEntry :: P.String -> P.Int -> Arities
oneEntry name arity =
  { name: mainModuleName
  , imports: []
  , arities: Map.singleton (Ident name) arity
  }

-- | The arities of an environment built from the interfaces given, every module
-- | among them named, which is how an environment is compared here: `Imports`
-- | itself is opaque.
environmentOf :: P.Array Arities -> Either InterfaceError (Map (Qualified Ident) P.Int)
environmentOf interfaces = importedArities (ModuleName "Elsewhere") (map _.name interfaces) <$> importsOf interfaces

spec :: Spec Unit
spec = describe "Stella.Compiler.Interface" do

  describe "what it buys" do
    it "makes a saturated call to an imported value a known call" do
      case libInterface of
        Left err -> fail err
        Right dmi -> bodyOf [ dmi ] mainModule `shouldEqual` Right
          (M.ETail (M.CCallKnown add2 [ M.ALit (LitInt 1), M.ALit (LitInt 2) ]))

    it "leaves the same call unknown without the interface" do
      -- absent an arity the call is a `callu`, which is correct for every callee:
      -- what the file buys is sharpness
      bodyOf [] mainModule `shouldEqual` Right
        ( M.ETail
            ( M.CCallUnknown (M.AGlobal add2)
                [ M.ALit (LitInt 1), M.ALit (LitInt 2) ]
            )
        )

    it "leaves a call unknown where the interface is of the module being translated" do
      -- an interface naming the module being translated claims an arity for a
      -- right-hand side whose arity is read off the term, so it sharpens nothing
      let selfNamed = { name: mainModuleName, imports: [], arities: Map.singleton (Ident "alias") 2 }
      bodyOf [ selfNamed ] aliasModule `shouldEqual` Right
        ( M.ETail
            ( M.CCallUnknown (M.AGlobal mainAlias)
                [ M.ALit (LitInt 1), M.ALit (LitInt 2) ]
            )
        )
      bodyOf [] aliasModule `shouldEqual` bodyOf [ selfNamed ] aliasModule

  describe "what an interface holds" do
    it "the arity of an exported value whose right-hand side is a lambda" do
      -- `one` is evaluated at initialization and has no definitional arity;
      -- `hidden` is a function this module keeps to itself
      map _.arities libInterface `shouldEqual`
        Right (Map.fromFoldable [ Tuple (Ident "add2") 2 ])

    it "the module's own name" do
      map _.name libInterface `shouldEqual` Right libModuleName

  describe "the environment a translation reads" do
    it "carries the arities of the modules imported, under the qualified names, and not the module translated" do
      case libInterface of
        Left err -> fail err
        Right lib -> do
          (importedArities mainModuleName [ libModuleName ] <$> importsOf [ lib ])
            `shouldEqual` Right (Map.singleton add2 2)
          (importedArities libModuleName [ libModuleName ] <$> importsOf [ lib ])
            `shouldEqual` Right Map.empty

    it "reaches a module through the imports of those imported, and no module outside them" do
      -- `C` imports `B`, which imports `A`; `U` is in the environment and in no
      -- module's imports
      let
        a = { name: ModuleName "A", imports: [], arities: Map.singleton (Ident "f") 2 }
        b = { name: ModuleName "B", imports: [ ModuleName "A" ], arities: Map.empty }
        u = { name: ModuleName "U", imports: [], arities: Map.singleton (Ident "g") 1 }
      (importedArities (ModuleName "C") [ ModuleName "B" ] <$> importsOf [ a, b, u ])
        `shouldEqual` Right (Map.singleton (Qualified (ModuleName "A") (Ident "f")) 2)

    it "refuses an arity of zero, and one below it" do
      -- an interface in memory need not have come through a reader, and
      -- translation splits an application spine at the arity it is given: at zero
      -- a saturated call would become a known call of no arguments
      environmentOf [ oneEntry "f" 0 ]
        `shouldEqual` Left (NotAnArity mainModuleName (Ident "f") 0)
      environmentOf [ oneEntry "f" (-1) ]
        `shouldEqual` Left (NotAnArity mainModuleName (Ident "f") (-1))

    it "refuses two interfaces of one module" do
      -- which arity each of that module's names has would otherwise depend on the
      -- order the two were read in
      environmentOf [ oneEntry "f" 1, oneEntry "g" 1 ]
        `shouldEqual` Left (ModuleTwice mainModuleName)
