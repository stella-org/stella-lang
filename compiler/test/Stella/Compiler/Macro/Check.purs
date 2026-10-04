-- | Whether a value a macro name stands for is a parser of terms, read from the
-- | interface declaring it; and `Stella.Syntax` compiled after `Base.Int`.
module Test.Stella.Compiler.Macro.Check (spec) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Either (Either(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Data.Tuple (Tuple(..))
import Stella.Compiler.Interface.Environment (addInterface, initialEnvironment, viewFor)
import Stella.Compiler.Interface.Module (ModuleInterface, ValueEntry, ValueSort(..), emptyDeclarations, emptyExports)
import Stella.Compiler.Interface.Prim (primAttribute)
import Stella.Compiler.Interface.Scheme (Scheme, SchemeBody(..), plainScheme)
import Stella.Compiler.Macro.Bundle (syntaxModuleName)
import Stella.Compiler.Macro.Check (Category(..), MacroRefusal(..), checkMacro)
import Stella.Compiler.Macro.Compiled (compiled)
import Stella.Compiler.TypedCore (Ident(..), Kind(..), KindVar(..), ModuleName(..), Qualified(..), TyName(..), TyVar(..), Type(..), monoScheme)
import Stella.Compiler.TypedCore.Prim (intTy, unitTy)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

syntaxType :: P.String -> Type
syntaxType n = TCon (Qualified syntaxModuleName (TyName n)) []

-- | `Parser τ`.
parserOf :: Type -> Type
parserOf = TApp (syntaxType "Parser")

termParser :: Type
termParser = parserOf (TApp (syntaxType "Syntax") (syntaxType "Term"))

macros :: ModuleName
macros = ModuleName "Macros"

marked :: Scheme -> ValueEntry
marked scheme = { sort: SortValue, scheme, attributes: [ { name: primAttribute "macro", positional: [], keyword: [] } ] }

-- | `Macros`, declaring a value of each kind a macro name could stand for.
macrosInterface :: ModuleInterface
macrosInterface =
  { name: macros
  , imports: []
  , exports: emptyExports
  , declarations: emptyDeclarations
      { values = Map.fromFoldable
          [ Tuple (Ident "terms") (marked (plainScheme (monoScheme termParser)))
          , Tuple (Ident "unmarked") ((marked (plainScheme (monoScheme termParser))) { attributes = [] })
          , Tuple (Ident "ints") (marked (plainScheme (monoScheme (parserOf (TCon intTy [])))))
          , Tuple (Ident "quantified") (marked (plainScheme (monoScheme (TForall (TyVar "a") KType termParser))))
          , Tuple (Ident "kinded") (marked { kindVars: [ KindVar "k" ], body: Plain termParser })
          , Tuple (Ident "computed") (marked { kindVars: [], body: Computation termParser (TCon unitTy []) })
          , Tuple (Ident "Built") ((marked (plainScheme (monoScheme termParser))) { sort = SortConstructor (Qualified macros (TyName "B")) })
          ]
      }
  , implicitHandlers: []
  , catalogOnly: Set.empty
  , arities: Map.empty
  }

spec :: Spec Unit
spec = describe "Stella.Compiler.Macro" do
  describe "a macro a call may run" do
    it "is a value carrying Prim.macro whose scheme is exactly Parser (Syntax Term)" do
      case addInterface macrosInterface initialEnvironment >>= viewFor [ macros ] # lmapShow of
        Left err -> fail err
        Right view -> do
          let checked x = checkMacro view (Qualified macros (Ident x))
          checked "terms" `shouldEqual` Right TermCategory
          checked "unmarked" `shouldEqual` Left (MacroNotMarked (Qualified macros (Ident "unmarked")))
          map refusedAs (Array.mapMaybe (\x -> leftOf (checked x)) [ "ints", "quantified", "kinded", "computed" ])
            `shouldEqual` [ "ints", "quantified", "kinded", "computed" ]
          checked "Built" `shouldEqual` Left (MacroNotAValue (Qualified macros (Ident "Built")))
          checked "absent" `shouldEqual` Left (MacroUndeclared (Qualified macros (Ident "absent")))

  describe "Stella.Syntax compiled" do
    it "loads after Base.Int, the one module it depends on" do
      case compiled of
        Left err -> fail err
        Right c -> map _.name c.modules `shouldEqual` [ ModuleName "Base.Int", syntaxModuleName ]
  where
  lmapShow = case _ of
    Left e -> Left (show e)
    Right x -> Right x
  leftOf = case _ of
    Left e -> Just e
    Right _ -> Nothing
  refusedAs = case _ of
    MacroNotAParser (Qualified _ (Ident x)) _ -> x
    other -> show other
