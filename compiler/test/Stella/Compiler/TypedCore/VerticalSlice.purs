-- | The vertical slice of the Examples document, written in Core by hand and
-- | run through declaration checking.
-- |
-- | Two modules are written out. `Base.Int` supplies the arithmetic the slice
-- | uses, as an ordinary foreign of the `Base` ABI surface. `Main` declares a
-- | list type, sums one recursively, and applies that to a literal list.
-- |
-- | Together they take the path a compiled module takes: the kinds of a `data`
-- | declaration, the scheme each constructor acquires, the dependency order of
-- | value declarations, and the typing of a decision tree. Passing is the
-- | assertion.
-- |
-- | Each mutation below is the slice with one thing changed, and each must be
-- | rejected. They are what keeps passing from being vacuous.
module Test.Stella.Compiler.TypedCore.VerticalSlice
  ( spec
  , intModule
  , verticalSlice
  , listDecl
  ) where

import Prelude

import Prim as P

import Stella.Compiler.TypedCore (CtorBranch, Decl(..), DecisionTree(..), Export(..), Expr(..), Ident(..), Kind(..), Literal(..), Module, ModuleName(..), Occurrence(..), Qualified(..), TyName(..), TyVar(..), Type(..), TypeScheme, monoScheme)
import Stella.Compiler.TypedCore.Check (CheckError(..))
import Stella.Compiler.TypedCore.Declare (DeclError(..), DeclFailure, declare)
import Stella.Compiler.TypedCore.Prim (intTy, primSignature, pureFn)
import Stella.Compiler.TypedCore.Signature (Signature, TyConInfo(..), lookupCtor, lookupTyCon, lookupValue)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

-- Names -----------------------------------------------------------------------

mainModuleName :: ModuleName
mainModuleName = ModuleName "Main"

intModuleName :: ModuleName
intModuleName = ModuleName "Base.Int"

int :: Type
int = TCon intTy []

listTyCon :: Qualified TyName
listTyCon = Qualified mainModuleName (TyName "List")

listOf :: Type -> Type
listOf a = TApp (TCon listTyCon []) a

nil :: Qualified Ident
nil = Qualified mainModuleName (Ident "Nil")

cons :: Qualified Ident
cons = Qualified mainModuleName (Ident "Cons")

sumName :: Qualified Ident
sumName = Qualified mainModuleName (Ident "sum")

resultName :: Qualified Ident
resultName = Qualified mainModuleName (Ident "result")

intAdd :: Qualified Ident
intAdd = Qualified intModuleName (Ident "add")

-- The modules -----------------------------------------------------------------

-- | `module Base.Int where foreign add : Int -> Int -> Int`.
-- |
-- | `Base.*` is the versioned runtime ABI surface, which is where arithmetic
-- | lives: `Prim` holds the vocabulary the rules of Core name and no values but
-- | `Prim.Unit`. Every arrow is pure, which is what D23 asks of a foreign type.
-- |
-- | This stands for the package implementing the ABI, which is the one entitled
-- | to a name under `Base`. Package resolution is what verifies that, so the
-- | module passes ordinary declaration checking like any other.
-- |
-- | The module carries 0 and its declaration 1.
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

-- | The slice. The module carries 0 and its declarations 1, 2, and 3, so that
-- | annotations are observable.
verticalSlice :: Module P.Int
verticalSlice = slice [ listDecl, sumDecl, resultDecl ]

slice :: P.Array (Decl P.Int) -> Module P.Int
slice decls =
  { annotation: 0
  , name: mainModuleName
  , imports: [ intModuleName ]
  , exports: []
  , decls
  }

-- | `data List (a : Type) = Nil | Cons a (List a)`.
listDecl :: Decl P.Int
listDecl = DeclData 1
  { name: TyName "List"
  , kindVars: []
  , params: [ { name: TyVar "a", kind: KType } ]
  , constructors:
      [ { name: Ident "Nil", tag: 0, fields: [] }
      , { name: Ident "Cons", tag: 1, fields: [ TVar (TyVar "a"), listOf (TVar (TyVar "a")) ] }
      ]
  , isNewtype: false
  , attributes: []
  }

-- | `rec { Main.sum : List Int -{()}-> Int = … }`.
sumDecl :: Decl P.Int
sumDecl = sumDeclOf sumBody

sumDeclOf :: Expr P.Int -> Decl P.Int
sumDeclOf value = DeclRec 2
  [ { name: Ident "sum"
    , scheme: monoScheme (pureFn (listOf int) int)
    , value
    , attributes: []
    }
  ]

-- | `nonrec Main.result : Int = …`.
resultDecl :: Decl P.Int
resultDecl = resultDeclOf resultBody

resultDeclOf :: Expr P.Int -> Decl P.Int
resultDeclOf value = DeclNonRec 3
  { name: Ident "result"
  , scheme: monoScheme int
  , value
  , attributes: []
  }

-- The terms -------------------------------------------------------------------

-- | `λ (xs : List Int). case (xs) of dt`, the shape every summation here keeps.
summing :: DecisionTree P.Int -> Expr P.Int
summing dt = Lam 0 (Ident "xs") (listOf int) (Case 0 [ Var 0 (Ident "xs") ] dt)

sumBody :: Expr P.Int
sumBody = summing (SwitchCtor (OccScrutinee 0) [ nilBranch, consBranch ] Nothing)

nilBranch :: CtorBranch P.Int
nilBranch = { ctor: nil, tree: Leaf (Lit 0 (LitInt 0)) }

-- | The fields are bound from the occurrence the dispatch established, and the
-- | body adds the head to the sum of the tail.
consBranch :: CtorBranch P.Int
consBranch =
  { ctor: cons
  , tree:
      Bind (Ident "x") (OccField (OccScrutinee 0) cons 0)
        $ Bind (Ident "ys") (OccField (OccScrutinee 0) cons 1)
        $ Leaf
        $ App 0
            (App 0 (Global 0 intAdd []) (Var 0 (Ident "x")))
            (App 0 (Global 0 sumName []) (Var 0 (Ident "ys")))
  }

-- | `Main.sum ( Main.Cons [Int] 1 ( … ( Main.Nil [Int] ) ) )`.
resultBody :: Expr P.Int
resultBody = summed (listLiteral (TyApp 0 (Global 0 nil []) int))

summed :: Expr P.Int -> Expr P.Int
summed xs = App 0 (Global 0 sumName []) xs

-- | `1, 2, 3` consed onto whatever stands at the end.
listLiteral :: Expr P.Int -> Expr P.Int
listLiteral end = consAt 1 (consAt 2 (consAt 3 end))
  where
  consAt n rest =
    App 0
      (App 0 (TyApp 0 (Global 0 cons []) int) (Lit 0 (LitInt n)))
      rest

-- Running the checker ---------------------------------------------------------

-- | `Σ` the two modules contribute, `Base.Int` first: the slice names
-- | `Base.Int.add`, so the signature of `Base.Int` is what `Main` is checked
-- | against.
checkedSignature :: Module P.Int -> Either (DeclFailure P.Int) Signature
checkedSignature m = do
  imported <- declare primSignature intModule
  declare imported m

-- | The verdict on a module, with the signature it would contribute dropped.
verdict :: Module P.Int -> Either DeclError Unit
verdict m = case checkedSignature m of
  Left failure -> Left failure.error
  Right _ -> Right unit

sliceSignature :: Maybe Signature
sliceSignature = case checkedSignature verticalSlice of
  Left _ -> Nothing
  Right sig -> Just sig

valueScheme :: Qualified Ident -> Maybe TypeScheme
valueScheme name = sliceSignature >>= \sig -> map _.scheme (lookupValue sig name)

ctorScheme :: Qualified Ident -> Maybe TypeScheme
ctorScheme name = sliceSignature >>= \sig -> map _.scheme (lookupCtor sig name)

-- | The constructors of a data entry. An intrinsic entry has none at all,
-- | which a `switchCtor` would otherwise exhaust vacuously, so the two are
-- | distinguished rather than both read as an empty list.
dataConstructors :: Qualified TyName -> Maybe (P.Array (Qualified Ident))
dataConstructors name = sliceSignature >>= \sig -> case lookupTyCon sig name of
  Just (DataTyCon _ constructors) -> Just constructors
  _ -> Nothing

-- Mutations -------------------------------------------------------------------

-- | The dispatch with its `Cons` branch removed. A `switch*` is locally total:
-- | absent a default its branches exhaust the constructors, or a value is left
-- | with no destination.
withoutConsBranch :: Module P.Int
withoutConsBranch =
  slice [ listDecl, sumDeclOf (summing (SwitchCtor (OccScrutinee 0) [ nilBranch ] Nothing)), resultDecl ]

-- | The end of the literal list left uninstantiated. `Main.Nil` is polymorphic
-- | until a type is applied to it, and `Main.Cons [Int]` takes a `List Int`.
withUninstantiatedNil :: Module P.Int
withUninstantiatedNil =
  slice [ listDecl, sumDecl, resultDeclOf (summed (listLiteral (Global 0 nil []))) ]

-- | The two value declarations transposed. Value declarations are in dependency
-- | order, so a `nonrec` refers to nothing declared later.
withResultBeforeSum :: Module P.Int
withResultBeforeSum = slice [ listDecl, resultDecl, sumDecl ]

-- | The summation defined as itself. A recursive right-hand side is guarded,
-- | that is, syntactically a function value (D14); under strict evaluation this
-- | binding has no meaning.
withUnguardedSum :: Module P.Int
withUnguardedSum = slice [ listDecl, sumDeclOf (Global 0 sumName []), resultDecl ]

-- The specification -----------------------------------------------------------

spec :: Spec Unit
spec = describe "Stella.Compiler.TypedCore.VerticalSlice" do
  describe "the slice" do
    it "passes declaration checking, kinds and types together" do
      verdict verticalSlice `shouldEqual` Right unit

    it "contributes a data entry carrying both constructors" do
      dataConstructors listTyCon `shouldEqual` Just [ nil, cons ]

    it "gives each constructor a type quantified over the parameter of its own type" do
      ctorScheme nil `shouldEqual`
        Just (monoScheme (TForall (TyVar "a") KType (listOf (TVar (TyVar "a")))))
      ctorScheme cons `shouldEqual`
        Just
          ( monoScheme
              ( TForall (TyVar "a") KType
                  ( pureFn (TVar (TyVar "a"))
                      (pureFn (listOf (TVar (TyVar "a"))) (listOf (TVar (TyVar "a"))))
                  )
              )
          )

    it "records the summation at the pure arrow it declares" do
      valueScheme sumName `shouldEqual` Just (monoScheme (pureFn (listOf int) int))

    it "records the applied result at Int" do
      valueScheme resultName `shouldEqual` Just (monoScheme int)

  describe "mutations of it" do
    it "refuses a dispatch that leaves a constructor with no destination" do
      verdict withoutConsBranch `shouldEqual` Left (IllTyped NotExhaustive)

    it "refuses a polymorphic constructor where an instantiated one is wanted" do
      verdict withUninstantiatedNil `shouldEqual`
        Left
          ( IllTyped
              ( TypeMismatch (listOf int)
                  (TForall (TyVar "a") KType (listOf (TVar (TyVar "a"))))
              )
          )

    it "refuses a nonrec referring to a value declared after it" do
      verdict withResultBeforeSum `shouldEqual` Left (ForwardReference sumName)

    it "refuses a recursive right-hand side that is not a function value" do
      verdict withUnguardedSum `shouldEqual` Left (RecursiveNotFunctionValue sumName)
