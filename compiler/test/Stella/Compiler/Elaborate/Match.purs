-- | The compiler of a `case`'s patterns into a decision plan: the domain each
-- | column ranges over, the plan a matrix compiles to, how many leaves take
-- | each alternative, what no value reaches, and a vector of values no row
-- | matches.
-- |
-- | The constructors are those of four data types of `M`, given to the table
-- | out of their declaration order, which is their tags': `Color` (`Red`,
-- | `Green`, `Blue`), `Opt a` (`None`, `Some a`), `Pair a b` (`Pair a b`), and
-- | `Prim.Unit`.
module Test.Stella.Compiler.Elaborate.Match (spec) where

import Prelude

import Data.Either (Either(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Effect.Aff (Aff)
import Stella.Compiler.Elaborate.Surface.Match (Compiled, Domain(..), Head(..), MatchError(..), Pattern(..), Plan(..), Witness(..), compile, coverageDomain, witness)
import Stella.Compiler.TypedCore.Name (Ident(..), ModuleName(..), Qualified(..), TyName(..))
import Stella.Compiler.TypedCore.Prim (unitCtor, unitTy)
import Stella.Compiler.TypedCore.Term (Literal(..), Occurrence(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

m :: ModuleName
m = ModuleName "M"

ctor :: String -> Qualified Ident
ctor = Qualified m <<< Ident

owner :: String -> Qualified TyName
owner = Qualified m <<< TyName

red :: Qualified Ident
red = ctor "Red"

green :: Qualified Ident
green = ctor "Green"

blue :: Qualified Ident
blue = ctor "Blue"

none :: Qualified Ident
none = ctor "None"

some :: Qualified Ident
some = ctor "Some"

pair :: Qualified Ident
pair = ctor "Pair"

table :: Map.Map (Qualified Ident) { owner :: Qualified TyName, tag :: Int, arity :: Int }
table = Map.fromFoldable
  [ Tuple blue { owner: owner "Color", tag: 2, arity: 0 }
  , Tuple some { owner: owner "Opt", tag: 1, arity: 1 }
  , Tuple red { owner: owner "Color", tag: 0, arity: 0 }
  , Tuple pair { owner: owner "Pair", tag: 0, arity: 2 }
  , Tuple none { owner: owner "Opt", tag: 0, arity: 0 }
  , Tuple green { owner: owner "Color", tag: 1, arity: 0 }
  , Tuple unitCtor { owner: unitTy, tag: 0, arity: 0 }
  ]

-- | A row of the alternative given, written as one row.
row :: Int -> Array (Pattern String) -> { alternative :: Int, choice :: Maybe String, patterns :: Array (Pattern String) }
row alternative patterns = { alternative, choice: Nothing, patterns }

-- | A row of the alternative given, written as the choice labelled.
choice :: Int -> String -> Array (Pattern String) -> { alternative :: Int, choice :: Maybe String, patterns :: Array (Pattern String) }
choice alternative label patterns = { alternative, choice: Just label, patterns }

c :: Qualified Ident -> Array (Pattern String) -> Pattern String
c = PCtor

v :: String -> Pattern String
v = PVar <<< Ident

int :: Int -> Pattern String
int = PLit <<< LitInt

bool :: Boolean -> Pattern String
bool = PLit <<< LitBoolean

or :: Array (Tuple String (Pattern String)) -> Pattern String
or choices = POr (map (\(Tuple label pattern) -> { label, pattern }) choices)

s :: Int -> Occurrence
s = OccScrutinee

field :: Occurrence -> Qualified Ident -> Int -> Occurrence
field = OccField

bound :: String -> Occurrence -> { name :: Ident, occurrence :: Occurrence }
bound name occurrence = { name: Ident name, occurrence }

-- | The plan a matrix of the width given compiles to.
planned :: Int -> Array { alternative :: Int, choice :: Maybe String, patterns :: Array (Pattern String) } -> (Plan -> Compiled String -> Aff Unit) -> Aff Unit
planned width rows k = case compile table width rows of
  Right compiled -> k compiled.plan compiled
  Left err -> fail (show err)

spec :: Spec Unit
spec = describe "Elaborate.Surface.Match" do
  describe "the domain of a column" do
    it "of a constructor is its data type's constructors, in the order of their tags" do
      coverageDomain table (HeadConstructor green) `shouldEqual`
        Just (Constructors [ { name: red, arity: 0 }, { name: green, arity: 0 }, { name: blue, arity: 0 } ])
      coverageDomain table (HeadConstructor unitCtor) `shouldEqual` Just (Constructors [ { name: unitCtor, arity: 0 } ])

    it "of a `Boolean` is its two literals, `false` first, and of any other literal open" do
      coverageDomain table (HeadLiteral (LitBoolean true)) `shouldEqual` Just (Literals [ LitBoolean false, LitBoolean true ])
      coverageDomain table (HeadLiteral (LitInt 0)) `shouldEqual` Just Open

    it "of a constructor the table does not hold is none" do
      coverageDomain table (HeadConstructor (ctor "Nope")) `shouldEqual` Nothing

  describe "a plan" do
    it "dispatches on a data type its alternatives exhaust with no default, binding a field where a leaf takes it" do
      planned 1 [ row 0 [ c none [] ], row 1 [ c some [ v "x" ] ] ] \plan compiled -> do
        plan `shouldEqual`
          SwitchCtor (s 0)
            [ { ctor: none, plan: Leaf 0 [] }
            , { ctor: some, plan: Leaf 1 [ bound "x" (field (s 0) some 0) ] }
            ]
            Nothing
        compiled.references `shouldEqual` Map.fromFoldable [ Tuple 0 1, Tuple 1 1 ]
        compiled.redundant `shouldEqual` { alternatives: [], choices: [] }

    it "exhausts `Prim.Unit` by its one constructor" do
      planned 1 [ row 0 [ c unitCtor [] ] ] \plan _ ->
        plan `shouldEqual` SwitchCtor (s 0) [ { ctor: unitCtor, plan: Leaf 0 [] } ] Nothing

    it "dispatches on the `Boolean` its alternatives exhaust with the last of its literals the default" do
      planned 1 [ row 0 [ bool true ], row 1 [ bool false ] ] \plan _ ->
        plan `shouldEqual` SwitchLit (s 0) [ { lit: LitBoolean false, plan: Leaf 1 [] } ] (Leaf 0 [])

    it "dispatches on an open domain with a default, and leaves what no row covers uncovered" do
      planned 1 [ row 0 [ int 1 ], row 1 [ int 0 ] ] \plan _ ->
        plan `shouldEqual` SwitchLit (s 0) [ { lit: LitInt 0, plan: Leaf 1 [] }, { lit: LitInt 1, plan: Leaf 0 [] } ] Uncovered
      planned 1 [ row 0 [ int 0 ], row 1 [ v "n" ] ] \plan _ ->
        plan `shouldEqual` SwitchLit (s 0) [ { lit: LitInt 0, plan: Leaf 0 [] } ] (Leaf 1 [ bound "n" (s 0) ])

    it "binds an as-pattern's variable and what its pattern binds" do
      planned 1 [ row 0 [ PAs (Ident "o") (c some [ v "x" ]) ], row 1 [ PAny ] ] \plan _ ->
        plan `shouldEqual`
          SwitchCtor (s 0)
            [ { ctor: some, plan: Leaf 0 [ bound "o" (s 0), bound "x" (field (s 0) some 0) ] } ]
            (Just (Leaf 1 []))

    it "takes the column the most leading rows need first, then the one of fewest branches, then the one whose constructors take fewest fields" do
      -- the second column is needed by two leading rows, the first by one
      planned 2 [ row 0 [ c red [], c none [] ], row 1 [ PAny, c some [ PAny ] ] ] \plan _ ->
        plan `shouldEqual`
          SwitchCtor (s 1)
            [ { ctor: none, plan: SwitchCtor (s 0) [ { ctor: red, plan: Leaf 0 [] } ] (Just Uncovered) }
            , { ctor: some, plan: Leaf 1 [] }
            ]
            Nothing
      -- `Unit` exhausted is one branch, `Red` with a default two
      planned 2 [ row 0 [ c red [], c unitCtor [] ], row 1 [ PAny, PAny ] ] \plan _ ->
        plan `shouldEqual`
          SwitchCtor (s 1)
            [ { ctor: unitCtor, plan: SwitchCtor (s 0) [ { ctor: red, plan: Leaf 0 [] } ] (Just (Leaf 1 [])) } ]
            Nothing
      -- `Some` and `Red` are two branches each, and `Red` takes no field
      planned 2 [ row 0 [ c some [ PAny ], c red [] ], row 1 [ PAny, PAny ] ] \plan _ ->
        plan `shouldEqual`
          SwitchCtor (s 1)
            [ { ctor: red, plan: SwitchCtor (s 0) [ { ctor: some, plan: Leaf 0 [] } ] (Just (Leaf 1 [])) } ]
            (Just (Leaf 1 []))

    it "takes the leftmost column where nothing else tells two apart" do
      planned 2 [ row 0 [ c red [], c green [] ], row 1 [ PAny, PAny ] ] \plan _ ->
        plan `shouldEqual`
          SwitchCtor (s 0)
            [ { ctor: red, plan: SwitchCtor (s 1) [ { ctor: green, plan: Leaf 0 [] } ] (Just (Leaf 1 [])) } ]
            (Just (Leaf 1 []))

  describe "the leaves of an alternative" do
    it "are counted, one taken by several leaves and one by none" do
      planned 2 [ row 0 [ c red [], bool true ], row 1 [ PAny, PAny ], row 2 [ c blue [], PAny ] ] \_ compiled -> do
        compiled.references `shouldEqual` Map.fromFoldable [ Tuple 0 1, Tuple 1 3 ]
        compiled.redundant.alternatives `shouldEqual` [ 2 ]

    it "are counted over the choices of an or-pattern, one leaf per choice" do
      planned 1 [ row 0 [ or [ Tuple "red" (c red []), Tuple "blue" (c blue []) ] ], row 1 [ c green [] ] ] \plan compiled -> do
        plan `shouldEqual`
          SwitchCtor (s 0) [ { ctor: red, plan: Leaf 0 [] }, { ctor: green, plan: Leaf 1 [] }, { ctor: blue, plan: Leaf 0 [] } ] Nothing
        compiled.references `shouldEqual` Map.fromFoldable [ Tuple 0 2, Tuple 1 1 ]

  describe "what no value reaches" do
    it "is a choice of an or-pattern no leaf takes, where its alternative is taken" do
      planned 1
        [ row 0 [ or [ Tuple "red" (c red []), Tuple "green" (c green []) ] ]
        , row 1 [ or [ Tuple "green again" (c green []), Tuple "blue" (c blue []) ] ]
        ]
        \_ compiled -> compiled.redundant `shouldEqual` { alternatives: [], choices: [ "green again" ] }

    it "is a choice written at the top of an alternative no leaf takes" do
      planned 1 [ choice 0 "first" [ c red [] ], choice 0 "again" [ c red [] ], row 1 [ PAny ] ] \_ compiled ->
        compiled.redundant `shouldEqual` { alternatives: [], choices: [ "again" ] }

    it "is an alternative no leaf takes, its choices not named apart" do
      planned 1 [ row 0 [ PAny ], row 1 [ or [ Tuple "red" (c red []), Tuple "nested" (c some [ or [ Tuple "zero" (int 0) ] ]) ] ] ] \_ compiled ->
        compiled.redundant `shouldEqual` { alternatives: [ 1 ], choices: [] }

  describe "a matrix no typing admits" do
    it "is refused, not compiled" do
      map _.plan (compile table 1 [ row 0 [ c red [] ], row 1 [ c none [] ] ]) `shouldEqual` Left (IncompatibleHeads (s 0))
      map _.plan (compile table 1 [ row 0 [ int 0 ], row 1 [ c none [] ] ]) `shouldEqual` Left (IncompatibleHeads (s 0))
      map _.plan (compile table 1 [ row 0 [ c (ctor "Nope") [] ] ]) `shouldEqual` Left (UnknownConstructor (s 0) (ctor "Nope"))
      map _.plan (compile table 1 [ row 0 [ c some [] ] ]) `shouldEqual` Left (ArityMismatch (s 0) some)

  describe "a witness" do
    it "is none where every value is matched" do
      witness table 1 [ row 0 [ c none [] ], row 1 [ c some [ PAny ] ] ] `shouldEqual` Right Nothing
      witness table 1 [ row 0 [ bool false ], row 1 [ bool true ] ] `shouldEqual` Right Nothing

    it "is the first constructor in declaration order that is not matched, and `_` for the rest of an open domain" do
      witness table 1 [ row 0 [ c green [] ] ] `shouldEqual` Right (Just [ WitnessConstructor red [] ])
      witness table 1 [ row 0 [ int 0 ] ] `shouldEqual` Right (Just [ WitnessAny ])
      witness table 1 [ row 0 [ c some [ int 0 ] ], row 1 [ c none [] ] ] `shouldEqual` Right (Just [ WitnessConstructor some [ WitnessAny ] ])

    it "reads the leftmost column first, and `false` before `true`" do
      witness table 2 [ row 0 [ c none [], PAny ], row 1 [ PAny, bool true ] ] `shouldEqual`
        Right (Just [ WitnessConstructor some [ WitnessAny ], WitnessLiteral (LitBoolean false) ])
      witness table 2 [ row 0 [ int 0, bool true ] ] `shouldEqual`
        Right (Just [ WitnessLiteral (LitInt 0), WitnessLiteral (LitBoolean false) ])

    it "takes an or-pattern's choices and a variable as what they match" do
      witness table 2 [ row 0 [ or [ Tuple "a" (c red []), Tuple "b" (c green []) ], v "x" ] ] `shouldEqual`
        Right (Just [ WitnessConstructor blue [], WitnessAny ])
      witness table 1 [ row 0 [ or [ Tuple "a" (c red []), Tuple "b" (c green []) ] ] ] `shouldEqual` Right (Just [ WitnessConstructor blue [] ])
