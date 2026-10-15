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
import Prim hiding (Row)

import Data.Array as Array
import Data.Either (Either(..))
import Data.Map as Map
import Data.Maybe (Maybe(..), maybe)
import Data.Tuple (Tuple(..))
import Effect.Aff (Aff)
import Stella.Compiler.Elaborate.Surface.Match (Binding, Compiled, Domain(..), Head(..), MatchError(..), Pattern(..), Plan(..), Row, Tags, Tail(..), Transform(..), Witness(..), closable, compile, coverageDomain, witness)
import Stella.Compiler.TypedCore.Name (Ident(..), ModuleName(..), Qualified(..), Symbol(..), Tag(..), TyName(..))
import Stella.Compiler.TypedCore.Prim (unitCtor, unitTy)
import Stella.Compiler.TypedCore.Term (Literal(..), Occurrence(..))
import Stella.Compiler.TypedCore.Type (RowKey(..))
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
row :: Int -> Array (Pattern String String) -> Row String String
row alternative patterns = { alternative, choice: Nothing, patterns, fallible: false }

-- | A row of the alternative given, written as the choice labelled.
choice :: Int -> String -> Array (Pattern String String) -> Row String String
choice alternative label patterns = { alternative, choice: Just label, patterns, fallible: false }

-- | A row of the alternative given whose guard block may fall through.
fallible :: Int -> Array (Pattern String String) -> Row String String
fallible alternative patterns = { alternative, choice: Nothing, patterns, fallible: true }

c :: Qualified Ident -> Array (Pattern String String) -> Pattern String String
c = PCtor

v :: String -> Pattern String String
v = PVar <<< Ident

int :: Int -> Pattern String String
int = PLit <<< LitInt

bool :: Boolean -> Pattern String String
bool = PLit <<< LitBoolean

or :: Array (Tuple String (Pattern String String)) -> Pattern String String
or choices = POr (map (\(Tuple label pattern) -> { label, pattern }) choices)

s :: Int -> Occurrence
s = OccScrutinee

field :: Occurrence -> Qualified Ident -> Int -> Occurrence
field = OccField

bound :: String -> Occurrence -> Binding String
bound name occurrence = { name: Ident name, occurrence, transform: Identity }

-- | The rest of a record bound to a variable: the record at the occurrence
-- | given without the keys given.
restOf :: String -> Occurrence -> Array String -> Binding String
restOf name occurrence keys = { name: Ident name, occurrence, transform: Restrict (map keyOf keys) }

keyOf :: String -> RowKey
keyOf = SymbolKey <<< Symbol

-- | A closed record pattern, its fields in the order given.
closed :: Array (Tuple String (Pattern String String)) -> Pattern String String
closed fields = PRecord { fields: map (\(Tuple k p) -> { key: keyOf k, pattern: p }) fields, rest: Nothing, open: false }

-- | An open record pattern, binding its rest where a name is given.
opened :: Array (Tuple String (Pattern String String)) -> Maybe String -> Pattern String String
opened fields rest = PRecord { fields: map (\(Tuple k p) -> { key: keyOf k, pattern: p }) fields, rest: map Ident rest, open: true }

tuple :: Array (Pattern String String) -> Pattern String String
tuple parts = PRecord { fields: Array.mapWithIndex (\i p -> { key: PositionKey i, pattern: p }) parts, rest: Nothing, open: false }

at :: Occurrence -> String -> Occurrence
at o k = OccRecordField o (keyOf k)

position :: Occurrence -> Int -> Occurrence
position o i = OccRecordField o (PositionKey i)

tagOf :: String -> RowKey
tagOf = TagKey <<< Tag

-- | The tags `'A` and `'B`, their payloads at `a` and `b`, and the tail given.
ab :: Tail String -> Tags String
ab tail = { keys: [ { key: tagOf "A", payload: "a" }, { key: tagOf "B", payload: "b" } ], tail }

tag :: Tags String -> String -> Pattern String String -> Pattern String String
tag domain name payload = PTag { key: tagOf name, payload, domain }

payloadAt :: Occurrence -> String -> Occurrence
payloadAt o name = OccVariantPayload o (tagOf name)

-- | A variable bound to the variant at the occurrence given, widened by the
-- | tags given, each with its payload's type.
widened :: String -> Occurrence -> Array (Tuple String String) -> Binding String
widened name occurrence tags = { name: Ident name, occurrence, transform: Weaken (map (\(Tuple k p) -> { key: tagOf k, payload: p }) tags) }

-- | Every variable a leaf of a plan binds.
bindingsOf :: Plan String -> Array (Binding String)
bindingsOf = case _ of
  Leaf _ bindings -> bindings
  Uncovered -> []
  SwitchCtor _ branches fallback -> Array.concatMap (bindingsOf <<< _.plan) branches <> maybe [] bindingsOf fallback
  SwitchLit _ branches fallback -> Array.concatMap (bindingsOf <<< _.plan) branches <> bindingsOf fallback
  SwitchKey _ _ branches fallback -> Array.concatMap (bindingsOf <<< _.plan) branches <> maybe [] bindingsOf fallback

-- | The domain of the column a constructor or a literal stands in.
domainOf :: Head -> Maybe (Domain String)
domainOf = coverageDomain table

-- | The plan a matrix of the width given compiles to.
planned :: Int -> Array (Row String String) -> (Plan String -> Compiled String String -> Aff Unit) -> Aff Unit
planned width rows k = case compile table width rows of
  Right compiled -> k compiled.plan compiled
  Left err -> fail (show err)

spec :: Spec Unit
spec = describe "Elaborate.Surface.Match" do
  describe "the domain of a column" do
    it "of a constructor is its data type's constructors, in the order of their tags" do
      domainOf (HeadConstructor green) `shouldEqual`
        Just (Constructors [ { name: red, arity: 0 }, { name: green, arity: 0 }, { name: blue, arity: 0 } ])
      domainOf (HeadConstructor unitCtor) `shouldEqual` Just (Constructors [ { name: unitCtor, arity: 0 } ])

    it "of a `Boolean` is its two literals, `false` first, and of any other literal open" do
      domainOf (HeadLiteral (LitBoolean true)) `shouldEqual` Just (Literals [ LitBoolean false, LitBoolean true ])
      domainOf (HeadLiteral (LitInt 0)) `shouldEqual` Just Open

    it "of a constructor the table does not hold is none" do
      domainOf (HeadConstructor (ctor "Nope")) `shouldEqual` Nothing

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

  describe "an alternative that may fail" do
    it "is taken where its patterns match, and where it fails the alternatives after it are matched afresh" do
      planned 1 [ fallible 0 [ c some [ v "x" ] ], row 1 [ c none [] ], row 2 [ PAny ] ] \plan compiled -> do
        plan `shouldEqual`
          SwitchCtor (s 0)
            [ { ctor: none, plan: Leaf 1 [] }, { ctor: some, plan: Leaf 0 [ bound "x" (field (s 0) some 0) ] } ]
            Nothing
        compiled.falls `shouldEqual` Map.singleton 0 (SwitchCtor (s 0) [ { ctor: none, plan: Leaf 1 [] } ] (Just (Leaf 2 [])))
        compiled.references `shouldEqual` Map.fromFoldable [ Tuple 0 1, Tuple 1 2, Tuple 2 1 ]
        compiled.redundant `shouldEqual` { alternatives: [], choices: [] }

    it "covers nothing the rows after it would otherwise take" do
      planned 1 [ row 0 [ c some [ v "x" ] ], row 1 [ c none [] ], row 2 [ PAny ] ] \_ compiled ->
        compiled.redundant.alternatives `shouldEqual` [ 2 ]
      planned 1 [ fallible 0 [ PAny ], fallible 1 [ PAny ], row 2 [ PAny ] ] \plan compiled -> do
        plan `shouldEqual` Leaf 0 []
        compiled.falls `shouldEqual` Map.fromFoldable [ Tuple 0 (Leaf 1 []), Tuple 1 (Leaf 2 []) ]
        compiled.references `shouldEqual` Map.fromFoldable [ Tuple 0 1, Tuple 1 1, Tuple 2 1 ]

    it "that no leaf takes falls through to no plan, nor makes the alternatives after it reachable" do
      planned 1 [ row 0 [ PAny ], fallible 1 [ c some [ v "x" ] ], row 2 [ c none [] ] ] \_ compiled -> do
        compiled.falls `shouldEqual` Map.empty
        compiled.redundant.alternatives `shouldEqual` [ 1, 2 ]

    it "leaves uncovered what it would have matched, where nothing after it does, and a witness passes over it" do
      planned 1 [ fallible 0 [ PAny ] ] \plan compiled -> do
        plan `shouldEqual` Leaf 0 []
        compiled.falls `shouldEqual` Map.singleton 0 Uncovered
      witness table 1 [ fallible 0 [ PAny ] ] `shouldEqual` Right (Just [ WitnessAny ])
      witness table 1 [ fallible 0 [ c some [ v "x" ] ], row 1 [ c none [] ] ] `shouldEqual` Right (Just [ WitnessConstructor some [ WitnessAny ] ])
      witness table 1 [ fallible 0 [ c some [ v "x" ] ], row 1 [ PAny ] ] `shouldEqual` Right Nothing

  describe "a matrix no typing admits" do
    it "is refused, not compiled" do
      map _.plan (compile table 1 [ row 0 [ c red [] ], row 1 [ c none [] ] ]) `shouldEqual` Left (IncompatibleHeads (s 0))
      map _.plan (compile table 1 [ row 0 [ int 0 ], row 1 [ c none [] ] ]) `shouldEqual` Left (IncompatibleHeads (s 0))
      map _.plan (compile table 1 [ row 0 [ c (ctor "Nope") [] ] ]) `shouldEqual` Left (UnknownConstructor (s 0) (ctor "Nope"))
      map _.plan (compile table 1 [ row 0 [ c some [] ] ]) `shouldEqual` Left (ArityMismatch (s 0) some)
      map _.plan (compile table 1 [ row 0 [ closed [ Tuple "x" PAny ] ], row 1 [ c none [] ] ]) `shouldEqual` Left (IncompatibleHeads (s 0))

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

  describe "a record or a tuple pattern" do
    it "is taken apart without a dispatch, a column for each key in the order the rows first write them" do
      planned 1 [ row 0 [ opened [ Tuple "x" (c none []) ] Nothing ], row 1 [ opened [ Tuple "y" (v "b"), Tuple "x" (v "a") ] Nothing ] ] \plan compiled -> do
        plan `shouldEqual`
          SwitchCtor (at (s 0) "x")
            [ { ctor: none, plan: Leaf 0 [] } ]
            (Just (Leaf 1 [ bound "a" (at (s 0) "x"), bound "b" (at (s 0) "y") ]))
        compiled.references `shouldEqual` Map.fromFoldable [ Tuple 0 1, Tuple 1 1 ]

    it "leaves nothing uncovered where every component matches anything" do
      planned 1 [ row 0 [ tuple [ v "a", v "b" ] ] ] \plan _ ->
        plan `shouldEqual` Leaf 0 [ bound "a" (position (s 0) 0), bound "b" (position (s 0) 1) ]
      planned 2 [ row 0 [ PAny, closed [ Tuple "x" (tuple [ PAny, v "c" ]) ] ] ] \plan _ ->
        plan `shouldEqual` Leaf 0 [ bound "c" (position (at (s 1) "x") 1) ]

    it "that writes no key takes its column apart into none" do
      planned 1 [ row 0 [ closed [] ] ] \plan _ -> plan `shouldEqual` Leaf 0 []
      planned 1 [ row 0 [ opened [] Nothing ] ] \plan _ -> plan `shouldEqual` Leaf 0 []
      planned 1 [ row 0 [ opened [] (Just "r") ] ] \plan _ -> plan `shouldEqual` Leaf 0 [ restOf "r" (s 0) [] ]

    it "binds its rest to the record without the keys it writes, in the order written, and not every key its column is taken apart into" do
      planned 1 [ row 0 [ opened [ Tuple "x" (c none []) ] (Just "r") ], row 1 [ opened [ Tuple "y" (v "b"), Tuple "x" PAny ] (Just "q") ] ] \plan _ ->
        plan `shouldEqual`
          SwitchCtor (at (s 0) "x")
            [ { ctor: none, plan: Leaf 0 [ restOf "r" (s 0) [ "x" ] ] } ]
            (Just (Leaf 1 [ restOf "q" (s 0) [ "y", "x" ], bound "b" (at (s 0) "y") ]))

    it "is shown in a witness by what each key holds, in the order of the keys, a tuple by position" do
      witness table 1 [ row 0 [ tuple [ bool true, PAny ] ] ] `shouldEqual`
        Right (Just [ WitnessRecord { fields: [ { key: PositionKey 0, witness: WitnessLiteral (LitBoolean false) }, { key: PositionKey 1, witness: WitnessAny } ], open: false } ])
      witness table 1 [ row 0 [ closed [ Tuple "y" (c none []), Tuple "x" PAny ] ] ] `shouldEqual`
        Right (Just [ WitnessRecord { fields: [ { key: keyOf "x", witness: WitnessAny }, { key: keyOf "y", witness: WitnessConstructor some [ WitnessAny ] } ], open: false } ])

    it "is shown open in a witness where no row closes it" do
      witness table 1 [ row 0 [ opened [ Tuple "x" (c none []) ] Nothing ] ] `shouldEqual`
        Right (Just [ WitnessRecord { fields: [ { key: keyOf "x", witness: WitnessConstructor some [ WitnessAny ] } ], open: true } ])
      witness table 1 [ row 0 [ opened [ Tuple "x" (c none []) ] Nothing ], row 1 [ closed [ Tuple "x" (c some [ int 0 ]) ] ] ] `shouldEqual`
        Right (Just [ WitnessRecord { fields: [ { key: keyOf "x", witness: WitnessConstructor some [ WitnessAny ] } ], open: false } ])
      witness table 1 [ row 0 [ opened [ Tuple "x" PAny ] Nothing ] ] `shouldEqual` Right Nothing

  describe "a tag pattern" do
    it "dispatches on the tags of a closed row with no default where every tag is taken" do
      planned 1 [ row 0 [ tag (ab Closed) "A" (v "x") ], row 1 [ tag (ab Closed) "B" PAny ] ] \plan compiled -> do
        plan `shouldEqual`
          SwitchKey (s 0) Closed
            [ { key: tagOf "A", plan: Leaf 0 [ bound "x" (payloadAt (s 0) "A") ] }, { key: tagOf "B", plan: Leaf 1 [] } ]
            Nothing
        compiled.references `shouldEqual` Map.fromFoldable [ Tuple 0 1, Tuple 1 1 ]

    it "has a default where a tag is not taken, or the row holds more than its tags" do
      planned 1 [ row 0 [ tag (ab Closed) "A" PAny ] ] \plan _ ->
        plan `shouldEqual` SwitchKey (s 0) Closed [ { key: tagOf "A", plan: Leaf 0 [] } ] (Just Uncovered)
      planned 1 [ row 0 [ tag (ab Rigid) "A" PAny ], row 1 [ tag (ab Rigid) "B" PAny ] ] \plan _ ->
        plan `shouldEqual`
          SwitchKey (s 0) Rigid [ { key: tagOf "A", plan: Leaf 0 [] }, { key: tagOf "B", plan: Leaf 1 [] } ] (Just Uncovered)

    it "takes each tag an or-pattern chooses" do
      planned 1 [ row 0 [ or [ Tuple "a" (tag (ab Closed) "A" PAny), Tuple "b" (tag (ab Closed) "B" PAny) ] ] ] \plan _ ->
        plan `shouldEqual`
          SwitchKey (s 0) Closed [ { key: tagOf "A", plan: Leaf 0 [] }, { key: tagOf "B", plan: Leaf 0 [] } ] Nothing

    it "widens a variable a default binds by the tags taken, in the order taken, and none a branch binds" do
      planned 1 [ row 0 [ tag (ab Rigid) "A" PAny ], row 1 [ tag (ab Rigid) "B" PAny ], row 2 [ v "x" ] ] \plan _ ->
        plan `shouldEqual`
          SwitchKey (s 0) Rigid
            [ { key: tagOf "A", plan: Leaf 0 [] }, { key: tagOf "B", plan: Leaf 1 [] } ]
            (Just (Leaf 2 [ widened "x" (s 0) [ Tuple "A" "a", Tuple "B" "b" ] ]))
      planned 1 [ row 0 [ PAs (Ident "y") (tag (ab Rigid) "A" PAny) ], row 1 [ v "x" ] ] \plan _ ->
        plan `shouldEqual`
          SwitchKey (s 0) Rigid
            [ { key: tagOf "A", plan: Leaf 0 [ bound "y" (s 0) ] } ]
            (Just (Leaf 1 [ widened "x" (s 0) [ Tuple "A" "a" ] ]))

    it "widens by the payload its occurrence's domain gives a tag, not by the tag alone" do
      let
        ofInt = { keys: [ { key: tagOf "A", payload: "Int" } ], tail: Rigid }
        ofString = { keys: [ { key: tagOf "A", payload: "String" } ], tail: Rigid }
      planned 2 [ row 0 [ tag ofInt "A" PAny, tag ofString "A" PAny ], row 1 [ v "x", v "y" ] ] \plan _ -> do
        Array.elem (widened "x" (s 0) [ Tuple "A" "Int" ]) (bindingsOf plan) `shouldEqual` true
        Array.elem (widened "y" (s 1) [ Tuple "A" "String" ]) (bindingsOf plan) `shouldEqual` true

    it "is refused where the tag patterns of one column carry different domains, or its domain does not hold its tag" do
      map _.plan (compile table 1 [ row 0 [ tag (ab Closed) "A" PAny ], row 1 [ tag (ab Rigid) "B" PAny ] ]) `shouldEqual` Left (DomainMismatch (s 0))
      map _.plan (compile table 1 [ row 0 [ tag (ab Closed) "C" PAny ] ]) `shouldEqual` Left (UnknownTag (s 0) (tagOf "C"))
      map _.plan (compile table 1 [ row 0 [ tag (ab Closed) "A" PAny ], row 1 [ c none [] ] ]) `shouldEqual` Left (IncompatibleHeads (s 0))

    it "is shown in a witness by the first tag not matched, with its payload's type, and `_` for the rest of an open row" do
      witness table 1 [ row 0 [ tag (ab Closed) "A" PAny ] ] `shouldEqual` Right (Just [ WitnessTag (tagOf "B") WitnessAny "b" ])
      witness table 1 [ row 0 [ tag (ab Closed) "A" (c none []) ], row 1 [ tag (ab Closed) "B" PAny ] ] `shouldEqual`
        Right (Just [ WitnessTag (tagOf "A") (WitnessConstructor some [ WitnessAny ]) "a" ])
      witness table 1 [ row 0 [ tag (ab Rigid) "A" PAny ], row 1 [ tag (ab Rigid) "B" PAny ] ] `shouldEqual` Right (Just [ WitnessAny ])
      witness table 1 [ row 0 [ tag (ab Closed) "A" PAny ], row 1 [ tag (ab Closed) "B" PAny ] ] `shouldEqual` Right Nothing

  describe "the tails a match may close" do
    let
      open = ab (Flexible [ "?r" ])
      closableOf rows = map closable (compile table 1 rows)
    it "are the metavariables of a variant whose default leaves values uncovered" do
      closableOf [ row 0 [ tag open "A" PAny ], row 1 [ tag open "B" PAny ] ] `shouldEqual` Right [ "?r" ]
      witness table 1 [ row 0 [ tag open "A" PAny ], row 1 [ tag open "B" PAny ] ] `shouldEqual` Right (Just [ WitnessAny ])

    it "are none where a default takes what the row may hold besides" do
      closableOf [ row 0 [ tag open "A" PAny ], row 1 [ PAny ] ] `shouldEqual` Right []

    it "follow a default past a guard block that may fall through" do
      closableOf [ row 0 [ tag open "A" PAny ], fallible 1 [ PAny ] ] `shouldEqual` Right [ "?r" ]

    it "are none where the row is closed, open by a variable a quantifier binds, or open by a metavariable of an outer level" do
      closableOf [ row 0 [ tag (ab Closed) "A" PAny ] ] `shouldEqual` Right []
      closableOf [ row 0 [ tag (ab Rigid) "A" PAny ] ] `shouldEqual` Right []
      closableOf [ row 0 [ tag (ab External) "A" PAny ] ] `shouldEqual` Right []
      witness table 1 [ row 0 [ tag (ab External) "A" PAny ], row 1 [ tag (ab External) "B" PAny ] ] `shouldEqual` Right (Just [ WitnessAny ])

    it "show a tag the row has come to hold that no row takes" do
      let grown = { keys: [ { key: tagOf "A", payload: "a" }, { key: tagOf "B", payload: "b" }, { key: tagOf "C", payload: "c" } ], tail: Flexible [ "?r" ] }
      closableOf [ row 0 [ tag grown "A" PAny ], row 1 [ tag grown "B" PAny ] ] `shouldEqual` Right [ "?r" ]
      witness table 1 [ row 0 [ tag grown "A" PAny ], row 1 [ tag grown "B" PAny ] ] `shouldEqual` Right (Just [ WitnessTag (tagOf "C") WitnessAny "c" ])

    it "are found where the variant stands in a constructor's field" do
      closableOf [ row 0 [ c some [ tag open "A" PAny ] ], row 1 [ c none [] ] ] `shouldEqual` Right [ "?r" ]
