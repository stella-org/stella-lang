-- | The grammar, one form at a time, shown by the sketch of what it builds.
module Test.Stella.Compiler.CST.Parser (spec) where

import Prelude

import Data.Either (Either(..))
import Data.String (joinWith)
import Effect.Aff (Aff)
import Stella.Compiler.CST (parseExpr, parseModule, parseType, printSyntaxError)
import Stella.Compiler.CST.Types (Module(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)
import Test.Stella.Compiler.CST.Sketch (sketchExpr, sketchItem, sketchType)

typeIs :: String -> String -> Aff Unit
typeIs src expected = case parseType src of
  Left e -> fail (printSyntaxError e)
  Right t -> sketchType t `shouldEqual` expected

exprIs :: String -> String -> Aff Unit
exprIs src expected = case parseExpr src of
  Left e -> fail (printSyntaxError e)
  Right e -> sketchExpr e `shouldEqual` expected

-- | The items of a module whose body is the lines given.
itemsAre :: Array String -> Array String -> Aff Unit
itemsAre body expected = case parseModule (joinWith "\n" ([ "module M where" ] <> body)) of
  Left e -> fail (printSyntaxError e)
  Right (Module m) -> map sketchItem m.items `shouldEqual` expected

typeRejected :: String -> Aff Unit
typeRejected src = case parseType src of
  Left _ -> pure unit
  Right t -> fail ("accepted: " <> sketchType t)

exprRejected :: String -> Aff Unit
exprRejected src = case parseExpr src of
  Left _ -> pure unit
  Right e -> fail ("accepted: " <> sketchExpr e)

rejects :: Array String -> Aff Unit
rejects body = case parseModule (joinWith "\n" ([ "module M where" ] <> body)) of
  Left _ -> pure unit
  Right (Module m) -> fail ("accepted: " <> joinWith " " (map sketchItem m.items))

spec :: Spec Unit
spec = describe "Stella.Compiler.CST.Parser" do
  describe "types" do
    it "reads arrows, application and quantifiers" do
      "forall a. Array a -> Int" `typeIs` "(forall a (-> (Array a) Int))"
      "forall a b (e :: Row Effect). (a -> b) -> a" `typeIs`
        "(forall a b (:: e (Row Effect)) (-> (parens (-> a b)) a))"
    it "attaches `/` to the last arrow of a chain" do
      "Int -> String -> Unit / {| Console |}" `typeIs` "(-> Int (-> String (/ Unit (effects Console))))"
    it "reads a computation type" do
      "Int / {| Random |}" `typeIs` "(/ Int (effects Random))"
      "(String -> Int) / {| Config |}" `typeIs` "(/ (parens (-> String Int)) (effects Config))"
    it "reads constraints" do
      "forall a. Show a => a -> String" `typeIs` "(forall a (=> (Show a) (-> a String)))"
    it "reads records, tuples, variants and effect rows" do
      "{ name :: String, ...r }" `typeIs` "(record name::String ...r)"
      "(Int, String)" `typeIs` "(tuple Int String)"
      "()" `typeIs` "()"
      "[ 'Ok :: Int, 'Err :: String ]" `typeIs` "(variant 'Ok::Int 'Err::String)"
      "[]" `typeIs` "(variant)"
      "Unit -> Int / {| cache :: State Int, ... |}" `typeIs` "(-> Unit (/ Int (effects cache::(State Int) ...)))"
    it "reads a record field named by a keyword" do
      "{ type :: String, where :: Int }" `typeIs` "(record type::String where::Int)"
    it "reads a kind annotation" do
      "Proxy (Maybe :: Type -> Type)" `typeIs` "(Proxy (:: Maybe (-> Type Type)))"
    it "reads the shape of a capability translation" do
      "Console ~> ( LiftIO )" `typeIs` "(~> Console (parens LiftIO))"
    it "reads a synthesized argument" do
      "{{ dict :: Show a by Typeclass.resolve }} -> a -> String" `typeIs`
        "(-> (synth dict (Show a) by Typeclass.resolve) (-> a String))"
    it "reads a directive on a type" do
      "(#unbox Int)" `typeIs` "((#unbox) Int)"
    it "reads `->*` wherever an arrow may stand, for a later check" do
      "Int -> String ->* Unit" `typeIs` "(-> Int (->* String Unit))"
    it "refuses `by` as a type variable, bound or used" do
      typeRejected "forall by. Int"
      typeRejected "forall (by :: Type). Int"
      rejects [ "data T by = T" ]

  describe "expressions" do
    it "reads operators in the order written" do
      "a + b * c" `exprIs` "(* (+ a b) c)"
      "n `rem` 3 == 0" `exprIs` "(== (`rem` n 3) 0)"
    it "reads application, negative literals and field access" do
      "f -1 x.name" `exprIs` "((f -1) (. x name))"
    it "reads lambdas, which extend to the right" do
      "\\x y -> x + y" `exprIs` "(\\ x y (+ x y))"
      "map \\x -> x" `exprIs` "(map (\\ x x))"
    it "reads let blocks" do
      "let x = 1 in x + 1" `exprIs` "(let (= x 1) (+ x 1))"
      "let\n  f x = x\n  (a, b) = t\nin f a" `exprIs` "(let (= f x x) (= (tuple a b) t) (f a))"
    it "reads records with puns, updates and a spread" do
      "{ name: \"Stella\", age }" `exprIs` "(record name:\"Stella\" age)"
      "{ x = 42, y: 1, ...rec }" `exprIs` "(record x=42 y:1 ...rec)"
      "{ ...rec }" `exprIs` "(record ...rec)"
    it "refuses a spread other than one standing last" do
      exprRejected "{ ...a, x: 1 }"
      exprRejected "{ x: 1, ...a, ...b }"
    it "reads tuples, unit, arrays and tags" do
      "(1, \"one\")" `exprIs` "(tuple 1 \"one\")"
      "()" `exprIs` "()"
      "[1, 2]" `exprIs` "(array 1 2)"
      "'Ok 42" `exprIs` "('Ok 42)"
    it "reads discriminators, holes and operators as values" do
      "filter Just? xs" `exprIs` "((filter Just?) xs)"
      "?todo" `exprIs` "?todo"
      "(+)" `exprIs` "(+)"
    it "reads a section" do
      "(_ + 1)" `exprIs` "(parens (+ _ 1))"
    it "reads a local open and an import" do
      "DA.( length xs + 1 )" `exprIs` "(open DA (+ (length xs) 1))"
      "import DA in length xs" `exprIs` "(import-in DA (length xs))"
    it "reads a type annotation" do
      "(xs :: Array Int)" `exprIs` "(parens (:: xs (Array Int)))"
    it "reads a labelled operation and cells" do
      "get@cache ()" `exprIs` "(get@cache ())"
      "let v = n! in n := v + 1" `exprIs` "(let (= v n!) (:= n (+ v 1)))"
    it "reads macro calls" do
      "format%\"Hello {world}\"" `exprIs` "(format% \"Hello {world}\")"
      "if%{ c then a else b }" `exprIs` "(if% { c then a else b })"

  describe "case" do
    it "reads alternatives and several scrutinees" do
      "case _, _ of\n  _, Just a -> a\n  a, _ -> a" `exprIs`
        "(case _ _ (_, (Just a) a) (a, _ a))"
    it "reads or-patterns, weaker than commas" do
      "case r of\n  SuperUser | Admin -> 1\n  Guest -> 0" `exprIs`
        "(case r (SuperUser | Admin 1) (Guest 0))"
      "case p of\n  A, (B | C) -> 1" `exprIs` "(case p (A, (parens (or B C)) 1))"
    it "keeps an as-pattern on the left of a guard block's binding" do
      "case _ of\n  n where\n      m@(Just y) = f n\n      x@z = g n\n      m -> y" `exprIs`
        "(case _ (n (= m@(parens (Just y)) (f n)) (= x@z (g n)) (? m y)))"
    it "reads a guard block" do
      "case _ of\n  n where\n      m = n `rem` 3 == 0\n      m -> \"Fizz\"\n      otherwise -> \"\"\n  n -> n" `exprIs`
        "(case _ (n (= m (== (`rem` n 3) 0)) (? m \"Fizz\") (? otherwise \"\")) (n n))"
    it "reads as-patterns, records, tuples and tags" do
      "case m of\n  mb@(Just _) -> mb\n  { name, age: a } -> a\n  (0, s) -> s\n  'Ok n -> n" `exprIs`
        "(case m (mb@(parens (Just _)) mb) ((record name age:a) a) ((tuple 0 s) s) (('Ok n) n))"

  describe "handlers" do
    it "reads a handling expression mixing groups and handlers" do
      "handle work with\n  runToStdout\n  runWithLimit 1_000\n  State full\n    | get _ -> resume 0\n    | set _ -> resume ()" `exprIs`
        "(handle work runToStdout (runWithLimit 1_000) (group State full (| get _ (resume 0)) (| set _ (resume ()))))"
    it "reads the prefix form" do
      "using\n  Emit fast | emit _ -> 42\nhandle\n  emit ()" `exprIs`
        "(using (group Emit fast (| emit _ 42)) (emit ()))"
    it "reads labelled groups" do
      "handle work with\n  cache full | get _ -> resume 0\n             | set _ -> resume ()\n  counter    | fast get _ -> 0" `exprIs`
        "(handle work (group cache full (| get _ (resume 0)) (| set _ (resume ()))) (group counter (| fast get _ 0)))"
    it "reads a group with a cell" do
      "handle w with\n  Counter\n    var n := 0\n    | fast next _ -> n!" `exprIs`
        "(handle w (group Counter (var n 0) (| fast next _ n!)))"

  describe "declarations" do
    it "reads signatures and single-equation definitions" do
      [ "add :: Int -> Int -> Int", "add x y = x + y" ] `itemsAre`
        [ "(sig add (-> Int (-> Int Int)))", "(value add x y (+ x y))" ]
    it "reads patterns in parameters and a `where`" do
      [ "unFoo (Foo n) = n", "hypot x y = sqrt (sq x)", "  where", "  sq n = n * n" ] `itemsAre`
        [ "(value unFoo (parens (Foo n)) n)", "(value hypot x y (sqrt (parens (sq x))) (where (= sq n (* n n))))" ]
    it "reads data, newtype and type declarations" do
      [ "data Maybe a = Just a | Nothing", "data Role", "  = SuperUser", "  | Admin", "newtype Age = Age Int", "type Pair a = (a, a)" ] `itemsAre`
        [ "(data Maybe a (Just a) (Nothing))"
        , "(data Role (SuperUser) (Admin))"
        , "(newtype Age Age Int)"
        , "(type Pair a (tuple a a))"
        ]
    it "reads a leading `|` and a field directive" do
      [ "data Pixel = | Pixel (#unbox Int) (#unbox Int)" ] `itemsAre`
        [ "(data Pixel (Pixel ((#unbox) Int) ((#unbox) Int)))" ]
    it "reads kind signatures and kinded parameters" do
      rejects [ "data Proxy :: forall k. k -> Type" ]
      [ "data Proxy (a :: k) = Proxy", "type T :: Type -> Type" ] `itemsAre`
        [ "(data Proxy (:: a k) (Proxy))", "(type-kind T (-> Type Type))" ]
    it "reads effect declarations" do
      [ "effect State s where", "  get :: Unit ->* s", "  put :: s ->* Unit" ] `itemsAre`
        [ "(effect State s (get (->* Unit s)) (put (->* s Unit)))" ]
      [ "effect Console where", "  writeAt :: Int -> String ->* Unit" ] `itemsAre`
        [ "(effect Console (writeAt (-> Int (->* String Unit))))" ]
      [ "effect Partial where", "  abort :: forall b. Unit ->* b" ] `itemsAre`
        [ "(effect Partial (abort (forall b (->* Unit b))))" ]
    it "reads a resumption type that is a function" do
      [ "effect E where", "  op :: A ->* B -> C" ] `itemsAre`
        [ "(effect E (op (->* A (-> B C))))" ]
    it "reads handler declarations" do
      [ "handler counter :: Counter ~> () where", "  var n := 0", "  fast | next _ -> n!" ] `itemsAre`
        [ "(handler counter (~> Counter ()) (var n 0) (group fast (| next _ n!)))" ]
      [ "handler toMaybe :: forall a. (Unit -> a / {| Partial |}) -> Maybe a where", "  | return x -> Just x", "  | full abort _ -> Nothing" ] `itemsAre`
        [ "(handler toMaybe (forall a (-> (parens (-> Unit (/ a (effects Partial)))) (Maybe a))) (group (| return x (Just x))) (group (| full abort _ Nothing)))" ]
      [ "handler runWithLimit (limit :: Int) :: Fuel ~> () where", "  fast | burn k -> k" ] `itemsAre`
        [ "(handler runWithLimit (parens (:: limit Int)) (~> Fuel ()) (group fast (| burn k k)))" ]
    it "reads foreign declarations and foreign types, a directive before them" do
      [ "#observ(none) foreign sqrt :: Number -> Number", "foreign type Window :: Type" ] `itemsAre`
        [ "(#observ (none))", "(foreign sqrt (-> Number Number))", "(foreign-type Window Type)" ]
    it "reads fixity declarations" do
      [ "infixr 5 add as +", "infixl 8 range as .." ] `itemsAre`
        [ "(infixr 5 add +)", "(infixl 8 range ..)" ]
    it "reads a keyword as an attribute's name or label" do
      [ "@[where]", "@[let]", "@[foo where=1 of=2]", "x = 1" ] `itemsAre`
        [ "(@ where)", "(@ let)", "(@ foo where=1 of=2)", "(value x 1)" ]
    it "reads attributes as items of their own" do
      [ "@[entrypoint runner=myrunner]", "main :: Unit / {| Console |}", "@[typeclass.instance] showInt = 1" ] `itemsAre`
        [ "(@ entrypoint runner=myrunner)", "(sig main (/ Unit (effects Console)))", "(@ typeclass.instance)", "(value showInt 1)" ]
    it "reads a modifier before a handler" do
      [ "implicit", "handler h :: E ~> () where", "  fast | op _ -> 0" ] `itemsAre`
        [ "(modifier implicit)", "(handler h (~> E ()) (group fast (| op _ 0)))" ]
    it "reads a macro called at a declaration's position" do
      [ "class%{", "  Show a where", "    show :: a -> String", "}" ] `itemsAre`
        [ "(class% { Show a where show :: a -> String })" ]

  describe "modules" do
    it "reads exports and imports" do
      case parseModule "module M (x, T(..), U(A, B), (++), module N) where\nimport Prelude\nimport Data.Array (length, Maybe(..)) as A\nimport lazy Data.Array as DA" of
        Left e -> fail (printSyntaxError e)
        Right (Module m) -> map sketchItem m.items `shouldEqual`
          [ "(import Prelude)", "(import Data.Array (length Maybe(..)) as A)", "(import-lazy Data.Array as DA)" ]
    it "refuses what the grammar does not have" do
      rejects [ "x = case" ]
