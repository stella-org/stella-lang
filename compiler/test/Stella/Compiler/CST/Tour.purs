-- | A module using every form of the surface syntax at once, which the parser
-- | must read through.
module Test.Stella.Compiler.CST.Tour (spec) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Stella.Compiler.CST (parseModule, printSyntaxError)
import Stella.Compiler.CST.Types (Module(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

tour :: String
tour =
  """module Tour (Maybe(..), Id, answer, (++), attribute json, module Data.Array) where

import Prelude
import TC (attribute instance, attribute priority) as TC
import Data.Array (length, elem)
import Data.Array (length, elem) as A
import lazy Data.Array as DA

data Maybe :: Type -> Type
data Maybe (a :: Type) = Just a | Nothing

data List a =
  | Nil
  | Cons a (List a)

newtype Id = Id Int

type T :: Type
type P (a :: Type) = Array a

length'   :: forall a. Array a -> Int
log       :: String -> Unit / {| Console |}
logAt     :: Int -> String -> Unit / {| Console |}
reader    :: (String -> Int) / {| Config |}
mapE      :: forall a b (e :: Row Effect). (a -> b / {| ...e |}) -> Array a -> Array b / {| ...e |}
showTwice :: forall a. Show a => a -> String
person    :: { name :: String, age :: Int }
named     :: forall r. { name :: String, ...r } -> String
pair      :: (Int, String)
unit'     :: ()
result    :: [ 'Ok :: Int, 'Err :: String ]
open      :: forall r. [ 'Ok :: Int, ...r ]
never     :: []
twoStates :: Unit -> Int / {| cache :: State Int, counter :: State Int |}
proxy     :: Proxy (Maybe :: Type -> Type)

effect Random where
  random :: Unit ->* Number

effect State s where
  get :: Unit ->* s
  put :: s ->* Unit

effect Console where
  writeAt :: Int -> String ->* Unit

#observ(none)
foreign length :: forall a. Array a -> Int

#observ(none) foreign sqrt :: Number -> Number

foreign type Window :: Type
foreign type Promise :: Type -> Type
foreign window :: IO Window

data Pixel = Pixel (#unbox Int) (#unbox Int)

infixr 5 append as ++
infixl 8 range as ..

attribute priority Int
attribute json (name :: String) (omitEmpty :: Boolean = false)

@[TC.priority 10]
@[json name="sum" omitEmpty=true]
#inline(arity=2)
sum2 x y = x + y

@[test]
additionIsCommutative :: Boolean
additionIsCommutative = true

@[entrypoint]
main :: Unit / {| Console |}
main = Console.log "Hello, World!"

@[TC.instance]
showInt :: Show Int
showInt = { show: Base.Int.toString }

answer :: Int
answer = 42

add :: Int -> Int -> Int
add x y = x + y

area { w, h } = w * h
unFoo (Foo n) = n
swap (a, b) = (b, a)

fromMaybe :: forall a. a -> Maybe a -> a
fromMaybe = case _, _ of
  _, Just a -> a
  a, _ -> a

hypot :: Number -> Number -> Number
hypot x y = sqrt (sq x + sq y)
  where
  sq n = n * n

randomInt :: Int / {| Random |}
randomInt =
  let n = random () in
  ceil n

literals = ( 42, -1, 1_000_000, 3.14, -0.5, 6.02e23, 1e-3, 0xFF, 0b1010 )
arithmetic = (x - 1, x-1, f -1, negate x, a + b * c, n `rem` 3, (+))
texts = ( "hello", "\u{1F600}" )
chars = ( 'a', '\n', '\'' )
lambdas = (\x y -> x + y, \_ -> Console.log "later", \{ name } -> name)
records = ({ name: "Stella", age: 3 }, { name, age }, person.name, { age = 4, ...person })
variants = (1, 'Ok 42, 'Err "boom")
misc = (filter Just? xs, ?todo, ?_, DA.( length xs + 1 ), import DA in length xs, (xs :: Array Int), get@cache ())
sections = (_ + 1, (_ `rem` 2))

isBoth :: Maybe Int -> Maybe Int -> Boolean
isBoth = case _, _ of
  Just _, Just _ -> true
  _, _ -> false

level role = case role of
  SuperUser | Admin -> 1
  Guest -> 0

digit = case _ of
  0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 -> true
  _ -> false

columns = case _, _ of
  A, (B | C) -> 1
  _, _ -> 0

fizzbuzz :: Int -> String
fizzbuzz = case _ of
  n where
      mul3 = n `rem` 3 == 0
      mul5 = n `rem` 5 == 0
      mul3 && mul5 -> "FizzBuzz"
      mul3 -> "Fizz"
      mul5 -> "Buzz"
  n -> format%"{n}"

sign = case _ of
  n where
      n > 0 -> 1
      n < 0 -> -1
      otherwise -> 0

patterns m = case m of
  mb@(Just _) -> mb
  { name, age } -> name
  (0, s) -> s
  'Ok n -> n
  'Err _ -> 0

abs' n = cases%{
  n          where n >= 0
  negate n   otherwise
}

handler runEmit :: Emit ~> () where
  fast | emit _ -> 42

handler toMaybe :: forall a e. (Unit -> a / {| Partial, ...e |}) -> Maybe a / {| ...e |} where
  | return x -> Just x
  | full abort _ -> Nothing

handler counter :: Counter ~> () where
  var n := 0
  fast | next _ -> let v = n! in let _ = n := v + 1 in v

implicit
handler runWithLimit (limit :: Int) :: Fuel ~> () where
  var used := 0
  fast | burn k -> used := used! + k

program :: Unit / {| Logger |}
program =
  handle work with
    var saved := 0
    runToStdout
    runWithLimit 1_000
    State full
      | get _ -> resume saved!
      | set n -> let _ = saved := n in resume ()

main' :: Unit / {| Console |}
main' =
  using
    Emit fast | emit _ -> 42
  handle
    let ans = emit () in
    Console.log format%"The ultimate answer is {ans}"

labelled =
  handle work with
    cache full | get _ -> resume 0
               | set _ -> resume ()
    counter    | fast get _ -> 0
               | fast set _ -> ()

choices =
  handle choose' with
    Choice
      | full choose _ ->
          let x = resume true in
          let y = resume false in
          x ++ y

thunks = (runToStdout (\_ -> work), runIO (\_ -> program))

class%{
  Show a where
    show :: a -> String
}

instance%{
  showArray :: Show a => Show (Array a) where
    show = showArrayWith show
}

doing = do%{
  x <- action1
  y <- action2 x
  pure y
}
"""

spec :: Spec Unit
spec = describe "Stella.Compiler.CST.Tour" do
  it "reads a module using every form" do
    case parseModule tour of
      Left e -> fail (printSyntaxError e)
      Right (Module m) -> (Array.length m.items > 90) `shouldEqual` true
