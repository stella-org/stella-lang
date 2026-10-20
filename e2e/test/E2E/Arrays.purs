-- | `Base.Array` and a module over it, carried the whole way.
-- |
-- | `Main` is built from `fixtures/source/arrays` with the `Base.Array` and
-- | `Base.Int` of `stella-packages/base`, and every module it reaches is
-- | loaded. What a global slot holds after that is the assertion, so what is
-- | exercised is the chain rather than any one link — `foreign type Array`
-- | supplying an intrinsic opaque type, a `foreign` the interpreter claims
-- | lowering to a `PRIM`, an array reaching a register as an opaque value, and
-- | the write being seen by the read.
-- |
-- | **`mapArray` is Stella over the entries and not an entry itself**: a
-- | `foreign` is a first-order leaf, so a function over an array is a loop that
-- | tests `i < length xs` with `Base.Int.lt` and writes every slot before it
-- | returns ([Implementation Plan](../../../docs/technical-references/01-Introduction/04-Implementation-Plan.md)).
module Test.E2E.Arrays (spec) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Either (Either(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Traversable (traverse)
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Ref as Ref
import Run (runBaseEffect)
import Run.Except as Except
import Steam.Foreign (emptyTable)
import Steam.Load (LoadError, Store, emptyStore, globalNamed, load, namesOf, noIdentities)
import Steam.Value (Value(..))
import Stella.Compiler.Bytecode (Dmo)
import Stella.Compiler.TypedCore (Ident(..), ModuleName(..), Qualified(..))
import Stella.Compiler.TypedCore.Prim (unitCtor)
import E2E.Build (Sources, builtFrom)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

mainNamed :: P.String -> Qualified Ident
mainNamed = Qualified (ModuleName "Main") <<< Ident

-- | The modules `Main` reaches, in the order they are built, `Main` last.
built :: Sources -> Either P.String (P.Array Dmo)
built sources = builtFrom sources [ "arrays" ]

fresh :: Effect Store
fresh = map (emptyStore emptyTable) (Ref.new noIdentities)

loading :: P.Array Dmo -> Aff (Either LoadError Store)
loading modules = liftEffect do
  store <- fresh
  runBaseEffect (Except.runExcept (Array.foldM load store modules))

-- | Every module loaded, and the store given to `k`.
loaded :: Sources -> (Store -> Aff Unit) -> Aff Unit
loaded sources k = case built sources of
  Left err -> fail err
  Right dmos -> loading dmos >>= case _ of
    Left err -> fail (show err)
    Right store -> k store

valueOf :: Store -> Qualified Ident -> Aff (Maybe Value)
valueOf store name = liftEffect case globalNamed store name of
  Nothing -> pure Nothing
  Just slot -> Ref.read slot

held :: Maybe Value -> Maybe P.Int
held = case _ of
  Just (VInt n) -> Just n
  _ -> Nothing

spec :: Sources -> Spec Unit
spec sources = describe "Steam, over Base.Array and a module on top of it" do

  it "builds every module it reaches the whole way" do
    case built sources of
      Left err -> fail err
      Right _ -> pure unit

  -- a saturated call to a `Base` entry the ABI fixes the meaning of is a `prim`
  -- and not an `ffi`, and the two would be indistinguishable downstream: the
  -- loader resolves such a name to the interpreter either way
  it "lowers the calls to operations rather than to foreign references" do
    case built sources of
      Left err -> fail err
      Right dmos -> case Array.last dmos of
        Nothing -> fail "nothing was built"
        Just main -> do
          Array.null main.prims `shouldEqual` false
          Array.null main.foreignRefs `shouldEqual` true

  -- the chain end to end: the intrinsic, four `foreign` declarations the loader
  -- resolves to the interpreter, and a program that allocates, writes, and reads
  -- back
  it "reads back what it wrote, through the whole pipeline" do
    loaded sources \store -> do
      value <- valueOf store (mainNamed "result")
      held value `shouldEqual` Just 9

  it "reports the slot count an allocation was asked for" do
    loaded sources \store -> do
      value <- valueOf store (mainNamed "size")
      held value `shouldEqual` Just 3

  -- the write answers with the registry's own `Prim.Unit`, which is what makes it
  -- the same value every other `Prim.Unit` in the program is
  it "answers a write with the Prim.Unit the registry assigned" do
    loaded sources \store -> do
      value <- valueOf store (mainNamed "wrote")
      names <- liftEffect (namesOf store)
      case value of
        Just (VData ctor []) ->
          Map.lookup ctor names.ctors `shouldEqual` Just unitCtor
        _ -> fail "the write did not answer with a constructor of no fields"

  -- the end-to-end case over the wider surface: a loop that counts with `add`, stops
  -- by `lt`, and writes every slot of an array it allocated before returning it
  it "maps over an array with a loop written over the entries" do
    loaded sources \store -> do
      length <- valueOf store (mainNamed "mappedLength")
      held length `shouldEqual` Just 3
      slots <- traverse (valueOf store <<< mainNamed) [ "mapped0", "mapped1", "mapped2" ]
      map held slots `shouldEqual` [ Just 11, Just 21, Just 31 ]
