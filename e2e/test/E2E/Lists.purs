-- | Modules written in source calling a macro, built with each parser run on a
-- | session, then loaded and run: the front end end to end.
-- |
-- | A macro runs from the bytecode the build wrote for the module declaring it,
-- | which the session loads before the parser is run; a module built before, and
-- | standing outside the build, is loaded into the session first.
-- |
-- | `Data.List.Syntax`, of the `lists` package, declares `ls`, which reads
-- | `[ e, … ]` or a block and gives back `Cons (e) (Cons (…) Nil)`, written with
-- | quotations. The names it writes are not qualified: they are resolved where the
-- | call stands, so a module calling `ls` imports `Data.List (List(..))`. An error
-- | in what a call produced is reported at the call, and beside it where what it
-- | is about was written. The sources are those of `fixtures/source/lists`.
module Test.E2E.Lists (spec) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Either (Either(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.String (joinWith)
import Data.String as String
import Data.Tuple (Tuple(..))
import E2E.Build (OnSessionBuilt, Prebuilt, Sources, builtOnSession, collectedFrom)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Ref as Ref
import Fmt (fmt)
import Run (runBaseEffect)
import Run.Except as Except
import Stella.CLI.Session.Client as Client
import Stella.Compiler.Bytecode (Dmo)
import Stella.Compiler.Macro.Compiled (compiled)
import Stella.Compiler.TypedCore (Ident(..), ModuleName(..), Qualified(..))
import Steam.Foreign (emptyTable)
import Steam.Load (emptyStore, globalNamed, load, noIdentities)
import Steam.Value (CtorId, Value(..))
import Test.E2E.InProcess (openInProcess)
import Test.E2E.Session (hello, node)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

-- | Where the bytecode a build writes stands.
dir :: P.String
dir = "e2e/.test-dmo/lists"

type Ran = { result :: Either P.String (P.Array P.String), values :: Map.Map P.String P.String }

-- | The directory of `fixtures/source/lists` named built on a session of its own,
-- | against the modules built before, the bytecode of the modules named left
-- | unwritten; then every module loaded — those the compiler carries, those built
-- | before, and those built — and each of the globals of `Main` named rendered.
building :: Sources -> P.Array Prebuilt -> P.Array P.String -> P.String -> P.Array P.String -> (Ran -> Aff Unit) -> Aff Unit
building sources prebuilt unwritten case' globals k = case compiled of
  Left err -> fail err
  Right syntax -> do
    made <- onSession sources prebuilt unwritten case'
    case made.outcome of
      Left err -> k { result: Left err, values: Map.empty }
      Right names -> do
        values <- loaded (syntax.modules <> map _.dmo prebuilt <> map _.dmo made.lowered) globals
        k { result: Right names, values }

-- | One build on a session opened for it, and closed after.
onSession :: Sources -> P.Array Prebuilt -> P.Array P.String -> P.String -> Aff OnSessionBuilt
onSession sources prebuilt unwritten case' =
  openInProcess 1_000 hello { offers = [ "modules", "parse" ] } >>= case _ of
    Left failure -> pure { outcome: Left ("the session did not open: " <> show failure), lowered: [] }
    Right session -> do
      made <- builtOnSession sources { session, dir, unwritten, prebuilt } [ "lists/" <> case' ]
      void (node (Client.close session))
      pure made

-- | `Data.List` and `Data.List.Syntax`, built before the build that uses them.
prebuiltLists :: Sources -> (P.Array Prebuilt -> Aff Unit) -> Aff Unit
prebuiltLists sources k = do
  made <- onSession sources [] [] "prebuilt"
  case made.outcome of
    Left err -> fail ("the lists did not build: " <> err)
    Right _ -> k (Array.filter (\p -> Array.elem p.dmo.name [ ModuleName "Data.List", ModuleName "Data.List.Syntax" ]) made.lowered)

-- | The modules loaded in the order given, and each global of `Main` named,
-- | rendered.
loaded :: P.Array Dmo -> P.Array P.String -> Aff (Map.Map P.String P.String)
loaded modules globals = liftEffect do
  identities <- Ref.new noIdentities
  stored <- runBaseEffect (Except.runExcept (Array.foldM load (emptyStore emptyTable identities) modules))
  case stored of
    Left err -> pure (Map.singleton "load" (show err))
    Right store -> do
      known <- Ref.read identities
      let render = renderWith known.ctorNames
      held <- Array.foldM
        ( \acc name -> case globalNamed store (Qualified (ModuleName "Main") (Ident name)) of
            Nothing -> pure (Array.snoc acc (Tuple name "absent"))
            Just slot -> Ref.read slot <#> \value -> Array.snoc acc (Tuple name (maybe' "uninitialized" render value))
        )
        []
        globals
      pure (Map.fromFoldable held)
  where
  maybe' d f = case _ of
    Nothing -> d
    Just x -> f x

-- | A value as `Cons(1, Nil)`, a constructor named by the store.
renderWith :: Map.Map CtorId (Qualified Ident) -> Value -> P.String
renderWith names = go
  where
  go = case _ of
    VInt n -> show n
    VData id fields ->
      let
        name = case Map.lookup id names of
          Just (Qualified _ (Ident c)) -> c
          Nothing -> "?"
      in
        if Array.null fields then name else fmt @"{name}({fields})" { name, fields: joinWith ", " (map go fields) }
    _ -> "…"

spec :: Sources -> Spec Unit
spec sources = describe "the front end end to end, a macro run on a session" do
  it "builds a module calling a macro of a module built before, outside the build, and runs what it built" do
    prebuiltLists sources \prebuilt ->
      building sources prebuilt [] "outside" [ "xs", "none" ] \r -> do
        r.result `shouldEqual` Right [ "Main" ]
        Map.lookup "xs" r.values `shouldEqual` Just "Cons(1, Cons(2, Nil))"
        Map.lookup "none" r.values `shouldEqual` Just "Nil"

  it "reports a call the parser refuses where in its input it stopped, then at the call" do
    building sources [] [] "refused" [] \r ->
      case r.result of
        Left message -> do
          let at = "fixtures/source/lists/refused/Main.stel:5:9: "
          String.take (String.length at) message `shouldEqual` at
          String.contains (String.Pattern "(see also 5:6)") message `shouldEqual` true
        Right _ -> fail "built"

  describe "a macro of the build" do
    it "is run from the bytecode the build wrote, its module loaded into the session first" do
      building sources [] [] "pass" [ "n" ] \r -> do
        r.result `shouldEqual` Right [ "Pass", "Main" ]
        Map.lookup "n" r.values `shouldEqual` Just "2"

    it "is not run where its module's bytecode was not written" do
      building sources [] [ "Pass" ] "pass" [] \r ->
        r.result `shouldEqual` Left "unavailable Pass"

  describe "a macro written with a quotation" do
    it "expands to the syntax the quotation built, what an antiquotation holds spliced in parentheses" do
      building sources [] [] "quoting" [ "n", "m" ] \r -> do
        r.result `shouldEqual` Right [ "Quoting", "Main" ]
        Map.lookup "n" r.values `shouldEqual` Just "1"
        Map.lookup "m" r.values `shouldEqual` Just "3"

  describe "the list macro of the lists package, used by another module" do
    it "builds a list of what the brackets hold, a call among them, and of what the block holds" do
      building sources [] [] "package" [ "xs", "none", "nested", "block" ] \r -> do
        r.result `shouldEqual` Right [ "Data.List.Syntax", "Data.List", "Main" ]
        Map.lookup "xs" r.values `shouldEqual` Just "Cons(1, Cons(2, Nil))"
        Map.lookup "none" r.values `shouldEqual` Just "Nil"
        Map.lookup "nested" r.values `shouldEqual` Just "Cons(Cons(1, Cons(2, Nil)), Cons(Cons(3, Cons(4, Nil)), Cons(Cons(5, Cons(6, Nil)), Nil)))"
        Map.lookup "block" r.values `shouldEqual` Just "Cons(1, Cons(2, Nil))"

    -- what a module imports for a macro alone is no module its program holds
    -- to run: `Main` runs with `Data.List` and `Base.Int`, which its values
    -- reach, and neither `Data.List.Syntax` nor `Stella.Syntax`
    it "builds a list by the macro `Data.List` re-exports, and runs holding neither module the macro comes from" do
      made <- onSession sources [] [] "reexported"
      case compiled, made.outcome of
        Left err, _ -> fail err
        _, Left err -> fail err
        Right syntax, Right names -> do
          names `shouldEqual` [ "Data.List.Syntax", "Data.List", "Main" ]
          let main = Array.find (\p -> p.dmo.name == ModuleName "Main") made.lowered
          map _.dmo.imports main `shouldEqual` Just [ ModuleName "Data.List" ]
          map _.interface.imports main `shouldEqual` Just [ ModuleName "Data.List" ]
          case collectedFrom [ ModuleName "Main" ] (syntax.modules <> map _.dmo made.lowered) of
            Left err -> fail err
            Right held -> do
              map _.name held `shouldEqual` map ModuleName [ "Base.Int", "Data.List", "Main" ]
              values <- loaded held [ "xs" ]
              Map.lookup "xs" values `shouldEqual` Just "Cons(1, Cons(2, Nil))"

    it "reports a constructor the call's module does not import at the call, written in the quotation" do
      building sources [] [] "unimported" [] \r ->
        r.result `shouldEqual` Left
          """fixtures/source/lists/unimported/Main.stel:5:6: There is no constructor `Cons` in scope (written at stella-packages/lists/src/Data/List/Syntax.stel:19:23)
fixtures/source/lists/unimported/Main.stel:5:6: There is no constructor `Nil` in scope (written at stella-packages/lists/src/Data/List/Syntax.stel:22:33)"""

    it "reports what an element names at the call, written in the call's input, through every call it stands in" do
      building sources [] [] "unbound" [] \r ->
        r.result `shouldEqual` Left
          """fixtures/source/lists/unbound/Main.stel:5:6: There is no value `y` in scope (written at fixtures/source/lists/unbound/Main.stel:5:13)
fixtures/source/lists/unbound/Main.stel:7:6: There is no value `z` in scope (written at fixtures/source/lists/unbound/Main.stel:7:14)"""
