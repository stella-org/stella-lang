module Test.Stella.Compiler.ProgramDescriptor (spec) where

import Prelude

import Data.Argonaut.Core (fromObject, fromString, stringify)
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.Maybe (Maybe(..))
import Data.String (Pattern(..), Replacement(..), replace)
import Data.Tuple (Tuple(..))
import Foreign.Object as Object
import Stella.Compiler.Bytecode.Instr (FuncIx(..))
import Stella.Compiler.Bytecode.Module (Dmo, GlobalInit(..))
import Stella.Compiler.ProgramDescriptor (Descriptor, DescriptorError(..), parse, print, validate)
import Stella.Compiler.TypedCore.Name (Ident(..), ModuleName(..), Qualified(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

program :: Descriptor
program =
  { entry: Qualified (ModuleName "Main") (Ident "$entrypoint")
  , modules: [ { module: ModuleName "Base.IO", object: "../base/Base.IO.dmo" }, { module: ModuleName "Main", object: "Main.dmo" } ]
  , foreign: Just (fromObject (Object.fromFoldable [ Tuple "target" (fromString "javascript") ]))
  }

-- | A descriptor read, `foreign` as text, which compares.
read :: String -> Either DescriptorError Shown
read = map shown <<< parse

type Shown = { entry :: Qualified Ident, modules :: Array { module :: ModuleName, object :: String }, foreign :: Maybe String }

shown :: Descriptor -> Shown
shown d = d { foreign = stringify <$> d.foreign }

written :: String -> String -> String
written field by = replace (Pattern field) (Replacement by) (print program)

-- | Bytecode of the name given, importing the modules given and holding the
-- | globals given, and nothing else.
dmo :: String -> Array String -> Array String -> Dmo
dmo name imports globals =
  { formatVersion: 0
  , abiVersion: "stella-base-0.1"
  , name: ModuleName name
  , imports: map ModuleName imports
  , constants: []
  , keys: []
  , ops: []
  , ctors: []
  , effects: []
  , foreigns: []
  , ctorRefs: []
  , foreignRefs: []
  , globalRefs: []
  , callees: []
  , prims: []
  , handlers: []
  , regions: []
  , functions: []
  , globals: map (\g -> { name: Qualified (ModuleName name) (Ident g), init: GRun (FuncIx 0) }) globals
  , exports: []
  }

spec :: Spec Unit
spec = describe "the program descriptor" do
  it "reads what it writes, with and without `foreign`" do
    for_ [ program, program { foreign = Nothing } ] \d ->
      read (print d) `shouldEqual` Right (shown d)

  it "refuses another format version, a field it does not fix, an empty string, a module listed twice, an entry module it does not list, and a `foreign` that is no object" do
    read (written "\"formatVersion\": 0" "\"formatVersion\": 1") `shouldEqual` Left (UnknownFormatVersion 0 1)
    read (written "\"formatVersion\": 0" "\"formatVersion\": 0, \"manifest\": \"m.json\"") `shouldEqual` Left (UnknownField "the descriptor" "manifest")
    read (written "\"global\": \"$entrypoint\"" "\"global\": \"$entrypoint\", \"arity\": 0") `shouldEqual` Left (UnknownField "`entry`" "arity")
    read (written "\"object\": \"Main.dmo\"" "\"object\": \"Main.dmo\", \"interface\": \"Main.dmi\"") `shouldEqual` Left (UnknownField "a module entry" "interface")
    read (written "\"object\": \"Main.dmo\"" "\"object\": \"\"") `shouldEqual` Left (MalformedDescriptor "`object` is not a non-empty string")
    read (written "\"module\": \"Base.IO\"" "\"module\": \"Main\"") `shouldEqual` Left (ModuleTwice (ModuleName "Main"))
    read (written "\"module\": \"Main\",\n    \"global\"" "\"module\": \"Other\",\n    \"global\"") `shouldEqual` Left (EntryUnlisted (ModuleName "Other"))
    read (print (program { foreign = Just (fromString "javascript") })) `shouldEqual` Left (MalformedDescriptor "`foreign` is not an object")
    read "{ \"formatVersion\": 0, \"modules\": [] }" `shouldEqual` Left (MalformedDescriptor "no `entry`")

  describe "held to its bytecode" do
    let
      -- `Main` imports `B` and `Prim`, and `B` imports `A`
      a = dmo "A" [] [ "x" ]
      b = dmo "B" [ "A" ] [ "y" ]
      main = dmo "Main" [ "B", "Prim" ] [ "main" ]
      listing names = { entry: Qualified (ModuleName "Main") (Ident "main"), modules: map (\n -> { module: ModuleName n, object: n <> ".dmo" }) names, foreign: Nothing }

    it "accepts the runtime closure of the entry module, each module after those it imports, `Prim` aside" do
      validate (listing [ "A", "B", "Main" ]) [ a, b, main ] `shouldEqual` Right unit

    it "refuses bytecode not one to one with the modules listed, a file of another module, a module before one it imports or with one unlisted, a module the entry module does not reach, and an entry point the entry module does not hold" do
      -- bytecode beyond what is listed, importing nothing unlisted, and bytecode short of it
      validate (listing [ "A", "B", "Main" ]) [ a, b, main, dmo "Extra" [] [ "main" ] ] `shouldEqual` Left (ObjectsUnmatched 3 4)
      validate (listing [ "A", "B", "Main" ]) [ a, b ] `shouldEqual` Left (ObjectsUnmatched 3 2)
      validate (listing [ "A", "B", "Main" ]) [ a, a, main ] `shouldEqual` Left (ObjectOfAnother (ModuleName "B") (ModuleName "A"))
      validate (listing [ "B", "A", "Main" ]) [ b, a, main ] `shouldEqual` Left (ImportNotBefore (ModuleName "B") (ModuleName "A"))
      validate (listing [ "B", "Main" ]) [ b, main ] `shouldEqual` Left (ImportNotBefore (ModuleName "B") (ModuleName "A"))
      validate (listing [ "A", "Other", "B", "Main" ]) [ a, dmo "Other" [] [ "main" ], b, main ] `shouldEqual` Left (Unreached (ModuleName "Other"))
      validate ((listing [ "A", "B", "Main" ]) { entry = Qualified (ModuleName "Main") (Ident "second") }) [ a, b, main ] `shouldEqual` Left (NoEntryGlobal (Qualified (ModuleName "Main") (Ident "second")))
