-- | A module's source compiled to bytecode, every stage in order, with parsers
-- | a table runs: what each stage reports, where it stands, and that a stage
-- | reporting an error is the last that runs.
module Test.Stella.Compiler.Build (spec) where

import Prelude
import Prim hiding (Type)

import Fmt (fmt)
import Data.Array as Array
import Data.Array.NonEmpty as NonEmptyArray
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.Identity (Identity(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Data.String (joinWith)
import Data.String as String
import Data.Tuple (Tuple(..))
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Ref as Ref
import Stella.Compiler.Bytecode.Lower (LowerError(..))
import Stella.Compiler.CST.Types (inSource)
import Stella.Compiler.Elaborate.CorePlus.Context (Origin(..))
import Stella.Compiler.Elaborate.Environment.Imported (compilationSignature, importedSignature)
import Stella.Compiler.Elaborate.Mechanism.Obligation (Basis(..), Breach(..))
import Stella.Compiler.Elaborate.Surface.Module (ElaborationError(..))
import Stella.Compiler.Elaborate.Vocabulary.Diagnostic (Diagnostic(..))
import Stella.Compiler.Interface.Environment (BuildEnvironment, addInterface, initialEnvironment, viewFor)
import Stella.Compiler.Interface.Module (ModuleInterface, TypeEntity(..), TypeSort(..), ValueSort(..), Via(..), emptyDeclarations, emptyExports)
import Stella.Compiler.Interface.Prim (primAttribute)
import Stella.Compiler.Interface.Scheme (plainScheme)
import Stella.Compiler.Macro.Bundle (syntaxModuleName)
import Stella.Compiler.Macro.Run (ParseOutcome(..), RunParser, defaultSettings)
import Stella.Compiler.Macro.Tree (Position(..), Range(..), SyntaxNode(..), Token(..), TokenTree(..))
import Stella.Compiler.Macro.Tree as Tree
import Stella.Compiler.Build (BackendProblem(..), BuildError(..), CompileError(..), CompileWarning, CompilerAction, DiagnosticLocation, EnvironmentProblem(..), PackageFile, SyntaxProblem(..), build, buildMessages, compileModule, defaultHooks, locationsOf, printCompileError, warningLocationOf)
import Stella.Compiler.Surface.Origin as Surface
import Stella.Compiler.TypedCore (Decl(..))
import Stella.Compiler.TypedCore.Kind (Kind(..), monoScheme)
import Stella.Compiler.TypedCore.Name (Ident(..), ModuleName(..), Qualified(..), Symbol(..), TyName(..))
import Stella.Compiler.TypedCore.Prim (intTy, pureFn)
import Stella.Compiler.TypedCore.Type (RowKey(..), Type(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

-- The modules imported ---------------------------------------------------------------

int :: Type
int = TCon intTy []

syntaxType :: String -> Type
syntaxType n = TCon (Qualified syntaxModuleName (TyName n)) []

-- | `Parser (Syntax Term)`.
termParser :: Type
termParser = TApp (syntaxType "Parser") (TApp (syntaxType "Syntax") (syntaxType "Term"))

-- | The types of `Stella.Syntax` a macro's scheme names, standing as foreign
-- | types: `Parser` and `Syntax` of kind `Type -> Type`, and `Term`.
syntaxInterface :: ModuleInterface
syntaxInterface =
  { name: syntaxModuleName
  , imports: []
  , exports: emptyExports { types = Map.fromFoldable (map (\(Tuple n _) -> Tuple n { entity: TypeEntity (Qualified syntaxModuleName (TyName n)), via: Declared, members: [] }) types) }
  , declarations: emptyDeclarations { types = Map.fromFoldable (map (\(Tuple n k) -> Tuple (TyName n) { kind: monoScheme k, sort: ForeignType, attributes: [] }) types) }
  , implicitHandlers: []
  , catalogOnly: Set.empty
  , arities: Map.empty
  }
  where
  types = [ Tuple "Parser" (KFun KType KType), Tuple "Syntax" (KFun KType KType), Tuple "Term" KType ]

-- | `A`: `inc : Int -> Int`, and the macros `unwrap` and `failing`.
interfaceA :: ModuleInterface
interfaceA =
  { name: moduleA
  , imports: [ syntaxModuleName ]
  , exports: emptyExports
      { values = Map.singleton "inc" (declared "inc")
      , macros = Map.fromFoldable (map (\n -> Tuple n (declared n)) macros)
      }
  , declarations: emptyDeclarations
      { values = Map.fromFoldable
          ( [ Tuple (Ident "inc") { sort: SortValue, scheme: plainScheme (monoScheme (pureFn int int)), attributes: [] } ]
              <> map (\n -> Tuple (Ident n) { sort: SortValue, scheme: plainScheme (monoScheme termParser), attributes: [ { name: primAttribute "macro", positional: [], keyword: [] } ] }) macros
          )
      }
  , implicitHandlers: []
  , catalogOnly: Set.empty
  , arities: Map.singleton (Ident "inc") 1
  }
  where
  macros = [ "unwrap", "failing" ]
  declared n = { entity: Qualified moduleA (Ident n), via: Declared }

-- | `C`, declaring a type `Bad` at `Effect`, a kind no type constructor
-- | produces.
interfaceC :: ModuleInterface
interfaceC =
  { name: ModuleName "C"
  , imports: []
  , exports: emptyExports { types = Map.singleton "Bad" { entity: TypeEntity (Qualified (ModuleName "C") (TyName "Bad")), via: Declared, members: [] } }
  , declarations: emptyDeclarations
      { types = Map.singleton (TyName "Bad") { kind: monoScheme KEffect, sort: ForeignType, attributes: [] } }
  , implicitHandlers: []
  , catalogOnly: Set.empty
  , arities: Map.empty
  }

moduleA :: ModuleName
moduleA = ModuleName "A"

environment :: BuildEnvironment
environment = case addInterface syntaxInterface initialEnvironment >>= addInterface interfaceA >>= addInterface interfaceC of
  Right env -> env
  Left _ -> initialEnvironment

-- | What each macro of `A` does with its input: `unwrap` gives back what its
-- | brackets hold, and `failing` fails at the input's first token.
parsers :: RunParser Identity
parsers (Qualified _ (Ident name)) { input } = Identity case name, input.trees of
  "unwrap", [ Group _ _ inner _ ] -> ParsedAs (Tree.Syntax (map nodeOf inner))
  "failing", [ Group _ _ inner _ ] | Just (Leaf (Token _ _ r _ _)) <- Array.head inner ->
    FailedAs { position: startOf r, expected: Set.singleton "`]`", labels: [] }
  _, _ -> FailedAs { position: Position 0 0, expected: Set.empty, labels: [] }
  where
  startOf (Range start _) = start

nodeOf :: TokenTree -> SyntaxNode
nodeOf = case _ of
  Leaf t -> SyntaxToken t
  Group d open inner closes -> SyntaxGroup (originOf open) d open (map nodeOf inner) closes
  where
  originOf (Token _ _ _ _ o) = o

-- Compiling a module -----------------------------------------------------------------

-- | What compiling a module gave: its errors, or its warnings and what each
-- | phase handed over — the values the Core binds, the Mid IR's module, and the
-- | bytecode's.
type Ran = Either (Array CompileError) { warnings :: Array CompileWarning, handed :: Array String }

-- | The module `M`, its lines as given after its header; compiled with the
-- | parsers the table runs, what each phase hands over recorded.
compiling :: Array String -> (Ran -> Aff Unit) -> Aff Unit
compiling lines k = do
  handed <- liftEffect (Ref.new [])
  let
    note s = liftEffect (Ref.modify_ (\l -> Array.snoc l s) handed)

    action :: CompilerAction Aff
    action =
      { readSource: \_ -> pure (Left "no file")
      , runParser: \q i -> pure (unwrapIdentity (parsers q i))
      , hooks: defaultHooks
          { onElaborated = \core -> note ("core " <> joinWith " " (Array.mapMaybe bound core.decls))
          , onTranslated = \mid -> note ("mid " <> moduleText mid.name)
          , onLowered = \bytecode -> note ("bytecode " <> moduleText bytecode.dmo.name)
          }
      }
  r <- compileModule action defaultSettings environment (joinWith "\n" ([ "module M where" ] <> lines))
  recorded <- liftEffect (Ref.read handed)
  k case r of
    Left errors -> Left (NonEmptyArray.toArray errors)
    Right warnings -> Right { warnings, handed: recorded }

unwrapIdentity :: forall a. Identity a -> a
unwrapIdentity (Identity a) = a

bound :: Decl Surface.Origin -> Maybe String
bound = case _ of
  DeclNonRec _ b -> Just (identText b.name)
  DeclRec _ bs -> Just (joinWith " " (map (identText <<< _.name) bs))
  _ -> Nothing
  where
  identText (Ident n) = n

-- | Every error, as its stage and where it stands.
failing :: Array String -> (Array String -> Aff Unit) -> Aff Unit
failing lines k = compiling lines case _ of
  Left errors -> k (map describe errors)
  Right _ -> fail "compiled"
  where
  describe e = stageOf e <> joinWith "" (map (\l -> " " <> at l) (locationsOf e))

stageOf :: CompileError -> String
stageOf = case _ of
  Syntax (Unparsed _) -> "syntax"
  Syntax (IllFormed _) -> "ill-formed"
  Resolution _ -> "resolution"
  Environment (ImportsRefused _) -> "imports"
  Environment _ -> "environment"
  Elaboration _ -> "elaboration"
  Backend _ -> "backend"

at :: DiagnosticLocation -> String
at l = fmt @"{line}:{column}" { line: l.start.line, column: l.start.column }

spec :: Spec Unit
spec = describe "Stella.Compiler.Build" do
  buildSpec
  describe "a module" do
    it "is compiled to bytecode, a macro call among it, its warnings kept" do
      compiling
        [ "import A"
        , "f :: Int -> Int"
        , "f x = inc x"
        , "n :: Int"
        , "n = unwrap%[inc 1]"
        , "g :: Int -> Int"
        , "g inc = inc"
        ]
        case _ of
          Left errors -> fail (joinWith "; " (map printCompileError errors))
          Right r -> do
            r.handed `shouldEqual` [ "core f n g", "mid M", "bytecode M" ]
            map (at <<< warningLocationOf) r.warnings `shouldEqual` [ "8:3" ]

  describe "a stage reporting an error" do
    it "is a syntax error where the parser stopped" do
      failing [ "f = = 1" ] \errors -> errors `shouldEqual` [ "syntax 2:5" ]

    it "is syntax no later stage reads, where it stands" do
      failing [ "f :: Int ->* Int", "f x = x" ] \errors -> errors `shouldEqual` [ "ill-formed 2:10" ]

    it "is the last that runs: resolution stops what elaboration would report" do
      failing [ "import A", "f :: Int", "f = nope", "g :: Int", "g = inc" ] \errors ->
        errors `shouldEqual` [ "resolution 4:5" ]

    it "reports a macro whose parser failed where in its input it failed, then at the call" do
      failing [ "import A", "n :: Int", "n = failing%[1]" ] \errors ->
        errors `shouldEqual` [ "resolution 4:14 4:5" ]

    it "reports imports whose interfaces make no signature, at no place" do
      failing [ "import C", "n :: Int", "n = 1" ] \errors -> errors `shouldEqual` [ "imports" ]

    it "reports what elaboration refused where it stands" do
      failing [ "import A", "bad :: Int", "bad = inc" ] \errors -> errors `shouldEqual` [ "elaboration 4:7" ]

  describe "an error" do
    it "keeps every place it is about" do
      let
        site line = AtSource { declaration: Qualified (ModuleName "M") (Ident "f"), origin: Surface.FromSource (inSource { line, column: 1 } { line, column: 2 }) }
        broken = Elaboration (Rejected (ObligationBroken { equation: site 3, obligation: site 5, basis: Assumed, breach: SidesShareKey (SymbolKey (Symbol "a")) }))
      map at (locationsOf broken) `shouldEqual` [ "3:1", "5:1" ]

    it "is said to be the compiler's where it is" do
      let refused = Backend (LowerFailed (RegionKeyInCode (SymbolKey (Symbol "r"))))
      locationsOf refused `shouldEqual` []
      String.take 23 (printCompileError refused) `shouldEqual` "Internal compiler error"
      String.take 23 (printCompileError (Elaboration AttemptPostponed)) `shouldEqual` "Internal compiler error"

  describe "the signature a module is compiled against" do
    it "holds the types the ABI manifest supplies to the module itself" do
      let
        self = ModuleName "M"
        handle = Qualified self (TyName "Handle")
        env = environment { abi = Map.singleton self (Map.singleton (TyName "Handle") { kind: monoScheme KType, sort: ForeignType, attributes: [] }) }
      case viewFor [] env of
        Left _ -> fail "no view"
        Right view -> do
          map (Map.member handle <<< _.types) (compilationSignature env view self) `shouldEqual` Right true
          map (Map.member handle <<< _.types) (importedSignature env view) `shouldEqual` Right false

-- Building a package -----------------------------------------------------------------

-- | A package of the files given, each at its path from the root with its
-- | text; built, with every read, every phase shown, and every module handed
-- | over recorded in order.
building :: Array (Tuple String String) -> ({ result :: Either BuildError (Array String), log :: Array String } -> Aff Unit) -> Aff Unit
building sources k = do
  log <- liftEffect (Ref.new [])
  let
    note s = liftEffect (Ref.modify_ (\l -> Array.snoc l s) log)
    files = map (\(Tuple p _) -> { path: p, within: String.split (String.Pattern "/") p }) sources

    action :: CompilerAction Aff
    action =
      { readSource: \p -> do
          note ("read " <> p)
          pure case Array.find (\(Tuple q _) -> q == p) sources of
            Just (Tuple _ text) -> Right text
            Nothing -> Left "no such file"
      , runParser: \q i -> pure (unwrapIdentity (parsers q i))
      , hooks: defaultHooks
          { onStartCompile = \p f -> note (fmt @"start {current}/{total} {name}" { current: p.current, total: p.total, name: moduleText f.name })
          , onElaborated = \_ -> note "elaborated"
          , onTranslated = \_ -> note "translated"
          , onEnterOptimizeIter = \_ -> note "optimize"
          , onLeaveOptimizeIter = \_ -> note "optimized"
          , onLowered = \b -> note ("lowered " <> moduleText b.dmo.name)
          , onModuleDone = \m -> note ("done " <> moduleText m.name)
          }
      }
  result <- build action defaultSettings environment (files :: Array PackageFile)
  logged <- liftEffect (Ref.read log)
  k { result: map (map (moduleText <<< _.name)) result, log: logged }

moduleText :: ModuleName -> String
moduleText (ModuleName m) = m

-- | A module's text: its header naming it and importing the modules given,
-- | then `n = 1`, or the lines given.
moduleOf :: String -> Array String -> Array String -> String
moduleOf name imports body = joinWith "\n" ([ fmt @"module {name} where" { name } ] <> map ("import " <> _) imports <> body)

valueModule :: String -> Array String -> String
valueModule name imports = moduleOf name imports [ "n :: Int", "n = 1" ]

buildSpec :: Spec Unit
buildSpec = describe "a build" do
  it "reads every header first, then compiles one module at a time, showing each phase" do
    building [ Tuple "src/A.stel" (valueModule "A" []), Tuple "test/B.stel" (valueModule "Test.B" []) ] \r -> do
      case r.result of
        Right built -> built `shouldEqual` [ "A", "Test.B" ]
        Left err -> fail (joinWith "; " (map _.message (NonEmptyArray.toArray (buildMessages err))))
      r.log `shouldEqual`
        ( [ "read src/A.stel", "read test/B.stel" ]
            <> [ "read src/A.stel", "start 1/2 A", "elaborated", "translated", "optimize", "optimized", "lowered A", "done A" ]
            <> [ "read test/B.stel", "start 2/2 Test.B", "elaborated", "translated", "optimize", "optimized", "lowered Test.B", "done Test.B" ]
        )

  it "names a module by its path, and refuses a header naming another" do
    building [ Tuple "src/A/B.stel" (valueModule "A.C" []) ] \r -> case r.result of
      Left (NameMismatch m) -> do
        moduleText m.expected `shouldEqual` "A.B"
        at m.at `shouldEqual` "1:8"
      _ -> fail "not refused"
    building [ Tuple "src/Test/B.stel" (valueModule "Test.B" []) ] \r -> case r.result of
      Left (NameReserved _) -> pure unit
      _ -> fail "not reserved"
    -- a segment of the path is no name a module's name may hold
    for_ [ "src/A.B.stel", "src/Test.B.stel", "src/a/B.stel", "src/.stel" ] \p ->
      building [ Tuple p (valueModule "A.B" []) ] \r -> case r.result of
        Left (NotAModuleName q) -> q `shouldEqual` p
        _ -> fail ("not refused: " <> p)
    building [ Tuple "lib/B.stel" (valueModule "B" []) ] \r -> case r.result of
      Left (OutsidePackage p) -> p `shouldEqual` "lib/B.stel"
      _ -> fail "not outside"
    building [ Tuple "src/B.stel" (valueModule "B" []), Tuple "src/B.stel" (valueModule "B" []) ] \r -> case r.result of
      Left (ListedTwice _) -> pure unit
      _ -> fail "not listed twice"

  it "compiles a module after those of the build it imports, the one given first taken first" do
    building [ Tuple "src/B.stel" (valueModule "B" [ "A" ]), Tuple "src/C.stel" (valueModule "C" []), Tuple "src/A.stel" (valueModule "A" []) ] \r -> do
      -- `B` is compiled only against modules built before this build
      case r.result of
        Left (ImportWithinBuild e) -> moduleText e.imported `shouldEqual` "A"
        _ -> fail "not refused"
      Array.filter (String.contains (String.Pattern "start")) r.log `shouldEqual` [ "start 1/3 C", "start 2/3 A" ]

  it "reports modules importing one another before compiling any" do
    building [ Tuple "src/A.stel" (valueModule "A" [ "B" ]), Tuple "src/B.stel" (valueModule "B" [ "A" ]) ] \r -> do
      case r.result of
        Left (ImportCycle members) -> map (moduleText <<< _.name) (NonEmptyArray.toArray members) `shouldEqual` [ "A", "B" ]
        _ -> fail "no cycle"
      Array.filter (String.contains (String.Pattern "start")) r.log `shouldEqual` []

  it "stops at a module that does not compile, its errors said of its file" do
    building [ Tuple "src/A.stel" (valueModule "A" []), Tuple "src/B.stel" (moduleOf "B" [] [ "n :: Int", "n = nope" ]), Tuple "src/C.stel" (valueModule "C" []) ] \r -> do
      case r.result of
        Left err -> map (\m -> { path: m.path, at: map at m.locations }) (NonEmptyArray.toArray (buildMessages err))
          `shouldEqual` [ { path: Just "src/B.stel", at: [ "3:5" ] } ]
        Right _ -> fail "built"
      Array.filter (String.contains (String.Pattern "done")) r.log `shouldEqual` [ "done A" ]

  it "reads a header without the declarations after it" do
    -- the syntax error stands in a declaration: the header is read, and the
    -- module's compiling reports it
    building [ Tuple "src/A.stel" (moduleOf "A" [] [ "n = = 1" ]) ] \r -> do
      case r.result of
        Left (ModuleFailed m) -> map (map at <<< locationsOf) (NonEmptyArray.toArray m.errors) `shouldEqual` [ [ "2:5" ] ]
        _ -> fail "compiled"
      Array.filter (String.contains (String.Pattern "read")) r.log `shouldEqual` [ "read src/A.stel", "read src/A.stel" ]

  it "reads a header without lexing the declarations after it" do
    -- a string left open in a declaration: the header is read, and the
    -- module's compiling reports it
    building [ Tuple "src/A.stel" (moduleOf "A" [] [ "n :: String", "n = \"open" ]) ] \r -> do
      case r.result of
        Left (ModuleFailed m) -> map (map at <<< locationsOf) (NonEmptyArray.toArray m.errors) `shouldEqual` [ [ "3:5" ] ]
        _ -> fail "compiled"
      Array.filter (String.contains (String.Pattern "read")) r.log `shouldEqual` [ "read src/A.stel", "read src/A.stel" ]

  it "takes a line break in a comment for one between items" do
    -- `x` begins an item, the comment before it spanning a line break
    building [ Tuple "src/A.stel" "module A where\n  import B {-\n-}x = \"open" ] \r -> do
      case r.result of
        Left (ModuleFailed m) -> map (map at <<< locationsOf) (NonEmptyArray.toArray m.errors) `shouldEqual` [ [ "3:7" ] ]
        _ -> fail "compiled"
      Array.filter (String.contains (String.Pattern "read")) r.log `shouldEqual` [ "read src/A.stel", "read src/A.stel" ]
