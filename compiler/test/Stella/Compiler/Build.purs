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
import Data.Foldable (foldM, for_)
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
import Stella.Compiler.Macro.Compiled (compiled)
import Stella.Compiler.Macro.Run (ParseOutcome(..), RunParser, defaultSettings)
import Stella.Compiler.Macro.Tree (Position(..), Range(..), SyntaxNode(..), Token(..), TokenTree(..))
import Stella.Compiler.Macro.Tree as Tree
import Stella.Compiler.Build (BackendProblem(..), BuildError(..), SourceRoot, defaultSourceRoots, CompileError(..), CompileWarning, CompilerAction, DiagnosticLocation, EnvironmentProblem(..), PackageFile, SyntaxProblem(..), build, buildMessages, compileModule, defaultHooks, locationsOf, printCompileError, warningLocationOf)
import Stella.Compiler.Surface.Origin as Surface
import Stella.Compiler.TypedCore (Decl(..))
import Stella.Compiler.TypedCore.Kind (Kind(..), monoScheme)
import Stella.Compiler.TypedCore.Name (Ident(..), KindVar(..), ModuleName(..), Qualified(..), Symbol(..), TyName(..))
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

-- | `Base.Int` and `Stella.Syntax`, which a macro's scheme names the types of,
-- | as the compiler compiles them.
syntaxInterfaces :: Array ModuleInterface
syntaxInterfaces = case compiled of
  Right c -> c.moduleInterfaces
  Left _ -> []

-- | `Macros`: `inc : Int -> Int`, and the macros `unwrap` and `failing`.
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

-- | `Ill`, declaring a type `Bad` at `Effect`, a kind no type constructor
-- | produces.
interfaceC :: ModuleInterface
interfaceC =
  { name: ModuleName "Ill"
  , imports: []
  , exports: emptyExports { types = Map.singleton "Bad" { entity: TypeEntity (Qualified (ModuleName "Ill") (TyName "Bad")), via: Declared, members: [] } }
  , declarations: emptyDeclarations
      { types = Map.singleton (TyName "Bad") { kind: monoScheme KEffect, sort: ForeignType, attributes: [] } }
  , implicitHandlers: []
  , catalogOnly: Set.empty
  , arities: Map.empty
  }

moduleA :: ModuleName
moduleA = ModuleName "Macros"

environment :: BuildEnvironment
environment = case foldM (flip addInterface) initialEnvironment (syntaxInterfaces <> [ interfaceA, interfaceC ]) of
  Right env -> env
  Left _ -> initialEnvironment

-- | What each macro does with its input: `unwrap`, and `wrap` of the build,
-- | give back what their brackets hold, and `failing` fails at the input's
-- | first token.
parsers :: RunParser Identity
parsers (Qualified _ (Ident name)) { input } = Identity case name, input.trees of
  n, [ Group _ _ inner _ ] | n == "unwrap" || n == "wrap" -> ParsedAs (Tree.Syntax (map nodeOf inner))
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

-- | What compiling a module gave: its errors, or its warnings, what each phase
-- | handed over — the values the Core binds, and the Mid IR's module — and the
-- | bytecode's module and interface it made.
type Ran = Either (Array CompileError) { warnings :: Array CompileWarning, handed :: Array String, interface :: ModuleInterface }

-- | The module `M`, its lines as given after its header; compiled with the
-- | parsers the table runs, what each phase hands over recorded.
compiling :: Array String -> (Ran -> Aff Unit) -> Aff Unit
compiling = compilingUnder [ "module M where" ]

-- | `compiling`, the module's header the lines given.
compilingUnder :: Array String -> Array String -> (Ran -> Aff Unit) -> Aff Unit
compilingUnder header lines k = do
  handed <- liftEffect (Ref.new [])
  let
    note s = liftEffect (Ref.modify_ (\l -> Array.snoc l s) handed)

    action :: CompilerAction Aff
    action =
      { readSource: \_ -> pure (Left "no file")
      , runParser: \_ q i -> pure (unwrapIdentity (parsers q i))
      , hooks: defaultHooks
          { onElaborated = \core -> note ("core " <> joinWith " " (Array.mapMaybe bound core.decls))
          , onTranslated = \mid -> note ("mid " <> moduleText mid.name)
          }
      }
  r <- compileModule action defaultSettings environment Map.empty (joinWith "\n" (header <> lines))
  recorded <- liftEffect (Ref.read handed)
  k case r of
    Left errors -> Left (NonEmptyArray.toArray errors)
    Right made -> Right { warnings: made.warnings, handed: Array.snoc recorded ("bytecode " <> moduleText made.dmo.name), interface: made.interface }

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
        [ "import Macros"
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

  describe "a module's interface" do
    it "holds the schemes and attributes of what it declares, what it exports, and the arities of what is reached" do
      compilingUnder [ "module M (macro mac, f, Box(..)) where", "import Stella.Syntax (Parser, Syntax, Term, fail)" ]
        [ "data Box a = Box a"
        , "data Poly = Poly (forall (f :: k -> Type) (a :: k). f a -> f a)"
        , "f :: Int -> Int"
        , "f x = x"
        , "@[macro]"
        , "mac :: Parser (Syntax Term)"
        , "mac = fail \"unused\""
        , "hidden :: Int"
        , "hidden = 1"
        ]
        case _ of
          Left errors -> fail (joinWith "; " (map printCompileError errors))
          Right r -> do
            Map.keys r.interface.declarations.values `shouldEqual` Set.fromFoldable (map Ident [ "Box", "Poly", "f", "hidden", "mac" ])
            map _.sort (Map.lookup (Ident "Box") r.interface.declarations.values) `shouldEqual` Just (SortConstructor (Qualified (ModuleName "M") (TyName "Box")))
            map (\t -> t.kind.body) (Map.lookup (TyName "Box") r.interface.declarations.types) `shouldEqual` Just (KFun KType KType)
            -- a kind variable written only in a field is the declaration's
            map _.kind (Map.lookup (TyName "Poly") r.interface.declarations.types) `shouldEqual` Just { kindVars: [ KindVar "k" ], body: KType }
            map _.members (Map.lookup "Box" r.interface.exports.types) `shouldEqual` Just [ Ident "Box" ]
            map _.scheme (Map.lookup (Ident "f") r.interface.declarations.values) `shouldEqual` Just (plainScheme (monoScheme (pureFn int int)))
            map _.attributes (Map.lookup (Ident "mac") r.interface.declarations.values) `shouldEqual` Just [ { name: primAttribute "macro", positional: [], keyword: [] } ]
            Map.keys r.interface.exports.values `shouldEqual` Set.fromFoldable [ "Box", "f" ]
            Map.keys r.interface.exports.macros `shouldEqual` Set.singleton "mac"
            r.interface.arities `shouldEqual` Map.singleton (Ident "f") 1

  describe "a stage reporting an error" do
    it "is a syntax error where the parser stopped" do
      failing [ "f = = 1" ] \errors -> errors `shouldEqual` [ "syntax 2:5" ]

    it "is syntax no later stage reads, where it stands" do
      failing [ "f :: Int ->* Int", "f x = x" ] \errors -> errors `shouldEqual` [ "ill-formed 2:10" ]

    it "is the last that runs: resolution stops what elaboration would report" do
      failing [ "import Macros", "f :: Int", "f = nope", "g :: Int", "g = inc" ] \errors ->
        errors `shouldEqual` [ "resolution 4:5" ]

    it "reports a macro whose parser failed where in its input it failed, then at the call" do
      failing [ "import Macros", "n :: Int", "n = failing%[1]" ] \errors ->
        errors `shouldEqual` [ "resolution 4:14 4:5" ]

    it "reports imports whose interfaces make no signature, at no place" do
      failing [ "import Ill", "n :: Int", "n = 1" ] \errors -> errors `shouldEqual` [ "imports" ]

    it "reports what elaboration refused where it stands" do
      failing [ "import Macros", "bad :: Int", "bad = inc" ] \errors -> errors `shouldEqual` [ "elaboration 4:7" ]

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
building = buildingUnder defaultSourceRoots

-- | `building`, the package's source directories the ones given.
buildingUnder :: Array SourceRoot -> Array (Tuple String String) -> ({ result :: Either BuildError (Array String), log :: Array String } -> Aff Unit) -> Aff Unit
buildingUnder roots sources k = do
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
      , runParser: \built q i -> do
          note (fmt @"parse with {built}" { built: joinWith " " (map moduleText (Array.fromFoldable (Map.keys built))) })
          pure (unwrapIdentity (parsers q i))
      , hooks: defaultHooks
          { onStartCompile = \p f -> note (fmt @"start {current}/{total} {name}" { current: p.current, total: p.total, name: moduleText f.name })
          , onElaborated = \_ -> note "elaborated"
          , onTranslated = \_ -> note "translated"
          , onEnterOptimizeIter = \_ -> note "optimize"
          , onLeaveOptimizeIter = \_ -> note "optimized"
          , onLowered = \b -> note (fmt @"lowered {name}, exporting {values}" { name: moduleText b.dmo.name, values: joinWith " " (Array.fromFoldable (Map.keys b.interface.exports.values)) })
          , onModuleDone = \m -> note ("done " <> moduleText m.name)
          }
      }
  result <- build action defaultSettings environment roots (files :: Array PackageFile)
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
            <> [ "read src/A.stel", "start 1/2 A", "elaborated", "translated", "optimize", "optimized", "lowered A, exporting n", "done A" ]
            <> [ "read test/B.stel", "start 2/2 Test.B", "elaborated", "translated", "optimize", "optimized", "lowered Test.B, exporting n", "done Test.B" ]
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

  it "compiles a module after those of the build it imports, the one given first taken first, against them" do
    building [ Tuple "src/B.stel" (moduleOf "B" [ "A" ] [ "m :: Int", "m = n" ]), Tuple "src/C.stel" (valueModule "C" []), Tuple "src/A.stel" (valueModule "A" []) ] \r -> do
      case r.result of
        Right built -> built `shouldEqual` [ "C", "A", "B" ]
        Left err -> fail (joinWith "; " (map _.message (NonEmptyArray.toArray (buildMessages err))))
      Array.filter (String.contains (String.Pattern "start")) r.log `shouldEqual` [ "start 1/3 C", "start 2/3 A", "start 3/3 B" ]

  describe "a data type of the build" do
    let
      lists exports = moduleOf "A" [] [ "data List a = Nil | Cons a (List a)", "xs :: List Int", "xs = Cons 1 Nil" ]
        # String.replace (String.Pattern "module A where") (String.Replacement (fmt @"module A ({exports}) where" { exports }))
      failedAt r = case r.result of
        Left err -> map (\m -> { path: m.path, at: map at m.locations, message: m.message }) (NonEmptyArray.toArray (buildMessages err))
        Right _ -> []

    it "is used with its constructors by a module importing them" do
      building [ Tuple "src/B.stel" (moduleOf "B" [ "A (List(..))" ] [ "ys :: List Int", "ys = Cons 2 Nil" ]), Tuple "src/A.stel" (lists "List(..), xs") ] \r ->
        case r.result of
          Right built -> built `shouldEqual` [ "A", "B" ]
          Left err -> fail (joinWith "; " (map _.message (NonEmptyArray.toArray (buildMessages err))))

    it "exported without its constructors is used as a type, and its constructors are not in reach" do
      building [ Tuple "src/B.stel" (moduleOf "B" [ "A" ] [ "ys :: List Int", "ys = xs" ]), Tuple "src/A.stel" (lists "List, xs") ] \r ->
        case r.result of
          Right built -> built `shouldEqual` [ "A", "B" ]
          Left err -> fail (joinWith "; " (map _.message (NonEmptyArray.toArray (buildMessages err))))
      building [ Tuple "src/B.stel" (moduleOf "B" [ "A" ] [ "ys :: List Int", "ys = Cons 2 Nil" ]), Tuple "src/A.stel" (lists "List, xs") ] \r ->
        failedAt r `shouldEqual`
          [ { path: Just "src/B.stel", at: [ "4:6" ], message: "There is no constructor `Cons` in scope" }
          , { path: Just "src/B.stel", at: [ "4:13" ], message: "There is no constructor `Nil` in scope" }
          ]

  it "runs a parser with the modules of the build compiled so far, a macro of the build among them and the module compiled not" do
    let
      -- `A` calls a macro of `Macros` while it is compiled, and declares one
      macros = moduleOf "A" [ "Stella.Syntax (Parser, Syntax, Term, fail)", "Macros (macro unwrap)" ]
        [ "k :: Int", "k = unwrap%[1]", "@[macro]", "wrap :: Parser (Syntax Term)", "wrap = fail \"unused\"" ]
    building [ Tuple "src/B.stel" (moduleOf "B" [ "A" ] [ "m :: Int", "m = wrap%[1]" ]), Tuple "src/A.stel" macros ] \r -> do
      case r.result of
        Right built -> built `shouldEqual` [ "A", "B" ]
        Left err -> fail (joinWith "; " (map _.message (NonEmptyArray.toArray (buildMessages err))))
      Array.filter (String.contains (String.Pattern "parse")) r.log `shouldEqual` [ "parse with ", "parse with A" ]

  it "hands over a module's bytecode and interface once the module is in the environment" do
    building [ Tuple "src/A.stel" (valueModule "A" []) ] \r ->
      Array.filter (String.contains (String.Pattern "lowered")) r.log `shouldEqual` [ "lowered A, exporting n" ]

  it "refuses a module named as one the build is compiled against is, before compiling any" do
    building [ Tuple "src/C.stel" (valueModule "C" []), Tuple "src/Macros.stel" (valueModule "Macros" []) ] \r -> do
      case r.result of
        Left (NameInEnvironment e) -> e.path `shouldEqual` "src/Macros.stel"
        _ -> fail "not refused"
      r.log `shouldEqual` []

  it "reports a module importing itself before compiling any, a module being compiled against no interface of its own" do
    building [ Tuple "src/A.stel" (valueModule "A" [ "A" ]) ] \r -> do
      case r.result of
        Left (ImportCycle members) -> map (moduleText <<< _.name) (NonEmptyArray.toArray members) `shouldEqual` [ "A" ]
        _ -> fail "no cycle"
      Array.filter (String.contains (String.Pattern "start")) r.log `shouldEqual` []

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

  it "names a module under the prefix of the source directory it stands in" do
    let roots = defaultSourceRoots <> [ { prefix: [ "Bench", "Fast" ], dir: [ "bench" ] } ]
    buildingUnder roots [ Tuple "bench/A.stel" (valueModule "Bench.Fast.A" []) ] \r -> case r.result of
      Right built -> built `shouldEqual` [ "Bench.Fast.A" ]
      Left _ -> fail "not built"
    -- the name falls under `Bench.Fast`, whose modules `bench` keeps
    buildingUnder roots [ Tuple "src/Bench/Fast/A.stel" (valueModule "Bench.Fast.A" []) ] \r -> case r.result of
      Left (NameReserved e) -> e.owner.dir `shouldEqual` [ "bench" ]
      _ -> fail "not reserved"
    -- `Bench.A` falls under no prefix longer than `src`'s
    buildingUnder roots [ Tuple "src/Bench/A.stel" (valueModule "Bench.A" []) ] \r -> case r.result of
      Right built -> built `shouldEqual` [ "Bench.A" ]
      Left _ -> fail "not built"

  it "refuses source directories that do not name their modules apart" do
    let
      conflicting roots = buildingUnder roots [] \r -> case r.result of
        Left (SourceRootsConflict _) -> pure unit
        _ -> fail "no conflict"
    -- one standing in the other
    conflicting [ { prefix: [], dir: [ "src" ] }, { prefix: [ "Gen" ], dir: [ "src", "gen" ] } ]
    -- two under one prefix
    conflicting [ { prefix: [ "Test" ], dir: [ "test" ] }, { prefix: [ "Test" ], dir: [ "spec" ] } ]
    buildingUnder [ { prefix: [ "bench" ], dir: [ "bench" ] } ] [] \r -> case r.result of
      Left (SourceRootInvalid _) -> pure unit
      _ -> fail "not refused"
