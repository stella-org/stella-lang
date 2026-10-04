-- | Expanding macro calls before resolution, with parsers a table runs: a call
-- | resolved in the macro namespace and inside local opens, what its parser
-- | returned read back as an expression of the expansion and expanded in turn,
-- | and every way a call fails, each reported once where the call stands.
module Test.Stella.Compiler.Macro.Expand (spec) where

import Prelude
import Prim hiding (Type)

import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.Identity (Identity(..))
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Set as Set
import Data.String (joinWith)
import Data.String as String
import Data.Tuple (Tuple(..))
import Effect.Aff (Aff)
import Stella.Compiler.CST (parseModule, printSyntaxError)
import Stella.Compiler.Interface.Environment (BuildEnvironment, addInterface, initialEnvironment)
import Stella.Compiler.Interface.Module (ModuleInterface, ValueSort(..), Via(..), emptyDeclarations, emptyExports)
import Stella.Compiler.Interface.Prim (primAttribute)
import Stella.Compiler.Interface.Scheme (plainScheme)
import Stella.Compiler.Macro.Bundle (syntaxModuleName)
import Stella.Compiler.Macro.Run (ExecutionReason(..), ExpansionSettings, ParseOutcome(..), RunParser, defaultSettings)
import Stella.Compiler.CST.Types (inSource)
import Stella.Compiler.Macro.Tree (OriginRef(..), Position(..), Range(..), Syntax(..), SyntaxItem(..), SyntaxNode(..), Token(..), TokenKind(..), TokenTree(..), Trivia(..))
import Stella.Compiler.Resolve.Module (resolveModuleExpanding)
import Stella.Compiler.Surface.Decl (Declaration(..))
import Stella.Compiler.Surface.Expr (exprOrigin)
import Stella.Compiler.Surface.Origin (Origin(..), rangeOf)
import Stella.Compiler.TypedCore.Kind (monoScheme)
import Stella.Compiler.TypedCore.Name (Ident(..), ModuleName(..), Qualified(..), TyName(..))
import Stella.Compiler.TypedCore.Prim (intTy, pureFn)
import Stella.Compiler.TypedCore.Type (Type(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)
import Test.Stella.Compiler.Resolve.Expr (renderExpr)

-- The modules imported ---------------------------------------------------------------

moduleA :: ModuleName
moduleA = ModuleName "A"

moduleB :: ModuleName
moduleB = ModuleName "B"

int :: Type
int = TCon intTy []

syntaxType :: String -> Type
syntaxType n = TCon (Qualified syntaxModuleName (TyName n)) []

-- | `Parser τ`.
parserOf :: Type -> Type
parserOf = TApp (syntaxType "Parser")

termParser :: Type
termParser = parserOf (TApp (syntaxType "Syntax") (syntaxType "Term"))

-- | A module exporting the macros given, each a parser of terms but `refused`,
-- | a parser of `Int`, and the function `g`.
exporting :: ModuleName -> Array String -> ModuleInterface
exporting name macros =
  { name
  , imports: []
  , exports: emptyExports
      { values = Map.singleton "g" (declared "g")
      , macros = Map.fromFoldable (map (\n -> Tuple n (declared n)) macros)
      }
  , declarations: emptyDeclarations
      { values = Map.fromFoldable
          ( [ Tuple (Ident "g") { sort: SortValue, scheme: plainScheme (monoScheme (pureFn int int)), attributes: [] } ]
              <> map (\n -> Tuple (Ident n) (macro n)) macros
          )
      }
  , implicitHandlers: []
  , catalogOnly: Set.empty
  , arities: Map.empty
  }
  where
  declared n = { entity: Qualified name (Ident n), via: Declared }
  macro n =
    { sort: SortValue
    , scheme: plainScheme (monoScheme (if n == "refused" then parserOf int else termParser))
    , attributes: [ { name: primAttribute "macro", positional: [], keyword: [] } ]
    }

environment :: BuildEnvironment
environment = case addInterface (exporting moduleA macrosOfA) initialEnvironment >>= addInterface (exporting moduleB [ "unwrap" ]) of
  Right env -> env
  Left _ -> initialEnvironment
  where
  macrosOfA = [ "unwrap", "block", "refused", "failing", "broken", "spent", "forged", "misspelled", "relabelled", "glued", "retrivia", "tight" ]

-- The parsers, run as a table ------------------------------------------------------------

-- | What each macro of `A` does with its input, `B.unwrap` doing what `A.unwrap`
-- | does.
parsers :: RunParser Identity
parsers (Qualified _ (Ident name)) { input } = Identity case name, input.trees of
  -- what the brackets hold, as it was written
  "unwrap", [ Group _ _ inner _ ] -> ParsedAs (Syntax (map nodeOf inner))
  -- `let x = e, … in e`, its bindings a layout block
  "block", [ Group _ _ inner _ ] -> ParsedAs (Syntax (block identity inner))
  -- the same, the first token of each binding written with no trivia before it
  "tight", [ Group _ _ inner _ ] -> ParsedAs (Syntax (block (\item -> fromMaybe item (Array.modifyAt 0 untrivia item)) inner))
  "failing", _ -> FailedAs { position: Position 3 9, expected: Set.fromFoldable [ "`,`", "`,`" ], labels: [ "list" ] }
  "broken", _ -> ExecutionFailedAs { reason: Fault, detail: "boom" }
  "spent", _ -> BudgetExceededAs
  -- a token under an origin the host never issued
  "forged", _ -> ParsedAs (Syntax [ SyntaxToken (Token (IntLiteral 1) "1" anywhere [] (OriginRef 999)) ])
  -- the first token of the input, its text no longer the token its kind says
  "misspelled", [ Group _ _ inner _ ] | Just (Leaf (Token kind _ r trivia o)) <- Array.head inner ->
    ParsedAs (Syntax [ SyntaxToken (Token kind "nope" r trivia o) ])
  -- the first token of the input, a name the lexer would read as a number
  "relabelled", [ Group _ _ inner _ ] | Just (Leaf (Token _ _ r trivia o)) <- Array.head inner ->
    ParsedAs (Syntax [ SyntaxToken (Token (LowerName Nothing "1") "1" r trivia o) ])
  -- every token of the input, the trivia between them dropped
  "glued", [ Group _ _ inner _ ] -> ParsedAs (Syntax (map (nodeOf <<< untrivia) inner))
  -- every token of the input, its trivia no whitespace
  "retrivia", [ Group _ _ inner _ ] -> ParsedAs (Syntax (map (nodeOf <<< retrivia) inner))
  _, _ -> FailedAs { position: Position 0 0, expected: Set.empty, labels: [] }
  where
  anywhere = Range (Position 1 1) (Position 1 2)

  block itemAs inner = case Array.uncons inner of
    Just { head: Leaf letToken, tail } ->
      let
        bindings = Array.takeWhile (not <<< isWord "in") tail
        rest = Array.drop (Array.length bindings) tail
        items = map (\item -> SyntaxItem (originOfTree item) (map nodeOf (itemAs item))) (splitAtCommas bindings)
      in
        [ SyntaxToken letToken, SyntaxLayout (originOf letToken) items ] <> map nodeOf rest
    _ -> []

  splitAtCommas trees = Array.filter (not <<< Array.null) (go [] [] trees)
    where
    go acc current ts = case Array.uncons ts of
      Nothing -> Array.snoc acc current
      Just { head, tail }
        | isComma head -> go (Array.snoc acc current) [] tail
        | otherwise -> go acc (Array.snoc current head) tail

  isComma = case _ of
    Leaf (Token Comma _ _ _ _) -> true
    _ -> false

  isWord w = case _ of
    Leaf (Token (LowerName Nothing n) _ _ _ _) -> n == w
    _ -> false

  originOfTree item = case Array.head item of
    Just t -> treeOrigin t
    Nothing -> OriginRef 0

untrivia :: TokenTree -> TokenTree
untrivia = case _ of
  Leaf (Token k t r _ o) -> Leaf (Token k t r [] o)
  other -> other

retrivia :: TokenTree -> TokenTree
retrivia = case _ of
  Leaf (Token k t r leading o) -> Leaf (Token k t r (map (\_ -> Spaces "x" r) leading) o)
  other -> other

-- | A tree as syntax, its tokens and origins kept.
nodeOf :: TokenTree -> SyntaxNode
nodeOf = case _ of
  Leaf t -> SyntaxToken t
  Group d open inner closes -> SyntaxGroup (originOf open) d open (map nodeOf inner) closes

originOf :: Token -> OriginRef
originOf (Token _ _ _ _ o) = o

treeOrigin :: TokenTree -> OriginRef
treeOrigin = case _ of
  Leaf t -> originOf t
  Group _ open _ _ -> originOf open

-- Running a module -------------------------------------------------------------------------

type Out = { body :: String, origin :: Origin, errors :: Array String }

-- | The module `M`, its header importing as the lines given say, and declaring
-- | `f` as the lines given; what `f` was resolved into, and every error.
expanding :: ExpansionSettings -> Array String -> Array String -> (Out -> Aff Unit) -> Aff Unit
expanding settings imports body k = case parseModule (joinWith "\n" ([ "module M where" ] <> imports <> body)) of
  Left e -> fail (printSyntaxError e)
  Right m -> do
    let Identity r = resolveModuleExpanding parsers settings environment m
    case Array.findMap valueF r.module.declarations of
      Nothing -> fail "no f"
      Just d -> k { body: renderExpr d.body, origin: exprOrigin d.body, errors: map show r.errors }
  where
  valueF = case _ of
    DeclValue d | d.name == Qualified (ModuleName "M") (Ident "f") -> Just d
    _ -> Nothing

-- | `f` written on line 3, after `import A as A` and `import A`.
expands :: Array String -> String -> Array String -> Aff Unit
expands body expected errors = expanding defaultSettings [ "import A as A", "import A" ] body \out -> do
  out.body `shouldEqual` expected
  out.errors `shouldEqual` errors

spec :: Spec Unit
spec = describe "Stella.Compiler.Macro.Expand" do
  describe "a call" do
    it "is replaced by what its parser produced, resolved where the call stands" do
      expands [ "f = A.unwrap%[g 1]" ] "(A.g 1)" []
      expands [ "f = unwrap%(1)" ] "1" []

    it "locates what was produced in the expansion, and through it at the input it was written as and at the call" do
      expanding defaultSettings [ "import A" ] [ "f = unwrap%[g 1]" ] \out -> case out.origin of
        FromExpansion e -> do
          rangeOf e.call `shouldEqual` call
          e.written `shouldEqual` FromSource (sourceRange 3 13 16)
          rangeOf out.origin `shouldEqual` call
        other -> fail ("not from an expansion: " <> show other)

    it "reads a layout group as the block the host's own layout makes" do
      expands [ "f = block%[let a = 1, b = a in b]" ] "(let a#0 = 1; b#1 = a#0 in b#1)" []
      -- a virtual token stands between two items, so what begins one is never
      -- read as going on from what ends the other
      expands [ "f = tight%[let a = 1, b = a in b]" ] "(let a#0 = 1; b#1 = a#0 in b#1)" []

    it "expands a call in what an expansion produced, one expansion deeper" do
      expands [ "f = unwrap%[unwrap%[unwrap%[1]]]" ] "1" []
      expanding { budget: 1_000, maxDepth: 2 } [ "import A" ] [ "f = unwrap%[unwrap%[unwrap%[1]]]" ] \out -> do
        out.body `shouldEqual` "!"
        -- the call too deep is the first token the second expansion produced
        out.errors `shouldEqual` [ "ExpansionError 1:1 DepthExceeded 2" ]

  describe "a macro's name" do
    it "is looked up in what the imports bring, and in what an enclosing local open brings" do
      expanding defaultSettings [ "import A as A" ] [ "f = (A.( unwrap%[1] ), import A in unwrap%[2])" ] \out -> do
        out.body `shouldEqual` "(1, 2)"
        out.errors `shouldEqual` []
      expanding defaultSettings [ "import lazy A as L" ] [ "f = L.( unwrap%[1] )" ] \out -> do
        out.body `shouldEqual` "1"
        out.errors `shouldEqual` []

    it "is reported where it stands for no macro, for one of this module, or for several" do
      expanding defaultSettings [ "import A as A" ] [ "f = unwrap%[1]" ] \out ->
        out.errors `shouldEqual` [ "ExpansionError 3:5 MacroNotInScope \"unwrap\"" ]
      expanding defaultSettings [ "import A" ] [ "f = Z.unwrap%[1]" ] \out ->
        out.errors `shouldEqual` [ "ExpansionError 3:5 AliasUnknown \"Z\"" ]
      expanding defaultSettings [ "import A", "import B" ] [ "f = unwrap%[1]" ] \out ->
        out.errors `shouldEqual` [ "ExpansionError 4:5 MacroAmbiguous \"unwrap\" [(Qualified \"A\" \"unwrap\"),(Qualified \"B\" \"unwrap\")]" ]
      expanding defaultSettings [ "import A" ] [ "@[macro]", "mine = g", "f = mine%[1]" ] \out ->
        out.errors `shouldEqual` [ "ExpansionError 5:5 MacroOfThisModule \"mine\"" ]

    it "counts as the module's own only a value declared a macro as the scope declares one" do
      -- `macro` with an argument, under an alias no import declares, or on a
      -- computation, declares no macro
      for_
        [ [ "@[macro 1]", "mine = g" ]
        , [ "@[Other.macro]", "mine = g" ]
        , [ "@[macro]", "mine :: Int / {| |}", "mine = 1" ]
        ]
        \declaring -> expanding defaultSettings [ "import A" ] (declaring <> [ "f = mine%[1]" ]) \out ->
          { notInScope: Array.any (String.contains (String.Pattern "MacroNotInScope \"mine\"")) out.errors
          , own: Array.any (String.contains (String.Pattern "MacroOfThisModule")) out.errors
          }
            `shouldEqual` { notInScope: true, own: false }

  describe "a call that fails" do
    it "is reported once where it stands, and is an invalid expression no later stage reports" do
      expands [ "f = A.refused%[1]" ] "!" [ "ExpansionError 4:5 MacroRefused ((MacroNotAParser (Qualified \"A\" \"refused\") { body: (Plain (TApp (TCon (Qualified \"Stella.Syntax\" \"Parser\") []) (TCon (Qualified \"Prim\" \"Int\") []))), kindVars: [] }))" ]
      expands [ "f = A.failing%[1]" ] "!" [ "ExpansionError 4:5 ParserFailed 3:9 [\"`,`\"] [\"list\"]" ]
      expands [ "f = A.broken%[1]" ] "!" [ "ExpansionError 4:5 ParserNotRun Fault \"boom\"" ]
      expands [ "f = A.spent%[1]" ] "!" [ "ExpansionError 4:5 BudgetSpent 1000000" ]

    it "is one whose syntax the host did not issue, or does not read" do
      expands [ "f = A.forged%[1]" ] "!" [ "ExpansionError 4:5 SyntaxInvalid (OriginNotIssued 999)" ]
      expands [ "f = A.misspelled%[x]" ] "!" [ "ExpansionError 4:5 SyntaxInvalid (NotAsLexed \"nope\")" ]

    it "is one whose tokens, written as they are, the lexer reads otherwise" do
      expands [ "f = A.relabelled%[x]" ] "!" [ "ExpansionError 4:5 SyntaxInvalid (NotAsLexed \"1\")" ]
      -- `g 1`, written with nothing between, is `g1`
      expands [ "f = A.glued%[g 1]" ] "!" [ "ExpansionError 4:5 SyntaxInvalid (NotAsLexed \"g1\")" ]
      expands [ "f = A.retrivia%[g 1]" ] "!" [ "ExpansionError 4:5 SyntaxInvalid (NotAsLexed \"gx1\")" ]
      expanding defaultSettings [ "import A as A", "import A" ] [ "f = A.unwrap%[=]" ] \out -> do
        out.body `shouldEqual` "!"
        map (String.contains (String.Pattern "ExpansionError 4:5 SyntaxInvalid (NotAnExpression (Just \"=\")")) out.errors `shouldEqual` [ true ]

    it "is one that produced an expression written source could not be" do
      expands [ "f = A.unwrap%[(1 :: Int ->* Int)]" ] "!" [ "ExpansionError 4:5 ExpansionIllFormed [\"OperationArrowOutsideOperation\"]" ]
  where
  call = sourceRange 3 5 17

  sourceRange line from to = inSource { line, column: from } { line, column: to }
