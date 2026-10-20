-- | Running parsers in a session: `Stella.Syntax` installed after `Base.Int`, the
-- | combinators executing on token trees read from source, and what a `parse` is
-- | answered with where the parser, its input, or what it returns is not as it
-- | should be.
-- |
-- | The parsers are built from `fixtures/source/parse` against `Stella.Syntax`, with
-- | the `Base` modules of `stella-packages/base`. Two values no well-typed module
-- | holds — a `Parser` around what is not a function, and one around a function
-- | performing an effect — are made by compiling a Core module of data types of its
-- | own and pointing its constructor references at `Stella.Syntax.Parser`.
module Test.E2E.Parse (spec) where

import Prelude hiding (ap)

import Prim as P

import Data.Argonaut.Core (fromNumber, fromObject, fromString, jsonEmptyObject, stringify)
import Data.Array as Array
import Data.Bifunctor (lmap)
import Data.Either (Either(..))
import Data.Foldable (foldMap, foldl, for_, lookup)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.Set as Set
import Data.String as String
import Data.Tuple (Tuple(..))
import Control.Monad.Error.Class (throwError)
import Effect.Aff (Aff)
import Effect.Exception (error)
import Effect.Class (liftEffect)
import Effect.Ref as Ref
import Foreign.Object as Object
import Node.Buffer as Buffer
import Node.FS.Aff as FS
import Run (runBaseEffect)
import Run.Except as Except
import Steam.Foreign (emptyTable, insert)
import Steam.Eval (Outcome(..), applyFunction, invokeClosed, resumePaused)
import Steam.Load (Initialization(..), LoadError(ImportNotLoaded, InitializationHalted), loadWith, Store, emptyStore, globalNamed, load, noIdentities, registryOf)
import Steam.Module (Registry)
import Steam.Value (ForeignOutcome(..), Value(..))
import Effect.Uncurried (mkEffectFn1)
import Stella.CLI.Session.Client (RequestFailure(..), Session)
import Stella.CLI.Session.Client as Client
import Stella.Compiler.Macro.Run (ExecutionReason(..), ParseOutcome(..))
import Stella.CLI.Session.Parse (ParseAnswer(..))
import Stella.CLI.Session.Protocol (Hello, RefusalReason(..))
import Stella.CLI.Session.Syntax (inputOf, readAnswer)
import Stella.CLI.Session.Value (WireValue(..), encodeValue)
import Stella.Compiler.Bytecode (Dmo, encode, lower)
import Stella.Compiler.CST (parseExpr)
import Stella.Compiler.CST.Types as CST
import Stella.Compiler.Elaborate.Environment.Imported (importedSignature)
import Stella.Compiler.Elaborate.Protocol.Guest (commandOp, elabModule, guestAnswerTy, guestCommandTy, kernelEffect)
import Stella.Compiler.Interface (importsOf)
import Stella.Compiler.Interface.Environment (addInterface, initialEnvironment, viewFor)
import Stella.Compiler.Macro.Bundle (syntaxModuleName)
import Stella.Compiler.Macro.Compiled (Compiled, compiled)
import Stella.Compiler.Macro.Tree (Delimiter(..), OriginRef(..), Position(..), Syntax(..), SyntaxNode(..), Token(..), TokenKind(..), TokenTree, treeOf)
import Stella.Compiler.MiddleEnd (translate)
import Stella.Compiler.TypedCore (Decl(..), Export(..), Expr(..), Ident(..), Literal(..), Module, ModuleName(..), Qualified(..), RowEntry(..), RowKey(..), Signature, TyName(..), Type(..), declareAnnotated, monoScheme)
import Stella.Compiler.TypedCore.Prim (fn, intTy, stringTy)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)
import E2E.Build (Sources, builtFrom)
import Node.FS.Perms as Perms
import Test.E2E.Command (requiring)
import Test.E2E.InProcess (openInProcess)
import Test.E2E.Session (hello, node, opened, steamWith, streams)
import Test.E2E.SlowLoud (slowLoud, writeSlowLoud)

-- Core, written short ---------------------------------------------------------------------

syn :: P.String -> Qualified Ident
syn = Qualified syntaxModuleName <<< Ident

ty :: P.String -> Type
ty n = TCon (Qualified syntaxModuleName (TyName n)) []

app :: P.String -> Type -> Type
app n = TApp (ty n)

int :: Type
int = TCon intTy []

string :: Type
string = TCon stringTy []

syntaxTerm :: Type
syntaxTerm = app "Syntax" (ty "Term")

g :: P.String -> P.Array Type -> Expr P.Int
g n = foldl (TyApp 0) (Global 0 (syn n) [])

ap :: Expr P.Int -> P.Array (Expr P.Int) -> Expr P.Int
ap = foldl (App 0)

var :: P.String -> Expr P.Int
var = Var 0 <<< Ident

lit :: P.Int -> Expr P.Int
lit = Lit 0 <<< LitInt

value :: P.String -> Type -> Expr P.Int -> Decl P.Int
value n t e = DeclNonRec 0 { name: Ident n, scheme: monoScheme t, value: e, attributes: [] }

forgedName :: ModuleName
forgedName = ModuleName "Forged"

-- | `Forged`, whose `Box` and `Wrap` become `Stella.Syntax.Parser` once compiled:
-- | `boxed` a parser around an `Int`, and `asking` one around a function that
-- | asks the kernel.
forgedModule :: Module P.Int
forgedModule =
  { annotation: 0
  , name: forgedName
  , imports: [ ModuleName "Stella.Elab", syntaxModuleName ]
  , exports: map (ExportValue <<< Ident) [ "boxed", "asking" ]
  , decls:
      [ dataOf "Box" int
      , dataOf "Wrap" asks
      , value "boxed" (ty' "Box") (ap (Global 0 (forged "Box") []) [ lit 7 ])
      -- what the function returns is built outside it, an application there being
      -- at the row of the function
      , value "asking" (ty' "Wrap") $
          Let 0 (Ident "failed") (app "Reply" syntaxTerm)
            ( ap (g "Err" [ syntaxTerm ])
                [ ap (g "Failure" []) [ ap (g "Position" []) [ lit 1, lit 1 ], g "Nil" [ string ], g "Nil" [ string ] ] ]
            )
            ( ap (Global 0 (forged "Wrap") [])
                [ Lam 0 (Ident "c") (TCon guestCommandTy []) kernel $
                    Let 0 (Ident "answer") (TCon guestAnswerTy [])
                      (Perform 0 (EffectKey kernelEffect) commandOp [] (var "c"))
                      (var "failed")
                ]
            )
      ]
  }
  where
  forged = Qualified forgedName <<< Ident
  ty' n = TCon (Qualified forgedName (TyName n)) []
  kernel = TRowExtend (RowEffectEntry kernelEffect []) TRowEmpty
  asks = fn (TCon guestCommandTy []) kernel (app "Reply" syntaxTerm)
  dataOf n field = DeclData 0
    { name: TyName n
    , kindVars: []
    , params: []
    , constructors: [ { name: Ident n, tag: 0, fields: [ field ] } ]
    , isNewtype: false
    , attributes: []
    }

-- | The module with its constructors pointed at `Stella.Syntax.Parser`.
forging :: Dmo -> Dmo
forging dmo = dmo { ctorRefs = map retarget dmo.ctorRefs }
  where
  retarget q@(Qualified m _)
    | m == forgedName = syn "Parser"
    | otherwise = q

compileAgainst :: Compiled -> (Signature -> Signature) -> Module P.Int -> Either P.String Dmo
compileAgainst syntax extend m = case declareAnnotated (extend syntax.signature) m of
  Left err -> Left ("does not declare: " <> show err.error)
  Right declared -> case importsOf syntax.interfaces of
    Left err -> Left (show err)
    Right imports -> case translate imports m declared of
      Left err -> Left ("does not translate: " <> show err)
      Right mid -> case lower mid of
        Left err -> Left ("does not lower: " <> show err)
        Right out -> Right out.dmo

-- | The signature a module importing `Stella.Syntax` and `Stella.Elab` reads off
-- | the interfaces the compiler carries.
syntaxAndElab :: Compiled -> Either P.String Signature
syntaxAndElab c = do
  env <- lmap show (Array.foldM (flip addInterface) initialEnvironment c.moduleInterfaces)
  view <- lmap show (viewFor [ syntaxModuleName, elabModule ] env)
  lmap show (importedSignature env view)

-- | Where the modules and files this suite reads stand.
dir :: P.String
dir = "e2e/.test-dmo/parse"

pathOf :: P.String -> P.String
pathOf name = dir <> "/" <> name <> ".dmo"

manifestPath :: P.String -> P.String
manifestPath name = dir <> "/" <> name <> ".json"

-- | The modules of the directory of `fixtures/source` given, built, each by its name.
builtNamed :: Sources -> P.String -> Either P.String (P.Array (Tuple P.String Dmo))
builtNamed sources d = builtFrom sources [ d ] <#> map \dmo -> Tuple (moduleText dmo.name) dmo

moduleText :: ModuleName -> P.String
moduleText (ModuleName m) = m

named :: P.String -> P.Array (Tuple P.String Dmo) -> Either P.String Dmo
named name modules = maybe (Left ("no " <> name)) Right (lookup name modules)

-- | The modules the parsers are loaded with, each by its name: `Base.Array` and
-- | `Parsers` built, `Forged` compiled from Core, and the `Base.Int` the compiler
-- | carries; or why one is not made.
parserModules :: Sources -> Compiled -> Either P.String (P.Array (Tuple P.String Dmo))
parserModules sources syntax = do
  built <- builtNamed sources "parse/parsers"
  array <- named "Base.Array" built
  parsers <- named "Parsers" built
  withElab <- syntaxAndElab syntax
  forged <- lmap ("Forged " <> _) (compileAgainst syntax (const withElab) forgedModule)
  base <- maybe (Left "no Base.Int") Right (Array.head syntax.modules)
  pure [ Tuple "Base.Array" array, Tuple "Parsers" parsers, Tuple "Forged" (forging forged), Tuple "Base.Int" base ]

writeParsers :: P.Array (Tuple P.String Dmo) -> P.Array Dmo -> Aff Unit
writeParsers modules hosts = do
  FS.mkdir' dir { recursive: true, mode: Perms.mkPerms Perms.all Perms.all Perms.all }
  for_ modules \(Tuple name dmo) -> write name dmo
  writeSlowLoud dir hosts
  where

  write name dmo = case encode dmo of
    Left err -> fail ("could not encode " <> name <> ": " <> show err)
    Right bytes -> do
      buffer <- liftEffect (Buffer.fromArray bytes)
      FS.writeFile (pathOf name) buffer

-- Talking to a session ---------------------------------------------------------------------

parsing :: Hello
parsing = hello { offers = [ "modules", "parse" ] }

-- | A session served in this process, the parsers loaded.
withSession :: Hello -> (Session -> Aff Unit) -> Aff Unit
withSession h k = openInProcess 1_000 h >>= case _ of
  Left failure -> fail ("the session did not open: " <> show failure)
  Right session -> do
    for [ "Base.Array", "Parsers", "Forged" ] \name ->
      node (Client.load session (pathOf name)) >>= case _ of
        Right (Right _) -> pure unit
        other -> fail ("did not load " <> name <> ": " <> show (map (map (const unit)) other))
    k session
    void (node (Client.close session))
  where
  for xs f = Array.foldM (\_ x -> f x) unit xs

-- | The trees of a macro call written in source, and where they end.
type Call = { trees :: P.Array TokenTree, end :: Position }

callOf :: P.String -> Either P.String Call
callOf src = case parseExpr src of
  Right (CST.ExprMacro m) -> case Array.last m.body of
    Just last -> Right { trees: (treeOf 0 m.body).trees, end: Position last.range.end.line last.range.end.column }
    Nothing -> Left "an empty call"
  _ -> Left ("not a macro call: " <> src)

-- | Run a parser of that module on the call, and the answer as JSON.
answerTo :: Session -> P.String -> P.String -> P.String -> P.Int -> Aff (Either P.String ParseAnswer)
answerTo session m name src budget = case callOf src >>= \c -> inputOf c.trees c.end of
  Left why -> pure (Left why)
  Right input -> node (Client.parse session { parser: { module: m, name }, input, budget }) <#> case _ of
    Left failure -> Left (show failure)
    Right answer -> Right answer

-- | Run a parser of `Parsers` on the call, and the answer in short.
run :: Compiled -> Session -> P.String -> P.String -> P.Int -> Aff P.String
run syntax session name src budget = answerTo session "Parsers" name src budget <#> case _ of
  Left why -> "not answered: " <> why
  Right answer -> case readAnswer syntax.descriptor answer of
    Left why -> "not read: " <> why
    Right outcome -> summary outcome

-- | An outcome in short: the text of each token parsed, where a parser failed and
-- | what it expected there, why one did not execute, or that it ran out of steps.
summary :: ParseOutcome -> P.String
summary = case _ of
  ParsedAs (Syntax nodes) -> "parsed" <> foldMap (" " <> _) (map nodeText nodes)
  FailedAs f -> "failed at " <> show f.position <> " expecting " <> show (Set.toUnfoldable f.expected :: P.Array P.String)
  ExecutionFailedAs f -> "executionFailed " <> show f.reason
  BudgetExceededAs -> "budgetExceeded"
  where
  nodeText = case _ of
    SyntaxToken (Token _ text _ _ _) -> text
    _ -> "(group)"

reasonOf :: Either P.String ParseAnswer -> Maybe ExecutionReason
reasonOf = case _ of
  Right (ExecutionFailed f) -> Just f.reason
  _ -> Nothing

-- | Where `quotedSplice` writes its antiquotation: the origin a splice of it
-- | carries, as `Parsers` the module and the range of `$(…)`.
antiquoted :: Sources -> OriginRef
antiquoted sources = case Map.lookup "fixtures/source/parse/parsers/Parsers.stel" sources.files of
  Nothing -> QuotedOrigin "Parsers" (Position 0 0) (Position 0 0)
  Just text -> fromMaybe (QuotedOrigin "Parsers" (Position 0 0) (Position 0 0)) do
    let lines = String.split (String.Pattern "\n") text
    line <- Array.findIndex (String.contains (String.Pattern written)) lines
    column <- String.indexOf (String.Pattern written) =<< Array.index lines line
    pure (QuotedOrigin "Parsers" (Position (line + 1) (column + 1)) (Position (line + 1) (column + 1 + String.length written)))
  where
  written = "$(S.Syntax (S.nodesOf ts))"

-- Cases ---------------------------------------------------------------------------------------

spec :: Sources -> Spec Unit
spec sources = describe "steam session, parsing" case compiled of
  Left err -> it "compiles Stella.Syntax" (fail err)
  Right syntax -> requiring (Tuple <$> parserModules sources syntax <*> slowLoud sources) \(Tuple modules hosts) -> do
    it "writes the fixture" (writeParsers modules hosts)

    describe "opening" do
      it "installs Base.Int and then Stella.Syntax through the loader, before it is ready" do
        withSession parsing \session -> do
          (Client.ready session).capabilities `shouldEqual` [ "modules", "parse" ]
          run syntax session "names" "m%[a, b]" 100_000 >>= shouldEqual "parsed a b"
          -- the one the session installed is the one there is
          node (Client.load session (pathOf "Base.Int")) >>= case _ of
            Right (Left f) -> String.contains (String.Pattern "ModuleTwice") f.detail `shouldEqual` true
            other -> fail ("loaded a second Base.Int: " <> show (map (map (const unit)) other))

      it "does not load Stella.Syntax where Base.Int is not loaded" do
        case Array.index syntax.modules 1 of
          Nothing -> fail "no Stella.Syntax"
          Just dmo -> do
            store <- liftEffect (emptyStore emptyTable <$> Ref.new noIdentities)
            outcome <- liftEffect (runBaseEffect (Except.runExcept (load store dmo)))
            case outcome of
              Left (ImportNotLoaded m) -> m `shouldEqual` ModuleName "Base.Int"
              Left err -> fail ("refused otherwise: " <> show err)
              Right _ -> fail "loaded"

      it "puts parse in force only beside modules, and refuses to open requiring it alone" do
        openInProcess 1_000 (hello { offers = [ "parse" ] }) >>= case _ of
          Left failure -> fail (show failure)
          Right session -> do
            (Client.ready session).capabilities `shouldEqual` []
            input <- case callOf "m%[a]" >>= \c -> inputOf c.trees c.end of
              Left why -> fail why *> pure { trees: jsonEmptyObject, end: jsonEmptyObject }
              Right input -> pure input
            node (Client.parse session { parser: { module: "Parsers", name: "names" }, input, budget: 1 }) >>= case _ of
              Left (RequestRefused e) -> e.code `shouldEqual` "capabilityNotInForce"
              _ -> fail "parsed outside the capability"
            void (node (Client.close session))
        openInProcess 1_000 (hello { requires = [ "parse" ] }) >>= case _ of
          Left (Client.Refused refusal) -> refusal.reason `shouldEqual` CapabilityIncomplete
          other -> fail ("opened: " <> show (map (const unit) other))

    describe "the combinators" do
      it "read a group whole, by what separates its items" do
        withSession parsing \session -> do
          run syntax session "names" "m%[a, b]" 100_000 >>= shouldEqual "parsed a b"
          run syntax session "names" "m%[]" 100_000 >>= shouldEqual "parsed"
          run syntax session "names" "m%[a b]" 100_000 >>= shouldEqual "failed at (Position 1 6) expecting [\"the end\"]"

      it "fold a list from the right and from the left" do
        withSession parsing \session -> do
          run syntax session "rebuilt" "m%[a, b]" 100_000 >>= shouldEqual "parsed a b"
          run syntax session "reversed" "m%[a, b]" 100_000 >>= shouldEqual "parsed b a"

      it "splice syntax in parentheses standing where a quotation's origin does, which crosses as the constructor it is" do
        withSession parsing \session -> answerTo session "Parsers" "quotedSplice" "m%[a, b]" 100_000 >>= case _ of
          Left why -> fail why
          Right answer -> case readAnswer syntax.descriptor answer of
            Right (ParsedAs (Syntax [ SyntaxGroup origin Paren (Token GroupBracket "(" _ _ _) inner [ Token GroupBracket ")" _ _ _ ] ])) -> do
              -- the range of the antiquotation as `Parsers` writes it
              origin `shouldEqual` antiquoted sources
              Array.length inner `shouldEqual` 2
            other -> fail ("not one parenthesized group: " <> show (map summary other))

      it "begin an item of a layout block where a line break stands in a comment" do
        withSession parsing \session -> do
          run syntax session "items" "m%[a {-\n -}b]" 100_000 >>= shouldEqual "parsed a b"
          run syntax session "items" "m%[a {- -} b]" 100_000 >>= shouldEqual "failed at (Position 1 12) expecting [\"the end\"]"

      it "take what two alternatives failing at one position expected as a set" do
        withSession parsing \session -> do
          answerTo session "Parsers" "twice" "m%[x]" 100_000 >>= case _ of
            Right (ParseFailed json) -> Array.length (String.split (String.Pattern "`,`") (stringify json)) `shouldEqual` 3
            other -> fail ("not a failure: " <> show (map (const unit) other))
          run syntax session "twice" "m%[x]" 100_000 >>= shouldEqual "failed at (Position 1 3) expecting [\"`,`\"]"

      it "fail a repetition of a parser that reads nothing" do
        withSession parsing \session ->
          run syntax session "stuck" "m%[x]" 100_000 >>= shouldEqual
            "failed at (Position 1 3) expecting [\"progress: `many` repeats a parser that read nothing\"]"

    closedSpec sources
    initializationSpec sources

    describe "a session running parsers" do
      it "refuses a module declaring a foreign the host carries out, before reaching it or initializing the module" do
        s <- streams
        opened (steamWith [ "--manifest", manifestPath "slow-loud" ] s parsing) \session -> do
          for_ [ "Loud", "Slow" ] \name ->
            node (Client.load session (pathOf name)) >>= case _ of
              Right (Left f) -> String.contains (String.Pattern "the host carries out") f.detail `shouldEqual` true
              other -> fail ("loaded " <> name <> ": " <> show (map (map (const unit)) other))
          void (node (Client.close session))
        err <- liftEffect (Ref.read s.stderr)
        String.contains (String.Pattern "slow reached") err `shouldEqual` false
        String.contains (String.Pattern "shouted") err `shouldEqual` false
        -- where no parser runs, the same module is loaded and initialized
        t <- streams
        opened (steamWith [ "--manifest", manifestPath "slow-loud" ] t (hello { offers = [ "modules" ] })) \session -> do
          node (Client.load session (pathOf "Loud")) >>= case _ of
            Right (Right _) -> pure unit
            other -> fail ("not loaded: " <> show (map (map (const unit)) other))
          void (node (Client.close session))
        liftEffect (Ref.read t.stderr) >>= \e -> String.contains (String.Pattern "shouted") e `shouldEqual` true

      it "runs a parser using an array it made, and refuses one reaching an array made before it" do
        withSession parsing \session -> do
          run syntax session "ownArray" "m%[]" 100_000 >>= shouldEqual "parsed"
          reasonOf <$> answerTo session "Parsers" "readsTable" "m%[]" 100_000 >>= shouldEqual (Just StateRequested)

    describe "what a parse is answered with" do
      it "a parser faulting, or running out of steps" do
        withSession parsing \session -> do
          run syntax session "faulting" "m%[]" 100_000 >>= shouldEqual "executionFailed Fault"
          run syntax session "spinning" "m%[]" 10_000 >>= shouldEqual "budgetExceeded"

      it "the steps a parse takes, exactly" do
        withSession parsing \session -> do
          let
            parses budget = run syntax session "names" "m%[a, b]" budget <#> (_ == "parsed a b")
            least lo hi
              | lo >= hi = pure hi
              | otherwise = do
                  let mid = (lo + hi) / 2
                  ok <- parses mid
                  if ok then least lo mid else least (mid + 1) hi
          k <- least 1 100_000
          run syntax session "names" "m%[a, b]" k >>= shouldEqual "parsed a b"
          run syntax session "names" "m%[a, b]" (k - 1) >>= shouldEqual "budgetExceeded"

      it "a global that holds no parser, or one around no function" do
        withSession parsing \session -> do
          reasonOf <$> answerTo session "Parsers" "identity" "m%[]" 1_000 >>= shouldEqual (Just NotAParser)
          reasonOf <$> answerTo session "Forged" "boxed" "m%[]" 1_000 >>= shouldEqual (Just ParserNotCallable)
          reasonOf <$> answerTo session "Nowhere" "names" "m%[]" 1_000 >>= shouldEqual (Just NoSuchModule)
          reasonOf <$> answerTo session "Parsers" "nothing" "m%[]" 1_000 >>= shouldEqual (Just NoSuchGlobal)

      it "a parser returning what is not syntax" do
        withSession parsing \session ->
          reasonOf <$> answerTo session "Parsers" "seven" "m%[]" 1_000 >>= shouldEqual (Just ResultInvalid)

      it "input that is no canonical value, or none of the type its place wants" do
        withSession parsing \session -> do
          let
            parseWith input = node (Client.parse session { parser: { module: "Parsers", name: "names" }, input, budget: 1_000 }) <#> case _ of
              Right (ExecutionFailed f) -> Just f.reason
              _ -> Nothing
            canonical w = case encodeValue w of
              Right json -> json
              Left _ -> jsonEmptyObject
            end = canonical (WData (syn "Position") [ WInt 1, WInt 1 ])
          parseWith { trees: canonical (WInt 1), end } >>= shouldEqual (Just InputInvalid)
          parseWith { trees: fromObject (Object.singleton "bogus" (fromNumber 1.0)), end } >>= shouldEqual (Just InputInvalid)
          parseWith { trees: canonical (WData (syn "Nil") []), end: fromString "end" } >>= shouldEqual (Just InputInvalid)

      it "an effect a parser handles nowhere, which never reaches the kernel" do
        withSession (hello { offers = [ "modules", "invoke", "kernel", "parse" ] }) \session ->
          reasonOf <$> answerTo session "Forged" "asking" "m%[]" 1_000 >>= shouldEqual (Just EffectRequested)

-- A closed run, on the machine --------------------------------------------------------------

hostedName :: ModuleName
hostedName = ModuleName "Hosted"

arraysName :: ModuleName
arraysName = ModuleName "Arrays"

-- | `Base.Array`, `Hosted`, and `Arrays` loaded, `Hosted.echo` counting its calls.
type Machine = { registry :: Registry, store :: Store, calls :: Ref.Ref P.Int }

-- | The modules of `fixtures/source/parse/closed` built and loaded, in the order
-- | built, `Hosted.echo` counting its calls.
machine :: Sources -> Aff Machine
machine sources = case builtFrom sources [ "parse/closed" ] of
  Left err -> failing err
  Right modules -> do
    calls <- liftEffect (Ref.new 0)
    let
      echo = mkEffectFn1 \args -> do
        Ref.modify_ (_ + 1) calls
        pure (Produced (fromMaybe (VInt 0) (Array.head args)))
      table = insert (Qualified hostedName (Ident "echo")) { arity: 1, body: echo } emptyTable
    start <- liftEffect (emptyStore table <$> Ref.new noIdentities)
    loaded <- liftEffect (runBaseEffect (Except.runExcept (Array.foldM load start modules)))
    case loaded of
      Left err -> failing (show err)
      Right store -> pure { registry: registryOf store, store, calls }

-- | A function of the machine, run closed on `n` in stretches of `stretch` steps,
-- | to how it ended.
closedRun :: Machine -> ModuleName -> P.String -> P.Int -> P.Int -> Aff P.String
closedRun m mod name n stretch = case globalNamed m.store (Qualified mod (Ident name)) of
  Nothing -> pure "no such global"
  Just slot -> liftEffect do
    held <- Ref.read slot
    case held of
      Nothing -> pure "empty"
      Just f -> runBaseEffect (Except.runExcept (invokeClosed m.registry stretch f [ VInt n ])) >>= go
  where
  go = case _ of
    Left failure -> pure ("failed " <> show failure)
    Right slice -> case slice.outcome of
      Done (VInt k) -> pure ("done " <> show k)
      Done _ -> pure "done"
      Halted halt -> pure ("halted " <> show halt)
      Paused pause -> runBaseEffect (Except.runExcept (resumePaused stretch pause)) >>= go
      Asked _ _ -> pure "asked"

-- | A test ending here, with what went wrong.
failing :: forall a. P.String -> Aff a
failing = throwError <<< error

-- | The same, run open: what the machine gives a program that is not a parser.
openRun :: Machine -> ModuleName -> P.String -> P.Int -> Aff P.String
openRun m mod name n = case globalNamed m.store (Qualified mod (Ident name)) of
  Nothing -> pure "no such global"
  Just slot -> liftEffect do
    held <- Ref.read slot
    case held of
      Just f -> runBaseEffect (Except.runExcept (applyFunction m.registry f [ VInt n ])) <#> case _ of
        Right (VInt k) -> "done " <> show k
        Right _ -> "done"
        Left failure -> "failed " <> show failure
      Nothing -> pure "empty"

closedSpec :: Sources -> Spec Unit
closedSpec sources = describe "a closed run" do
  it "halts at a foreign the host carries out, the host never reached" do
    m <- machine sources
    closedRun m hostedName "callsEcho" 3 1_000 >>= shouldEqual "halted (HostForeignCalled (Qualified \"Hosted\" \"echo\"))"
    liftEffect (Ref.read m.calls) >>= shouldEqual 0
    -- run open, the same function reaches it
    openRun m hostedName "callsEcho" 3 >>= shouldEqual "done 3"
    liftEffect (Ref.read m.calls) >>= shouldEqual 1

  it "reaches no array it did not make, to read, to measure, or to write" do
    m <- machine sources
    closedRun m arraysName "reads" 0 1_000 >>= shouldEqual "halted (StateNotOwned ArrayUnsafeIndex)"
    closedRun m arraysName "measures" 0 1_000 >>= shouldEqual "halted (StateNotOwned ArrayLength)"
    closedRun m arraysName "writes" 9 1_000 >>= shouldEqual "halted (StateNotOwned ArrayUnsafeSet)"
    -- and nothing was written
    openRun m arraysName "reads" 0 >>= shouldEqual "done 7"

  it "uses an array it made, across every pause" do
    m <- machine sources
    closedRun m arraysName "keepsOwn" 5 1_000 >>= shouldEqual "done 5"
    closedRun m arraysName "keepsOwn" 5 1 >>= shouldEqual "done 5"
    -- what one run made is not the next run's
    closedRun m arraysName "reads" 0 1 >>= shouldEqual "halted (StateNotOwned ArrayUnsafeIndex)"

-- Initialization, closed ---------------------------------------------------------------------

-- | `Base.Array`, `Shared`, `Snapshot`, and `Writer`, built from
-- | `fixtures/source/parse/initialization`.
initializing :: Sources -> Either P.String { array :: Dmo, shared :: Dmo, snapshot :: Dmo, writer :: Dmo }
initializing sources = do
  built <- builtNamed sources "parse/initialization"
  array <- named "Base.Array" built
  shared <- named "Shared" built
  snapshot <- named "Snapshot" built
  writer <- named "Writer" built
  pure { array, shared, snapshot, writer }

-- | Load the modules in order, each initialized as given, to how the last load
-- | ended.
loadedAs :: Initialization -> P.Array Dmo -> Aff P.String
loadedAs initialization dmos = liftEffect do
  start <- emptyStore emptyTable <$> Ref.new noIdentities
  outcome <- runBaseEffect (Except.runExcept (Array.foldM (loadWith initialization) start dmos))
  pure case outcome of
    Right _ -> "loaded"
    Left (InitializationHalted (Qualified _ (Ident name)) halt) -> name <> " halted " <> show halt
    Left err -> show err

initializationSpec :: Sources -> Spec Unit
initializationSpec sources = describe "a closed initialization" do
  it "reaches the arrays its own module makes, and no other" do
    case initializing sources of
      Left err -> fail err
      Right m -> do
        loadedAs ClosedInitialization [ m.array, m.shared ] >>= shouldEqual "loaded"
        loadedAs ClosedInitialization [ m.array, m.shared, m.snapshot ] >>= shouldEqual "reached halted (StateNotOwned ArrayUnsafeIndex)"
        loadedAs ClosedInitialization [ m.array, m.shared, m.writer ] >>= shouldEqual "reached halted (StateNotOwned ArrayUnsafeSet)"
        -- initialized open, both reach it
        loadedAs OpenInitialization [ m.array, m.shared, m.snapshot ] >>= shouldEqual "loaded"
        loadedAs OpenInitialization [ m.array, m.shared, m.writer ] >>= shouldEqual "loaded"

  it "keeps a session running parsers from taking in what an invocation wrote" do
    case initializing sources of
      Left err -> fail err
      Right m -> do
        let
          write name dmo = case encode dmo of
            Left err -> fail (show err)
            Right bytes -> do
              buffer <- liftEffect (Buffer.fromArray bytes)
              FS.writeFile (pathOf name) buffer
        write "Base.Array" m.array
        write "Shared" m.shared
        write "Snapshot" m.snapshot
        openInProcess 1_000 (hello { offers = [ "modules", "invoke", "parse" ] }) >>= case _ of
          Left failure -> fail (show failure)
          Right session -> do
            for_ [ "Base.Array", "Shared" ] \name ->
              node (Client.load session (pathOf name)) >>= case _ of
                Right (Right _) -> pure unit
                other -> fail ("did not load " <> name <> ": " <> show (map (map (const unit)) other))
            -- the invocation writes the array, as an open run may
            let token = Object.singleton "slot" (fromNumber 1.0)
            node (Client.invoke session { global: { module: "Shared", name: "bump" }, arguments: [ token ], attempt: 1, budget: 1_000 }) >>= case _ of
              Right (Right _) -> pure unit
              other -> fail ("not invoked: " <> show (map (map (const unit)) other))
            -- and a module initialized after it does not see what it wrote
            node (Client.load session (pathOf "Snapshot")) >>= case _ of
              Right (Left f) -> String.contains (String.Pattern "StateNotOwned") f.detail `shouldEqual` true
              other -> fail ("loaded Snapshot: " <> show (map (map (const unit)) other))
            void (node (Client.close session))
