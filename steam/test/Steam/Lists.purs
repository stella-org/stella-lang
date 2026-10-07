-- | Modules written in source, calling a macro of a module written in Core or
-- | of a module of the same build, compiled by the build driver with each
-- | parser run on a session, then loaded and run: the front end end to end.
-- |
-- | A macro of the build runs from the bytecode the build wrote for its module,
-- | which the session loads before the parser is run.
-- |
-- | `Lists` declares `List` and the macro `ls`, which reads `[ e, … ]` and gives
-- | back `Cons (e) (Cons (…) Nil)`. The elements keep their tokens and origins;
-- | what the macro makes up — `Cons`, `Nil`, and the parentheses — stands where
-- | the call's bracket does. The names it writes are not qualified: they are
-- | resolved where the call stands, so a module calling `ls` imports `Lists`.
module Test.Steam.Lists (spec) where

import Prelude hiding (ap)

import Prim as P

import Data.Array as Array
import Data.Array.NonEmpty as NonEmptyArray
import Data.Either (Either(..))
import Data.Foldable (foldM, foldl, foldr)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Data.String (joinWith)
import Data.String as String
import Data.Tuple (Tuple(..))
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Ref as Ref
import Fmt (fmt)
import Node.Buffer as Buffer
import Node.FS.Aff as FS
import Run (AFF, EFFECT, Run, liftAff, runBaseEffect)
import Run.Except (EXCEPT)
import Run.Except as Except
import Steam.Foreign (emptyTable)
import Steam.Load (emptyStore, globalNamed, load, noIdentities)
import Steam.Value (CtorId, Value(..))
import Stella.CLI.Session.Client as Client
import Stella.CLI.Effect.Process (PROCESS)
import Stella.CLI.Session.RunParser (ParserRunnerError(..), loadingParser)
import Stella.Compiler.Build (CompilerAction, build, buildMessages, defaultHooks, defaultSourceRoots)
import Stella.Compiler.Bytecode (Dmo, encode, lower)
import Stella.Compiler.Interface (aritiesOf, importsOf)
import Stella.Compiler.Interface.Environment (addInterface, initialEnvironment)
import Stella.Compiler.Interface.FromCore (interfaceOfCore)
import Stella.Compiler.Interface.Module (ModuleInterface)
import Stella.Compiler.Interface.Prim (primAttribute)
import Stella.Compiler.Macro.Bundle (syntaxModuleName)
import Stella.Compiler.Macro.Compiled (Compiled, compiled)
import Stella.Compiler.Macro.Run (defaultSettings)
import Stella.Compiler.MiddleEnd (translate)
import Stella.Compiler.TypedCore (DecisionTree(..), Decl(..), Export(..), Expr(..), Ident(..), Kind(..), Literal(..), Module, ModuleName(..), Occurrence(..), Qualified(..), TyName(..), TyVar(..), Type(..), declareAnnotated, monoScheme, scalarString)
import Stella.Compiler.TypedCore.Prim (booleanTy, pureFn, stringTy)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)
import Test.Steam.Command (pathOf, writeModules)
import Test.Steam.InProcess (openInProcess)
import Test.Steam.Session (hello, node)
import Type.Row (type (+))

-- Core, written short ---------------------------------------------------------------------

listsName :: ModuleName
listsName = ModuleName "Lists"

syn :: P.String -> Qualified Ident
syn = Qualified syntaxModuleName <<< Ident

own :: P.String -> Expr P.Int
own n = Global 0 (Qualified listsName (Ident n)) []

ty :: P.String -> Type
ty n = TCon (Qualified syntaxModuleName (TyName n)) []

-- | `Stella.Syntax.List τ`.
listOf :: Type -> Type
listOf = TApp (ty "List")

string :: Type
string = TCon stringTy []

tree :: Type
tree = ty "TokenTree"

token :: Type
token = ty "Token"

syntaxNode :: Type
syntaxNode = ty "SyntaxNode"

syntaxTerm :: Type
syntaxTerm = TApp (ty "Syntax") (ty "Term")

g :: P.String -> P.Array Type -> Expr P.Int
g n = foldl (TyApp 0) (Global 0 (syn n) [])

ap :: Expr P.Int -> P.Array (Expr P.Int) -> Expr P.Int
ap = foldl (App 0)

call :: P.String -> P.Array Type -> P.Array (Expr P.Int) -> Expr P.Int
call n tys = ap (g n tys)

lam :: P.Array (Tuple P.String Type) -> Expr P.Int -> Expr P.Int
lam ps body = foldr (\(Tuple x t) e -> Lam 0 (Ident x) t e) body ps

v :: P.String -> Expr P.Int
v = Var 0 <<< Ident

text :: P.String -> Expr P.Int
text s = case scalarString s of
  Just str -> Lit 0 (LitString str)
  Nothing -> Lit 0 (LitInt 0)

nil :: Type -> Expr P.Int
nil a = g "Nil" [ a ]

cons :: Type -> Expr P.Int -> Expr P.Int -> Expr P.Int
cons a x xs = call "Cons" [ a ] [ x, xs ]

-- | A case on the constructors of `Stella.Syntax`: a constructor, a variable for
-- | each field (`_` binding none), and the body; and what else the case gives.
match :: Expr P.Int -> P.Array { ctor :: P.String, fields :: P.Array P.String, body :: Expr P.Int } -> Maybe (Expr P.Int) -> Expr P.Int
match e branches fallback = Case 0 [ e ] (SwitchCtor (OccScrutinee 0) (map treeOf branches) (map Leaf fallback))
  where
  treeOf b = { ctor: syn b.ctor, tree: foldr (bind b.ctor) (Leaf b.body) (Array.mapWithIndex Tuple b.fields) }
  bind c (Tuple i x) inner
    | x == "_" = inner
    | otherwise = Bind (Ident x) (OccField (OccScrutinee 0) (syn c) i) inner

ifThenElse :: Expr P.Int -> Expr P.Int -> Expr P.Int -> Expr P.Int
ifThenElse cond yes no = Case 0 [ cond ] (SwitchLit (OccScrutinee 0) [ { lit: LitBoolean true, tree: Leaf yes } ] (Leaf no))

-- | `τ1 -> … -> τn -> τ`, with pure arrows.
fns :: P.Array Type -> Type -> Type
fns args result = foldr pureFn result args

-- The module ------------------------------------------------------------------------------

-- | `Lists`: `data List a = Nil | Cons a (List a)`, and `@[macro] ls`.
listsModule :: Module P.Int
listsModule =
  { annotation: 0
  , name: listsName
  , imports: [ syntaxModuleName ]
  , exports: [ ExportType (TyName "List"), ExportCtor (Ident "Nil"), ExportCtor (Ident "Cons"), ExportValue (Ident "ls") ]
  , decls:
      [ DeclData 0
          { name: TyName "List"
          , kindVars: []
          , params: [ { name: TyVar "a", kind: KType } ]
          , constructors:
              [ { name: Ident "Nil", tag: 0, fields: [] }
              , { name: Ident "Cons", tag: 1, fields: [ TVar (TyVar "a"), TApp (TCon (Qualified listsName (TyName "List")) []) (TVar (TyVar "a")) ] }
              ]
          , isNewtype: false
          , attributes: []
          }
      -- the trees of an element: those before the first comma
      , recursive "takeElement" (pureFn (listOf tree) (listOf tree)) $ lam [ Tuple "ts" (listOf tree) ] $
          match (v "ts")
            [ { ctor: "Nil", fields: [], body: nil tree }
            , { ctor: "Cons", fields: [ "t", "rest" ], body: ifThenElse (call "isComma" [] [ v "t" ]) (nil tree) (cons tree (v "t") (ap (own "takeElement") [ v "rest" ])) }
            ]
            Nothing
      -- the trees after the first comma
      , recursive "dropElement" (pureFn (listOf tree) (listOf tree)) $ lam [ Tuple "ts" (listOf tree) ] $
          match (v "ts")
            [ { ctor: "Nil", fields: [], body: nil tree }
            , { ctor: "Cons", fields: [ "t", "rest" ], body: ifThenElse (call "isComma" [] [ v "t" ]) (v "rest") (ap (own "dropElement") [ v "rest" ]) }
            ]
            Nothing
      -- a token made up, standing where the token given does, after a space
      , value "madeUp" (fns [ ty "TokenKind", string, token ] token) $ lam [ Tuple "kind" (ty "TokenKind"), Tuple "text" string, Tuple "at" token ] $
          match (v "at")
            [ { ctor: "Token"
              , fields: [ "_", "_", "range", "_", "origin" ]
              , body: call "Token" [] [ v "kind", v "text", v "range", cons (ty "Trivia") (call "Spaces" [] [ text " ", v "range" ]) (nil (ty "Trivia")), v "origin" ]
              }
            ]
            Nothing
      -- `( nodes )`, made up where the token given stands
      , value "parenthesized" (fns [ token, listOf syntaxNode ] syntaxNode) $ lam [ Tuple "at" token, Tuple "nodes" (listOf syntaxNode) ] $
          call "SyntaxGroup" []
            [ call "originOf" [] [ v "at" ]
            , g "Paren" []
            , ap (own "madeUp") [ g "GroupBracket" [], text "(", v "at" ]
            , v "nodes"
            , cons token (ap (own "madeUp") [ g "GroupBracket" [], text ")", v "at" ]) (nil token)
            ]
      , value "named" (fns [ string, token ] syntaxNode) $ lam [ Tuple "name" string, Tuple "at" token ] $
          call "SyntaxToken" [] [ ap (own "madeUp") [ call "UpperName" [] [ g "Nothing" [ string ], v "name" ], v "name", v "at" ] ]
      -- `Cons (e) (Cons (…) Nil)` of the elements the trees hold
      , recursive "listOf" (fns [ token, listOf tree ] (listOf syntaxNode)) $ lam [ Tuple "at" token, Tuple "ts" (listOf tree) ] $
          match (v "ts")
            [ { ctor: "Nil", fields: [], body: cons syntaxNode (ap (own "named") [ text "Nil", v "at" ]) (nil syntaxNode) }
            , { ctor: "Cons"
              , fields: [ "_", "_" ]
              , body:
                  cons syntaxNode (ap (own "named") [ text "Cons", v "at" ])
                    $ cons syntaxNode (ap (own "parenthesized") [ v "at", call "nodesOf" [] [ ap (own "takeElement") [ v "ts" ] ] ])
                    $ cons syntaxNode (ap (own "parenthesized") [ v "at", ap (own "listOf") [ v "at", ap (own "dropElement") [ v "ts" ] ] ])
                    $ nil syntaxNode
              }
            ]
            Nothing
      , value "isBracketGroup" (pureFn tree (TCon booleanTy [])) $ lam [ Tuple "t" tree ] $
          match (v "t") [ { ctor: "Group", fields: [ "d", "_", "_", "_" ], body: call "isBracket" [] [ v "d" ] } ] (Just (Lit 0 (LitBoolean false)))
      , value "build" (pureFn tree syntaxTerm) $ lam [ Tuple "t" tree ] $
          match (v "t")
            [ { ctor: "Group", fields: [ "_", "open", "inner", "_" ], body: call "Syntax" [ ty "Term" ] [ ap (own "listOf") [ v "open", v "inner" ] ] } ]
            (Just (call "Syntax" [ ty "Term" ] [ nil syntaxNode ]))
      , DeclNonRec 0
          { name: Ident "ls"
          , scheme: monoScheme (TApp (ty "Parser") syntaxTerm)
          , value: call "map" [ tree, syntaxTerm ] [ own "build", call "satisfy" [] [ text "`[`", own "isBracketGroup" ] ]
          , attributes: [ { name: primAttribute "macro", positional: [], keyword: [] } ]
          }
      ]
  }
  where
  value n t e = DeclNonRec 0 { name: Ident n, scheme: monoScheme t, value: e, attributes: [] }
  recursive n t e = DeclRec 0 [ { name: Ident n, scheme: monoScheme t, value: e, attributes: [] } ]

-- | `Lists` compiled against `Stella.Syntax`, and its interface.
compiledLists :: Compiled -> Either P.String { dmo :: Dmo, interface :: ModuleInterface }
compiledLists syntax = case declareAnnotated syntax.signature listsModule of
  Left err -> Left ("does not declare: " <> show err.error)
  Right declared -> case importsOf syntax.interfaces of
    Left err -> Left (show err)
    Right imports -> case translate imports listsModule declared of
      Left err -> Left ("does not translate: " <> show err)
      Right mid -> case lower mid of
        Left err -> Left ("does not lower: " <> show err)
        Right out -> case interfaceOfCore listsModule declared (Map.filterKeys (\x -> Array.elem (ExportValue x) listsModule.exports) (aritiesOf mid.module)) of
          Left err -> Left ("has no interface: " <> show err)
          Right interface -> Right { dmo: out.dmo, interface }

-- Building and running ----------------------------------------------------------------------

type Ran = { result :: Either P.String (P.Array P.String), values :: Map.Map P.String P.String }

-- | `src/Main.stel`, its lines after its header importing `Lists`, built as
-- | `building` builds a package.
buildingMain :: P.Array P.String -> P.Array P.String -> (Ran -> Aff Unit) -> Aff Unit
buildingMain lines = building [] [ Tuple "Main" ([ "import Lists" ] <> lines) ]

-- | The modules given, each its lines after its header, built in one build
-- | against `Base.Int`, `Stella.Syntax`, and `Lists`, each parser run on a
-- | session; each module's bytecode written as it is built, but that of the
-- | modules named first. Then the modules loaded, in the order built, and each
-- | of the globals of `Main` named rendered.
building :: P.Array P.String -> P.Array (Tuple P.String (P.Array P.String)) -> P.Array P.String -> (Ran -> Aff Unit) -> Aff Unit
building unwritten modules globals k = case compiled of
  Left err -> fail err
  Right syntax -> case compiledLists syntax of
    Left err -> fail ("Lists " <> err)
    Right lists -> case foldM (flip addInterface) initialEnvironment (syntax.moduleInterfaces <> [ lists.interface ]) of
      Left err -> fail (show err)
      Right env -> do
        writeModules
        write "Lists" lists.dmo
        openInProcess 1_000 hello { offers = [ "modules", "parse" ] } >>= case _ of
          Left failure -> fail ("the session did not open: " <> show failure)
          Right session -> do
            -- `Lists` is no module of the build, and is loaded beforehand
            node (Client.load session (pathOf "Lists")) >>= case _ of
              Right (Right _) -> pure unit
              _ -> fail "did not load Lists"
            lowered <- liftEffect (Ref.new [])
            written <- liftEffect (Ref.new Set.empty)
            inSession <- liftEffect (Ref.new Set.empty)
            let
              sources = map (\(Tuple name lines) -> Tuple (fmt @"src/{name}.stel" { name }) (joinWith "\n" ([ fmt @"module {name} where" { name } ] <> lines))) modules
              loading =
                { loaded: inSession
                , locate: \name -> liftEffect (Ref.read written) <#> \names ->
                    if Set.member name names then Just (pathOf (moduleText name)) else Nothing
                }

              action :: CompilerAction (Run (EXCEPT ParserRunnerError + PROCESS + AFF + EFFECT + ()))
              action =
                { readSource: \path -> pure case Array.find (\(Tuple p _) -> p == path) sources of
                    Just (Tuple _ body) -> Right body
                    Nothing -> Left "no such file"
                , runParser: loadingParser loading session syntax.descriptor
                , hooks: defaultHooks
                    { onLowered = \b -> do
                        liftEffect (Ref.modify_ (\ds -> Array.snoc ds b.dmo) lowered)
                        unless (Array.elem (moduleText b.dmo.name) unwritten) do
                          liftAff (write (moduleText b.dmo.name) b.dmo)
                          liftEffect (Ref.modify_ (Set.insert b.dmo.name) written)
                    }
                }
            outcome <- node (Except.runExcept (build action defaultSettings env defaultSourceRoots (map (\(Tuple path _) -> { path, within: String.split (String.Pattern "/") path }) sources)))
            void (node (Client.close session))
            built <- liftEffect (Ref.read lowered)
            case outcome of
              Left failure -> k { result: Left (runnerFailure failure), values: Map.empty }
              Right (Left err) -> k { result: Left (describe err), values: Map.empty }
              Right (Right names) -> do
                values <- loaded (syntax.modules <> [ lists.dmo ] <> built) globals
                k { result: Right (map (\b -> moduleText b.name) names), values }
  where
  write name dmo = case encode dmo of
    Left err -> fail (fmt @"could not encode {name}: {err}" { name, err: show err })
    Right bytes -> do
      buffer <- liftEffect (Buffer.fromArray bytes)
      FS.writeFile (pathOf name) buffer
  describe err = joinWith "; " (map (\m -> fmt @"{at} {message}" { at: joinWith " " (map (\l -> fmt @"{line}:{column}" { line: l.start.line, column: l.start.column }) m.locations), message: m.message }) (NonEmptyArray.toArray (buildMessages err)))
  runnerFailure = case _ of
    ModuleUnavailable m -> "unavailable " <> moduleText m
    failure -> show failure

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
      held <- for globals \name -> case globalNamed store (Qualified (ModuleName "Main") (Ident name)) of
        Nothing -> pure (Tuple name "absent")
        Just slot -> Ref.read slot <#> \value -> Tuple name (maybe' "uninitialized" render value)
      pure (Map.fromFoldable held)
  where
  for xs f = traverse' f xs
  traverse' f = Array.foldM (\acc x -> f x <#> Array.snoc acc) []
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

moduleText :: ModuleName -> P.String
moduleText (ModuleName m) = m

spec :: Spec Unit
spec = describe "Steam, the front end end to end" do
  it "builds a module calling a macro of a module written in Core, and runs what it built" do
    buildingMain [ "xs :: List Int", "xs = ls%[1, 2]", "none :: List Int", "none = ls%[]" ] [ "xs", "none" ] \r -> do
      r.result `shouldEqual` Right [ "Main" ]
      Map.lookup "xs" r.values `shouldEqual` Just "Cons(1, Cons(2, Nil))"
      Map.lookup "none" r.values `shouldEqual` Just "Nil"

  it "reports a call the parser refuses where in its input it stopped, then at the call" do
    buildingMain [ "xs :: List Int", "xs = ls%(1)" ] [] \r ->
      case r.result of
        Left message -> String.take 8 message `shouldEqual` "4:9 4:6 "
        Right _ -> fail "built"

  describe "a macro of the build" do
    let
      pass = Tuple "Pass"
        [ "import Stella.Syntax (List, Parser, Syntax(..), Term, TokenTree, brackets, many, map, nodesOf, tree)"
        , "asSyntax :: List TokenTree -> Syntax Term"
        , "asSyntax ts = Syntax (nodesOf ts)"
        , "@[macro]"
        , "pass :: Parser (Syntax Term)"
        , "pass = brackets (map asSyntax (many tree))"
        ]
      main = Tuple "Main" [ "import Pass", "n :: Int", "n = pass%[2]" ]

    it "is run from the bytecode the build wrote, its module loaded into the session first" do
      building [] [ main, pass ] [ "n" ] \r -> do
        r.result `shouldEqual` Right [ "Pass", "Main" ]
        Map.lookup "n" r.values `shouldEqual` Just "2"

    it "is not run where its module's bytecode was not written" do
      building [ "Pass" ] [ main, pass ] [] \r ->
        r.result `shouldEqual` Left "unavailable Pass"

  describe "a macro written with a quotation" do
    let
      quoting = Tuple "Quoting"
        [ "import Stella.Syntax (List, Parser, Syntax(..), Term, TokenTree, brackets, many, map, nodesOf, tree)"
        , "one :: List TokenTree -> Syntax Term"
        , "one ts = %term{ 1 }"
        , "@[macro]"
        , "constant :: Parser (Syntax Term)"
        , "constant = brackets (map one (many tree))"
        , "inc :: List TokenTree -> Syntax Term"
        , "inc ts = %term{ add $(Syntax (nodesOf ts)) 1 }"
        , "@[macro]"
        , "incremented :: Parser (Syntax Term)"
        , "incremented = brackets (map inc (many tree))"
        ]

    it "expands to the syntax the quotation built, what an antiquotation holds spliced in parentheses" do
      building [] [ Tuple "Main" [ "import Quoting", "import Base.Int (add)", "n :: Int", "n = constant%[]", "m :: Int", "m = incremented%[2]" ], quoting ] [ "n", "m" ] \r -> do
        r.result `shouldEqual` Right [ "Quoting", "Main" ]
        Map.lookup "n" r.values `shouldEqual` Just "1"
        Map.lookup "m" r.values `shouldEqual` Just "3"
