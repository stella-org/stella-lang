-- | Expressions resolved against a module's scope, each shown as a compact
-- | rendering of the Surface AST it becomes.
module Test.Stella.Compiler.Resolve.Expr (spec) where

import Prelude
import Prim hiding (Type)

import Data.Array as Array
import Data.Either (Either(..))
import Data.Map as Map
import Data.Maybe (Maybe(..), maybe)
import Data.Set as Set
import Data.String (joinWith)
import Data.Tuple (Tuple(..))
import Effect.Aff (Aff)
import Stella.Compiler.CST (parseModule, printSyntaxError)
import Stella.Compiler.CST.Types as CST
import Stella.Compiler.Interface.Environment (BuildEnvironment, addInterface, initialEnvironment)
import Stella.Compiler.Interface.Module (ModuleInterface, TypeEntity(..), TypeSort(..), ValueSort(..), Via(..), emptyDeclarations, emptyExports)
import Stella.Compiler.Interface.Scheme (SchemeBody(..), plainScheme)
import Stella.Compiler.Resolve.Expr (resolveDefinition)
import Stella.Compiler.Resolve.Group (groupModule)
import Stella.Compiler.Resolve.Monad (ResolveError(..), ResolveReason(..), ResolveWarning(..), contextOf, runResolve)
import Stella.Compiler.Resolve.Scope (resolveScope)
import Stella.Compiler.Surface.Decl (Associativity(..), FixityTarget(..))
import Stella.Compiler.Surface.Expr (AlternativeBody(..), Binder(..), Expr(..), GuardLine(..), HandlerItem(..), LetBinding(..), RecordField(..))
import Stella.Compiler.Surface.Name (BindingId(..), LocalVar(..), OperatorName(..))
import Stella.Compiler.TypedCore.Domain (codePointOf, textOf)
import Stella.Compiler.TypedCore.Kind (Kind(..), monoScheme)
import Stella.Compiler.TypedCore.Name (EffName(..), Ident(..), ModuleName(..), Qualified(..), Symbol(..), Tag(..), TyName(..))
import Stella.Compiler.TypedCore.Prim (intTy)
import Stella.Compiler.TypedCore.Term (Literal(..))
import Stella.Compiler.TypedCore.Type (Type(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

moduleA :: ModuleName
moduleA = ModuleName "A"

moduleB :: ModuleName
moduleB = ModuleName "B"

inA :: forall a. a -> Qualified a
inA = Qualified moduleA

-- | `A` declares the values `x`, `plus`, `times`, `eq`, and `append`, the
-- | computation `comp`, `data Maybe = Nothing | Just Int`, `data List = Nil |
-- | Cons Int List`, the effect `E` with its operation `get`, and the operators
-- | `+` (`infixl 6 plus`), `*` (`infixl 7 times`), `<>` (`infixr 6 append`),
-- | `==` (`infix 4 eq`), and `:|` (`infixr 5 Cons`). `B` declares `len`.
environment :: BuildEnvironment
environment = case addInterface interfaceA initialEnvironment >>= addInterface interfaceB of
  Right env -> env
  Left _ -> initialEnvironment
  where
  interfaceA = interfaceOf moduleA
    { values: [ "x", "plus", "times", "eq", "append" ]
    , computations: [ "comp" ]
    , types: [ Tuple "Maybe" [ Tuple "Nothing" 0, Tuple "Just" 1 ], Tuple "List" [ Tuple "Nil" 0, Tuple "Cons" 2 ] ]
    , operations: [ "get" ]
    , operators:
        [ Tuple "+" { associativity: AssociateLeft, precedence: 6, target: FixityValue (inA (Ident "plus")) }
        , Tuple "*" { associativity: AssociateLeft, precedence: 7, target: FixityValue (inA (Ident "times")) }
        , Tuple "<>" { associativity: AssociateRight, precedence: 6, target: FixityValue (inA (Ident "append")) }
        , Tuple "==" { associativity: AssociateNone, precedence: 4, target: FixityValue (inA (Ident "eq")) }
        , Tuple ":|" { associativity: AssociateRight, precedence: 5, target: FixityConstructor (inA (Ident "Cons")) }
        ]
    }
  interfaceB = interfaceOf moduleB { values: [ "len" ], computations: [], types: [], operations: [], operators: [] }

interfaceOf
  :: ModuleName
  -> { values :: Array String
     , computations :: Array String
     , types :: Array (Tuple String (Array (Tuple String Int)))
     , operations :: Array String
     , operators :: Array (Tuple String { associativity :: Associativity, precedence :: Int, target :: FixityTarget })
     }
  -> ModuleInterface
interfaceOf name d =
  { name
  , imports: []
  , exports: emptyExports
      { values = Map.fromFoldable (map (\n -> Tuple n (declared (Qualified name (Ident n)))) (d.values <> d.computations <> d.operations <> constructors))
      , types = Map.fromFoldable
          ( map (\(Tuple t _) -> Tuple t { entity: TypeEntity (Qualified name (TyName t)), via: Declared, members: [] }) d.types
              <> (if Array.null d.operations then [] else [ Tuple "E" { entity: EffectEntity (Qualified name (EffName "E")), via: Declared, members: [] } ])
          )
      , operators = Map.fromFoldable (map (\(Tuple op _) -> Tuple op (declared (Qualified name (OperatorName op)))) d.operators)
      }
  , declarations: emptyDeclarations
      { values = Map.fromFoldable
          ( map (\n -> Tuple (Ident n) { sort: SortValue, scheme: plain, attributes: [] }) d.values
              <> map (\n -> Tuple (Ident n) { sort: SortValue, scheme: { kindVars: [], body: Computation int TRowEmpty }, attributes: [] }) d.computations
              <> map (\n -> Tuple (Ident n) { sort: SortOperation (Qualified name (EffName "E")), scheme: plain, attributes: [] }) d.operations
              <> Array.concatMap (\(Tuple t cs) -> map (\(Tuple c _) -> Tuple (Ident c) { sort: SortConstructor (Qualified name (TyName t)), scheme: plain, attributes: [] }) cs) d.types
          )
      , types = Map.fromFoldable
          ( map
              ( \(Tuple t cs) -> Tuple (TyName t)
                  { kind: monoScheme KType
                  , sort: DataType { params: [], constructors: map (\(Tuple c n) -> { name: Ident c, fields: Array.replicate n int }) cs, isNewtype: false }
                  , attributes: []
                  }
              )
              d.types
          )
      , operators = Map.fromFoldable (map (\(Tuple op entry) -> Tuple (OperatorName op) entry) d.operators)
      }
  , implicitHandlers: []
  , catalogOnly: Set.empty
  , arities: Map.empty
  }
  where
  int = TCon intTy []
  plain = plainScheme (monoScheme int)
  constructors = Array.concatMap (\(Tuple _ cs) -> map (\(Tuple c _) -> c) cs) d.types

  declared :: forall a. a -> { entity :: a, via :: Via }
  declared e = { entity: e, via: Declared }

type Ran = { result :: String, reasons :: Array ResolveReason, warnings :: Array String }

-- | The definition of `f` in the module `M`, which imports `A` unqualified
-- | and as `M`, and `B` lazily as `L`, and declares the computation `c`, the
-- | effect `Own` with its operation `tick`, and `<+>` (`infixl 4 own`).
definition :: Array String -> (Ran -> Aff Unit) -> Aff Unit
definition body k = case parseModule (joinWith "\n" (header <> body)) of
  Left e -> fail (printSyntaxError e)
  Right m@(CST.Module cst) -> case Array.findMap definitionOfF cst.items of
    Nothing -> fail "no definition of f"
    Just d -> do
      let
        grouped = (groupModule m).grouped
        ran = runResolve (contextOf environment grouped (resolveScope environment grouped).scoped) 0
          (resolveDefinition d.params d.body d.local)
      k
        { result: renderExpr ran.result.body
        , reasons: map (\(ResolveError _ reason) -> reason) ran.errors
        , warnings: map warningName ran.warnings
        }
  where
  header =
    [ "module M where"
    , "import A"
    , "import A as M"
    , "import lazy B as L"
    , "c :: Int / {| |}"
    , "c = 1"
    , "effect Own where"
    , "  tick :: Unit ->* Unit"
    , "infixl 4 own as <+>"
    , "own a b = a"
    ]
  definitionOfF = case _ of
    CST.ItemDecl (CST.DeclValue n params rhs local) | n.name == "f" -> Just { params, body: rhs, local }
    _ -> Nothing
  warningName = case _ of
    HidesTypeVariable _ n -> n
    HidesValue _ n -> n
    OpenHidesLocal _ n -> n

shows :: Array String -> String -> Array ResolveReason -> Aff Unit
shows body expected reasons = definition body \r -> do
  r.result `shouldEqual` expected
  r.reasons `shouldEqual` reasons

spec :: Spec Unit
spec = describe "Stella.Compiler.Resolve.Expr" do
  describe "references" do
    it "become the node of what they name" do
      shows [ "f a = (a, x, comp, c, Just, Nothing?, get, tick, own, 'T, ?h, 1, true, 'c', \"s\", 1.5, ())" ]
        "(a#0, A.x, comp:A.comp, comp:M.c, A.Just, A.Nothing?, op:A.get, op:M.tick, M.own, 'T, ?h, 1, true, char99, \"s\", 1.5, Prim.Unit)"
        []

    it "report a name nothing in scope stands for" do
      shows [ "f = (nope, Nope, Nope?, Just.x)" ] "(!, !, !, !)"
        [ UnknownValue "nope", UnknownConstructor "Nope", UnknownConstructor "Nope", UnknownValue "Just.x" ]

    it "select an operation's instance by a label" do
      shows [ "f = (get@cache, x@cache, get@Cache)" ] "(op:A.get@cache, !, !)" [ NotAnOperation "x", LabelExpected ]

  describe "operators" do
    it "are rebracketed by fixity, a constructor's among them, and a name used infix binds as infixl 9" do
      shows [ "f = 1 + 2 * 3 + 4 <+> 5" ] "<M.own <A.plus <A.plus 1 <A.times 2 3>> 4> 5>" []
      shows [ "f = 1 :| 2 :| Nil" ] "<A.Cons 1 <A.Cons 2 A.Nil>>" []
      shows [ "f = 1 `plus` 2 * 3" ] "<A.times <A.plus 1 2> 3>" []
      shows [ "f = (+) 1 (:|)" ] "((A.plus 1) A.Cons)" []

    it "of one precedence that cannot be chained, and one nothing stands for, leave the chain invalid" do
      shows [ "f = 1 + 2 <> 3" ] "!" [ OperatorsUnordered "<>" "+" ]
      shows [ "f = 1 == 2 == 3" ] "!" [ OperatorsUnordered "==" "==" ]
      shows [ "f = 1 %% 2" ] "!" [ UnknownOperator "%%" ]
      shows [ "f = 1 `missing` 2 * 3" ] "!" [ UnknownValue "missing" ]
      shows [ "infixl 4 nope as <!>", "f = 1 <!> 2" ] "!" []

  describe "local scopes" do
    it "of a `let` block are recursive, every binding in scope in every right-hand side" do
      shows [ "f = let", "      g y = h y", "      h z = g z", "    in g" ]
        "(let g#0 y#2 = (h#1 y#2); h#1 z#3 = (g#0 z#3) in g#0)"
        []

    it "of a `where` see the parameters, and the body sees the `where`" do
      shows [ "f a = b", "  where", "  b = a" ] "(let b#1 = a#0 in b#1)" []

    it "put a local signature's type variables in scope over its definition" do
      definition [ "f = let", "      g :: a -> a", "      g y = (y :: a)", "    in g" ] \r -> r.reasons `shouldEqual` []

    it "take irrefutable patterns, and report a block whose bindings do not pair up" do
      shows [ "f = let Just y = x in \\(Just z) -> z" ] "(let (A.Just y#0) = A.x in (\\(A.Just z#1) -> z#1))" [ RefutablePattern, RefutablePattern ]
      shows [ "f = let", "      a = 1", "      a = 2", "    in a" ] "(let a#0 = 1; a#1 = 2 in a#0)" [ BoundTwice "a" ]

    it "of a `case` alternative bind its patterns, and a guard block's bindings the lines after them" do
      shows
        [ "f p = case p of"
        , "  Just y where"
        , "      z = y"
        , "      z == y -> z"
        , "      otherwise -> y"
        , "  Nothing -> 0"
        ]
        "(case p#0 of (A.Just y#1) where z#2 = y#1 | <A.eq z#2 y#1> -> z#2 | otherwise -> y#1 ; A.Nothing -> 0)"
        []

    it "of an open bring an alias's names, a lazy one's among them, ahead of everything outside it" do
      shows [ "f = (L.( len ), import L in len, M.( x ))" ] "(B.len, B.len, A.x)" []
      shows [ "f = (len, L.len, Q.( 1 ))" ] "(!, !, !)" [ UnknownValue "len", UnknownValue "L.len", UnknownAlias "Q" ]
      definition [ "f len = L.( len )" ] \r -> do
        r.result `shouldEqual` "B.len"
        r.warnings `shouldEqual` [ "len" ]
      definition [ "f = L.( \\len -> len )" ] \r -> do
        r.result `shouldEqual` "(\\len#0 -> len#0)"
        r.warnings `shouldEqual` [ "len" ]

  describe "records" do
    it "hold their fields, a pun being a field, and report a label written twice" do
      shows [ "f a r = ({ a, b: 1 }, { c = 2, ...r }, r.a.b)" ] "({ a: a#0, b: 1 }, { c = 2, ...r#1 }, r#1.a.b)" []
      shows [ "f a = { a, a: 1, b: 2, b: 3 }" ] "{ a: a#0, a: 1, b: 2, b: 3 }" [ LabelTwice "a", LabelTwice "b" ]

  describe "what is not supported yet" do
    it "is reported where it stands" do
      shows [ "f = (_ + 1, m%(1), case _ of", "  _ -> 1)" ] "(<A.plus ! 1>, !, (case ! of _ -> 1))"
        [ NotYetSupported "The anonymous argument `_`", NotYetSupported "A macro call", NotYetSupported "`case _ of`" ]
      shows [ "f = handle x with", "  E fast | get _ -> 0", "  x" ] "(handle A.x with A.x)" [ NotYetSupported "A handler group written in place" ]

renderVar :: LocalVar -> String
renderVar (LocalVar v) = case v.name, v.id of
  Ident n, BindingId i -> n <> "#" <> show i

renderExpr :: Expr -> String
renderExpr = case _ of
  ExprLocal _ v -> renderVar v
  ExprValue _ q -> qualified q
  ExprComputation _ q -> "comp:" <> qualified q
  ExprConstructor _ q -> qualified q
  ExprOperation _ q label -> "op:" <> qualified q <> maybe "" (\(Symbol l) -> "@" <> l) label
  ExprDiscriminator _ q -> qualified q <> "?"
  ExprTag _ (Tag t) -> "'" <> t
  ExprLiteral _ l -> literal l
  ExprHole _ h -> "?" <> h
  ExprApp _ f a -> "(" <> renderExpr f <> " " <> renderExpr a <> ")"
  ExprOperator _ op l r -> "<" <> renderExpr op <> " " <> renderExpr l <> " " <> renderExpr r <> ">"
  ExprTyped _ e _ -> "(" <> renderExpr e <> " :: τ)"
  ExprSelect _ e (Symbol l) -> renderExpr e <> "." <> l
  ExprTuple _ es -> "(" <> joinWith ", " (map renderExpr es) <> ")"
  ExprRecord _ fs -> "{ " <> joinWith ", " (map field fs) <> " }"
  ExprLambda _ ps body -> "(\\" <> joinWith " " (map renderBinder ps) <> " -> " <> renderExpr body <> ")"
  ExprLet _ bs body -> "(let " <> joinWith "; " (map binding bs) <> " in " <> renderExpr body <> ")"
  ExprCase _ ss alts -> "(case " <> joinWith ", " (map renderExpr ss) <> " of " <> joinWith " ; " (map alternative alts) <> ")"
  ExprHandle _ items e -> "(handle " <> renderExpr e <> " with " <> joinWith ", " (map item items) <> ")"
  ExprCellRead _ _ -> "cell!"
  ExprCellWrite _ _ _ -> "cell:="
  ExprResume _ -> "resume"
  ExprInvalid _ -> "!"
  where
  field = case _ of
    FieldValue _ (Symbol l) e -> l <> ": " <> renderExpr e
    FieldUpdate _ (Symbol l) e -> l <> " = " <> renderExpr e
    FieldSpread _ e -> "..." <> renderExpr e
  binding = case _ of
    LetValue b -> joinWith " " ([ renderVar b.var ] <> map renderBinder b.params) <> " = " <> renderExpr b.body
    LetPattern b -> renderBinder b.binder <> " = " <> renderExpr b.body
  alternative alt =
    joinWith " | " (map (joinWith ", " <<< map renderBinder) alt.patterns) <> case alt.body of
      Unconditional e -> " -> " <> renderExpr e
      Guarded lines -> " where " <> joinWith " | " (map guard lines)
  guard = case _ of
    GuardBinding _ b e -> renderBinder b <> " = " <> renderExpr e
    GuardWhen _ c e -> renderExpr c <> " -> " <> renderExpr e
    GuardOtherwise _ e -> "otherwise -> " <> renderExpr e
  item = case _ of
    HandlerApplied e -> renderExpr e
    HandlerGroup _ -> "group"

renderBinder :: Binder -> String
renderBinder = case _ of
  BinderWildcard _ -> "_"
  BinderVar _ v -> renderVar v
  BinderAs _ v b -> renderVar v <> "@" <> renderBinder b
  BinderConstructor _ q [] -> qualified q
  BinderConstructor _ q bs -> "(" <> qualified q <> " " <> joinWith " " (map renderBinder bs) <> ")"
  BinderTag _ (Tag t) b -> "'" <> t <> maybe "" (\p -> " " <> renderBinder p) b
  BinderLiteral _ l -> literal l
  BinderTuple _ bs -> "(" <> joinWith ", " (map renderBinder bs) <> ")"
  BinderRecord _ _ _ -> "{…}"
  BinderOr _ bs -> "(" <> joinWith " | " (map renderBinder bs) <> ")"
  BinderTyped _ b _ -> "(" <> renderBinder b <> " :: τ)"
  BinderInvalid _ -> "!"

literal :: Literal -> String
literal = case _ of
  LitInt i -> show i
  LitBoolean b -> show b
  LitChar c -> "char" <> show (codePointOf c)
  LitString s -> show (textOf s)
  LitNumber n -> show n

qualified :: Qualified Ident -> String
qualified (Qualified (ModuleName m) (Ident n)) = m <> "." <> n
