-- | Patterns resolved against a module's scope and its constructor table, each
-- | shown as a compact rendering of the Surface AST it becomes.
module Test.Stella.Compiler.Resolve.Binder (spec) where

import Prelude
import Prim hiding (Type)

import Data.Array as Array
import Data.Either (Either(..))
import Data.Map as Map
import Data.Maybe (Maybe(..), maybe)
import Data.Set as Set
import Data.String (joinWith)
import Data.Traversable (traverse, traverse_)
import Data.Tuple (Tuple(..))
import Effect.Aff (Aff)
import Stella.Compiler.CST (parseModule, printSyntaxError)
import Stella.Compiler.CST.Types as CST
import Stella.Compiler.Interface.Environment (BuildEnvironment, addInterface, initialEnvironment)
import Stella.Compiler.Interface.Module (TypeEntity(..), TypeSort(..), ValueSort(..), Via(..), emptyDeclarations, emptyExports)
import Stella.Compiler.Interface.Scheme (plainScheme)
import Stella.Compiler.Resolve.Binder (Member(..), ResolvedMember(..), requireIrrefutable, resolveAlternative, resolveBinders, resolveGroup)
import Stella.Compiler.Resolve.Group (groupModule)
import Stella.Compiler.Resolve.Monad (Resolve, ResolveError(..), ResolveReason(..), ResolveWarning(..), contextOf, runResolve, withValues)
import Stella.Compiler.Resolve.Scope (resolveScope)
import Stella.Compiler.Surface.Expr (Binder(..))
import Stella.Compiler.Surface.Name (BindingId(..), LocalVar(..))
import Stella.Compiler.TypedCore.Domain (codePointOf, textOf)
import Stella.Compiler.TypedCore.Kind (Kind(..), monoScheme)
import Stella.Compiler.TypedCore.Name (Ident(..), ModuleName(..), Qualified(..), Symbol(..), Tag(..), TyName(..))
import Stella.Compiler.TypedCore.Prim (intTy)
import Stella.Compiler.TypedCore.Term (Literal(..))
import Stella.Compiler.TypedCore.Type (Type(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

moduleA :: ModuleName
moduleA = ModuleName "A"

inA :: forall a. a -> Qualified a
inA = Qualified moduleA

-- | `A` declares `data Maybe = Nothing | Just Int`, `data Box = Box Int`,
-- | `data Pair = Pair Int Int`, and the value `x`.
environment :: BuildEnvironment
environment = case addInterface interfaceA initialEnvironment of
  Right env -> env
  Left _ -> initialEnvironment
  where
  interfaceA =
    { name: moduleA
    , imports: []
    , exports: emptyExports
        { values = Map.fromFoldable (map (\n -> Tuple n { entity: inA (Ident n), via: Declared }) [ "Nothing", "Just", "Box", "Pair", "x" ])
        , types = Map.fromFoldable (map (\(Tuple t _) -> Tuple t { entity: TypeEntity (inA (TyName t)), via: Declared, members: [] }) types)
        }
    , declarations: emptyDeclarations
        { values = Map.fromFoldable
            ( [ Tuple (Ident "x") { sort: SortValue, scheme, attributes: [] } ]
                <> Array.concatMap (\(Tuple t cs) -> map (\(Tuple c _) -> Tuple (Ident c) { sort: SortConstructor (inA (TyName t)), scheme, attributes: [] }) cs) types
            )
        , types = Map.fromFoldable (map (\(Tuple t cs) -> Tuple (TyName t) (dataType cs)) types)
        }
    , implicitHandlers: []
    , catalogOnly: Set.empty
    , arities: Map.empty
    }
  scheme = plainScheme (monoScheme (TCon intTy []))
  int = TCon intTy []
  types =
    [ Tuple "Maybe" [ Tuple "Nothing" [], Tuple "Just" [ int ] ]
    , Tuple "Box" [ Tuple "Box" [ int ] ]
    , Tuple "Pair" [ Tuple "Pair" [ int, int ] ]
    ]
  dataType cs =
    { kind: monoScheme KType
    , sort: DataType { params: [], constructors: map (\(Tuple c fs) -> { name: Ident c, fields: fs }) cs, isNewtype: false }
    , attributes: []
    }

type Ran a = { result :: a, reasons :: Array ResolveReason, warnings :: Array String }

-- | Runs a resolution against the module `M`, which imports `A`, declares
-- | `data Own = One | Two Int`, `newtype N = N Int`, and `top`, and has the
-- | lines given besides, on its declaration `f`.
resolvingF :: forall a. Array String -> (CST.Decl -> Resolve a) -> (Ran a -> Aff Unit) -> Aff Unit
resolvingF body f k = case parseModule (joinWith "\n" ([ "module M where", "import A", "data Own = One | Two Int", "newtype N = N Int", "top = 1" ] <> body)) of
  Left e -> fail (printSyntaxError e)
  Right m@(CST.Module cst) -> case Array.findMap declarationF cst.items of
    Nothing -> fail "no declaration of f"
    Just d -> do
      let
        grouped = (groupModule m).grouped
        ran = runResolve (contextOf environment grouped (resolveScope environment grouped).scoped) 0 (f d)
      k
        { result: ran.result
        , reasons: map (\(ResolveError _ reason) -> reason) ran.errors
        , warnings: map warningName ran.warnings
        }
  where
  declarationF = case _ of
    CST.ItemDecl d@(CST.DeclValue n _ _ _) | n.name == "f" -> Just d
    _ -> Nothing
  warningName = case _ of
    HidesTypeVariable _ n -> n
    HidesValue _ n -> n
    OpenHidesLocal _ n -> n

-- | Runs a resolution on the parameters of `f`.
resolving :: forall a. Array String -> (Array CST.Binder -> Resolve a) -> (Ran a -> Aff Unit) -> Aff Unit
resolving body f = resolvingF body case _ of
  CST.DeclValue _ ps _ _ -> f ps
  _ -> f []

-- | The parameters of `f`, as one group: each pattern, then what the group
-- | puts in scope.
parameters :: Array String -> (Ran String -> Aff Unit) -> Aff Unit
parameters body = resolving body \ps -> resolveBinders ps <#> render

render :: { binders :: Array Binder, bound :: Array LocalVar } -> String
render r = joinWith " " (map renderBinder r.binders) <> " | " <> joinWith " " (map renderVar r.bound)

-- | The members of the `where` of a declaration.
members :: CST.Decl -> Array Member
members = case _ of
  CST.DeclValue _ _ _ (Just bindings) -> Array.mapMaybe memberOf bindings
  _ -> []
  where
  memberOf = case _ of
    CST.LetValue n _ _ -> Just (MemberName n)
    CST.LetPattern b _ -> Just (MemberPattern b)
    CST.LetSignature _ _ -> Nothing

member :: ResolvedMember -> String
member = case _ of
  ResolvedName v -> renderVar v
  ResolvedPattern b -> renderBinder b

shows :: Array String -> String -> Array ResolveReason -> Aff Unit
shows body expected reasons = parameters body \r -> do
  r.result `shouldEqual` expected
  r.reasons `shouldEqual` reasons

-- | What requiring every parameter of `f` to be irrefutable reports.
irrefutability :: Array String -> Array ResolveReason -> Aff Unit
irrefutability body reasons =
  resolving body (\ps -> resolveBinders ps >>= \r -> traverse_ requireIrrefutable r.binders) \r ->
    r.reasons `shouldEqual` reasons

spec :: Spec Unit
spec = describe "Stella.Compiler.Resolve.Binder" do
  describe "variables" do
    it "are numbered in the order written, and the group puts each in scope" do
      shows [ "f a (b, c) d@{ e, g: _ } = 1" ] "a#0 (b#1, c#2) d#3@{ e = e#4, g = _ } | a#0 b#1 c#2 d#3 e#4" []

    it "bound twice in one group are reported, and the first is in scope" do
      shows [ "f a (b, a) = 1" ] "a#0 (b#1, a#2) | a#0 b#1" [ BoundTwice "a" ]

    it "warn where they hide a top-level, an imported, or an enclosing local value" do
      parameters [ "f top x y = 1" ] \r -> r.warnings `shouldEqual` [ "top", "x" ]
      resolving [ "f a = 1" ]
        (\ps -> resolveBinders ps >>= \outer -> withValues outer.bound (resolveBinders ps))
        \r -> r.warnings `shouldEqual` [ "a" ]

    it "are bound even where the pattern holding them is invalid" do
      shows [ "f (Nope a) (Just b | Nothing) = 1" ] "! ! | a#0 b#1" [ UnknownConstructor "Nope", OrPatternBinds ]

    it "are handed out in the order written, whatever ranges their names carry" do
      let
        r = { start: { line: 1, column: 1 }, end: { line: 1, column: 2 } }
        named n = CST.BinderVar { range: r, qualifier: Nothing, name: n }
      resolving [ "f = 1" ] (\_ -> resolveBinders [ named "a", CST.BinderTuple [ named "b", named "c" ] ] <#> render)
        \ran -> ran.result `shouldEqual` "a#0 (b#1, c#2) | a#0 b#1 c#2"

  describe "groups" do
    it "of a `let` block or a `where` bind the names its definitions bind and the variables of its patterns, as one" do
      resolvingF [ "f = 1", "  where", "  y = 1", "  (a, (Just b | Nothing)) = p", "  b = 2", "  a = 3" ]
        (\d -> resolveGroup (members d) <#> \r -> joinWith " " (map member r.members) <> " | " <> joinWith " " (map renderVar r.bound))
        \ran -> do
          ran.result `shouldEqual` "y#0 (a#1, !) b#3 a#4 | y#0 a#1 b#2"
          ran.reasons `shouldEqual` [ BoundTwice "b", BoundTwice "a", OrPatternBinds ]

    it "of a `case` alternative are its patterns, its or-choices at its top binding nothing" do
      let
        alternatives = case _ of
          CST.DeclValue _ _ (CST.ExprCase _ alts) _ -> traverse (\alt -> resolveAlternative alt.patterns <#> \r -> joinWith " ; " (map (joinWith " " <<< map renderBinder) r.patterns) <> " | " <> joinWith " " (map renderVar r.bound)) alts
          _ -> pure []
      resolvingF [ "f = case p, q of", "  Nothing, One | x, Two _ -> 1", "  Just a, b -> 2" ] alternatives \ran -> do
        ran.result `shouldEqual` [ "A.Nothing M.One ; ! (M.Two _) | x#0", "(A.Just a#1) b#2 | a#1 b#2" ]
        ran.reasons `shouldEqual` [ OrPatternBinds ]

  describe "constructors" do
    it "resolve to the constructor, imported or the module's own, and `()` to `Prim.Unit`" do
      shows [ "f (Just a) Nothing (Box _) One (Two n) (N m) () = 1" ]
        "(A.Just a#0) A.Nothing (A.Box _) M.One (M.Two n#1) (M.N m#2) Prim.Unit | a#0 n#1 m#2"
        []

    it "take one pattern per field" do
      shows [ "f Just (Nothing a) (Pair _) = 1" ] "! ! ! | a#0"
        [ ConstructorArity "Just" 1 0, ConstructorArity "Nothing" 0 1, ConstructorArity "Pair" 2 1 ]

  describe "other patterns" do
    it "keep tags with one payload or none, and literals other than a Number" do
      shows [ "f 'A ('B a) ('C a b) 1 true 'c' \"s\" 1.5 = 1" ]
        "'A ('B a#0) ! 1 true char99 \"s\" ! | a#0 b#2"
        [ BoundTwice "a", TagPayloadMany, NumberPattern ]

    it "keep or-patterns that bind nothing, records, and annotations" do
      shows [ "f (One | Two _) { a, b: (c, _), ...r } (d :: Int) = 1" ]
        "(M.One | (M.Two _)) { a = a#0, b = (c#1, _), ...r#2 } (d#3 :: τ) | a#0 c#1 r#2 d#3"
        []

    it "report a label a record pattern writes twice, apart from a variable bound twice" do
      shows [ "f { a: x, a: y } { b, b: z } { c: w, c: w } = 1" ] "{ a = x#0, a = y#1 } { b = b#2, b = z#3 } { c = w#4, c = w#5 } | x#0 y#1 b#2 z#3 w#4"
        [ BoundTwice "w", LabelTwice "a", LabelTwice "b", LabelTwice "c" ]

    it "report what is no pattern" do
      shows [ "f (g a) = 1" ] "! | g#0 a#1" [ NotAPattern ]

  describe "irrefutability" do
    it "admits variables, tuples, records, single constructors, and as- and annotated patterns around them" do
      irrefutability [ "f a _ (b, c) { d } (Box e) g@(N h) (i :: Int) () (Pair _ _) = 1" ] []

    it "reports each largest part that can fail" do
      irrefutability [ "f (Just a) 1 'A (One | Two _) (Box (Just b)) (Pair (Box _) 2) One = 1" ]
        [ RefutablePattern, RefutablePattern, RefutablePattern, RefutablePattern, RefutablePattern, RefutablePattern, RefutablePattern ]

renderVar :: LocalVar -> String
renderVar (LocalVar v) = case v.name, v.id of
  Ident n, BindingId i -> n <> "#" <> show i

renderBinder :: Binder -> String
renderBinder = case _ of
  BinderWildcard _ -> "_"
  BinderVar _ v -> renderVar v
  BinderAs _ v b -> renderVar v <> "@" <> renderBinder b
  BinderConstructor _ q [] -> qualified q
  BinderConstructor _ q bs -> "(" <> qualified q <> " " <> joinWith " " (map renderBinder bs) <> ")"
  BinderTag _ (Tag t) Nothing -> "'" <> t
  BinderTag _ (Tag t) (Just b) -> "('" <> t <> " " <> renderBinder b <> ")"
  BinderLiteral _ l -> case l of
    LitInt i -> show i
    LitBoolean b -> show b
    LitChar c -> "char" <> show (codePointOf c)
    LitString s -> show (textOf s)
    LitNumber n -> show n
  BinderTuple _ bs -> "(" <> joinWith ", " (map renderBinder bs) <> ")"
  BinderRecord _ fs rest ->
    "{ " <> joinWith ", " (map (\f -> case f.label of Symbol l -> l <> " = " <> renderBinder f.binder) fs <> maybe [] (\r -> [ "..." <> maybe "" renderVar r.var ]) rest) <> " }"
  BinderOr _ bs -> "(" <> joinWith " | " (map renderBinder bs) <> ")"
  BinderTyped _ b _ -> "(" <> renderBinder b <> " :: τ)"
  BinderInvalid _ -> "!"
  where
  qualified (Qualified (ModuleName m) (Ident n)) = m <> "." <> n
