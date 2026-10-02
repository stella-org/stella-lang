-- | Kinds, types, and signatures resolved against a module's scope, each shown
-- | as a compact rendering of the Surface AST it becomes.
module Test.Stella.Compiler.Resolve.Type (spec) where

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
import Stella.Compiler.Interface.Module (TypeEntity(..), TypeSort(..), Via(..), emptyDeclarations, emptyExports)
import Stella.Compiler.Resolve.Group (groupModule)
import Stella.Compiler.Resolve.Monad (Context, Resolve, ResolveError(..), ResolveReason(..), ResolveWarning(..), contextOf, runResolve, withTypeVariables)
import Stella.Compiler.Resolve.Scope (resolveScope)
import Stella.Compiler.Resolve.Type (bindTypeVariables, computationScope, handlerScope, resolveComputationSignature, resolveHandlerSignature, resolveKind, resolveOperationSignature, resolveSignature, resolveType, signatureScope)
import Stella.Compiler.Surface.Decl (Associativity(..))
import Stella.Compiler.Surface.Name (BindingId(..), OperatorName(..), TypeVar(..))
import Stella.Compiler.Surface.Type (ComputationType, EffectApplication, EffectRowItem(..), HandlerSignature(..), Kind(..), OperationSignature, RecordRowItem(..), Signature, SignaturePrefix(..), Type(..), TypeOperatorTarget(..), TypeVarBinder, VariantRowItem(..))
import Stella.Compiler.TypedCore.Kind (Kind(..), RowElemKind(..), monoScheme) as K
import Stella.Compiler.TypedCore.Name (EffName(..), Ident(..), KindVar(..), ModuleName(..), Qualified(..), Symbol(..), Tag(..), TyName(..), TyVar(..))
import Stella.Compiler.TypedCore.Prim (intTy)
import Stella.Compiler.TypedCore.Type (Type(..)) as Core
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

moduleA :: ModuleName
moduleA = ModuleName "A"

inA :: forall a. a -> Qualified a
inA = Qualified moduleA

-- | `A` declares the data types `T` and `Show`, the synonym `S`, the effects
-- | `E`, `State`, and `Both`, the value `show`, and these type operators:
-- |
-- | | operator | fixity | stands for |
-- | | --- | --- | --- |
-- | | `+` | `infixl 6` | `T` |
-- | | `<>` | `infixr 6` | `T` |
-- | | `*` | `infixl 7` | `S` |
-- | | `^` | `infixr 8` | `T` |
-- | | `==` | `infix 4` | `T` |
-- | | `&` | `infixl 5` | `Both` |
environment :: BuildEnvironment
environment = case addInterface interfaceA initialEnvironment of
  Right env -> env
  Left _ -> initialEnvironment
  where
  interfaceA =
    { name: moduleA
    , imports: []
    , exports: emptyExports
        { values = Map.singleton "show" (declared (inA (Ident "show")))
        , types = Map.fromFoldable
            [ typeExport "T" (TypeEntity (inA (TyName "T")))
            , typeExport "Show" (TypeEntity (inA (TyName "Show")))
            , typeExport "S" (TypeEntity (inA (TyName "S")))
            , typeExport "E" (EffectEntity (inA (EffName "E")))
            , typeExport "State" (EffectEntity (inA (EffName "State")))
            , typeExport "Both" (EffectEntity (inA (EffName "Both")))
            ]
        , typeOperators = Map.fromFoldable (map (\(Tuple op _) -> Tuple op (declared (inA (OperatorName op)))) operators)
        }
    , declarations: emptyDeclarations
        { types = Map.fromFoldable
            [ Tuple (TyName "T") (dataType)
            , Tuple (TyName "Show") (dataType)
            , Tuple (TyName "S") { kind: K.monoScheme K.KType, sort: Synonym { params: [], body: Core.TCon intTy [] }, attributes: [] }
            ]
        , typeOperators = Map.fromFoldable (map (\(Tuple op entry) -> Tuple (OperatorName op) entry) operators)
        }
    , implicitHandlers: []
    , catalogOnly: Set.empty
    , arities: Map.empty
    }

  declared :: forall a. a -> { entity :: a, via :: Via }
  declared e = { entity: e, via: Declared }
  typeExport n e = Tuple n { entity: e, via: Declared, members: [] }
  dataType = { kind: K.monoScheme K.KType, sort: DataType { params: [], constructors: [], isNewtype: false }, attributes: [] }
  operators =
    [ Tuple "+" { associativity: AssociateLeft, precedence: 6, target: TargetTypeConstructor (inA (TyName "T")) }
    , Tuple "<>" { associativity: AssociateRight, precedence: 6, target: TargetTypeConstructor (inA (TyName "T")) }
    , Tuple "*" { associativity: AssociateLeft, precedence: 7, target: TargetTypeSynonym (inA (TyName "S")) }
    , Tuple "^" { associativity: AssociateRight, precedence: 8, target: TargetTypeConstructor (inA (TyName "T")) }
    , Tuple "==" { associativity: AssociateNone, precedence: 4, target: TargetTypeConstructor (inA (TyName "T")) }
    , Tuple "&" { associativity: AssociateLeft, precedence: 5, target: TargetEffect (inA (EffName "Both")) }
    ]

type Ran a = { result :: a, reasons :: Array ResolveReason, warnings :: Array String }

-- | Runs a resolution against the module `M`, which imports `A` and has the
-- | body given, on what `pick` takes from the module's items.
resolving :: forall a. Array String -> (Array CST.Decl -> Maybe (Resolve a)) -> (Ran a -> Aff Unit) -> Aff Unit
resolving body pick k = case parseModule (joinWith "\n" ([ "module M where", "import A" ] <> body)) of
  Left e -> fail (printSyntaxError e)
  Right m@(CST.Module cst) -> case pick (Array.mapMaybe declaration cst.items) of
    Nothing -> fail "nothing to resolve"
    Just r -> do
      let
        grouped = (groupModule m).grouped

        ctx :: Context
        ctx = contextOf environment grouped (resolveScope environment grouped).scoped
        ran = runResolve ctx 0 r
      k
        { result: ran.result
        , reasons: map (\(ResolveError _ reason) -> reason) ran.errors
        , warnings: map (\(HidesTypeVariable _ n) -> n) ran.warnings
        }
  where
  declaration = case _ of
    CST.ItemDecl d -> Just d
    _ -> Nothing

signatureOf :: String -> Array CST.Decl -> Maybe CST.Type
signatureOf n = Array.findMap case _ of
  CST.DeclSignature name t | name.name == n -> Just t
  _ -> Nothing

-- | The signature of `f`, resolved as a value's.
signature :: Array String -> (Ran String -> Aff Unit) -> Aff Unit
signature body k = resolving body (map (map renderSignature <<< resolveSignature) <<< signatureOf "f") k

-- | The signature of `f`, resolved as a type standing where nothing binds
-- | implicitly.
annotation :: Array String -> (Ran String -> Aff Unit) -> Aff Unit
annotation body k = resolving body (map (map renderType <<< resolveType) <<< signatureOf "f") k

shows :: Array String -> String -> Array ResolveReason -> Aff Unit
shows body expected reasons = signature body \r -> do
  r.result `shouldEqual` expected
  r.reasons `shouldEqual` reasons

spec :: Spec Unit
spec = describe "Stella.Compiler.Resolve.Type" do
  describe "kinds" do
    let
      kindOf n = Array.findMap case _ of
        CST.DeclKindSignature _ name k | name.name == n -> Just (map renderKind (resolveKind k))
        _ -> Nothing
    it "are made of `Type`, `Effect`, `Row Type`, `Row Effect`, variables, and arrows" do
      resolving [ "data P :: (Type -> Effect) -> Row Effect -> Row Type -> k -> Type" ] (kindOf "P") \r -> do
        r.result `shouldEqual` "((Type -> Effect) -> (Row Effect -> (Row Type -> (k -> Type))))"
        r.reasons `shouldEqual` []

    it "are malformed with any other word, or `Row` applied to anything else" do
      resolving [ "data P :: Row (Type -> Type) -> Foo -> Prim.Type -> Row" ] (kindOf "P") \r -> do
        r.result `shouldEqual` "(! -> (! -> (! -> !)))"
        r.reasons `shouldEqual` [ KindMalformed, KindMalformed, KindMalformed, KindMalformed ]

  describe "names" do
    it "resolve to a type constructor, a synonym, and `()` to `Prim.Unit`" do
      shows [ "type Own = Int", "f :: T -> S -> Own -> () -> Int" ]
        "[] (A.T -> (syn:A.S -> (syn:M.Own -> (Prim.Unit -> Prim.Int))))"
        []

    it "report one nothing stands for, and an effect standing as a type" do
      shows [ "f :: Nope -> E -> { a :: State Int }" ] "[] (! -> (! -> { a :: (! Prim.Int) }))"
        [ UnknownType "Nope", EffectNotType "E", EffectNotType "State" ]

    it "keep a tuple, a wildcard, a hole, and a kinded type" do
      shows [ "f :: (Int, _, ?h, (T :: Type))" ] "[] (Prim.Int, _, ?h, (A.T :: Type))" []

  describe "type variables" do
    it "a signature quantifies implicitly, in the order they first appear" do
      shows [ "f :: b -> a -> b" ] "[b#0 a#1] (b#0 -> (a#1 -> b#0))" []

    it "a `forall` binds, with kinds, and is no implicit quantification" do
      shows [ "f :: forall a (r :: Row Effect). a -> b" ]
        "[b#0] (forall a#1 (r#2 :: Row Effect). (a#1 -> b#0))"
        []

    it "an inner binder hides an outer one, with a warning" do
      signature [ "f :: forall a. a -> (forall a. a)" ] \r -> do
        r.result `shouldEqual` "[] (forall a#0. (a#0 -> (forall a#1. a#1)))"
        r.warnings `shouldEqual` [ "a" ]

    it "a name bound twice by one `forall` is reported, and refers to the first" do
      shows [ "f :: forall a a. a" ] "[] (forall a#0 a#1. a#0)" [ BoundTwice "a" ]

    it "a type that is no signature binds nothing implicitly" do
      annotation [ "f :: a -> Int" ] \r -> do
        r.result `shouldEqual` "(! -> Prim.Int)"
        r.reasons `shouldEqual` [ UnknownTypeVariable "a" ]

    it "a signature's variables scope over a nested signature, which quantifies only the rest" do
      let
        nested decls = do
          outer <- signatureOf "f" decls
          inner <- signatureOf "g" decls
          pure do
            s <- resolveSignature outer
            withTypeVariables (signatureScope s) (map renderSignature (resolveSignature inner))
      resolving [ "f :: forall b. a -> b", "g :: a -> b -> c" ] nested \r ->
        r.result `shouldEqual` "[c#2] (a#0 -> (b#1 -> c#2))"

  describe "type operators" do
    it "are rebracketed by precedence and associativity, looser than application and tighter than `->`" do
      shows [ "f :: Int + T * Int + Int -> Int ^ Int ^ Int" ]
        "[] ((A.T (A.T Prim.Int (syn:A.S A.T Prim.Int)) Prim.Int) -> (A.T Prim.Int (A.T Prim.Int Prim.Int)))"
        []

    it "stand for what the module's own fixity declaration names" do
      shows [ "infixr 5 type Own as :+:", "type Own = Int", "f :: Int :+: Int :+: Int" ]
        "[] (syn:M.Own Prim.Int (syn:M.Own Prim.Int Prim.Int))"
        []

    it "of one precedence that associate differently, or that associate not at all, cannot be chained" do
      shows [ "f :: Int + Int <> Int" ] "[] !" [ OperatorsUnordered "<>" "+" ]
      shows [ "f :: Int == Int == Int" ] "[] !" [ OperatorsUnordered "==" "==" ]
      shows [ "f :: Int == (Int == Int)" ] "[] (A.T Prim.Int (A.T Prim.Int Prim.Int))" []

    it "report one nothing stands for" do
      shows [ "f :: Int %% Int" ] "[] !" [ UnknownTypeOperator "%%" ]

  describe "rows" do
    it "keep the items their bracket admits" do
      shows [ "f :: { a :: Int, ...r } -> ['Ok :: Int, err :: String, ...] -> Int / {| E, s :: State Int, Int & Int, ...e |}" ]
        "[r#0 e#1] ({ a :: Prim.Int, ...r#0 } -> ([ 'Ok :: Prim.Int, err :: Prim.String, ... ] -> Prim.Int / {| A.E, s :: A.State Prim.Int, A.Both Prim.Int Prim.Int, ...e#1 |}))"
        []

    it "drop an item their bracket does not admit, and an element of an effect row that is no effect" do
      shows [ "f :: { 'A :: Int, Int } -> [Int] -> {| a :: Int, T, x, 'B :: E |}" ]
        "[x#0] ({  } -> ([  ] -> {|  |}))"
        [ RowItemMisplaced, RowItemMisplaced, RowItemMisplaced, EffectExpected, EffectExpected, EffectExpected, RowItemMisplaced ]

    it "apply an effect a type operator stands for to its operands, then to what an application adds" do
      shows [ "f :: Unit -> Int / {| (Int & Int) String, s :: (Int & T) Int Int |}" ]
        "[] (Prim.Unit -> Prim.Int / {| A.Both Prim.Int Prim.Int Prim.String, s :: A.Both Prim.Int A.T Prim.Int Prim.Int |})"
        []

  describe "synthesized arguments" do
    it "stand on the spine, behind quantifiers, constraints, and one another" do
      shows [ "f :: forall a. T => {{ d :: Show a by show }} -> {{ _ :: Show T by show }} -> a" ]
        "[] (forall a#0. (A.T => ({{d :: (A.Show a#0) by A.show}} -> ({{_ :: (A.Show A.T) by A.show}} -> a#0))))"
        []

    it "are misplaced after an ordinary parameter and inside one" do
      shows [ "f :: Int -> {{ d :: Show Int by show }} -> ({{ e :: Show Int by show }} -> Int) -> Int" ]
        "[] (Prim.Int -> (! -> ((! -> Prim.Int) -> Prim.Int)))"
        [ SynthesizedMisplaced, SynthesizedMisplaced ]

    it "report a synthesizer nothing stands for" do
      shows [ "f :: {{ d :: Show Int by nope }} -> Int" ] "[] (! -> Prim.Int)" [ UnknownValue "nope" ]

    it "leave a computation type after one invalid in a signature that is no computation's, `CST.Check` reporting it" do
      shows [ "f :: {{ d :: Show Int by show }} -> Int / {| E |}" ] "[] !" []

    it "put the variables a spine binds in scope for the body" do
      resolving [ "f :: forall a. {{ d :: Show a by show }} -> (forall b. a -> b -> c)" ]
        (map (map (renderVars <<< signatureScope) <<< resolveSignature) <<< signatureOf "f")
        \r -> r.result `shouldEqual` "c#0 a#1 b#2"

  describe "computation signatures" do
    it "hold the quantifiers and constraints in the order written, the result, and the row" do
      resolving [ "f :: forall a. T => forall b. a / {| State b, ...r |}" ]
        (map (map renderComputation <<< resolveComputationSignature) <<< signatureOf "f")
        \r -> do
          r.result `shouldEqual` "[r#0] forall a#1. A.T => forall b#2. a#1 / {| A.State b#2, ...r#0 |}"
          r.reasons `shouldEqual` []
      resolving [ "f :: forall a. T => forall b. a / {| State b, ...r |}" ]
        (map (map (renderVars <<< computationScope) <<< resolveComputationSignature) <<< signatureOf "f")
        \r -> r.result `shouldEqual` "r#0 a#1 b#2"

    it "hold synthesized arguments on the spine, the arrow after one being pure" do
      resolving [ "f :: forall a. T => {{ d :: Show a by show }} -> ({{ _ :: Show T by show }} -> a / {| E |})" ]
        (map (map renderComputation <<< resolveComputationSignature) <<< signatureOf "f")
        \r -> do
          r.result `shouldEqual` "[] forall a#0. A.T => {{d :: (A.Show a#0) by A.show}} -> {{_ :: (A.Show A.T) by A.show}} -> a#0 / {| A.E |}"
          r.reasons `shouldEqual` []

  describe "operation signatures" do
    let
      operations decls = Array.findMap
        ( case _ of
            CST.DeclEffect _ params ops -> Just do
              b <- bindTypeVariables params
              withTypeVariables b.scope (map (joinWith "; ") (traverseOps ops))
            _ -> Nothing
        )
        decls
      traverseOps ops = map (map renderOperation) (sequenceOps (map (resolveOperationSignature <<< _.type) ops))
      sequenceOps = Array.foldl (\acc x -> Array.snoc <$> acc <*> x) (pure [])
    it "hold their own variables, the arguments, and the type they resume with" do
      resolving
        [ "effect St s where"
        , "  get :: Unit ->* s"
        , "  put :: s -> Int ->* Unit"
        , "  abort :: forall b. Unit ->* b"
        , "  cont :: Int ->* Int -> s"
        ]
        operations
        \r -> do
          r.result `shouldEqual`
            "[] Prim.Unit ->* s#0; [] s#0 Prim.Int ->* Prim.Unit; [b#1] Prim.Unit ->* b#1; [] Prim.Int ->* (Prim.Int -> s#0)"
          r.reasons `shouldEqual` []

    it "quantify nothing implicitly" do
      resolving [ "effect St s where", "  get :: Unit ->* t" ] operations \r -> do
        r.result `shouldEqual` "[] Prim.Unit ->* !"
        r.reasons `shouldEqual` [ UnknownTypeVariable "t" ]

  describe "handler signatures" do
    let
      handlerWith :: forall a. (Signature HandlerSignature -> a) -> Array CST.Decl -> Maybe (Resolve a)
      handlerWith f = Array.findMap case _ of
        CST.DeclHandler _ _ t _ -> Just (map f (resolveHandlerSignature t))
        _ -> Nothing
      handler = handlerWith renderHandler
      clause = "  fast | get _ -> resume ()"
    it "read `E ~> ( t̄ )` as a capability translation" do
      resolving [ "handler h :: State s ~> ( E, Both s Int ) where", clause ] handler \r -> do
        r.result `shouldEqual` "[s#0] A.State s#0 ~> A.E, A.Both s#0 Prim.Int"
        r.reasons `shouldEqual` []
      resolving [ "handler h :: E ~> () where", clause ] handler \r ->
        r.result `shouldEqual` "[] A.E ~> "
      resolving [ "handler h :: E ~> ( State Int ) where", clause ] handler \r ->
        r.result `shouldEqual` "[] A.E ~> A.State Prim.Int"
      resolving [ "handler h :: E ~> ( (Int & Int) String ) where", clause ] handler \r ->
        r.result `shouldEqual` "[] A.E ~> A.Both Prim.Int Prim.Int Prim.String"

    it "read each quantifier in front of `~>` as binding over the rest, all of them in scope over the handler" do
      resolving [ "handler h :: forall s. (forall (t :: Type). State s ~> ( Both s t, State u )) where", clause ] handler \r -> do
        r.result `shouldEqual` "[u#0] forall s#1. forall (t#2 :: Type). A.State s#1 ~> A.Both s#1 t#2, A.State u#0"
        r.reasons `shouldEqual` []
      resolving [ "handler h :: forall s. (forall (t :: Type). State s ~> ( Both s t, State u )) where", clause ]
        (handlerWith (renderVars <<< handlerScope))
        \r -> r.result `shouldEqual` "u#0 s#1 t#2"
      resolving [ "handler h :: forall s s. State s ~> () where", clause ] handler \r -> do
        r.result `shouldEqual` "[] forall s#0 s#1. A.State s#0 ~> "
        r.reasons `shouldEqual` [ BoundTwice "s" ]
        r.warnings `shouldEqual` []
      resolving [ "handler h :: forall s. forall s. State s ~> () where", clause ] handler \r -> do
        r.result `shouldEqual` "[] forall s#0. forall s#1. A.State s#1 ~> "
        r.reasons `shouldEqual` []
        r.warnings `shouldEqual` [ "s" ]
      resolving [ "handler h :: forall s. forall s. State s ~> () where", clause ] (handlerWith (renderVars <<< handlerScope)) \r ->
        r.result `shouldEqual` "s#0 s#1"

    it "report what `~>` translates into where it is no list of effects" do
      resolving [ "handler h :: E ~> E where", clause ] handler \r -> do
        r.result `shouldEqual` "[] A.E ~> "
        r.reasons `shouldEqual` [ CapabilityTargetMalformed ]

    it "read any other type as written in full, and `~>` nowhere else" do
      resolving [ "handler h :: (Unit -> a / {| E |}) -> a where", clause ] handler \r ->
        r.result `shouldEqual` "[a#0] ((Prim.Unit -> a#0 / {| A.E |}) -> a#0)"
      shows [ "f :: Int -> (E ~> ())" ] "[] (Prim.Int -> !)" [ CapabilityMisplaced ]

renderVar :: TypeVar -> String
renderVar (TypeVar v) = case v.name, v.id of
  TyVar n, BindingId i -> n <> "#" <> show i

renderVars :: Array TypeVar -> String
renderVars = joinWith " " <<< map renderVar

renderSignature :: Signature Type -> String
renderSignature s = "[" <> renderVars s.implicit <> "] " <> renderType s.body

renderComputation :: Signature ComputationType -> String
renderComputation s =
  "[" <> renderVars s.implicit <> "] "
    <> joinWith "" (map prefix s.body.prefix)
    <> renderType s.body.result
    <> " / "
    <> renderType s.body.row
  where
  prefix = case _ of
    PrefixForall _ bs -> "forall " <> renderBinders bs <> ". "
    PrefixConstraint c -> renderType c <> " => "
    PrefixSynthesized t -> renderType t <> " -> "

renderOperation :: OperationSignature -> String
renderOperation o =
  "[" <> renderBinders o.binders <> "] "
    <> joinWith " " (map renderType o.arguments)
    <> " ->* "
    <> renderType o.resumesWith

renderHandler :: Signature HandlerSignature -> String
renderHandler s = "[" <> renderVars s.implicit <> "] " <> case s.body of
  Capability c -> joinWith "" (map (\bs -> "forall " <> renderBinders bs <> ". ") c.quantifiers)
    <> renderApplication c.source
    <> " ~> "
    <> joinWith ", " (map renderApplication c.targets)
  General t -> renderType t

renderBinders :: Array TypeVarBinder -> String
renderBinders = joinWith " " <<< map \b -> case b.kind of
  Nothing -> renderVar b.var
  Just k -> "(" <> renderVar b.var <> " :: " <> renderKind k <> ")"

renderKind :: Kind -> String
renderKind = case _ of
  KindType _ -> "Type"
  KindEffect _ -> "Effect"
  KindRow _ K.RowType -> "Row Type"
  KindRow _ K.RowEffect -> "Row Effect"
  KindArrow _ a b -> "(" <> renderKind a <> " -> " <> renderKind b <> ")"
  KindVariable _ (KindVar k) -> k
  KindInvalid _ -> "!"

renderType :: Type -> String
renderType = case _ of
  TypeVariable _ v -> renderVar v
  TypeConstructor _ q -> qualified q
  TypeSynonym _ q -> "syn:" <> qualified q
  TypeWildcard _ -> "_"
  TypeHole _ h -> "?" <> h
  TypeApp _ f a -> "(" <> renderType f <> " " <> renderType a <> ")"
  TypeOperator _ op l r -> "(" <> target op.target <> " " <> renderType l <> " " <> renderType r <> ")"
  TypeFunction _ a b row -> "(" <> renderType a <> " -> " <> renderType b <> maybe "" (\r -> " / " <> renderType r) row <> ")"
  TypeForall _ bs t -> "(forall " <> renderBinders bs <> ". " <> renderType t <> ")"
  TypeConstrained _ c t -> "(" <> renderType c <> " => " <> renderType t <> ")"
  TypeKinded _ t k -> "(" <> renderType t <> " :: " <> renderKind k <> ")"
  TypeTuple _ ts -> "(" <> joinWith ", " (map renderType ts) <> ")"
  TypeRecord _ items -> "{ " <> joinWith ", " (map record items) <> " }"
  TypeVariant _ items -> "[ " <> joinWith ", " (map variant items) <> " ]"
  TypeEffectRow _ items -> "{| " <> joinWith ", " (map effect items) <> " |}"
  TypeSynthesized _ n t f ->
    "{{" <> maybe "_" (\(Ident i) -> i) n <> " :: " <> renderType t <> " by " <> qualifiedIdent f <> "}}"
  TypeInvalid _ -> "!"
  where
  target = case _ of
    TargetTypeConstructor q -> qualified q
    TargetTypeSynonym q -> "syn:" <> qualified q
    TargetEffect (Qualified (ModuleName m) (EffName e)) -> "eff:" <> m <> "." <> e
  record = case _ of
    RecordField _ (Symbol l) t -> l <> " :: " <> renderType t
    RecordSpread _ t -> spread t
  variant = case _ of
    VariantTag _ (Tag l) t -> "'" <> l <> " :: " <> renderType t
    VariantLabel _ (Symbol l) t -> l <> " :: " <> renderType t
    VariantSpread _ t -> spread t
  effect = case _ of
    EffectElement a -> renderApplication a
    EffectInstance _ (Symbol l) a -> l <> " :: " <> renderApplication a
    EffectSpread _ t -> spread t
  spread = maybe "..." (\t -> "..." <> renderType t)

renderApplication :: EffectApplication -> String
renderApplication a = case a.effect of
  Qualified (ModuleName m) (EffName e) -> joinWith " " ([ m <> "." <> e ] <> map renderType a.arguments)

qualified :: Qualified TyName -> String
qualified (Qualified (ModuleName m) (TyName n)) = m <> "." <> n

qualifiedIdent :: Qualified Ident -> String
qualifiedIdent (Qualified (ModuleName m) (Ident n)) = m <> "." <> n
