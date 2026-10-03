-- | Modules resolved as a whole, each declaration shown as a compact rendering
-- | of what the Surface AST holds of it.
module Test.Stella.Compiler.Resolve.Module (spec) where

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
import Stella.Compiler.Interface.Environment (BuildEnvironment, addInterface, initialEnvironment)
import Stella.Compiler.Interface.Module (Constant(..), ModuleInterface, TypeEntity(..), TypeSort(..), ValueSort(..), Via(..), emptyDeclarations, emptyExports)
import Stella.Compiler.Interface.Scheme (SchemeBody(..), plainScheme)
import Stella.Compiler.Resolve.Module (ResolutionError(..), resolveModule)
import Stella.Compiler.Resolve.Monad (HandledEffectProblem(..), ResolveError(..), ResolveReason(..))
import Stella.Compiler.Resolve.Scope (ScopeError(..), ScopeReason(..))
import Stella.Compiler.Surface.Decl (Attribute, Constant(..), Declaration(..), FixityTarget(..), Observation(..)) as Surface
import Stella.Compiler.Surface.Name (OperatorName(..))
import Stella.Compiler.Surface.Type (TypeOperatorTarget(..))
import Stella.Compiler.TypedCore.Domain (textOf)
import Stella.Compiler.TypedCore.Kind (Kind(..), monoScheme)
import Stella.Compiler.TypedCore.Name (EffName(..), Ident(..), ModuleName(..), Qualified(..), Symbol(..), TyName(..))
import Stella.Compiler.TypedCore.Prim (intTy)
import Stella.Compiler.TypedCore.Term (Literal(..))
import Stella.Compiler.TypedCore.Type (Type(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

moduleA :: ModuleName
moduleA = ModuleName "A"

inA :: forall a. a -> Qualified a
inA = Qualified moduleA

-- | `A` declares the value `x`, the computation `comp`, `data Maybe = Nothing
-- | | Just Int`, `attribute priority Int`, and `attribute tag (level :: Int =
-- | 3)`. `Stella.Elab` declares `attribute synthesizedBy`.
environment :: BuildEnvironment
environment = case addInterface interfaceA initialEnvironment >>= addInterface elab of
  Right env -> env
  Left _ -> initialEnvironment
  where
  int = TCon intTy []
  plain = plainScheme (monoScheme int)

  declared :: forall a. a -> { entity :: a, via :: Via }
  declared e = { entity: e, via: Declared }

  interfaceA :: ModuleInterface
  interfaceA =
    { name: moduleA
    , imports: []
    , exports: emptyExports
        { values = Map.fromFoldable (map (\n -> Tuple n (declared (inA (Ident n)))) [ "x", "comp", "Nothing", "Just" ])
        , types = Map.singleton "Maybe" { entity: TypeEntity (inA (TyName "Maybe")), via: Declared, members: [ Ident "Nothing", Ident "Just" ] }
        , attributes = Map.fromFoldable (map (\n -> Tuple n (declared (inA (Ident n)))) [ "priority", "tag" ])
        }
    , declarations: emptyDeclarations
        { values = Map.fromFoldable
            [ Tuple (Ident "x") { sort: SortValue, scheme: plain, attributes: [] }
            , Tuple (Ident "comp") { sort: SortValue, scheme: { kindVars: [], body: Computation int TRowEmpty }, attributes: [] }
            , Tuple (Ident "Nothing") { sort: SortConstructor (inA (TyName "Maybe")), scheme: plain, attributes: [] }
            , Tuple (Ident "Just") { sort: SortConstructor (inA (TyName "Maybe")), scheme: plain, attributes: [] }
            ]
        , types = Map.singleton (TyName "Maybe")
            { kind: monoScheme KType
            , sort: DataType { params: [], constructors: [ { name: Ident "Nothing", fields: [] }, { name: Ident "Just", fields: [ int ] } ], isNewtype: false }
            , attributes: []
            }
        , attributes = Map.fromFoldable
            [ Tuple (Ident "priority") { positional: [ int ], keyword: [] }
            , Tuple (Ident "tag") { positional: [], keyword: [ { label: "level", type: int, default: Just (ConstantLiteral (LitInt 3)) } ] }
            ]
        }
    , implicitHandlers: []
    , catalogOnly: Set.empty
    , arities: Map.empty
    }

  elab :: ModuleInterface
  elab =
    { name: ModuleName "Stella.Elab"
    , imports: []
    , exports: emptyExports { attributes = Map.singleton "synthesizedBy" (declared (Qualified (ModuleName "Stella.Elab") (Ident "synthesizedBy"))) }
    , declarations: emptyDeclarations { attributes = Map.singleton (Ident "synthesizedBy") { positional: [], keyword: [] } }
    , implicitHandlers: []
    , catalogOnly: Set.empty
    , arities: Map.empty
    }

type Ran = { declarations :: Array String, errors :: Array String }

-- | The module `M`, importing `A` and `Stella.Elab` as `E`, with the lines
-- | given as its declarations.
resolved :: String -> Array String -> (Ran -> Aff Unit) -> Aff Unit
resolved name body k = case parseModule (joinWith "\n" ([ "module " <> name <> " where", "import A", "import Stella.Elab as E" ] <> body)) of
  Left e -> fail (printSyntaxError e)
  Right m -> do
    let r = resolveModule environment m
    k { declarations: map renderDeclaration r.module.declarations, errors: map renderError r.errors }

shows :: Array String -> Array String -> Array String -> Aff Unit
shows body declarations errors = resolved "M" body \r -> do
  r.declarations `shouldEqual` declarations
  r.errors `shouldEqual` errors

spec :: Spec Unit
spec = describe "Stella.Compiler.Resolve.Module" do
  describe "declarations" do
    it "are resolved in the order written, each into what it declares" do
      shows
        [ "f :: Int -> Int"
        , "f n = n"
        , "c :: Int / {| |}"
        , "c = 1"
        , "data Box a = Box a | Empty"
        , "newtype Wrap = Wrap Int"
        , "type Pair :: Type -> Type"
        , "type Pair a = (a, a)"
        , "effect Ask a where"
        , "  ask :: Unit ->* a"
        , "handler h :: Ask Int ~> () where"
        , "  fast | ask _ -> 0"
        , "#observ(none)"
        , "foreign sqrt :: Number -> Number"
        , "foreign type Ref :: Type -> Type"
        , "infixl 6 f as +++"
        , "infixr 0 type Pair as ***"
        , "attribute json (name :: String) (omitEmpty :: Boolean = false)"
        ]
        [ "value M.f"
        , "computation M.c"
        , "data M.Box (M.Box, M.Empty)"
        , "newtype M.Wrap (M.Wrap)"
        , "synonym M.Pair kinded"
        , "effect M.Ask (M.ask)"
        , "handler M.h of M.Ask"
        , "foreign M.sqrt observes none"
        , "foreign type M.Ref"
        , "infix M.+++ value M.f"
        , "type infix M.*** synonym M.Pair"
        , "attribute M.json 0 [name, omitEmpty=false]"
        ]
        []

    it "are left out where nothing could be held, and reported" do
      shows
        [ "c :: Int / {| |}"
        , "c n = 1"
        , "infixl 6 nope as +++"
        , "infixr 0 type Nope as ***"
        , "handler h :: Int -> Int where"
        , "  | return r -> r"
        , "m%( 1 )"
        ]
        []
        [ "ComputationWithParameters c", "UnknownValue nope", "UnknownType Nope", "HandledEffect HandlerShape", "NotYetSupported" ]

    it "name a computation or a constructor as an operator's target" do
      shows [ "infixl 6 comp as +++", "infixr 5 Just as :::" ] [ "infix M.+++ value A.comp", "infix M.::: constructor A.Just" ] []

    it "bind their parameters over what they hold, and nothing else" do
      shows [ "data Bad = Bad a" ] [ "data M.Bad (M.Bad)" ] [ "UnknownTypeVariable a" ]

  describe "attributes" do
    it "are normalized: every keyword argument in the order declared, a default filled in" do
      shows
        [ "attribute json (name :: String) (omitEmpty :: Boolean = false)"
        , "@[json name=\"u\"]"
        , "@[priority 10]"
        , "@[tag]"
        , "f = 1"
        ]
        [ "attribute M.json 0 [name, omitEmpty=false]", "value M.f @M.json(; name=\"u\", omitEmpty=false) @A.priority(10) @A.tag(; level=3)" ]
        []

    it "whose arguments do not match their declaration are reported and left out" do
      shows
        [ "attribute json (name :: String) (omitEmpty :: Boolean = false)"
        , "@[priority]"
        , "@[json]"
        , "@[json name=\"a\" name=\"b\"]"
        , "@[json nme=\"a\"]"
        , "@[nope]"
        , "f = 1"
        ]
        [ "attribute M.json 0 [name, omitEmpty=false]", "value M.f" ]
        [ "AttributeArity priority 1 0", "KeywordMissing json name", "KeywordTwice name", "KeywordUnknown json nme", "KeywordMissing json name", "UnknownAttribute nope" ]

    it "take constants, and keep an attribute whose argument is none" do
      shows [ "@[priority x]", "@[priority (Just 1)]", "@[priority { a: 1, b: () }]", "f = 1" ]
        [ "value M.f @A.priority(A.x) @A.priority((A.Just 1)) @A.priority({ a: 1, b: Prim.Unit })" ]
        []
      shows [ "@[priority comp]", "@[priority (Just)]", "@[priority { a: 1, a: 2 }]", "f = 1" ]
        [ "value M.f @A.priority(!) @A.priority(!) @A.priority({ a: 1, a: 2 })" ]
        [ "NotAConstant", "ConstructorArity Just", "LabelTwice a" ]

    it "stand on no fixity or attribute declaration, and those the compiler reads once on what they are for" do
      shows
        [ "@[priority 1]"
        , "infixl 6 x as +++"
        , "@[priority 1]"
        , "attribute flag"
        , "@[macro]"
        , "data T = T"
        , "@[E.synthesizedBy]"
        , "effect Ask where"
        , "  ask :: Unit ->* Int"
        , "@[entrypoint]"
        , "@[entrypoint]"
        , "main = 1"
        ]
        [ "infix M.+++ value A.x", "attribute M.flag 0 []", "data M.T (M.T)", "effect M.Ask (M.ask)", "value M.main @Prim.entrypoint" ]
        [ "AttributeMisplaced priority", "AttributeMisplaced priority", "AttributeMisplaced macro", "AttributeMisplaced E.synthesizedBy", "AttributeTwice entrypoint" ]

    it "leave `elaborationOnly` the scope refused out, unreported again, and keep it where the compiler lists the declaration" do
      shows [ "@[elaborationOnly]", "data T = T" ] [ "data M.T (M.T)" ] [ "ElaborationOnlyNotAllowed" ]
      resolved "Base.Continuation" [ "@[elaborationOnly]", "newtype Continuation a = Continuation a" ] \r -> do
        r.declarations `shouldEqual` [ "newtype Base.Continuation.Continuation (Base.Continuation.$Continuation) @Prim.elaborationOnly" ]
        r.errors `shouldEqual` []

  describe "the attributes the scope acts on" do
    it "change nothing where they are later refused, on a computation or written with an argument" do
      shows [ "@[macro]", "c :: Int / {| |}", "c = 1", "@[macro 1]", "g = 1", "f = (c, g)" ]
        [ "computation M.c", "value M.g", "value M.f" ]
        [ "AttributeMisplaced macro", "AttributeArity macro 0 1" ]
      shows [ "@[elaborationOnly 1]", "data T = T" ] [ "data M.T (M.T)" ] [ "AttributeArity elaborationOnly 0 1" ]
      resolved "Base.Continuation" [ "@[elaborationOnly 1]", "newtype Continuation a = Continuation a" ] \r -> do
        r.declarations `shouldEqual` [ "newtype Base.Continuation.Continuation (Base.Continuation.Continuation)" ]
        r.errors `shouldEqual` [ "AttributeArity elaborationOnly 0 1" ]

    it "count a use whose arguments do not match toward the one each declaration may carry" do
      shows [ "@[entrypoint bad=1]", "@[entrypoint]", "main = 1" ] [ "value M.main" ] [ "KeywordUnknown entrypoint bad", "AttributeTwice entrypoint" ]
      shows [ "@[macro 1]", "@[macro]", "f = 1", "g = f" ] [ "value M.f", "value M.g" ] [ "AttributeArity macro 0 1", "AttributeTwice macro" ]
      shows [ "@[elaborationOnly]", "@[elaborationOnly]", "data T = T" ] [ "data M.T (M.T)" ] [ "ElaborationOnlyNotAllowed", "AttributeTwice elaborationOnly" ]
      resolved "Base.Continuation" [ "@[elaborationOnly 1]", "@[elaborationOnly]", "newtype Continuation a = Continuation a" ] \r -> do
        r.declarations `shouldEqual` [ "newtype Base.Continuation.Continuation (Base.Continuation.Continuation)" ]
        r.errors `shouldEqual` [ "AttributeArity elaborationOnly 0 1", "AttributeTwice elaborationOnly" ]

  describe "attribute declarations" do
    it "take positional parameters first, each keyword once, and closed types" do
      shows [ "attribute bad (k :: Int) Int", "attribute dup (k :: Int) (k :: Int)", "attribute open (a -> a)" ]
        [ "attribute M.bad 1 [k]", "attribute M.dup 0 [k]", "attribute M.open 1 []" ]
        [ "PositionalAfterKeyword", "KeywordParameterTwice k", "UnknownTypeVariable a", "UnknownTypeVariable a" ]

renderDeclaration :: Surface.Declaration -> String
renderDeclaration = case _ of
  Surface.DeclValue d -> "value " <> qualified d.name <> attributes d.attributes
  Surface.DeclComputation d -> "computation " <> qualified d.name <> attributes d.attributes
  Surface.DeclData d -> "data " <> typeName d.name <> " (" <> joinWith ", " (map (qualified <<< _.name) d.constructors) <> ")" <> attributes d.attributes
  Surface.DeclNewtype d -> "newtype " <> typeName d.name <> " (" <> qualified d.constructor.name <> ")" <> attributes d.attributes
  Surface.DeclSynonym d -> "synonym " <> typeName d.name <> maybe "" (const " kinded") d.kind <> attributes d.attributes
  Surface.DeclEffect d -> "effect " <> effectName d.name <> " (" <> joinWith ", " (map (qualified <<< _.name) d.operations) <> ")" <> attributes d.attributes
  Surface.DeclHandler d -> "handler " <> qualified d.name <> " of " <> effectName d.effect <> attributes d.attributes
  Surface.DeclForeign d -> "foreign " <> qualified d.name <> (if d.observation == Surface.ObservesNone then " observes none" else "") <> attributes d.attributes
  Surface.DeclForeignType d -> "foreign type " <> typeName d.name <> attributes d.attributes
  Surface.DeclFixity d -> "infix " <> operator d.operator <> " " <> case d.target of
    Surface.FixityValue q -> "value " <> qualified q
    Surface.FixityConstructor q -> "constructor " <> qualified q
  Surface.DeclTypeFixity d -> "type infix " <> operator d.operator <> " " <> case d.target of
    TargetTypeConstructor q -> "constructor " <> typeName q
    TargetTypeSynonym q -> "synonym " <> typeName q
    TargetEffect e -> "effect " <> effectName e
  Surface.DeclAttribute d ->
    "attribute " <> qualified d.name <> " " <> show (Array.length d.positional) <> " ["
      <> joinWith ", " (map (\k -> k.label <> maybe "" (\c -> "=" <> constant c) k.default) d.keyword)
      <> "]"
  where
  operator (OperatorName o) = "M." <> o

attributes :: Array Surface.Attribute -> String
attributes = joinWith "" <<< map \a ->
  " @" <> qualified a.name <>
    if Array.null a.positional && Array.null a.keyword then ""
    else "(" <> joinWith ", " (map constant a.positional) <> (if Array.null a.keyword then "" else "; " <> joinWith ", " (map (\k -> k.label <> "=" <> constant k.value) a.keyword)) <> ")"

constant :: Surface.Constant -> String
constant = case _ of
  Surface.ConstantLiteral _ l -> case l of
    LitInt i -> show i
    LitBoolean b -> show b
    LitString s -> show (textOf s)
    LitNumber n -> show n
    LitChar _ -> "char"
  Surface.ConstantValue _ q -> qualified q
  Surface.ConstantConstructor _ q [] -> qualified q
  Surface.ConstantConstructor _ q cs -> "(" <> qualified q <> " " <> joinWith " " (map constant cs) <> ")"
  Surface.ConstantRecord _ fs -> "{ " <> joinWith ", " (map (\f -> case f.label of Symbol l -> l <> ": " <> constant f.value) fs) <> " }"
  Surface.ConstantInvalid _ -> "!"

renderError :: ResolutionError -> String
renderError = case _ of
  ResolvingError (ResolveError _ reason) -> case reason of
    ComputationWithParameters n -> "ComputationWithParameters " <> n
    UnknownValue n -> "UnknownValue " <> n
    UnknownType n -> "UnknownType " <> n
    UnknownTypeVariable n -> "UnknownTypeVariable " <> n
    HandledEffect HandlerShape -> "HandledEffect HandlerShape"
    NotYetSupported _ -> "NotYetSupported"
    AttributeArity n p w -> "AttributeArity " <> n <> " " <> show p <> " " <> show w
    KeywordMissing n l -> "KeywordMissing " <> n <> " " <> l
    KeywordTwice l -> "KeywordTwice " <> l
    KeywordUnknown n l -> "KeywordUnknown " <> n <> " " <> l
    UnknownAttribute n -> "UnknownAttribute " <> n
    NotAConstant -> "NotAConstant"
    ConstructorArity n _ _ -> "ConstructorArity " <> n
    LabelTwice l -> "LabelTwice " <> l
    AttributeMisplaced n -> "AttributeMisplaced " <> n
    AttributeTwice n -> "AttributeTwice " <> n
    PositionalAfterKeyword -> "PositionalAfterKeyword"
    KeywordParameterTwice l -> "KeywordParameterTwice " <> l
    other -> show other
  ScopingError (ScopeError _ ElaborationOnlyNotAllowed) -> "ElaborationOnlyNotAllowed"
  other -> show other

qualified :: Qualified Ident -> String
qualified (Qualified (ModuleName m) (Ident n)) = m <> "." <> n

typeName :: Qualified TyName -> String
typeName (Qualified (ModuleName m) (TyName n)) = m <> "." <> n

effectName :: Qualified EffName -> String
effectName (Qualified (ModuleName m) (EffName e)) = m <> "." <> e
