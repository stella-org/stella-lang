-- | The trusted bundle a guest synthesizer is written against: `Stella.Elab`, the
-- | signature fragment that types its handles, and the shape descriptor read off it.
-- |
-- | What is held here is that the three agree with each other and with the kernel's
-- | own vocabulary: the module checks and lowers, every constructor of a mirrored
-- | host type has its twin of the same name whose fields have, in order, the shapes
-- | the host's fields are carried as, the descriptor gives every
-- | field a shape, and a guest can perform `command` and cannot take a handle apart.
-- | The typed facade is held to the host's: each operation has the host facade's
-- | name, makes the request the host's operation makes, takes its fields in order, and
-- | gives back what the answer the host's table gives it carries.
module Test.Stella.Compiler.Elaborate.GuestBundle (spec) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Either (Either(..), isLeft)
import Data.Foldable (for_)
import Data.Generic.Rep (class Generic, Argument, Constructor, NoArguments, Product, Sum(..), from)
import Data.Map as Map
import Data.Maybe (Maybe(..), isNothing)
import Data.String as String
import Data.Symbol (class IsSymbol, reflectSymbol)
import Data.Tuple (Tuple(..))
import Stella.Compiler.Bytecode (lower)
import Stella.Compiler.Elaborate.Environment.Catalog (EntrySort)
import Stella.Compiler.Elaborate.Protocol.Guest (abortEffect, breachEffect, bundle, commandOp, elabModule, elabRow, guestAnswerTy, guestCommandTy, guestModule, handleTy, kernelEffect, nameTy, operationType, operations, withGuest)
import Stella.Compiler.Elaborate.Protocol.Guest.Shape (Descriptor, Shape(..))
import Stella.Compiler.Elaborate.Vocabulary.Handle (Handle)
import Stella.Compiler.Elaborate.Vocabulary.Message (MessagePart)
import Stella.Compiler.Elaborate.Vocabulary.Request (AnswerShape, BuildRequest, HandlerRequest, KernelAnswer, KernelRequest(..), ObserveRequest, RecordRequest, ReportRequest, SolveRequest, TermRequest, TreeRequest, expectedAnswerShape)
import Stella.Compiler.Elaborate.Vocabulary.View (ConstraintView, KindView, PayloadView, TypeView)
import Stella.Compiler.Interface (noImports)
import Stella.Compiler.MiddleEnd (translate)
import Stella.Compiler.TypedCore.Check (CheckError(..))
import Stella.Compiler.TypedCore.Declare (DeclError(..))
import Stella.Compiler.TypedCore (Constant, Decl(..), DecisionTree(..), Expr(..), Ident(..), KindVar, Literal, Module, ModuleName(..), OpName, Occurrence(..), Qualified(..), RowEntry(..), RowElemKind, RowKey(..), ScalarString, ScalarValue, Symbol, Tag, TyName(..), TyVar(..), Type(..), Kind(..), declareAnnotated, monoScheme, primSignature)
import Stella.Compiler.TypedCore.Prim (asFunction, fn, intTy, pureFn, unitTy)
import Test.Stella.Compiler.Elaborate.Facade (probes)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual, shouldSatisfy)
import Prim.RowList (class RowToList, Cons, Nil, RowList)
import Type.Proxy (Proxy(..))

-- The shape a host type has once it crosses to a guest -----------------------------------

-- | The field shape a value of the host type is carried as. Names are strings, a
-- | qualified name is a `Name`, an array is a `List`, and a mirrored host type is
-- | its twin; this is stated here, apart from the module, so that the module's
-- | fields are held to the host's and not to themselves.
class HostShape :: P.Type -> P.Constraint
class HostShape a where
  hostShape :: Proxy a -> Shape

twin :: P.String -> Shape
twin n = ShapeData (Qualified elabModule (TyName n)) []

instance HostShape Handle where
  hostShape _ = ShapeToken

instance HostShape P.String where
  hostShape _ = ShapeString

instance HostShape P.Int where
  hostShape _ = ShapeInt

instance HostShape P.Number where
  hostShape _ = ShapeNumber

instance HostShape P.Boolean where
  hostShape _ = ShapeBoolean

instance HostShape ScalarValue where
  hostShape _ = ShapeChar

instance HostShape ScalarString where
  hostShape _ = ShapeString

instance HostShape Ident where
  hostShape _ = ShapeString

instance HostShape TyVar where
  hostShape _ = ShapeString

instance HostShape KindVar where
  hostShape _ = ShapeString

instance HostShape OpName where
  hostShape _ = ShapeString

instance HostShape Symbol where
  hostShape _ = ShapeString

instance HostShape Tag where
  hostShape _ = ShapeString

instance HostShape (Qualified a) where
  hostShape _ = ShapeData nameTy []

instance HostShape a => HostShape (P.Array a) where
  hostShape _ = ShapeData (Qualified elabModule (TyName "List")) [ hostShape (Proxy :: Proxy a) ]

instance HostShape a => HostShape (Maybe a) where
  hostShape _ = ShapeData (Qualified elabModule (TyName "Maybe")) [ hostShape (Proxy :: Proxy a) ]

instance (RowToList r rl, FieldShapes rl) => HostShape (P.Record r) where
  hostShape _ = ShapeRecord (Array.sortWith _.key (fieldShapes (Proxy :: Proxy rl)))

instance HostShape KernelRequest where
  hostShape _ = twin "KernelRequest"

instance HostShape BuildRequest where
  hostShape _ = twin "BuildRequest"

instance HostShape TermRequest where
  hostShape _ = twin "TermRequest"

instance HostShape TreeRequest where
  hostShape _ = twin "TreeRequest"

instance HostShape RecordRequest where
  hostShape _ = twin "RecordRequest"

instance HostShape HandlerRequest where
  hostShape _ = twin "HandlerRequest"

instance HostShape SolveRequest where
  hostShape _ = twin "SolveRequest"

instance HostShape ObserveRequest where
  hostShape _ = twin "ObserveRequest"

instance HostShape ReportRequest where
  hostShape _ = twin "ReportRequest"

instance HostShape KernelAnswer where
  hostShape _ = twin "KernelAnswer"

instance HostShape TypeView where
  hostShape _ = twin "TypeView"

instance HostShape PayloadView where
  hostShape _ = twin "PayloadView"

instance HostShape KindView where
  hostShape _ = twin "KindView"

instance HostShape ConstraintView where
  hostShape _ = twin "ConstraintView"

instance HostShape RowElemKind where
  hostShape _ = twin "RowElemKind"

instance HostShape RowKey where
  hostShape _ = twin "RowKey"

instance HostShape Literal where
  hostShape _ = twin "Literal"

instance HostShape MessagePart where
  hostShape _ = twin "MessagePart"

instance HostShape EntrySort where
  hostShape _ = twin "EntrySort"

instance HostShape Constant where
  hostShape _ = twin "Constant"

class FieldShapes :: RowList P.Type -> P.Constraint
class FieldShapes rl where
  fieldShapes :: Proxy rl -> P.Array { key :: P.String, shape :: Shape }

instance FieldShapes Nil where
  fieldShapes _ = []

instance (IsSymbol key, HostShape a, FieldShapes rest) => FieldShapes (Cons key a rest) where
  fieldShapes _ = Array.cons
    { key: reflectSymbol (Proxy :: Proxy key), shape: hostShape (Proxy :: Proxy a) }
    (fieldShapes (Proxy :: Proxy rest))

-- The constructors of a host type, read off its generic representation -------------------

type CtorEntry = { name :: P.String, fields :: P.Array Shape }

class Ctors :: forall k. k -> P.Constraint
class Ctors rep where
  ctors :: Proxy rep -> P.Array CtorEntry

instance (Ctors a, Ctors b) => Ctors (Sum a b) where
  ctors _ = ctors (Proxy :: Proxy a) <> ctors (Proxy :: Proxy b)

instance (IsSymbol name, Fields a) => Ctors (Constructor name a) where
  ctors _ = [ { name: reflectSymbol (Proxy :: Proxy name), fields: fields (Proxy :: Proxy a) } ]

class Fields :: forall k. k -> P.Constraint
class Fields rep where
  fields :: Proxy rep -> P.Array Shape

instance Fields NoArguments where
  fields _ = []

instance HostShape a => Fields (Argument a) where
  fields _ = [ hostShape (Proxy :: Proxy a) ]

instance (Fields a, Fields b) => Fields (Product a b) where
  fields _ = fields (Proxy :: Proxy a) <> fields (Proxy :: Proxy b)

-- | The constructors of a host type, in declaration order, each with its fields'
-- | shapes.
hostCtors :: forall a rep. Generic a rep => Ctors rep => Proxy a -> P.Array CtorEntry
hostCtors _ = ctors (Proxy :: Proxy rep)

-- | The constructors a data type of `Stella.Elab` has in the descriptor read off the
-- | module, each with its fields' shapes.
guestCtors :: Descriptor -> P.String -> Maybe (P.Array CtorEntry)
guestCtors descriptor name = Map.lookup (Qualified elabModule (TyName name)) descriptor <#>
  \t -> map (\c -> { name: unIdent c.name, fields: c.fields }) t.constructors
  where
  unIdent (Qualified _ (Ident x)) = x

-- | Every host type the guest vocabulary mirrors, and its twin's name.
mirrored :: P.Array (Tuple P.String (P.Array CtorEntry))
mirrored =
  [ Tuple "KernelRequest" (hostCtors (Proxy :: Proxy KernelRequest))
  , Tuple "BuildRequest" (hostCtors (Proxy :: Proxy BuildRequest))
  , Tuple "TermRequest" (hostCtors (Proxy :: Proxy TermRequest))
  , Tuple "TreeRequest" (hostCtors (Proxy :: Proxy TreeRequest))
  , Tuple "RecordRequest" (hostCtors (Proxy :: Proxy RecordRequest))
  , Tuple "HandlerRequest" (hostCtors (Proxy :: Proxy HandlerRequest))
  , Tuple "SolveRequest" (hostCtors (Proxy :: Proxy SolveRequest))
  , Tuple "ObserveRequest" (hostCtors (Proxy :: Proxy ObserveRequest))
  , Tuple "ReportRequest" (hostCtors (Proxy :: Proxy ReportRequest))
  , Tuple "KernelAnswer" (hostCtors (Proxy :: Proxy KernelAnswer))
  , Tuple "TypeView" (hostCtors (Proxy :: Proxy TypeView))
  , Tuple "PayloadView" (hostCtors (Proxy :: Proxy PayloadView))
  , Tuple "KindView" (hostCtors (Proxy :: Proxy KindView))
  , Tuple "ConstraintView" (hostCtors (Proxy :: Proxy ConstraintView))
  , Tuple "RowElemKind" (hostCtors (Proxy :: Proxy RowElemKind))
  , Tuple "RowKey" (hostCtors (Proxy :: Proxy RowKey))
  , Tuple "Literal" (hostCtors (Proxy :: Proxy Literal))
  , Tuple "MessagePart" (hostCtors (Proxy :: Proxy MessagePart))
  , Tuple "EntrySort" (hostCtors (Proxy :: Proxy EntrySort))
  , Tuple "Constant" (hostCtors (Proxy :: Proxy Constant))
  ]

-- Probes --------------------------------------------------------------------------------

probeName :: ModuleName
probeName = ModuleName "Probe"

elab :: P.String -> Qualified Ident
elab x = Qualified elabModule (Ident x)

elabType :: P.String -> Type
elabType x = TCon (Qualified elabModule (TyName x)) []

kernelRow :: Type
kernelRow = TRowExtend (RowEffectEntry kernelEffect []) TRowEmpty

-- | A guest synthesizer: it asks for its goal's type and returns the goal. Each
-- | constructor it applies is widened into the ambient row, constructor arrows being
-- | pure (D8).
synthesizer :: Module Unit
synthesizer =
  { annotation: unit
  , name: probeName
  , imports: [ elabModule ]
  , exports: []
  , decls:
      [ DeclNonRec unit
          { name: Ident "synth"
          , scheme: monoScheme (fn (TCon handleTy []) kernelRow (TCon handleTy []))
          , value: Lam unit (Ident "g") (TCon handleTy [])
              ( Let unit (Ident "a") (elabType "GuestAnswer")
                  ( Perform unit (EffectKey kernelEffect) commandOp []
                      ( app "Kernel"
                          (app "ObserveRequest" (app "GoalType" (Var unit (Ident "g"))))
                      )
                  )
                  (Var unit (Ident "g"))
              )
          , attributes: []
          }
      ]
  }
  where
  app c x = App unit (OpenEff unit kernelRow (Global unit (elab c) [])) x

-- | A guest that takes a handle apart. A handle is intrinsic, so no dispatch on
-- | constructors reaches one.
takesApart :: Module Unit
takesApart =
  { annotation: unit
  , name: probeName
  , imports: [ elabModule ]
  , exports: []
  , decls:
      [ DeclNonRec unit
          { name: Ident "inspect"
          , scheme: monoScheme (pureFn (TCon handleTy []) (TCon intTy []))
          , value: Lam unit (Ident "h") (TCon handleTy [])
              (Case unit [ Var unit (Ident "h") ] (SwitchCtor (OccScrutinee 0) [] Nothing))
          , attributes: []
          }
      ]
  }

-- The facade, read against the host's -------------------------------------------------------

-- | The name of the constructor a value is built with, read off its generic
-- | representation.
class CtorName rep where
  ctorNameOf :: rep -> P.String

instance (CtorName a, CtorName b) => CtorName (Sum a b) where
  ctorNameOf = case _ of
    Inl a -> ctorNameOf a
    Inr b -> ctorNameOf b

instance IsSymbol name => CtorName (Constructor name a) where
  ctorNameOf _ = reflectSymbol (Proxy :: Proxy name)

nameOf :: forall a rep. Generic a rep => CtorName rep => a -> P.String
nameOf = ctorNameOf <<< from

-- | The family and the constructor of a host request.
requestNames :: KernelRequest -> { family :: P.String, request :: P.String }
requestNames request = { family: nameOf request, request: inner }
  where
  inner = case request of
    BuildRequest r -> nameOf r
    TermRequest r -> nameOf r
    TreeRequest r -> nameOf r
    RecordRequest r -> nameOf r
    HandlerRequest r -> nameOf r
    SolveRequest r -> nameOf r
    ObserveRequest r -> nameOf r
    ReportRequest r -> nameOf r

-- | The constructor of `KernelAnswer` an answer of the shape given is built with.
answerOfShape :: AnswerShape -> P.String
answerOfShape shape = case String.stripSuffix (String.Pattern "Shape") (show shape) of
  Just stem -> stem <> "Answer"
  Nothing -> show shape

-- | The fields a data type of `Stella.Elab` declares for a constructor, read off the
-- | module's declaration.
declaredFields :: P.String -> P.String -> Maybe (P.Array Type)
declaredFields typeName ctorName = do
  d <- Array.findMap
    ( case _ of
        DeclData _ d | d.name == TyName typeName -> Just d
        _ -> Nothing
    )
    guestModule.decls
  _.fields <$> Array.find (\c -> c.name == Ident ctorName) d.constructors

-- | An operation's type taken apart: the quantified variable, if any, each argument
-- | with the row of its arrow, and the result.
type Arrows = { quantified :: Maybe TyVar, arguments :: P.Array { argument :: Type, row :: Type }, result :: Type }

arrowsOf :: Type -> Arrows
arrowsOf = case _ of
  TForall v _ body -> (go [] body) { quantified = Just v }
  other -> go [] other
  where
  go acc t = case asFunction t of
    Just parts -> go (Array.snoc acc { argument: parts.argument, row: parts.row }) parts.result
    Nothing -> { quantified: Nothing, arguments: acc, result: t }

unitType :: Type
unitType = TCon unitTy []

handle :: Type
handle = TCon handleTy []

maybeOf :: Type -> Type
maybeOf = TApp (elabType "Maybe")

-- Cases ----------------------------------------------------------------------------------

descriptorOf :: Either P.String Descriptor
descriptorOf = map _.descriptor bundle

spec :: Spec Unit
spec = describe "Stella.Elab, the trusted bundle" do
  it "declares against a signature holding its handle type, and lowers" do
    case declareAnnotated (withGuest primSignature) guestModule of
      Left err -> fail ("Stella.Elab did not declare: " <> show err.error)
      Right declared -> case translate noImports guestModule declared of
        Left err -> fail ("Stella.Elab did not translate: " <> show err)
        Right mid -> case lower mid of
          Left err -> fail ("Stella.Elab did not lower: " <> show err)
          Right _ -> pure unit

  it "does not declare without the fragment that types its handles" do
    declareAnnotated primSignature guestModule `shouldSatisfy` isLeft

  it "gives every mirrored host type a twin with the same constructors, fields, and field order" do
    case descriptorOf of
      Left err -> fail ("no descriptor: " <> err)
      Right descriptor -> for_ mirrored \(Tuple name host) ->
        Tuple name (guestCtors descriptor name) `shouldEqual` Tuple name (Just host)

  it "holds the guest's own command, answer, and names, and nothing more of the host's control" do
    case descriptorOf of
      Left err -> fail ("no descriptor: " <> err)
      Right descriptor -> do
        guestCtors descriptor "GuestCommand" `shouldEqual` Just
          [ { name: "Kernel", fields: [ twin "KernelRequest" ] }
          , { name: "BeginTransaction", fields: [] }
          , { name: "CommitTransaction", fields: [] }
          ]
        guestCtors descriptor "GuestAnswer" `shouldEqual` Just
          [ { name: "Returned", fields: [ twin "KernelAnswer" ] }
          , { name: "TransactionBegun", fields: [] }
          , { name: "TransactionCommitted", fields: [] }
          , { name: "CandidateFailed", fields: [] }
          ]
        guestCtors descriptor "Name" `shouldEqual` Just
          [ { name: "Name", fields: [ ShapeString, ShapeString ] } ]

  it "reads a shape off every field of every data type" do
    case descriptorOf of
      Left err -> fail ("no descriptor: " <> err)
      Right descriptor -> do
        Map.size descriptor `shouldEqual` Array.length
          (Array.filter isData guestModule.decls)
        map _.constructors (Map.lookup guestAnswerTy descriptor) `shouldEqual` Just
          [ { name: elab "Returned", fields: [ ShapeData (kernelAnswer) [] ] }
          , { name: elab "TransactionBegun", fields: [] }
          , { name: elab "TransactionCommitted", fields: [] }
          , { name: elab "CandidateFailed", fields: [] }
          ]
        map _.params (Map.lookup guestCommandTy descriptor) `shouldEqual` Just 0
        map _.params (Map.lookup (Qualified elabModule (TyName "List")) descriptor) `shouldEqual` Just 1
        map _.constructors (Map.lookup (Qualified elabModule (TyName "Maybe")) descriptor) `shouldEqual` Just
          [ { name: elab "Nothing", fields: [] }, { name: elab "Just", fields: [ ShapeParam 0 ] } ]
        map _.constructors (Map.lookup (Qualified elabModule (TyName "MessagePart")) descriptor) `shouldEqual` Just
          [ { name: elab "TextPart", fields: [ ShapeString ] }
          , { name: elab "TypePart", fields: [ ShapeToken ] }
          , { name: elab "TermPart", fields: [ ShapeToken ] }
          , { name: elab "NamePart", fields: [ ShapeData (Qualified elabModule (TyName "Name")) [] ] }
          ]

  it "shapes a record by its fields in ascending order of key" do
    case descriptorOf of
      Left err -> fail err
      Right descriptor ->
        ( Map.lookup kernelAnswer descriptor
            >>= \t -> Array.find (\c -> c.name == elab "BinderAnswer") t.constructors
        ) `shouldEqual` Just
          { name: elab "BinderAnswer"
          , fields:
              [ ShapeRecord
                  [ { key: "binder", shape: ShapeToken }
                  , { key: "bodyScope", shape: ShapeToken }
                  , { key: "variable", shape: ShapeToken }
                  ]
              ]
          }

  it "lets a guest perform command, typed at the kernel row" do
    case declareAnnotated (withGuest primSignature) guestModule of
      Left err -> fail (show err.error)
      Right declared -> declareAnnotated declared.signature synthesizer `shouldSatisfy` isRight'

  describe "the typed facade" do
    it "has an operation for every public kernel operation, under the host's name and in its order" do
      map _.name operations `shouldEqual` map _.operation probes

    it "makes the request the host's operation of the same name makes, and takes back the answer the host's table gives it" do
      for_ probes \p -> case p.request, Array.find (\o -> o.name == p.operation) operations of
        Just request, Just o -> do
          let host = requestNames request
          Tuple p.operation { family: o.family, request: o.request } `shouldEqual` Tuple p.operation host
          Tuple p.operation o.answer `shouldEqual` Tuple p.operation (answerOfShape <$> expectedAnswerShape request)
        _, found -> fail (p.operation <> ": no request, or no guest operation: " <> show (map _.name found))

    it "takes the request's fields in order, curried, the last arrow alone at the facade's row" do
      for_ operations \o -> case declaredFields o.family o.request of
        Nothing -> fail (o.name <> ": no such request declared")
        Just fields -> do
          let
            arrows = arrowsOf (operationType o)
            expected = if Array.null fields then [ unitType ] else fields
            rows = map _.row arrows.arguments
          Tuple o.name (map _.argument arrows.arguments) `shouldEqual` Tuple o.name expected
          Tuple o.name (Array.dropEnd 1 rows) `shouldEqual` Tuple o.name (map (const TRowEmpty) (Array.dropEnd 1 rows))
          Tuple o.name (Array.last rows) `shouldEqual` Tuple o.name (Just elabRow)

    it "gives back what its answer carries, `Unit` for an answer carrying nothing, and anything for throw and postpone" do
      for_ operations \o -> do
        let arrows = arrowsOf (operationType o)
        case o.answer of
          Nothing -> Tuple o.name (map TVar arrows.quantified) `shouldEqual` Tuple o.name (Just arrows.result)
          Just answer -> case declaredFields "KernelAnswer" answer of
            Just [ carried ] -> Tuple o.name arrows.result `shouldEqual` Tuple o.name carried
            Just [] -> Tuple o.name arrows.result `shouldEqual` Tuple o.name unitType
            other -> fail (o.name <> ": the answer " <> answer <> " is not declared with at most one field: " <> show other)
        Tuple o.name (isNothing o.answer) `shouldEqual` Tuple o.name (o.name == "throw" || o.name == "postpone")

    it "declares every operation, transact, and synthesizer at the types the facade gives them" do
      case declareAnnotated (withGuest primSignature) guestModule of
        Left err -> fail (show err.error)
        Right declared -> do
          let
            schemeOf n = _.scheme.body <$> Map.lookup (elab n) declared.signature.values
            a = TyVar "a"
          for_ operations \o -> Tuple o.name (schemeOf o.name) `shouldEqual` Tuple o.name (Just (operationType o))
          schemeOf "transact" `shouldEqual` Just
            (TForall a KType (fn (fn unitType elabRow (TVar a)) elabRow (maybeOf (TVar a))))
          -- no escape is left in the row once a policy is made a synthesizer
          schemeOf "synthesizer" `shouldEqual` Just
            (pureFn (fn handle elabRow handle) (fn handle kernelRow handle))

    it "runs at a row holding each of its three effects once" do
      elabRow `shouldEqual`
        TRowExtend (RowEffectEntry abortEffect [])
          (TRowExtend (RowEffectEntry breachEffect []) (TRowExtend (RowEffectEntry kernelEffect []) TRowEmpty))

  it "refuses a guest that takes a handle apart" do
    case declareAnnotated (withGuest primSignature) guestModule of
      Left err -> fail (show err.error)
      Right declared -> case declareAnnotated declared.signature takesApart of
        Left { error: IllTyped (NotADataType name) } -> name `shouldEqual` handleTy
        Left err -> fail ("refused for another reason: " <> show err.error)
        Right _ -> fail "a guest took a handle apart"
  where
  kernelAnswer = Qualified elabModule (TyName "KernelAnswer")

  isData = case _ of
    DeclData _ _ -> true
    _ -> false

  isRight' = case _ of
    Right _ -> true
    Left _ -> false
