-- | The typed facade of `Stella.Elab`, run on the machine: every operation asks the
-- | command its request is and gives back what the answer it expects carries, and
-- | `transact` and `synthesizer` settle where a candidate fails and where the host
-- | answers outside its contract.
-- |
-- | Each operation is called by a probe of its own, a guest made a synthesizer: it
-- | calls the operation on arguments of every field's type — the goal wherever a
-- | handle goes — and returns what it gave back where that is a handle, and
-- | otherwise the handle `rootScope` then answers with. **An answer the operation
-- | does not expect ends the probe with its goal**, before it asks anything more,
-- | which is what tells the two apart.
-- |
-- | The probes are written in source here, from each operation's type on the
-- | interface, and appended to `fixtures/source/guests/facade/Probe.stel`, which
-- | holds the probes of `transact`; the module is built as a fixture is.
module Test.E2E.Facade (spec) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Either (Either(..), either)
import Data.Map as Map
import Data.Foldable (for_)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Tuple (Tuple(..))
import Effect.Aff (Aff)
import Stella.CLI.Session.Value (WireValue(..))
import Stella.Compiler.Bytecode.Module (Key(..))
import Stella.Compiler.Elaborate.Protocol.Guest (Operation, elabModule, handleTy, operationType, operations)
import Stella.Compiler.Interface.Module (TypeSort(..))
import Stella.Compiler.TypedCore (Ident(..), ModuleName(..), Qualified(..), RowEntry(..), RowKey(..), Symbol(..), TyName(..), Type(..))
import Stella.Compiler.TypedCore.Domain (scalarString)
import Stella.Compiler.TypedCore.Prim (asFunction, booleanTy, intTy, recordTy, stringTy, unitTy)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)
import Data.String as String
import E2E.Build (Sources, builtFrom)
import Test.E2E.Guest (Machine, elabInterface, Ran(..), goalToken, machineWith, runGuest, token, wire, wireList, wireText)

-- Arguments of every type ---------------------------------------------------------------------

-- | A value of a type the facade takes or gives, as source text and as a generic
-- | value. A handle is the one given; a list holds one element and an optional
-- | value one; any other data type of `Stella.Elab` is its first constructor.
type Sample = { text :: P.String, value :: WireValue }

sampleOf :: Sample -> Type -> Sample
sampleOf handle = go
  where
  go t = case t of
    TCon name []
      | name == handleTy' -> handle
      | name == stringTy -> { text: "\"s\"", value: wireText "s" }
      | name == booleanTy -> { text: "true", value: WBoolean true }
      | name == intTy -> { text: "1", value: WInt 1 }
      | name == unitTy -> { text: "()", value: WData unitName [] }
    TApp (TCon name []) row | name == recordTy ->
      let
        fields = entries row
      in
        { text: "{ " <> String.joinWith ", " (map (\(Tuple k s) -> k <> ": " <> s.text) fields) <> " }"
        , value: WRecord (map (\(Tuple k s) -> { key: KSymbol (Symbol k), value: s.value }) (Array.sortWith (\(Tuple k _) -> k) fields))
        }
    TApp (TCon name []) element
      | name == elabType "List" ->
          let s = go element in { text: "(Cons " <> s.text <> " Nil)", value: wireList [ s.value ] }
      | name == elabType "Maybe" ->
          let s = go element in { text: "(Just " <> s.text <> ")", value: wire "Just" [ s.value ] }
    TCon (Qualified _ (TyName n)) [] -> case firstCtor n of
      Just (Tuple c fields) ->
        let samples = map go fields in { text: applied c (map _.text samples), value: wire c (map _.value samples) }
      Nothing -> { text: "()", value: WString (unsafeText ("no sample of " <> n)) }
    _ -> { text: "()", value: WString (unsafeText "no sample") }

  applied c args = if Array.null args then c else "(" <> String.joinWith " " (Array.cons c args) <> ")"

  entries row = case row of
    TRowExtend (RowTypeEntry (SymbolKey (Symbol k)) t') rest -> Array.cons (Tuple k (go t')) (entries rest)
    _ -> []

  handleTy' = Qualified elabModule (TyName "Handle")
  unitName = Qualified (ModuleName "Prim") (Ident "Unit")

  unsafeText s = fromMaybe' (scalarString s)
  fromMaybe' = case _ of
    Just x -> x
    Nothing -> fromMaybe' (scalarString "")

handleT :: Type
handleT = TCon handleTy []

elabType :: P.String -> Qualified TyName
elabType n = Qualified elabModule (TyName n)

-- | The constructors a data type of the carried `Stella.Elab` declares, read off
-- | its interface.
constructorsOf :: P.String -> P.Array { name :: Ident, fields :: P.Array Type }
constructorsOf n = case elabInterface of
  Right i -> case Map.lookup (TyName n) i.declarations.types of
    Just { sort: DataType d } -> d.constructors
    _ -> []
  Left _ -> []

-- | The first constructor a data type of `Stella.Elab` declares, and its fields.
firstCtor :: P.String -> Maybe (Tuple P.String (P.Array Type))
firstCtor n = do
  c <- Array.head (constructorsOf n)
  pure (Tuple (unIdent c.name) c.fields)
  where
  unIdent (Ident x) = x

-- | The type of an operation read off the carried interface, or none where it
-- | cannot be read, which the first case reports.
typeOfOperation :: Operation -> Either P.String Type
typeOfOperation o = elabInterface >>= \i -> operationType i o

goalSample :: Sample
goalSample = { text: "goal", value: WToken goalToken }

-- | What a handle in an answer is: a token no request holds.
answered :: Sample
answered = { text: "()", value: WToken (token "answered") }

marker :: WireValue
marker = WToken (token "marker")

-- The probes ----------------------------------------------------------------------------------

-- | What an operation takes and gives back, its quantifier instantiated at `Handle`.
type Signature' = { parameters :: P.Array Type, result :: Type }

signatureOf :: Operation -> Signature'
signatureOf o = go [] case typeOfOperation o of
  Right (TForall v _ body) -> substitute v body
  Right t -> t
  Left _ -> TCon unitTy []
  where
  go acc t = case asFunction t of
    Just parts -> go (Array.snoc acc parts.argument) parts.result
    Nothing -> { parameters: acc, result: t }

  substitute v = case _ of
    TVar w | w == v -> handleT
    TApp f x -> TApp (substitute v f) (substitute v x)
    other -> other

probeModuleName :: ModuleName
probeModuleName = ModuleName "Probe"

-- | A type of the facade as source text: the names of `Stella.Elab` and of `Prim`,
-- | which the probes import whole, applied, and closed records.
typeText :: Type -> P.String
typeText = case _ of
  TCon (Qualified _ (TyName n)) [] -> n
  TApp (TCon name []) row | name == recordTy -> "{ " <> String.joinWith ", " (fieldsOf row) <> " }"
  TApp f x -> "(" <> typeText f <> " " <> typeText x <> ")"
  _ -> "?"
  where
  fieldsOf = case _ of
    TRowExtend (RowTypeEntry (SymbolKey (Symbol k)) t) rest -> Array.cons (k <> " :: " <> typeText t) (fieldsOf rest)
    _ -> []

-- | `probe_<operation> = synthesizer \goal -> let result = operation samples in
-- | result`, `rootScope ()` in place of `result` where it is no handle; what an
-- | operation answering nothing gives is a handle.
probeText :: Operation -> P.String
probeText o = String.joinWith "\n"
  [ ""
  , name <> " :: Handle -> Handle / {| Kernel |}"
  , name <> " = synthesizer \\goal ->"
  , "  let"
  , "    result :: " <> typeText sig.result
  , "    result = " <> String.joinWith " " (Array.cons o.name (map (_.text <<< sampleOf goalSample) sig.parameters))
  , "  in"
  , "    " <> (if sig.result == handleT then "result" else "rootScope ()")
  ]
  where
  name = "probe_" <> o.name
  sig = signatureOf o

-- | The command an operation's probe asks first.
commandOf :: Operation -> WireValue
commandOf o = wire "Kernel"
  [ wire o.family
      [ wire o.request (map (_.value <<< sampleOf goalSample) (Array.filter (_ /= TCon unitTy []) (signatureOf o).parameters)) ]
  ]

-- | The answer an operation expects, carrying a sample of what it carries.
expectedAnswer :: Operation -> P.String -> WireValue
expectedAnswer _ answer = wire "Returned"
  [ wire answer case fieldsOfAnswer answer of
      [ carried ] -> [ (sampleOf answered carried).value ]
      _ -> []
  ]

fieldsOfAnswer :: P.String -> P.Array Type
fieldsOfAnswer answer = fromMaybe [] (_.fields <$> Array.find (\c -> c.name == Ident answer) (constructorsOf "KernelAnswer"))

-- | Another answer than the one expected.
otherAnswer :: Operation -> WireValue
otherAnswer o = case o.answer of
  Just "UnitAnswer" -> wire "Returned" [ wire "HandleAnswer" [ (answered).value ] ]
  _ -> wire "Returned" [ wire "UnitAnswer" [] ]

rootScopeCommand :: WireValue
rootScopeCommand = wire "Kernel" [ wire "BuildRequest" [ wire "RootScope" [] ] ]

-- The cases ---------------------------------------------------------------------------------

-- | `Probe`: the probes of `transact` the fixture holds, and one for each
-- | operation, appended.
withProbes :: Sources -> (Machine -> Aff Unit) -> Aff Unit
withProbes sources k = case builtFrom (sources { files = Map.update (\written -> Just (written <> String.joinWith "\n" (map probeText operations) <> "\n")) probes sources.files }) [ "guests/facade" ] of
  Left err -> fail ("the probes did not compile: " <> err)
  Right dmos -> machineWith dmos >>= k
  where
  probes = "fixtures/source/guests/facade/Probe.stel"

run :: Machine -> P.String -> P.Array WireValue -> Aff Ran
run machine name = runGuest machine (Qualified probeModuleName (Ident name)) [ goalToken ]

goalValue :: WireValue
goalValue = WToken goalToken

begin :: WireValue
begin = wire "BeginTransaction" []

commit :: WireValue
commit = wire "CommitTransaction" []

goalTypeCommand :: WireValue
goalTypeCommand = wire "Kernel" [ wire "ObserveRequest" [ wire "GoalType" [ goalValue ] ] ]

spec :: Sources -> Spec Unit
spec sources = describe "Stella.Elab, the typed facade on the machine" do
  it "reads every operation's type off the interface of the `Stella.Elab` the compiler carries" do
    for_ operations \o -> Tuple o.name (either Just (const Nothing) (typeOfOperation o)) `shouldEqual` Tuple o.name Nothing

  it "asks each operation's request, and gives back what the answer it expects carries" do
    withProbes sources \machine -> for_ operations \o -> do
      let first = commandOf o
      ran <- run machine ("probe_" <> o.name) case o.answer of
        Nothing -> [ wire "Returned" [ wire "UnitAnswer" [] ] ]
        Just answer -> [ expectedAnswer o answer, wire "Returned" [ wire "HandleAnswer" [ marker ] ] ]
      Tuple o.name ran `shouldEqual` Tuple o.name case o.answer of
        -- the host ends the attempt rather than answering these: an answer is a breach
        Nothing -> Returned [ first ] goalValue
        Just answer
          | fieldsOfAnswer answer == [ handleT ] -> Returned [ first ] answered.value
          | otherwise -> Returned [ first, rootScopeCommand ] marker

  it "ends with its goal where an operation is answered with another answer, before asking anything more" do
    withProbes sources \machine -> for_ operations \o -> do
      ran <- run machine ("probe_" <> o.name) [ otherAnswer o ]
      Tuple o.name ran `shouldEqual` Tuple o.name (Returned [ commandOf o ] goalValue)

  it "ends with its goal where a command is answered with no kernel answer at all" do
    withProbes sources \machine -> for_ operations \o -> do
      ran <- run machine ("probe_" <> o.name) [ wire "TransactionCommitted" [] ]
      Tuple o.name ran `shouldEqual` Tuple o.name (Returned [ commandOf o ] goalValue)

  it "ends with its goal where a candidate fails outside every transaction" do
    withProbes sources \machine -> for_ operations \o -> do
      ran <- run machine ("probe_" <> o.name) [ wire "CandidateFailed" [] ]
      Tuple o.name ran `shouldEqual` Tuple o.name (Returned [ commandOf o ] goalValue)

  describe "transact" do
    it "answers Nothing in the innermost transaction a candidate fails in, and the one around it commits" do
      withProbes sources \machine -> do
        ran <- run machine "nested"
          [ wire "TransactionBegun" []
          , wire "TransactionBegun" []
          , wire "CandidateFailed" []
          , wire "Returned" [ wire "HandleAnswer" [ marker ] ]
          , wire "TransactionCommitted" []
          ]
        ran `shouldEqual` Returned
          [ begin
          , begin
          , wire "Kernel" [ wire "ReportRequest" [ wire "Throw" [ wireList [ wire "TextPart" [ wireText "no" ] ] ] ] ]
          , rootScopeCommand
          , commit
          ]
          marker

    it "answers Just what the candidate returned where the transaction commits" do
      withProbes sources \machine -> do
        ran <- run machine "guarded"
          [ wire "TransactionBegun" []
          , wire "Returned" [ wire "HandleAnswer" [ marker ] ]
          , wire "TransactionCommitted" []
          ]
        ran `shouldEqual` Returned [ begin, goalTypeCommand, commit ] marker

    it "answers Nothing where the candidate fails, sending nothing to close it" do
      withProbes sources \machine -> do
        ran <- run machine "guarded"
          [ wire "TransactionBegun" []
          , wire "CandidateFailed" []
          , wire "Returned" [ wire "HandleAnswer" [ marker ] ]
          ]
        ran `shouldEqual` Returned [ begin, goalTypeCommand, rootScopeCommand ] marker

    it "answers Nothing where the transaction fails as it commits" do
      withProbes sources \machine -> do
        ran <- run machine "guarded"
          [ wire "TransactionBegun" []
          , wire "Returned" [ wire "HandleAnswer" [ WToken (token "found") ] ]
          , wire "CandidateFailed" []
          , wire "Returned" [ wire "HandleAnswer" [ marker ] ]
          ]
        ran `shouldEqual` Returned [ begin, goalTypeCommand, commit, rootScopeCommand ] marker

    it "lets a breach inside it through to the synthesizer, which ends with its goal" do
      withProbes sources \machine -> do
        ran <- run machine "guarded"
          [ wire "TransactionBegun" []
          , wire "Returned" [ wire "UnitAnswer" [] ]
          ]
        -- neither committed nor answered `Nothing`: nothing more is asked
        ran `shouldEqual` Returned [ begin, goalTypeCommand ] goalValue

    it "ends with its goal where a transaction is not begun" do
      withProbes sources \machine -> do
        ran <- run machine "guarded" [ wire "Returned" [ wire "UnitAnswer" [] ] ]
        ran `shouldEqual` Returned [ begin ] goalValue
