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
module Test.Steam.Facade (spec) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Tuple (Tuple(..))
import Effect.Aff (Aff)
import Stella.CLI.Session.Value (WireValue(..))
import Stella.Compiler.Bytecode.Module (Key(..))
import Stella.Compiler.Elaborate.Protocol.Guest (Operation, elabModule, guestModule, kernelEffect, operationType, operations)
import Stella.Compiler.TypedCore (DecisionTree(..), Decl(..), Expr(..), Ident(..), Literal(..), Module, ModuleName(..), Occurrence(..), Qualified(..), RowEntry(..), RowKey(..), Symbol(..), TyName(..), Type(..), monoScheme)
import Stella.Compiler.TypedCore.Domain (scalarString)
import Stella.Compiler.TypedCore.Prim (asFunction, booleanTy, fn, intTy, recordTy, stringTy, unitTy)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)
import Test.Steam.Guest (Machine, Ran(..), call, compileGuest, construct, elab, elabRow, elabT, global, goalToken, handleT, listOf, machineWith, runGuest, text, token, unitValue, wire, wireList, wireText)

-- Arguments of every type ---------------------------------------------------------------------

-- | A value of a type the facade takes or gives, as a term and as a generic value.
-- | A handle is the one given; a list holds one element and an optional value one;
-- | any other data type of `Stella.Elab` is its first constructor.
type Sample = { term :: Expr Unit, value :: WireValue }

sampleOf :: Sample -> Type -> Sample
sampleOf handle = go
  where
  go t = case t of
    TCon name []
      | name == handleTy' -> handle
      | name == stringTy -> { term: text "s", value: wireText "s" }
      | name == booleanTy -> { term: Lit unit (LitBoolean true), value: WBoolean true }
      | name == intTy -> { term: Lit unit (LitInt 1), value: WInt 1 }
      | name == unitTy -> { term: unitValue, value: WData unitName [] }
    TApp (TCon name []) row | name == recordTy ->
      let
        fields = entries row
      in
        { term: Array.foldr (\(Tuple k s) rest -> RecordExtend unit (SymbolKey (Symbol k)) s.term rest) (RecordEmpty unit) fields
        , value: WRecord (map (\(Tuple k s) -> { key: KSymbol (Symbol k), value: s.value }) (Array.sortWith (\(Tuple k _) -> k) fields))
        }
    TApp (TCon name []) element
      | name == elabType "List" ->
          let s = go element in { term: listOf element [ s.term ], value: wireList [ s.value ] }
      | name == elabType "Maybe" ->
          let s = go element in { term: construct elabRow "Just" [ element ] [ s.term ], value: wire "Just" [ s.value ] }
    TCon (Qualified _ (TyName n)) [] -> case firstCtor n of
      Just (Tuple c fields) ->
        let samples = map go fields in { term: construct elabRow c [] (map _.term samples), value: wire c (map _.value samples) }
      Nothing -> { term: unitValue, value: WString (unsafeText ("no sample of " <> n)) }
    _ -> { term: unitValue, value: WString (unsafeText "no sample") }

  entries row = case row of
    TRowExtend (RowTypeEntry (SymbolKey (Symbol k)) t') rest -> Array.cons (Tuple k (go t')) (entries rest)
    _ -> []

  handleTy' = Qualified elabModule (TyName "Handle")
  unitName = Qualified (ModuleName "Prim") (Ident "Unit")

  unsafeText s = fromMaybe' (scalarString s)
  fromMaybe' = case _ of
    Just x -> x
    Nothing -> fromMaybe' (scalarString "")

elabType :: P.String -> Qualified TyName
elabType n = Qualified elabModule (TyName n)

-- | The first constructor a data type of `Stella.Elab` declares, and its fields.
firstCtor :: P.String -> Maybe (Tuple P.String (P.Array Type))
firstCtor n = do
  d <- Array.findMap
    ( case _ of
        DeclData _ d | d.name == TyName n -> Just d
        _ -> Nothing
    )
    guestModule.decls
  c <- Array.head d.constructors
  pure (Tuple (unIdent c.name) c.fields)
  where
  unIdent (Ident x) = x

goalSample :: Sample
goalSample = { term: Var unit goal, value: WToken goalToken }

-- | What a handle in an answer is: a token no request holds.
answered :: Sample
answered = { term: unitValue, value: WToken (token "answered") }

marker :: WireValue
marker = WToken (token "marker")

goal :: Ident
goal = Ident "goal"

-- The probes ----------------------------------------------------------------------------------

-- | What an operation takes and gives back, its quantifier instantiated at `Handle`.
type Signature' = { parameters :: P.Array Type, result :: Type }

signatureOf :: Operation -> Signature'
signatureOf o = go [] case operationType o of
  TForall v _ body -> substitute v body
  t -> t
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

-- | `synthesizer (λgoal. let result = op samples in result)`, or `rootScope ()` in
-- | place of `result` where it is no handle.
probeDecl :: Operation -> Decl Unit
probeDecl o = DeclNonRec unit
  { name: Ident ("probe_" <> o.name)
  , scheme: monoScheme synthesizerType
  , value: App unit (global "synthesizer")
      ( Lam unit goal handleT
          ( Let unit result sig.result (call operation (map (_.term <<< sampleOf goalSample) sig.parameters))
              (if sig.result == handleT then Var unit result else call (global "rootScope") [ unitValue ])
          )
      )
  , attributes: []
  }
  where
  sig = signatureOf o
  result = Ident "result"
  operation = case o.answer of
    Nothing -> TyApp unit (global o.name) handleT
    Just _ -> global o.name

synthesizerType :: Type
synthesizerType = fn handleT (TRowExtend (RowEffectEntry kernelEffect []) TRowEmpty) handleT

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
fieldsOfAnswer answer = fromMaybe [] do
  d <- Array.findMap
    ( case _ of
        DeclData _ d | d.name == TyName "KernelAnswer" -> Just d
        _ -> Nothing
    )
    guestModule.decls
  _.fields <$> Array.find (\c -> c.name == Ident answer) d.constructors

-- | Another answer than the one expected.
otherAnswer :: Operation -> WireValue
otherAnswer o = case o.answer of
  Just "UnitAnswer" -> wire "Returned" [ wire "HandleAnswer" [ (answered).value ] ]
  _ -> wire "Returned" [ wire "UnitAnswer" [] ]

rootScopeCommand :: WireValue
rootScopeCommand = wire "Kernel" [ wire "BuildRequest" [ wire "RootScope" [] ] ]

-- Transactions ----------------------------------------------------------------------------------

-- | `transact [Handle] (λ_. body)`.
transacting :: P.String -> Expr Unit -> Expr Unit
transacting binder body = call (TyApp unit (global "transact") handleT) [ Lam unit (Ident binder) (TCon unitTy []) body ]

-- | `case e of Just h -> h; Nothing -> otherwise`.
orElse :: P.String -> Expr Unit -> Expr Unit -> Expr Unit
orElse binder e otherwise = Case unit [ e ]
  ( SwitchCtor (OccScrutinee 0)
      [ { ctor: elab "Just", tree: Bind (Ident binder) (OccField (OccScrutinee 0) (elab "Just") 0) (Leaf (Var unit (Ident binder))) }
      , { ctor: elab "Nothing", tree: Leaf otherwise }
      ]
      Nothing
  )

rootScope :: Expr Unit
rootScope = call (global "rootScope") [ unitValue ]

synthesizing :: P.String -> Expr Unit -> Decl Unit
synthesizing name body = DeclNonRec unit
  { name: Ident name
  , scheme: monoScheme synthesizerType
  , value: App unit (global "synthesizer") (Lam unit goal handleT body)
  , attributes: []
  }

-- | A `throw` inside a `transact` inside another, then `rootScope`: the inner
-- | answers `Nothing` and the outer commits with the handle.
nested :: Decl Unit
nested = synthesizing "nested" $
  orElse "outer"
    ( transacting "u1"
        ( Let unit (Ident "inner") (TApp (TCon (elabType "Maybe") []) handleT)
            ( transacting "u2"
                (call (TyApp unit (global "throw") handleT) [ listOf (elabT "MessagePart") [ construct elabRow "TextPart" [] [ text "no" ] ] ])
            )
            rootScope
        )
    )
    (Var unit goal)

-- | `goalType goal` inside a `transact`, and `rootScope` where the transaction
-- | answers `Nothing`.
guarded :: Decl Unit
guarded = synthesizing "guarded" $
  orElse "found" (transacting "u3" (call (global "goalType") [ Var unit goal ])) rootScope

probeModule :: Module Unit
probeModule =
  { annotation: unit
  , name: probeModuleName
  , imports: [ elabModule ]
  , exports: []
  , decls: map probeDecl operations <> [ nested, guarded ]
  }

-- The cases ---------------------------------------------------------------------------------

withProbes :: (Machine -> Aff Unit) -> Aff Unit
withProbes k = case compileGuest probeModule of
  Left err -> fail ("the probes did not compile: " <> err)
  Right dmo -> machineWith [ dmo ] >>= k

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

spec :: Spec Unit
spec = describe "Stella.Elab, the typed facade on the machine" do
  it "asks each operation's request, and gives back what the answer it expects carries" do
    withProbes \machine -> for_ operations \o -> do
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
    withProbes \machine -> for_ operations \o -> do
      ran <- run machine ("probe_" <> o.name) [ otherAnswer o ]
      Tuple o.name ran `shouldEqual` Tuple o.name (Returned [ commandOf o ] goalValue)

  it "ends with its goal where a command is answered with no kernel answer at all" do
    withProbes \machine -> for_ operations \o -> do
      ran <- run machine ("probe_" <> o.name) [ wire "TransactionCommitted" [] ]
      Tuple o.name ran `shouldEqual` Tuple o.name (Returned [ commandOf o ] goalValue)

  it "ends with its goal where a candidate fails outside every transaction" do
    withProbes \machine -> for_ operations \o -> do
      ran <- run machine ("probe_" <> o.name) [ wire "CandidateFailed" [] ]
      Tuple o.name ran `shouldEqual` Tuple o.name (Returned [ commandOf o ] goalValue)

  describe "transact" do
    it "answers Nothing in the innermost transaction a candidate fails in, and the one around it commits" do
      withProbes \machine -> do
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
      withProbes \machine -> do
        ran <- run machine "guarded"
          [ wire "TransactionBegun" []
          , wire "Returned" [ wire "HandleAnswer" [ marker ] ]
          , wire "TransactionCommitted" []
          ]
        ran `shouldEqual` Returned [ begin, goalTypeCommand, commit ] marker

    it "answers Nothing where the candidate fails, sending nothing to close it" do
      withProbes \machine -> do
        ran <- run machine "guarded"
          [ wire "TransactionBegun" []
          , wire "CandidateFailed" []
          , wire "Returned" [ wire "HandleAnswer" [ marker ] ]
          ]
        ran `shouldEqual` Returned [ begin, goalTypeCommand, rootScopeCommand ] marker

    it "answers Nothing where the transaction fails as it commits" do
      withProbes \machine -> do
        ran <- run machine "guarded"
          [ wire "TransactionBegun" []
          , wire "Returned" [ wire "HandleAnswer" [ WToken (token "found") ] ]
          , wire "CandidateFailed" []
          , wire "Returned" [ wire "HandleAnswer" [ marker ] ]
          ]
        ran `shouldEqual` Returned [ begin, goalTypeCommand, commit, rootScopeCommand ] marker

    it "lets a breach inside it through to the synthesizer, which ends with its goal" do
      withProbes \machine -> do
        ran <- run machine "guarded"
          [ wire "TransactionBegun" []
          , wire "Returned" [ wire "UnitAnswer" [] ]
          ]
        -- neither committed nor answered `Nothing`: nothing more is asked
        ran `shouldEqual` Returned [ begin, goalTypeCommand ] goalValue

    it "ends with its goal where a transaction is not begun" do
      withProbes \machine -> do
        ran <- run machine "guarded" [ wire "Returned" [ wire "UnitAnswer" [] ] ]
        ran `shouldEqual` Returned [ begin ] goalValue
