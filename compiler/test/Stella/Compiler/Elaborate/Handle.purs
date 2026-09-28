-- | Opaque handles: their lifetime, and what refuses one that names nothing.
-- |
-- | Two things are what these cases are for. **A handle lives for the attempt
-- | that issued it and its contents are transactional**, so a handle issued
-- | before a `transact` survives that `transact` rolling back while one issued
-- | inside it does not. And **a generation is never issued twice**, which is
-- | what makes a handle to a deleted object fail to match whatever the reused
-- | slot holds next.
module Test.Stella.Compiler.Elaborate.Handle (spec) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.CorePlus.Context (Origin(..))
import Stella.Compiler.Elaborate.Vocabulary.Diagnostic (Defect(..), Diagnostic(..))
import Stella.Compiler.Elaborate.Kernel.Elab (Elab, Outcome(..), SolverState, emptySessionEnv, initialState, issue, postpone, resolveExpr, resolveMeta, resolveType, runElab, raiseDiagnostic, transact)
import Stella.Compiler.Elaborate.Vocabulary.Handle (Handle(..), HandleClass(..), HandleError(..), HandleObject(..), SessionId(..))
import Stella.Compiler.Elaborate.CorePlus.Kind (XKind(..))
import Stella.Compiler.Elaborate.Mechanism.Kinding (KindEvidence(..), emptyScope)
import Stella.Compiler.Elaborate.Driver.Attempt (runAttempt)
import Stella.Compiler.Elaborate.CorePlus.Type (MetaVar(..), XType(..))
import Stella.Compiler.Elaborate.Mechanism.Unify (UnifyError(..))
import Stella.Compiler.TypedCore (Ident(..), ModuleName(..), Qualified(..), TyName(..))
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Data.Tuple (Tuple(..), fst)
import Effect.Aff (Aff)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

prim :: ModuleName
prim = ModuleName "Prim"

tA :: XType
tA = XCon (Qualified prim (TyName "A")) []

tB :: XType
tB = XCon (Qualified prim (TyName "B")) []

typeA :: HandleObject
typeA = TypeObject { type: tA, kind: ExactKind XKType, scope: emptyScope, builtIn: Nothing }

typeB :: HandleObject
typeB = TypeObject { type: tB, kind: ExactKind XKType, scope: emptyScope, builtIn: Nothing }

session :: SolverState
session = initialState (SessionId 0) 10

-- | A failure a candidate is discarded with.
discarded :: Diagnostic
discarded = EquationFailed (InDeclaration (Qualified prim (Ident "decl"))) (TypeNotEqual tA tB)

-- | Run an action to completion and continue with what it produced.
produced :: forall a. Show a => Tuple (Outcome a) SolverState -> (a -> SolverState -> Aff Unit) -> Aff Unit
produced (Tuple outcome s) k = case outcome of
  Done a -> k a s
  _ -> fail ("the action did not complete: " <> show outcome)

type Fields =
  { session :: SessionId
  , handleClass :: HandleClass
  , slot :: P.Int
  , generation :: P.Int
  }

forged :: Handle -> (Fields -> Fields) -> Handle
forged (Handle h) f = Handle (f h)

-- | The first handle a session issues: slot 0, generation 0.
first :: HandleClass -> Handle
first handleClass = Handle { session: SessionId 0, handleClass, slot: 0, generation: 0 }

-- | A candidate that is issued a handle and is then discarded.
issuedAndDiscarded :: Elab Unit
issuedAndDiscarded = void (transact (issue typeA *> (raiseDiagnostic discarded :: Elab Unit)))

spec :: Spec Unit
spec = describe "Elaborate.Handle" do
  describe "resolving" do
    it "gives back the object a handle names, as the class it was issued for" do
      produced (runElab session (issue typeA >>= resolveType)) \object _ ->
        object `shouldEqual` { type: tA, kind: ExactKind XKType, scope: emptyScope, builtIn: Nothing }

    it "refuses a handle presented as another class" do
      produced (runElab session (issue typeA)) \h s ->
        fst (runElab s (resolveExpr h)) `shouldEqual` Broke (InvalidHandle h (HandleClassMismatch ExprClass))

    it "refuses a handle whose stated class is forged over the object it names" do
      produced (runElab session (issue typeA)) \h s -> do
        let
          claimsExpr = forged h (_ { handleClass = ExprClass })
        fst (runElab s (resolveExpr claimsExpr))
          `shouldEqual` Broke (InvalidHandle claimsExpr (HandleClassMismatch ExprClass))

    it "refuses a handle another session issued" do
      produced (runElab (initialState (SessionId 1) 10) (issue typeA)) \h _ ->
        fst (runElab session (resolveType h)) `shouldEqual` Broke (InvalidHandle h ForeignHandle)

    it "refuses a generation never issued, and a negative one, as unknown" do
      produced (runElab session (issue typeA)) \h s -> do
        let
          ahead = forged h (_ { generation = 5 })
          negative = forged h (_ { generation = -1 })
        fst (runElab s (resolveType ahead)) `shouldEqual` Broke (InvalidHandle ahead UnknownHandle)
        fst (runElab s (resolveType negative)) `shouldEqual` Broke (InvalidHandle negative UnknownHandle)

  describe "inside one attempt" do
    it "keeps a handle issued before a transact that rolled back" do
      let
        action = do
          before <- issue typeA
          issuedAndDiscarded
          resolveType before
      produced (runElab session action) \object _ -> object `shouldEqual` { type: tA, kind: ExactKind XKType, scope: emptyScope, builtIn: Nothing }

    it "loses a handle issued inside a transact that rolled back" do
      -- The discarded candidate was the first thing issued a handle. Presenting
      -- it again is what a synthesizer caching one across candidates would do.
      let
        action = issuedAndDiscarded *> resolveType (first TypeClass)
      fst (runElab session action) `shouldEqual` Broke (InvalidHandle (first TypeClass) StaleHandle)

    it "refuses an old handle once its slot holds another object, the two generations differing" do
      let
        action = issuedAndDiscarded *> issue typeB
      produced (runElab session action) \new s -> do
        let
          Handle fields = new
        fields.slot `shouldEqual` 0
        fields.generation `shouldEqual` 1
        fst (runElab s (resolveType (first TypeClass))) `shouldEqual` Broke (InvalidHandle (first TypeClass) StaleHandle)
        fst (runElab s (resolveType new)) `shouldEqual` Done { type: tB, kind: ExactKind XKType, scope: emptyScope, builtIn: Nothing }

    it "does not give back a generation when it rolls back" do
      produced (runElab session issuedAndDiscarded) \_ s ->
        s.retained.nextGeneration `shouldEqual` 1

  describe "across attempts" do
    it "invalidates a handle once the attempt that issued it has committed" do
      let
        Tuple outcome s = runAttempt emptySessionEnv (issue typeA) session
      case outcome of
        Done h -> fst (runAttempt emptySessionEnv (resolveType h) s) `shouldEqual` Broke (InvalidHandle h StaleHandle)
        _ -> fail ("the attempt did not commit: " <> show outcome)

    it "invalidates one issued by an attempt that postponed, keeping its generation spent" do
      let
        issuing = issue (MetaObject (MetaVar 0)) *> (postpone (Set.singleton (MetaVar 0)) :: Elab Unit)
        Tuple _ s = runAttempt emptySessionEnv issuing session
      fst (runAttempt emptySessionEnv (resolveMeta (first MetaClass)) s)
        `shouldEqual` Broke (InvalidHandle (first MetaClass) StaleHandle)
      s.retained.nextGeneration `shouldEqual` 1

  describe "the supply of generations" do
    it "stops the session rather than issue a generation twice" do
      let
        spent = session { retained { nextGeneration = top } }
      fst (runElab spent (issue typeA)) `shouldEqual` Broke GenerationsExhausted
