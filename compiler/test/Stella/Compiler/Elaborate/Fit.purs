-- | Fits: `source ⊆ target` decided on the difference of the two rows, placed
-- | where it can be decided and otherwise kept as a job, and made what it was
-- | decided to where its term is made Core.
module Test.Stella.Compiler.Elaborate.Fit (spec) where

import Prelude

import Data.Array as Array
import Data.Array.NonEmpty as NonEmptyArray
import Data.Either (Either(..))
import Data.Foldable (foldr)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Data.Tuple (Tuple(..))
import Effect.Aff (Aff)
import Stella.Compiler.Elaborate.CorePlus.Context (Origin(..), emptyXContext)
import Stella.Compiler.Elaborate.CorePlus.Kind (XKind(..))
import Stella.Compiler.Elaborate.CorePlus.Row (XRowNormalForm, emptyXNormalForm, xnf)
import Stella.Compiler.Elaborate.CorePlus.Term (FitId, Residue(..), XExpr(..), toCoreExpr)
import Stella.Compiler.Elaborate.CorePlus.Type (MetaVar(..), XRowEntry(..), XType(..))
import Stella.Compiler.Elaborate.Driver.Attempt (runAttempt)
import Stella.Compiler.Elaborate.Driver.Loop (RunResult(..), run)
import Stella.Compiler.Elaborate.Environment.Imported (sessionEnvOf)
import Stella.Compiler.Elaborate.Kernel.Elab (Elab, Outcome(..), SessionEnv, SolverState, equate, freshInstantiationRow, freshTypeMeta, initialState, placeFit, raiseDiagnostic)
import Stella.Compiler.Elaborate.Mechanism.Fit (Classified(..), FitState(..), FitUse(..), classify)
import Stella.Compiler.Elaborate.Mechanism.Pending (Job(..), Site)
import Stella.Compiler.Elaborate.Mechanism.TermMeta (zonkExpr)
import Stella.Compiler.Elaborate.Mechanism.Unify (isInstantiationRow, substitute)
import Stella.Compiler.Elaborate.Vocabulary.Diagnostic (Defect(..), Diagnostic(..))
import Stella.Compiler.Elaborate.Vocabulary.Handle (SessionId(..))
import Stella.Compiler.TypedCore (Expr(..), Literal(..), primSignature)
import Stella.Compiler.TypedCore.Kind (RowElemKind(..))
import Stella.Compiler.TypedCore.Name (EffName(..), Ident(..), ModuleName(..), Qualified(..), TyVar(..))
import Stella.Compiler.TypedCore.Prim (intTy, stringTy)
import Stella.Compiler.TypedCore.Type (RowKey(..), Type(..), RowEntry(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

session :: SessionEnv
session = sessionEnvOf primSignature []

site :: Site
site = { context: emptyXContext, origin: InDeclaration (Qualified (ModuleName "M") (Ident "f")) }

effect :: String -> Qualified EffName
effect = Qualified (ModuleName "M") <<< EffName

console :: XRowEntry
console = XRowEffectEntry (effect "Console") []

clock :: XRowEntry
clock = XRowEffectEntry (effect "Clock") []

state :: XType -> XRowEntry
state t = XRowEffectEntry (effect "State") [ t ]

int :: XType
int = XCon intTy []

string :: XType
string = XCon stringTy []

-- | A row of the entries given over the tail given.
row :: Array XRowEntry -> XType -> XType
row entries tail = foldr XRowExtend tail entries

closed :: Array XRowEntry -> XType
closed entries = row entries XRowEmpty

-- | The normal form of a row whose known part is the entries given.
known :: Array XRowEntry -> XRowNormalForm
known entries = emptyXNormalForm { known = Map.fromFoldable (map (\x -> Tuple (keyOf x) x) entries) }

keyOf :: XRowEntry -> RowKey
keyOf = case _ of
  XRowEffectEntry n _ -> EffectKey n
  XRowLabelledEffectEntry s _ _ -> SymbolKey s
  XRowTypeEntry k _ -> k
  XRowRegionEntry r -> RegionKey r

-- | `1`, as the expression a wrapping fit holds.
literal :: XExpr Unit
literal = ELit unit (LitInt 1)

-- | Run the action as an attempt, then the loop.
attempted :: forall a. Elab a -> (Tuple (Outcome a) SolverState -> RunResult -> SolverState -> Aff Unit) -> Aff Unit
attempted action k = do
  let
    Tuple outcome s = runAttempt session action (initialState (SessionId 0) 10)
    Tuple report after = run session s
  k (Tuple outcome s) report.result after

-- | A wrapping fit placed around `1`, and the term it makes.
wrapped :: XType -> XType -> Elab { fit :: FitId, term :: XExpr Unit }
wrapped source target = do
  f <- placeFit site Wrapping source target
  pure { fit: f, term: EFit unit f literal }

stateOf :: SolverState -> FitId -> Maybe FitState
stateOf s f = map _.state (Map.lookup f s.tentative.metas.fits)

spec :: Spec Unit
spec = describe "Stella.Compiler.Elaborate.Mechanism.Fit" do
  describe "a fit decided on the difference of its rows" do
    it "is equal where nothing is left of either, and widens by what is left of the target" do
      classify (known [ console ]) (known [ console ]) `shouldEqual` Contained Equal
      classify (known [ console ]) (known [ console, clock ]) `shouldEqual` Contained (Widen (closed [ clock ]))
      -- `( Console | e ) ⊆ ( Console, Clock | e )`: the tails cancel as the keys do
      classify ((known [ console ]) { rigid = Set.singleton (TyVar "e") }) ((known [ console, clock ]) { rigid = Set.singleton (TyVar "e") })
        `shouldEqual` Contained (Widen (closed [ clock ]))

    it "is not contained where the source keeps a key or a rigid tail and the target no flexible tail" do
      classify (known [ console ]) (known [ clock ]) `shouldEqual` NotContained { source: known [ console ], target: known [ clock ] }
      classify (emptyXNormalForm { rigid = Set.singleton (TyVar "e") }) emptyXNormalForm
        `shouldEqual` NotContained { source: emptyXNormalForm { rigid = Set.singleton (TyVar "e") }, target: emptyXNormalForm }

    it "waits on the flexible tails left, a source's own tail no help where its known keys have nowhere to go" do
      classify (emptyXNormalForm { flexible = Set.singleton m0 }) emptyXNormalForm `shouldEqual` Waiting (Set.singleton m0)
      classify (known [ console ]) (emptyXNormalForm { flexible = Set.singleton m0 }) `shouldEqual` Waiting (Set.singleton m0)
      classify ((known [ console ]) { flexible = Set.singleton m0 }) (known [ clock ]) `shouldEqual` NotContained { source: (known [ console ]) { flexible = Set.singleton m0 }, target: known [ clock ] }

  describe "a fit placed" do
    it "is decided where it can be, and its term is the expression alone, or the expression opened by what it widens" do
      attempted
        ( do
            equal <- wrapped (closed [ console ]) (closed [ console ])
            widen <- wrapped (closed [ console ]) (closed [ console, clock ])
            pure { equal, widen }
        )
        \(Tuple outcome s) _ _ -> case outcome of
          Done r -> do
            stateOf s r.equal.fit `shouldEqual` Just Equal
            zonkExpr s.tentative.metas r.equal.term `shouldEqual` literal
            map (map (const unit)) (toCoreExpr (zonkExpr s.tentative.metas r.widen.term))
              `shouldEqual` Right (OpenEff unit (TRowExtend (RowEffectEntry (effect "Clock") []) TRowEmpty) (Lit unit (LitInt 1)))
            Map.size s.tentative.scheduler.pending `shouldEqual` 0
          _ -> fail "not done"

    it "equates the payloads of a key the two rows share" do
      attempted
        ( do
            a <- freshTypeMeta emptyXContext XKType
            _ <- placeFit site Wrapping (closed [ state a ]) (closed [ state int ])
            pure a
        )
        \(Tuple outcome s) _ _ -> case outcome of
          Done a -> substitute s.tentative.metas a `shouldEqual` int
          _ -> fail "not done"
      attempted (placeFit site Wrapping (closed [ state int ]) (closed [ state string ]))
        \(Tuple outcome _) _ _ -> case outcome of
          Failed (EquationFailed _ _) -> pure unit
          _ -> fail "not refused"

    it "is refused where the source performs what the target cannot hold, by what is left of each" do
      attempted (placeFit site Wrapping (closed [ console, clock ]) (closed [ clock ]))
        \(Tuple outcome _) _ _ -> case outcome of
          Failed (RowNotContained _ r) -> r `shouldEqual` { source: known [ console ], target: emptyXNormalForm }
          _ -> fail "not refused"

    it "becomes a job where it waits, decided once what it waits on is assigned" do
      attempted
        ( do
            m <- freshTypeMeta emptyXContext (XKRow RowEffect)
            w <- wrapped (closed [ console ]) m
            -- what placed it goes on, and decides the target afterwards
            equate site { kind: XKRow RowEffect, left: m, right: closed [ console, clock ] }
            pure w
        )
        \(Tuple outcome s) result after -> case outcome of
          Done w -> do
            map _.job (Map.values s.tentative.scheduler.pending # Array.fromFoldable) `shouldEqual` [ JobEffectFit w.fit ]
            case stateOf s w.fit of
              Just (Undecided _) -> pure unit
              other -> fail ("decided already: " <> show other)
            result `shouldEqual` Completed
            stateOf after w.fit `shouldEqual` Just (Widen (closed [ clock ]))
            map (map (const unit)) (toCoreExpr (zonkExpr after.tentative.metas w.term))
              `shouldEqual` Right (OpenEff unit (TRowExtend (RowEffectEntry (effect "Clock") []) TRowEmpty) (Lit unit (LitInt 1)))
          _ -> fail "not done"

    it "is reported waiting where nothing assigns what it waits on, and its term is no Core" do
      attempted
        ( do
            m <- freshTypeMeta emptyXContext (XKRow RowEffect)
            wrapped (closed [ console ]) m
        )
        \(Tuple outcome _) result after -> case outcome, result of
          Done w, Blocked waiting -> do
            map _.job (NonEmptyArray.toArray waiting) `shouldEqual` [ JobEffectFit w.fit ]
            case toCoreExpr (zonkExpr after.tentative.metas w.term) of
              Left residues -> NonEmptyArray.toArray residues `shouldEqual` [ ResidualFit unit w.fit ]
              Right _ -> fail "made Core"
          _, _ -> fail "not waiting"

    it "is taken back, with its job, by the attempt that placed it" do
      attempted
        ( do
            m <- freshTypeMeta emptyXContext (XKRow RowEffect)
            _ <- placeFit site Wrapping (closed [ console ]) m
            raiseDiagnostic (RowNotContained (InDeclaration (Qualified (ModuleName "M") (Ident "g"))) { source: emptyXNormalForm, target: emptyXNormalForm })
        )
        \(Tuple outcome s) _ _ -> case outcome of
          Failed _ -> do
            Map.size s.tentative.metas.fits `shouldEqual` 0
            Map.size s.tentative.scheduler.pending `shouldEqual` 0
          _ -> fail "not failed"

    it "holding a tail Ψ does not hold is the host's defect, whether the tail would cancel or be waited on" do
      let
        unbound = XMeta (MetaVar 99)
      attempted (placeFit site Wrapping unbound unbound)
        \(Tuple outcome _) _ _ -> case outcome of
          Broke (FitTailUnbound _ m) -> m `shouldEqual` MetaVar 99
          _ -> fail "not a defect"
      attempted (placeFit site Wrapping (closed [ console ]) unbound)
        \(Tuple outcome _) _ _ -> case outcome of
          Broke (FitTailUnbound _ m) -> m `shouldEqual` MetaVar 99
          _ -> fail "not a defect"

    it "that demands containment alone is decided as one that wraps is" do
      attempted (placeFit site Demanding (closed [ console ]) (closed [ console, clock ]))
        \(Tuple outcome s) _ _ -> case outcome of
          Done f -> map _.use (Map.lookup f s.tentative.metas.fits) `shouldEqual` Just Demanding
          _ -> fail "not done"

  describe "a row metavariable's provenance" do
    it "is an instantiation row where instantiation made it, and the tail two are identified through is one only if both were" do
      attempted
        ( do
            a <- freshInstantiationRow emptyXContext
            b <- freshInstantiationRow emptyXContext
            c <- freshTypeMeta emptyXContext (XKRow RowEffect)
            d <- freshInstantiationRow emptyXContext
            equate site { kind: XKRow RowEffect, left: row [ console ] a, right: row [ clock ] b }
            equate site { kind: XKRow RowEffect, left: row [ console ] c, right: row [ clock ] d }
            pure { a, c }
        )
        \(Tuple outcome s) _ _ -> case outcome of
          Done r -> do
            map (isInstantiationRow s.tentative.metas) (tailOf (substitute s.tentative.metas r.a)) `shouldEqual` Just true
            map (isInstantiationRow s.tentative.metas) (tailOf (substitute s.tentative.metas r.c)) `shouldEqual` Just false
          _ -> fail "not done"

    it "is the same whichever side of an equation two bare row metavariables stand on" do
      attempted
        ( do
            inferred <- freshTypeMeta emptyXContext (XKRow RowEffect)
            instantiated <- freshInstantiationRow emptyXContext
            instantiated' <- freshInstantiationRow emptyXContext
            inferred' <- freshTypeMeta emptyXContext (XKRow RowEffect)
            both <- freshInstantiationRow emptyXContext
            both' <- freshInstantiationRow emptyXContext
            equate site { kind: XKRow RowEffect, left: inferred, right: instantiated }
            equate site { kind: XKRow RowEffect, left: instantiated', right: inferred' }
            equate site { kind: XKRow RowEffect, left: both, right: both' }
            pure { inferred, inferred', both }
        )
        \(Tuple outcome s) _ _ -> case outcome of
          Done r -> do
            let
              provenance m = map (isInstantiationRow s.tentative.metas) (tailOf (substitute s.tentative.metas m))
            provenance r.inferred `shouldEqual` Just false
            provenance r.inferred' `shouldEqual` Just false
            provenance r.both `shouldEqual` Just true
          _ -> fail "not done"

  where
  m0 = MetaVar 0

-- | The flexible tail a row ends in.
tailOf :: XType -> Maybe MetaVar
tailOf t = case xnf t of
  Right n -> Set.findMin n.flexible
  Left _ -> Nothing
