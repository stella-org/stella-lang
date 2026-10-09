-- | Resolving undecided fits by direction where the loop is quiescent, and the
-- | checking boundary a body is built under.
module Test.Stella.Compiler.Elaborate.Resolve (spec) where

import Prelude

import Data.Array as Array
import Data.Foldable (foldr)
import Data.Map as Map
import Data.Set as Set
import Data.Maybe (Maybe(..))
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Effect.Aff (Aff)
import Stella.Compiler.Elaborate.CorePlus.Context (Origin(..), XContext, bindTyVar, emptyXContext)
import Stella.Compiler.Elaborate.CorePlus.Kind (XKind(..))
import Stella.Compiler.Elaborate.CorePlus.Row (emptyXNormalForm, xnf)
import Stella.Compiler.Elaborate.CorePlus.Term (FitId)
import Stella.Compiler.Elaborate.CorePlus.Type (MetaVar, XConstraint(..), XRowEntry(..), XType(..))
import Stella.Compiler.Elaborate.Driver.Attempt (Runner, attemptPendingWith, hostRunner, runAttempt)
import Stella.Compiler.Elaborate.Driver.Loop (RunResult(..), run, runWith)
import Stella.Compiler.Elaborate.Driver.Resolve (Ambiguity(..), ComponentOutcome(..), Resolution(..), resolveByDirection)
import Stella.Compiler.Elaborate.Environment.Imported (sessionEnvOf)
import Stella.Compiler.Elaborate.Kernel.Elab (Elab, Outcome(..), SessionEnv, SolverState, closeBoundary, drainWarnings, equate, formUnion, freshInstantiationRow, freshTypeMeta, initialState, openBoundary, placeFit, recordWarning, require)
import Stella.Compiler.Elaborate.Mechanism.Fit (FitState(..), FitUse(..))
import Stella.Compiler.Elaborate.Mechanism.Pending (Site)
import Stella.Compiler.Elaborate.Mechanism.Unify (substitute)
import Stella.Compiler.Elaborate.Vocabulary.Diagnostic (Defect(..), Diagnostic(..))
import Stella.Compiler.Elaborate.Vocabulary.Handle (SessionId(..))
import Stella.Compiler.TypedCore (primSignature)
import Stella.Compiler.TypedCore.Prim (intTy)
import Stella.Compiler.Elaborate.Vocabulary.Message (FrozenMessagePart(..))
import Stella.Compiler.TypedCore.Kind (RowElemKind(..))
import Stella.Compiler.TypedCore.Name (EffName(..), Ident(..), ModuleName(..), Qualified(..), TyVar(..))
import Stella.Compiler.TypedCore.Type (RowKey(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

session :: SessionEnv
session = sessionEnvOf primSignature []

declaration :: String -> Qualified Ident
declaration = Qualified (ModuleName "M") <<< Ident

-- | A site in the declaration named, under the context given.
siteIn :: String -> XContext -> Site
siteIn name context = { context, origin: InDeclaration (declaration name) }

-- | A site in `f`, under nothing.
site :: Site
site = siteIn "f" emptyXContext

-- | The declaration a site stands in, which owns what is placed there.
ownerOf :: Origin -> Qualified Ident
ownerOf = case _ of
  InDeclaration name -> name
  AtSource o -> o.declaration

effect :: String -> Qualified EffName
effect = Qualified (ModuleName "M") <<< EffName

console :: XRowEntry
console = XRowEffectEntry (effect "Console") []

clock :: XRowEntry
clock = XRowEffectEntry (effect "Clock") []

state :: XType -> XRowEntry
state t = XRowEffectEntry (effect "State") [ t ]

stateR :: XType -> XRowEntry
stateR r = XRowEffectEntry (effect "StateR") [ r ]

int :: XType
int = XCon intTy []

row :: Array XRowEntry -> XType -> XType
row entries tail = foldr XRowExtend tail entries

closed :: Array XRowEntry -> XType
closed entries = row entries XRowEmpty

rowEffect :: XKind
rowEffect = XKRow RowEffect

-- | `e`, a row variable a signature binds, apart from `Console` and `Clock`.
withE :: XContext
withE = (bindTyVar emptyXContext (TyVar "e") rowEffect) { assumed = [ XLacks (EffectKey (effect "Console")) e, XLacks (EffectKey (effect "Clock")) e ] }

e :: XType
e = XVar (TyVar "e")

-- | Run the action as an attempt and the loop to quiescence, then resolve the
-- | fits by direction.
resolving :: forall a. Elab a -> (a -> Resolution (Qualified Ident) -> SolverState -> Aff Unit) -> Aff Unit
resolving = resolvingWith hostRunner

-- | `resolving`, each job run by the runner given.
resolvingWith :: forall a. Runner -> Elab a -> (a -> Resolution (Qualified Ident) -> SolverState -> Aff Unit) -> Aff Unit
resolvingWith runner action k = case runAttempt session action (initialState (SessionId 0) 100) of
  Tuple (Done a) s -> do
    let
      Tuple _ quiet = runWith session runner s
      Tuple _ drained = drainWarnings quiet
      Tuple resolution after = resolveByDirection session (attemptPendingWith session runner) ownerOf drained
    k a resolution after
  Tuple _ _ -> fail "the attempt did not commit"

-- | What each component came to.
outcomes :: Resolution (Qualified Ident) -> Array ComponentOutcome
outcomes = case _ of
  Resolution r -> map _.outcome r.components
  ResolutionHalted _ -> []

-- | That the two rows are one, as their normal forms say once what is solved
-- | is substituted.
sameRow :: SolverState -> XType -> XType -> Aff Unit
sameRow s a b = xnf (substitute s.tentative.metas a) `shouldEqual` xnf (substitute s.tentative.metas b)

stateOf :: SolverState -> FitId -> Maybe FitState
stateOf s f = map _.state (Map.lookup f s.tentative.metas.fits)

spec :: Spec Unit
spec = describe "Stella.Compiler.Elaborate.Driver.Resolve" do
  describe "a target whose remainder is one flexible tail" do
    it "takes the union of every source fitted into it, each fit then widened by what the others bring" do
      resolving
        ( do
            -- `greet = \_ -> let _ = say "a" in tock ()`: the λ's row is `?e`
            lambda <- freshTypeMeta emptyXContext rowEffect
            say <- placeFit site Wrapping (closed [ console ]) lambda
            tock <- placeFit site Wrapping (closed [ clock ]) lambda
            pure { lambda, say, tock }
        )
        \r resolution after -> do
          outcomes resolution `shouldEqual` [ Settled ]
          sameRow after r.lambda (closed [ console, clock ])
          stateOf after r.say `shouldEqual` Just (Widen (closed [ clock ]))
          stateOf after r.tock `shouldEqual` Just (Widen (closed [ console ]))

    it "is left where the union would join two distinct flexible tails, everything rolled back" do
      resolving
        ( do
            target <- freshTypeMeta emptyXContext rowEffect
            a <- freshTypeMeta emptyXContext rowEffect
            b <- freshTypeMeta emptyXContext rowEffect
            _ <- placeFit site Wrapping (row [ console ] a) target
            _ <- placeFit site Wrapping (row [ clock ] b) target
            pure target
        )
        \target resolution after -> do
          map ambiguityOf (outcomes resolution) `shouldEqual` [ Just "union" ]
          substitute after.tentative.metas target `shouldEqual` target

  describe "a source whose remainder is one flexible tail" do
    it "takes the target's remainder where instantiation made it, and is left alone where inference did" do
      resolving
        ( do
            instantiated <- freshInstantiationRow withE
            _ <- placeFit (siteIn "f" withE) Wrapping (row [ console ] instantiated) (row [ console, clock ] e)
            inferred <- freshTypeMeta withE rowEffect
            _ <- placeFit (siteIn "g" withE) Wrapping (row [ console ] inferred) (row [ console, clock ] e)
            pure { instantiated, inferred }
        )
        \r resolution after -> do
          map ambiguityOf (outcomes resolution) `shouldEqual` [ Nothing, Just "undecided" ]
          sameRow after r.instantiated (row [ clock ] e)
          substitute after.tentative.metas r.inferred `shouldEqual` r.inferred

  describe "assignments of one round" do
    it "that depend on one another are not made, and the component is left" do
      resolving
        ( do
            -- rule 1 gives `?m := ?t` and rule 2 `?t := ?m`
            t <- freshInstantiationRow emptyXContext
            m <- freshTypeMeta emptyXContext rowEffect
            _ <- placeFit site Wrapping t m
            pure { t, m }
        )
        \r resolution after -> do
          map ambiguityOf (outcomes resolution) `shouldEqual` [ Just "depend" ]
          substitute after.tentative.metas r.m `shouldEqual` r.m

    it "that break an obligation refuse the component, and roll it back" do
      resolving
        ( do
            m <- freshTypeMeta emptyXContext rowEffect
            require site (XLacks (EffectKey (effect "Console")) m)
            _ <- placeFit site Wrapping (closed [ console ]) m
            pure m
        )
        \m resolution after -> do
          case outcomes resolution of
            [ Refused (ObligationBroken _) ] -> pure unit
            other -> fail ("not refused: " <> show other)
          substitute after.tentative.metas m `shouldEqual` m

  describe "components" do
    it "are resolved apart by their owners, one left and another settled" do
      resolving
        ( do
            settled <- freshTypeMeta emptyXContext rowEffect
            _ <- placeFit (siteIn "f" emptyXContext) Wrapping (closed [ console ]) settled
            left <- freshTypeMeta emptyXContext rowEffect
            a <- freshTypeMeta emptyXContext rowEffect
            b <- freshTypeMeta emptyXContext rowEffect
            _ <- placeFit (siteIn "g" emptyXContext) Wrapping (row [ console ] a) left
            _ <- placeFit (siteIn "g" emptyXContext) Wrapping (row [ clock ] b) left
            pure settled
        )
        \settled resolution after -> do
          case resolution of
            Resolution r -> map (\c -> Tuple c.owner (ambiguityOf c.outcome)) r.components `shouldEqual` [ Tuple (declaration "f") Nothing, Tuple (declaration "g") (Just "union") ]
            ResolutionHalted d -> fail (show d)
          substitute after.tentative.metas settled `shouldEqual` closed [ console ]

    it "of two owners sharing a metavariable are the host's defect" do
      resolving
        ( do
            m <- freshTypeMeta emptyXContext rowEffect
            _ <- placeFit (siteIn "f" emptyXContext) Wrapping (closed [ console ]) m
            _ <- placeFit (siteIn "g" emptyXContext) Wrapping (closed [ clock ]) m
            pure unit
        )
        \_ resolution _ -> case resolution of
          ResolutionHalted (OwnersShareMetavariable _) -> pure unit
          _ -> fail "not a defect"

  describe "a checking boundary" do
    it "decides at once where the union of its body's sources fits the row expected, and the fits inside then against that row" do
      case runAttempt session (boundaryWith (closed [ console, clock ]) (\sigma -> [ Tuple (closed [ console ]) sigma ])) (initialState (SessionId 0) 100) of
        Tuple (Done r) s -> do
          let
            Tuple report after = run session s
          report.result `shouldEqual` Completed
          sameRow after (XMeta r.sigma) (closed [ console, clock ])
          map (stateOf after) r.fits `shouldEqual` [ Just (Widen (closed [ clock ])) ]
        _ -> fail "not done"

    it "is refused where its body performs what the row expected cannot hold" do
      case runAttempt session (boundaryWith XRowEmpty (\sigma -> [ Tuple (closed [ console ]) sigma ])) (initialState (SessionId 0) 100) of
        Tuple (Done _) s -> case run session s of
          Tuple { result: Rejected (BoundaryNotContained _ r) } _ -> r.source `shouldEqual` (emptyXNormalForm { known = Map.singleton (EffectKey (effect "Console")) console })
          Tuple report _ -> fail ("not refused: " <> show report.result)
        _ -> fail "not done"

    it "takes as its own a fit whose target's remainder is its ambient row alone, whatever the target holds besides" do
      case runAttempt session (boundaryWith (closed [ console ]) (\sigma -> [ Tuple (closed [ console, clock ]) (row [ console ] sigma) ])) (initialState (SessionId 0) 100) of
        Tuple (Done _) s -> case run session s of
          Tuple { result: Rejected (BoundaryNotContained _ r) } _ -> r.source `shouldEqual` (emptyXNormalForm { known = Map.singleton (EffectKey (effect "Clock")) clock })
          Tuple report _ -> fail ("not refused: " <> show report.result)
        _ -> fail "not done"

    it "stands in for its fits by its own against the row expected, where the union of its sources is not formed" do
      resolving
        ( do
            t1 <- freshInstantiationRow withE
            t2 <- freshInstantiationRow withE
            r <- boundaryIn (siteIn "f" withE) (row [ console, clock ] e) (\sigma -> [ Tuple (row [ console ] t1) sigma, Tuple (row [ clock ] t2) sigma ])
            pure { t1, t2, sigma: r.sigma }
        )
        \r resolution after -> do
          outcomes resolution `shouldEqual` [ Settled ]
          sameRow after r.t1 (row [ clock ] e)
          sameRow after r.t2 (row [ console ] e)
          sameRow after (XMeta r.sigma) (row [ console, clock ] e)
  describe "a component resolved" do
    it "reads and changes no fit of another, which is rolled back with its own component" do
      resolving
        ( do
            _ <- settling "f"
            ambiguousWithPayload "g"
        )
        \p resolution after -> do
          map ambiguityOf (outcomes resolution) `shouldEqual` [ Nothing, Just "undecided" ]
          substitute after.tentative.metas p `shouldEqual` p

    it "is joined by every metavariable a waiting job could assign, its goal's among them" do
      resolving
        ( do
            x <- freshTypeMeta emptyXContext rowEffect
            y <- freshTypeMeta emptyXContext rowEffect
            n <- freshTypeMeta emptyXContext rowEffect
            p <- freshTypeMeta emptyXContext XKType
            -- waits on `?x` and `?y`, and holds `?p` in its goal
            equate site { kind: rowEffect, left: XRowUnion x y, right: closed [ state p ] }
            _ <- placeFit site Wrapping (closed [ console ]) x
            _ <- placeFit site Wrapping (closed [ state p ]) n
            pure unit
        )
        \_ resolution _ -> Array.length (outcomes resolution) `shouldEqual` 1

    it "keeps only the warnings of what it kept" do
      resolvingWith warningRunner
        ( do
            _ <- settling "f"
            ambiguousWithPayload "g"
        )
        \_ resolution _ -> case resolution of
          Resolution r -> map _.goal.origin r.warnings `shouldEqual` [ InDeclaration (declaration "f") ]
          ResolutionHalted d -> fail (show d)

  describe "the union of the sources" do
    it "is formed once the payloads of the keys they share are equated, an equation identifying their tails" do
      resolving
        ( do
            m <- freshTypeMeta emptyXContext rowEffect
            a <- freshTypeMeta emptyXContext rowEffect
            b <- freshTypeMeta emptyXContext rowEffect
            _ <- placeFit site Wrapping (row [ stateR a ] a) m
            _ <- placeFit site Wrapping (row [ stateR b ] b) m
            pure { m, a }
        )
        \r resolution after -> do
          outcomes resolution `shouldEqual` [ Settled ]
          sameRow after r.m (row [ stateR r.a ] r.a)

    it "not formed yet is waited on while other assignments of its component are made, and formed once they are" do
      resolving
        ( do
            let
              at = siteIn "f" withE
            m <- freshTypeMeta withE rowEffect
            a <- freshTypeMeta withE rowEffect
            b <- freshTypeMeta withE rowEffect
            _ <- placeFit at Wrapping e a
            _ <- placeFit at Wrapping e b
            _ <- placeFit at Wrapping (row [ console ] a) m
            _ <- placeFit at Wrapping (row [ clock ] b) m
            pure m
        )
        \m resolution after -> do
          outcomes resolution `shouldEqual` [ Settled ]
          sameRow after m (row [ console, clock ] e)

    it "is required to be a row at the site of each source it joins, whichever comes first" do
      let
        withEBare = bindTyVar emptyXContext (TyVar "e") rowEffect
        -- `Console ∉ e` is assumed where the first is placed and not where the second is
        known = { site: siteIn "f" withE, row: emptyXNormalForm { known = Map.singleton (EffectKey (effect "Console")) console } }
        tail = { site: siteIn "f" withEBare, row: emptyXNormalForm { rigid = Set.singleton (TyVar "e") } }
        refused inputs = case runAttempt session (formUnion inputs) (initialState (SessionId 0) 100) of
          Tuple (Failed (ObligationRejected _)) _ -> true
          _ -> false
      refused [ known, tail ] `shouldEqual` true
      refused [ tail, known ] `shouldEqual` true

  where
  ambiguityOf = case _ of
    Settled -> Nothing
    Ambiguous { cause: UnionNotFormed _ } -> Just "union"
    Ambiguous { cause: AssignmentsDepend _ } -> Just "depend"
    Ambiguous { cause: LeftUndecided } -> Just "undecided"
    Refused _ -> Just "refused"

-- | A fit of the declaration named that rule 1 settles.
settling :: String -> Elab XType
settling name = do
  m <- freshTypeMeta emptyXContext rowEffect
  _ <- placeFit (siteIn name emptyXContext) Wrapping (closed [ console ]) m
  pure m

-- | Two fits of the declaration named into one target, which resolution leaves
-- | undecided once it has equated a payload of one of them: `?p`, which nothing
-- | but that equation decides.
ambiguousWithPayload :: String -> Elab XType
ambiguousWithPayload name = do
  let
    at = siteIn name emptyXContext
  q <- freshTypeMeta emptyXContext rowEffect
  a <- freshTypeMeta emptyXContext rowEffect
  b <- freshTypeMeta emptyXContext rowEffect
  z <- freshTypeMeta emptyXContext rowEffect
  p <- freshTypeMeta emptyXContext XKType
  _ <- placeFit at Wrapping (row [ state p ] a) q
  _ <- placeFit at Wrapping (row [ clock ] b) q
  -- the fits' jobs equate `?p` with `Int`, and then wait, rolled back
  equate at { kind: rowEffect, left: q, right: row [ state int ] z }
  pure p

-- | The host's runner, warning at every attempt it makes.
warningRunner :: Runner
warningRunner p = do
  recordWarning { goal: { origin: p.site.origin, pending: p.id, synthesizer: declaration "w", expectedType: XRowEmpty }, message: [ FrozenText "attempted" ] }
  hostRunner p

-- | A boundary opened in `f` under nothing, with the fits the function given
-- | places into its ambient row, and closed against the row given.
boundaryWith :: XType -> (XType -> Array (Tuple XType XType)) -> Elab { sigma :: MetaVar, fits :: Array FitId }
boundaryWith = boundaryIn site

boundaryIn :: Site -> XType -> (XType -> Array (Tuple XType XType)) -> Elab { sigma :: MetaVar, fits :: Array FitId }
boundaryIn at expected body = do
  sigma <- openBoundary at.context
  fits <- traverse (\(Tuple source target) -> placeFit at Wrapping source target) (body (XMeta sigma))
  closeBoundary at sigma expected
  pure { sigma, fits }
