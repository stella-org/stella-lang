-- | Resolving undecided fits by direction where the loop is quiescent, and the
-- | checking boundary a body is built under.
module Test.Stella.Compiler.Elaborate.Resolve (spec) where

import Prelude

import Data.Array as Array
import Data.Foldable (foldr, for_)
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
import Stella.Compiler.Elaborate.Environment.Implicit (ImplicitCandidate)
import Stella.Compiler.Elaborate.Kernel.Elab (Elab, Outcome(..), SessionEnv, SolverState, closeBoundary, drainWarnings, equate, formUnion, freshInstantiationRow, freshTypeMeta, initialState, openBoundary, placeFit, recordWarning, require)
import Stella.Compiler.Elaborate.Mechanism.Fit (FitState(..), FitUse(..))
import Stella.Compiler.Elaborate.Mechanism.Obligation (Breach(..))
import Stella.Compiler.Elaborate.Mechanism.Pending (Site)
import Stella.Compiler.Elaborate.Mechanism.Unify (isInstantiationRow, substitute)
import Stella.Compiler.Elaborate.Vocabulary.Diagnostic (Defect(..), Diagnostic(..))
import Stella.Compiler.Elaborate.Vocabulary.Handle (SessionId(..))
import Stella.Compiler.TypedCore (primSignature)
import Stella.Compiler.TypedCore.Prim (fn, intTy, unitTy)
import Stella.Compiler.Elaborate.Vocabulary.Message (FrozenMessagePart(..))
import Stella.Compiler.TypedCore.Kind (Kind(..), RowElemKind(..))
import Stella.Compiler.TypedCore.Name (EffName(..), Ident(..), KindVar(..), ModuleName(..), Qualified(..), TyName, TyVar(..))
import Stella.Compiler.TypedCore.Type (Constraint(..), RowEntry(..), RowKey(..), Type(..), TypeScheme, rowEntryKey)
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
      Tuple resolution after = resolveByDirection session (attemptPendingWith session runner) ownerOf (const 0) drained
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

    it "takes the target's remainder but for the keys it is required to lack, which the fit widens by, whatever order they come in" do
      let
        -- `e`, apart from every effect the rows hold
        apart = (bindTyVar emptyXContext (TyVar "e") rowEffect)
          { assumed = map (\name -> XLacks (EffectKey (effect name)) e) [ "Console", "Clock", "State", "StateR" ] }
        at = siteIn "f" apart
        steps t =
          [ void (placeFit at Wrapping (row [ console ] t) (row [ console, clock, state int, stateR int ] e))
          , require at (XLacks (EffectKey (effect "Clock")) t)
          , require at (XDisjoint t (closed [ state int ]))
          ]
      for_ [ identity, Array.reverse ] \order ->
        resolving
          ( do
              t <- freshInstantiationRow apart
              for_ (order (steps t)) identity
              pure t
          )
          \t resolution after -> do
            outcomes resolution `shouldEqual` [ Settled ]
            sameRow after t (row [ stateR int ] e)
            map (\f -> f.state) (Array.fromFoldable (Map.values after.tentative.metas.fits)) `shouldEqual` [ Widen (closed [ clock, state int ]) ]

    it "lacks what a union of the same round requires it to, whatever order the fits come in" do
      let
        fits t m =
          [ void (placeFit site Wrapping (row [ console ] t) m)
          , void (placeFit site Wrapping (closed [ clock ]) m)
          ]
      for_ [ identity, Array.reverse ] \order ->
        resolving
          ( do
              t <- freshInstantiationRow emptyXContext
              m <- freshTypeMeta emptyXContext rowEffect
              for_ (order (fits t m)) identity
              -- the union into `?m` requires `Clock ∉ ?t`
              into <- placeFit site Wrapping t (closed [ clock ])
              pure { t, m, into }
          )
          \r resolution after -> do
            outcomes resolution `shouldEqual` [ Settled ]
            sameRow after r.t XRowEmpty
            sameRow after r.m (closed [ console, clock ])
            stateOf after r.into `shouldEqual` Just (Widen (closed [ clock ]))

    it "keeps a rigid tail of the target, refused where the obligations' sites do not prove it lacks the keys" do
      resolving
        ( do
            t <- freshInstantiationRow withE
            require (siteIn "f" (bindTyVar emptyXContext (TyVar "e") rowEffect)) (XLacks (EffectKey (effect "Clock")) t)
            _ <- placeFit (siteIn "f" withE) Wrapping (row [ console ] t) (row [ console, clock ] e)
            pure t
        )
        \t resolution after -> do
          case outcomes resolution of
            [ Refused (ObligationBroken b) ] -> b.breach `shouldEqual` LacksUnprovenAtSite (EffectKey (effect "Clock")) (TyVar "e")
            other -> fail ("not refused: " <> show other)
          substitute after.tentative.metas t `shouldEqual` t

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

    it "that wait on another's are made in a round after it, a chain of two or of three, whatever order its fits come in" do
      let
        chain order = do
          a <- freshTypeMeta emptyXContext rowEffect
          b <- freshTypeMeta emptyXContext rowEffect
          c <- freshTypeMeta emptyXContext rowEffect
          let fits = [ Tuple (closed [ console ]) a, Tuple a b, Tuple b c ]
          _ <- traverse (\(Tuple source target) -> placeFit site Wrapping source target) (order fits)
          pure { a, b, c }
      resolving
        ( do
            inner <- freshTypeMeta emptyXContext rowEffect
            outer <- freshTypeMeta emptyXContext rowEffect
            _ <- placeFit site Wrapping inner outer
            _ <- placeFit site Wrapping (closed [ console ]) inner
            pure { inner, outer }
        )
        \r resolution after -> do
          outcomes resolution `shouldEqual` [ Settled ]
          sameRow after r.outer (closed [ console ])
      for_ [ identity, Array.reverse ] \order ->
        resolving (chain order) \r resolution after -> do
          outcomes resolution `shouldEqual` [ Settled ]
          for_ [ r.a, r.b, r.c ] \m -> sameRow after m (closed [ console ])

    it "giving one metavariable two solutions wait until what is made first makes them one" do
      resolving
        ( do
            t <- freshInstantiationRow emptyXContext
            p <- freshTypeMeta emptyXContext rowEffect
            q <- freshTypeMeta emptyXContext rowEffect
            -- `?p := ?q` is ready, and makes the two solutions of `?t` one
            _ <- placeFit site Wrapping q p
            _ <- placeFit site Wrapping t (row [ console ] p)
            _ <- placeFit site Wrapping t (row [ console ] q)
            pure { t, q }
        )
        \r resolution after -> do
          outcomes resolution `shouldEqual` [ Settled ]
          sameRow after r.t (row [ console ] r.q)

    it "giving one metavariable two solutions nothing makes one leave the component" do
      resolving
        ( do
            t <- freshInstantiationRow emptyXContext
            p <- freshTypeMeta emptyXContext rowEffect
            q <- freshTypeMeta emptyXContext rowEffect
            _ <- placeFit site Wrapping t (row [ console ] p)
            _ <- placeFit site Wrapping t (row [ clock ] q)
            pure t
        )
        \t resolution after -> do
          map ambiguityOf (outcomes resolution) `shouldEqual` [ Just "depend" ]
          substitute after.tentative.metas t `shouldEqual` t

    it "are read again once a union identifies the rows they are about, an instantiation row made an inference row maximized no more" do
      resolving
        ( do
            t <- freshInstantiationRow emptyXContext
            m <- freshTypeMeta emptyXContext rowEffect
            target <- freshTypeMeta emptyXContext rowEffect
            -- the union equates `?t` with `?m`, an inference row
            _ <- placeFit site Wrapping (closed [ stateR t ]) target
            _ <- placeFit site Wrapping (closed [ stateR m ]) target
            _ <- placeFit site Wrapping t (closed [ console ])
            pure { t, m }
        )
        \r resolution after -> do
          map ambiguityOf (outcomes resolution) `shouldEqual` [ Just "undecided" ]
          map (substitute after.tentative.metas) [ r.t, r.m ] `shouldEqual` [ r.t, r.m ]

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

  describe "tails on a cycle of fits" do
    let fresh = freshTypeMeta emptyXContext rowEffect
    it "are identified, a cycle of two or of three, each with one of them" do
      resolving
        ( do
            a <- fresh
            b <- fresh
            _ <- placeFit site Wrapping a b
            _ <- placeFit site Wrapping b a
            x <- fresh
            y <- fresh
            z <- fresh
            _ <- placeFit site Wrapping x y
            _ <- placeFit site Wrapping y z
            _ <- placeFit site Wrapping z x
            pure { a, b, x, y, z }
        )
        \r resolution after -> do
          outcomes resolution `shouldEqual` [ Settled, Settled ]
          substitute after.tentative.metas r.b `shouldEqual` r.a
          map (substitute after.tentative.metas) [ r.y, r.z ] `shouldEqual` [ r.x, r.x ]

    it "are identified in a round of their own, what the cycle needs decided in the next" do
      resolving
        ( do
            a <- fresh
            b <- fresh
            _ <- placeFit site Wrapping a b
            _ <- placeFit site Wrapping b a
            _ <- placeFit site Wrapping (closed [ console ]) a
            pure { a, b }
        )
        \r resolution after -> do
          outcomes resolution `shouldEqual` [ Settled ]
          sameRow after r.a (closed [ console ])
          sameRow after r.b (closed [ console ])

    it "are not identified by a containment one way" do
      resolving
        ( do
            a <- fresh
            b <- fresh
            _ <- placeFit site Wrapping a b
            _ <- placeFit site Wrapping (closed [ console ]) b
            pure { a, b }
        )
        \r resolution after -> do
          outcomes resolution `shouldEqual` [ Settled ]
          sameRow after r.b (row [ console ] r.a)
          (xnf (substitute after.tentative.metas r.a) == xnf (substitute after.tentative.metas r.b)) `shouldEqual` false

    it "are not identified through a fit whose remainder holds a known key or a rigid tail" do
      resolving
        ( do
            a <- fresh
            b <- fresh
            _ <- placeFit site Wrapping (row [ console ] a) b
            _ <- placeFit site Wrapping b a
            pure a
        )
        \a resolution after -> do
          map ambiguityOf (outcomes resolution) `shouldEqual` [ Just "depend" ]
          substitute after.tentative.metas a `shouldEqual` a
      resolving
        ( do
            a <- freshTypeMeta withE rowEffect
            b <- freshTypeMeta withE rowEffect
            _ <- placeFit (siteIn "f" withE) Wrapping (XRowUnion e a) b
            _ <- placeFit (siteIn "f" withE) Wrapping b a
            pure a
        )
        \a resolution after -> do
          map ambiguityOf (outcomes resolution) `shouldEqual` [ Just "depend" ]
          substitute after.tentative.metas a `shouldEqual` a

    it "are not identified with a checking boundary's ambient row" do
      resolving
        ( do
            a <- fresh
            r <- boundaryWith (closed [ console ]) (\sigma -> [ Tuple a sigma ])
            _ <- placeFit site Wrapping (XMeta r.sigma) a
            pure { a, sigma: r.sigma }
        )
        \r resolution after -> do
          -- a union holding the boundary's row gives no target, so the
          -- component is left with nothing solved
          map ambiguityOf (outcomes resolution) `shouldEqual` [ Just "undecided" ]
          substitute after.tentative.metas r.a `shouldEqual` r.a
          substitute after.tentative.metas (XMeta r.sigma) `shouldEqual` XMeta r.sigma

    it "leave a checking boundary's ambient row unwritten, and its boundary's, where the row expected of it is that row" do
      resolving
        ( do
            expected <- fresh
            r <- boundaryWith expected (const [])
            equate site { kind: rowEffect, left: expected, right: XMeta r.sigma }
            pure r
        )
        \r resolution after -> do
          -- the boundary waits, deciding nothing, and nothing has broken
          map ambiguityOf (outcomes resolution) `shouldEqual` [ Just "undecided" ]
          substitute after.tentative.metas (XMeta r.sigma) `shouldEqual` XMeta r.sigma
          Set.member r.sigma after.tentative.metas.boundaryRows `shouldEqual` true

    it "give a target from a union holding a checking boundary's ambient row once the boundary has decided it" do
      resolving
        ( do
            a <- fresh
            r <- boundaryWith (closed [ console ]) (\sigma -> [ Tuple (closed [ console ]) sigma ])
            _ <- placeFit site Wrapping (XMeta r.sigma) a
            pure { a, sigma: r.sigma }
        )
        \r resolution after -> do
          outcomes resolution `shouldEqual` [ Settled ]
          sameRow after (XMeta r.sigma) (closed [ console ])
          sameRow after r.a (closed [ console ])

    it "are an inference row once identified where an inference row is among them" do
      resolving
        ( do
            t <- freshInstantiationRow emptyXContext
            m <- fresh
            _ <- placeFit site Wrapping t m
            _ <- placeFit site Wrapping m t
            pure { t, m }
        )
        \r resolution after -> do
          outcomes resolution `shouldEqual` [ Settled ]
          case substitute after.tentative.metas r.t, substitute after.tentative.metas r.m of
            XMeta one, XMeta other | one == other -> isInstantiationRow after.tentative.metas one `shouldEqual` false
            one, other -> fail ("not identified: " <> show one <> ", " <> show other)

    it "are rolled back with their component where what is decided of them later breaks an obligation" do
      resolving
        ( do
            a <- fresh
            b <- fresh
            require site (XLacks (EffectKey (effect "Console")) b)
            _ <- placeFit site Wrapping a b
            _ <- placeFit site Wrapping b a
            _ <- placeFit site Wrapping (closed [ console ]) a
            pure { a, b }
        )
        \r resolution after -> do
          map ambiguityOf (outcomes resolution) `shouldEqual` [ Just "refused" ]
          map (substitute after.tentative.metas) [ r.a, r.b ] `shouldEqual` [ r.a, r.b ]

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

    it "is refused where its body performs what the row expected cannot hold, no implicit handler handling it" do
      case runAttempt session (boundaryWith XRowEmpty (\sigma -> [ Tuple (closed [ console ]) sigma ])) (initialState (SessionId 0) 100) of
        Tuple (Done _) s -> case run session s of
          Tuple { result: Rejected (ImplicitHandlerMissing _ k r) } _ -> do
            k `shouldEqual` EffectKey (effect "Console")
            r `shouldEqual` (emptyXNormalForm { known = Map.singleton (EffectKey (effect "Console")) console })
          Tuple report _ -> fail ("not refused: " <> show report.result)
        _ -> fail "not done"

    it "takes as its own a fit whose target's remainder is its ambient row alone, whatever the target holds besides" do
      case runAttempt session (boundaryWith (closed [ console ]) (\sigma -> [ Tuple (closed [ console, clock ]) (row [ console ] sigma) ])) (initialState (SessionId 0) 100) of
        Tuple (Done _) s -> case run session s of
          Tuple { result: Rejected (ImplicitHandlerMissing _ _ r) } _ -> r `shouldEqual` (emptyXNormalForm { known = Map.singleton (EffectKey (effect "Clock")) clock })
          Tuple report _ -> fail ("not refused: " <> show report.result)
        _ -> fail "not done"

    it "inserts the one implicit handler of the key its body performs, the thunk widened by the target, the plan recorded" do
      planned [ lowering "lowerConsole" "Console" [ "LiftIO" ] ] (boundaryWith (closed [ liftIO ]) (\sigma -> [ Tuple (closed [ console ]) sigma ])) \result r after -> do
        result `shouldEqual` Completed
        sameRow after (XMeta r.sigma) (closed [ console ])
        planOf after r.sigma `shouldEqual` Just { handlers: [ "lowerConsole" ], widening: [ liftIO ] }

    it "cancels a flexible tail both rows share before reading the plan, and waits on nothing" do
      planned [ lowering "lowerConsole" "Console" [ "LiftIO" ] ]
        ( do
            t <- freshTypeMeta emptyXContext rowEffect
            boundaryWith (row [ liftIO ] t) (\sigma -> [ Tuple (row [ console ] t) sigma ])
        )
        \result r after -> do
          result `shouldEqual` Completed
          planOf after r.sigma `shouldEqual` Just { handlers: [ "lowerConsole" ], widening: [ liftIO ] }

    it "widens by nothing a target the body performs already, and by a key only the row expected carries" do
      planned [ lowering "lowerConsole" "Console" [ "LiftIO" ] ] (boundaryWith (closed [ liftIO ]) (\sigma -> [ Tuple (closed [ console, liftIO ]) sigma ])) \result r after -> do
        result `shouldEqual` Completed
        planOf after r.sigma `shouldEqual` Just { handlers: [ "lowerConsole" ], widening: [] }
      planned [ lowering "lowerConsole" "Console" [ "LiftIO" ] ] (boundaryWith (closed [ liftIO, clock ]) (\sigma -> [ Tuple (closed [ console ]) sigma ])) \result r after -> do
        result `shouldEqual` Completed
        planOf after r.sigma `shouldEqual` Just { handlers: [ "lowerConsole" ], widening: [ clock, liftIO ] }

    it "orders a chain by the transitive closure of what each handler performs, innermost first" do
      planned [ lowering "lowerLogging" "Logging" [ "LiftIO" ], lowering "lowerConsole" "Console" [ "Logging" ] ] (boundaryWith (closed [ liftIO ]) (\sigma -> [ Tuple (closed [ console ]) sigma ])) \result r after -> do
        result `shouldEqual` Completed
        planOf after r.sigma `shouldEqual` Just { handlers: [ "lowerConsole", "lowerLogging" ], widening: [ liftIO, logging ] }

    it "is refused where two handlers lower independently into one target, or two handle one key, and records no plan" do
      planned [ lowering "lowerConsole" "Console" [ "LiftIO" ], lowering "lowerClock" "Clock" [ "LiftIO" ] ] (boundaryWith (closed [ liftIO ]) (\sigma -> [ Tuple (closed [ console, clock ]) sigma ])) \result r after -> do
        result `shouldEqual` Rejected (ImplicitOrderAmbiguous (InDeclaration (declaration "f")) [ declaration "lowerClock", declaration "lowerConsole" ])
        planOf after r.sigma `shouldEqual` Nothing
      planned [ lowering "quiet" "Console" [], lowering "loud" "Console" [ "LiftIO" ] ] (boundaryWith (closed [ liftIO ]) (\sigma -> [ Tuple (closed [ console ]) sigma ])) \result _ _ ->
        result `shouldEqual` Rejected (ImplicitHandlerAmbiguous (InDeclaration (declaration "f")) (EffectKey (effect "Console")) [ declaration "loud", declaration "quiet" ])

    it "is refused where a target and the row expected carry one key with payloads that differ" do
      planned [ loweringOf "stateful" (RowEffectEntry (effect "Console") []) [ stateEntry intTy ] ]
        (boundaryWith (closed [ state (XCon unitTy []) ]) (\sigma -> [ Tuple (closed [ console ]) sigma ]))
        \result _ _ -> result `shouldEqual` Rejected (ImplicitPayloadConflict (InDeclaration (declaration "f")) (EffectKey (effect "State")))

    it "is refused where a target carries a key the body performs with another payload, or a handler's source is not the element it was chosen for" do
      -- `State Unit` performed and handled, `State Int` performed in place of `Console`
      planned [ loweringOf "lowerConsole" (RowEffectEntry (effect "Console") []) [ stateEntry intTy ], loweringOf "dropState" (stateEntry unitTy) [] ]
        (boundaryWith XRowEmpty (\sigma -> [ Tuple (closed [ console, state (XCon unitTy []) ]) sigma ]))
        \result _ _ -> result `shouldEqual` Rejected (ImplicitPayloadConflict (InDeclaration (declaration "f")) (EffectKey (effect "State")))
      -- the one handler of `State` handles `State Unit`, and the body performs `State Int`
      planned [ loweringOf "dropState" (stateEntry unitTy) [] ]
        (boundaryWith XRowEmpty (\sigma -> [ Tuple (closed [ state int ]) sigma ]))
        \result _ _ -> result `shouldEqual` Rejected (ImplicitPayloadConflict (InDeclaration (declaration "f")) (EffectKey (effect "State")))

    it "opens a handler's kind quantifiers at fresh kinds, recorded with the plan" do
      let
        quiet = lowering "quiet" "Console" []
        kinded = quiet { scheme = { kindVars: [ KindVar "k" ], body: TForall (TyVar "p") (KVar (KindVar "k")) quiet.scheme.body } }
      planned [ kinded ] (boundaryWith XRowEmpty (\sigma -> [ Tuple (closed [ console ]) sigma ])) \result r after -> do
        result `shouldEqual` Completed
        map (\p -> map (Array.length <<< _.kinds) p.steps) (Map.lookup r.sigma after.tentative.plans) `shouldEqual` Just [ 1 ]

    it "fixes a tail only the body's row holds by the plan's last equation, the handler's constraints required at the boundary" do
      planned [ lowering "lowerConsole" "Console" [ "Clock" ] ]
        ( do
            t <- freshInstantiationRow withE
            r <- boundaryIn (siteIn "f" withE) (row [ clock ] e) (\sigma -> [ Tuple (row [ console ] t) sigma ])
            pure { sigma: r.sigma, fits: r.fits, t }
        )
        \result r after -> do
          result `shouldEqual` Completed
          sameRow after r.t e
      planned [ lowering "lowerConsole" "Console" [ "LiftIO" ] ]
        ( do
            t <- freshInstantiationRow withE
            boundaryIn (siteIn "f" withE) (row [ liftIO ] e) (\sigma -> [ Tuple (row [ console ] t) sigma ])
        )
        \result _ _ -> case result of
          Rejected (ObligationBroken b) -> b.breach `shouldEqual` LacksUnprovenAtSite (EffectKey (effect "LiftIO")) (TyVar "e")
          other -> fail ("not the constraint `LiftIO ∉ e`: " <> show other)

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
  closeBoundary at sigma expected (XCon unitTy [])
  pure { sigma, fits }

liftIO :: XRowEntry
liftIO = XRowEffectEntry (effect "LiftIO") []

logging :: XRowEntry
logging = XRowEffectEntry (effect "Logging") []

-- | `E ~> ( t̄ )` in `M`, under the name given, as `Ξ` holds it.
lowering :: String -> String -> Array String -> ImplicitCandidate
lowering name source targets = loweringOf name (entry source) (map entry targets)
  where
  entry n = RowEffectEntry (effect n) []

-- | `E τ̄ ~> ( t̄ )` under the name given, its elements as written.
loweringOf :: String -> RowEntry -> Array RowEntry -> ImplicitCandidate
loweringOf name source targets = { handler: declaration name, source, targets, scheme: capabilityScheme source targets }

-- | The expansion of `E τ̄ ~> ( t̄ )`.
capabilityScheme :: RowEntry -> Array RowEntry -> TypeScheme
capabilityScheme source targets = { kindVars: [], body }
  where
  residual = TVar (TyVar "q")
  answer = TVar (TyVar "b")
  elements = Array.cons source targets
  rowOf entries tail = foldr TRowExtend tail entries
  lacking = map (\entry -> Lacks (rowEntryKey entry) residual) elements
  body = TForall (TyVar "q") (KRow RowEffect)
    (foldr TConstrained (TForall (TyVar "b") KType (fn (fn (TCon unitTy []) (rowOf elements residual) answer) (rowOf targets residual) answer)) lacking)

-- | The boundary the action builds, decided with `Ξ` holding the handlers
-- | given: what the loop came to, what the action gave, and the state after.
planned
  :: forall r
   . Array ImplicitCandidate
  -> Elab { sigma :: MetaVar | r }
  -> (RunResult -> { sigma :: MetaVar | r } -> SolverState -> Aff Unit)
  -> Aff Unit
planned implicits action k = case runAttempt withXi action (initialState (SessionId 0) 100) of
  Tuple (Done r) s -> case run withXi s of
    Tuple report after -> k report.result r after
  _ -> fail "not done"
  where
  withXi = session { implicits = implicits }

-- | The plan a boundary recorded: its handlers by name, innermost first, and
-- | what the thunk of its body is widened by.
planOf :: SolverState -> MetaVar -> Maybe { handlers :: Array String, widening :: Array XRowEntry }
planOf s sigma = Map.lookup sigma s.tentative.plans <#> \p ->
  { handlers: map (\step -> case step.handler of Qualified _ (Ident n) -> n) p.steps, widening: p.widening }

-- | `State τ`, the type constructor given at no kind.
stateEntry :: Qualified TyName -> RowEntry
stateEntry t = RowEffectEntry (effect "State") [ TCon t [] ]
