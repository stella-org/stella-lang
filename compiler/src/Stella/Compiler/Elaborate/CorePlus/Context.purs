-- | The local context `Γ` over Core⁺, and the atomic facts `Γ*` an attempt
-- | reads off it.
-- |
-- | A pending job is created deep inside a term and attempted much later, when
-- | elaboration stands somewhere else entirely, so each job carries the context
-- | it was created under and is decided against that one (D40). What is carried
-- | is **lexical belonging and not solutions**: the types bound here and the
-- | rows the assumptions mention may contain metavariables, and what one of
-- | those stands for is `Ψ`'s to say at the moment of the attempt.
-- |
-- | A context therefore holds no metavariable context, and `facts` takes the
-- | substitution as an argument: the assumptions are decomposed afresh at each
-- | attempt rather than once where they were written.
module Stella.Compiler.Elaborate.CorePlus.Context
  ( XContext
  , Origin(..)
  , Zonk
  , FactsError(..)
  , emptyXContext
  , bindKindVars
  , bindTyVar
  , lookupTyVar
  , bindVar
  , lookupVar
  , kindVarInScope
  , assume
  , facts
  ) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.CorePlus.Kind (XKind)
import Stella.Compiler.Elaborate.CorePlus.Row (XRowError, knownKeys, rigidTails, sharedKey, xnf)
import Stella.Compiler.Elaborate.CorePlus.Type (XConstraint(..), XType)
import Stella.Compiler.TypedCore (Ident, KindVar, Qualified, RowKey, TyVar)
import Stella.Compiler.TypedCore.Entailment (AtomicFacts, addDisjoint, addLacks, noFacts)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldM, foldr)
import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Set as Set
import Data.Show.Generic (genericShow)

-- | `Γ` of Core⁺.
-- |
-- | `assumed` holds the row constraints assumed here **as they were written**.
-- | Core's context keeps them decomposed instead, which it can because nothing
-- | in it is unsolved; here what a decomposition yields depends on `Ψ`, so the
-- | written form is what is kept and `facts` is the projection.
-- |
-- | The two are one field read two ways: what a synthesizer is shown of the
-- | constraints assumed at its site, and what entailment decides from.
type XContext =
  { kindVars :: Set KindVar
  , tyVars :: Map TyVar XKind
  , vars :: Map Ident XType
  , assumed :: P.Array XConstraint
  }

-- | Where a context came from, for diagnostics: the declaration whose
-- | elaboration built it.
-- |
-- | Everything carrying a context carries this beside it — a job, so that a
-- | failure names where the goal was written, and an obligation, so that one
-- | broken by an assignment elsewhere names where it was assumed.
data Origin = InDeclaration (Qualified Ident)

-- | Applying what `Ψ` has solved, which the session supplies.
type Zonk = XType -> XType

data FactsError
  -- | `k ∉ ρ` where the known part of `ρ` carries `k`. Nothing satisfies the
  -- | assumption, which is a property of the context rather than of any
  -- | constraint decided against it.
  = LacksContradiction RowKey
  -- | `ρ1 # ρ2` where the two known parts share a key.
  | DisjointContradiction RowKey
  | FactsRowError XRowError

emptyXContext :: XContext
emptyXContext =
  { kindVars: Set.empty
  , tyVars: Map.empty
  , vars: Map.empty
  , assumed: []
  }

-- | Bind the kind variables of a declaration's scheme. A kind variable enters
-- | `Γ` here and nowhere else: neither grammar has a kind quantifier (D3).
bindKindVars :: XContext -> P.Array KindVar -> XContext
bindKindVars ctx vars =
  ctx { kindVars = foldr Set.insert ctx.kindVars vars }

bindTyVar :: XContext -> TyVar -> XKind -> XContext
bindTyVar ctx name kind =
  ctx { tyVars = Map.insert name kind ctx.tyVars }

lookupTyVar :: XContext -> TyVar -> Maybe XKind
lookupTyVar ctx name = Map.lookup name ctx.tyVars

bindVar :: XContext -> Ident -> XType -> XContext
bindVar ctx name ty =
  ctx { vars = Map.insert name ty ctx.vars }

lookupVar :: XContext -> Ident -> Maybe XType
lookupVar ctx name = Map.lookup name ctx.vars

kindVarInScope :: XContext -> KindVar -> P.Boolean
kindVarInScope ctx name = Set.member name ctx.kindVars

-- | Record an assumption as it was written, and nothing else.
-- |
-- | **This is the lexical half alone, and it is not by itself enough to hold an
-- | assumption.** One whose row has a flexible tail also forbids assignments to
-- | that metavariable — `k ∉ ?r` is violated by `?r := ( k : A | () )` — and
-- | nothing a context does refuses one: `facts` derives no atomic fact from a
-- | flexible tail, so such a solution passes every check made here.
-- |
-- | What refuses it is the obligation the session carries against the
-- | metavariable, and introducing an assumption is therefore one act with
-- | recording that obligation. This operation is what that act is built from
-- | rather than the way to perform it.
assume :: XContext -> XConstraint -> XContext
assume ctx constraint =
  ctx { assumed = Array.snoc ctx.assumed constraint }

-- | `Γ*`, as an attempt reads it.
-- |
-- | **Only a rigid tail yields an atomic fact.** Entailment decides by facts
-- | about the row variables `Γ` binds, and a flexible tail is a metavariable of
-- | `Ψ`: what an assumption says about one is a condition on the assignments it
-- | admits, which the obligation the session carries against that metavariable
-- | enforces rather than these facts.
-- |
-- | This is a projection and never a store. Nothing here is the whole of what an
-- | assumption means, and reading these facts is not what keeps one.
-- |
-- | Every fact derived here is a consequence of the assumption it came from, so
-- | a constraint these facts prove is proved under the assumptions. An
-- | assumption whose tail is still flexible contributes nothing yet and
-- | contributes once that tail is solved to a row with a rigid one, which is
-- | what deriving this at each attempt is for.
facts :: Zonk -> XContext -> Either FactsError AtomicFacts
facts zonk ctx = foldM add noFacts ctx.assumed
  where
  add acc = case _ of
    XLacks key row -> do
      n <- normalize row
      if Map.member key n.known then
        Left (LacksContradiction key)
      else
        Right (foldr (addLacks key) acc (rigidTails n))

    XDisjoint left right -> do
      l <- normalize left
      r <- normalize right
      case sharedKey l r of
        Just key ->
          Left (DisjointContradiction key)
        Nothing ->
          Right (withPairs l r (withKeysOf r l (withKeysOf l r acc)))

  -- { k ∉ t | k ∈ dom(F_a), t ∈ T_b }
  withKeysOf a b acc =
    foldr (\t inner -> foldr (\key i -> addLacks key t i) inner (knownKeys a)) acc
      (rigidTails b)

  -- { t1 # t2 | t1 ∈ T_l, t2 ∈ T_r }
  withPairs l r acc =
    foldr (\t1 inner -> foldr (addDisjoint t1) inner (rigidTails r)) acc (rigidTails l)

  normalize row = case xnf (zonk row) of
    Left err -> Left (FactsRowError err)
    Right n -> Right n

derive instance Eq Origin
derive instance Generic Origin _

instance Show Origin where
  show x = genericShow x

derive instance Eq FactsError
derive instance Generic FactsError _

instance Show FactsError where
  show x = genericShow x
