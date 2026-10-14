-- | A value or computation declaration's body elaborated into Core⁺, checked
-- | against its signature ([Elaboration](../../../../../docs/technical-references/02-Surface-Language/01-Elaboration.md)).
-- |
-- | **Checking is directed by the signature.** A declaration's scheme is opened
-- | by type abstractions, its parameters are bound by λs at the argument types
-- | its arrows give, and its body is checked against what is left. An
-- | application infers its function, checks its argument, and fits the row
-- | the function performs into the row ambient there; a global is instantiated
-- | at a fresh metavariable for each of its kind variables and each `forall`
-- | of its scheme, a row quantifier's an instantiation row; a λ is checked
-- | against an arrow, or inferred under a fresh row where nothing gives its
-- | type; and a form whose type is only inferred is subsumed by what is
-- | expected. Every equation is stated where the node it is about stands, and
-- | one that cannot be decided yet is left to the loop.
-- |
-- | **What a signature or an annotation writes is a checking boundary**: the
-- | right-hand side of a declaration at `()`, and a λ at each arrow written,
-- | its body built under an ambient row of its own that only the boundary
-- | decides. An arrow instantiation or inference gives is no boundary, its row
-- | being ambient as it is.
-- |
-- | **A computation is a thunk**: its definition binds the `Unit` of its Core
-- | type ahead of its body, which is checked under a boundary at the row its
-- | signature writes, and a reference to it is forced, applied to `Prim.Unit`
-- | as any function is applied.
-- |
-- | **What a `Λ` or a constraint abstraction encloses is built at `()` as a
-- | value form**, wherever a quantifier or a constraint expected is opened: a
-- | function whose evaluation may move under a λ is η-expanded, and contracted
-- | again once its fits are decided where it was one already; anything else
-- | no value form is the Core checker's to refuse, as the author's.
-- |
-- | **A definition without a signature is inferred**, its parameters at fresh
-- | types and its body under a fresh inference row, under `()` and no
-- | boundary; one with no parameter may be η-expanded as a quantified body is.
-- |
-- | **A scheme's constraints are assumed where its declaration's body opens
-- | it**, under a constraint abstraction, **and required where a global is
-- | instantiated**, under a constraint application.
-- |
-- | **This version elaborates a subset**: variables, globals, computations,
-- | constructors, literals, application, λ over variables, type annotations,
-- | a wildcard or a typed hole among what they write, expression holes,
-- | `let` blocks and `where`s binding variables and `_`, with a signature or
-- | without, and `case` over variables, `_`, as-patterns, constructors,
-- | literals, or-patterns, and annotated patterns, its alternatives
-- | unguarded. A synthesized argument of the declaration's own is a parameter like any other; a
-- | reference to a value taking one is outside the subset, a goal being what
-- | supplies the argument. Anything else is reported where it stands, and the
-- | declaration holding it is not elaborated further.
module Stella.Compiler.Elaborate.Surface.Expr
  ( Surf
  , Noted
  , ExpressionHole
  , UncoveredMatch
  , runSurf
  , elaborateValue
  , elaborateComputation
  , inferDefinition
  , checkDefinition
  , Parameter(..)
  , expandable
  , references
  , asArrow
  ) where

import Prelude
import Prim hiding (Type)

import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldMap, foldl, foldr)
import Data.Map as Map
import Data.Maybe (Maybe(..), isJust, maybe)
import Data.Set (Set)
import Data.Set as Set
import Data.String (Pattern(..))
import Data.String as String
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Stella.Compiler.Elaborate.CorePlus.Context (Origin(..), XContext, bindKindVars, bindTyVar, bindVar, emptyXContext, lookupVar)
import Stella.Compiler.Elaborate.CorePlus.Kind (XKind(..))
import Stella.Compiler.Elaborate.CorePlus.Term (CoverageId, XDecisionTree(..), XExpr(..), isValueForm)
import Stella.Compiler.Elaborate.CorePlus.Type (XType(..), fromCore)
import Stella.Compiler.Elaborate.Surface.Internal (Internal)
import Stella.Compiler.Elaborate.Surface.Group (groups)
import Stella.Compiler.Elaborate.Environment.Catalog (lookupEntry)
import Stella.Compiler.Elaborate.Environment.Constructors (lookupConstructor)
import Stella.Compiler.Elaborate.Environment.Surface (SurfaceBinding(..), SurfaceEnv)
import Stella.Compiler.Elaborate.Kernel.Builder.Common (substituteKindVars, substituteTyVars)
import Stella.Compiler.Elaborate.Kernel.Elab (Elab, askEnv, assume, break, closeBoundary, currentMetas, equate, freshCoverage, freshIdent, freshJoin, freshInstantiationRow, freshKindMeta, freshTypeMeta, openBoundary, placeFit, recursiveRef, require)
import Stella.Compiler.Elaborate.Mechanism.Fit (FitUse(..))
import Stella.Compiler.Elaborate.Mechanism.Pending (Site)
import Stella.Compiler.Elaborate.Mechanism.Unify (KindRequirement(..), substitute)
import Stella.Compiler.Elaborate.Surface.Match as Match
import Stella.Compiler.Elaborate.Vocabulary.Diagnostic (Defect(..))
import Stella.Compiler.Elaborate.Surface.Type (Elaborated, TypeHole, Unsupported(..), Wildcard, elaborateLocalSignature, elaborateType, xFunction)
import Stella.Compiler.Surface.Expr (Alternative, AlternativeBody(..), Binder(..), Expr(..), GuardLine(..), HandlerItem(..), LetBinding(..), RecordField(..), exprOrigin)
import Stella.Compiler.Surface.Name (BindingId, LocalVar(..))
import Stella.Compiler.Surface.Origin as Surface
import Stella.Compiler.TypedCore.Name (Ident(..), KindVar, Qualified)
import Stella.Compiler.TypedCore.Prim (functionTy, litType, unitCtor, unitTy)
import Stella.Compiler.TypedCore.Kind (RowElemKind(..))
import Stella.Compiler.TypedCore.Type (TypeScheme)

-- | Elaboration that stops at the first form this version does not read, and
-- | notes the typed holes and the wildcards its annotations hold, to be
-- | reported once the body is settled.
newtype Surf a = Surf (Elab (Either Unsupported (Noted a)))

-- | What was built, and the typed holes, the wildcards, the kinds a local
-- | signature leaves unwritten, the expression holes, and the matches that
-- | leave values uncovered, noted on the way, in the order met.
type Noted a =
  { value :: a
  , holes :: Array TypeHole
  , wildcards :: Array Wildcard
  , unwritten :: Array { origin :: Surface.Origin, kind :: XKind }
  , expressionHoles :: Array ExpressionHole
  , uncovered :: Array UncoveredMatch
  }

-- | An expression hole where it is written, by its name, the type it stands
-- | at, and the locals in scope there that source can name, each at its type.
type ExpressionHole = { origin :: Surface.Origin, name :: String, type :: XType, context :: Array { name :: Ident, type :: XType } }

-- | A `case` that leaves values uncovered, where it is written: the number its
-- | uncovered places carry, and a vector of values it does not match.
type UncoveredMatch = { id :: CoverageId, origin :: Surface.Origin, witness :: Array Match.Witness }

runSurf :: forall a. Surf a -> Elab (Either Unsupported (Noted a))
runSurf (Surf e) = e

instance Functor Surf where
  map f (Surf e) = Surf (map (map (\n -> n { value = f n.value })) e)

instance Apply Surf where
  apply = ap

instance Applicative Surf where
  pure a = Surf (pure (Right { value: a, holes: [], wildcards: [], unwritten: [], expressionHoles: [], uncovered: [] }))

instance Bind Surf where
  bind (Surf e) k = Surf
    ( e >>= case _ of
        Left problem -> pure (Left problem)
        Right a -> map (map (\b -> b { holes = a.holes <> b.holes, wildcards = a.wildcards <> b.wildcards, unwritten = a.unwritten <> b.unwritten, expressionHoles = a.expressionHoles <> b.expressionHoles, uncovered = a.uncovered <> b.uncovered })) (runSurf (k a.value))
    )

instance Monad Surf

lift :: forall a. Elab a -> Surf a
lift = Surf <<< map (\a -> Right { value: a, holes: [], wildcards: [], unwritten: [], expressionHoles: [], uncovered: [] })

outside :: forall a. Unsupported -> Surf a
outside = Surf <<< pure <<< Left

-- | Note the typed holes and the wildcards an annotation holds.
note :: forall r. { holes :: Array TypeHole, wildcards :: Array Wildcard | r } -> Surf Unit
note read = Surf (pure (Right { value: unit, holes: read.holes, wildcards: read.wildcards, unwritten: [], expressionHoles: [], uncovered: [] }))

-- | Note what a local signature holds: its typed holes and wildcards, and the
-- | kinds it leaves unwritten, which nothing local generalizes.
noteSignature :: Elaborated -> Surf Unit
noteSignature e = Surf (pure (Right { value: unit, holes: e.holes, wildcards: e.wildcards, unwritten: e.unwritten, expressionHoles: [], uncovered: [] }))

-- | An expression hole at the type given, noted with the locals in scope where
-- | it stands: a value form that performs nothing. Every occurrence is a hole
-- | of its own, its name a label of what is reported.
hole :: Scope -> Surface.Origin -> String -> XType -> Surf (XExpr Surface.Origin)
hole scope origin name ty = Surf (pure (Right { value: EHole origin ty, holes: [], wildcards: [], unwritten: [], expressionHoles: [ { origin, name, type: ty, context } ], uncovered: [] }))
  where
  -- a name with `#` is one the elaborator made
  context = Array.mapMaybe
    (\(Tuple x@(Ident n) t) -> if String.contains (Pattern "#") n then Nothing else Just { name: x, type: t })
    (Map.toUnfoldable scope.context.vars)

-- | What an expression is elaborated under: the declaration it belongs to, the
-- | context its node stands in, the row its evaluation may perform, the entries
-- | the compiler's desugarings refer to that no catalog holds, and what the
-- | surface elaborator reads of the imports and of the module: the synonyms its
-- | annotations are read through, and the values taking a synthesized argument.
type Scope = { declaration :: Qualified Ident, context :: XContext, ambient :: XType, internal :: Internal, surface :: SurfaceEnv }

-- | Where a type an expression is checked against comes from. **An arrow a
-- | signature or an annotation writes is a checking boundary**, and so is every
-- | arrow reached by opening its quantifiers, constraints, and parameters; one
-- | instantiation or inference gives is not, its row being ambient as it is.
data Expected
  = Written
  | Derived

siteAt :: Scope -> Surface.Origin -> Site
siteAt scope origin = { context: scope.context, origin: AtSource { declaration: scope.declaration, origin } }

-- | A value declaration's definition, at its scheme: `Λ`s for its quantifiers,
-- | `λ`s for its parameters, and its body checked against what is left, the
-- | whole of it a checking boundary at `()`, the row every top-level value is
-- | defined at.
elaborateValue
  :: Internal
  -> SurfaceEnv
  -> Qualified Ident
  -> Surface.Origin
  -> TypeScheme
  -> Array Binder
  -> Expr
  -> Surf (XExpr Surface.Origin)
elaborateValue internal surface declaration origin scheme params =
  definition internal surface declaration origin scheme (map Named params)

-- | A computation declaration's definition, at its Core scheme `∀ā. C =>
-- | Unit -{ρ}-> τ`: as a value's, its one parameter the thunk's `Unit`, so its
-- | body is checked against `τ` under a checking boundary at `ρ`.
elaborateComputation
  :: Internal
  -> SurfaceEnv
  -> Qualified Ident
  -> Surface.Origin
  -> TypeScheme
  -> Expr
  -> Surf (XExpr Surface.Origin)
elaborateComputation internal surface declaration origin scheme =
  definition internal surface declaration origin scheme [ Thunk ]

-- | A value declaration's definition where it has no signature, inferred: a
-- | `λ` for each parameter at a fresh type, its body under a fresh inference
-- | row, the whole of it under `()`, which no boundary holds. **A body with no
-- | parameter is η-expanded where that is asked for**, built as the `λ`
-- | applying it to its parameter is inferred, and contracted again once its
-- | fits are decided where it was a value form already.
inferDefinition
  :: Internal
  -> SurfaceEnv
  -> Qualified Ident
  -> Surface.Origin
  -> Array Binder
  -> Expr
  -> Boolean
  -> Surf { expr :: XExpr Surface.Origin, type :: XType }
inferDefinition internal surface declaration origin params body expand = case params of
  [] | expand -> do
    argument <- lift (freshTypeMeta scope.context XKType)
    row <- lift (freshTypeMeta scope.context (XKRow RowEffect))
    x <- lift (freshIdent (Map.keys scope.context.vars) "x")
    let inner = scope { context = bindVar scope.context x argument, ambient = row }
    f <- infer inner body
    applied <- applyTo inner at at f \a -> subsume inner at { expr: EVar at x, type: argument } a
    lambda <- expansion at (ELam at x argument applied.expr)
    pure { expr: lambda, type: xFunction argument row applied.type }
  [] -> infer scope body
  _ -> infer scope (ExprLambda origin params body)
  where
  scope = { declaration, context: emptyXContext, ambient: XRowEmpty, internal, surface }
  at = exprOrigin body

-- | Whether a definition's body is one η-expansion may move under a `λ`: one
-- | with no parameter, that may move, and is no `λ` already.
expandable :: Array Binder -> Expr -> Boolean
expandable params body = Array.null params && delayable body && case body of
  ExprLambda _ _ _ -> false
  _ -> true

definition :: Internal -> SurfaceEnv -> Qualified Ident -> Surface.Origin -> TypeScheme -> Array Parameter -> Expr -> Surf (XExpr Surface.Origin)
definition internal surface declaration origin scheme =
  checkDefinition internal surface declaration origin { kindVars: scheme.kindVars, body: fromCore scheme.body }

-- | A definition checked against the scheme given, as a declaration with a
-- | signature is: a partial signature's, holding what its body decides, among
-- | them.
checkDefinition :: Internal -> SurfaceEnv -> Qualified Ident -> Surface.Origin -> { kindVars :: Array KindVar, body :: XType } -> Array Parameter -> Expr -> Surf (XExpr Surface.Origin)
checkDefinition internal surface declaration origin scheme params body =
  boundary scope0 origin XRowEmpty \scope -> abstractions origin true false Written scope params body scheme.body
  where
  scope0 = { declaration, context: bindKindVars emptyXContext scheme.kindVars, ambient: XRowEmpty, internal, surface }

-- | A parameter a definition binds: one written, or a computation's thunk,
-- | whose `Unit` nothing names.
data Parameter
  = Named Binder
  | Thunk

-- | What the action given builds under a checking boundary's ambient row, the
-- | boundary closed against the row expected once it is built.
boundary :: forall a. Scope -> Surface.Origin -> XType -> (Scope -> Surf a) -> Surf a
boundary scope origin expected inside = do
  sigma <- lift (openBoundary scope.context)
  built <- inside (scope { ambient = XMeta sigma })
  lift (closeBoundary (siteAt scope origin) sigma expected)
  pure built

-- | The expected type opened along its spine: a `Λ` for each quantifier and a
-- | constraint abstraction for each constraint, the constraint assumed in what
-- | it encloses, and a `λ` for each variable given at the argument its arrow
-- | gives, its body under the arrow's row; then the body at what is left.
-- | Quantifiers and constraints are opened in front of the first variable and
-- | wherever variables remain, so a `forall` following a parameter, a
-- | synthesized argument's among them, is opened where it stands; one left
-- | once every variable is bound is the body's to meet. A `λ` at an arrow that
-- | is written is a checking boundary at the arrow's row. What a `Λ` or a
-- | constraint abstraction encloses is built at `()`, as a value form.
abstractions :: Surface.Origin -> Boolean -> Boolean -> Expected -> Scope -> Array Parameter -> Expr -> XType -> Surf (XExpr Surface.Origin)
abstractions origin front quantified expected scope params body ty = case ty, Array.uncons params of
  XForall a k rest, _ | opening -> ETyLam origin a k <$> abstractions origin front true expected (scope { context = bindTyVar scope.context a k, ambient = XRowEmpty }) params body rest
  XConstrained c rest, _ | opening -> do
    context <- lift (assume (siteAt scope origin) c)
    EConstraintLam origin c <$> abstractions origin front true expected (scope { context = context, ambient = XRowEmpty }) params body rest
  _, Nothing
    | quantified -> quantifiedBody scope body expected ty
    | otherwise -> check scope body expected ty
  _, Just { head, tail } -> do
    let at = parameterOrigin head
    parts <- arrow scope at ty
    let bound o name = lambdaAt scope o expected name parts \s -> abstractions origin false false expected s tail body parts.result
    case head of
      Named (BinderVar o (LocalVar v)) -> bound o v.name
      Named (BinderInvalid o) -> outside (ReportedAlready o)
      Named other -> outside (OutsideSubset (binderOrigin other) "a pattern that is no variable")
      Thunk -> bound at =<< lift (freshIdent (Map.keys scope.context.vars) "u")
  where
  opening = front || not (Array.null params)
  parameterOrigin = case _ of
    Named b -> binderOrigin b
    Thunk -> origin

-- | A `λ` binding the name given at the arrow's argument, its body built by the
-- | action given: under a checking boundary at the arrow's row where the arrow
-- | is written, and under the row as it is otherwise.
lambdaAt :: Scope -> Surface.Origin -> Expected -> Ident -> { argument :: XType, row :: XType, result :: XType } -> (Scope -> Surf (XExpr Surface.Origin)) -> Surf (XExpr Surface.Origin)
lambdaAt scope origin expected name parts body =
  ELam origin name parts.argument <$> case expected of
    Written -> boundary inner origin parts.row body
    Derived -> body (inner { ambient = parts.row })
  where
  inner = scope { context = bindVar scope.context name parts.argument }

-- | What a `Λ` or a constraint abstraction encloses, which Core takes only as a
-- | value form. **Where its type is a function and its evaluation may move
-- | under a λ, it is η-expanded**, built under the new λ so each wrapping fit in
-- | it is fitted into that λ's row, and contracted again once every fit is
-- | decided where what the λ applies is a value form as it stands. Anything
-- | else is built as it is, the Core checker refusing it where it is no value
-- | form.
quantifiedBody :: Scope -> Expr -> Expected -> XType -> Surf (XExpr Surface.Origin)
quantifiedBody scope body expected ty = do
  metas <- lift currentMetas
  case body, asArrow (substitute metas ty) of
    ExprLambda _ _ _, _ -> check scope body expected ty
    _, Just _ | delayable body -> do
      parts <- arrow scope origin ty
      x <- lift (freshIdent (Map.keys scope.context.vars) "x")
      lambda <- lambdaAt scope origin expected x parts \s -> do
        f <- infer s body
        applied <- applyTo s origin origin f \argument -> subsume s origin { expr: EVar origin x, type: parts.argument } argument
        subsume s origin applied parts.result
      expansion origin lambda
    _, _ -> check scope body expected ty
  where
  origin = exprOrigin body

-- | A `λ` an η-expansion built, marked as one, and as contractible where what it
-- | applies to its parameter is a value form as it stands.
expansion :: Surface.Origin -> XExpr Surface.Origin -> Surf (XExpr Surface.Origin)
expansion origin lambda = do
  env <- lift askEnv
  let
    isConstructor = isJust <<< lookupConstructor env.session.constructors
    -- what the λ applies, under the fits around the application
    applies = case _ of
      EFit _ _ e -> applies e
      EApp _ f _ -> Just f
      _ -> Nothing
    contractible = case lambda of
      ELam _ _ _ inner -> maybe false (isValueForm isConstructor) (applies inner)
      _ -> false
  pure (EEta origin contractible lambda)

-- | Whether the evaluation of an expression may move under a λ with no
-- | observable difference: a variable, a global, a constructor, a literal, a
-- | λ, an annotation of such a form, and a constructor applied to such forms.
-- | None performs, faults, diverges, or reads a cell.
delayable :: Expr -> Boolean
delayable = case _ of
  ExprLocal _ _ -> true
  ExprValue _ _ -> true
  ExprConstructor _ _ -> true
  ExprLiteral _ _ -> true
  ExprLambda _ _ _ -> true
  ExprTyped _ inner _ -> delayable inner
  ExprApp _ f x -> constructorSpine f && delayable x
  _ -> false
  where
  constructorSpine = case _ of
    ExprConstructor _ _ -> true
    ExprApp _ f x -> constructorSpine f && delayable x
    _ -> false

-- | The top-level values and computations an expression refers to anywhere in
-- | it, read off every form, whether or not this version elaborates it. A
-- | local is no reference, being bound where it is used.
references :: Expr -> Set (Qualified Ident)
references = mentioned case _ of
  ExprValue _ name -> Just (Set.singleton name)
  ExprComputation _ name -> Just (Set.singleton name)
  _ -> Nothing

-- | The locals an expression refers to anywhere in it, by their bindings.
localReferences :: Expr -> Set BindingId
localReferences = mentioned case _ of
  ExprLocal _ (LocalVar v) -> Just (Set.singleton v.id)
  _ -> Nothing

-- | What the leaf given reads off each form of an expression where it reads
-- | anything, every form traversed whether or not this version elaborates it.
mentioned :: forall x. Ord x => (Expr -> Maybe (Set x)) -> Expr -> Set x
mentioned leaf = go
  where
  go e = case leaf e of
    Just found -> found
    Nothing -> case e of
      ExprApp _ f x -> go f <> go x
      ExprOperator _ op l r -> go op <> go l <> go r
      ExprTyped _ inner _ -> go inner
      ExprSelect _ inner _ -> go inner
      ExprTuple _ es -> foldMap go es
      ExprRecord _ fields -> foldMap field fields
      ExprLambda _ _ body -> go body
      ExprLet _ bindings body -> foldMap binding bindings <> go body
      ExprCase _ scrutinees alternatives -> foldMap go scrutinees <> foldMap (alternative <<< _.body) alternatives
      ExprHandle _ cells items body -> foldMap (go <<< _.initial) cells <> foldMap item items <> go body
      ExprCellWrite _ _ value -> go value
      _ -> Set.empty
  field = case _ of
    FieldValue _ _ e -> go e
    FieldUpdate _ _ e -> go e
    FieldSpread _ e -> go e
  binding = case _ of
    LetValue b -> go b.body
    LetPattern b -> go b.body
  alternative = case _ of
    Unconditional e -> go e
    Guarded lines -> foldMap guardLine lines
  guardLine = case _ of
    GuardBinding _ _ e -> go e
    GuardWhen _ condition e -> go condition <> go e
    GuardOtherwise _ e -> go e
  item = case _ of
    HandlerApplied e -> go e
    HandlerGroup g -> foldMap (go <<< _.body) g.body.operations <> foldMap (go <<< _.body) g.body.return

-- | A `let` block or a `where`, its bindings elaborated: the scope its body is
-- | elaborated under, and what wraps that body in them.
-- |
-- | **A local binding without a signature is monomorphic** (D48), and one with
-- | a signature is checked against it: every name the block binds is in scope
-- | in every right-hand side and in the body, at its signature's type or else
-- | at a type metavariable of the level it stands at, which its right-hand
-- | side's type is equated with — a parameter's binding inferred as a `λ` is.
-- | A right-hand side is elaborated in the order its group stands in, so that
-- | a reference finds the type of what it refers to as far as it is decided.
-- |
-- | **The bindings are grouped by the references they make to one another**,
-- | each a node — a `_` among them, named apart from every name source can
-- | write, its right-hand side kept — and the groups stand in a stable
-- | dependency order, the one depended on outside: one that does not refer to
-- | itself is a `let`, its right-hand side evaluated where the block stands,
-- | under its ambient row, and a recursive one a `letrec`, every member of
-- | which is elaborated under the empty row, as Core checks it: a member that
-- | is no function is initialized as the group is entered, and what it reads
-- | too early is judged once the declaration is settled.
letBlock :: Scope -> Surface.Origin -> Array LetBinding -> Surf { scope :: Scope, wrap :: XExpr Surface.Origin -> XExpr Surface.Origin }
letBlock scope origin bindings = do
  heads <- traverse head bindings
  let
    inner = scope { context = foldl (\c h -> bindVar c h.name h.type) scope.context heads }
    indexOf = Map.fromFoldable (Array.catMaybes (Array.mapWithIndex (\i h -> map (\v -> Tuple v i) h.binding) heads))
    refers = map (\h -> Set.fromFoldable (Array.mapMaybe (\v -> Map.lookup v indexOf) (Array.fromFoldable (localReferences h.body)))) heads
    grouped = groups refers
  -- each right-hand side in the order its group stands, what it refers to
  -- elaborated before it
  built <- traverse (\g -> traverse (rhs (if g.recursive then inner { ambient = XRowEmpty } else inner)) (Array.mapMaybe (Array.index heads) g.members)) grouped
  let wraps = map (\(Tuple g members) -> wrapping g members) (Array.zip grouped built)
  pure { scope: inner, wrap: \e -> foldr (\w acc -> w acc) e wraps }
  where
  head = case _ of
    -- a local signature is read under the context the block stands in, and
    -- what it holds undecided reported once the declaration is settled
    LetValue v | Just signature <- v.signature -> do
      let LocalVar l = v.var
      e <- lift (elaborateLocalSignature scope.surface.synonyms scope.declaration scope.context signature)
      case Array.head e.unsupported of
        Just problem -> outside problem
        Nothing
          | not (Array.null e.synthesized) -> outside (OutsideSubset v.origin "a local signature taking a synthesized argument")
          | otherwise -> do
              noteSignature e
              pure { origin: v.origin, binding: Just l.id, name: l.name, params: v.params, body: v.body, type: e.type, signed: true }
    LetValue v -> let LocalVar l = v.var in fresh v.origin (Just l.id) l.name v.params v.body
    LetPattern p -> case p.binder of
      BinderVar _ (LocalVar l) -> fresh p.origin (Just l.id) l.name [] p.body
      BinderWildcard _ -> do
        name <- lift (freshIdent (Map.keys scope.context.vars) "_")
        fresh p.origin Nothing name [] p.body
      BinderInvalid o -> outside (ReportedAlready o)
      other -> outside (OutsideSubset (binderOrigin other) "a pattern that is no variable")

  fresh o binding name params body = do
    ty <- lift (freshTypeMeta scope.context XKType)
    pure { origin: o, binding, name, params, body, type: ty, signed: false }

  -- a binding with a signature is checked against it, as a definition is,
  -- under the row its group is elaborated under
  rhs inner h | h.signed = do
    expr <- abstractions h.origin true false Written inner (map Named h.params) h.body h.type
    pure { head: h, expr }
  rhs inner h = do
    inferred <- case h.params of
      [] -> infer inner h.body
      params -> infer inner (ExprLambda h.origin params h.body)
    lift (equate (siteAt inner h.origin) { kind: XKType, left: inferred.type, right: h.type })
    pure { head: h, expr: inferred.expr }

  wrapping g members' = case g.recursive, members' of
    false, [ b ] -> \e -> ELet b.head.origin b.head.name b.head.type b.expr e
    _, members -> \e -> ELetRec (maybe origin _.head.origin (Array.head members)) (map (\b -> { name: b.head.name, ty: b.head.type, value: b.expr }) members) e

-- | The argument, the row, and the result of the arrow the type must be: its
-- | own where it is one, and otherwise an arrow of fresh metavariables it is
-- | equated with, its row an inference row.
arrow :: Scope -> Surface.Origin -> XType -> Surf { argument :: XType, row :: XType, result :: XType }
arrow scope origin ty = do
  metas <- lift currentMetas
  case substitute metas ty of
    XApp (XApp (XApp (XCon name []) argument) row) result | name == functionTy -> pure { argument, row, result }
    _ -> do
      argument <- lift (freshTypeMeta scope.context XKType)
      row <- lift (freshTypeMeta scope.context (XKRow RowEffect))
      result <- lift (freshTypeMeta scope.context XKType)
      lift (equate (siteAt scope origin) { kind: XKType, left: ty, right: xFunction argument row result })
      pure { argument, row, result }

check :: Scope -> Expr -> Expected -> XType -> Surf (XExpr Surface.Origin)
check scope expr expected ty = case expr of
  ExprLambda o binders body -> abstractions o false false expected scope (map Named binders) body ty
  ExprLet o bindings body -> do
    block <- letBlock scope o bindings
    block.wrap <$> check block.scope body expected ty
  ExprInvalid o -> outside (ReportedAlready o)
  ExprHole o name -> hole scope o name ty
  _ -> do
    metas <- lift currentMetas
    case substitute metas ty of
      -- a quantifier or a constraint expected is opened where the form stands
      opened@(XForall _ _ _) -> abstractions (exprOrigin expr) true false expected scope [] expr opened
      opened@(XConstrained _ _) -> abstractions (exprOrigin expr) true false expected scope [] expr opened
      _ -> case expr of
        ExprCase o scrutinees alternatives -> caseOf scope o scrutinees alternatives expected ty
        _ -> do
          inferred <- infer scope expr
          subsume scope (exprOrigin expr) inferred ty

-- | An expression inferred at one type where another is expected. **Where both
-- | are arrows, the outermost row alone is contained**, a wrapping fit around
-- | the expression, and the arguments and the results are equal; anything else
-- | is an equation of the two types.
subsume :: Scope -> Surface.Origin -> { expr :: XExpr Surface.Origin, type :: XType } -> XType -> Surf (XExpr Surface.Origin)
subsume scope origin inferred expected = do
  metas <- lift currentMetas
  case asArrow (substitute metas inferred.type), asArrow (substitute metas expected) of
    Just given, Just wanted -> do
      lift (equate site { kind: XKType, left: given.argument, right: wanted.argument })
      lift (equate site { kind: XKType, left: given.result, right: wanted.result })
      fit <- lift (placeFit site Wrapping given.row wanted.row)
      pure (EFit origin fit inferred.expr)
    _, _ -> do
      lift (equate site { kind: XKType, left: inferred.type, right: expected })
      pure inferred.expr
  where
  site = siteAt scope origin

asArrow :: XType -> Maybe { argument :: XType, row :: XType, result :: XType }
asArrow = case _ of
  XApp (XApp (XApp (XCon name []) argument) row) result | name == functionTy -> Just { argument, row, result }
  _ -> Nothing

infer :: Scope -> Expr -> Surf { expr :: XExpr Surface.Origin, type :: XType }
infer scope expr = case expr of
  -- a local at a scheme, however it came to be one, is instantiated where it
  -- is referred to, as a global is
  ExprLocal o (LocalVar v) -> case lookupVar scope.context v.name of
    Just ty -> do
      metas <- lift currentMetas
      instantiated o (EVar o v.name) (substitute metas ty)
    Nothing -> outside (OutsideSubset o "a variable bound outside what this version elaborates")
  ExprValue o name -> global o name
  ExprConstructor o name -> global o name
  -- a computation is forced, applied to `Prim.Unit` where it is referred to
  ExprComputation o name -> do
    thunk <- global o name
    applyTo scope o o thunk \argument -> subsume scope o { expr: EGlobal o unitCtor [], type: XCon unitTy [] } argument
  ExprLiteral o literal -> pure { expr: ELit o literal, type: fromCore (litType literal) }
  ExprApp _ f x -> do
    f' <- infer scope f
    applyTo scope (exprOrigin f) (exprOrigin expr) f' \argument -> check scope x Derived argument
  ExprTyped _ inner t -> do
    annotation <- lift (elaborateType scope.surface.synonyms scope.declaration scope.context t)
    case Array.head annotation.unsupported of
      Just problem -> outside problem
      Nothing -> do
        note annotation
        inner' <- check scope inner Written annotation.type
        pure { expr: inner', type: annotation.type }
  -- a λ whose type is not known: each parameter at a fresh type, its body
  -- under a fresh inference row
  ExprLambda _ binders body -> lambda binders body
  ExprLet o bindings body -> do
    block <- letBlock scope o bindings
    inner <- infer block.scope body
    pure { expr: block.wrap inner.expr, type: inner.type }
  ExprInvalid o -> outside (ReportedAlready o)
  ExprHole o name -> do
    ty <- lift (freshTypeMeta scope.context XKType)
    { expr: _, type: ty } <$> hole scope o name ty
  ExprCase o scrutinees alternatives -> do
    ty <- lift (freshTypeMeta scope.context XKType)
    { expr: _, type: ty } <$> caseOf scope o scrutinees alternatives Derived ty
  _ -> outside (OutsideSubset (exprOrigin expr) "this form")
  where
  lambda binders body = case Array.uncons binders of
    Nothing -> infer scope body
    Just { head: BinderVar o (LocalVar v), tail } -> do
      argument <- lift (freshTypeMeta scope.context XKType)
      row <- lift (freshTypeMeta scope.context (XKRow RowEffect))
      inner <- infer' (scope { context = bindVar scope.context v.name argument, ambient = row }) tail body
      pure { expr: ELam o v.name argument inner.expr, type: xFunction argument row inner.type }
    Just { head: BinderInvalid o } -> outside (ReportedAlready o)
    Just { head } -> outside (OutsideSubset (binderOrigin head) "a pattern that is no variable")

  infer' s binders body = case binders of
    [] -> infer s body
    _ -> infer s (ExprLambda (exprOrigin body) binders body)

  -- a global at a fresh metavariable for each kind variable and each
  -- quantifier of its scheme, outermost first, a row quantifier's an
  -- instantiation row: one the catalog holds, or one a desugaring of the
  -- compiler's refers to
  global o name = do
    env <- lift askEnv
    case Map.lookup name scope.surface.bindings of
      -- a member of the group being elaborated is referred to at the one type
      -- it has there, the reference made ordinary once the group is
      -- generalized
      Just (Provisional ty) -> do
        id <- lift (recursiveRef (siteAt scope o) name)
        pure { expr: ERecursiveRef o id, type: ty }
      Just ProvisionalScheme -> outside (OutsideSubset o "a recursive reference to a value whose partial signature is a scheme")
      _ -> case lookupScheme env.session.catalog name of
        Nothing -> outside (OutsideSubset o "a global the catalog does not hold")
        -- a synthesized argument is supplied by a goal, which this version
        -- does not create
        Just _ | Set.member name scope.surface.synthesizing -> outside (OutsideSubset o "a reference to a value taking a synthesized argument")
        Just scheme -> do
          kinds <- lift (traverse (\_ -> freshKindMeta scope.context.kindVars (Set.singleton Quantifiable)) scheme.kindVars)
          let ty = substituteKindVars (Map.fromFoldable (Array.zip scheme.kindVars kinds)) scheme.body
          instantiated o (EGlobal o name kinds) ty

  lookupScheme catalog name = case lookupEntry catalog name, Map.lookup name scope.surface.bindings of
    Just entry, _ -> Just entry.scheme
    Nothing, Just (Final scheme) -> Just { kindVars: scheme.kindVars, body: fromCore scheme.body }
    Nothing, _ -> Map.lookup name scope.internal

  instantiated o e = case _ of
    XForall a k rest -> do
      m <- lift case k of
        XKRow RowEffect -> freshInstantiationRow scope.context
        _ -> freshTypeMeta scope.context k
      instantiated o (ETyApp o e m) (substituteTyVars (Map.singleton a m) Map.empty rest)
    XConstrained c rest -> do
      lift (require (siteAt scope o) c)
      instantiated o (EConstraintApp o e) rest
    ty -> pure { expr: e, type: ty }

-- | A function inferred where it stands, applied to the argument built at the
-- | type it takes, and fitted there into the row ambient: the function's place,
-- | then the application's.
applyTo :: Scope -> Surface.Origin -> Surface.Origin -> { expr :: XExpr Surface.Origin, type :: XType } -> (XType -> Surf (XExpr Surface.Origin)) -> Surf { expr :: XExpr Surface.Origin, type :: XType }
applyTo scope at whole f argument = do
  parts <- arrow scope at f.type
  x <- argument parts.argument
  fit <- lift (placeFit (siteAt scope at) Wrapping parts.row scope.ambient)
  pure { expr: EApp whole (EFit at fit f.expr) x, type: parts.result }

-- | A `case`, at the type given. Its scrutinees are inferred from the left
-- | under the ambient row; each alternative's patterns are checked against
-- | their types, and its body is elaborated once, under the variables they
-- | bind, against the type given; and the match is compiled into a decision
-- | tree (`Stella.Compiler.Elaborate.Surface.Match`).
-- |
-- | **No body is copied.** An alternative one leaf takes stands in that leaf;
-- | any other, one no leaf takes among them, is a join point around the `case`
-- | whose parameters are the variables its patterns bind, each leaf binding
-- | them and jumping to it. A match leaving values uncovered is noted with a
-- | vector of values it does not match, and each place it leaves uncovered
-- | stands in the tree under the number of that note.
caseOf :: Scope -> Surface.Origin -> Array Expr -> Array Alternative -> Expected -> XType -> Surf (XExpr Surface.Origin)
caseOf scope origin scrutinees alternatives expected result = do
  inferred <- traverse (infer scope) scrutinees
  typed <- traverse (alternative (map _.type inferred)) (Array.mapWithIndex Tuple alternatives)
  env <- lift askEnv
  let
    table = map (\c -> { owner: c.owner, tag: c.tag, arity: Array.length c.fields }) env.session.constructors
    rows = Array.concatMap _.rows typed
    width = Array.length scrutinees
  compiled <- matched (Match.compile table width rows)
  uncovered <-
    if uncovers compiled.plan then do
      found <- matched (Match.witness table width rows)
      case found of
        Just witness -> do
          id <- lift freshCoverage
          noteUncovered { id, origin, witness }
          pure (Just id)
        Nothing -> malformed
    else pure Nothing
  placed <- traverse (place compiled.references) typed
  tree <- built uncovered placed compiled.plan
  pure (foldr wrap (ECase origin (map _.expr inferred) tree) placed)
  where
  -- an alternative's rows, one per choice written at its top, the variables
  -- they bind, and its body
  alternative types (Tuple index alt) = case alt.body of
    Guarded _ -> outside (OutsideSubset alt.origin "a guard block")
    Unconditional body -> do
      rows <- traverse (\written -> traverse (\(Tuple b t) -> pattern scope b t) (Array.zip written types)) alt.patterns
      let
        vars = Array.concatMap _.vars (Array.concat rows)
        several = Array.length alt.patterns > 1
        choice written = case Array.head written, Array.last written of
          Just first, Just last | several -> Just (Surface.spanning (binderOrigin first) (binderOrigin last))
          _, _ -> Nothing
      body' <- check (scope { context = foldl (\c v -> bindVar c v.name v.type) scope.context vars }) body expected result
      pure
        { index
        , vars
        , body: body'
        , rows: Array.zipWith (\written typedRow -> { alternative: index, choice: choice written, patterns: map _.pattern typedRow }) alt.patterns rows
        }

  place counts t = case Map.lookup t.index counts of
    Just 1 -> pure { alternative: t, join: Nothing }
    _ -> do
      j <- lift (freshJoin Set.empty "alt")
      pure { alternative: t, join: Just j }

  built uncovered placed = case _ of
    Match.Leaf i bindings -> case Array.find (\p -> p.alternative.index == i) placed of
      Just p -> pure (foldr (\b t -> XBind b.name b.occurrence t) (XLeaf (leafOf p)) bindings)
      Nothing -> malformed
    Match.Uncovered -> maybe malformed (pure <<< XUncovered) uncovered
    Match.SwitchCtor o branches fallback ->
      XSwitchCtor o
        <$> traverse (\b -> { ctor: b.ctor, tree: _ } <$> built uncovered placed b.plan) branches
        <*> traverse (built uncovered placed) fallback
    Match.SwitchLit o branches fallback ->
      XSwitchLit o
        <$> traverse (\b -> { lit: b.lit, tree: _ } <$> built uncovered placed b.plan) branches
        <*> built uncovered placed fallback

  leafOf p = case p.join of
    Nothing -> p.alternative.body
    Just j -> EJump origin j (map (\v -> EVar origin v.name) p.alternative.vars)

  wrap p e = case p.join of
    Nothing -> e
    Just j -> ELetJoin origin j (map (\v -> { name: v.name, ty: v.type }) p.alternative.vars) result p.alternative.body e

  matched :: forall x. Either Match.MatchError x -> Surf x
  matched = case _ of
    Right x -> pure x
    Left _ -> malformed

  malformed :: forall x. Surf x
  malformed = lift (break (MatchMalformed (AtSource { declaration: scope.declaration, origin })))

  uncovers = case _ of
    Match.Leaf _ _ -> false
    Match.Uncovered -> true
    Match.SwitchCtor _ branches fallback -> Array.any (uncovers <<< _.plan) branches || maybe false uncovers fallback
    Match.SwitchLit _ branches fallback -> Array.any (uncovers <<< _.plan) branches || uncovers fallback

-- | Note a match that leaves values uncovered.
noteUncovered :: UncoveredMatch -> Surf Unit
noteUncovered m = Surf (pure (Right { value: unit, holes: [], wildcards: [], unwritten: [], expressionHoles: [], uncovered: [ m ] }))

-- | A pattern checked against the type of the value it matches, as the
-- | compiler of matches reads it, and the variables it binds, each at its
-- | type, in the order written. A constructor is instantiated as a reference
-- | to it is, its fields read off its arrows and what it builds equated with
-- | the type given; a literal's type is equated with it, and so is an
-- | annotation's.
pattern :: Scope -> Binder -> XType -> Surf { pattern :: Match.Pattern Surface.Origin, vars :: Array { name :: Ident, type :: XType } }
pattern scope binder ty = case binder of
  BinderWildcard _ -> pure { pattern: Match.PAny, vars: [] }
  BinderVar _ (LocalVar v) -> pure { pattern: Match.PVar v.name, vars: [ { name: v.name, type: ty } ] }
  BinderAs _ (LocalVar v) inner -> do
    p <- pattern scope inner ty
    pure { pattern: Match.PAs v.name p.pattern, vars: Array.cons { name: v.name, type: ty } p.vars }
  BinderConstructor o name args -> do
    instantiated <- infer scope (ExprConstructor o name)
    fields <- fieldsOf o (Array.length args) instantiated.type
    lift (equate (siteAt scope o) { kind: XKType, left: fields.result, right: ty })
    parts <- traverse (\(Tuple b t) -> pattern scope b t) (Array.zip args fields.arguments)
    pure { pattern: Match.PCtor name (map _.pattern parts), vars: Array.concatMap _.vars parts }
  BinderLiteral o literal -> do
    lift (equate (siteAt scope o) { kind: XKType, left: fromCore (litType literal), right: ty })
    pure { pattern: Match.PLit literal, vars: [] }
  BinderOr _ choices -> do
    parts <- traverse (\b -> pattern scope b ty) choices
    pure
      { pattern: Match.POr (Array.zipWith (\b p -> { label: binderOrigin b, pattern: p.pattern }) choices parts)
      , vars: Array.concatMap _.vars parts
      }
  BinderTyped o inner t -> do
    annotation <- lift (elaborateType scope.surface.synonyms scope.declaration scope.context t)
    case Array.head annotation.unsupported of
      Just problem -> outside problem
      Nothing -> do
        note annotation
        lift (equate (siteAt scope o) { kind: XKType, left: annotation.type, right: ty })
        pattern scope inner ty
  BinderTag o _ _ -> outside (OutsideSubset o "a tag pattern")
  BinderTuple o _ -> outside (OutsideSubset o "a tuple pattern")
  BinderRecord o _ _ -> outside (OutsideSubset o "a record pattern")
  BinderInvalid o -> outside (ReportedAlready o)
  where
  -- the argument of each of a constructor's arrows, one per field, and what
  -- is left
  fieldsOf o n t
    | n <= 0 = pure { arguments: [], result: t }
    | otherwise = do
        parts <- arrow scope o t
        rest <- fieldsOf o (n - 1) parts.result
        pure (rest { arguments = Array.cons parts.argument rest.arguments })

binderOrigin :: Binder -> Surface.Origin
binderOrigin = case _ of
  BinderWildcard o -> o
  BinderVar o _ -> o
  BinderAs o _ _ -> o
  BinderConstructor o _ _ -> o
  BinderTag o _ _ -> o
  BinderLiteral o _ -> o
  BinderTuple o _ -> o
  BinderRecord o _ _ -> o
  BinderOr o _ -> o
  BinderTyped o _ _ -> o
  BinderInvalid o -> o
