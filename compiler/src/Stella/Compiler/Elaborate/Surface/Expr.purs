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
-- | constructors, literals, application, λ, type annotations, a wildcard or a
-- | typed hole among what they write, expression holes, records and the
-- | fields selected from them, tuples, `let` blocks and `where`s, with a
-- | signature or without, and `case` with guard blocks; the patterns are
-- | variables, `_`, as-patterns, constructors, literals, or-patterns,
-- | annotated patterns, and record and tuple patterns, and those a parameter, a
-- | binding of a block, or a guard block's binding is written as always match;
-- | a recursive group binds variables alone. A synthesized parameter of the
-- | declaration's own is a parameter like any other, and a reference to a
-- | value taking one is given the synthesized argument a goal fills. Anything
-- | else is reported where it stands, and the declaration holding it is not
-- | elaborated further.
module Stella.Compiler.Elaborate.Surface.Expr
  ( Surf
  , Noted
  , ExpressionHole
  , UncoveredMatch
  , PendingCase
  , CellRegion
  , CellReference
  , tagsOf
  , runSurf
  , elaborateValue
  , elaborateComputation
  , elaborateHandler
  , inferDefinition
  , checkDefinition
  , Parameter(..)
  , expandable
  , references
  , handlerReferences
  , asArrow
  ) where

import Prelude
import Prim hiding (Symbol, Type)

import Data.Array as Array
import Data.Either (Either(..), either)
import Data.Foldable (foldM, foldMap, foldl, foldr, for_)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, isJust, maybe)
import Data.Set (Set)
import Data.Set as Set
import Data.String (Pattern(..))
import Data.String as String
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..), snd)
import Stella.Compiler.Elaborate.CorePlus.Context (Origin(..), XContext, bindKindVars, bindRegion, bindTyVar, bindVar, emptyXContext, lookupVar)
import Stella.Compiler.Elaborate.CorePlus.Kind (XKind(..), fromCoreKind)
import Stella.Compiler.Elaborate.CorePlus.Row (rebuild, xnf)
import Stella.Compiler.Elaborate.CorePlus.Term (CoverageId, PendingCaseId, XDecisionTree(..), XExpr(..), XOpClause(..), isValueForm)
import Stella.Compiler.Elaborate.CorePlus.Type (XConstraint(..), XRowEntry(..), XType(..), fromCore)
import Stella.Compiler.Elaborate.Surface.Internal (Internal, continuationConstructor)
import Stella.Compiler.Elaborate.Surface.Group (groups)
import Stella.Compiler.Elaborate.Environment.Catalog (lookupEntry)
import Stella.Compiler.Elaborate.Environment.Constructors (lookupConstructor)
import Stella.Compiler.Elaborate.Environment.Imported (operationArgument)
import Stella.Compiler.Interface.Operation (operationElement, operationKey, operationRest, operationRow)
import Stella.Compiler.Interface.Scheme (SchemeBody(..), coreBody)
import Stella.Compiler.Elaborate.Environment.Surface (SurfaceBinding(..), SurfaceEnv)
import Stella.Compiler.Elaborate.Kernel.Builder.Common (substituteKindVars, substituteTyVars)
import Stella.Compiler.Elaborate.Kernel.Elab (Elab, askEnv, assume, break, closeBoundary, createSynthesis, currentMetas, currentLevel, equate, freshCoverage, freshBinderName, freshIdent, freshJoin, freshPendingCase, freshRegionName, freshInstantiationRow, freshKindMeta, freshTypeMeta, openBoundary, placeFit, recursiveRef, require)
import Stella.Compiler.Elaborate.Mechanism.Fit (FitUse(..))
import Stella.Compiler.Elaborate.Mechanism.Pending (Site)
import Stella.Compiler.Elaborate.Mechanism.Unify (KindRequirement(..), MetaBinding(..), MetaContext, lookupMeta, substitute)
import Stella.Compiler.Elaborate.Surface.Match as Match
import Stella.Compiler.Elaborate.Vocabulary.Diagnostic (Defect(..))
import Stella.Compiler.Elaborate.Surface.Type (Elaborated, TypeHole, Unsupported(..), Wildcard, elaborateLocalSignature, elaborateType, xFunction)
import Stella.Compiler.Surface.Expr (Alternative, AlternativeBody(..), Binder(..), CellDeclaration, ClauseForm(..), Expr(..), Group, GuardLine(..), HandlerItem(..), LetBinding(..), RecordField(..), exprOrigin)
import Stella.Compiler.Surface.Decl (HandlerDeclaration)
import Stella.Compiler.Surface.Name (BindingId(..), CellVar(..), LocalVar(..))
import Stella.Compiler.Surface.Type (typeOrigin)
import Stella.Compiler.Surface.Origin as Surface
import Stella.Compiler.TypedCore.Name (Ident(..), KindVar, Qualified, RegionName, Symbol(..), TyVar(..))
import Stella.Compiler.TypedCore.Prim (booleanTy, functionTy, litType, recordTy, unitCtor, unitTy, variantTy)
import Stella.Compiler.TypedCore.Term (Literal(..))
import Stella.Compiler.TypedCore.Kind (RowElemKind(..))
import Stella.Compiler.TypedCore.Type (RowKey(..), Type(..), TypeScheme)

-- | Elaboration that stops at the first form this version does not read, and
-- | notes the typed holes and the wildcards its annotations hold, to be
-- | reported once the body is settled.
newtype Surf a = Surf (Elab (Either Unsupported (Noted a)))

-- | What was built, and the typed holes, the wildcards, the kinds a local
-- | signature leaves unwritten, the expression holes, the matches that leave
-- | values uncovered, the `case`s left pending, and the regions of cells opened
-- | and the references to their cells, noted on the way, in the order met.
type Noted a =
  { value :: a
  , holes :: Array TypeHole
  , wildcards :: Array Wildcard
  , unwritten :: Array { origin :: Surface.Origin, kind :: XKind }
  , expressionHoles :: Array ExpressionHole
  , uncovered :: Array UncoveredMatch
  , pending :: Array PendingCase
  , regions :: Array CellRegion
  , references :: Array CellReference
  }

-- | A region a handling expression declaring cells opens, with where the
-- | expression stands.
type CellRegion = { region :: RegionName, boundary :: Surface.Origin }

-- | A reference to a cell, by the cell's name, with its region and where it
-- | stands.
type CellReference = { region :: RegionName, cell :: Ident, origin :: Surface.Origin }

-- | An expression hole where it is written, by its name, the type it stands
-- | at, and the locals in scope there that source can name, each at its type.
type ExpressionHole = { origin :: Surface.Origin, name :: String, type :: XType, context :: Array { name :: Ident, type :: XType } }

-- | A `case` that leaves values uncovered, where it is written: the number its
-- | uncovered places carry, and a vector of values it does not match.
type UncoveredMatch = { id :: CoverageId, origin :: Surface.Origin, witness :: Array (Match.Witness XType) }

-- | A `case` left pending, where it is written: the number its node carries,
-- | the site it is elaborated at, the metavariables its match may close, read
-- | off the metavariables as they stand, and the match built once they are
-- | decided.
type PendingCase =
  { id :: PendingCaseId
  , site :: Site
  , closable :: MetaContext -> Either Match.MatchError (Array XType)
  , assembled :: MetaContext -> Surf (XExpr Surface.Origin)
  }

runSurf :: forall a. Surf a -> Elab (Either Unsupported (Noted a))
runSurf (Surf e) = e

instance Functor Surf where
  map f (Surf e) = Surf (map (map (\n -> n { value = f n.value })) e)

instance Apply Surf where
  apply = ap

instance Applicative Surf where
  pure a = Surf (pure (Right { value: a, holes: [], wildcards: [], unwritten: [], expressionHoles: [], uncovered: [], pending: [], regions: [], references: [] }))

instance Bind Surf where
  bind (Surf e) k = Surf
    ( e >>= case _ of
        Left problem -> pure (Left problem)
        Right a -> map (map (\b -> b { holes = a.holes <> b.holes, wildcards = a.wildcards <> b.wildcards, unwritten = a.unwritten <> b.unwritten, expressionHoles = a.expressionHoles <> b.expressionHoles, uncovered = a.uncovered <> b.uncovered, pending = a.pending <> b.pending, regions = a.regions <> b.regions, references = a.references <> b.references })) (runSurf (k a.value))
    )

instance Monad Surf

lift :: forall a. Elab a -> Surf a
lift = Surf <<< map (\a -> Right { value: a, holes: [], wildcards: [], unwritten: [], expressionHoles: [], uncovered: [], pending: [], regions: [], references: [] })

outside :: forall a. Unsupported -> Surf a
outside = Surf <<< pure <<< Left

-- | Note the typed holes and the wildcards an annotation holds.
note :: forall r. { holes :: Array TypeHole, wildcards :: Array Wildcard | r } -> Surf Unit
note read = Surf (pure (Right { value: unit, holes: read.holes, wildcards: read.wildcards, unwritten: [], expressionHoles: [], uncovered: [], pending: [], regions: [], references: [] }))

-- | Note what a local signature holds: its typed holes and wildcards, and the
-- | kinds it leaves unwritten, which nothing local generalizes.
noteSignature :: Elaborated -> Surf Unit
noteSignature e = Surf (pure (Right { value: unit, holes: e.holes, wildcards: e.wildcards, unwritten: e.unwritten, expressionHoles: [], uncovered: [], pending: [], regions: [], references: [] }))

-- | An expression hole at the type given, noted with the locals in scope where
-- | it stands: a value form that performs nothing. Every occurrence is a hole
-- | of its own, its name a label of what is reported.
hole :: Scope -> Surface.Origin -> String -> XType -> Surf (XExpr Surface.Origin)
hole scope origin name ty = Surf (pure (Right { value: EHole origin ty, holes: [], wildcards: [], unwritten: [], expressionHoles: [ { origin, name, type: ty, context } ], uncovered: [], pending: [], regions: [], references: [] }))
  where
  -- a name with `#` is one the compiler made
  context = Array.mapMaybe
    (\(Tuple x@(Ident n) t) -> if String.contains (Pattern "#") n then Nothing else Just { name: x, type: t })
    (Map.toUnfoldable scope.context.vars)

-- | What an expression is elaborated under: the declaration it belongs to, the
-- | context its node stands in, the row its evaluation may perform, the entries
-- | the compiler's desugarings refer to that no catalog holds, and what the
-- | surface elaborator reads of the imports and of the module: the synonyms its
-- | annotations are read through, and the values taking a synthesized parameter;
-- | the cells in reach, each by its binding, with its region, its key, and its
-- | type; and, in the body of a `full` clause, the continuation `resume`
-- | applies.
type Scope =
  { declaration :: Qualified Ident
  , context :: XContext
  , ambient :: XType
  , internal :: Internal
  , surface :: SurfaceEnv
  , cells :: Map BindingId { region :: RegionName, name :: Ident, key :: RowKey, type :: XType }
  , resume :: Maybe { name :: Ident, type :: XType }
  }

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

-- | A handler declaration's definition, at its scheme: as a value's, its
-- | parameters bound by `λ`s, then a `λ` binding the thunk of what it handles,
-- | by a name the compiler makes, and its body the handling expression of the
-- | declaration's cells and the group of its clauses around that thunk applied
-- | to `Prim.Unit`. Each application of the handler so enters a region of its
-- | own.
elaborateHandler
  :: Internal
  -> SurfaceEnv
  -> Qualified Ident
  -> Surface.Origin
  -> TypeScheme
  -> HandlerDeclaration
  -> Surf (XExpr Surface.Origin)
elaborateHandler internal surface declaration origin scheme h = do
  name <- lift (freshIdent Set.empty "thunk")
  let thunk = LocalVar { id: thunkBinding, name }
  definition internal surface declaration origin scheme (map Named h.params <> [ Named (BinderVar origin thunk) ])
    (handlerExpr h (ExprApp origin (ExprLocal origin thunk) (ExprConstructor origin unitCtor)))

-- | The binding of a handler declaration's thunk, numbered apart from every
-- | binding resolution numbers.
thunkBinding :: BindingId
thunkBinding = BindingId (-1)

-- | A handler declaration's cells and the group of its clauses, as a handling
-- | expression around the computation given. The group's head is the
-- | declaration's signature, which names the effect handled.
handlerExpr :: HandlerDeclaration -> Expr -> Expr
handlerExpr h computation =
  ExprHandle h.origin h.cells [ HandlerGroup { origin: h.origin, head: typeOrigin h.signature.body, label: Nothing, effect: h.handled, body: h.body } ] computation

-- | The top-level values and computations a handler declaration's cells and
-- | clauses refer to.
handlerReferences :: HandlerDeclaration -> Set (Qualified Ident)
handlerReferences h = references (handlerExpr h (ExprInvalid h.origin))

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
    lambda <- expansion at (ELam at x argument row applied.expr)
    pure { expr: lambda, type: xFunction argument row applied.type }
  [] -> infer scope body
  _ -> infer scope (ExprLambda origin params body)
  where
  scope = { declaration, context: emptyXContext, ambient: XRowEmpty, internal, surface, cells: Map.empty, resume: Nothing }
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
  scope0 = { declaration, context: bindKindVars emptyXContext scheme.kindVars, ambient: XRowEmpty, internal, surface, cells: Map.empty, resume: Nothing }

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
-- | synthesized parameter's among them, is opened where it stands; one left
-- | once every variable is bound is the body's to meet. A `λ` at an arrow that
-- | is written is a checking boundary at the arrow's row. What a `Λ` or a
-- | constraint abstraction encloses is built at `()`, as a value form.
-- |
-- | **A parameter written as a pattern is a variable the compiler names**, the
-- | pattern checked against the arrow's argument, and the patterns of every
-- | such parameter are matched as one row, from the left, around the body,
-- | inside every abstraction the spine opens.
abstractions :: Surface.Origin -> Boolean -> Boolean -> Expected -> Scope -> Array Parameter -> Expr -> XType -> Surf (XExpr Surface.Origin)
abstractions origin = opened []
  where
  opened matched front quantified expected scope params body ty = case ty, Array.uncons params of
    XForall a k rest, _ | opening -> ETyLam origin a k <$> opened matched front true expected (scope { context = bindTyVar scope.context a k, ambient = XRowEmpty }) params body rest
    XConstrained c rest, _ | opening -> do
      context <- lift (assume (siteAt scope origin) c)
      EConstraintLam origin c <$> opened matched front true expected (scope { context = context, ambient = XRowEmpty }) params body rest
    _, Nothing -> do
      matching <- parametersMatched scope origin matched
      matching.wrap <$>
        if quantified then quantifiedBody matching.scope body expected ty
        else check matching.scope body expected ty
    _, Just { head, tail } -> do
      let at = parameterOrigin head
      parts <- arrow scope at ty
      let
        bound o name more = lambdaAt scope o expected name parts \s -> more s >>= \m -> opened m false false expected s tail body parts.result
        plain o name = bound o name \_ -> pure matched
      case head of
        Named (BinderVar o (LocalVar v)) -> plain o v.name
        Named (BinderWildcard o) -> plain o =<< unnamed "_"
        Named (BinderInvalid o) -> outside (ReportedAlready o)
        Named b -> do
          name <- unnamed "p"
          bound at name \s -> Array.snoc matched <<< { name, typed: _ } <$> pattern s b parts.argument
        Thunk -> plain at =<< unnamed "u"
    where
    opening = front || not (Array.null params)
    unnamed hint = lift (freshIdent (Map.keys scope.context.vars) hint)
  parameterOrigin = case _ of
    Named b -> binderOrigin b
    Thunk -> origin

-- | A `λ` binding the name given at the arrow's argument, its body built by the
-- | action given: under a checking boundary at the arrow's row where the arrow
-- | is written, and under the row as it is otherwise.
lambdaAt :: Scope -> Surface.Origin -> Expected -> Ident -> { argument :: XType, row :: XType, result :: XType } -> (Scope -> Surf (XExpr Surface.Origin)) -> Surf (XExpr Surface.Origin)
lambdaAt scope origin expected name parts body =
  ELam origin name parts.argument parts.row <$> case expected of
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
      ELam _ _ _ _ inner -> maybe false (isValueForm isConstructor) (applies inner)
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
      ExprSelect _ inner _ _ -> go inner
      ExprTuple _ es -> foldMap go es
      ExprRecord _ fields -> foldMap field fields
      ExprTag _ _ _ payload -> foldMap go payload
      ExprLambda _ _ body -> go body
      ExprLet _ bindings body -> foldMap binding bindings <> go body
      ExprCase _ scrutinees alternatives -> foldMap go scrutinees <> foldMap (alternative <<< _.body) alternatives
      ExprHandle _ cells items body -> foldMap (go <<< _.initial) cells <> foldMap item items <> go body
      ExprCellWrite _ _ value -> go value
      _ -> Set.empty
  field = case _ of
    FieldValue _ _ _ e -> go e
    FieldUpdate _ _ _ e -> go e
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
-- |
-- | **A pattern is one node**, whichever of its variables is referred to, one
-- | binding none among them: checked against a type metavariable its
-- | right-hand side's type is equated with, and matched against that side's
-- | value where the block stands. No recursive group binds a pattern.
letBlock :: Scope -> Surface.Origin -> Array LetBinding -> Surf { scope :: Scope, wrap :: XExpr Surface.Origin -> XExpr Surface.Origin }
letBlock scope origin bindings = do
  heads <- traverse head bindings
  let
    inner = scope { context = foldl (\c h -> foldl (\c' v -> bindVar c' v.name v.type) c h.vars) scope.context heads }
    indexOf = Map.fromFoldable (Array.concat (Array.mapWithIndex (\i h -> map (\v -> Tuple v i) h.bindings) heads))
    refers = map (\h -> Set.fromFoldable (Array.mapMaybe (\v -> Map.lookup v indexOf) (Array.fromFoldable (localReferences h.body)))) heads
    grouped = groups refers
  -- a pattern is bound by no recursive group, which would bind some of its
  -- variables before the others
  for_ grouped \g -> when g.recursive do
    for_ (Array.findMap (either Just (const Nothing) <<< _.bound) (Array.mapMaybe (Array.index heads) g.members)) \p ->
      outside (OutsideSubset p.at "a pattern a recursive group binds")
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
          | not (Array.null e.synthesized) -> outside (OutsideSubset v.origin "a local signature taking a synthesized parameter")
          | otherwise -> do
              noteSignature e
              pure { origin: v.origin, bindings: [ l.id ], bound: Right l.name, vars: [ { name: l.name, type: e.type } ], params: v.params, body: v.body, type: e.type, signed: true }
    LetValue v -> let LocalVar l = v.var in named v.origin [ l.id ] l.name v.params v.body
    LetPattern p -> case p.binder of
      BinderVar _ (LocalVar l) -> named p.origin [ l.id ] l.name [] p.body
      BinderWildcard _ -> do
        name <- lift (freshIdent (Map.keys scope.context.vars) "_")
        named p.origin [] name [] p.body
      BinderInvalid o -> outside (ReportedAlready o)
      -- a pattern checked against the type of the value it matches, its
      -- variables at the types it gives them
      b -> do
        ty <- lift (freshTypeMeta scope.context XKType)
        typed <- pattern scope b ty
        pure
          { origin: p.origin
          , bindings: map (\(LocalVar l) -> l.id) (binderVars b)
          , vars: typed.vars
          , bound: Left { at: binderOrigin b, pattern: typed.pattern }
          , params: []
          , body: p.body
          , type: ty
          , signed: false
          }

  named o ids name params body = do
    ty <- lift (freshTypeMeta scope.context XKType)
    pure { origin: o, bindings: ids, bound: Right name, vars: [ { name, type: ty } ], params, body, type: ty, signed: false }

  -- a binding with a signature is checked against it, as a definition is,
  -- under the row its group is elaborated under
  rhs inner h | h.signed = do
    expr <- abstractions h.origin true false Written inner (map Named h.params) h.body h.type
    { head: h, expr, bound: _ } <$> matcher inner h
  rhs inner h = do
    inferred <- case h.params of
      [] -> infer inner h.body
      params -> infer inner (ExprLambda h.origin params h.body)
    lift (equate (siteAt inner h.origin) { kind: XKType, left: inferred.type, right: h.type })
    -- a variable without a signature is bound at a scheme only where an
    -- annotation of its right-hand side writes one, never at one an
    -- application gives where it is not applied
    metas <- lift currentMetas
    unless (annotated h.body) $ for_ h.vars \v -> case substitute metas v.type of
      XForall _ _ _ -> outside (OutsideSubset h.origin "a polymorphic value bound without a signature")
      XConstrained _ _ -> outside (OutsideSubset h.origin "a polymorphic value bound without a signature")
      _ -> pure unit
    { head: h, expr: inferred.expr, bound: _ } <$> matcher inner h

  annotated = case _ of
    ExprTyped _ _ _ -> true
    _ -> false

  matcher inner h = case h.bound of
    Left p -> Left <$> irrefutable inner h.origin [ { pattern: p.pattern, vars: h.vars } ]
    Right name -> pure (Right name)

  -- a pattern matches its right-hand side's value around what follows, and a
  -- recursive group binds names alone
  wrapping g members' = case g.recursive, members' of
    false, [ b ] -> case b.bound of
      Left match -> \e -> match [ b.expr ] e
      Right name -> \e -> ELet b.head.origin name b.head.type b.expr e
    _, members -> \e -> ELetRec (maybe origin _.head.origin (Array.head members)) (Array.mapMaybe (\b -> either (const Nothing) (\name -> Just { name, ty: b.head.type, value: b.expr }) b.bound) members) e

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
        -- the payload is checked against the type the variant expected gives
        -- the tag, where that variant is known to hold it; otherwise the
        -- variant is equated with one holding the tag at a type of its own
        ExprTag o at tag payload -> do
          let key = TagKey tag
          known <- case substitute metas ty of
            XApp (XCon name []) row
              | name == variantTy
              , Right normal <- xnf row
              , Just (XRowTypeEntry _ argument) <- Map.lookup key normal.known ->
                  pure { argument, rest: rebuild normal { known = Map.delete key normal.known } }
            _ -> do
              argument <- lift (freshTypeMeta scope.context XKType)
              rest <- lift (freshTypeMeta scope.context (XKRow RowType))
              lift (equate (siteAt scope at) { kind: XKType, left: variantOf (XRowExtend (XRowTypeEntry key argument) rest), right: ty })
              pure { argument, rest }
          lift (require (siteAt scope at) (XLacks key known.rest))
          value <- case payload of
            Nothing -> check scope (ExprConstructor at unitCtor) Derived known.argument
            Just p -> check scope p expected known.argument
          pure (EVariantInject o key known.rest value)
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
      instantiated scope o (EVar o v.name) (substitute metas ty)
    Nothing -> outside (OutsideSubset o "a variable bound outside what this version elaborates")
  ExprValue o name -> global o name
  ExprConstructor o name -> global o name
  -- a computation is forced, applied to `Prim.Unit` where it is referred to
  ExprComputation o name -> do
    thunk <- global o name
    applyTo scope o o thunk \argument -> subsume scope o { expr: EGlobal o unitCtor [], type: XCon unitTy [] } argument
  ExprLiteral o literal -> pure { expr: ELit o literal, type: fromCore (litType literal) }
  -- an operation is called with the arguments of the whole application at once
  -- `resume` applies the continuation of the `full` clause it stands in
  ExprApp o (ExprResume at) x -> case scope.resume of
    Just k -> applyTo scope at o { expr: EVar at k.name, type: k.type } \argument -> check scope x Derived argument
    Nothing -> outside (OutsideSubset at "`resume` outside the body of a `full` clause")
  ExprApp _ f x -> case operationSpine expr of
    Just call -> operation scope call
    Nothing -> do
      f' <- infer scope f
      applyTo scope (exprOrigin f) (exprOrigin expr) f' \argument -> check scope x Derived argument
  ExprHandle o cells items body
    | Array.null cells -> handling scope o items body
    | otherwise -> cellRegion scope o cells items body
  ExprCellRead o (CellVar c) -> do
    cell <- cellOf scope o c.id
    pure { expr: EReadCell o cell.region cell.key, type: cell.type }
  ExprCellWrite o (CellVar c) value -> do
    cell <- cellOf scope o c.id
    written <- check scope value Derived cell.type
    pure { expr: EWriteCell o cell.region cell.key written, type: XCon unitTy [] }
  ExprOperation o at name label -> operation scope { origin: o, at, name, label, arguments: [] }
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
  -- a tuple is the record of its components at their positions, built from
  -- the left
  ExprTuple o components -> do
    parts <- traverse (infer scope) components
    let indexed = Array.mapWithIndex Tuple parts
    pure
      { expr: foldr (\(Tuple i p) rest -> ERecordExtend o (PositionKey i) p.expr rest) (ERecordEmpty o) indexed
      , type: recordOf (foldr (\(Tuple i p) rest -> XRowExtend (XRowTypeEntry (PositionKey i) p.type) rest) XRowEmpty indexed)
      }
  ExprRecord o fields -> recordLiteral scope o fields
  -- a tag injects its payload, `()` where none is written, into a variant of
  -- that tag at a row the rest lacks it from
  ExprTag o at tag payload -> do
    let key = TagKey tag
    value <- case payload of
      Nothing -> infer scope (ExprConstructor at unitCtor)
      Just p -> infer scope p
    rest <- lift (freshTypeMeta scope.context (XKRow RowType))
    lift (require (siteAt scope at) (XLacks key rest))
    pure { expr: EVariantInject o key rest value.expr, type: variantOf (XRowExtend (XRowTypeEntry key value.type) rest) }
  -- the record has the field at a row the rest of it lacks it from
  ExprSelect o inner at (Symbol label) -> do
    record <- infer scope inner
    let key = SymbolKey (Symbol label)
    field <- lift (freshTypeMeta scope.context XKType)
    rest <- lift (freshTypeMeta scope.context (XKRow RowType))
    lift (equate (siteAt scope at) { kind: XKType, left: record.type, right: recordOf (XRowExtend (XRowTypeEntry key field) rest) })
    lift (require (siteAt scope at) (XLacks key rest))
    pure { expr: ERecordSelect o key record.expr, type: field }
  ExprInvalid o -> outside (ReportedAlready o)
  ExprHole o name -> do
    ty <- lift (freshTypeMeta scope.context XKType)
    { expr: _, type: ty } <$> hole scope o name ty
  ExprCase o scrutinees alternatives -> do
    ty <- lift (freshTypeMeta scope.context XKType)
    { expr: _, type: ty } <$> caseOf scope o scrutinees alternatives Derived ty
  _ -> outside (OutsideSubset (exprOrigin expr) "this form")
  where
  -- each parameter written as a pattern a variable the compiler names, the
  -- patterns matched as one row around the body
  lambda = parameters scope []
  parameters s matched binders body = case Array.uncons binders of
    Nothing -> do
      matching <- parametersMatched s (exprOrigin expr) matched
      inner <- infer matching.scope body
      pure inner { expr = matching.wrap inner.expr }
    Just { head: BinderInvalid o } -> outside (ReportedAlready o)
    Just { head, tail } -> do
      argument <- lift (freshTypeMeta s.context XKType)
      row <- lift (freshTypeMeta s.context (XKRow RowEffect))
      let o = binderOrigin head
      name <- case head of
        BinderVar _ (LocalVar v) -> pure v.name
        BinderWildcard _ -> lift (freshIdent (Map.keys s.context.vars) "_")
        _ -> lift (freshIdent (Map.keys s.context.vars) "p")
      let s' = s { context = bindVar s.context name argument, ambient = row }
      matched' <- case head of
        BinderVar _ _ -> pure matched
        BinderWildcard _ -> pure matched
        _ -> Array.snoc matched <<< { name, typed: _ } <$> pattern s' head argument
      inner <- parameters s' matched' tail body
      pure { expr: ELam o name argument row inner.expr, type: xFunction argument row inner.type }

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
        Just scheme -> do
          kinds <- lift (traverse (\_ -> freshKindMeta scope.context.kindVars (Set.singleton Quantifiable)) scheme.kindVars)
          let
            kindsOf = Map.fromFoldable (Array.zip scheme.kindVars kinds)
            ty = substituteKindVars kindsOf scheme.body
          case Map.lookup name scope.surface.synthesizing of
            Nothing -> instantiated scope o (EGlobal o name kinds) ty
            Just spine -> synthesized o name (substituteKindVars kindsOf <<< fromCore) spine Map.empty (EGlobal o name kinds) ty

  lookupScheme catalog name = case lookupEntry catalog name, Map.lookup name scope.surface.bindings of
    Just entry, _ -> Just entry.scheme
    Nothing, Just (Final scheme) -> Just { kindVars: scheme.kindVars, body: fromCore scheme.body }
    Nothing, _ -> Map.lookup name scope.internal

  -- a global taking a synthesized parameter instantiated along the spine its
  -- interface gives it, which the scheme the catalog holds must be: each
  -- synthesized parameter a goal of the type of the argument it takes, made
  -- where the global stands and filled by the synthesizer named, from the
  -- left. **The synthesized argument is evaluated under the empty row**, the
  -- body of a thunk of no row fitted into the row ambient and applied at
  -- once, so a synthesizer builds it alike wherever the goal stands:
  -- `(openEff [ρ] (λ (_ : Unit) / (). ?m)) Prim.Unit`
  synthesized o name core spine variables e ty = case spine, ty of
    Forall a _ rest, XForall b k body -> do
      m <- lift (instanceAt scope k)
      synthesized o name core rest (Map.insert a m variables) (ETyApp o e m) (substituteTyVars (Map.singleton b m) Map.empty body)
    Constrained _ rest, XConstrained c body -> do
      lift (require (siteAt scope o) c)
      synthesized o name core rest variables (EConstraintApp o e) body
    Synthesized p rest, _
      | Just taking <- asArrow ty
      , taking.row == XRowEmpty
      , taking.argument == written p.argumentType -> do
          Tuple _ goal <- lift (createSynthesis (siteAt scope o) taking.argument p.synthesizer)
          unused <- lift (freshIdent (Map.keys scope.context.vars) "_")
          thunked <- lift (placeFit (siteAt scope o) Wrapping XRowEmpty scope.ambient)
          let evidence = EApp o (EFit o thunked (ELam o unused (XCon unitTy []) XRowEmpty (ETermMeta o goal))) (EGlobal o unitCtor [])
          -- applied as any function is, its pure arrow fitted into the row
          -- ambient
          fit <- lift (placeFit (siteAt scope o) Wrapping taking.row scope.ambient)
          synthesized o name core rest variables (EApp o (EFit o fit e) evidence) taking.result
    Plain t, _ | ty == written t -> pure { expr: e, type: ty }
    Computation result row, _ | ty == written (coreBody (Computation result row)) -> pure { expr: e, type: ty }
    _, _ -> lift (break (SynthesizedSpineAmiss (AtSource { declaration: scope.declaration, origin: o }) name))
    where
    written = substituteTyVars variables Map.empty <<< core

-- | An expression whose type is a `forall` or a constraint at its root,
-- | instantiated where it stands, outermost first: each quantifier at a fresh
-- | metavariable, a row quantifier's an instantiation row, and each constraint
-- | required there, under a constraint application.
instantiated :: Scope -> Surface.Origin -> XExpr Surface.Origin -> XType -> Surf { expr :: XExpr Surface.Origin, type :: XType }
instantiated scope o e = case _ of
  XForall a k rest -> do
    m <- lift (instanceAt scope k)
    instantiated scope o (ETyApp o e m) (substituteTyVars (Map.singleton a m) Map.empty rest)
  XConstrained c rest -> do
    lift (require (siteAt scope o) c)
    instantiated scope o (EConstraintApp o e) rest
  ty -> pure { expr: e, type: ty }

instanceAt :: Scope -> XKind -> Elab XType
instanceAt scope = case _ of
  XKRow RowEffect -> freshInstantiationRow scope.context
  k -> freshTypeMeta scope.context k

-- | An operation referred to where it is written, its name and its label, and
-- | the arguments it is applied to from the left, each with the application
-- | that gives it.
type OperationCall =
  { origin :: Surface.Origin
  , at :: Surface.Origin
  , name :: Qualified Ident
  , label :: Maybe { origin :: Surface.Origin, label :: Symbol }
  , arguments :: Array { origin :: Surface.Origin, argument :: Expr }
  }

-- | An application whose head is an operation.
operationSpine :: Expr -> Maybe OperationCall
operationSpine = go []
  where
  go arguments = case _ of
    ExprApp o f x -> go (Array.cons { origin: o, argument: x } arguments) f
    ExprOperation o at name label -> Just { origin: o, at, name, label, arguments }
    _ -> Nothing

-- | An operation, applied to the arguments given (D17). **Given every argument
-- | it is written with, it is performed where it is applied**: the arguments
-- | are checked from the left against the types it takes, the effect's
-- | parameters and its own variables instantiated afresh, and the row ambient
-- | must hold the element it is performed on, by a demanding fit placed where
-- | its name is written. Several arguments are bound from the right, as an
-- | application evaluates them, and passed as the record of their positions.
-- | The arguments past those are applied to what it resumes with.
-- |
-- | **Given fewer, it is the `λ`s taking every argument and performing it**, at
-- | the type it is called at with the rest of the row an instantiation row,
-- | lacking the element's key where the operation is referred to; the arguments
-- | given are applied to them.
operation :: Scope -> OperationCall -> Surf { expr :: XExpr Surface.Origin, type :: XType }
operation scope call = case Map.lookup call.name scope.surface.operations of
  Nothing -> lift (break (OperationUnknown (AtSource { declaration: scope.declaration, origin: call.at }) call.name))
  Just op -> do
    params <- traverse fresh op.params
    binders <- traverse fresh op.binders
    let
      label = map _.label call.label
      key = operationKey label op
      substitution = Map.fromFoldable (Array.zip (map _.name op.params) params <> Array.zip (map _.name op.binders) binders)
      instantiate = substituteTyVars substitution Map.empty <<< fromCore
      types = map instantiate op.arguments
      arity = Array.length op.arguments
      perform o values = EPerform o key op.name binders case values of
        [ one ] -> one
        _ -> foldr (\(Tuple i v) rest -> ERecordExtend o (PositionKey i) v rest) (ERecordEmpty o) (Array.mapWithIndex Tuple values)
      resumed = instantiate op.resumesWith
    case Array.index call.arguments (arity - 1) of
      Just saturating -> do
        let o = saturating.origin
        values <- traverse (\(Tuple a t) -> check scope a.argument Derived t) (Array.zip call.arguments types)
        _ <- lift (placeFit (siteAt scope call.at) Demanding (instantiate (TRowExtend (operationElement label op) TRowEmpty)) scope.ambient)
        performed <- case values of
          [ _ ] -> pure (perform o values)
          _ -> do
            names <- traverse (\_ -> lift (freshIdent (Map.keys scope.context.vars) "a")) values
            -- the last argument bound outermost, so it is evaluated first
            pure (foldl (\inner (Tuple x (Tuple v t)) -> ELet o x t v inner) (perform o (map (EVar o) names)) (Array.zip names (Array.zip values types)))
        applied o { expr: performed, type: resumed } (Array.drop arity call.arguments)
      Nothing -> do
        let o = call.origin
        rest <- lift (freshInstantiationRow scope.context)
        lift (require (siteAt scope call.at) (XLacks key rest))
        names <- traverse (\_ -> lift (freshIdent (Map.keys scope.context.vars) "a")) types
        let
          -- only the last `λ` performs, on the element over the rest
          rows = Array.snoc (map (const XRowEmpty) (Array.drop 1 types)) (substituteTyVars (Map.insert (operationRest op) rest substitution) Map.empty (fromCore (operationRow label op)))
          lambdas = foldr
            (\(Tuple x (Tuple t row)) inner -> { expr: ELam o x t row inner.expr, type: xFunction t row inner.type })
            { expr: perform o (map (EVar o) names), type: resumed }
            (Array.zip names (Array.zip types rows))
        applied o lambdas call.arguments
  where
  fresh b = lift (freshTypeMeta scope.context (fromCoreKind b.kind))
  applied o f arguments = snd <$> foldM
    (\(Tuple at g) a -> Tuple a.origin <$> applyTo scope at a.origin g \t -> check scope a.argument Derived t)
    (Tuple o f)
    arguments

-- | The items of a handling expression, from the outermost, around its
-- | computation, inside the region of its cells where it declares any
-- | ([Effect Handlers](../../../../../docs/technical-references/02-Surface-Language/02-Effect-Handlers.md)).
-- | **A group is a `handle` of what the items after it make of the
-- | computation**, and a handler written as an item is applied to the thunk of
-- | it, as an application written so is.
handling :: Scope -> Surface.Origin -> Array HandlerItem -> Expr -> Surf { expr :: XExpr Surface.Origin, type :: XType }
handling scope o items computation = case Array.uncons items of
  Nothing -> infer scope computation
  Just { head: HandlerApplied h, tail } -> infer scope (ExprApp o h (ExprLambda o [ BinderWildcard o ] (inner tail)))
  Just { head: HandlerGroup g, tail } -> handlerGroup scope g (inner tail)
  where
  inner tail
    | Array.null tail = computation
    | otherwise = ExprHandle o [] tail computation

-- | A group written in place, handling the computation given. **The element it
-- | handles extends the row ambient where it stands**, which must lack its key:
-- | the effect's parameters at fresh metavariables, decided by what the
-- | computation performs. The computation is inferred under that row, and the
-- | return clause, the identity where none is written, and the operation
-- | clauses under the row ambient; what the return clause gives is the answer.
-- | The clauses stand in the order the effect declares its operations, each
-- | binding the operation's own variables apart and the one argument Core gives
-- | it, matched against the patterns written, one per argument: a `fast` one is
-- | at the type the operation resumes with, and a `full` one at the answer, its
-- | continuation resuming under the row ambient with the answer. A `reifiable
-- | full` one is a `full` one whose continuation is matched, wrapped in
-- | `Continuation`, against the pattern written for it.
handlerGroup :: Scope -> Group -> Expr -> Surf { expr :: XExpr Surface.Origin, type :: XType }
handlerGroup scope g computation = case Map.lookup g.effect scope.surface.effects of
  Nothing -> lift (break (HandledEffectUnknown (AtSource { declaration: scope.declaration, origin: g.head }) g.effect))
  Just effect -> do
    params <- traverse (\b -> lift (freshTypeMeta scope.context (fromCoreKind b.kind))) effect.params
    let
      element = case g.label of
        Just l -> XRowLabelledEffectEntry l g.effect params
        Nothing -> XRowEffectEntry g.effect params
      key = maybe (EffectKey g.effect) SymbolKey g.label
    lift (require (siteAt scope g.head) (XLacks key scope.ambient))
    handled <- infer (scope { ambient = XRowExtend element scope.ambient }) computation
    returned <- case g.body.return of
      Just r -> do
        bound <- binderBound scope r.binder handled.type
        result <- infer bound.scope r.body
        pure { clause: { binder: bound.name, ty: handled.type, body: bound.wrap result.expr }, answer: result.type }
      Nothing -> do
        x <- lift (freshIdent (Map.keys scope.context.vars) "x")
        pure { clause: { binder: x, ty: handled.type, body: EVar g.origin x }, answer: handled.type }
    clauses <- traverse (clauseFor params returned.answer) effect.operations
    pure
      { expr: EHandle g.origin handled.expr { element, returnClause: returned.clause, opClauses: clauses }
      , type: returned.answer
      }
  where
  clauseFor params answer name = case Array.find (\c -> c.operation == name) g.body.operations, Map.lookup name scope.surface.operations of
    Nothing, _ -> lift (break (HandlerClauseMissing (AtSource { declaration: scope.declaration, origin: g.head }) name))
    _, Nothing -> lift (break (OperationUnknown (AtSource { declaration: scope.declaration, origin: g.head }) name))
    Just c, Just op -> do
      variables <- traverse (\b -> lift (freshBinderName (Map.keys scope.context.tyVars) (tyVarText b.name))) op.binders
      let
        binders = Array.zipWith (\b v -> { name: v, kind: fromCoreKind b.kind }) op.binders variables
        instantiate = substituteTyVars (Map.fromFoldable (Array.zip (map _.name op.params) params <> Array.zip (map _.name op.binders) (map XVar variables))) Map.empty <<< fromCore
        argument = instantiate (operationArgument op.arguments)
        resumes = instantiate op.resumesWith
        opened = scope { context = foldl (\ctx b -> bindTyVar ctx b.name b.kind) scope.context binders, resume = Nothing }
      bound <- case c.arguments of
        [ one ] -> binderBound opened one argument
        several -> binderBound opened (BinderTuple c.origin several) argument
      case c.form of
        ClauseFast -> do
          body <- check bound.scope c.body Derived resumes
          pure (XFastClause { op: op.name, tyBinders: binders, argBinder: { name: bound.name, ty: argument }, body: bound.wrap body })
        ClauseFull -> do
          k <- lift (freshIdent (Map.keys bound.scope.context.vars) "k")
          let continuation = xFunction resumes scope.ambient answer
          body <- check (bound.scope { context = bindVar bound.scope.context k continuation, resume = Just { name: k, type: continuation } }) c.body Derived answer
          pure (XFullClause { op: op.name, tyBinders: binders, argBinder: { name: bound.name, ty: argument }, contBinder: { name: k, ty: continuation }, body: bound.wrap body })
        -- the continuation bound as a `full` clause's, and the pattern written
        -- for it matched against it wrapped in `Continuation`
        ClauseReifiable written -> do
          k <- lift (freshIdent (Map.keys bound.scope.context.vars) "k")
          let
            continuation = xFunction resumes scope.ambient answer
            withK = bound.scope { context = bindVar bound.scope.context k continuation }
          -- the constructor instantiated as any global is, and applied as any
          -- function is to the continuation, at the type it takes
          unless (Map.member continuationConstructor scope.internal) do
            lift (break (ContinuationAbsent (AtSource { declaration: scope.declaration, origin: c.origin })))
          constructor <- infer withK (ExprConstructor c.origin continuationConstructor)
          wrapped <- applyTo withK c.origin c.origin constructor \taken -> do
            lift (equate (siteAt withK c.origin) { kind: XKType, left: continuation, right: taken })
            pure (EVar c.origin k)
          kept <- binderBound withK written wrapped.type
          body <- check kept.scope c.body Derived answer
          pure (XFullClause { op: op.name, tyBinders: binders, argBinder: { name: bound.name, ty: argument }, contBinder: { name: k, ty: continuation }, body: bound.wrap (ELet c.origin kept.name wrapped.type wrapped.expr (kept.wrap body)) })

  tyVarText (TyVar v) = v

-- | A handling expression declaring cells: one region around its items, its
-- | initial values evaluated before it in the order declared, under the row
-- | ambient. **Each cell is at the type its initial value has**, whose
-- | metavariables, as the answer's, are created outside the region, so no type
-- | that outlives the region holds it; the items and the computation stand
-- | under the row ambient extended by the region.
cellRegion :: Scope -> Surface.Origin -> Array CellDeclaration -> Array HandlerItem -> Expr -> Surf { expr :: XExpr Surface.Origin, type :: XType }
cellRegion scope o cells items computation = do
  initials <- traverse (\c -> infer scope c.initial) cells
  name <- lift (freshRegionName (Map.keys scope.context.regions) "r")
  answer <- lift (freshTypeMeta scope.context XKType)
  let
    declared = Array.zipWith (\c i -> { binding: bindingOf c.cell, name: nameOf c.cell, key: keyOf c.cell, type: i.type }) cells initials
    inner = scope
      { context = bindRegion scope.context name (Map.fromFoldable (map (\d -> Tuple d.key d.type) declared))
      , ambient = XRowExtend (XRowRegionEntry name) scope.ambient
      , cells = Map.union (Map.fromFoldable (map (\d -> Tuple d.binding { region: name, name: d.name, key: d.key, type: d.type }) declared)) scope.cells
      }
  noteRegion { region: name, boundary: o }
  handled <- handling inner o items computation
  lift (equate (siteAt scope o) { kind: XKType, left: handled.type, right: answer })
  pure { expr: ERegion o name (map (\d -> { key: d.key, ty: d.type }) declared) (map _.expr initials) handled.expr, type: answer }
  where
  bindingOf (CellVar c) = c.id
  nameOf (CellVar c) = c.name
  keyOf (CellVar c) = case c.name of
    Ident n -> SymbolKey (Symbol n)

-- | The cell a reference reaches, the row ambient required to hold its region
-- | by a demanding fit placed where the reference stands.
cellOf :: Scope -> Surface.Origin -> BindingId -> Surf { region :: RegionName, name :: Ident, key :: RowKey, type :: XType }
cellOf scope o binding = case Map.lookup binding scope.cells of
  Nothing -> lift (break (CellUnbound (AtSource { declaration: scope.declaration, origin: o })))
  Just cell -> do
    _ <- lift (placeFit (siteAt scope o) Demanding (XRowExtend (XRowRegionEntry cell.region) XRowEmpty) scope.ambient)
    noteReference { region: cell.region, cell: cell.name, origin: o }
    pure cell

-- | A binder bound at the type given, as a parameter is: a variable by its
-- | name, and anything else by a name the compiler makes, matched against the
-- | pattern around the body the binding encloses.
binderBound :: Scope -> Binder -> XType -> Surf { name :: Ident, scope :: Scope, wrap :: XExpr Surface.Origin -> XExpr Surface.Origin }
binderBound scope binder ty = case binder of
  BinderVar _ (LocalVar v) -> pure { name: v.name, scope: scope { context = bindVar scope.context v.name ty }, wrap: identity }
  BinderInvalid o -> outside (ReportedAlready o)
  BinderWildcard _ -> do
    name <- lift (freshIdent (Map.keys scope.context.vars) "_")
    pure { name, scope: scope { context = bindVar scope.context name ty }, wrap: identity }
  _ -> do
    name <- lift (freshIdent (Map.keys scope.context.vars) "p")
    let bound = scope { context = bindVar scope.context name ty }
    typed <- pattern bound binder ty
    matching <- parametersMatched bound (binderOrigin binder) [ { name, typed } ]
    pure { name, scope: matching.scope, wrap: matching.wrap }

-- | A record literal, inferred. An extension `k: e` adds a field the record
-- | lacks, and a replacement `k = e` replaces one of the record spread, at a
-- | type of its own; the replacements stand inside, nearest the record spread,
-- | and the extensions outside, each outermost first in the order written. A
-- | field the record must lack, or have, is required where its label stands.
-- |
-- | **The fields are evaluated from the left, and the record spread last.** An
-- | extension evaluates its value before the record it extends and a
-- | replacement after, so where a replacement is written each field's value is
-- | bound by a `let` first, in the order written.
recordLiteral :: Scope -> Surface.Origin -> Array RecordField -> Surf { expr :: XExpr Surface.Origin, type :: XType }
recordLiteral scope origin fields = do
  written <- traverse (\f -> f { value = _ } <$> infer scope f.value) (Array.mapMaybe field fields)
  let replacing = Array.any _.replaces written
  named <- traverse (\f -> f { name = _ } <$> if replacing then Just <$> lift (freshIdent (Map.keys scope.context.vars) "v") else pure Nothing) written
  base <- case Array.findMap spread fields of
    Nothing -> pure { expr: ERecordEmpty origin, row: XRowEmpty }
    Just s -> do
      spreading <- infer scope s.expr
      row <- lift (freshTypeMeta scope.context (XKRow RowType))
      lift (equate (siteAt scope s.at) { kind: XKType, left: spreading.type, right: recordOf row })
      pure { expr: spreading.expr, row }
  replaced <- foldM replace base (Array.reverse (Array.filter _.replaces named))
  extended <- foldM extend replaced (Array.reverse (Array.filter (not <<< _.replaces) named))
  let bound = Array.mapMaybe (\f -> f.name <#> \name -> { at: f.at, name, value: f.value }) named
  pure
    { expr: foldr (\b e -> ELet b.at b.name b.value.type b.value.expr e) extended.expr bound
    , type: recordOf extended.row
    }
  where
  field = case _ of
    FieldValue at labelAt label value -> Just { at, labelAt, key: SymbolKey label, replaces: false, value, name: Nothing }
    FieldUpdate at labelAt label value -> Just { at, labelAt, key: SymbolKey label, replaces: true, value, name: Nothing }
    FieldSpread _ _ -> Nothing

  spread = case _ of
    FieldSpread at expr -> Just { at, expr }
    _ -> Nothing

  -- a field's value, or the variable it is bound to
  valueOf f = maybe f.value.expr (EVar f.at) f.name

  -- the record has the field at a type of its own, at a row the rest of it
  -- lacks it from
  replace record f = do
    old <- lift (freshTypeMeta scope.context XKType)
    rest <- lift (freshTypeMeta scope.context (XKRow RowType))
    lift (equate (siteAt scope f.labelAt) { kind: XKType, left: recordOf record.row, right: recordOf (XRowExtend (XRowTypeEntry f.key old) rest) })
    lift (require (siteAt scope f.labelAt) (XLacks f.key rest))
    pure { expr: ERecordUpdate f.at f.key record.expr (valueOf f), row: XRowExtend (XRowTypeEntry f.key f.value.type) rest }

  extend record f = do
    lift (require (siteAt scope f.labelAt) (XLacks f.key record.row))
    pure { expr: ERecordExtend f.at f.key (valueOf f) record.expr, row: XRowExtend (XRowTypeEntry f.key f.value.type) record.row }

-- | `Prim.Record` of the row given.
recordOf :: XType -> XType
recordOf row = XApp (XCon recordTy []) row

-- | `Prim.Variant` of the row given.
variantOf :: XType -> XType
variantOf row = XApp (XCon variantTy []) row

-- | A pattern as typed, read for the compiler of matches against the
-- | metavariables as they stand once its match is typed, and the variables it
-- | binds, each at its type, in the order written.
type TypedPattern = { pattern :: MetaContext -> Match.Pattern XType Surface.Origin, vars :: Array { name :: Ident, type :: XType } }

-- | The tags of a variant type, zonked: each known tag, in the order of its
-- | key, with the type of its payload, and what its row holds besides them. A
-- | rigid variable may stand for any other tag, and so may a metavariable of a
-- | level outside the one given, which the match leaves as it is; the
-- | metavariables of that level may be closed for the match's sake, and a row
-- | holding none of these holds nothing more.
tagsOf :: Int -> MetaContext -> XType -> Match.Tags XType
tagsOf level metas ty = case substitute metas ty of
  XApp (XCon name []) row
    | name == variantTy
    , Right normal <- xnf row ->
        let
          flexible = Set.toUnfoldable normal.flexible
        in
          { keys: Array.mapMaybe tag (Map.toUnfoldable normal.known)
          , tail:
              if not (Set.isEmpty normal.rigid) then Match.Rigid
              else if Array.any ofOuterLevel flexible then Match.External
              else if not (Array.null flexible) then Match.Flexible (map XMeta flexible)
              else Match.Closed
          }
  _ -> { keys: [], tail: Match.External }
  where
  ofOuterLevel m = case lookupMeta metas m of
    Just (Unsolved info) -> info.level < level
    _ -> false
  tag (Tuple key entry) = case entry of
    XRowTypeEntry _ payload -> Just { key, payload }
    _ -> Nothing

-- | A function inferred where it stands, applied to the argument built at the
-- | type it takes, and fitted there into the row ambient: the function's place,
-- | then the application's. **A function whose type is a `forall` or a
-- | constraint is instantiated where it is applied**, as a global is where it
-- | is referred to: a handler a field holds, or one an application gives.
applyTo :: Scope -> Surface.Origin -> Surface.Origin -> { expr :: XExpr Surface.Origin, type :: XType } -> (XType -> Surf (XExpr Surface.Origin)) -> Surf { expr :: XExpr Surface.Origin, type :: XType }
applyTo scope at whole function argument = do
  metas <- lift currentMetas
  f <- instantiated scope at function.expr (substitute metas function.type)
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
-- | **A guard block is an expression of its own**: a binding a `let`, a guard
-- | a `case` of no scrutinee dispatching on its condition, and where every
-- | guard fails a jump to the alternative's fall-through point, a join point
-- | matching the alternatives after it afresh. Where a block may fall through,
-- | the scrutinees are bound to variables first, in order, so that a
-- | fall-through point matches the same values again. A fall-through point
-- | nothing can reach — of an alternative no leaf takes, or after a guard that
-- | always succeeds — jumps to itself, and never runs.
-- |
-- | **No body is copied.** An alternative one leaf takes stands in that leaf;
-- | any other, one no leaf takes among them, is a join point around the `case`
-- | whose parameters are the variables its patterns bind, each leaf binding
-- | them and jumping to it. The join points of alternatives with no guard block
-- | stand outermost, then, from the last alternative to the first, each
-- | fall-through point and the join point of its block, each reaching only
-- | those around it. A match leaving values uncovered is noted with a vector of
-- | values it does not match, and each place it leaves uncovered stands in the
-- | tree under the number of that note.
-- |
-- | **A match on a variant whose row its declaration may yet close for it is
-- | left pending**: a node stands where the `case` does, numbered as the record
-- | noted of it, and the match is built once the declaration is settled, the
-- | rows it may close closed first.
caseOf :: Scope -> Surface.Origin -> Array Expr -> Array Alternative -> Expected -> XType -> Surf (XExpr Surface.Origin)
caseOf scope origin scrutinees alternatives expected result = do
  inferred <- traverse (infer scope) scrutinees
  typed <- traverse (alternative (map _.type inferred)) (Array.mapWithIndex Tuple alternatives)
  table <- constructorTable
  metas <- lift currentMetas
  let
    width = Array.length scrutinees
    rowsAt ms = map (\r -> r { patterns = map (_ $ ms) r.patterns }) (Array.concatMap _.rows typed)
    closableAt ms = Match.closable <$> Match.compile table width (rowsAt ms)
  case closableAt metas of
    Left _ -> malformed
    Right [] -> assembled table width inferred typed (rowsAt metas)
    -- a variant whose row may yet be closed for the match's sake leaves the
    -- match to be built once its declaration is settled
    Right _ -> do
      id <- lift freshPendingCase
      notePending { id, site: siteAt scope origin, closable: closableAt, assembled: \ms -> assembled table width inferred typed (rowsAt ms) }
      pure (EPendingCase origin id)
  where
  assembled table width inferred typed rows = do
    compiled <- matched (Match.compile table width rows)
    found <- matched (Match.witness table width rows)
    uncovered <- case found, uncovers compiled.plan || Array.any uncovers (Array.fromFoldable (Map.values compiled.falls)) of
      Just witness, true -> do
        id <- lift freshCoverage
        noteUncovered { id, origin, witness }
        pure (Just id)
      Nothing, false -> pure Nothing
      _, _ -> malformed
    placed <- traverse (place compiled.references) typed
    -- the scrutinees bound to variables where a fall-through point matches them
    -- again
    bound <-
      if Array.any (isJust <<< _.fall) typed then traverse (\s -> { scrutinee: s, name: _ } <$> lift (freshIdent (Map.keys scope.context.vars) "s")) inferred
      else pure []
    let
      matchedValues = if Array.null bound then map _.expr inferred else map (\b -> EVar origin b.name) bound
      fallsThrough p = case p.alternative.fall of
        Just j -> do
          body <- case Map.lookup p.alternative.index compiled.falls of
            Just plan -> ECase origin matchedValues <$> built uncovered placed plan
            Nothing -> pure (EJump origin j [])
          pure [ \e -> ELetJoin origin j [] result body e ]
        Nothing -> pure []
    tree <- built uncovered placed compiled.plan
    falls <- traverse (\p -> (_ <> joined p) <$> fallsThrough p) (Array.reverse (Array.filter _.alternative.guarded placed))
    let
      wraps = Array.concatMap joined (Array.filter (not <<< _.alternative.guarded) placed) <> Array.concat falls
      matching = foldr (\w e -> w e) (ECase origin matchedValues tree) wraps
    pure (foldr (\b e -> ELet origin b.name b.scrutinee.type b.scrutinee.expr e) matching bound)

  -- an alternative's rows, one per choice written at its top, the variables
  -- they bind, its body, and the fall-through point of its guard block where
  -- the block may fall through
  alternative types (Tuple index alt) = do
    rows <- traverse (\written -> traverse (\(Tuple b t) -> pattern scope b t) (Array.zip written types)) alt.patterns
    let
      vars = Array.concatMap _.vars (Array.concat rows)
      several = Array.length alt.patterns > 1
      choice written = case Array.head written, Array.last written of
        Just first, Just last | several -> Just (Surface.spanning (binderOrigin first) (binderOrigin last))
        _, _ -> Nothing
      inner = withVars scope vars
      rowsOf fallible = Array.zipWith (\written typedRow -> { alternative: index, choice: choice written, patterns: map _.pattern typedRow, fallible }) alt.patterns rows
    case alt.body of
      Unconditional body -> do
        body' <- check inner body expected result
        pure { index, vars, body: body', rows: rowsOf false, guarded: false, fall: Nothing }
      Guarded lines -> do
        fall <- if fallsAtEnd lines then Just <$> lift (freshJoin Set.empty "fall") else pure Nothing
        body' <- block inner lines fall
        pure { index, vars, body: body', rows: rowsOf (not (Array.any total lines)), guarded: true, fall }

  -- a guard block's lines from the one given: a binding a `let` over the
  -- lines after it, a guard a dispatch on its condition, the lines after it
  -- where it fails, and a jump to the fall-through point past the last
  block inner lines fall = case Array.uncons lines of
    Nothing -> case fall of
      Just j -> pure (EJump origin j [])
      Nothing -> malformed
    Just { head: line, tail } -> case line of
      GuardBinding o b e -> do
        let
          named name = do
            value <- infer inner e
            rest <- block (inner { context = bindVar inner.context name value.type }) tail fall
            pure (ELet o name value.type value.expr rest)
        case b of
          BinderVar _ (LocalVar v) -> named v.name
          BinderWildcard _ -> named =<< lift (freshIdent (Map.keys inner.context.vars) "_")
          BinderInvalid at -> outside (ReportedAlready at)
          -- a pattern matches the value around the lines after it
          _ -> do
            value <- infer inner e
            typed <- pattern inner b value.type
            match <- irrefutable inner o [ typed ]
            rest <- block (withVars inner typed.vars) tail fall
            pure (match [ value.expr ] rest)
      GuardWhen o condition body
        | Array.null tail && total line -> check inner body expected result
        | otherwise -> do
            condition' <- check inner condition Derived (XCon booleanTy [])
            guarded o condition' body tail
      GuardOtherwise o body
        | Array.null tail -> check inner body expected result
        | otherwise -> guarded o (ELit o (LitBoolean true)) body tail
    where
    guarded o condition body tail = do
      body' <- check inner body expected result
      rest <- block inner tail fall
      pure (ECase o [] (XGuard condition (XLeaf body') (XLeaf rest)))

  -- whether a guard always succeeds: `otherwise`, and the literal `true`
  total = case _ of
    GuardOtherwise _ _ -> true
    GuardWhen _ (ExprLiteral _ (LitBoolean true)) _ -> true
    _ -> false

  -- whether control can reach past a block's last line: it is no guard that
  -- always succeeds
  fallsAtEnd lines = maybe true (not <<< total) (Array.last lines)

  place counts t = case Map.lookup t.index counts of
    Just 1 -> pure { alternative: t, join: Nothing }
    _ -> do
      j <- lift (freshJoin Set.empty "alt")
      pure { alternative: t, join: Just j }

  built uncovered placed = case _ of
    Match.Leaf i bindings -> case Array.find (\p -> p.alternative.index == i) placed of
      Just p -> (_ $ leafOf p) <$> boundAround scope origin p.alternative.vars bindings
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
    Match.SwitchKey o _ branches fallback ->
      XSwitchKey o
        <$> traverse (\b -> { key: b.key, tree: _ } <$> built uncovered placed b.plan) branches
        <*> traverse (built uncovered placed) fallback

  leafOf p = case p.join of
    Nothing -> p.alternative.body
    Just j -> EJump origin j (map (\v -> EVar origin v.name) p.alternative.vars)

  joined p = case p.join of
    Nothing -> []
    Just j -> [ \e -> ELetJoin origin j (map (\v -> { name: v.name, ty: v.type }) p.alternative.vars) result p.alternative.body e ]

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
    Match.SwitchKey _ _ branches fallback -> Array.any (uncovers <<< _.plan) branches || maybe false uncovers fallback

-- | Note a `case` left pending.
notePending :: PendingCase -> Surf Unit
notePending p = Surf (pure (Right { value: unit, holes: [], wildcards: [], unwritten: [], expressionHoles: [], uncovered: [], pending: [ p ], regions: [], references: [] }))

-- | Note a region a handling expression declaring cells opens.
noteRegion :: CellRegion -> Surf Unit
noteRegion r = Surf (pure (Right { value: unit, holes: [], wildcards: [], unwritten: [], expressionHoles: [], uncovered: [], pending: [], regions: [ r ], references: [] }))

-- | Note a reference to a cell.
noteReference :: CellReference -> Surf Unit
noteReference r = Surf (pure (Right { value: unit, holes: [], wildcards: [], unwritten: [], expressionHoles: [], uncovered: [], pending: [], regions: [], references: [ r ] }))

-- | Note a match that leaves values uncovered.
noteUncovered :: UncoveredMatch -> Surf Unit
noteUncovered m = Surf (pure (Right { value: unit, holes: [], wildcards: [], unwritten: [], expressionHoles: [], uncovered: [ m ], pending: [], regions: [], references: [] }))

-- | A pattern checked against the type of the value it matches, as the
-- | compiler of matches reads it, and the variables it binds, each at its
-- | type, in the order written. A constructor is instantiated as a reference
-- | to it is, its fields read off its arrows and what it builds equated with
-- | the type given; a literal's type is equated with it, and so is an
-- | annotation's. A tuple is the record of its components at their positions,
-- | closed. A record pattern takes each key it writes, in the order written,
-- | from the row of the record, which the rest of the row lacks it from, where
-- | its label stands; the row left is empty where the pattern is closed, and
-- | its rest's where it binds one. A tag pattern takes its tag from the row of
-- | the variant, which the rest lacks it from, where it stands; a tag written
-- | with no payload matches `()`.
-- |
-- | **The pattern is read once every pattern of its match is typed**: a tag
-- | pattern carries the tags its variant holds, which the patterns of the rows
-- | after it may add to, so what the compiler of matches is given is read off
-- | the metavariables as they then stand.
pattern :: Scope -> Binder -> XType -> Surf TypedPattern
pattern scope binder ty = case binder of
  BinderWildcard _ -> pure { pattern: const Match.PAny, vars: [] }
  BinderVar _ (LocalVar v) -> pure { pattern: const (Match.PVar v.name), vars: [ { name: v.name, type: ty } ] }
  BinderAs _ (LocalVar v) inner -> do
    p <- pattern scope inner ty
    pure { pattern: Match.PAs v.name <<< p.pattern, vars: Array.cons { name: v.name, type: ty } p.vars }
  BinderConstructor o name args -> do
    constructor <- infer scope (ExprConstructor o name)
    fields <- fieldsOf o (Array.length args) constructor.type
    lift (equate (siteAt scope o) { kind: XKType, left: fields.result, right: ty })
    parts <- traverse (\(Tuple b t) -> pattern scope b t) (Array.zip args fields.arguments)
    pure { pattern: \metas -> Match.PCtor name (map (\p -> p.pattern metas) parts), vars: Array.concatMap _.vars parts }
  BinderLiteral o literal -> do
    lift (equate (siteAt scope o) { kind: XKType, left: fromCore (litType literal), right: ty })
    pure { pattern: const (Match.PLit literal), vars: [] }
  BinderOr _ choices -> do
    parts <- traverse (\b -> pattern scope b ty) choices
    pure
      { pattern: \metas -> Match.POr (Array.zipWith (\b p -> { label: binderOrigin b, pattern: p.pattern metas }) choices parts)
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
  BinderTag _ at tag payload -> do
    let key = TagKey tag
    argument <- lift (freshTypeMeta scope.context XKType)
    rest <- lift (freshTypeMeta scope.context (XKRow RowType))
    let whole = variantOf (XRowExtend (XRowTypeEntry key argument) rest)
    lift (equate (siteAt scope at) { kind: XKType, left: whole, right: ty })
    lift (require (siteAt scope at) (XLacks key rest))
    inner <- pattern scope (fromMaybe (BinderConstructor at unitCtor []) payload) argument
    level <- lift currentLevel
    pure { pattern: \metas -> Match.PTag { key, payload: inner.pattern metas, domain: tagsOf level metas whole }, vars: inner.vars }
  BinderTuple o components -> do
    types <- traverse (\_ -> lift (freshTypeMeta scope.context XKType)) components
    let indexed = Array.mapWithIndex Tuple types
    lift (equate (siteAt scope o) { kind: XKType, left: recordOf (foldr (\(Tuple i t) rest -> XRowExtend (XRowTypeEntry (PositionKey i) t) rest) XRowEmpty indexed), right: ty })
    parts <- traverse (\(Tuple b t) -> pattern scope b t) (Array.zip components types)
    pure
      { pattern: \metas -> Match.PRecord { fields: Array.mapWithIndex (\i p -> { key: PositionKey i, pattern: p.pattern metas }) parts, rest: Nothing, open: false }
      , vars: Array.concatMap _.vars parts
      }
  BinderRecord o fields rest -> do
    whole <- lift (freshTypeMeta scope.context (XKRow RowType))
    lift (equate (siteAt scope o) { kind: XKType, left: recordOf whole, right: ty })
    taken <- foldM field { row: whole, parts: [] } fields
    case rest of
      Nothing -> lift (equate (siteAt scope o) { kind: XKType, left: recordOf taken.row, right: recordOf XRowEmpty })
      Just _ -> pure unit
    let restVar = foldMap (\(LocalVar v) -> [ { name: v.name, type: recordOf taken.row } ]) (rest >>= _.var)
    pure
      { pattern: \metas -> Match.PRecord
          { fields: map (\p -> { key: p.key, pattern: p.typed.pattern metas }) taken.parts
          , rest: map (\(LocalVar v) -> v.name) (rest >>= _.var)
          , open: isJust rest
          }
      , vars: Array.concatMap _.typed.vars taken.parts <> restVar
      }
  BinderInvalid o -> outside (ReportedAlready o)
  where
  -- a field of a record pattern takes its key from the row it is matched
  -- against, which the rest lacks it from, where its label stands
  field acc f = do
    let key = SymbolKey f.label
    payload <- lift (freshTypeMeta scope.context XKType)
    next <- lift (freshTypeMeta scope.context (XKRow RowType))
    lift (equate (siteAt scope f.labelOrigin) { kind: XKType, left: recordOf acc.row, right: recordOf (XRowExtend (XRowTypeEntry key payload) next) })
    lift (require (siteAt scope f.labelOrigin) (XLacks key next))
    typed <- pattern scope f.binder payload
    pure { row: next, parts: Array.snoc acc.parts { key, typed } }

  -- the argument of each of a constructor's arrows, one per field, and what
  -- is left
  fieldsOf o n t
    | n <= 0 = pure { arguments: [], result: t }
    | otherwise = do
        parts <- arrow scope o t
        rest <- fieldsOf o (n - 1) parts.result
        pure (rest { arguments = Array.cons parts.argument rest.arguments })

-- | Patterns that always match, compiled as the one row of a match: what
-- | matches the values given against them around the body given, binding the
-- | variables they bind. Name resolution admits none here that can fail, so
-- | the tree leaves no value uncovered and takes the body at one leaf.
irrefutable
  :: Scope
  -> Surface.Origin
  -> Array TypedPattern
  -> Surf (Array (XExpr Surface.Origin) -> XExpr Surface.Origin -> XExpr Surface.Origin)
irrefutable scope origin typed = do
  table <- constructorTable
  metas <- lift currentMetas
  case Match.compile table (Array.length typed) [ { alternative: 0, choice: Nothing, patterns: map (\t -> t.pattern metas) typed, fallible: false } ] of
    Right compiled
      | Map.lookup 0 compiled.references == Just 1
      , [ bindings ] <- leafBindings compiled.plan -> do
          leaf <- boundAround scope origin (Array.concatMap _.vars typed) bindings
          case planted leaf compiled.plan of
            Just tree -> pure \values body -> ECase origin values (tree body)
            Nothing -> malformed
    _ -> malformed
  where
  malformed :: forall x. Surf x
  malformed = lift (break (MatchMalformed (AtSource { declaration: scope.declaration, origin })))

  leafBindings = case _ of
    Match.Leaf _ bindings -> [ bindings ]
    Match.Uncovered -> []
    Match.SwitchCtor _ branches fallback -> Array.concatMap (leafBindings <<< _.plan) branches <> foldMap leafBindings fallback
    Match.SwitchLit _ branches fallback -> Array.concatMap (leafBindings <<< _.plan) branches <> leafBindings fallback
    Match.SwitchKey _ _ branches fallback -> Array.concatMap (leafBindings <<< _.plan) branches <> foldMap leafBindings fallback

  planted leaf = case _ of
    Match.Leaf _ _ -> Just leaf
    Match.Uncovered -> Nothing
    Match.SwitchCtor o branches fallback -> do
      branches' <- traverse (\b -> { ctor: b.ctor, tree: _ } <$> planted leaf b.plan) branches
      fallback' <- traverse (planted leaf) fallback
      pure \body -> XSwitchCtor o (map (\b -> { ctor: b.ctor, tree: b.tree body }) branches') (map (_ $ body) fallback')
    Match.SwitchLit o branches fallback -> do
      branches' <- traverse (\b -> { lit: b.lit, tree: _ } <$> planted leaf b.plan) branches
      fallback' <- planted leaf fallback
      pure \body -> XSwitchLit o (map (\b -> { lit: b.lit, tree: b.tree body }) branches') (fallback' body)
    Match.SwitchKey o _ branches fallback -> do
      branches' <- traverse (\b -> { key: b.key, tree: _ } <$> planted leaf b.plan) branches
      fallback' <- traverse (planted leaf) fallback
      pure \body -> XSwitchKey o (map (\b -> { key: b.key, tree: b.tree body }) branches') (map (_ $ body) fallback')

-- | A leaf binding what its patterns bind around the expression given: each
-- | variable at its occurrence, and, by a `let` around the expression, from
-- | the value bound at its occurrence under a name the compiler makes, the
-- | rest of a record pattern, the keys the pattern writes restricted in the
-- | order written, and a variant a default holds without the tags its
-- | dispatches took, widened by them from the last taken to the first. The
-- | variables given are those of the row, at their types.
boundAround
  :: Scope
  -> Surface.Origin
  -> Array { name :: Ident, type :: XType }
  -> Array (Match.Binding XType)
  -> Surf (XExpr Surface.Origin -> XDecisionTree Surface.Origin)
boundAround scope origin vars bindings = do
  steps <- traverse step bindings
  pure \body -> foldr (\s t -> XBind s.bound s.occurrence t) (XLeaf (foldr _.around body steps)) steps
  where
  step b = case b.transform of
    Match.Identity -> pure { bound: b.name, occurrence: b.occurrence, around: identity }
    Match.Restrict keys -> made b "r" \value -> foldl (\e k -> ERecordRestrict origin k e) value keys
    Match.Weaken taken -> made b "v" \value -> foldr (\k e -> EVariantWeaken origin k.key k.payload e) value taken

  made b hint transform = case Array.find (\v -> v.name == b.name) vars of
    Just v -> do
      value <- lift (freshIdent (Map.keys scope.context.vars) hint)
      pure { bound: value, occurrence: b.occurrence, around: ELet origin b.name v.type (transform (EVar origin value)) }
    Nothing -> lift (break (MatchMalformed (AtSource { declaration: scope.declaration, origin })))

-- | The parameters written as patterns, each a variable the compiler named,
-- | matched as one row: the scope the variables they bind are in, and what
-- | matches them around a body.
parametersMatched
  :: Scope
  -> Surface.Origin
  -> Array { name :: Ident, typed :: TypedPattern }
  -> Surf { scope :: Scope, wrap :: XExpr Surface.Origin -> XExpr Surface.Origin }
parametersMatched scope origin matched
  | Array.null matched = pure { scope, wrap: identity }
  | otherwise = do
      match <- irrefutable scope origin (map _.typed matched)
      pure
        { scope: withVars scope (Array.concatMap _.typed.vars matched)
        , wrap: match (map (\m -> EVar origin m.name) matched)
        }

-- | The scope given with the variables given bound, in order.
withVars :: Scope -> Array { name :: Ident, type :: XType } -> Scope
withVars scope vars = scope { context = foldl (\c v -> bindVar c v.name v.type) scope.context vars }

-- | Every constructor the session knows, as the compiler of matches reads it.
constructorTable :: Surf Match.Constructors
constructorTable = lift askEnv <#> \env -> map (\c -> { owner: c.owner, tag: c.tag, arity: Array.length c.fields }) env.session.constructors

-- | The variables a pattern binds, in the order written.
binderVars :: Binder -> Array LocalVar
binderVars = case _ of
  BinderVar _ v -> [ v ]
  BinderAs _ v inner -> Array.cons v (binderVars inner)
  BinderConstructor _ _ args -> Array.concatMap binderVars args
  BinderTag _ _ _ payload -> foldMap binderVars payload
  BinderTuple _ parts -> Array.concatMap binderVars parts
  BinderRecord _ fields rest -> Array.concatMap (binderVars <<< _.binder) fields <> foldMap (Array.fromFoldable <<< _.var) rest
  BinderOr _ _ -> []
  BinderTyped _ inner _ -> binderVars inner
  BinderWildcard _ -> []
  BinderLiteral _ _ -> []
  BinderInvalid _ -> []

binderOrigin :: Binder -> Surface.Origin
binderOrigin = case _ of
  BinderWildcard o -> o
  BinderVar o _ -> o
  BinderAs o _ _ -> o
  BinderConstructor o _ _ -> o
  BinderTag o _ _ _ -> o
  BinderLiteral o _ -> o
  BinderTuple o _ -> o
  BinderRecord o _ _ -> o
  BinderOr o _ -> o
  BinderTyped o _ _ -> o
  BinderInvalid o -> o
