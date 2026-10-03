-- | What resolving the inside of a module's declarations runs in: the module's
-- | context, the bindings in scope where it stands, a supply of binding
-- | numbers, and the errors and warnings it reports.
-- |
-- | Every problem found is reported, with where it stands, and resolution goes
-- | on past it: what an error leaves in the Surface AST is an invalid node of
-- | the class it stands in
-- | ([Surface AST](../../../../docs/technical-references/02-Surface-Language/08-Surface-AST.md)).
module Stella.Compiler.Resolve.Monad
  ( Resolve
  , Context
  , Constructor
  , Env
  , ResolveError(..)
  , ResolveReason(..)
  , ResolveWarning(..)
  , printResolveReason
  , printResolveWarning
  , contextOf
  , runResolve
  , context
  , typeVariable
  , typeVariables
  , withTypeVariables
  , localValue
  , withValues
  , valueInScope
  , constructorOf
  , freshBinding
  , report
  , warn
  , Found(..)
  , lookupType
  , lookupTypeOperator
  , lookupValue
  , TypeReference(..)
  , TypeOperatorFixity
  ) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldl)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, isJust)
import Data.Set (Set)
import Data.Set as Set
import Data.Tuple (Tuple(..))
import Stella.Compiler.CST.Types (Decl(..), Fixity(..), Name, SourceRange)
import Stella.Compiler.Interface.Environment (BuildEnvironment, ModuleView, viewFor)
import Stella.Compiler.Interface.Environment as Environment
import Stella.Compiler.Interface.Module (Export, TypeEntity(..), TypeExport, TypeSort(..), ValueSort(..))
import Stella.Compiler.Resolve.Group (Declaration(..), GroupedModule)
import Stella.Compiler.Resolve.Scope (Names, Scope, ScopedModule)
import Stella.Compiler.Surface.Decl (Associativity(..))
import Stella.Compiler.Surface.Name (BindingId(..), LocalVar(..), OperatorName(..), TypeVar(..))
import Stella.Compiler.Surface.Type (TypeOperatorTarget(..))
import Stella.Compiler.TypedCore.Name (EffName, Ident(..), ModuleName, Qualified(..), TyName(..), TyVar(..))

-- | What resolving a module's declarations reads of the module as a whole:
-- | its scope, the build environment as the module sees it, which of its own
-- | type names are synonyms, the fixity of each type operator it declares,
-- | and each constructor it declares, under the identity it is declared with.
type Context =
  { module :: ModuleName
  , scope :: Scope
  , view :: Maybe ModuleView
  , ownSynonyms :: Set String
  , ownTypeOperators :: Map String { associativity :: Associativity, precedence :: Int, target :: Name }
  , ownConstructors :: Map Ident Constructor
  }

-- | What a pattern needs of a constructor: how many fields it has, and how many
-- | constructors its type has.
type Constructor = { arity :: Int, siblings :: Int }

-- | Where resolution stands: the module's context, and the type variables and
-- | local values in scope, by the name they are written with.
type Env =
  { context :: Context
  , typeVariables :: Map String TypeVar
  , values :: Map String LocalVar
  }

type State =
  { next :: Int
  , errors :: Array ResolveError
  , warnings :: Array ResolveWarning
  }

newtype Resolve a = Resolve (Env -> State -> Tuple a State)

instance Functor Resolve where
  map f (Resolve r) = Resolve \e s -> case r e s of
    Tuple a s' -> Tuple (f a) s'

instance Apply Resolve where
  apply (Resolve rf) (Resolve ra) = Resolve \e s -> case rf e s of
    Tuple f s' -> case ra e s' of
      Tuple a s'' -> Tuple (f a) s''

instance Applicative Resolve where
  pure a = Resolve \_ s -> Tuple a s

instance Bind Resolve where
  bind (Resolve r) k = Resolve \e s -> case r e s of
    Tuple a s' -> case k a of
      Resolve r' -> r' e s'

instance Monad Resolve

data ResolveError = ResolveError SourceRange ResolveReason

data ResolveReason
  -- | A name of the type namespace nothing in scope stands for.
  = UnknownType String
  -- | A name of the type namespace several entities in scope stand for.
  | AmbiguousType String
  -- | A type operator nothing in scope stands for.
  | UnknownTypeOperator String
  | AmbiguousTypeOperator String
  -- | A type variable no binder in scope binds, where nothing quantifies one
  -- | implicitly.
  | UnknownTypeVariable String
  -- | A value nothing in scope stands for, the synthesizer after `by` among
  -- | them.
  | UnknownValue String
  | AmbiguousValue String
  -- | Two operators of one precedence that associate differently, or a
  -- | non-associative operator beside another of its precedence: the second
  -- | operator, and the first.
  | OperatorsUnordered String String
  -- | A word in a kind other than `Type`, `Effect`, and `Row`, or `Row` applied
  -- | to anything but `Type` or `Effect`.
  | KindMalformed
  -- | A name bound twice by one group of binders.
  | BoundTwice String
  -- | A name standing for an effect anywhere but at the head of an effect
  -- | application in an effect row or a capability signature.
  | EffectNotType String
  -- | An element of an effect row, or the source or a target of `~>`, that is
  -- | not an effect applied to its arguments.
  | EffectExpected
  -- | A row item the bracket it stands in does not admit.
  | RowItemMisplaced
  -- | `{{ … }}` off the spine of a signature.
  | SynthesizedMisplaced
  -- | `E ~> ρ` anywhere but at the end of the quantifiers of a handler
  -- | declaration's signature.
  | CapabilityMisplaced
  -- | A target of `~>` that is not an effect applied to its arguments.
  | CapabilityTargetMalformed
  -- | A name in a pattern that no constructor in scope stands for.
  | UnknownConstructor String
  -- | A name in a pattern that stands for a value other than a constructor.
  | NotAConstructor String
  -- | A constructor pattern with other than one pattern per field: the
  -- | constructor, its fields, and the patterns written.
  | ConstructorArity String Int Int
  -- | A tag pattern with more than one pattern after it.
  | TagPayloadMany
  -- | A `Number` literal as a pattern.
  | NumberPattern
  -- | An or-pattern with a variable in one of its choices.
  | OrPatternBinds
  -- | A character or string literal holding something that is no Unicode
  -- | scalar value.
  | LiteralNotScalar
  -- | Something written where a pattern stands that is no pattern.
  | NotAPattern
  -- | A refutable pattern in a binding position.
  | RefutablePattern

data ResolveWarning
  -- | A type variable bound where another of its name is in scope.
  = HidesTypeVariable SourceRange String
  -- | A local value bound where a value of its name is in scope.
  | HidesValue SourceRange String

derive instance Eq ResolveError
derive instance Eq ResolveReason
derive instance Eq ResolveWarning

instance Show ResolveError where
  show (ResolveError r reason) =
    "ResolveError " <> show r.start.line <> ":" <> show r.start.column <> " " <> printResolveReason reason

instance Show ResolveReason where
  show = printResolveReason

instance Show ResolveWarning where
  show = printResolveWarning

printResolveReason :: ResolveReason -> String
printResolveReason = case _ of
  UnknownType n -> "There is no type `" <> n <> "` in scope"
  AmbiguousType n -> "The type `" <> n <> "` is ambiguous here; write it qualified"
  UnknownTypeOperator n -> "There is no type operator `" <> n <> "` in scope"
  AmbiguousTypeOperator n -> "The type operator `" <> n <> "` is ambiguous here; write it qualified"
  UnknownTypeVariable n -> "The type variable `" <> n <> "` is not bound here"
  UnknownValue n -> "There is no value `" <> n <> "` in scope"
  AmbiguousValue n -> "The value `" <> n <> "` is ambiguous here; write it qualified"
  OperatorsUnordered a b ->
    "`" <> a <> "` and `" <> b <> "` have one precedence and cannot be chained; add parentheses"
  KindMalformed -> "A kind is made of `Type`, `Effect`, `Row Type`, `Row Effect`, kind variables, and arrows"
  BoundTwice n -> "`" <> n <> "` is bound twice here"
  EffectNotType n -> "`" <> n <> "` is an effect, which stands only at the head of an effect application, in an effect row or a capability signature"
  EffectExpected -> "An effect applied to its arguments is expected here"
  RowItemMisplaced -> "This item cannot stand in a row of this bracket"
  SynthesizedMisplaced ->
    "A synthesized argument stands on the spine of a signature, before any ordinary parameter"
  CapabilityMisplaced -> "`~>` stands only as the signature of a handler declaration, under its quantifiers"
  CapabilityTargetMalformed -> "What `~>` translates into is a list of effects, such as `( Console )` or `()`"
  UnknownConstructor n -> "There is no constructor `" <> n <> "` in scope"
  NotAConstructor n -> "`" <> n <> "` is not a constructor"
  ConstructorArity n fields written ->
    "The constructor `" <> n <> "` has " <> show fields <> " field(s), and is matched here with " <> show written <> " pattern(s)"
  TagPayloadMany -> "A tag carries one value; match several with a tuple, `'T (a, b)`"
  NumberPattern -> "A `Number` cannot be matched by a literal; compare it in a guard"
  OrPatternBinds -> "The choices of an or-pattern cannot bind variables"
  NotAPattern -> "This is not a pattern"
  LiteralNotScalar -> "This literal holds something that is no Unicode scalar value"
  RefutablePattern -> "This pattern can fail to match, which a binding cannot; match it with `case`"

printResolveWarning :: ResolveWarning -> String
printResolveWarning = case _ of
  HidesTypeVariable _ n -> "This binder hides the type variable `" <> n <> "`"
  HidesValue _ n -> "This binding hides the value `" <> n <> "`"

contextOf :: BuildEnvironment -> GroupedModule -> ScopedModule -> Context
contextOf env g scoped =
  { module: scoped.name
  , scope: scoped.scope
  , view: case viewFor (map _.module scoped.imports) env of
      Right v -> Just v
      Left _ -> Nothing
  , ownSynonyms: Set.fromFoldable (Array.mapMaybe synonym g.declarations)
  , ownTypeOperators: Map.fromFoldable (Array.mapMaybe typeFixity g.declarations)
  , ownConstructors: Map.fromFoldable (Array.concatMap constructors g.declarations)
  }
  where
  -- A constructor is keyed by the identity the scope declares it under, which
  -- for an elaboration-only one is its internal identity.
  constructors = case _ of
    DeclarationType _ _ (DeclData _ _ cs) ->
      Array.mapMaybe (\c -> declaredAs c.name <#> \i -> Tuple i { arity: Array.length c.fields, siblings: Array.length cs }) cs
    DeclarationType _ _ (DeclNewtype _ _ c _) ->
      Array.fromFoldable (declaredAs c <#> \i -> Tuple i { arity: 1, siblings: 1 })
    _ -> []
  declaredAs n = Array.findMap own (fromMaybe [] (Map.lookup n.name scoped.scope.declared.values))

  own :: Export (Qualified Ident) -> Maybe Ident
  own c = case c.entity of
    Qualified owner i | owner == scoped.name -> Just i
    _ -> Nothing
  synonym = case _ of
    DeclarationType _ _ (DeclType n _ _) -> Just n.name
    _ -> Nothing
  typeFixity = case _ of
    DeclarationOther _ (DeclTypeFixity f p target op) ->
      Just (Tuple op.name { associativity: associativityOf f, precedence: p.value, target })
    _ -> Nothing
  associativityOf = case _ of
    Infix -> AssociateNone
    Infixl -> AssociateLeft
    Infixr -> AssociateRight

-- | Runs a resolution against a module's context, with no type variable in
-- | scope, numbering bindings from the number given.
runResolve
  :: forall a
   . Context
  -> Int
  -> Resolve a
  -> { result :: a, next :: Int, errors :: Array ResolveError, warnings :: Array ResolveWarning }
runResolve ctx next (Resolve r) = case r { context: ctx, typeVariables: Map.empty, values: Map.empty } { next, errors: [], warnings: [] } of
  Tuple result s -> { result, next: s.next, errors: s.errors, warnings: s.warnings }

asks :: forall a. (Env -> a) -> Resolve a
asks f = Resolve \e s -> Tuple (f e) s

context :: Resolve Context
context = asks _.context

typeVariable :: String -> Resolve (Maybe TypeVar)
typeVariable n = asks (Map.lookup n <<< _.typeVariables)

typeVariables :: Resolve (Map String TypeVar)
typeVariables = asks _.typeVariables

-- | Runs a resolution with the type variables given in scope besides those
-- | already there, each hiding one of its name.
withTypeVariables :: forall a. Array TypeVar -> Resolve a -> Resolve a
withTypeVariables vs (Resolve r) = Resolve \e s ->
  r (e { typeVariables = foldl (\m v@(TypeVar t) -> Map.insert (unTyVar t.name) v m) e.typeVariables vs }) s
  where
  unTyVar (TyVar n) = n

localValue :: String -> Resolve (Maybe LocalVar)
localValue n = asks (Map.lookup n <<< _.values)

-- | Runs a resolution with the local values given in scope besides those
-- | already there, each hiding one of its name.
withValues :: forall a. Array LocalVar -> Resolve a -> Resolve a
withValues vs (Resolve r) = Resolve \e s ->
  r (e { values = foldl (\m v@(LocalVar l) -> Map.insert (unIdent l.name) v m) e.values vs }) s
  where
  unIdent (Ident n) = n

-- | Whether a value of the name is in scope unqualified: a local one, or one
-- | the module declares or imports.
valueInScope :: String -> Resolve Boolean
valueInScope n = do
  local <- localValue n
  ctx <- context
  pure (isJust local || not (Array.null (candidatesIn _.values { range: nowhere, qualifier: Nothing, name: n } ctx.scope)))
  where
  nowhere = { start: { line: 0, column: 0 }, end: { line: 0, column: 0 } }

-- | What a pattern needs of a constructor, where the entity is one.
constructorOf :: Qualified Ident -> Resolve (Maybe Constructor)
constructorOf q@(Qualified owner name) = do
  ctx <- context
  pure
    if owner == ctx.module then Map.lookup name ctx.ownConstructors
    else do
      view <- ctx.view
      entry <- Environment.lookupValue q view
      case entry.sort of
        SortConstructor ty -> do
          t <- Environment.lookupType ty view
          case t.sort of
            DataType d -> do
              c <- Array.find (\c -> c.name == name) d.constructors
              pure { arity: Array.length c.fields, siblings: Array.length d.constructors }
            _ -> Nothing
        _ -> Nothing

-- | A number for a binding, unique within the module.
freshBinding :: Resolve BindingId
freshBinding = Resolve \_ s -> Tuple (BindingId s.next) (s { next = s.next + 1 })

report :: SourceRange -> ResolveReason -> Resolve Unit
report r reason = Resolve \_ s -> Tuple unit (s { errors = Array.snoc s.errors (ResolveError r reason) })

warn :: ResolveWarning -> Resolve Unit
warn w = Resolve \_ s -> Tuple unit (s { warnings = Array.snoc s.warnings w })

-- | What looking a name up came to.
data Found a
  = Found a
  | NotFound
  | Ambiguous

-- | Candidates for a name, the module's own first where it is unqualified, and
-- | those under its alias where it is qualified.
candidatesIn :: forall a. (Names -> Map String (Array a)) -> Name -> Scope -> Array a
candidatesIn field n scope = case n.qualifier of
  Nothing -> case Map.lookup n.name (field scope.declared) of
    Just cs -> cs
    Nothing -> fromMaybe [] (Map.lookup n.name (field scope.imported))
  Just q -> fromMaybe [] (Map.lookup q scope.qualified >>= Map.lookup n.name <<< field)

found :: forall a. Array a -> Found a
found = case _ of
  [ c ] -> Found c
  [] -> NotFound
  _ -> Ambiguous

-- | What a name of the type namespace stands for.
data TypeReference
  = TypeConstructorReference (Qualified TyName)
  | TypeSynonymReference (Qualified TyName)
  | EffectReference (Qualified EffName)

lookupType :: Name -> Resolve (Found TypeReference)
lookupType n = do
  ctx <- context
  pure case found (candidatesIn _.types n ctx.scope) of
    Found (t :: TypeExport) -> Found (referenceOf ctx t.entity)
    NotFound -> NotFound
    Ambiguous -> Ambiguous
  where
  referenceOf ctx = case _ of
    EffectEntity e -> EffectReference e
    TypeEntity q@(Qualified owner (TyName name))
      | owner == ctx.module ->
          if Set.member name ctx.ownSynonyms then TypeSynonymReference q else TypeConstructorReference q
      | otherwise -> case ctx.view >>= Environment.lookupType q of
          Just { sort: Synonym _ } -> TypeSynonymReference q
          _ -> TypeConstructorReference q

-- | How a type operator binds, and what it stands for. One whose target does
-- | not resolve is reported where it is declared, and stands for nothing here.
type TypeOperatorFixity =
  { associativity :: Associativity
  , precedence :: Int
  , target :: Maybe TypeOperatorTarget
  }

lookupTypeOperator :: Name -> Resolve (Found (Tuple (Qualified OperatorName) TypeOperatorFixity))
lookupTypeOperator n = do
  ctx <- context
  case found (candidatesIn _.typeOperators n ctx.scope) of
    Found (c :: Export (Qualified OperatorName)) -> case c.entity of
      q@(Qualified owner (OperatorName name))
        | owner == ctx.module -> case Map.lookup name ctx.ownTypeOperators of
            Just own -> do
              target <- map targetOf (lookupType own.target)
              pure (Found (Tuple q { associativity: own.associativity, precedence: own.precedence, target }))
            Nothing -> pure NotFound
        | otherwise -> pure case ctx.view >>= Environment.lookupTypeOperator q of
            Just entry -> Found (Tuple q { associativity: entry.associativity, precedence: entry.precedence, target: Just entry.target })
            Nothing -> Found (Tuple q { associativity: AssociateLeft, precedence: 9, target: Nothing })
    NotFound -> pure NotFound
    Ambiguous -> pure Ambiguous
  where
  targetOf = case _ of
    Found (TypeConstructorReference q) -> Just (TargetTypeConstructor q)
    Found (TypeSynonymReference q) -> Just (TargetTypeSynonym q)
    Found (EffectReference e) -> Just (TargetEffect e)
    _ -> Nothing

lookupValue :: Name -> Resolve (Found (Qualified Ident))
lookupValue n = do
  ctx <- context
  pure case found (candidatesIn _.values n ctx.scope) of
    Found (c :: Export (Qualified Ident)) -> Found c.entity
    NotFound -> NotFound
    Ambiguous -> Ambiguous
