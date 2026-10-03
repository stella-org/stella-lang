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
  , withValues
  , withOpened
  , atTopLevel
  , openedBy
  , valueInScope
  , constructorOf
  , ValueKind(..)
  , valueKind
  , freshBinding
  , report
  , warn
  , Found(..)
  , lookupType
  , lookupTypeOperator
  , lookupValue
  , lookupOperator
  , lookupValueReference
  , ValueReference(..)
  , TypeReference(..)
  , TypeOperatorFixity
  , OperatorFixity
  ) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldl)
import Data.Map (Map)
import Data.Map as Map
import Data.List (List(..), (:))
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Set (Set)
import Data.Set as Set
import Data.Tuple (Tuple(..))
import Stella.Compiler.CST.Types (Decl(..), Fixity(..), Name, SourceRange)
import Stella.Compiler.Interface.Environment (BuildEnvironment, ModuleView, viewFor)
import Stella.Compiler.Interface.Environment as Environment
import Stella.Compiler.Interface.Module (Export, TypeEntity(..), TypeExport, TypeSort(..), ValueSort(..), isComputation)
import Stella.Compiler.Resolve.Group (Declaration(..), GroupReason, GroupedModule, printGroupReason)
import Stella.Compiler.Resolve.Scope (Names, Scope, ScopedModule, emptyNames)
import Stella.Compiler.Surface.Decl (Associativity(..), FixityTarget(..))
import Stella.Compiler.Surface.Name (BindingId(..), LocalVar(..), OperatorName(..), TypeVar(..))
import Stella.Compiler.Surface.Type (TypeOperatorTarget(..))
import Stella.Compiler.TypedCore.Name (EffName, Ident(..), ModuleName, Qualified(..), TyName(..), TyVar(..))

-- | What resolving a module's declarations reads of the module as a whole:
-- | its scope, the build environment as the module sees it, which of its own
-- | type names are synonyms, the fixity of each type operator it declares,
-- | the fixity of each operator it declares, each constructor it declares
-- | under the identity it is declared with, and which of its values are
-- | operations and which computations.
type Context =
  { module :: ModuleName
  , scope :: Scope
  , view :: Maybe ModuleView
  , ownSynonyms :: Set String
  , ownTypeOperators :: Map String { associativity :: Associativity, precedence :: Int, target :: Name }
  , ownOperators :: Map String { associativity :: Associativity, precedence :: Int, target :: Name }
  , ownConstructors :: Map Ident Constructor
  , ownOperations :: Set Ident
  , ownComputations :: Set Ident
  }

-- | What a pattern needs of a constructor: how many fields it has, and how many
-- | constructors its type has.
type Constructor = { arity :: Int, siblings :: Int }

-- | Where resolution stands: the module's context, the type variables in scope
-- | by the name they are written with, and the frames around it, innermost
-- | first.
type Env =
  { context :: Context
  , typeVariables :: Map String TypeVar
  , frames :: List Frame
  }

-- | What a construct around the position puts in scope: the local values a
-- | binding group binds, or the names a local open opens. An unqualified name
-- | is looked up in the innermost frame holding it before the module's scope.
data Frame
  = Locals (Map String LocalVar)
  | Opened Names

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
  -- | A form this version does not resolve yet, named.
  | NotYetSupported String
  -- | An alias a local open names that no import declares.
  | UnknownAlias String
  -- | An operator nothing in scope stands for.
  | UnknownOperator String
  | AmbiguousOperator String
  -- | `op@label` where `op` is no operation.
  | NotAnOperation String
  -- | `op@x` where `x` is no label.
  | LabelExpected
  -- | A label a record, its update, or its pattern writes twice.
  | LabelTwice String
  -- | A `let` block whose signatures and definitions do not pair up.
  | LetGrouping GroupReason

data ResolveWarning
  -- | A type variable bound where another of its name is in scope.
  = HidesTypeVariable SourceRange String
  -- | A local value bound where a value of its name is in scope.
  | HidesValue SourceRange String
  -- | A name a local open brings, used where a local value of its name is in
  -- | scope outside the open.
  | OpenHidesLocal SourceRange String

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
  NotYetSupported what -> what <> " is not supported yet"
  UnknownAlias a -> "There is no module imported as `" <> a <> "`"
  UnknownOperator n -> "There is no operator `" <> n <> "` in scope"
  AmbiguousOperator n -> "The operator `" <> n <> "` is ambiguous here; write it qualified"
  NotAnOperation n -> "`" <> n <> "` is not an operation, which a label selects the instance of"
  LabelExpected -> "A label, the name of an instance, follows `@` here"
  LabelTwice l -> "The label `" <> l <> "` is written twice here"
  LetGrouping reason -> printGroupReason reason

printResolveWarning :: ResolveWarning -> String
printResolveWarning = case _ of
  HidesTypeVariable _ n -> "This binder hides the type variable `" <> n <> "`"
  HidesValue _ n -> "This binding hides the value `" <> n <> "`"
  OpenHidesLocal _ n -> "The open brings a `" <> n <> "` that hides the local one outside it"

contextOf :: BuildEnvironment -> GroupedModule -> ScopedModule -> Context
contextOf env g scoped =
  { module: scoped.name
  , scope: scoped.scope
  , view: case viewFor (map _.module scoped.imports) env of
      Right v -> Just v
      Left _ -> Nothing
  , ownSynonyms: Set.fromFoldable (Array.mapMaybe synonym g.declarations)
  , ownTypeOperators: Map.fromFoldable (Array.mapMaybe typeFixity g.declarations)
  , ownOperators: Map.fromFoldable (Array.mapMaybe fixity g.declarations)
  , ownConstructors: Map.fromFoldable (Array.concatMap constructors g.declarations)
  , ownOperations: Set.fromFoldable (Array.concatMap operations g.declarations)
  , ownComputations: Set.fromFoldable (Array.mapMaybe computation g.declarations)
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
  fixity = case _ of
    DeclarationOther _ (DeclFixity f p target op) ->
      Just (Tuple op.name { associativity: associativityOf f, precedence: p.value, target })
    _ -> Nothing
  operations = case _ of
    DeclarationOther _ (DeclEffect _ _ ops) -> map (\op -> Ident op.name.name) ops
    _ -> []
  computation = case _ of
    DeclarationValue _ v | v.computation -> Just (Ident v.name.name)
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
-- | scope and no frame around it, numbering bindings from the number given.
runResolve
  :: forall a
   . Context
  -> Int
  -> Resolve a
  -> { result :: a, next :: Int, errors :: Array ResolveError, warnings :: Array ResolveWarning }
runResolve ctx next (Resolve r) = case r { context: ctx, typeVariables: Map.empty, frames: Nil } { next, errors: [], warnings: [] } of
  Tuple result s -> { result, next: s.next, errors: s.errors, warnings: s.warnings }

asks :: forall a. (Env -> a) -> Resolve a
asks f = Resolve \e s -> Tuple (f e) s

locally :: forall a. (Env -> Env) -> Resolve a -> Resolve a
locally f (Resolve r) = Resolve \e s -> r (f e) s

context :: Resolve Context
context = asks _.context

typeVariable :: String -> Resolve (Maybe TypeVar)
typeVariable n = asks (Map.lookup n <<< _.typeVariables)

typeVariables :: Resolve (Map String TypeVar)
typeVariables = asks _.typeVariables

-- | Runs a resolution with the type variables given in scope besides those
-- | already there, each hiding one of its name.
withTypeVariables :: forall a. Array TypeVar -> Resolve a -> Resolve a
withTypeVariables vs = locally \e ->
  e { typeVariables = foldl (\m v@(TypeVar t) -> Map.insert (unTyVar t.name) v m) e.typeVariables vs }
  where
  unTyVar (TyVar n) = n

-- | Runs a resolution with the local values given in a frame of their own.
withValues :: forall a. Array LocalVar -> Resolve a -> Resolve a
withValues vs = locally \e -> e { frames = Locals (Map.fromFoldable (map entry vs)) : e.frames }
  where
  entry v@(LocalVar l) = case l.name of
    Ident n -> Tuple n v

-- | Runs a resolution with the names an open brings in a frame of their own.
withOpened :: forall a. Names -> Resolve a -> Resolve a
withOpened names = locally \e -> e { frames = Opened names : e.frames }

-- | Runs a resolution at the module's top level, outside every frame: what a
-- | declaration names is resolved there wherever it is used.
atTopLevel :: forall a. Resolve a -> Resolve a
atTopLevel = locally _ { frames = Nil }

-- | Whether a value of the name is in scope unqualified: a local one, one an
-- | open brings, or one the module declares or imports.
valueInScope :: String -> Resolve Boolean
valueInScope n = do
  frames <- asks _.frames
  ctx <- context
  pure (Array.any holds (Array.fromFoldable frames) || not (Array.null (topLevel _.values n ctx.scope)))
  where
  holds = case _ of
    Locals m -> Map.member n m
    Opened names -> Map.member n names.values

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

-- | What a global of the value namespace is, which decides the node a
-- | reference to it is.
data ValueKind
  = PlainValue
  | ComputationValue
  | ConstructorValue
  | OperationValue

valueKind :: Qualified Ident -> Resolve ValueKind
valueKind q@(Qualified owner name) = do
  ctx <- context
  pure
    if owner == ctx.module then
      if Map.member name ctx.ownConstructors then ConstructorValue
      else if Set.member name ctx.ownOperations then OperationValue
      else if Set.member name ctx.ownComputations then ComputationValue
      else PlainValue
    else case ctx.view >>= Environment.lookupValue q of
      Just { sort: SortConstructor _ } -> ConstructorValue
      Just { sort: SortOperation _ } -> OperationValue
      Just entry | isComputation entry.scheme -> ComputationValue
      _ -> PlainValue

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

derive instance Functor Found

-- | Candidates for a name. An unqualified one is looked up in the innermost
-- | open bringing it, then among the module's own declarations, then among its
-- | imports; a qualified one under its alias.
candidates :: forall a. (Names -> Map String (Array a)) -> Name -> Resolve (Array a)
candidates field n = do
  frames <- asks _.frames
  ctx <- context
  pure case n.qualifier of
    Nothing -> fromMaybe (topLevel field n.name ctx.scope) (Array.findMap opened (Array.fromFoldable frames))
    Just q -> fromMaybe [] (Map.lookup q ctx.scope.qualified >>= Map.lookup n.name <<< field)
  where
  opened = case _ of
    Opened names -> Map.lookup n.name (field names)
    Locals _ -> Nothing

topLevel :: forall a. (Names -> Map String (Array a)) -> String -> Scope -> Array a
topLevel field n scope = case Map.lookup n (field scope.declared) of
  Just cs -> cs
  Nothing -> fromMaybe [] (Map.lookup n (field scope.imported))

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
  cs <- candidates _.types n
  pure (found cs <#> \(t :: TypeExport) -> referenceOf ctx t.entity)
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
  cs <- candidates _.typeOperators n
  case found cs of
    Found (c :: Export (Qualified OperatorName)) -> case c.entity of
      q@(Qualified owner (OperatorName name))
        | owner == ctx.module -> case Map.lookup name ctx.ownTypeOperators of
            Just own -> do
              target <- map targetOf (atTopLevel (lookupType own.target))
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

-- | How an operator binds, and the value or constructor it stands for. One
-- | whose target does not resolve is reported where it is declared, and stands
-- | for nothing here.
type OperatorFixity =
  { associativity :: Associativity
  , precedence :: Int
  , target :: Maybe (Qualified Ident)
  }

lookupOperator :: Name -> Resolve (Found OperatorFixity)
lookupOperator n = do
  ctx <- context
  cs <- candidates _.operators n
  case found cs of
    Found (c :: Export (Qualified OperatorName)) -> case c.entity of
      q@(Qualified owner (OperatorName name))
        | owner == ctx.module -> case Map.lookup name ctx.ownOperators of
            Just own -> do
              target <- atTopLevel (lookupValue own.target)
              pure (Found { associativity: own.associativity, precedence: own.precedence, target: targetOf target })
            Nothing -> pure NotFound
        | otherwise -> pure case ctx.view >>= Environment.lookupOperator q of
            Just entry -> Found
              { associativity: entry.associativity
              , precedence: entry.precedence
              , target: Just case entry.target of
                  FixityValue v -> v
                  FixityConstructor v -> v
              }
            Nothing -> Found { associativity: AssociateLeft, precedence: 9, target: Nothing }
    NotFound -> pure NotFound
    Ambiguous -> pure Ambiguous
  where
  targetOf = case _ of
    Found v -> Just v
    _ -> Nothing

-- | A global of the value namespace.
lookupValue :: Name -> Resolve (Found (Qualified Ident))
lookupValue n = candidates _.values n <#> \cs -> found cs <#> \(c :: Export (Qualified Ident)) -> c.entity

-- | What a name of the value namespace stands for where an expression names
-- | it.
data ValueReference
  = LocalReference LocalVar
  | GlobalReference (Qualified Ident)

-- | A name of the value namespace as an expression names it: an unqualified
-- | one in the innermost frame holding it, a local binding or an open, and
-- | then in the module's scope. An open that takes a name from a local binding
-- | outside it is warned of.
lookupValueReference :: Name -> Resolve (Found ValueReference)
lookupValueReference n = case n.qualifier of
  Just _ -> map GlobalReference <$> lookupValue n
  Nothing -> asks _.frames >>= go
  where
  go = case _ of
    Locals m : rest -> case Map.lookup n.name m of
      Just v -> pure (Found (LocalReference v))
      Nothing -> go rest
    Opened names : rest -> case Map.lookup n.name names.values of
      Just cs -> do
        when (Array.any local (Array.fromFoldable rest)) (warn (OpenHidesLocal n.range n.name))
        pure (found cs <#> \(c :: Export (Qualified Ident)) -> GlobalReference c.entity)
      Nothing -> go rest
    Nil -> map GlobalReference <$> atTopLevel (lookupValue n)
  local = case _ of
    Locals m -> Map.member n.name m
    Opened _ -> false

-- | The names an alias opens: everything the imports declaring it make
-- | reachable through it, a lazy alias's among them.
openedBy :: String -> Resolve (Maybe Names)
openedBy alias = do
  ctx <- context
  pure case Map.lookup alias ctx.scope.qualified, Map.lookup alias ctx.scope.lazy of
    Nothing, Nothing -> Nothing
    a, b -> Just (unite (fromMaybe emptyNames a) (fromMaybe emptyNames b))
  where
  unite a b =
    { values: merge a.values b.values
    , types: merge a.types b.types
    , operators: merge a.operators b.operators
    , typeOperators: merge a.typeOperators b.typeOperators
    , macros: merge a.macros b.macros
    , attributes: merge a.attributes b.attributes
    }

  merge :: forall e r. Eq e => Map String (Array { entity :: e | r }) -> Map String (Array { entity :: e | r }) -> Map String (Array { entity :: e | r })
  merge = Map.unionWith \xs ys -> xs <> Array.filter (\y -> not (Array.any (\x -> x.entity == y.entity) xs)) ys
