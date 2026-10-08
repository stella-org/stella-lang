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
  , HandledEffectProblem(..)
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
  , Operation
  , operationOf
  , operationsOf
  , Cell(..)
  , CellClosure(..)
  , withCells
  , withCellsClosed
  , lookupCell
  , ResumeState(..)
  , ResumeBlock(..)
  , resumeState
  , withResume
  , blockResume
  , freshBinding
  , report
  , warn
  , Found(..)
  , lookupType
  , SynonymBody(..)
  , synonymBody
  , speculatively
  , lookupTypeOperator
  , lookupValue
  , lookupOperator
  , lookupAttribute
  , AttributeShape
  , AttributeDefault(..)
  , attributeShape
  , ownValue
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
import Stella.Compiler.CST.Types as CST
import Stella.Compiler.Interface.Environment (BuildEnvironment, ModuleView, viewFor)
import Stella.Compiler.Interface.Environment as Environment
import Stella.Compiler.Interface.Module (Export, TypeEntity(..), TypeExport, TypeSort(..), ValueSort(..), isComputation)
import Stella.Compiler.TypedCore.Decl (Constant)
import Stella.Compiler.Resolve.Group (Declaration(..), GroupReason, GroupedModule, printGroupReason)
import Stella.Compiler.Resolve.Scope (Names, Scope, ScopedModule, emptyNames)
import Stella.Compiler.Surface.Decl (Associativity(..), FixityTarget(..))
import Stella.Compiler.Surface.Name (BindingId(..), CellVar(..), LocalVar(..), OperatorName(..), TypeVar(..))
import Stella.Compiler.Surface.Type (TypeOperatorTarget(..))
import Stella.Compiler.TypedCore.Name (EffName(..), Ident(..), ModuleName(..), Qualified(..), TyName(..), TyVar(..))
import Stella.Compiler.TypedCore.Type as Core

-- | What resolving a module's declarations reads of the module as a whole:
-- | its scope, the build environment as the module sees it, which of its own
-- | type names are synonyms, with the number of their parameters and their
-- | bodies as written, the fixity of each type operator it declares,
-- | the fixity of each operator it declares, each constructor it declares
-- | under the identity it is declared with, each operation it declares with
-- | its effect and the number of its arguments, which of its values are
-- | computations, the parameters of each attribute it declares, and whether it
-- | is or imports `Base.Continuation`.
type Context =
  { module :: ModuleName
  , scope :: Scope
  , view :: Maybe ModuleView
  , ownSynonyms :: Map String { params :: Int, body :: CST.Type }
  , ownTypeOperators :: Map String { associativity :: Associativity, precedence :: Int, target :: Name }
  , ownOperators :: Map String { associativity :: Associativity, precedence :: Int, target :: Name }
  , ownConstructors :: Map Ident Constructor
  , ownOperations :: Map Ident { effect :: EffName, arity :: Int }
  , ownComputations :: Set Ident
  , ownAttributes :: Map Ident (Array CST.AttributeParameter)
  , continuation :: Boolean
  }

-- | What a pattern needs of a constructor: how many fields it has, and how many
-- | constructors its type has.
type Constructor = { arity :: Int, siblings :: Int }

-- | Where resolution stands: the module's context, the type variables in scope
-- | by the name they are written with, the frames around it, innermost first,
-- | the cells in scope by name, and whether `resume` may stand there.
type Env =
  { context :: Context
  , typeVariables :: Map String TypeVar
  , frames :: List Frame
  , cells :: Map String Cell
  , resume :: ResumeState
  }

-- | A cell in scope. A cell of a handling expression is open in the operation
-- | clauses of its groups, and closed everywhere else in the expression, its
-- | region not being reached from there.
data Cell
  = CellOpen CellVar
  | CellClosed CellVar CellClosure

data CellClosure
  = InInitialValue
  | InReturnClause
  | InHandledComputation
  | InHandlerApplied

-- | Whether `resume` may stand where resolution stands: in the immediate body
-- | of a `full` clause it may, and anywhere else it may not, for the reason
-- | given.
data ResumeState
  = ResumeAvailable
  | ResumeBlocked ResumeBlock

data ResumeBlock
  = OutsideFullClause
  | InFastClause
  | InReifiableClause
  -- | Inside a lambda, a local function, or a handling expression, within a
  -- | `full` clause: each could keep what it encloses beyond the clause.
  | InsideLambda
  | InsideLocalFunction
  | InsideHandling

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
  -- | A type synonym written as an element of an effect row.
  | SynonymAsEffect String
  -- | A type synonym written as the source or a target of `~>`.
  | SynonymAtCapability String
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
  -- | A quotation in a module that reaches no `Stella.Syntax` through its
  -- | imports, the syntax it builds being of that module's types.
  | QuotationWithoutSyntax
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
  -- | `x!` or `x := e` where no cell of the name is in scope.
  | UnknownCell String
  -- | A cell reached from a part of its handling expression other than the
  -- | operation clauses of its groups.
  | CellClosedHere String CellClosure
  -- | A `var` of a handler declaration standing after a clause.
  | CellAfterClause String
  -- | A `var` of a handling expression standing after a group or a handler.
  | CellAfterItem String
  -- | `resume` where it may not stand.
  | ResumeMisplaced ResumeBlock
  -- | `resume` other than applied to an argument.
  | ResumeNotApplied
  -- | A group's head that names something of the type namespace other than
  -- | an effect.
  | NotAnEffect String
  -- | A clause naming no operation of the effect its handler handles: the
  -- | name, and the effect.
  | NotAnOperationOf String String
  -- | A clause of a group headed by a label naming no operation in scope, or
  -- | a value that is no operation.
  | UnknownOperation String
  -- | A clause of a group headed by a label naming an operation of another
  -- | effect than the earlier clauses: the operation, its effect, and theirs.
  | OperationOfOtherEffect String String String
  -- | A group headed by a label with no operation clause.
  | LabelledGroupEmpty String
  -- | A clause with other than one pattern per argument of its operation: the
  -- | operation, its arguments, the patterns written, and whether the clause
  -- | takes its continuation as well.
  | ClauseArity String Int Int Boolean
  -- | A second clause for one operation.
  | ClauseTwice String
  -- | A second return clause.
  | ReturnTwice
  -- | A `reifiable full` clause in a module that does not import
  -- | `Base.Continuation`.
  | ContinuationNotImported
  -- | An attribute nothing in scope stands for, or several do.
  | UnknownAttribute String
  | AmbiguousAttribute String
  -- | An attribute on a declaration it cannot stand on.
  | AttributeMisplaced String
  -- | A second use of an attribute the compiler reads, on one declaration.
  | AttributeTwice String
  -- | An attribute with other than as many positional arguments as its
  -- | declaration has parameters: the attribute, its parameters, and the
  -- | arguments written.
  | AttributeArity String Int Int
  -- | A keyword argument its attribute does not declare: the attribute, and
  -- | the label.
  | KeywordUnknown String String
  -- | A keyword argument given twice.
  | KeywordTwice String
  -- | A keyword parameter without a default left out: the attribute, and the
  -- | label.
  | KeywordMissing String String
  -- | An argument of an attribute, or a default, that is no constant.
  | NotAConstant
  -- | A positional parameter of an attribute declaration after a keyword one.
  | PositionalAfterKeyword
  -- | A keyword parameter of an attribute declaration declared twice.
  | KeywordParameterTwice String
  -- | A computation declaration with parameters.
  | ComputationWithParameters String
  -- | A handler declaration's signature from which the effect it handles is
  -- | not read.
  | HandledEffect HandledEffectProblem

-- | Why a handler declaration's signature does not tell the effect handled.
data HandledEffectProblem
  -- | The signature is neither `E ~> ( … )` nor a function from a thunk
  -- | `Unit -> α / {| … |}` to a result, its rows written as rows.
  = HandlerShape
  -- | The thunk's row holds no element the result's row does not.
  | HandlesNothing
  -- | The thunk's row holds several elements the result's row does not.
  | HandlesSeveral
  -- | The one element the result's row does not hold is a labelled instance.
  | HandlesInstance String

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
derive instance Eq HandledEffectProblem
derive instance Eq CellClosure
derive instance Eq ResumeBlock
derive instance Eq ResolveWarning

instance Show ResolveError where
  show (ResolveError r reason) =
    "ResolveError " <> show r.start.line <> ":" <> show r.start.column <> " " <> printResolveReason reason

instance Show ResolveReason where
  show = printResolveReason

instance Show ResolveWarning where
  show = printResolveWarning

-- | The part of a handling expression a cell is closed in.
closedPart :: CellClosure -> String
closedPart = case _ of
  InInitialValue -> "an initial value"
  InReturnClause -> "a return clause"
  InHandledComputation -> "the computation handled"
  InHandlerApplied -> "a handler applied as an item"

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
  SynonymAsEffect n ->
    "`" <> n <> "` is a type synonym, and an element of an effect row is one effect applied to its arguments; where `" <> n <> "` stands for a row of effects, write `/ " <> n <> "` for the row itself, or `..." <> n <> "` to bring its effects into another row"
  SynonymAtCapability n ->
    "`" <> n <> "` is a type synonym, and the source of `~>` and each target on its right name one effect applied to its arguments, written directly"
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
  QuotationWithoutSyntax -> "A quotation builds syntax of `Stella.Syntax`, which this module must import"
  UnknownAlias a -> "There is no module imported as `" <> a <> "`"
  UnknownOperator n -> "There is no operator `" <> n <> "` in scope"
  AmbiguousOperator n -> "The operator `" <> n <> "` is ambiguous here; write it qualified"
  NotAnOperation n -> "`" <> n <> "` is not an operation, which a label selects the instance of"
  LabelExpected -> "A label, the name of an instance, follows `@` here"
  LabelTwice l -> "The label `" <> l <> "` is written twice here"
  LetGrouping reason -> printGroupReason reason
  UnknownCell n -> "There is no cell `" <> n <> "` here; a cell is reached from the operation clauses of the handling expression or handler declaring it"
  CellClosedHere n where_ ->
    "The cell `" <> n <> "` cannot be reached from " <> closedPart where_
      <> "; a cell is reached from the operation clauses of the handling expression or handler declaring it alone"
  CellAfterClause n -> "The cell `" <> n <> "` is declared after a clause; every `var` of a handler stands ahead of its clauses"
  CellAfterItem n -> "The cell `" <> n <> "` is declared after a group or a handler; every `var` of a handling expression stands ahead of them"
  ResumeMisplaced block -> case block of
    OutsideFullClause -> "`resume` stands only in the body of a `full` clause"
    InFastClause -> "A `fast` clause does not capture its continuation, so `resume` cannot stand in it; the body's value is what the operation resumes with"
    InReifiableClause -> "A `reifiable full` clause takes its continuation as its last parameter; resume it with `Continuation.continue`"
    InsideLambda -> "`resume` cannot stand inside a lambda within its clause, which could keep it beyond the clause; mark the clause `reifiable full` to keep the continuation"
    InsideLocalFunction -> "`resume` cannot stand inside a local function within its clause, which could keep it beyond the clause; mark the clause `reifiable full` to keep the continuation"
    InsideHandling -> "`resume` cannot stand inside a handling expression within its clause, whose handlers could keep it beyond the clause; mark the clause `reifiable full` to keep the continuation"
  ResumeNotApplied -> "`resume` is applied to the value the operation resumes with, as `resume x`, and is no value of its own"
  NotAnEffect n -> "`" <> n <> "` is not an effect; a group is headed by an effect or by a label"
  NotAnOperationOf n e -> "`" <> n <> "` is not an operation of the effect `" <> e <> "`"
  UnknownOperation n -> "There is no operation `" <> n <> "` in scope"
  OperationOfOtherEffect n e first ->
    "`" <> n <> "` is an operation of `" <> e <> "`, and the earlier clauses of this group handle `" <> first <> "`; a group handles one effect"
  LabelledGroupEmpty l -> "The group headed by `" <> l <> "` has no operation clause, which is what tells the effect it handles"
  ClauseArity n arguments written continuation ->
    "The operation `" <> n <> "` takes " <> show arguments <> " argument(s)"
      <> (if continuation then ", and the clause its continuation after them," else ",")
      <> " and the clause binds "
      <> show written
      <> " pattern(s)"
  ClauseTwice n -> "The operation `" <> n <> "` has a clause already"
  ReturnTwice -> "This handler has a return clause already"
  ContinuationNotImported -> "A `reifiable full` clause depends on `Base.Continuation`, which this module does not import"
  UnknownAttribute n -> "There is no attribute `" <> n <> "` in scope"
  AmbiguousAttribute n -> "The attribute `" <> n <> "` is ambiguous here; write it qualified"
  AttributeMisplaced n -> "The attribute `" <> n <> "` cannot stand on this declaration"
  AttributeTwice n -> "The attribute `" <> n <> "` stands on this declaration already"
  AttributeArity n parameters written ->
    "The attribute `" <> n <> "` takes " <> show parameters <> " positional argument(s), and is given " <> show written
  KeywordUnknown n l -> "The attribute `" <> n <> "` has no keyword parameter `" <> l <> "`"
  KeywordTwice l -> "The keyword argument `" <> l <> "` is given twice"
  KeywordMissing n l -> "The attribute `" <> n <> "` needs the keyword argument `" <> l <> "`, which has no default"
  NotAConstant -> "An argument of an attribute is a constant: a literal, a global value, a constructor applied to constants, or a record of constants"
  PositionalAfterKeyword -> "The positional parameters of an attribute come before its keyword parameters"
  KeywordParameterTwice l -> "The keyword parameter `" <> l <> "` is declared twice"
  ComputationWithParameters n -> "The computation `" <> n <> "` takes no parameter; one that does is a function, whose signature is an arrow"
  HandledEffect problem -> case problem of
    HandlerShape ->
      "A handler's signature is `E ~> ( … )`, or a function from a thunk `Unit -> a / ρ` to its result, each row written with `{| … |}` or named by a type synonym without parameters"
    HandlesNothing -> "Every effect the thunk's row holds is in the result's row too; a handler declaration removes one"
    HandlesSeveral -> "The thunk's row holds several effects the result's row does not; a handler declaration removes one"
    HandlesInstance l ->
      "A handler declaration handles an effect, and `" <> l <> "` is a labelled instance; handle it with a group headed by `" <> l <> "`"

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
  , ownSynonyms: Map.fromFoldable (Array.mapMaybe synonym g.declarations)
  , ownTypeOperators: Map.fromFoldable (Array.mapMaybe typeFixity g.declarations)
  , ownOperators: Map.fromFoldable (Array.mapMaybe fixity g.declarations)
  , ownConstructors: Map.fromFoldable (Array.concatMap constructors g.declarations)
  , ownOperations: Map.fromFoldable (Array.concatMap operations g.declarations)
  , ownComputations: Set.fromFoldable (Array.mapMaybe computation g.declarations)
  , ownAttributes: Map.fromFoldable (Array.mapMaybe attribute g.declarations)
  , continuation: scoped.name == continuationModule || Array.any (\i -> i.module == continuationModule) scoped.imports
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
    DeclarationType _ _ (DeclType n params body) -> Just (Tuple n.name { params: Array.length params, body })
    _ -> Nothing
  fixity = case _ of
    DeclarationOther _ (DeclFixity f p target op) ->
      Just (Tuple op.name { associativity: associativityOf f, precedence: p.value, target })
    _ -> Nothing
  operations = case _ of
    DeclarationOther _ (DeclEffect e _ ops) ->
      map (\op -> Tuple (Ident op.name.name) { effect: EffName e.name, arity: arityOf op.type }) ops
    _ -> []
  computation = case _ of
    DeclarationValue _ v | v.computation -> Just (Ident v.name.name)
    _ -> Nothing
  attribute = case _ of
    DeclarationOther _ (DeclAttribute n params) -> Just (Tuple (Ident n.name) params)
    _ -> Nothing
  typeFixity = case _ of
    DeclarationOther _ (DeclTypeFixity f p target op) ->
      Just (Tuple op.name { associativity: associativityOf f, precedence: p.value, target })
    _ -> Nothing
  associativityOf = case _ of
    Infix -> AssociateNone
    Infixl -> AssociateLeft
    Infixr -> AssociateRight
  -- The arguments of an operation are the types left of its arrows, `->*`
  -- the last of them.
  arityOf = case _ of
    CST.TypeForall _ body -> arityOf body
    CST.TypeParens inner -> arityOf inner
    CST.TypeArrow _ rest -> 1 + arityOf rest
    CST.TypeOperationArrow _ _ _ -> 1
    _ -> 0

continuationModule :: ModuleName
continuationModule = ModuleName "Base.Continuation"

-- | Runs a resolution against a module's context, with no type variable, frame,
-- | or cell around it and outside every clause, numbering bindings from the
-- | number given.
runResolve
  :: forall a
   . Context
  -> Int
  -> Resolve a
  -> { result :: a, next :: Int, errors :: Array ResolveError, warnings :: Array ResolveWarning }
runResolve ctx next (Resolve r) = case r { context: ctx, typeVariables: Map.empty, frames: Nil, cells: Map.empty, resume: ResumeBlocked OutsideFullClause } { next, errors: [], warnings: [] } of
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
      else if Map.member name ctx.ownOperations then OperationValue
      else if Set.member name ctx.ownComputations then ComputationValue
      else PlainValue
    else case ctx.view >>= Environment.lookupValue q of
      Just { sort: SortConstructor _ } -> ConstructorValue
      Just { sort: SortOperation _ } -> OperationValue
      Just entry | isComputation entry.scheme -> ComputationValue
      _ -> PlainValue

-- | An operation: the effect declaring it, and the number of its arguments.
type Operation = { effect :: Qualified EffName, arity :: Int }

operationOf :: Qualified Ident -> Resolve (Maybe Operation)
operationOf q@(Qualified owner name) = do
  ctx <- context
  pure
    if owner == ctx.module then
      Map.lookup name ctx.ownOperations <#> \op -> { effect: Qualified owner op.effect, arity: op.arity }
    else do
      view <- ctx.view
      entry <- Environment.lookupValue q view
      case entry.sort of
        SortOperation effect -> do
          e <- Environment.lookupEffect effect view
          op <- Array.find (\o -> o.name == name) e.operations
          pure { effect, arity: Array.length op.arguments }
        _ -> Nothing

-- | The operations an effect declares, each by its name and the number of its
-- | arguments.
operationsOf :: Qualified EffName -> Resolve (Array { name :: Ident, arity :: Int })
operationsOf e@(Qualified owner name) = do
  ctx <- context
  pure
    if owner == ctx.module then
      Array.mapMaybe (\(Tuple i op) -> if op.effect == name then Just { name: i, arity: op.arity } else Nothing)
        (Map.toUnfoldable ctx.ownOperations)
    else case ctx.view >>= Environment.lookupEffect e of
      Just entry -> map (\op -> { name: op.name, arity: Array.length op.arguments }) entry.operations
      Nothing -> []

-- | Runs a resolution with the cells given open, each hiding a cell of its
-- | name.
withCells :: forall a. Array CellVar -> Resolve a -> Resolve a
withCells = withCellsAs CellOpen

-- | Runs a resolution with the cells given closed for the reason given, each
-- | hiding a cell of its name.
withCellsClosed :: forall a. CellClosure -> Array CellVar -> Resolve a -> Resolve a
withCellsClosed why = withCellsAs (\v -> CellClosed v why)

withCellsAs :: forall a. (CellVar -> Cell) -> Array CellVar -> Resolve a -> Resolve a
withCellsAs k vs = locally \e -> e { cells = foldl (\m v@(CellVar c) -> Map.insert (unIdent c.name) (k v) m) e.cells vs }
  where
  unIdent (Ident n) = n

lookupCell :: String -> Resolve (Maybe Cell)
lookupCell n = asks (Map.lookup n <<< _.cells)

resumeState :: Resolve ResumeState
resumeState = asks _.resume

-- | Runs a resolution with `resume` available or blocked as given, which is
-- | what entering a clause does.
withResume :: forall a. ResumeState -> Resolve a -> Resolve a
withResume st = locally _ { resume = st }

-- | Runs a resolution behind a boundary `resume` does not cross: where it is
-- | available, it is blocked for the reason given, and otherwise it stays as
-- | it is.
blockResume :: forall a. ResumeBlock -> Resolve a -> Resolve a
blockResume why = locally \e -> case e.resume of
  ResumeAvailable -> e { resume = ResumeBlocked why }
  ResumeBlocked _ -> e

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
          if Map.member name ctx.ownSynonyms then TypeSynonymReference q else TypeConstructorReference q
      | otherwise -> case ctx.view >>= Environment.lookupType q of
          Just { sort: Synonym _ } -> TypeSynonymReference q
          _ -> TypeConstructorReference q

-- | The body of a type synonym without parameters: one the module declares,
-- | as written, or one an interface holds, expanded already.
data SynonymBody
  = OwnSynonym CST.Type
  | ImportedSynonym Core.Type

synonymBody :: Qualified TyName -> Resolve (Maybe SynonymBody)
synonymBody q@(Qualified owner (TyName name)) = do
  ctx <- context
  pure
    if owner == ctx.module then case Map.lookup name ctx.ownSynonyms of
      Just s | s.params == 0 -> Just (OwnSynonym s.body)
      _ -> Nothing
    else case ctx.view >>= Environment.lookupType q of
      Just { sort: Synonym s } | Array.null s.params -> Just (ImportedSynonym s.body)
      _ -> Nothing

-- | Runs a resolution at the module's top level, outside every binder and
-- | frame, keeping its result alone: it takes no binding number and reports
-- | nothing. What a declaration resolves to is read this way where another
-- | declaration needs it before its own turn.
speculatively :: forall a. Resolve a -> Resolve a
speculatively (Resolve r) = Resolve \e s -> case r (e { typeVariables = Map.empty, frames = Nil, cells = Map.empty }) s of
  Tuple a _ -> Tuple a s

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

-- | An attribute, in the attribute namespace.
lookupAttribute :: Name -> Resolve (Found (Qualified Ident))
lookupAttribute n = candidates _.attributes n <#> \cs -> found cs <#> \(c :: Export (Qualified Ident)) -> c.entity

-- | What normalizing an attribute's arguments reads of its declaration: how
-- | many positional parameters it has, and its keyword parameters in the order
-- | declared, each with its default where it has one.
type AttributeShape =
  { positional :: Int
  , keyword :: Array { label :: String, default :: Maybe AttributeDefault }
  }

-- | A keyword parameter's default: as the module's own declaration writes it,
-- | or as an interface holds it.
data AttributeDefault
  = OwnDefault CST.Expr
  | ImportedDefault Constant

attributeShape :: Qualified Ident -> Resolve (Maybe AttributeShape)
attributeShape q@(Qualified owner name) = do
  ctx <- context
  pure
    if owner == ctx.module then Map.lookup name ctx.ownAttributes <#> \params ->
      { positional: Array.length (Array.filter positional params)
      , keyword: Array.mapMaybe keyword params
      }
    else ctx.view >>= Environment.lookupAttribute q <#> \entry ->
      { positional: Array.length entry.positional
      , keyword: map (\k -> { label: k.label, default: map ImportedDefault k.default }) entry.keyword
      }
  where
  positional = case _ of
    CST.AttributePositional _ -> true
    CST.AttributeKeyword _ _ _ -> false
  keyword = case _ of
    CST.AttributeKeyword l _ d -> Just { label: l.name, default: map OwnDefault d }
    CST.AttributePositional _ -> Nothing

-- | The entity a value the module declares is, by the name written: its own
-- | name, or the internal identity an elaboration-only constructor takes.
ownValue :: String -> Resolve (Qualified Ident)
ownValue n = do
  ctx <- context
  let
    own (c :: Export (Qualified Ident)) = case c.entity of
      Qualified owner _ | owner == ctx.module -> Just c.entity
      _ -> Nothing
  pure (fromMaybe (Qualified ctx.module (Ident n)) (Array.findMap own (fromMaybe [] (Map.lookup n ctx.scope.declared.values))))

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
