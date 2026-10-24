-- | A module's type and value declarations elaborated into Core, against what
-- | its imports reach ([Elaboration](../../../../../docs/technical-references/02-Surface-Language/01-Elaboration.md)).
-- |
-- | **The type declarations are elaborated before any value**
-- | ([Types](Types.purs)), and what they declare is added to what the values
-- | are elaborated against: the data types, the foreign types, and the effects
-- | to the signature, the constructors to the signature and the catalog, and
-- | the synonyms to those the values' types are read through. That signature is the module's own:
-- | the build environment is not, and the Core checker is given the signature
-- | of the imports alone, as for any module, with the foreign types the module
-- | declares, which no Core declaration produces. A type declaration that does
-- | not elaborate leaves the values unread, a value naming its type having
-- | nothing to be read against. An attribute on a synonym or a foreign type,
-- | having no Core declaration to stand on, is checked here.
-- |
-- | **Every signature is read before any body.** A declaration's scheme is
-- | what every other declaration refers to it at, so the schemes are settled
-- | first — their kinds decided, and each that could not be reported — and
-- | entered into the catalog beside what the imports publish; a body may then
-- | refer to any value of the module, itself among them.
-- |
-- | **Each body is elaborated as an attempt of its own.** What it leaves
-- | undecided stands as equality jobs, which the loop runs once every body has
-- | been elaborated, so an equation one body states may be decided by what
-- | another does. A body that fails, or holds a form this version does not
-- | read, leaves nothing behind. Once the loop is quiescent, the fits left
-- | undecided are resolved by direction, each declaration's apart
-- | ([Resolve](../Driver/Resolve.purs)); a declaration whose effect rows nothing
-- | decides is reported, and a checking boundary its body cannot meet without
-- | an implicit handler is outside what this version elaborates. Then each
-- | body is zonked and made a Core term, and a type nothing decided is
-- | reported where it stands. A body is a value only once every equation and
-- | fit stated for it holds; one the loop stopped before deciding is reported,
-- | never returned.
-- |
-- | **A foreign is read as a value's signature is, and has no body**: what it
-- | takes and gives must cross to the host ([ForeignBoundary](../../ForeignBoundary.purs)),
-- | which its type decides where it is declared. **A foreign naming an entry the
-- | runtime carries out is no host's**, by its qualified name alone
-- | ([Primitive](../../Primitive.purs)): nothing crosses, and it must be declared
-- | at the scheme the ABI declares the entry at. An attribute declaration's
-- | parameters are read at closed types against the module's types.
-- |
-- | **A computation declaration is a value whose Core type is a thunk**, its
-- | signature read as that type and its body under it. **A handler declaration
-- | is a value at its signature's type**, its body a handling expression under
-- | its parameters and its thunk. **An implicit one is also read against the
-- | conditions of being one**: those its declaration shows, whether or not its
-- | body elaborates, and its cells' initial values, judged on the Core the body
-- | became. What it removes and performs mentions no variable in this version,
-- | and the interface records it with those elements.
-- |
-- | **A value without a signature is generalized**, each strongly connected
-- | component of the references such values make to one another a group, the
-- | groups in dependency order and before any body with a signature; its scheme
-- | is read by the module's bodies and is in no catalog. **A declaration whose
-- | signature is partial** is a member of such a group, its body deciding what
-- | the signature leaves unwritten and its scheme gaining nothing else. Inside
-- | its group, a member is referred to at the one type it has there. A
-- | declaration referring to a value with no scheme — one its group did not
-- | generalize, or one whose signature gave none — is left unchecked, and so is
-- | every member of a group one of which does. A fixity gives Core nothing.
module Stella.Compiler.Elaborate.Surface.Module
  ( ElaborationError(..)
  , ImplicitProblem(..)
  , ElaboratedValue
  , Elaborating
  , ElaboratedModule
  , elaborateModule
  , elaborateModuleM
  , elaborateValues
  , settleBodies
  , settleBodiesM
  , cellRecords
  , escapedCells
  ) where

import Prelude
import Prim hiding (Type)

import Control.Monad.Except (ExceptT, catchError, runExceptT, throwError)
import Control.Monad.Rec.Class (class MonadRec)
import Control.Monad.State (StateT(..), get, gets, modify_, put, runStateT, state)
import Control.Monad.Trans.Class (lift)
import Data.Array as Array
import Data.Array.NonEmpty (NonEmptyArray)
import Data.Array.NonEmpty as NonEmptyArray
import Data.Either (Either(..), either)
import Data.Foldable (foldl, for_)
import Data.Identity (Identity(..))
import Data.Traversable (traverse)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, isJust, isNothing, maybe)
import Data.Set (Set)
import Data.Set as Set
import Data.Tuple (Tuple(..), fst, snd)
import Stella.Compiler.Elaborate.CorePlus.Context (Origin(..), emptyXContext)
import Stella.Compiler.Elaborate.CorePlus.Term (Residue(..), XExpr, isSettledValueForm, pendingCasesOf, replacePendingCases, toCoreExpr, toInitializationExpr)
import Stella.Compiler.Elaborate.CorePlus.Kind (KindMetaVar, XKind(..), kindMetasOf)
import Stella.Compiler.Elaborate.CorePlus.Type (MetaVar, XType(..), freeKindVars, fromCore, kindMetasOfType, metasOf, toCore)
import Stella.Compiler.Elaborate.Surface.Types (readAttributeDeclaration, readTypes, settledTypes)
import Stella.Compiler.Elaborate.Environment.Synonyms (SynonymEntry)
import Stella.Compiler.Elaborate.Surface.Internal (Internal, declaredEntryMismatches, internalEntries)
import Stella.Compiler.Elaborate.Driver.Attempt (attemptPending, runAttempt)
import Stella.Compiler.Elaborate.Driver.Loop (Attempter, AttempterM, identically, runAttemptingM)
import Stella.Compiler.Elaborate.Driver.Loop as Loop
import Stella.Compiler.Elaborate.Driver.Resolve (ComponentOutcome(..), Resolution(..), resolveByDirectionM, resolveOwnersM)
import Stella.Compiler.Elaborate.Driver.Generalize (Hindrance(..)) as Hindrance
import Stella.Compiler.Elaborate.Driver.Generalize (Commitment(..), Finalization(..), Hindrance, Preparation(..), commitGeneralization, finalizeGeneralization, prepareGeneralizationM)
import Stella.Compiler.Elaborate.Driver.Close (Closing(..), Undoing(..), closeRowsM)
import Stella.Compiler.Elaborate.Environment.Catalog (CatalogEntry, EntrySort(..), XScheme)
import Stella.Compiler.Elaborate.CorePlus.Row (rebuild, xnf)
import Stella.Compiler.Elaborate.Protocol.Guest (synthesizerType)
import Stella.Compiler.Elaborate.Environment.Imported (sessionEnvOf)
import Stella.Compiler.Elaborate.Environment.Implicit (cyclicComponents)
import Stella.Compiler.Elaborate.Environment.Operations (HandledEffect)
import Stella.Compiler.Interface.Operation (Operation, operationOf, operationScheme)
import Stella.Compiler.Elaborate.Environment.Surface (SurfaceBinding(..), SurfaceEnv, takesSynthesized)
import Stella.Compiler.Elaborate.Kernel.Elab (Outcome(..), SessionEnv, SolverState, atLevel, equate, freshTypeMeta, initialState)
import Stella.Compiler.Elaborate.Mechanism.Obligation (Basis(..))
import Stella.Compiler.Elaborate.Mechanism.TermMeta (zonkExpr)
import Stella.Compiler.Elaborate.Mechanism.Pending (Job(JobSynthesis), Site)
import Stella.Compiler.Elaborate.Mechanism.Unify (MetaContext, UnifyError(..), substitute, substituteKind)
import Stella.Compiler.Elaborate.Surface.Match (Witness)
import Stella.Compiler.Elaborate.Surface.Expr (CellReference, CellRegion, ExpressionHole, PendingCase, UncoveredMatch, Parameter(..), asArrow, checkDefinition, elaborateComputation, elaborateHandler, elaborateValue, expandable, handlerReferences, inferDefinition, references, runSurf)
import Stella.Compiler.Elaborate.Surface.Type (Elaborated, TypeHole, Unsupported(..), Wildcard, elaborateComputationSignature, elaborateSignature, elaborateValueSignature, schemeOf, settledScheme)
import Stella.Compiler.Elaborate.Vocabulary.Diagnostic (Defect(..), Diagnostic(..), Warning)
import Stella.Compiler.Elaborate.Vocabulary.Handle (SessionId(..))
import Stella.Compiler.Elaborate.Surface.Group (groups)
import Stella.Compiler.ForeignBoundary (Refused, crossingOf)
import Stella.Compiler.Interface.Assemble (CoreInterface, CoreTypeSort(..), coreAttribute, reachedFromOutside)
import Stella.Compiler.Interface.Module (Exports, TypeEntity(..), Via(..))
import Stella.Compiler.Interface.Prim (primAttribute)
import Stella.Compiler.Interface.Scheme (Scheme, plainScheme)
import Stella.Compiler.Surface.Decl (Declaration(..))
import Stella.Compiler.Surface.Decl (Attribute, HandlerDeclaration, Module) as Surface
import Stella.Compiler.Surface.Expr (Binder, Expr) as Surface
import Stella.Compiler.Surface.Expr (ClauseForm(..), binderOrigin)
import Stella.Compiler.Surface.Type (Type(..)) as Surface
import Stella.Compiler.Surface.Type (typeOrigin)
import Stella.Compiler.Surface.Origin (Origin) as Surface
import Stella.Compiler.Surface.Name (CellVar(..))
import Stella.Compiler.TypedCore (Decl(DeclAttribute, DeclData, DeclEffect, DeclForeign), Module) as Core
import Stella.Compiler.TypedCore (Attribute, AttributeDecl, DataDecl, DeclError(..), DeclFailure, Decl(DeclNonRec, DeclRec), Declared, EffectDecl, Export(..), ForeignDecl, declareAnnotated)
import Stella.Compiler.TypedCore.Declare (ctorInfo, dataEntry)
import Stella.Compiler.TypedCore.AttributeCheck (AttributeError, checkAttribute)
import Stella.Compiler.TypedCore.Check (CheckError(NotAValueForm), isValueForm)
import Stella.Compiler.TypedCore.Prim (asFunction)
import Stella.Compiler.TypedCore.Term (Expr(..), subterms) as Core
import Stella.Compiler.TypedCore.Initialization (localGroupViolations, topLevelViolations)
import Stella.Compiler.TypedCore.Reference (globalsOf, runtimeDependencies)
import Stella.Compiler.TypedCore.Name (EffName(..), Ident(..), KindVar(..), ModuleName, OpName(..), Qualified(..), TyName(..), TyVar, unqualified)
import Stella.Compiler.TypedCore.Signature (CanonicalClass(..), Signature, TyConInfo(..))
import Stella.Compiler.TypedCore.Kind (Kind(..), KindScheme, RowElemKind(..))
import Stella.Compiler.TypedCore.Kind as Kind
import Stella.Compiler.TypedCore.Type (RowEntry(..), RowKey(EffectKey), Type(..), TypeScheme, compareRowKeys, freeTypeVars, rowEntryKey)
import Stella.Compiler.TypedCore.Equality (schemeEquiv)
import Stella.Compiler.Primitive (abiTypeDescriptors, runtimeEntryNamed, schemeOfRuntimeEntry)

data ElaborationError
  -- | A form this version does not elaborate, or one resolution reported.
  = Unsupported Unsupported
  -- | A value without a signature whose type its right-hand side leaves
  -- | undecided where that is no value form, or whose synthesis would cross a
  -- | quantifier: a signature decides it.
  | SignatureNeeded Surface.Origin (Qualified Ident)
  -- | A constraint naming the type variable given, which a `forall` inside the
  -- | value binds, where the constraint arose: the value's scheme would leave
  -- | the variable free.
  | ConstraintEscapes Surface.Origin TyVar
  -- | A synthesis nothing decided, where it is asked for.
  | SynthesisUndecided Surface.Origin
  -- | A synthesizer named by a synthesized parameter, where it is written, whose
  -- | scheme is not the one a synthesizer is invoked at: `Stella.Elab.Handle
  -- | -{( Stella.Elab.Kernel )}-> Stella.Elab.Handle`.
  | SynthesizerIllTyped Surface.Origin (Qualified Ident)
  -- | A synthesizer named by a synthesized parameter, where it is written, that the
  -- | module being compiled declares: a synthesizer runs from a module compiled
  -- | before this one.
  | SynthesizerNotBuilt Surface.Origin (Qualified Ident)
  -- | A condition a declaration whose signature is partial needs, which the
  -- | signature does not write, where it arose: a partial signature gains none.
  | ConstraintUnwritten Surface.Origin
  -- | A kind nothing decided, where it was left unwritten: a binder, or a
  -- | constructor instantiated at fresh kinds.
  | KindUndetermined Surface.Origin
  -- | An equation, or an obligation, that does not hold.
  | Rejected Diagnostic
  -- | An equation nothing decided, where it was stated.
  | EquationUndecided Origin
  -- | A type nothing decided, where it stands.
  | TypeUndetermined Surface.Origin
  -- | A declaration with an equation left unattempted: the loop stopped at a
  -- | failure of another declaration before reaching it.
  | LeftUnchecked Surface.Origin (Qualified Ident)
  -- | The mechanism used against its contract, which is the elaborator's fault.
  | Broken Defect
  -- | An attribute a declaration carries whose arguments do not check against
  -- | its declaration, where the declaration stands.
  | AttributeRejected Surface.Origin AttributeError
  -- | A foreign whose type does not cross to the host, where it is declared.
  | ForeignRefused Surface.Origin (Qualified Ident) Refused
  -- | A foreign naming an entry the runtime carries out, declared at another
  -- | scheme than the ABI declares the entry at, where it is declared.
  | AbiEntryMismatch Surface.Origin (Qualified Ident) { expected :: TypeScheme, declared :: TypeScheme }
  -- | A foreign type naming a type constructor the ABI supplies, declared of
  -- | another kind, or of another class, than the ABI gives it, where it is
  -- | declared.
  | AbiTypeMismatch Surface.Origin (Qualified TyName) { expected :: KindScheme, declared :: KindScheme }
  -- | A typed hole an annotation holds, where it is written, by its name and
  -- | the type standing for it as far as it is decided.
  | TypeHoleStands Surface.Origin String XType
  -- | A `case` that leaves values uncovered, where it is written, and a
  -- | vector of values it does not match. This version reports such a match,
  -- | `Prelude.Partial` not being supplied.
  | NonExhaustiveMatch Surface.Origin (Array (Witness XType))
  -- | An expression hole, where it is written, by its name, the type it
  -- | stands for as far as it is decided, and the locals in scope there that
  -- | source can name, each at its type.
  | ExpressionHoleStands Surface.Origin String XType (Array { name :: Ident, type :: XType })
  -- | Implicit handlers the module and its imports make available together that
  -- | lower into one another, where the module's header stands: the members of
  -- | one strongly connected component, in the order of their identities.
  | ImplicitCycle Surface.Origin (Array (Qualified Ident))
  -- | An implicit handler declaration failing a condition of being one, where
  -- | what fails it stands.
  | ImplicitCondition Surface.Origin ImplicitProblem
  -- | What a `Λ` or a constraint abstraction encloses that is no value form,
  -- | where the abstraction stands: the Core checker's refusal, and the
  -- | author's.
  | ValueFormNeeded Surface.Origin
  -- | A definition generalized over kinds whose right-hand side is no value,
  -- | where it is declared: the Core checker's refusal, and the author's (D52).
  | KindValueNeeded Surface.Origin (Qualified Ident)
  -- | A right-hand side of a recursive group reading, while the group is
  -- | initialized, a member not written before it: where the reference stands,
  -- | where the form that made the read immediate stands, if one did, the
  -- | member whose right-hand side it is, and the member read.
  | ReadWhileInitializing Surface.Origin (Maybe Surface.Origin) (Qualified Ident) (Qualified Ident)
  -- | A right-hand side of a local recursive group reading, while the group is
  -- | initialized, a member not written before it, as a top-level one does:
  -- | the member read by the name the group binds it to.
  | LocalReadWhileInitializing Surface.Origin (Maybe Surface.Origin) Ident Ident
  -- | A Core module the Core checker refused, which is the elaborator's fault.
  | CoreRefused (DeclFailure Surface.Origin)
  -- | An entry a desugaring of the compiler's refers to, which a signature
  -- | reaching its module lacks or holds at another scheme than the one listed:
  -- | the compiler's fault.
  | InternalEntryMismatch (Qualified Ident)
  -- | An entry a desugaring of the compiler's refers to, which the module
  -- | declaring it lacks or declares at another scheme than the one listed,
  -- | where it is declared, or where the module is where it lacks one.
  | InternalEntryDeclared Surface.Origin (Qualified Ident) { expected :: TypeScheme, declared :: Maybe TypeScheme }
  -- | A declaration whose effect rows nothing decided, where its fits stand.
  | EffectRowAmbiguous (Qualified Ident) (Array Surface.Origin)
  -- | An attempt that postponed itself, which nothing the elaborator states
  -- | does: it is the elaborator's fault.
  | AttemptPostponed

-- | Which condition of an implicit handler a declaration fails.
data ImplicitProblem
  -- | Its signature does not write `E ~> ( … )` itself.
  = ImplicitNotCapability
  -- | Its clause for the operation named is not `fast`.
  | ImplicitClauseNotFast (Qualified Ident)
  -- | It has a return clause.
  | ImplicitReturnClause
  -- | It takes parameters.
  | ImplicitParameters
  -- | The initial value of the cell named is no value form.
  | ImplicitInitialNotValue String

-- | A value declaration elaborated: its name, where it was declared and its
-- | ordinal among the module's declarations, its attributes, its scheme, and
-- | its definition as a Core term, located by the Surface AST, and as the
-- | initialization of a recursive group is judged on it.
type ElaboratedValue =
  { name :: Qualified Ident
  , origin :: Surface.Origin
  , ordinal :: Int
  , attributes :: Array Attribute
  , scheme :: TypeScheme
  , spine :: Scheme
  , body :: Core.Expr Surface.Origin
  , initialization :: Core.Expr Surface.Origin
  }

-- | A value declaration whose body is elaborated, its equations not yet all
-- | decided: those left are jobs of the state it was elaborated into. Its
-- | annotations' typed holes and wildcards, and its expression holes, are
-- | reported once it is settled.
type Elaborating =
  { name :: Qualified Ident
  , origin :: Surface.Origin
  , ordinal :: Int
  , attributes :: Array Attribute
  , scheme :: TypeScheme
  , spine :: Scheme
  , body :: XExpr Surface.Origin
  , holes :: Array TypeHole
  , wildcards :: Array Wildcard
  , unwritten :: Array { origin :: Surface.Origin, kind :: XKind }
  , expressionHoles :: Array ExpressionHole
  , uncovered :: Array UncoveredMatch
  , pending :: Array PendingCase
  , regions :: Array CellRegion
  , references :: Array CellReference
  }

-- | A data declaration elaborated, and where it stands.
type ElaboratedData = { origin :: Surface.Origin, decl :: DataDecl }

-- | A type synonym elaborated: where it stands, its attributes, its name, and
-- | what an interface holds of it.
type ElaboratedSynonym = { origin :: Surface.Origin, attributes :: Array Surface.Attribute, name :: Qualified TyName, entry :: SynonymEntry }

-- | An effect elaborated: where it stands, its name, its Core declaration, and
-- | the arguments each operation is written with.
type ElaboratedEffect = { origin :: Surface.Origin, name :: Qualified EffName, decl :: EffectDecl, arguments :: Array (Array Type) }

-- | The operations of an effect the module declares, each by the qualified name
-- | it is referred to by.
localOperations :: ModuleName -> ElaboratedEffect -> Array (Tuple (Qualified Ident) Operation)
localOperations m e = Array.zipWith
  (\o arguments -> Tuple (Qualified m (identOf o.name)) (operationOf e.name e.decl.params { name: o.name, binders: o.tyBinders, arguments, resumesWith: o.resumesWith }))
  e.decl.operations
  e.arguments
  where
  identOf (OpName n) = Ident n

-- | An effect the module declares, as a handler reads it.
localEffect :: ModuleName -> ElaboratedEffect -> Tuple (Qualified EffName) HandledEffect
localEffect m e = Tuple e.name { params: e.decl.params, operations: map (\o -> Qualified m (identOf o.name)) e.decl.operations }
  where
  identOf (OpName n) = Ident n

-- | A foreign type elaborated: where it stands, its attributes, its name, and
-- | its kind scheme.
type ElaboratedForeignType = { origin :: Surface.Origin, attributes :: Array Surface.Attribute, name :: Qualified TyName, kind :: KindScheme }

-- | A foreign elaborated, its type one that crosses to the host: where it
-- | stands, its name, its Core declaration, and its scheme as an interface
-- | holds it.
type ElaboratedForeign = { origin :: Surface.Origin, name :: Qualified Ident, decl :: ForeignDecl, spine :: Scheme }

-- | An attribute declaration elaborated, and where it stands.
type ElaboratedAttribute = { origin :: Surface.Origin, decl :: AttributeDecl }

-- | Elaborate the module's declarations against the signature and the catalog
-- | its imports give.
elaborateValues
  :: Signature
  -> SurfaceEnv
  -> Array CatalogEntry
  -> Surface.Module
  -> { data :: Array ElaboratedData, synonyms :: Array ElaboratedSynonym, foreignTypes :: Array ElaboratedForeignType, effects :: Array ElaboratedEffect, foreigns :: Array ElaboratedForeign, attributes :: Array ElaboratedAttribute, values :: Array ElaboratedValue, errors :: Array ElaborationError, warnings :: Array Warning }
elaborateValues imports surface importedEntries m = case elaborateValuesM (identically <<< attemptPending) imports surface importedEntries m of
  Identity result -> result

-- | `elaborateValues`, each job carried out in the monad the attempter the
-- | function given makes of the module's session carries its attempts out in.
elaborateValuesM
  :: forall m
   . MonadRec m
  => (SessionEnv -> AttempterM m)
  -> Signature
  -> SurfaceEnv
  -> Array CatalogEntry
  -> Surface.Module
  -> m { data :: Array ElaboratedData, synonyms :: Array ElaboratedSynonym, foreignTypes :: Array ElaboratedForeignType, effects :: Array ElaboratedEffect, foreigns :: Array ElaboratedForeign, attributes :: Array ElaboratedAttribute, values :: Array ElaboratedValue, errors :: Array ElaborationError, warnings :: Array Warning }
elaborateValuesM attempterOf imports surface importedEntries m =
  if Array.null dataErrors then do
    generalized <- Array.foldRecM generalizeOne
      { state: attributesRead.state
      , bindings: Map.empty
      , values: []
      , unavailable: Set.union unread (Set.fromFoldable (Array.mapMaybe (either (Just <<< _.name) (const Nothing)) unsignedRead))
      , errors: Array.mapMaybe (either (Just <<< _.error) (const Nothing)) unsignedRead
      , warnings: []
      }
      (groups (map (\u -> Set.fromFoldable (Array.mapMaybe (\n -> Map.lookup n unsignedIndex) (Array.fromFoldable (references u.body)))) unsigned))
    let bodies = bodiesOf generalized
    settled' <- settleBodiesM session attempter bodies.state bodies.bodies
    pure
      { data: elaboratedData
      , synonyms: types.synonyms
      , foreignTypes: types.foreignTypes
      , effects: types.effects
      , foreigns: crossing.foreigns
      , attributes: attributesRead.declared
      , values: Array.sortWith _.ordinal (generalized.values <> settled'.values)
      , errors: internalErrors <> unsupported <> signatureErrors <> partialErrors <> crossing.errors <> attributesRead.errors <> cycleErrors <> generalized.errors <> attributeErrorsOf generalized <> bodies.errors <> settled'.errors
      , warnings: generalized.warnings
      }
  else pure { data: [], synonyms: [], foreignTypes: [], effects: [], foreigns: [], attributes: [], values: [], errors: dataErrors <> unsupported, warnings: [] }
  where
  initial0 = initialState (SessionId 0) 1_000_000

  -- the type declarations, every head before anything a head names
  typeDeclarations =
    { order: Array.mapMaybe
        ( case _ of
            DeclData d -> Just d.name
            DeclNewtype d -> Just d.name
            DeclSynonym d -> Just d.name
            _ -> Nothing
        )
        m.declarations
    , data: Array.mapMaybe
        ( case _ of
            DeclData d -> Just { origin: d.origin, attributes: d.attributes, name: d.name, kind: d.kind, params: d.params, constructors: d.constructors, isNewtype: false }
            DeclNewtype d -> Just { origin: d.origin, attributes: d.attributes, name: d.name, kind: d.kind, params: d.params, constructors: [ { origin: d.constructor.origin, name: d.constructor.name, fields: [ d.constructor.field ] } ], isNewtype: true }
            _ -> Nothing
        )
        m.declarations
    , synonyms: Array.mapMaybe
        ( case _ of
            DeclSynonym d -> Just d
            _ -> Nothing
        )
        m.declarations
    , foreignTypes: Array.mapMaybe
        ( case _ of
            DeclForeignType d -> Just d
            _ -> Nothing
        )
        m.declarations
    , effects: Array.mapMaybe
        ( case _ of
            DeclEffect d -> Just d
            _ -> Nothing
        )
        m.declarations
    }
  typesRead = case readTypes (sessionEnvOf imports importedEntries) surface.synonyms typeDeclarations initial0 of
    Tuple (Done reads) s -> { types: settledTypes s.tentative.metas reads, errors: [], state: s }
    Tuple outcome _ -> { types: { data: [], synonyms: [], foreignTypes: [], effects: [], unsupported: [] }, errors: [ failure outcome ], state: initial0 }
  initial = typesRead.state
  types = typesRead.types
  elaboratedData = types.data

  -- the signature and the catalog the values are elaborated against: the
  -- imports', with the data types, their constructors, the foreign types, and
  -- the effects the module declares
  signature = foldl addEffect (foldl addForeignType (foldl (addData m.name) imports (map _.decl elaboratedData)) types.foreignTypes) types.effects
  dataErrors = typesRead.errors <> map Unsupported types.unsupported <> Array.mapMaybe abiTypeMismatch types.foreignTypes
  -- a foreign type naming a type the ABI supplies is that type, of the kind
  -- and the class the ABI gives it, or not declared at all
  abiTypeMismatch f = case Array.find (\t -> t.name == f.name) abiTypeDescriptors of
    Just t | t.canonical /= CanonicalOpaque || not (sameKindScheme t.kind f.kind) -> Just (AbiTypeMismatch f.origin f.name { expected: t.kind, declared: f.kind })
    _ -> Nothing
  -- the synonyms the values' types are read through, the operations they
  -- call, and the effects they handle: the imports', and the module's own
  withSynonyms = surface
    { synonyms = Map.union (Map.fromFoldable (map (\s -> Tuple s.name s.entry) types.synonyms)) surface.synonyms
    , operations = Map.union (Map.fromFoldable (Array.concatMap (localOperations m.name) types.effects)) surface.operations
    , effects = Map.union (Map.fromFoldable (map (localEffect m.name) types.effects)) surface.effects
    }
  -- the entries the compiler's desugarings refer to, read off it
  Tuple internal internalErrors = case internalEntries m.name signature of
    Right entries -> Tuple entries []
    Left name -> Tuple Map.empty [ InternalEntryMismatch name ]
  constructorEntries = Array.concatMap (constructorsOf m.name) (map _.decl elaboratedData)
  imported = importedEntries <> constructorEntries

  -- the value declarations, and what else the module declares; a fixity
  -- gives Core nothing
  candidates = Array.catMaybes (Array.mapWithIndex candidate m.declarations)
  candidate ordinal = case _ of
    -- a value without a signature is generalized instead
    DeclValue d -> d.signature <#> \signature' -> case traverse coreAttribute d.attributes of
      Left o -> Left (Unsupported (ReportedAlready o))
      Right attributes -> Right
        { declared: { name: d.name, origin: d.origin, ordinal, attributes, definition: Right (ValueBody d.params d.body) }
        , read: \synonyms -> elaborateValueSignature synonyms d.name signature'
        }
    -- a foreign is read as a value's signature is, and has no body
    DeclForeign d -> Just case traverse coreAttribute d.attributes of
      Left o -> Left (Unsupported (ReportedAlready o))
      Right attributes -> Right
        { declared: { name: d.name, origin: d.origin, ordinal, attributes, definition: Left d.observation }
        , read: \synonyms -> elaborateSignature synonyms d.name d.signature
        }
    -- a computation's signature is read as its Core type, a thunk
    DeclComputation d -> Just case traverse coreAttribute d.attributes of
      Left o -> Left (Unsupported (ReportedAlready o))
      Right attributes -> Right
        { declared: { name: d.name, origin: d.origin, ordinal, attributes, definition: Right (ComputationBody d.body) }
        , read: \synonyms -> elaborateComputationSignature synonyms d.name d.signature
        }
    -- a handler declaration is a value at its signature's type, `~>` read as
    -- the function it stands for
    DeclHandler d -> Just case traverse coreAttribute d.attributes of
      Left o -> Left (Unsupported (ReportedAlready o))
      Right attributes -> Right
        { declared: { name: d.name, origin: d.origin, ordinal, attributes, definition: Right (HandlerDefinition d) }
        , read: \synonyms -> elaborateSignature synonyms d.name d.signature
        }
    DeclAttribute _ -> Nothing
    DeclData _ -> Nothing
    DeclNewtype _ -> Nothing
    DeclSynonym _ -> Nothing
    DeclForeignType _ -> Nothing
    DeclEffect _ -> Nothing
    DeclFixity _ -> Nothing
    DeclTypeFixity _ -> Nothing
  unsupported = Array.mapMaybe
    ( case _ of
        Left e -> Just e
        Right _ -> Nothing
    )
    candidates
  written = Array.mapMaybe
    ( case _ of
        Right c -> Just c
        Left _ -> Nothing
    )
    candidates

  importedSession = sessionEnvOf signature imported

  -- every signature read, as one attempt each
  read = foldl readOne { state: initial, read: [], errors: [] } written
  readOne acc c =
    case runAttempt importedSession (c.read withSynonyms.synonyms) acc.state of
      Tuple (Done e) s
        | Array.null e.unsupported -> acc { state = s, read = Array.snoc acc.read (Tuple c.declared e) }
        | otherwise -> acc { errors = acc.errors <> map Unsupported e.unsupported }
      Tuple outcome _ -> acc { errors = Array.snoc acc.errors (failure outcome) }

  -- their schemes, once every kind is decided; a partial signature's is
  -- complete only once its body decides what it holds
  isPartial e = not (Array.null e.holes && Array.null e.wildcards)
  settled = map (\(Tuple d e) -> Tuple d (map (\scheme -> { scheme, spine: schemeOf e scheme }) (settledScheme read.state.tentative.metas e))) (Array.filter (not <<< isPartial <<< snd) read.read)
  -- a declaration whose signature is partial is inferred with the values
  -- without one, its scheme published once its group is committed; a
  -- synthesized parameter on its spine is supplied by a goal, which this
  -- version does not create
  partialRead = Array.filter (isPartial <<< snd) read.read
  partialErrors = Array.mapMaybe
    (\(Tuple d e) -> if Array.null e.synthesized then Nothing else Just (Unsupported (OutsideSubset d.origin "a partial signature taking a synthesized parameter")))
    partialRead
  partials = Array.mapMaybe
    ( \(Tuple d e) -> case d.definition of
        Right (ValueBody params body) | Array.null e.synthesized -> Just { name: d.name, origin: d.origin, ordinal: d.ordinal, attributes: d.attributes, params, body, signature: Just e }
        Right (ComputationBody body) | Array.null e.synthesized -> Just { name: d.name, origin: d.origin, ordinal: d.ordinal, attributes: d.attributes, params: [], body, signature: Just e }
        _ -> Nothing
    )
    partialRead
  schemes = Array.mapMaybe
    ( \(Tuple d s) -> case s of
        Right r | not (Set.member d.name illNamed) -> Just { declared: d, scheme: r.scheme, spine: r.spine }
        _ -> Nothing
    )
    settled
  -- a synthesized parameter names a synthesizer an import reaches, at the type
  -- one is invoked at, where it is written: one this module declares has no
  -- bytecode to run yet. A signature naming either gives no scheme
  illTyped = Array.concatMap
    (\(Tuple d e) -> Array.mapMaybe (\mark -> map (\error -> { name: d.name, error }) (refusal mark)) e.synthesized)
    (Array.filter (not <<< isPartial <<< snd) read.read)
  illNamed = Set.fromFoldable (map _.name illTyped)
  refusal mark = case mark.synthesizer of
    Qualified owner _
      | owner == m.name -> Just (SynthesizerNotBuilt mark.at mark.synthesizer)
      | maybe false isSynthesizerScheme (Map.lookup mark.synthesizer synthesizers) -> Nothing
      | otherwise -> Just (SynthesizerIllTyped mark.at mark.synthesizer)
  synthesizers = Map.fromFoldable (map (\entry -> Tuple entry.name entry.scheme) imported)
  signatureErrors = read.errors <> map _.error illTyped <> Array.concatMap
    ( \(Tuple _ s) -> case s of
        Left places -> map KindUndetermined (NonEmptyArray.toArray places)
        Right _ -> []
    )
    settled

  -- the implicit handlers the search may take: those the imports publish, and
  -- each one the module declares, exported or not, once its signature is read
  -- and it meets the conditions read off its declaration; one whose cell is
  -- initialized otherwise than by a value form is taken all the same, the
  -- module failing once its body is elaborated
  implicits = surface.implicits <> Array.mapMaybe ownImplicit schemes
  ownImplicit v = case v.declared.definition of
    Right (HandlerDefinition h)
      | h.implicit
      , Array.null (implicitFailures h)
      , Just e <- capabilityElements h.handled v.scheme.body
      , closedElements e -> Just { handler: v.declared.name, source: e.source, targets: e.targets, scheme: v.scheme }
    _ -> Nothing
  -- the handlers among them that lower into one another, reported where the
  -- module's imports are, whether or not a boundary would take one
  cycleErrors = map (ImplicitCycle m.origin) (cyclicComponents implicits)

  -- the values, each with its body
  defined = Array.mapMaybe (\v -> either (const Nothing) (\d -> Just { declared: v.declared, scheme: v.scheme, spine: v.spine, definition: d }) v.declared.definition) schemes
  -- what a foreign takes and gives must cross to the host, which its type
  -- decides where it is declared; an entry the runtime carries out crosses to
  -- no host, and is declared at the scheme the ABI declares it at
  crossing = foldl crossOne { foreigns: [], errors: [] } (Array.filter (isForeignDefinition <<< _.declared.definition) schemes)
  crossOne acc v = case runtimeEntryNamed v.declared.name of
    Just entry ->
      let
        expected = schemeOfRuntimeEntry entry.id
      in
        if schemeEquiv v.scheme expected then accepted acc v
        else acc { errors = Array.snoc acc.errors (AbiEntryMismatch v.declared.origin v.declared.name { expected, declared: v.scheme }) }
    Nothing -> case crossingOf signature v.scheme of
      Right _ -> accepted acc v
      Left refused -> acc { errors = Array.snoc acc.errors (ForeignRefused v.declared.origin v.declared.name refused) }
  accepted acc v = acc { foreigns = Array.snoc acc.foreigns { origin: v.declared.origin, name: v.declared.name, decl: { name: unqualified v.declared.name, scheme: v.scheme, attributes: v.declared.attributes }, spine: v.spine } }

  -- the attribute declarations, their parameters' types closed and read
  -- against the module's types
  attributeDeclarations = Array.mapMaybe
    ( case _ of
        DeclAttribute d -> Just d
        _ -> Nothing
    )
    m.declarations
  attributesRead = foldl readAttribute { state: read.state, declared: [], errors: [] } attributeDeclarations
  readAttribute acc d =
    case runAttempt importedSession (readAttributeDeclaration withSynonyms.synonyms d) acc.state of
      Tuple (Done (Right decl)) s -> acc { state = s, declared = Array.snoc acc.declared { origin: d.origin, decl } }
      Tuple (Done (Left refused)) _ -> acc { errors = acc.errors <> map Unsupported refused.unsupported <> map KindUndetermined refused.undetermined }
      Tuple outcome _ -> acc { errors = Array.snoc acc.errors (failure outcome) }

  -- an attribute on a declaration with no Core form is checked here, once
  -- the scheme of every value and foreign of the module is known, a constant
  -- naming one, and every attribute declaration of the module
  attributeSignature generalized =
    foldl (\s a -> s { attributes = Map.insert (Qualified m.name a.decl.name) { positional: a.decl.positional, keyword: a.decl.keyword } s.attributes })
      ( foldl (\s v -> s { values = Map.insert v.name { scheme: v.scheme, isForeign: false } s.values })
          (foldl (\s v -> s { values = Map.insert v.declared.name { scheme: v.scheme, isForeign: isForeignDefinition v.declared.definition } s.values }) signature schemes)
          generalized.values
      )
      attributesRead.declared
  attributeErrorsOf generalized = Array.concatMap
    ( \d -> Array.mapMaybe
        ( \a -> case coreAttribute a of
            Right attribute -> either (Just <<< AttributeRejected d.origin) (const Nothing) (checkAttribute (attributeSignature generalized) attribute)
            Left _ -> Nothing
        )
        d.attributes
    )
    (map (\s -> { origin: s.origin, attributes: s.attributes }) types.synonyms <> map (\f -> { origin: f.origin, attributes: f.attributes }) types.foreignTypes)

  -- the catalog the bodies are elaborated against: what the imports publish,
  -- and every value and foreign the module declares at its scheme, with its
  -- attributes
  own = map (\v -> { name: v.declared.name, sort: if isForeignDefinition v.declared.definition then ForeignEntry else ValueEntry, scheme: { kindVars: v.scheme.kindVars, body: fromCore v.scheme.body }, attributes: v.declared.attributes }) schemes
  session = sessionEnvOf signature (imported <> own)
  -- what the bodies read beyond: the module's values taking a synthesized
  -- argument, at their spines, among those the imports declare
  withOwn = withSynonyms { synthesizing = Map.union (Map.fromFoldable (map (\v -> Tuple v.declared.name v.spine.body) (Array.filter (takesSynthesized <<< _.spine) schemes))) withSynonyms.synthesizing }

  -- the values without a signature
  unsignedRead = Array.catMaybes (Array.mapWithIndex unsignedOf m.declarations)
  unsignedOf ordinal = case _ of
    DeclValue d | Nothing <- d.signature -> Just case traverse coreAttribute d.attributes of
      Left o -> Left { name: d.name, error: Unsupported (ReportedAlready o) }
      Right attributes -> Right { name: d.name, origin: d.origin, ordinal, attributes, params: d.params, body: d.body, signature: Nothing }
    _ -> Nothing
  -- the values, computations, and foreigns with a signature that gave no
  -- scheme, which a reference to them cannot be checked against
  unread = Set.difference
    ( Set.fromFoldable
        ( Array.mapMaybe
            ( case _ of
                DeclValue d -> d.signature $> d.name
                DeclComputation d -> Just d.name
                DeclHandler d -> Just d.name
                DeclForeign d -> Just d.name
                _ -> Nothing
            )
            m.declarations
        )
    )
    (Set.fromFoldable (map _.declared.name schemes <> map _.name partials))
  unsigned = Array.sortWith _.ordinal (Array.mapMaybe (either (const Nothing) Just) unsignedRead <> partials)
  unsignedIndex = Map.fromFoldable (Array.mapWithIndex (\i u -> Tuple u.name i) unsigned)

  -- each strongly connected component of the references they make to one
  -- another a group, generalized in dependency order before any body with a
  -- signature is elaborated, and published whole once committed; one
  -- referring to a value with no scheme — one without a signature its group
  -- did not generalize, or one whose signature gave none — is left unchecked
  attempter = attempterOf session
  generalizeOne acc g =
    let
      members = Array.mapMaybe (Array.index unsigned) g.members
      named = Set.fromFoldable (map _.name members)
    in
      -- a group a member of which refers to what has no scheme is not
      -- elaborated, none of its members being generalizable without it
      case NonEmptyArray.fromArray members of
        Nothing -> pure acc
        Just _ | Array.any (\u -> meets (references u.body) acc.unavailable) members ->
          pure acc { unavailable = Set.union acc.unavailable named, errors = acc.errors <> map (\u -> LeftUnchecked u.origin u.name) members }
        Just group ->
          generalizeGroup session attempter internal (withOwn { bindings = acc.bindings }) (\n -> Map.member n signature.ctors) group acc.state <#> \done ->
            case done.result of
              Left errors -> acc { state = done.state, unavailable = Set.union acc.unavailable named, errors = acc.errors <> errors }
              Right r -> acc
                { state = done.state
                , bindings = foldl (\b v -> Map.insert v.name (Final v.scheme) b) acc.bindings r.values
                , values = acc.values <> r.values
                , warnings = acc.warnings <> r.warnings
                }

  -- every body, as one attempt each, a body that does not elaborate leaving
  -- nothing behind; one referring to a value with no scheme is left unchecked
  bodiesOf generalized = foldl (bodyOne generalized) { state: generalized.state, bodies: [], errors: [] } defined
  bodyOne generalized acc v = case v.definition of
    ValueBody _ body | meets (references body) generalized.unavailable -> unchecked acc v
    ComputationBody body | meets (references body) generalized.unavailable -> unchecked acc v
    HandlerDefinition h | meets (handlerReferences h) generalized.unavailable -> unchecked acc v
    ValueBody params body -> attemptBody acc v (elaborateValue internal (withFinal generalized) v.declared.name v.declared.origin v.scheme params body)
    -- a synthesized parameter is supplied by a goal, which this version does
    -- not create, and a computation has no parameter to bind it to
    ComputationBody _ | takesSynthesized v.spine -> acc { errors = Array.snoc acc.errors (Unsupported (OutsideSubset v.declared.origin "a computation taking a synthesized parameter")) }
    ComputationBody body -> attemptBody acc v (elaborateComputation internal (withFinal generalized) v.declared.name v.declared.origin v.scheme body)
    -- a synthesized parameter is not among the parameters a handler
    -- declaration writes
    HandlerDefinition _ | takesSynthesized v.spine -> acc { errors = Array.snoc acc.errors (Unsupported (OutsideSubset v.declared.origin "a handler declaration taking a synthesized parameter")) }
    -- an implicit handler is sought by the effects it removes and performs,
    -- which this version reads only where they mention no variable; its body
    -- is elaborated either way
    HandlerDefinition h -> attemptBody (openElements h v acc) v (elaborateHandler internal (withFinal generalized) v.declared.name v.declared.origin v.scheme h)
  attemptBody acc v elaborating =
    case runAttempt session (runSurf elaborating) acc.state of
      Tuple (Done (Right built)) s -> acc { state = s, bodies = Array.snoc acc.bodies { name: v.declared.name, origin: v.declared.origin, ordinal: v.declared.ordinal, attributes: v.declared.attributes, scheme: v.scheme, spine: v.spine, body: built.value, holes: built.holes, wildcards: built.wildcards, unwritten: built.unwritten, expressionHoles: built.expressionHoles, uncovered: built.uncovered, pending: built.pending, regions: built.regions, references: built.references } }
      Tuple (Done (Left problem)) _ -> acc { errors = Array.snoc acc.errors (Unsupported problem) }
      Tuple outcome _ -> acc { errors = Array.snoc acc.errors (failure outcome) }
  unchecked acc v = acc { errors = Array.snoc acc.errors (LeftUnchecked v.declared.origin v.declared.name) }
  openElements h v acc
    | h.implicit, isJust h.capabilityTargets, not (maybe true closedElements (capabilityElements h.handled v.scheme.body)) =
        acc { errors = Array.snoc acc.errors (Unsupported (OutsideSubset v.declared.origin "an implicit handler whose effects mention a type or kind variable")) }
    | otherwise = acc
  withFinal generalized = withOwn { bindings = generalized.bindings }

-- | A signature with a data type the module declares, and its constructors.
addData :: ModuleName -> Signature -> DataDecl -> Signature
addData self sig decl =
  sig
    { types = Map.insert owner (dataEntry self decl) sig.types
    , ctors = foldl (\acc c -> Map.insert (Qualified self c.name) (ctorInfo owner decl c) acc) sig.ctors decl.constructors
    }
  where
  owner = Qualified self decl.name

-- | A signature with a foreign type the module declares: an opaque type of the
-- | module, which no Core declaration produces.
addForeignType :: Signature -> ElaboratedForeignType -> Signature
addForeignType sig f = sig { types = Map.insert f.name (IntrinsicTyCon f.kind CanonicalOpaque) sig.types }

-- | A signature with an effect the module declares, and its operations.
addEffect :: Signature -> ElaboratedEffect -> Signature
addEffect sig e = sig { effects = Map.insert e.name { params: e.decl.params, operations: Map.fromFoldable (map (\o -> Tuple o.name o) e.decl.operations) } sig.effects }

-- | The body a declaration defines: a value's, by its parameters, a
-- | computation's, which has none, or a handler declaration's.
data Body
  = ValueBody (Array Surface.Binder) Surface.Expr
  | ComputationBody Surface.Expr
  | HandlerDefinition Surface.HandlerDeclaration

-- | Whether a declaration's definition is a foreign's, which has no body.
isForeignDefinition :: forall a b. Either a b -> Boolean
isForeignDefinition = either (const true) (const false)

-- | The catalog entry of each constructor of a data type the module declares.
constructorsOf :: ModuleName -> DataDecl -> Array CatalogEntry
constructorsOf self decl = map entry decl.constructors
  where
  entry c =
    let
      scheme = (ctorInfo (Qualified self decl.name) decl c).scheme
    in
      { name: Qualified self c.name, sort: ConstructorEntry, scheme: { kindVars: scheme.kindVars, body: fromCore scheme.body }, attributes: [] }

-- | Run the jobs the bodies left to quiescence, each attempted by the attempter
-- | given, then make each body whose equations were all decided a Core term.
-- |
-- | **A body is a value only once everything stated for it holds.** The loop
-- | stops at the first failure, so where it stops, a declaration it names — the
-- | one a job it refused, or one it left undecided, belongs to — is reported by
-- | that, and any other with a job still waiting is reported as left
-- | unchecked. A defect leaves no body a value. A body made a value holding a
-- | type nothing decided is reported where that type stands.
settleBodies
  :: SessionEnv
  -> Attempter
  -> SolverState
  -> Array Elaborating
  -> { values :: Array ElaboratedValue, errors :: Array ElaborationError }
settleBodies session attempter state bodies = case settleBodiesM session (identically attempter) state bodies of
  Identity result -> result

-- | `settleBodies`, each job carried out in the monad the attempter given
-- | carries its attempts out in.
settleBodiesM
  :: forall m
   . MonadRec m
  => SessionEnv
  -> AttempterM m
  -> SolverState
  -> Array Elaborating
  -> m { values :: Array ElaboratedValue, errors :: Array ElaborationError }
settleBodiesM session attempter state bodies = do
  Tuple report quiet <- runAttemptingM attempter state
  -- at quiescence: the fits left undecided resolved by direction, the
  -- variants pending `case`s leave open closed for their sake and each such
  -- `case` replaced by its match, each declaration's rows nothing needs
  -- closed, the fits resolved again and the loop run to what it then waits
  -- on, every state handed on to the next
  Tuple settledBy after <- case report.result of
    Loop.Completed -> settling quiet
    Loop.Blocked _ -> settling quiet
    _ -> pure (Tuple Nothing quiet)
  pure (concluded report settledBy after)
  where
  componentErrors c = case c.outcome of
    Settled -> []
    Ambiguous a -> [ { error: EffectRowAmbiguous c.owner (Array.mapMaybe sourceOrigin a.origins), names: [ c.owner ] } ]
    Refused d -> [ { error: rejected d, names: Array.cons c.owner (diagnosticDeclarations d) } ]

  -- a body's rows closed, a defect stopping every later one; a closing
  -- undone is the declaration's report, the rows decided again without it
  -- need not fail as it did
  closing acc b = case acc of
    { defect: Nothing, state: s, undone } -> closeRowsM session attempter declarationOf b.name 0 [ { site: { context: emptyXContext, origin: InDeclaration b.name }, term: b.body, types: [] } ] s <#> case _ of
      Tuple (Left d) s' -> { defect: Just d, state: s', undone }
      Tuple (Right { closing: Undone u }) s' -> { defect: Nothing, state: s', undone: Map.insert b.name u.cause undone }
      Tuple (Right _) s' -> { defect: Nothing, state: s', undone }
    stopped -> pure stopped

  -- the variants the pending `case`s leave open closed for their sake, the
  -- loop run and the fits resolved by direction again, until none is left to
  -- close
  bounded s = case closableTails s.tentative.metas (Array.concatMap _.pending bodies) of
    Left d -> pure (Tuple (Left (brokenBy d)) s)
    Right [] -> pure (Tuple (Right unit) s)
    Right ts -> case closeTails session 0 ts s of
      Tuple (Done _) s1 -> do
        Tuple again s2 <- runAttemptingM attempter s1
        case again.result of
          Loop.Rejected d -> pure (Tuple (Left (rejectedBy d)) s2)
          Loop.Exhausted p -> pure (Tuple (Left { errors: [ EquationUndecided p.origin ], names: Just (Set.singleton (declarationOf p.origin)) }) s2)
          Loop.Halted d -> pure (Tuple (Left (brokenBy d)) s2)
          _ -> resolveByDirectionM session attempter declarationOf (const 0) s2 >>= case _ of
            Tuple (ResolutionHalted d) s3 -> pure (Tuple (Left (brokenBy d)) s3)
            Tuple (Resolution _) s3 -> bounded s3
      Tuple (Failed d) s1 -> pure (Tuple (Left (rejectedBy d)) s1)
      Tuple (Broke d) s1 -> pure (Tuple (Left (brokenBy d)) s1)
      Tuple outcome s1 -> pure (Tuple (Left { errors: [ failure outcome ], names: Just (Set.fromFoldable (map (declarationOf <<< _.site.origin) ts)) }) s1)

  -- what stops the settling: a refusal names the declarations its diagnostic
  -- is about, and a defect leaves nothing to trust
  rejectedBy d = { errors: [ rejected d ], names: Just (Set.fromFoldable (diagnosticDeclarations d)) }
  brokenBy d = { errors: [ Broken d ], names: Nothing }

  -- a body with each pending `case` it holds replaced by its match
  placed (Tuple acc s) b = case acc of
    Left e -> Tuple (Left e) s
    Right done -> case settlePending session 0 { term: b.body, pending: b.pending } s of
      Tuple (Left e@(Broken _)) s' -> Tuple (Left { errors: [ e ], names: Nothing }) s'
      Tuple (Left e) s' -> Tuple (Left { errors: [ e ], names: Just (Set.singleton b.name) }) s'
      Tuple (Right r) s' -> Tuple (Right (Array.snoc done b { body = r.term, uncovered = b.uncovered <> r.uncovered, pending = [] })) s'

  settling quiet = resolveByDirectionM session attempter declarationOf (const 0) quiet >>= case _ of
    Tuple (ResolutionHalted d) s1 -> pure (Tuple (Just (Left (brokenBy d))) s1)
    Tuple (Resolution _) s1 -> bounded s1 >>= case _ of
      Tuple (Left e) s2 -> pure (Tuple (Just (Left e)) s2)
      Tuple (Right _) s2 -> case foldl placed (Tuple (Right []) s2) bodies of
        Tuple (Left e) s3 -> pure (Tuple (Just (Left e)) s3)
        Tuple (Right settledBodies) s3 -> Array.foldRecM closing { defect: Nothing, state: s3, undone: Map.empty } settledBodies >>= case _ of
          { defect: Just d, state: s4 } -> pure (Tuple (Just (Left (brokenBy d))) s4)
          { state: s4, undone } -> do
            Tuple resolution s5 <- resolveByDirectionM session attempter declarationOf (const 0) s4
            Tuple left s6 <- runAttemptingM attempter s5
            pure (Tuple (Just (Right { resolution, left, undone, bodies: settledBodies })) s6)

  -- the values and the errors the settling comes to
  concluded report settledBy after =
    { values: Array.catMaybes (map snd finished)
    , errors: map (escapedCells (cellRecords (map (\b -> { name: b.name, regions: b.regions, references: b.references }) bodies))) (loopErrors <> Array.concatMap fst finished)
    }
    where
    -- what the loop, the resolution, and the closing stopped at, and the
    -- declarations they name; `Nothing` at a defect, which leaves nothing to
    -- trust
    Tuple loopErrors named = case report.result, settledBy of
      Loop.Rejected d, _ -> Tuple [ rejected d ] (Just (Set.fromFoldable (diagnosticDeclarations d)))
      Loop.Exhausted p, _ -> Tuple [ EquationUndecided p.origin ] (Just (Set.singleton (declarationOf p.origin)))
      Loop.Halted d, _ -> Tuple [ Broken d ] Nothing
      _, Just (Left stop) -> Tuple stop.errors stop.names
      _, Just (Right { resolution: ResolutionHalted d }) -> Tuple [ Broken d ] Nothing
      _, Just (Right { resolution: Resolution r, left, undone }) ->
        let
          closings = map (\(Tuple name cause) -> { error: undoneError cause, names: [ name ] }) (Map.toUnfoldable undone :: Array (Tuple (Qualified Ident) Undoing))
          components = closings <> Array.concatMap componentErrors (Array.filter (\c -> not (Map.member c.owner undone)) r.components)
          resolvedNames = Set.fromFoldable (Array.concatMap _.names components)
          -- a goal still waiting is a synthesis nothing decided, and any other
          -- job an equation
          undecided p = case p.job, sourceOrigin p.origin of
            JobSynthesis _, Just o -> SynthesisUndecided o
            _, _ -> EquationUndecided p.origin
          -- a job of a declaration the resolution reported is reported by that
          stillWaiting = case left.result of
            Loop.Blocked waiting -> Array.filter (\p -> not (Set.member (declarationOf p.origin) resolvedNames)) (NonEmptyArray.toArray waiting)
            _ -> []
        in
          Tuple (map _.error components <> map undecided stillWaiting)
            (Just (Set.union resolvedNames (Set.fromFoldable (map (\p -> declarationOf p.origin) stillWaiting))))
      _, Nothing -> Tuple [] (Just Set.empty)

    -- the declarations a job still waits for
    waiting = Set.fromFoldable (map (\p -> declarationOf p.site.origin) (Map.values after.tentative.scheduler.pending))

    -- the bodies with their pending `case`s replaced where the loop reached
    -- quiescence; one holding a `case` left pending otherwise is unchecked
    finished = map finish case settledBy of
      Just (Right r) -> r.bodies
      _ -> bodies
    finish b = case named of
      Nothing -> Tuple [] Nothing
      Just names
        | Set.member b.name names -> Tuple [] Nothing
        | Set.member b.name waiting || not (Array.null b.pending) -> Tuple [ LeftUnchecked b.origin b.name ] Nothing
        | otherwise -> settled b

    -- a settled body holding a typed hole, an expression hole, or a wildcard not
    -- wholly decided, is no value: each hole is reported, and each such wildcard
    -- where it is written, and nothing these stand for undecided is reported
    -- again where the term holds it
    settled b =
      let
        metas = after.tentative.metas
        { reported, covered } = annotated metas b.holes b.wildcards b.unwritten b.expressionHoles b.uncovered
      in
        case asCore (zonkExpr metas b.body) of
          Right core
            | Array.null reported -> Tuple [] (Just { name: b.name, origin: b.origin, ordinal: b.ordinal, attributes: b.attributes, scheme: b.scheme, spine: b.spine, body: core.body, initialization: core.initialization })
            | otherwise -> Tuple reported Nothing
          Left residues -> case Array.findMap defectOf (Array.filter (not <<< covered) (NonEmptyArray.toArray residues)) of
            -- every fit is decided or reported, every recursive reference made
            -- ordinary, and every place a match leaves uncovered noted, before a
            -- body is made Core
            Just defect -> Tuple [ Broken defect ] Nothing
            -- a place is reported once, however many undecided types stand there
            Nothing -> Tuple (reported <> map TypeUndetermined (Array.nubEq (map residueOrigin (Array.filter (not <<< covered) (NonEmptyArray.toArray residues))))) Nothing

-- | The typed holes and the wildcards an annotation holds, and the expression
-- | holes a body holds, settled: each hole reported, whatever is decided of
-- | it, each wildcard not wholly decided reported where it is written, and the
-- | residues of what they stand for, which are not reported again.
annotated :: MetaContext -> Array TypeHole -> Array Wildcard -> Array { origin :: Surface.Origin, kind :: XKind } -> Array ExpressionHole -> Array UncoveredMatch -> { reported :: Array ElaborationError, covered :: Residue Surface.Origin -> Boolean }
annotated metas holes wildcards unwritten expressionHoles uncovered = { reported, covered }
  where
  open = Array.filter (\w -> not (Set.isEmpty (typeMetas w) && Set.isEmpty (kindMetas w))) wildcards
  -- a kind a signature leaves unwritten that nothing decided, where it is
  -- left so, but for one a wildcard reported stands at
  undecided = Array.filter (\u -> let ks = unwrittenMetas u in not (Set.isEmpty ks) && Set.isEmpty (Set.intersection ks kinds)) unwritten
  reported = map (\h -> TypeHoleStands h.origin h.name (substitute metas h.type)) holes
    <> map TypeUndetermined (Array.nubEq (map _.origin open))
    <> map KindUndetermined (Array.nubEq (map _.origin undecided))
    <> map (\h -> ExpressionHoleStands h.origin h.name (substitute metas h.type) (map (\x -> x { type = substitute metas x.type }) h.context)) expressionHoles
    <> map (\m -> NonExhaustiveMatch m.origin (map (map (substitute metas)) m.witness)) uncovered
  written = map (\h -> { type: h.type, kind: h.kind }) holes <> map (\w -> { type: w.type, kind: w.kind }) wildcards <> map (\h -> { type: h.type, kind: XKType }) expressionHoles
  types = Set.unions (map typeMetas written)
  kinds = Set.unions (map kindMetas written)
  unwrittenKinds = Set.unions (map unwrittenMetas unwritten)
  covered = case _ of
    ResidualTypeMeta _ m -> Set.member m types
    ResidualKindMeta _ k -> Set.member k kinds || Set.member k unwrittenKinds
    -- an expression hole reported, where it is written and at what it stands
    -- for: one nothing noted is reported as what it is
    ResidualHole o t -> Array.any (\h -> h.origin == o && substitute metas h.type == t) expressionHoles
    -- a place a match noted as uncovered leaves, which the match is reported
    -- for; one nothing noted is the host's defect
    ResidualUncovered _ id -> Array.any (\m -> m.id == id) uncovered
    _ -> false

  unwrittenMetas u = kindMetasOf (substituteKind metas u.kind)

  -- what is undecided in a type an annotation writes, however deep
  typeMetas :: forall r. { type :: XType | r } -> Set MetaVar
  typeMetas w = metasOf (substitute metas w.type)

  kindMetas :: forall r. { type :: XType, kind :: XKind | r } -> Set KindMetaVar
  kindMetas w = Set.union (kindMetasOfType (substitute metas w.type)) (kindMetasOf (substituteKind metas w.kind))

-- | The metavariables the pending `case`s given may close for their matches'
-- | sake, read off the metavariables as they stand, each once with the site of
-- | the first `case` naming it. A match its compiler refuses is the host's
-- | defect, its patterns having been typed.
closableTails :: MetaContext -> Array PendingCase -> Either Defect (Array { tail :: XType, site :: Site })
closableTails metas pending = Array.nubByEq (\a b -> a.tail == b.tail) <<< Array.concat <$> traverse tails pending
  where
  tails p = case p.closable metas of
    Right ts -> Right (map (\t -> { tail: substitute metas t, site: p.site }) ts)
    Left _ -> Left (MatchMalformed p.site.origin)

-- | The tails given closed, each equated with the empty row where the `case`
-- | naming it stands.
closeTails :: SessionEnv -> Int -> Array { tail :: XType, site :: Site } -> SolverState -> Tuple (Outcome Unit) SolverState
closeTails session level tails = runAttempt session (atLevel level (for_ tails \t -> equate t.site { kind: XKRow RowType, left: t.tail, right: XRowEmpty }))

-- | A term with each pending `case` it holds replaced by the match built for
-- | it, the `case`s built once each in the order of their numbers against the
-- | metavariables as they stand, and the matches they leave uncovered. A
-- | `case` held with no record, one recorded and held nowhere, one held more
-- | than once, and one still held once replaced are the host's defects.
settlePending
  :: SessionEnv
  -> Int
  -> { term :: XExpr Surface.Origin, pending :: Array PendingCase }
  -> SolverState
  -> Tuple (Either ElaborationError { term :: XExpr Surface.Origin, uncovered :: Array UncoveredMatch }) SolverState
settlePending session level b state = case foldl build (Tuple (Right []) state) (Array.sortWith _.id b.pending) of
  Tuple (Left e) s -> Tuple (Left e) s
  Tuple (Right built) s -> Tuple (replaced built) s
  where
  metas = state.tentative.metas

  build (Tuple acc s) p = case acc of
    Left e -> Tuple (Left e) s
    Right done -> case runAttempt session (atLevel level (runSurf (p.assembled metas))) s of
      Tuple (Done (Right n)) s' -> Tuple (Right (Array.snoc done { id: p.id, term: n.value, uncovered: n.uncovered })) s'
      Tuple (Done (Left problem)) s' -> Tuple (Left (Unsupported problem)) s'
      Tuple outcome s' -> Tuple (Left (failure outcome)) s'

  replaced built =
    let
      recorded = map _.id built
      held = pendingCasesOf b.term <> Array.concatMap (pendingCasesOf <<< _.term) built
      matches = Map.fromFoldable (map (\m -> Tuple m.id m.term) built)
      term = replacePendingCases (\id -> Map.lookup id matches) b.term
    in
      case Array.find (\id -> not (Array.elem id recorded)) held, Array.find (\id -> Array.length (Array.filter (_ == id) held) /= 1) recorded, Array.head (pendingCasesOf term) of
        Just id, _, _ -> Left (Broken (PendingCaseUnrecorded id))
        _, Just id, _
          | Array.elem id held -> Left (Broken (PendingCaseRepeated id))
          | otherwise -> Left (Broken (PendingCaseNodeless id))
        _, _, Just id -> Left (Broken (PendingCaseLeft id))
        Nothing, Nothing, Nothing -> Right { term, uncovered: Array.concatMap _.uncovered built }

residueOrigin :: forall a. Residue a -> a
residueOrigin = case _ of
  ResidualTypeMeta o _ -> o
  ResidualKindMeta o _ -> o
  ResidualTermMeta o _ -> o
  ResidualHole o _ -> o
  ResidualFit o _ -> o
  ResidualRecursiveRef o _ -> o
  ResidualEta o -> o
  ResidualUncovered o _ -> o
  ResidualPendingCase o _ -> o

-- | A settled body as Core, and as its initialization is judged.
asCore :: forall a. XExpr a -> Either (NonEmptyArray (Residue a)) { body :: Core.Expr a, initialization :: Core.Expr a }
asCore e = { body: _, initialization: _ } <$> toCoreExpr e <*> toInitializationExpr e

-- | A residue no body made Core may hold, which is the host's defect.
defectOf :: forall a. Residue a -> Maybe Defect
defectOf = case _ of
  ResidualFit _ f -> Just (FitLeftUndecided f)
  ResidualRecursiveRef _ id -> Just (RecursiveReferenceLeft id)
  ResidualEta _ -> Just EtaExpansionMalformed
  ResidualUncovered _ id -> Just (UncoveredUnrecorded id)
  ResidualPendingCase _ id -> Just (PendingCaseLeft id)
  _ -> Nothing

-- | A diagnostic as the author is told it: a boundary no row expected of it
-- | contains asks for an implicit handler, which this version does not resolve.
rejected :: Diagnostic -> ElaborationError
rejected d = case d of
  BoundaryNotContained o _ | Just at <- sourceOrigin o -> Unsupported (OutsideSubset at "implicit-handler resolution at this checking boundary")
  ImplicitHandlerMissing o _ _ | Just at <- sourceOrigin o -> Unsupported (OutsideSubset at "implicit-handler resolution at this checking boundary")
  _ -> Rejected d

-- | Why a closing was undone, as the declaration is reported by it.
undoneError :: Undoing -> ElaborationError
undoneError = case _ of
  UndoneBy d -> rejected d
  UndoneWaiting p -> EquationUndecided p.origin

-- | Where in source a site stands, if anywhere but its declaration.
sourceOrigin :: Origin -> Maybe Surface.Origin
sourceOrigin = case _ of
  AtSource o -> Just o.origin
  InDeclaration _ -> Nothing

-- | A declaration whose scheme its body decides: a value without a signature,
-- | or a value or a computation whose signature is partial. Its name, where it
-- | was declared and its ordinal, its attributes, its parameters, its body,
-- | and its partial signature where it has one.
type Unsigned =
  { name :: Qualified Ident
  , origin :: Surface.Origin
  , ordinal :: Int
  , attributes :: Array Attribute
  , params :: Array Surface.Binder
  , body :: Surface.Expr
  , signature :: Maybe Elaborated
  }

-- | The level a top-level group is generalized at, every one of them: a group
-- | is done with, committed or rolled back, before the next begins.
topLevel :: Int
topLevel = 1

-- | What keeps a group from being generalized, each with the members it names.
type Failure = { error :: ElaborationError, names :: Array (Qualified Ident) }

-- | Generalizing one group: what keeps it from being generalized, over the
-- | solver state.
type Generalizing m = ExceptT (Array Failure) (StateT SolverState m)

-- | A group of values without a signature, generalized
-- | ([Elaboration](../../../../../docs/technical-references/02-Surface-Language/01-Elaboration.md#the-procedure)):
-- | each member's body inferred at the top level, each reference to a member
-- | at the one type the member has in the group, the loop run to quiescence and
-- | the fits resolved by direction, the value restriction and the provisional
-- | quantifiers, the rows closed, the annotations' holes and wildcards judged,
-- | and each member's quantifiers made final, the group committed whole. With
-- | what the jobs it ran warned of.
-- |
-- | **The fits are resolved and the rows closed for the group as one owner**,
-- | its members sharing the metavariables of the types they have in it; each
-- | member is generalized, and reported, as its own.
-- |
-- | **A group that is not generalized leaves nothing behind**: its tentative
-- | state is rolled back to where it began, its warnings with it, and what no
-- | rollback restores is kept. It is reported by what failed, each member that
-- | names; a member nothing names is left unchecked.
-- |
-- | **A body η-expansion may move is built again under its `λ` where its type
-- | is a function** and it is no value form once the loop is quiescent: the
-- | group starts over once, every such body expanded and nothing of the first
-- | build kept. One that asks for it the second time round is a defect.
generalizeGroup
  :: forall m
   . MonadRec m
  => SessionEnv
  -> AttempterM m
  -> Internal
  -> SurfaceEnv
  -> (Qualified Ident -> Boolean)
  -> NonEmptyArray Unsigned
  -> SolverState
  -> m { result :: Either (Array ElaborationError) { values :: Array ElaboratedValue, warnings :: Array Warning }, state :: SolverState }
generalizeGroup session attempter internal surface isConstructor group s0 =
  runStateT (runExceptT (attempt Set.empty)) s0 <#> case _ of
    Tuple (Left failures) s ->
      let
        named = Set.fromFoldable (Array.concatMap _.names failures)
      in
        { result: Left (map _.error failures <> map (\u -> LeftUnchecked u.origin u.name) (Array.filter (\u -> not (Set.member u.name named)) members))
        , state: { tentative: s0.tentative, retained: s.retained }
        }
    Tuple (Right r) s -> { result: Right r, state: s }
  where
  members = NonEmptyArray.toArray group
  names = map _.name members
  -- the group's key, its first member's name
  key = (NonEmptyArray.head group).name
  -- the owner fits and boundaries are resolved and rows closed for
  groupOwner o = let d = declarationOf o in if Array.elem d names then key else d
  -- the owner each member is generalized as
  memberOwner = declarationOf
  -- what fails where the mechanism does names every member
  defect d = { error: Broken d, names }

  attempt :: Set (Qualified Ident) -> Generalizing m { values :: Array ElaboratedValue, warnings :: Array Warning }
  attempt expanded = do
    types <- monomorphic
    let
      inGroup = surface { bindings = foldl (\b (Tuple u t) -> Map.insert u.name (provisional u t) b) surface.bindings (Array.zip members types) }
    built <- traverse (\(Tuple u t) -> elaborated inGroup expanded u t) (Array.zip members types)
    escaping built (afterBuilt expanded built)

  -- what the bodies built come to, a cell's region escaping reported as such
  escaping built = flip catchError \failures ->
    throwError (map (\f -> f { error = escapedCells (cellRecords (map (\b -> { name: b.unsigned.name, regions: b.regions, references: b.references }) built)) f.error }) failures)

  afterBuilt expanded built = do
    report <- stepM (runAttemptingM attempter)
    throwIfAny (stoppedAt report.result)
    asked <- gets \s -> Set.fromFoldable (map _.unsigned.name (Array.filter (expansionAsked expanded s) built))
    if Set.isEmpty asked then settle built report.warnings
    else if Set.isEmpty expanded then do
      -- the group started over with every such body expanded
      modify_ \s -> { tentative: s0.tentative, retained: s.retained }
      attempt asked
    else throwError (map (\name -> defect (ExpansionUnsettled name)) (Set.toUnfoldable asked))

  -- the one type each member has in the group: its partial signature's, or a
  -- metavariable
  monomorphic = do
    s <- get
    case runAttempt session (atLevel topLevel (traverse (\u -> maybe (freshTypeMeta emptyXContext XKType) (pure <<< _.type) u.signature) members)) s of
      Tuple (Done types) s' -> put s' $> types
      Tuple outcome s' -> put s' *> throwError [ attemptFailure names outcome ]

  expansionAsked expanded s b =
    let
      metas = s.tentative.metas
    in
      isNothing b.unsigned.signature && not (Set.member b.unsigned.name expanded) && expandable b.unsigned.params b.unsigned.body
        && not (isSettledValueForm isConstructor (zonkExpr metas b.expr))
        && isJust (asArrow (substitute metas b.type))

  elaborated inGroup expanded u t = do
    s <- get
    let
      site = { context: emptyXContext, origin: AtSource { declaration: u.name, origin: u.origin } }
      body = case u.signature of
        -- checked against its partial signature, as a body with a signature is
        Just e -> do
          noted <- runSurf (checkDefinition internal inGroup u.name u.origin { kindVars: e.kindVars, body: e.type } (if e.computation then [ Thunk ] else map Named u.params) u.body)
          pure (map (\n -> n { holes = e.holes <> n.holes, wildcards = e.wildcards <> n.wildcards }) noted)
        Nothing -> do
          noted <- runSurf (inferDefinition internal inGroup u.name u.origin u.params u.body (Set.member u.name expanded))
          for_ noted \n -> equate site { kind: XKType, left: n.value.type, right: t }
          pure (map (\n -> n { value = n.value.expr }) noted)
    case runAttempt session (atLevel topLevel body) s of
      Tuple (Done (Right n)) s' -> put s' $> { unsigned: u, expr: n.value, type: t, holes: n.holes, wildcards: n.wildcards, unwritten: n.unwritten, expressionHoles: n.expressionHoles, uncovered: n.uncovered, pending: n.pending, regions: n.regions, references: n.references }
      Tuple (Done (Left problem)) s' -> put s' *> throwError [ { error: Unsupported problem, names: [ u.name ] } ]
      Tuple outcome s' -> put s' *> throwError [ attemptFailure [ u.name ] outcome ]

  settle unbounded loopWarnings = do
    resolution <- stepM (resolveOwnersM session attempter groupOwner (const topLevel) (_ == key))
    resolutionWarnings <- resolvedBy resolution
    boundWarnings <- variantsBounded (Array.concatMap _.pending unbounded)
    built <- traverse settledPending unbounded
    generalizing <- gets \s -> map (\b -> { key: b.unsigned.name, name: b.unsigned.name, type: b.type, body: b.expr, valueForm: isSettledValueForm isConstructor (zonkExpr s.tentative.metas b.expr), written: isJust b.unsigned.signature }) built
    prepared <- stepM (prepareGeneralizationM attempter memberOwner topLevel generalizing)
    draft <- case prepared.preparation of
      Drafted d -> pure d
      Hindered hindrances -> hindered built hindrances
      PreparationStopped result -> throwError (stoppedAt result)
    closed <- stepM (closeRowsM session attempter groupOwner key topLevel (map (\b -> { site: { context: emptyXContext, origin: InDeclaration b.unsigned.name }, term: b.expr, types: [ b.type ] }) built))
    closingWarnings <- case closed of
      Left d -> throwError [ defect d ]
      Right { closing: Undone c } -> throwError [ undone c.cause ]
      Right c -> pure c.warnings
    -- a hole or a wildcard is reported before what it stands for is
    -- quantified or found ambiguous
    noted <- gets \s -> Array.concatMap (\b -> map (\error -> { error, names: [ b.unsigned.name ] }) (judged s.tentative.metas b)) built
    throwIfAny noted
    planned <- step (finalizeGeneralization memberOwner draft generalizing)
    plan <- case planned of
      Planned p -> pure p
      FinalizationHindered hindrances -> hindered built hindrances
    committed <- step (commitGeneralization memberOwner plan generalizing)
    finalized <- case committed of
      Generalized g | map _.name g.members == names -> pure g.members
      Generalized _ -> throwError [ defect (CommitmentAmiss key) ]
      GeneralizationHindered hindrances -> hindered built hindrances
      GeneralizationHalted d -> throwError [ defect d ]
    metas <- gets _.tentative.metas
    values <- traverse (made metas) (Array.zip members finalized)
    pure { values, warnings: loopWarnings <> resolutionWarnings <> boundWarnings <> prepared.warnings <> closingWarnings }

  resolvedBy = case _ of
    ResolutionHalted d -> throwError [ defect d ]
    Resolution r -> case Array.findMap refusal r.components of
      Just d -> throwError [ diagnosed d ]
      Nothing -> pure r.warnings

  -- the variants the pending `case`s leave open closed for their sake, the
  -- loop run and the fits resolved again, until none is left to close
  variantsBounded pending = do
    tails <- gets \s -> closableTails s.tentative.metas pending
    case tails of
      Left d -> throwError [ defect d ]
      Right [] -> pure []
      Right ts -> do
        closed <- step (closeTails session topLevel ts)
        case closed of
          Done _ -> pure unit
          outcome -> throwError [ attemptFailure names outcome ]
        report <- stepM (runAttemptingM attempter)
        throwIfAny (stoppedAt report.result)
        resolution <- stepM (resolveOwnersM session attempter groupOwner (const topLevel) (_ == key))
        warnings <- resolvedBy resolution
        more <- variantsBounded pending
        pure (report.warnings <> warnings <> more)

  -- a member with each pending `case` it holds replaced by its match
  settledPending b = do
    result <- step (settlePending session topLevel { term: b.expr, pending: b.pending })
    case result of
      Left error -> throwError [ { error, names } ]
      Right r -> pure b { expr = r.term, uncovered = b.uncovered <> r.uncovered }

  -- a member as Core: its scheme and its definition
  made metas (Tuple u f) = do
    scheme <- case toCore f.scheme.body of
      Just body -> pure { kindVars: maybe [] _.kindVars u.signature <> f.scheme.kindVars, body }
      Nothing -> throwError [ defect (CommitmentAmiss u.name) ]
    core <- case asCore (zonkExpr metas f.body) of
      Right core -> pure core
      Left residues -> throwError case Array.findMap defectOf (NonEmptyArray.toArray residues) of
        Just d -> [ defect d ]
        Nothing -> map (\o -> { error: TypeUndetermined o, names: [ u.name ] }) (Array.nubEq (map residueOrigin (NonEmptyArray.toArray residues)))
    pure { name: u.name, origin: u.origin, ordinal: u.ordinal, attributes: u.attributes, scheme, spine: maybe (plainScheme scheme) (\e -> schemeOf e scheme) u.signature, body: core.body, initialization: core.initialization }

  -- a member as a reference inside its group reads it: at the one type it has
  -- there, unless its partial signature is a scheme, which such a reference
  -- cannot instantiate
  provisional u t = case u.signature of
    Just e | not (Array.null e.kindVars) || schematic e.type -> ProvisionalScheme
    _ -> Provisional t
  schematic = case _ of
    XForall _ _ _ -> true
    XConstrained _ _ -> true
    _ -> false

  -- a member's holes and wildcards, the kinds its partial signature and the
  -- local ones in its body leave unwritten that nothing decided, and its
  -- expression holes
  judged metas b = (annotated metas b.holes b.wildcards (maybe [] _.unwritten b.unsigned.signature <> b.unwritten) b.expressionHoles b.uncovered).reported

  -- each member's hindrances, where the residues of its body place them
  hindered :: forall r x. Array { unsigned :: Unsigned, expr :: XExpr Surface.Origin | r } -> Array (Hindrance (Qualified Ident)) -> Generalizing m x
  hindered built hindrances = do
    metas <- gets _.tentative.metas
    throwError
      ( Array.concatMap
          ( \b ->
              let
                own = Array.filter (\h -> hindranceKey h == b.unsigned.name) hindrances
                residues = either NonEmptyArray.toArray (const []) (toCoreExpr (zonkExpr metas b.expr))
              in
                if Array.null own then [] else map (\error -> { error, names: [ b.unsigned.name ] }) (hindranceErrors b.unsigned residues own)
          )
          built
      )

  stoppedAt = case _ of
    Loop.Rejected d -> [ diagnosed d ]
    Loop.Exhausted p -> [ { error: EquationUndecided p.origin, names: [ declarationOf p.origin ] } ]
    Loop.Halted d -> [ defect d ]
    Loop.Completed -> []
    Loop.Blocked _ -> []

  diagnosed d = { error: rejected d, names: diagnosticDeclarations d }

  -- an attempt that did not commit, by what it came to: a refusal names what
  -- its diagnostic is about, a defect every member, and anything else the
  -- members given
  attemptFailure :: forall x. Array (Qualified Ident) -> Outcome x -> Failure
  attemptFailure given = case _ of
    Failed d -> { error: Rejected d, names: diagnosticDeclarations d }
    Broke d -> defect d
    outcome -> { error: failure outcome, names: given }

  undone = case _ of
    UndoneBy d -> diagnosed d
    UndoneWaiting p -> { error: EquationUndecided p.origin, names: [ declarationOf p.origin ] }

  refusal c = case c.outcome of
    Refused d -> Just d
    _ -> Nothing

  step :: forall x. (SolverState -> Tuple x SolverState) -> Generalizing m x
  step f = lift (state f)

  -- a step carried out in the monad the attempter carries its attempts out in
  stepM :: forall x. (SolverState -> m (Tuple x SolverState)) -> Generalizing m x
  stepM f = lift (StateT f)

  throwIfAny errors = unless (Array.null errors) (throwError errors)

-- | The member a hindrance is about.
hindranceKey :: forall k. Hindrance k -> k
hindranceKey = case _ of
  Hindrance.GoalTouchesQuantifier k _ _ -> k
  Hindrance.SynthesisUndecided k _ _ -> k
  Hindrance.RestrictedUnsolved k -> k
  Hindrance.AmbiguousCandidates k _ -> k
  Hindrance.AmbiguousKindCandidates k _ -> k
  Hindrance.KindNotQuantifiable k _ -> k
  Hindrance.FitLeft k _ _ -> k
  Hindrance.BoundaryLeft k _ _ -> k
  Hindrance.TermMetaLeft k _ -> k
  Hindrance.ConstraintRefused k _ _ -> k
  Hindrance.AmbiguousConstraint k _ -> k
  Hindrance.RecursiveArgumentAmbiguous k _ -> k
  Hindrance.ConstraintEscapes k _ _ -> k
  Hindrance.ConstraintUnwritten k _ -> k
  Hindrance.EquationLeft k _ _ -> k

-- | What keeps a value without a signature from being generalized, as its
-- | author is told it, each where the residues of its body place it, and where
-- | the value is declared where nothing does.
hindranceErrors :: Unsigned -> Array (Residue Surface.Origin) -> Array (Hindrance (Qualified Ident)) -> Array ElaborationError
hindranceErrors u residues hindrances =
  (if Array.any asksSignature hindrances then [ SignatureNeeded u.origin u.name ] else [])
    <> (if Array.null rows then [] else [ EffectRowAmbiguous u.name (Array.nubEq (map at rows)) ])
    <> Array.concatMap one hindrances
  where
  asksSignature = case _ of
    Hindrance.RestrictedUnsolved _ -> true
    Hindrance.GoalTouchesQuantifier _ _ _ -> true
    _ -> false
  rows = Array.mapMaybe
    ( case _ of
        Hindrance.FitLeft _ o _ -> Just o
        Hindrance.BoundaryLeft _ o _ -> Just o
        _ -> Nothing
    )
    hindrances
  one = case _ of
    Hindrance.SynthesisUndecided _ o _ -> [ SynthesisUndecided (at o) ]
    Hindrance.AmbiguousCandidates _ ms -> map TypeUndetermined
      ( placed \r -> case r of
          ResidualTypeMeta o m | Array.elem m ms -> Just o
          _ -> Nothing
      )
    Hindrance.AmbiguousKindCandidates _ ks -> map TypeUndetermined
      ( placed \r -> case r of
          ResidualKindMeta o k | Array.elem k ks -> Just o
          _ -> Nothing
      )
    Hindrance.KindNotQuantifiable _ _ -> [ KindUndetermined u.origin ]
    Hindrance.TermMetaLeft _ t -> map SynthesisUndecided
      ( placed \r -> case r of
          ResidualTermMeta o t' | t == t' -> Just o
          _ -> Nothing
      )
    Hindrance.ConstraintRefused _ o breach -> [ Rejected (ObligationRejected { obligation: o, basis: Required, breach }) ]
    Hindrance.AmbiguousConstraint _ o -> [ TypeUndetermined (at o) ]
    Hindrance.RecursiveArgumentAmbiguous _ o -> [ TypeUndetermined (at o) ]
    Hindrance.ConstraintEscapes _ o v -> [ ConstraintEscapes (at o) v ]
    Hindrance.ConstraintUnwritten _ o -> [ ConstraintUnwritten (at o) ]
    Hindrance.EquationLeft _ o _ -> [ EquationUndecided o ]
    Hindrance.RestrictedUnsolved _ -> []
    Hindrance.GoalTouchesQuantifier _ _ _ -> []
    Hindrance.FitLeft _ _ _ -> []
    Hindrance.BoundaryLeft _ _ _ -> []
  at o = fromMaybe u.origin (sourceOrigin o)
  placed f = case Array.nubEq (Array.mapMaybe f residues) of
    [] -> [ u.origin ]
    os -> os

-- | The declaration a site stands in.
declarationOf :: Origin -> Qualified Ident
declarationOf = case _ of
  InDeclaration name -> name
  AtSource o -> o.declaration

-- | The declarations a diagnostic is about.
diagnosticDeclarations :: Diagnostic -> Array (Qualified Ident)
diagnosticDeclarations = case _ of
  EquationFailed o _ -> [ declarationOf o ]
  ObligationBroken b -> [ declarationOf b.equation, declarationOf b.obligation ]
  ObligationRejected r -> [ declarationOf r.obligation ]
  TermAssignmentFailed o _ -> [ declarationOf o ]
  SynthesisFailed s -> [ declarationOf s.goal.origin ]
  RowNotContained o _ -> [ declarationOf o ]
  BoundaryNotContained o _ -> [ declarationOf o ]
  ImplicitHandlerMissing o _ _ -> [ declarationOf o ]
  ImplicitHandlerAmbiguous o _ _ -> [ declarationOf o ]
  ImplicitOrderAmbiguous o _ -> [ declarationOf o ]
  ImplicitPayloadConflict o _ -> [ declarationOf o ]
  CellEscapes e -> [ declarationOf e.reference ]

-- | What each body noted of its cells, by its declaration: the regions it
-- | opened, and the references to their cells, in the order met.
type CellRecords = Map (Qualified Ident) { regions :: Array CellRegion, references :: Array CellReference }

cellRecords :: Array { name :: Qualified Ident, regions :: Array CellRegion, references :: Array CellReference } -> CellRecords
cellRecords = Map.fromFoldable <<< map (\b -> Tuple b.name { regions: b.regions, references: b.references })

-- | An error as reported. **An equation failing because a cell's region would
-- | escape is the escape of the cell** where the declaration it fails in noted
-- | that region, whichever constraint the solver found it at: named by the
-- | first reference to a cell of the region and by the expression declaring
-- | the cells. Anything else is as it is.
escapedCells :: CellRecords -> ElaborationError -> ElaborationError
escapedCells records = case _ of
  Rejected (EquationFailed site (EscapingRegion _ region)) | Just escape <- escapeOf site region -> Rejected escape
  e -> e
  where
  escapeOf site region = do
    let declaration = declarationOf site
    noted <- Map.lookup declaration records
    owner <- Array.find (\r -> r.region == region) noted.regions
    first <- Array.find (\r -> r.region == region) noted.references
    pure (CellEscapes { reference: AtSource { declaration, origin: first.origin }, boundary: AtSource { declaration, origin: owner.boundary }, cell: first.cell, region })

failure :: forall a. Outcome a -> ElaborationError
failure = case _ of
  Failed d -> Rejected d
  Broke d -> Broken d
  -- nothing the surface elaborator states postpones it: an equation it cannot
  -- decide becomes a job
  _ -> AttemptPostponed

-- | A module elaborated into a Core module the Core checker accepts, what
-- | checking it declared — the signature and the checked values — and the Core
-- | part of its interface, or what kept it from being one; and the values
-- | elaborated either way.
type ElaboratedModule =
  { result :: Either (NonEmptyArray ElaborationError) { core :: Core.Module Surface.Origin, declared :: Declared Surface.Origin, interface :: CoreInterface }
  , values :: Array ElaboratedValue
  }

-- | Elaborate a module, as `elaborateValues` does, into a Core module checked
-- | against the signature its imports give, its type, attribute, and foreign
-- | declarations first.
-- |
-- | **Its values are grouped by what they refer to**, in a stable dependency
-- | order: a recursive group becomes a `DeclRec`, any other value a
-- | `DeclNonRec`. **A recursive group is initialized in the order written**,
-- | each member reading only the members written before it, judged on what the
-- | source writes, an η-expansion making no read later; a read that is not is
-- | reported where the reference stands and where what made it immediate does.
-- | **A Core module is made only of a module with no error**: one missing a
-- | declaration would refer to what it does not bind. **It imports the modules
-- | its values depend on when they run** (D51), which are within what the header
-- | reaches, the Core being checked against what the header reaches; and it
-- | exports each value it declares that is reached from outside — by its name,
-- | as a macro, or through an operator it exports —
-- | each foreign so reached, and each data type and effect it declares and
-- | exports, a data type with the constructors it exports of it. The Core part
-- | of its interface holds each data type and newtype it declares, each synonym
-- | at its parameters and the type it stands for, each foreign type at its
-- | kind, the scheme of every value, foreign, and constructor, each effect with
-- | its operations, each operation's scheme among the values', each
-- | attribute declaration at its parameters' types, and each implicit handler
-- | with the element it handles and the elements it performs.
-- | **The Core checker refusing it is the elaborator's fault**, reported as
-- | such, but for what only the Core checker checks: an attribute's arguments,
-- | reported where its declaration stands; the value form a `Λ` encloses; and
-- | the value right-hand side of a declaration generalized over kinds (D52),
-- | reported where the declaration stands.
elaborateModule
  :: Signature
  -> SurfaceEnv
  -> Array CatalogEntry
  -> Surface.Module
  -> Exports
  -> ElaboratedModule
elaborateModule signature surface imported m exports = case elaborateModuleM (identically <<< attemptPending) signature surface imported m exports of
  Identity result -> result

-- | `elaborateModule`, each job carried out in the monad the attempter the
-- | function given makes of the module's session carries its attempts out
-- | in; what that monad stops with is the caller's, and no diagnostic.
elaborateModuleM
  :: forall m
   . MonadRec m
  => (SessionEnv -> AttempterM m)
  -> Signature
  -> SurfaceEnv
  -> Array CatalogEntry
  -> Surface.Module
  -> Exports
  -> m ElaboratedModule
elaborateModuleM attempterOf signature surface imported m exports =
  elaborateValuesM attempterOf signature surface imported m <#> assembled signature m exports

-- | The Core module, its declarations judged and checked, made of what the
-- | module's declarations elaborated to.
assembled
  :: Signature
  -> Surface.Module
  -> Exports
  -> { data :: Array ElaboratedData, synonyms :: Array ElaboratedSynonym, foreignTypes :: Array ElaboratedForeignType, effects :: Array ElaboratedEffect, foreigns :: Array ElaboratedForeign, attributes :: Array ElaboratedAttribute, values :: Array ElaboratedValue, errors :: Array ElaborationError, warnings :: Array Warning }
  -> ElaboratedModule
assembled signature m exports elaborated =
  { result, values: elaborated.values }
  where
  values = elaborated.values

  ordinalOf = Map.fromFoldable (Array.mapWithIndex (\i v -> Tuple v.name i) values)
  grouped = groups (map (\v -> Set.fromFoldable (Array.mapMaybe (\g -> Map.lookup g ordinalOf) (Array.fromFoldable (globalsOf v.body)))) values)
  members g = Array.mapMaybe (Array.index values) g.members

  -- a recursive group initialized in the order written, judged on its
  -- members as the source writes them, an η-expansion making no read later
  recursiveValues = Array.concatMap
    ( \g ->
        if g.recursive then
          let
            group = members g
            nameAt i = _.name <$> Array.index group i
          in
            Array.mapMaybe (\v -> ReadWhileInitializing v.at v.through <$> nameAt v.initializer <*> nameAt v.read)
              (topLevelViolations initializing (map (\v -> { name: v.name, value: v.initialization }) group))
        else []
    )
    grouped
  -- each value's local groups, judged as the top-level ones are
  localValues = Array.concatMap
    (\v -> map (\l -> LocalReadWhileInitializing l.at l.through l.initializer l.read) (localGroupViolations initializing v.initialization))
    values
  -- what a group is judged against: the imports' signature, with the
  -- constructors and the foreigns the module declares
  initializing = foldl (\s f -> s { values = Map.insert f.name { scheme: f.decl.scheme, isForeign: true } s.values })
    (foldl (addData m.name) signature (map _.decl elaborated.data))
    elaborated.foreigns
  errors = implicitConditions <> elaborated.errors <> localValues <> recursiveValues <> implicitInitials

  -- the implicit handlers the module declares, each with its elaborated value
  -- where its body elaborated
  implicitDeclared = Array.mapMaybe
    ( case _ of
        DeclHandler d | d.implicit -> Just { declaration: d, value: Array.find (\v -> v.name == d.name) values }
        _ -> Nothing
    )
    m.declarations
  -- the conditions an implicit handler's declaration fails, whether or not its
  -- body elaborated
  implicitConditions = Array.concatMap (implicitFailures <<< _.declaration) implicitDeclared
  -- each initial value of an implicit handler's cells is to be a value form,
  -- judged on the Core it elaborated to; the region its handling expression
  -- opens holds them in the order the cells are declared
  implicitInitials = Array.concatMap
    ( \i -> case i.value >>= (regionOpenedAt i.declaration.origin <<< _.body) of
        Just initials -> Array.mapMaybe
          (\(Tuple c e) -> if isValueForm initializing e then Nothing else Just (ImplicitCondition c.origin (ImplicitInitialNotValue (cellName c.cell))))
          (Array.zip i.declaration.cells initials)
        Nothing -> []
    )
    implicitDeclared

  decls = map (\d -> Core.DeclData d.origin d.decl) elaborated.data
    <> map (\e -> Core.DeclEffect e.origin e.decl) elaborated.effects
    <> map (\a -> Core.DeclAttribute a.origin a.decl) elaborated.attributes
    <> map (\f -> Core.DeclForeign f.origin f.decl) elaborated.foreigns
    <> map
      ( \g -> case members g of
          [ v ] | not g.recursive -> DeclNonRec v.origin (binding v)
          vs -> DeclRec (maybe m.origin _.origin (Array.head vs)) (map binding vs)
      )
      grouped
  binding v = { name: nameOf v.name, scheme: v.scheme, value: v.body, attributes: v.attributes }

  operators = Map.fromFoldable
    ( Array.mapMaybe
        ( case _ of
            DeclFixity d -> Just (Tuple d.operator { associativity: d.associativity, precedence: d.precedence, target: d.target })
            _ -> Nothing
        )
        m.declarations
    )
  core =
    { annotation: m.origin
    , name: m.name
    , imports: runtimeDependencies m.name (map _.body values)
    , exports: Array.concatMap typeExports elaborated.data
        <> Array.concatMap elaborationOnlyExports elaborated.data
        <> map (ExportEffect <<< _.decl.name) (Array.filter effectExported elaborated.effects)
        <> map (ExportValue <<< nameOf <<< _.name) (Array.filter (\v -> reachedFromOutside m.name exports operators (nameOf v.name) || elaborationOnlyValue v) values)
        <> map (ExportValue <<< _.decl.name) (Array.filter (reachedFromOutside m.name exports operators <<< _.decl.name) elaborated.foreigns)
    , decls
    }
  result = case NonEmptyArray.fromArray errors of
    Just es -> Left es
    -- a foreign type the module declares has no Core declaration, and is in
    -- what the module is checked against as the ABI's types are
    Nothing -> case declareAnnotated (foldl addForeignType signature elaborated.foreignTypes) core of
      -- what the compiler's desugarings refer to of the module is held to
      -- the schemes listed, now that the module's values are declared
      Right declared -> case NonEmptyArray.fromArray (map entryDeclared (declaredEntryMismatches m.name declared.signature)) of
        Nothing -> Right { core, declared, interface }
        Just es -> Left es
      -- an attribute's arguments are checked by Core alone
      Left { at, error: AttributeIllTyped err } -> Left (NonEmptyArray.singleton (AttributeRejected at err))
      -- and so is the value form a `Λ` encloses, what was not η-expanded
      -- being the author's to give a parameter
      Left { at, error: IllTyped NotAValueForm } -> Left (NonEmptyArray.singleton (ValueFormNeeded at))
      -- and so is a value right-hand side where a declaration is generalized
      -- over kinds, the author's to give
      Left { error: KindGeneralizedNonValue name } -> Left (NonEmptyArray.singleton (KindValueNeeded (entryOrigin name) name))
      Left refusal -> Left (NonEmptyArray.singleton (CoreRefused refusal))

  -- an entry declared otherwise than listed, where its declaration stands
  entryDeclared e = InternalEntryDeclared (entryOrigin e.name) e.name { expected: e.expected, declared: e.declared }
  entryOrigin name = case Array.find (\v -> v.name == name) values, Array.find (\d -> Array.any (\c -> Qualified m.name c.name == name) d.decl.constructors) elaborated.data of
    Just v, _ -> v.origin
    _, Just d -> d.origin
    _, _ -> m.origin
  -- a data type exported, abstractly or with the constructors exported of it
  typeExports d
    | declaredHere (map (\e -> e.entity == TypeEntity (Qualified m.name d.decl.name) && e.via == Declared) (Map.lookup (tyNameText d.decl.name) exports.types)) =
        [ ExportType d.decl.name ] <> map (ExportCtor <<< _.name) (Array.filter (\c -> exportedValue c.name) d.decl.constructors)
    | otherwise = []
  -- a constructor only elaboration names, exported under its internal identity
  -- apart from the export list, which never names it, and once
  elaborationOnlyExports d
    | Array.any (\a -> a.name == primAttribute "elaborationOnly") d.decl.attributes =
        map (ExportCtor <<< _.name) (Array.filter (\c -> not (exportedValue c.name)) d.decl.constructors)
    | otherwise = []
  -- a value only elaboration names, exported under its internal identity
  -- apart from the export list, which never names it
  elaborationOnlyValue v = Array.any (\a -> a.name == primAttribute "elaborationOnly") v.attributes
  -- an effect exported by name, with its operations
  effectExported e = declaredHere (map (\x -> x.entity == EffectEntity e.name && x.via == Declared) (Map.lookup (effNameText e.decl.name) exports.types))
  -- an operation's scheme: the type it is called at
  operationSchemes e = map (\(Tuple q op) -> Tuple (nameOf q) (plainScheme (operationScheme Nothing op))) (localOperations m.name e)
  exportedValue c = declaredHere (map (\e -> e.entity == Qualified m.name c && e.via == Declared) (Map.lookup (identText c) exports.values))
  declaredHere = case _ of
    Just true -> true
    _ -> false

  interface =
    { schemes: Map.fromFoldable
        ( map (\v -> Tuple (nameOf v.name) v.spine) values
            <> map (\f -> Tuple f.decl.name f.spine) elaborated.foreigns
            <> Array.concatMap (\d -> map (\c -> Tuple c.name (plainScheme (ctorInfo (Qualified m.name d.decl.name) d.decl c).scheme)) d.decl.constructors) elaborated.data
            <> Array.concatMap operationSchemes elaborated.effects
        )
    , types: Map.fromFoldable
        ( map (\d -> Tuple d.decl.name { kind: dataKind d.decl, sort: CoreData { params: d.decl.params, fields: map _.fields d.decl.constructors } }) elaborated.data
            <> map (\s -> Tuple (tyNameOf s.name) { kind: s.entry.kind, sort: CoreSynonym { params: s.entry.params, body: s.entry.body } }) elaborated.synonyms
            <> map (\f -> Tuple (tyNameOf f.name) { kind: f.kind, sort: CoreForeign }) elaborated.foreignTypes
        )
    , effects: Map.fromFoldable (map (\e -> Tuple e.decl.name { params: e.decl.params, operations: Array.zipWith (\o arguments -> { binders: o.tyBinders, arguments, resumesWith: o.resumesWith }) e.decl.operations e.arguments }) elaborated.effects)
    , attributes: Map.fromFoldable (map (\a -> Tuple a.decl.name { positional: a.decl.positional, keyword: map _.type a.decl.keyword }) elaborated.attributes)
    , implicitHandlers: Map.fromFoldable
        (Array.mapMaybe (\i -> i.value >>= \v -> Tuple (nameOf v.name) <$> capabilityElements i.declaration.handled v.scheme.body) implicitDeclared)
    }

  nameOf (Qualified _ n) = n
  tyNameOf (Qualified _ n) = n
  identText (Ident n) = n
  tyNameText (TyName n) = n
  effNameText (EffName n) = n

  -- `T : forall k̄. κ̄ -> Type`
  dataKind decl = case dataEntry m.name decl of
    DataTyCon kind _ -> kind
    IntrinsicTyCon kind _ -> kind

-- | Whether the two sets share a member.
meets :: forall x. Ord x => Set x -> Set x -> Boolean
meets a b = not (Set.isEmpty (Set.intersection a b))

-- | Whether a scheme is the one a synthesizer is invoked at, its row taken by
-- | its normal form. It binds nothing, so no binder is told apart.
isSynthesizerScheme :: XScheme -> Boolean
isSynthesizerScheme s = Array.null s.kindVars && case asArrow s.body, asArrow (fromCore synthesizerType) of
  Just given, Just wanted -> given.argument == wanted.argument && given.result == wanted.result && sameRow given.row wanted.row
  _, _ -> false
  where
  sameRow a b = case xnf a, xnf b of
    Right x, Right y -> rebuild x == rebuild y
    _, _ -> false

-- | Whether two kind schemes bind as many kind variables, and are the same
-- | kind once each side's variables are renamed, in order, to one name for
-- | each position.
sameKindScheme :: KindScheme -> KindScheme -> Boolean
sameKindScheme a b = Array.length a.kindVars == Array.length b.kindVars && renamed a == renamed b
  where
  renamed s = Kind.substituteKind (Map.fromFoldable (Array.mapWithIndex (\i k -> Tuple k (KVar (KindVar ("$k" <> show i)))) s.kindVars)) s.body

-- | The element a handler declaration's type handles and the elements it
-- | performs in its place, read off the expansion of `E ~> ( t̄ )`: the
-- | thunk's row holds the handled element, and the result's row the performed
-- | ones beside the residual row. The performed ones come in the canonical
-- | order of their keys.
capabilityElements :: Qualified EffName -> Type -> Maybe { source :: RowEntry, targets :: Array RowEntry }
capabilityElements handled = case _ of
  TForall _ _ body -> capabilityElements handled body
  TConstrained _ body -> capabilityElements handled body
  t -> do
    f <- asFunction t
    thunk <- asFunction f.argument
    source <- Array.find (\e -> rowEntryKey e == EffectKey handled) (knownElements thunk.row)
    pure { source, targets: Array.sortBy (\x y -> compareRowKeys (rowEntryKey x) (rowEntryKey y)) (knownElements f.row) }
  where
  knownElements = case _ of
    TRowExtend entry rest -> Array.cons entry (knownElements rest)
    TRowUnion left right -> knownElements left <> knownElements right
    _ -> []

-- | Whether the elements an implicit handler removes and performs mention no
-- | type variable and no kind variable.
closedElements :: { source :: RowEntry, targets :: Array RowEntry } -> Boolean
closedElements e = Array.all closed (Array.cons e.source e.targets)
  where
  closed entry = Array.all (\t -> Set.isEmpty (freeTypeVars t) && Set.isEmpty (freeKindVars (fromCore t))) (payloadOf entry)
  payloadOf = case _ of
    RowEffectEntry _ args -> args
    RowLabelledEffectEntry _ _ args -> args
    RowTypeEntry _ t -> [ t ]
    RowRegionEntry _ -> []

-- | The initial values of the region opened by the handling expression
-- | written at the given origin, taking the outermost such region in the term.
regionOpenedAt :: Surface.Origin -> Core.Expr Surface.Origin -> Maybe (Array (Core.Expr Surface.Origin))
regionOpenedAt at = case _ of
  Core.Region o _ _ initials _ | o == at -> Just initials
  e -> Array.findMap (regionOpenedAt at) (Core.subterms e)

cellName :: CellVar -> String
cellName (CellVar c) = case c.name of
  Ident n -> n

-- | The conditions of an implicit handler its declaration fails, each where
-- | what fails it stands, read off the declaration before its body: written
-- | with `~>`, no parameter, every clause `fast`, and no return clause.
implicitFailures :: Surface.HandlerDeclaration -> Array ElaborationError
implicitFailures h =
  (if isJust h.capabilityTargets then [] else [ ImplicitCondition (typeOrigin (handlerTypeAfter (Array.length h.params) h.signature.body)) ImplicitNotCapability ])
    <> maybe [] (\p -> [ ImplicitCondition (binderOrigin p) ImplicitParameters ]) (Array.head h.params)
    <> Array.mapMaybe notFast h.body.operations
    <> maybe [] (\r -> [ ImplicitCondition r.origin ImplicitReturnClause ]) h.body.return
  where
  notFast c = case c.form of
    ClauseFast -> Nothing
    _ -> Just (ImplicitCondition c.origin (ImplicitClauseNotFast c.operation))

-- | The type a handler declaration's signature reaches after a pure arrow for
-- | each of its parameters, past the quantifiers, constraints, synthesized
-- | parameters, and kind annotations on the way.
handlerTypeAfter :: Int -> Surface.Type -> Surface.Type
handlerTypeAfter n t = case t of
  Surface.TypeForall _ _ body -> handlerTypeAfter n body
  Surface.TypeConstrained _ _ body -> handlerTypeAfter n body
  Surface.TypeKinded _ body _ -> handlerTypeAfter n body
  Surface.TypeFunction _ (Surface.TypeSynthesized _ _ _ _ _) rest Nothing -> handlerTypeAfter n rest
  Surface.TypeFunction _ _ rest Nothing | n > 0 -> handlerTypeAfter (n - 1) rest
  _ -> t
