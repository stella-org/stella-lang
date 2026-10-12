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
-- | which its type decides where it is declared. An attribute declaration's
-- | parameters are read at closed types against the module's types.
-- |
-- | **A computation declaration is a value whose Core type is a thunk**, its
-- | signature read as that type and its body under it.
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
-- | every member of a group one of which does. A fixity gives Core nothing, and
-- | a handler is outside what it elaborates.
module Stella.Compiler.Elaborate.Surface.Module
  ( ElaborationError(..)
  , ElaboratedValue
  , Elaborating
  , ElaboratedModule
  , elaborateModule
  , elaborateValues
  , settleBodies
  ) where

import Prelude
import Prim hiding (Type)

import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.State (State, get, gets, modify_, put, runState, state)
import Control.Monad.Trans.Class (lift)
import Data.Array as Array
import Data.Array.NonEmpty (NonEmptyArray)
import Data.Array.NonEmpty as NonEmptyArray
import Data.Either (Either(..), either)
import Data.Foldable (foldl, for_)
import Data.Traversable (traverse)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, isJust, isNothing, maybe)
import Data.Set (Set)
import Data.Set as Set
import Data.Tuple (Tuple(..), fst, snd)
import Stella.Compiler.Elaborate.CorePlus.Context (Origin(..), emptyXContext)
import Stella.Compiler.Elaborate.CorePlus.Term (Residue(..), XExpr, isSettledValueForm, toCoreExpr)
import Stella.Compiler.Elaborate.CorePlus.Kind (KindMetaVar, XKind(..), kindMetasOf)
import Stella.Compiler.Elaborate.CorePlus.Type (MetaVar, XType(..), fromCore, kindMetasOfType, metasOf, toCore)
import Stella.Compiler.Elaborate.Surface.Types (readAttributeDeclaration, readTypes, settledTypes)
import Stella.Compiler.Elaborate.Environment.Synonyms (SynonymEntry)
import Stella.Compiler.Elaborate.Surface.Internal (Internal, internalEntries)
import Stella.Compiler.Elaborate.Driver.Attempt (attemptPending, runAttempt)
import Stella.Compiler.Elaborate.Driver.Loop (Attempter, runAttempting)
import Stella.Compiler.Elaborate.Driver.Loop as Loop
import Stella.Compiler.Elaborate.Driver.Resolve (ComponentOutcome(..), Resolution(..), resolveByDirection, resolveOwners)
import Stella.Compiler.Elaborate.Driver.Generalize (Hindrance(..)) as Hindrance
import Stella.Compiler.Elaborate.Driver.Generalize (Commitment(..), Finalization(..), Hindrance, Preparation(..), commitGeneralization, finalizeGeneralization, prepareGeneralization)
import Stella.Compiler.Elaborate.Driver.Close (Closing(..), Undoing(..), closeRows)
import Stella.Compiler.Elaborate.Environment.Catalog (CatalogEntry, EntrySort(..))
import Stella.Compiler.Elaborate.Environment.Imported (sessionEnvOf)
import Stella.Compiler.Elaborate.Environment.Surface (SurfaceBinding(..), SurfaceEnv, takesSynthesized)
import Stella.Compiler.Elaborate.Kernel.Elab (Outcome(..), SessionEnv, SolverState, atLevel, equate, freshTypeMeta, initialState)
import Stella.Compiler.Elaborate.Mechanism.Obligation (Basis(..))
import Stella.Compiler.Elaborate.Mechanism.TermMeta (zonkExpr)
import Stella.Compiler.Elaborate.Mechanism.Unify (MetaContext, substitute, substituteKind)
import Stella.Compiler.Elaborate.Surface.Expr (Parameter(..), asArrow, checkDefinition, elaborateComputation, elaborateValue, expandable, immediateReferences, inferDefinition, references, runSurf)
import Stella.Compiler.Elaborate.Surface.Type (Elaborated, TypeHole, Unsupported(..), Wildcard, elaborateComputationSignature, elaborateSignature, elaborateValueSignature, schemeOf, settledScheme)
import Stella.Compiler.Elaborate.Vocabulary.Diagnostic (Defect(..), Diagnostic(..), Warning)
import Stella.Compiler.Elaborate.Vocabulary.Handle (SessionId(..))
import Stella.Compiler.Elaborate.Surface.Group (groups)
import Stella.Compiler.ForeignBoundary (Refused, crossingOf)
import Stella.Compiler.Interface.Assemble (CoreInterface, CoreTypeSort(..), coreAttribute, reachedFromOutside)
import Stella.Compiler.Interface.Module (Exports, TypeEntity(..), Via(..))
import Stella.Compiler.Interface.Scheme (Scheme, plainScheme)
import Stella.Compiler.Surface.Decl (Declaration(..), declarationOrigin)
import Stella.Compiler.Surface.Decl (Attribute, Module) as Surface
import Stella.Compiler.Surface.Expr (Binder, Expr) as Surface
import Stella.Compiler.Surface.Origin (Origin) as Surface
import Stella.Compiler.TypedCore (Decl(DeclAttribute, DeclData, DeclEffect, DeclForeign), Expr, Module) as Core
import Stella.Compiler.TypedCore (Attribute, AttributeDecl, DataDecl, DeclError(..), DeclFailure, Decl(DeclNonRec, DeclRec), Declared, EffectDecl, Export(..), ForeignDecl, declareAnnotated)
import Stella.Compiler.TypedCore.Declare (ctorInfo, dataEntry)
import Stella.Compiler.TypedCore.AttributeCheck (AttributeError, checkAttribute)
import Stella.Compiler.TypedCore.Check (CheckError(NotAValueForm), isFunVal)
import Stella.Compiler.TypedCore.Reference (globalsOf)
import Stella.Compiler.TypedCore.Name (EffName(..), Ident(..), ModuleName, OpName(..), Qualified(..), TyName(..), TyVar, unqualified)
import Stella.Compiler.TypedCore.Signature (CanonicalClass(..), Signature, TyConInfo(..))
import Stella.Compiler.TypedCore.Kind (KindScheme)
import Stella.Compiler.TypedCore.Type (Type(..), TypeScheme)
import Stella.Compiler.TypedCore.Prim (pureFn)

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
  -- | A typed hole an annotation holds, where it is written, by its name and
  -- | the type standing for it as far as it is decided.
  | TypeHoleStands Surface.Origin String XType
  -- | What a `Λ` or a constraint abstraction encloses that is no value form,
  -- | where the abstraction stands: the Core checker's refusal, and the
  -- | author's.
  | ValueFormNeeded Surface.Origin
  -- | A Core module the Core checker refused, which is the elaborator's fault.
  | CoreRefused (DeclFailure Surface.Origin)
  -- | An entry a desugaring of the compiler's refers to, which a signature
  -- | reaching its module lacks or holds at another scheme than the one listed:
  -- | the compiler's fault.
  | InternalEntryMismatch (Qualified Ident)
  -- | A declaration whose effect rows nothing decided, where its fits stand.
  | EffectRowAmbiguous (Qualified Ident) (Array Surface.Origin)
  -- | An attempt that postponed itself, which nothing the elaborator states
  -- | does: it is the elaborator's fault.
  | AttemptPostponed

-- | A value declaration elaborated: its name, where it was declared and its
-- | ordinal among the module's declarations, its attributes, its scheme, and
-- | its definition as a Core term, located by the Surface AST.
type ElaboratedValue =
  { name :: Qualified Ident
  , origin :: Surface.Origin
  , ordinal :: Int
  , attributes :: Array Attribute
  , scheme :: TypeScheme
  , spine :: Scheme
  , body :: Core.Expr Surface.Origin
  }

-- | A value declaration whose body is elaborated, its equations not yet all
-- | decided: those left are jobs of the state it was elaborated into. Its
-- | annotations' typed holes and wildcards are reported once it is settled.
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
  }

-- | A data declaration elaborated, and where it stands.
type ElaboratedData = { origin :: Surface.Origin, decl :: DataDecl }

-- | A type synonym elaborated: where it stands, its attributes, its name, and
-- | what an interface holds of it.
type ElaboratedSynonym = { origin :: Surface.Origin, attributes :: Array Surface.Attribute, name :: Qualified TyName, entry :: SynonymEntry }

-- | An effect elaborated: where it stands, its name, its Core declaration, and
-- | the arguments each operation is written with.
type ElaboratedEffect = { origin :: Surface.Origin, name :: Qualified EffName, decl :: EffectDecl, arguments :: Array (Array Type) }

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
  -> { data :: Array ElaboratedData, synonyms :: Array ElaboratedSynonym, foreignTypes :: Array ElaboratedForeignType, effects :: Array ElaboratedEffect, foreigns :: Array ElaboratedForeign, attributes :: Array ElaboratedAttribute, values :: Array ElaboratedValue, immediate :: Map (Qualified Ident) (Set (Qualified Ident)), errors :: Array ElaborationError, warnings :: Array Warning }
elaborateValues imports surface importedEntries m =
  if Array.null dataErrors then
    { data: elaboratedData
    , synonyms: types.synonyms
    , foreignTypes: types.foreignTypes
    , effects: types.effects
    , foreigns: crossing.foreigns
    , attributes: attributesRead.declared
    , values: Array.sortWith _.ordinal (generalized.values <> settled'.values)
    , immediate
    , errors: internalErrors <> unsupported <> signatureErrors <> partialErrors <> crossing.errors <> attributesRead.errors <> generalized.errors <> attributeErrors <> bodyErrors <> settled'.errors
    , warnings: generalized.warnings
    }
  else { data: [], synonyms: [], foreignTypes: [], effects: [], foreigns: [], attributes: [], values: [], immediate: Map.empty, errors: dataErrors <> unsupported, warnings: [] }
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
  dataErrors = typesRead.errors <> map Unsupported types.unsupported
  -- the synonyms the values' types are read through: the imports', and the
  -- module's own
  withSynonyms = surface { synonyms = Map.union (Map.fromFoldable (map (\s -> Tuple s.name s.entry) types.synonyms)) surface.synonyms }
  -- the entries the compiler's desugarings refer to, read off it
  Tuple internal internalErrors = case internalEntries signature of
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
    DeclAttribute _ -> Nothing
    DeclData _ -> Nothing
    DeclNewtype _ -> Nothing
    DeclSynonym _ -> Nothing
    DeclForeignType _ -> Nothing
    DeclEffect _ -> Nothing
    DeclFixity _ -> Nothing
    DeclTypeFixity _ -> Nothing
    other -> Just (Left (Unsupported (OutsideSubset (declarationOrigin other) "this declaration")))
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
  -- synthesized argument on its spine is supplied by a goal, which this
  -- version does not create
  partialRead = Array.filter (isPartial <<< snd) read.read
  partialErrors = Array.mapMaybe
    (\(Tuple d e) -> if Array.null e.synthesized then Nothing else Just (Unsupported (OutsideSubset d.origin "a partial signature taking a synthesized argument")))
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
        Right r -> Just { declared: d, scheme: r.scheme, spine: r.spine }
        Left _ -> Nothing
    )
    settled
  signatureErrors = read.errors <> Array.concatMap
    ( \(Tuple _ s) -> case s of
        Left places -> map KindUndetermined (NonEmptyArray.toArray places)
        Right _ -> []
    )
    settled

  -- the values, each with its body
  defined = Array.mapMaybe (\v -> either (const Nothing) (\d -> Just { declared: v.declared, scheme: v.scheme, spine: v.spine, definition: d }) v.declared.definition) schemes
  -- what a foreign takes and gives must cross to the host, which its type
  -- decides where it is declared
  crossing = foldl crossOne { foreigns: [], errors: [] } (Array.filter (isForeignDefinition <<< _.declared.definition) schemes)
  crossOne acc v = case crossingOf signature v.scheme of
    Right _ -> acc { foreigns = Array.snoc acc.foreigns { origin: v.declared.origin, name: v.declared.name, decl: { name: unqualified v.declared.name, scheme: v.scheme, attributes: v.declared.attributes }, spine: v.spine } }
    Left refused -> acc { errors = Array.snoc acc.errors (ForeignRefused v.declared.origin v.declared.name refused) }

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
  attributeSignature =
    foldl (\s a -> s { attributes = Map.insert (Qualified m.name a.decl.name) { positional: a.decl.positional, keyword: a.decl.keyword } s.attributes })
      ( foldl (\s v -> s { values = Map.insert v.name { scheme: v.scheme, isForeign: false } s.values })
          (foldl (\s v -> s { values = Map.insert v.declared.name { scheme: v.scheme, isForeign: isForeignDefinition v.declared.definition } s.values }) signature schemes)
          generalized.values
      )
      attributesRead.declared
  attributeErrors = Array.concatMap
    ( \d -> Array.mapMaybe
        ( \a -> case coreAttribute a of
            Right attribute -> either (Just <<< AttributeRejected d.origin) (const Nothing) (checkAttribute attributeSignature attribute)
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
  -- argument among those the imports declare
  withOwn = withSynonyms { synthesizing = withSynonyms.synthesizing <> Set.fromFoldable (map _.declared.name (Array.filter (takesSynthesized <<< _.spine) schemes)) }

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
  generalized = foldl generalizeOne
    { state: attributesRead.state
    , bindings: Map.empty
    , values: []
    , unavailable: Set.union unread (Set.fromFoldable (Array.mapMaybe (either (Just <<< _.name) (const Nothing)) unsignedRead))
    , errors: Array.mapMaybe (either (Just <<< _.error) (const Nothing)) unsignedRead
    , warnings: []
    }
    (groups (map (\u -> Set.fromFoldable (Array.mapMaybe (\n -> Map.lookup n unsignedIndex) (Array.fromFoldable (references u.body)))) unsigned))
  generalizeOne acc g =
    let
      members = Array.mapMaybe (Array.index unsigned) g.members
      named = Set.fromFoldable (map _.name members)
    in
      -- a group a member of which refers to what has no scheme is not
      -- elaborated, none of its members being generalizable without it
      case NonEmptyArray.fromArray members of
        Nothing -> acc
        Just _ | Array.any (\u -> meets (references u.body) acc.unavailable) members ->
          acc { unavailable = Set.union acc.unavailable named, errors = acc.errors <> map (\u -> LeftUnchecked u.origin u.name) members }
        Just group ->
          let
            done = generalizeGroup session (attemptPending session) internal (withOwn { bindings = acc.bindings }) (\n -> Map.member n signature.ctors) group acc.state
          in
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
  withFinal = withOwn { bindings = generalized.bindings }
  bodies = foldl bodyOne { state: generalized.state, bodies: [], errors: [] } defined
  bodyOne acc v = case v.definition of
    ValueBody _ body | meets (references body) generalized.unavailable -> unchecked acc v
    ComputationBody body | meets (references body) generalized.unavailable -> unchecked acc v
    ValueBody params body -> attemptBody acc v (elaborateValue internal withFinal v.declared.name v.declared.origin v.scheme params body)
    -- a synthesized argument is supplied by a goal, which this version does
    -- not create, and a computation has no parameter to bind it to
    ComputationBody _ | takesSynthesized v.spine -> acc { errors = Array.snoc acc.errors (Unsupported (OutsideSubset v.declared.origin "a computation taking a synthesized argument")) }
    ComputationBody body -> attemptBody acc v (elaborateComputation internal withFinal v.declared.name v.declared.origin v.scheme body)
  attemptBody acc v elaborating =
    case runAttempt session (runSurf elaborating) acc.state of
      Tuple (Done (Right built)) s -> acc { state = s, bodies = Array.snoc acc.bodies { name: v.declared.name, origin: v.declared.origin, ordinal: v.declared.ordinal, attributes: v.declared.attributes, scheme: v.scheme, spine: v.spine, body: built.value, holes: built.holes, wildcards: built.wildcards, unwritten: built.unwritten } }
      Tuple (Done (Left problem)) _ -> acc { errors = Array.snoc acc.errors (Unsupported problem) }
      Tuple outcome _ -> acc { errors = Array.snoc acc.errors (failure outcome) }
  unchecked acc v = acc { errors = Array.snoc acc.errors (LeftUnchecked v.declared.origin v.declared.name) }
  bodyErrors = bodies.errors
  -- what each value with no parameter refers to before entering any λ
  immediate = Map.fromFoldable
    ( Array.mapMaybe
        ( \v -> case v.definition of
            ValueBody [] body -> Just (Tuple v.declared.name (immediateReferences body))
            _ -> Nothing
        )
        defined
        <> map (\u -> Tuple u.name (immediateReferences u.body)) (Array.filter (\u -> Array.null u.params && not (maybe false _.computation u.signature)) unsigned)
    )

  settled' = settleBodies session (attemptPending session) bodies.state bodies.bodies

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

-- | The body a declaration defines: a value's, by its parameters, or a
-- | computation's, which has none.
data Body
  = ValueBody (Array Surface.Binder) Surface.Expr
  | ComputationBody Surface.Expr

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
settleBodies session attempter state bodies =
  { values: Array.catMaybes (map snd finished)
  , errors: loopErrors <> Array.concatMap fst finished
  }
  where
  componentErrors c = case c.outcome of
    Settled -> []
    Ambiguous a -> [ { error: EffectRowAmbiguous c.owner (Array.mapMaybe sourceOrigin a.origins), names: [ c.owner ] } ]
    Refused d -> [ { error: rejected d, names: Array.cons c.owner (diagnosticDeclarations d) } ]

  -- a body's rows closed, a defect stopping every later one; a closing
  -- undone is the declaration's report, the rows decided again without it
  -- need not fail as it did
  closing acc b = case acc of
    { defect: Nothing, state: s, undone } -> case closeRows session attempter declarationOf b.name 0 [ { site: { context: emptyXContext, origin: InDeclaration b.name }, term: b.body, types: [] } ] s of
      Tuple (Left d) s' -> { defect: Just d, state: s', undone }
      Tuple (Right { closing: Undone u }) s' -> { defect: Nothing, state: s', undone: Map.insert b.name u.cause undone }
      Tuple (Right _) s' -> { defect: Nothing, state: s', undone }
    stopped -> stopped

  Tuple report quiet = runAttempting attempter state

  -- at quiescence: the fits left undecided resolved by direction, each
  -- declaration's rows nothing needs closed, the fits resolved again and the
  -- loop run to what it then waits on, every state handed on to the next
  Tuple settledBy after = case report.result of
    Loop.Completed -> settling
    Loop.Blocked _ -> settling
    _ -> Tuple Nothing quiet
    where
    settling = case resolveByDirection session attempter declarationOf (const 0) quiet of
      Tuple (ResolutionHalted d) s1 -> Tuple (Just (Left d)) s1
      Tuple (Resolution _) s1 -> case foldl closing { defect: Nothing, state: s1, undone: Map.empty } bodies of
        { defect: Just d, state: s2 } -> Tuple (Just (Left d)) s2
        { state: s2, undone } ->
          let
            Tuple resolution s3 = resolveByDirection session attempter declarationOf (const 0) s2
            Tuple left s4 = runAttempting attempter s3
          in
            Tuple (Just (Right { resolution, left, undone })) s4

  -- what the loop, the resolution, and the closing stopped at, and the
  -- declarations they name; `Nothing` at a defect, which leaves nothing to
  -- trust
  Tuple loopErrors named = case report.result, settledBy of
    Loop.Rejected d, _ -> Tuple [ rejected d ] (Just (Set.fromFoldable (diagnosticDeclarations d)))
    Loop.Exhausted p, _ -> Tuple [ EquationUndecided p.origin ] (Just (Set.singleton (declarationOf p.origin)))
    Loop.Halted d, _ -> Tuple [ Broken d ] Nothing
    _, Just (Left d) -> Tuple [ Broken d ] Nothing
    _, Just (Right { resolution: ResolutionHalted d }) -> Tuple [ Broken d ] Nothing
    _, Just (Right { resolution: Resolution r, left, undone }) ->
      let
        closings = map (\(Tuple name cause) -> { error: undoneError cause, names: [ name ] }) (Map.toUnfoldable undone :: Array (Tuple (Qualified Ident) Undoing))
        components = closings <> Array.concatMap componentErrors (Array.filter (\c -> not (Map.member c.owner undone)) r.components)
        resolvedNames = Set.fromFoldable (Array.concatMap _.names components)
        -- a job of a declaration the resolution reported is reported by that
        stillWaiting = case left.result of
          Loop.Blocked waiting -> Array.filter (\p -> not (Set.member (declarationOf p.origin) resolvedNames)) (NonEmptyArray.toArray waiting)
          _ -> []
      in
        Tuple (map _.error components <> map (\p -> EquationUndecided p.origin) stillWaiting)
          (Just (Set.union resolvedNames (Set.fromFoldable (map (\p -> declarationOf p.origin) stillWaiting))))
    _, Nothing -> Tuple [] (Just Set.empty)

  -- the declarations a job still waits for
  waiting = Set.fromFoldable (map (\p -> declarationOf p.site.origin) (Map.values after.tentative.scheduler.pending))

  finished = map finish bodies
  finish b = case named of
    Nothing -> Tuple [] Nothing
    Just names
      | Set.member b.name names -> Tuple [] Nothing
      | Set.member b.name waiting -> Tuple [ LeftUnchecked b.origin b.name ] Nothing
      | otherwise -> settled b

  -- a settled body holding a typed hole, or a wildcard not wholly decided, is
  -- no value: each hole an annotation holds is reported, and each such
  -- wildcard where it is written, and nothing these stand for undecided is
  -- reported again where the term holds it
  settled b =
    let
      metas = after.tentative.metas
      { reported, covered } = annotated metas b.holes b.wildcards b.unwritten
    in
      case toCoreExpr (zonkExpr metas b.body) of
        Right body
          | Array.null reported -> Tuple [] (Just { name: b.name, origin: b.origin, ordinal: b.ordinal, attributes: b.attributes, scheme: b.scheme, spine: b.spine, body })
          | otherwise -> Tuple reported Nothing
        Left residues -> case Array.findMap defectOf (NonEmptyArray.toArray residues) of
          -- every fit is decided or reported, and every recursive reference made
          -- ordinary, before a body is made Core
          Just defect -> Tuple [ Broken defect ] Nothing
          -- a place is reported once, however many undecided types stand there
          Nothing -> Tuple (reported <> map TypeUndetermined (Array.nubEq (map residueOrigin (Array.filter (not <<< covered) (NonEmptyArray.toArray residues))))) Nothing

-- | The typed holes and the wildcards an annotation holds, settled: each hole
-- | reported, each wildcard not wholly decided reported where it is written,
-- | and the residues of what they stand for, which are not reported again.
annotated :: MetaContext -> Array TypeHole -> Array Wildcard -> Array { origin :: Surface.Origin, kind :: XKind } -> { reported :: Array ElaborationError, covered :: Residue Surface.Origin -> Boolean }
annotated metas holes wildcards unwritten = { reported, covered }
  where
  open = Array.filter (\w -> not (Set.isEmpty (typeMetas w) && Set.isEmpty (kindMetas w))) wildcards
  -- a kind a signature leaves unwritten that nothing decided, where it is
  -- left so, but for one a wildcard reported stands at
  undecided = Array.filter (\u -> let ks = unwrittenMetas u in not (Set.isEmpty ks) && Set.isEmpty (Set.intersection ks kinds)) unwritten
  reported = map (\h -> TypeHoleStands h.origin h.name (substitute metas h.type)) holes
    <> map TypeUndetermined (Array.nubEq (map _.origin open))
    <> map KindUndetermined (Array.nubEq (map _.origin undecided))
  written = map (\h -> { type: h.type, kind: h.kind }) holes <> map (\w -> { type: w.type, kind: w.kind }) wildcards
  types = Set.unions (map typeMetas written)
  kinds = Set.unions (map kindMetas written)
  unwrittenKinds = Set.unions (map unwrittenMetas unwritten)
  covered = case _ of
    ResidualTypeMeta _ m -> Set.member m types
    ResidualKindMeta _ k -> Set.member k kinds || Set.member k unwrittenKinds
    _ -> false

  unwrittenMetas u = kindMetasOf (substituteKind metas u.kind)

  -- what is undecided in a type an annotation writes, however deep
  typeMetas :: forall r. { type :: XType | r } -> Set MetaVar
  typeMetas w = metasOf (substitute metas w.type)

  kindMetas :: forall r. { type :: XType, kind :: XKind | r } -> Set KindMetaVar
  kindMetas w = Set.union (kindMetasOfType (substitute metas w.type)) (kindMetasOf (substituteKind metas w.kind))

residueOrigin :: forall a. Residue a -> a
residueOrigin = case _ of
  ResidualTypeMeta o _ -> o
  ResidualKindMeta o _ -> o
  ResidualTermMeta o _ -> o
  ResidualHole o _ -> o
  ResidualFit o _ -> o
  ResidualRecursiveRef o _ -> o

-- | A residue no body made Core may hold, which is the host's defect.
defectOf :: forall a. Residue a -> Maybe Defect
defectOf = case _ of
  ResidualFit _ f -> Just (FitLeftUndecided f)
  ResidualRecursiveRef _ id -> Just (RecursiveReferenceLeft id)
  _ -> Nothing

-- | A diagnostic as the author is told it: a boundary no row expected of it
-- | contains asks for an implicit handler, which this version does not resolve.
rejected :: Diagnostic -> ElaborationError
rejected d = case d of
  BoundaryNotContained o _ | Just at <- sourceOrigin o -> Unsupported (OutsideSubset at "implicit-handler resolution at this checking boundary")
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
type Generalizing = ExceptT (Array Failure) (State SolverState)

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
  :: SessionEnv
  -> Attempter
  -> Internal
  -> SurfaceEnv
  -> (Qualified Ident -> Boolean)
  -> NonEmptyArray Unsigned
  -> SolverState
  -> { result :: Either (Array ElaborationError) { values :: Array ElaboratedValue, warnings :: Array Warning }, state :: SolverState }
generalizeGroup session attempter internal surface isConstructor group s0 =
  case runState (runExceptT (attempt Set.empty)) s0 of
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

  attempt :: Set (Qualified Ident) -> Generalizing { values :: Array ElaboratedValue, warnings :: Array Warning }
  attempt expanded = do
    types <- monomorphic
    let
      inGroup = surface { bindings = foldl (\b (Tuple u t) -> Map.insert u.name (provisional u t) b) surface.bindings (Array.zip members types) }
    built <- traverse (\(Tuple u t) -> elaborated inGroup expanded u t) (Array.zip members types)
    report <- step (runAttempting attempter)
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
      Tuple (Done (Right n)) s' -> put s' $> { unsigned: u, expr: n.value, type: t, holes: n.holes, wildcards: n.wildcards, unwritten: n.unwritten }
      Tuple (Done (Left problem)) s' -> put s' *> throwError [ { error: Unsupported problem, names: [ u.name ] } ]
      Tuple outcome s' -> put s' *> throwError [ attemptFailure [ u.name ] outcome ]

  settle built loopWarnings = do
    resolution <- step (resolveOwners session attempter groupOwner (const topLevel) (_ == key))
    resolutionWarnings <- case resolution of
      ResolutionHalted d -> throwError [ defect d ]
      Resolution r -> case Array.findMap refusal r.components of
        Just d -> throwError [ diagnosed d ]
        Nothing -> pure r.warnings
    generalizing <- gets \s -> map (\b -> { key: b.unsigned.name, name: b.unsigned.name, type: b.type, body: b.expr, valueForm: isSettledValueForm isConstructor (zonkExpr s.tentative.metas b.expr), written: isJust b.unsigned.signature }) built
    prepared <- step (prepareGeneralization attempter memberOwner topLevel generalizing)
    draft <- case prepared.preparation of
      Drafted d -> pure d
      Hindered hindrances -> hindered built hindrances
      PreparationStopped result -> throwError (stoppedAt result)
    closed <- step (closeRows session attempter groupOwner key topLevel (map (\b -> { site: { context: emptyXContext, origin: InDeclaration b.unsigned.name }, term: b.expr, types: [ b.type ] }) built))
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
    pure { values, warnings: loopWarnings <> resolutionWarnings <> prepared.warnings <> closingWarnings }

  -- a member as Core: its scheme and its definition
  made metas (Tuple u f) = do
    scheme <- case toCore f.scheme.body of
      Just body -> pure { kindVars: maybe [] _.kindVars u.signature <> f.scheme.kindVars, body }
      Nothing -> throwError [ defect (CommitmentAmiss u.name) ]
    body <- case toCoreExpr (zonkExpr metas f.body) of
      Right body -> pure body
      Left residues -> throwError case Array.findMap defectOf (NonEmptyArray.toArray residues) of
        Just d -> [ defect d ]
        Nothing -> map (\o -> { error: TypeUndetermined o, names: [ u.name ] }) (Array.nubEq (map residueOrigin (NonEmptyArray.toArray residues)))
    pure { name: u.name, origin: u.origin, ordinal: u.ordinal, attributes: u.attributes, scheme, spine: maybe (plainScheme scheme) (\e -> schemeOf e scheme) u.signature, body }

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

  -- a member's holes and wildcards, and the kinds its partial signature and
  -- the local ones in its body leave unwritten that nothing decided
  judged metas b = (annotated metas b.holes b.wildcards (maybe [] _.unwritten b.unsigned.signature <> b.unwritten)).reported

  -- each member's hindrances, where the residues of its body place them
  hindered :: forall r x. Array { unsigned :: Unsigned, expr :: XExpr Surface.Origin | r } -> Array (Hindrance (Qualified Ident)) -> Generalizing x
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

  step :: forall x. (SolverState -> Tuple x SolverState) -> Generalizing x
  step f = lift (state f)

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
-- | `DeclNonRec`. Core binds only function values recursively, so a recursive
-- | group with a member that is none is reported at that member as a form this
-- | version does not elaborate. **A Core module is made only of a module with
-- | no error**: one missing a declaration would refer to what it does not bind. It imports what
-- | the module imports, and exports each value it declares that is reached from
-- | outside — by its name, as a macro, or through an operator it exports —
-- | each foreign so reached, and each data type and effect it declares and
-- | exports, a data type with the constructors it exports of it. The Core part
-- | of its interface holds each data type and newtype it declares, each synonym
-- | at its parameters and the type it stands for, each foreign type at its
-- | kind, the scheme of every value, foreign, and constructor, each effect with
-- | its operations, each operation's scheme among the values', and each
-- | attribute declaration at its parameters' types.
-- | **The Core checker refusing it is the elaborator's fault**, reported as
-- | such, but for an attribute's arguments, which only the Core checker checks:
-- | one that does not check is reported where its declaration stands.
elaborateModule
  :: Signature
  -> SurfaceEnv
  -> Array CatalogEntry
  -> Surface.Module
  -> Exports
  -> ElaboratedModule
elaborateModule signature surface imported m exports =
  { result, values: elaborated.values }
  where
  elaborated = elaborateValues signature surface imported m
  values = elaborated.values

  ordinalOf = Map.fromFoldable (Array.mapWithIndex (\i v -> Tuple v.name i) values)
  grouped = groups (map (\v -> Set.fromFoldable (Array.mapMaybe (\g -> Map.lookup g ordinalOf) (Array.fromFoldable (globalsOf v.body)))) values)
  members g = Array.mapMaybe (Array.index values) g.members

  -- Core binds only function values recursively: a member that is none is
  -- outside what this version lowers, whether or not the surface admits it,
  -- and so is one whose evaluation refers to a member before entering any λ,
  -- which an η-expansion does not make a function
  recursiveValues = Array.concatMap
    ( \g ->
        if g.recursive then
          let
            names = Set.fromFoldable (map _.name (members g))
            immediate v = maybe false (not <<< Set.isEmpty <<< Set.intersection names) (Map.lookup v.name elaborated.immediate)
          in
            map (\v -> Unsupported (OutsideSubset v.origin "a recursive value that is no function")) (Array.filter (\v -> not (isFunVal v.body) || immediate v) (members g))
        else []
    )
    grouped
  errors = elaborated.errors <> recursiveValues

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
    , imports: Array.nub (map _.module m.imports)
    , exports: Array.concatMap typeExports elaborated.data
        <> map (ExportEffect <<< _.decl.name) (Array.filter effectExported elaborated.effects)
        <> map (ExportValue <<< nameOf <<< _.name) (Array.filter (reachedFromOutside m.name exports operators <<< nameOf <<< _.name) values)
        <> map (ExportValue <<< _.decl.name) (Array.filter (reachedFromOutside m.name exports operators <<< _.decl.name) elaborated.foreigns)
    , decls
    }
  result = case NonEmptyArray.fromArray errors of
    Just es -> Left es
    -- a foreign type the module declares has no Core declaration, and is in
    -- what the module is checked against as the ABI's types are
    Nothing -> case declareAnnotated (foldl addForeignType signature elaborated.foreignTypes) core of
      Right declared -> Right { core, declared, interface }
      -- an attribute's arguments are checked by Core alone
      Left { at, error: AttributeIllTyped err } -> Left (NonEmptyArray.singleton (AttributeRejected at err))
      -- and so is the value form a `Λ` encloses, what was not η-expanded
      -- being the author's to give a parameter
      Left { at, error: IllTyped NotAValueForm } -> Left (NonEmptyArray.singleton (ValueFormNeeded at))
      Left refusal -> Left (NonEmptyArray.singleton (CoreRefused refusal))

  -- a data type exported, abstractly or with the constructors exported of it
  typeExports d
    | declaredHere (map (\e -> e.entity == TypeEntity (Qualified m.name d.decl.name) && e.via == Declared) (Map.lookup (tyNameText d.decl.name) exports.types)) =
        [ ExportType d.decl.name ] <> map (ExportCtor <<< _.name) (Array.filter (\c -> exportedValue c.name) d.decl.constructors)
    | otherwise = []
  -- an effect exported by name, with its operations
  effectExported e = declaredHere (map (\x -> x.entity == EffectEntity e.name && x.via == Declared) (Map.lookup (effNameText e.decl.name) exports.types))
  -- an operation's scheme: its effect's parameters and its own variables
  -- quantified over its one argument to what it resumes with
  operationSchemes e = map (\o -> Tuple (identOfOp o.name) (plainScheme { kindVars: [], body: Array.foldr (\b t -> TForall b.name b.kind t) (pureFn o.argument o.resumesWith) (e.decl.params <> o.tyBinders) })) e.decl.operations
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
    , implicitHandlers: Map.empty
    }

  nameOf (Qualified _ n) = n
  tyNameOf (Qualified _ n) = n
  identText (Ident n) = n
  tyNameText (TyName n) = n
  effNameText (EffName n) = n
  identOfOp (OpName n) = Ident n

  -- `T : forall k̄. κ̄ -> Type`
  dataKind decl = case dataEntry m.name decl of
    DataTyCon kind _ -> kind
    IntrinsicTyCon kind _ -> kind

-- | Whether the two sets share a member.
meets :: forall x. Ord x => Set x -> Set x -> Boolean
meets a b = not (Set.isEmpty (Set.intersection a b))
