-- | A module's data and value declarations elaborated into Core, against what
-- | its imports reach ([Elaboration](../../../../../docs/technical-references/02-Surface-Language/01-Elaboration.md)).
-- |
-- | **The data declarations are elaborated before any value**
-- | ([Data](Data.purs)), and what they declare is added to the signature and
-- | the catalog the values are elaborated against. That signature is the
-- | module's own: the build environment is not, and the Core checker is given
-- | the signature of the imports alone, as for any module. A data declaration
-- | that does not elaborate leaves the values unread, a value naming its type
-- | having nothing to be read against.
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
-- | read, leaves nothing behind. Once the loop is done, each body is zonked and
-- | made a Core term, and a type nothing decided is reported where it stands.
-- | A body is a value only once every equation stated for it holds; one the
-- | loop stopped before deciding is reported, never returned.
-- |
-- | **A value declaration needs a signature in this version**, a fixity gives
-- | Core nothing, and every declaration but a data declaration and a value
-- | declaration is outside what it elaborates.
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

import Data.Array as Array
import Data.Array.NonEmpty (NonEmptyArray)
import Data.Array.NonEmpty as NonEmptyArray
import Data.Either (Either(..), either, hush)
import Data.Foldable (foldl)
import Data.Traversable (traverse)
import Data.Map as Map
import Data.Maybe (Maybe(..), maybe)
import Data.Set as Set
import Data.Tuple (Tuple(..), fst, snd)
import Stella.Compiler.Elaborate.CorePlus.Context (Origin(..))
import Stella.Compiler.Elaborate.CorePlus.Term (Residue(..), XExpr, toCoreExpr)
import Stella.Compiler.Elaborate.CorePlus.Type (fromCore)
import Stella.Compiler.Elaborate.Surface.Data (readData, settledData)
import Stella.Compiler.Elaborate.Surface.Internal (internalEntries)
import Stella.Compiler.Elaborate.Driver.Attempt (attemptPending, runAttempt)
import Stella.Compiler.Elaborate.Driver.Loop (Attempter, runAttempting)
import Stella.Compiler.Elaborate.Driver.Loop as Loop
import Stella.Compiler.Elaborate.Environment.Catalog (CatalogEntry, EntrySort(..))
import Stella.Compiler.Elaborate.Environment.Imported (sessionEnvOf)
import Stella.Compiler.Elaborate.Environment.Surface (SurfaceEnv, takesSynthesized)
import Stella.Compiler.Elaborate.Kernel.Elab (Outcome(..), SolverState, initialState)
import Stella.Compiler.Elaborate.Mechanism.TermMeta (zonkExpr)
import Stella.Compiler.Elaborate.Surface.Expr (elaborateValue, runSurf)
import Stella.Compiler.Elaborate.Surface.Type (Unsupported(..), elaborateSignature, schemeOf, settledScheme)
import Stella.Compiler.Elaborate.Vocabulary.Diagnostic (Defect, Diagnostic(..))
import Stella.Compiler.Elaborate.Vocabulary.Handle (SessionId(..))
import Stella.Compiler.Elaborate.Surface.Group (groups)
import Stella.Compiler.Interface.Assemble (CoreInterface, CoreTypeSort(..), coreAttribute, reachedFromOutside)
import Stella.Compiler.Interface.Module (Exports, TypeEntity(..), Via(..))
import Stella.Compiler.Interface.Scheme (Scheme, plainScheme)
import Stella.Compiler.Surface.Decl (Declaration(..), declarationOrigin)
import Stella.Compiler.Surface.Decl (Module) as Surface
import Stella.Compiler.Surface.Origin (Origin) as Surface
import Stella.Compiler.TypedCore (Decl(DeclData), Expr, Module) as Core
import Stella.Compiler.TypedCore (Attribute, DataDecl, DeclError(..), DeclFailure, Decl(DeclNonRec, DeclRec), Declared, Export(..), declareAnnotated)
import Stella.Compiler.TypedCore.Declare (ctorInfo, dataEntry)
import Stella.Compiler.TypedCore.AttributeCheck (AttributeError)
import Stella.Compiler.TypedCore.Check (isFunVal)
import Stella.Compiler.TypedCore.Reference (globalsOf)
import Stella.Compiler.TypedCore.Name (Ident(..), ModuleName, Qualified(..), TyName(..))
import Stella.Compiler.TypedCore.Signature (Signature, TyConInfo(..))
import Stella.Compiler.TypedCore.Type (TypeScheme)

data ElaborationError
  -- | A form this version does not elaborate, or one resolution reported.
  = Unsupported Unsupported
  -- | A value declaration with no signature, which this version needs.
  | WithoutSignature Surface.Origin (Qualified Ident)
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
  -- | A Core module the Core checker refused, which is the elaborator's fault.
  | CoreRefused (DeclFailure Surface.Origin)
  -- | An entry a desugaring of the compiler's refers to, which a signature
  -- | reaching its module lacks or holds at another scheme than the one listed:
  -- | the compiler's fault.
  | InternalEntryMismatch (Qualified Ident)
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
-- | decided: those left are jobs of the state it was elaborated into.
type Elaborating =
  { name :: Qualified Ident
  , origin :: Surface.Origin
  , ordinal :: Int
  , attributes :: Array Attribute
  , scheme :: TypeScheme
  , spine :: Scheme
  , body :: XExpr Surface.Origin
  }

-- | A data declaration elaborated, and where it stands.
type ElaboratedData = { origin :: Surface.Origin, decl :: DataDecl }

-- | Elaborate the module's data and value declarations against the signature
-- | and the catalog its imports give.
elaborateValues
  :: Signature
  -> SurfaceEnv
  -> Array CatalogEntry
  -> Surface.Module
  -> { data :: Array ElaboratedData, values :: Array ElaboratedValue, errors :: Array ElaborationError }
elaborateValues imports surface importedEntries m =
  if Array.null dataErrors then
    { data: elaboratedData
    , values: settled'.values
    , errors: internalErrors <> unsupported <> signatureErrors <> bodyErrors <> settled'.errors
    }
  else { data: [], values: [], errors: dataErrors <> unsupported }
  where
  initial0 = initialState (SessionId 0) 1_000_000

  -- the data declarations, each head before any field
  declarations = Array.mapMaybe
    ( case _ of
        DeclData d -> Just d
        _ -> Nothing
    )
    m.declarations
  Tuple dataRead initial = case runAttempt (sessionEnvOf imports importedEntries) (readData surface.synonyms declarations) initial0 of
    Tuple (Done reads) s ->
      let
        settledOnes = map (\r -> { origin: r.declaration.origin, decl: settledData s.tentative.metas r }) reads
      in
        Tuple
          { data: Array.mapMaybe (\d -> map { origin: d.origin, decl: _ } (hush d.decl)) settledOnes
          , errors: Array.concatMap (\d -> either (map Unsupported) (const []) d.decl) settledOnes
          }
          s
    Tuple outcome _ -> Tuple { data: [], errors: [ failure outcome ] } initial0
  elaboratedData = dataRead.data
  dataErrors = dataRead.errors

  -- the signature and the catalog the values are elaborated against: the
  -- imports', with the data types and constructors the module declares
  signature = foldl (addData m.name) imports (map _.decl elaboratedData)
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
    DeclValue d -> Just case d.signature, traverse coreAttribute d.attributes of
      Nothing, _ -> Left (WithoutSignature d.origin d.name)
      _, Left o -> Left (Unsupported (ReportedAlready o))
      Just signature', Right attributes -> Right
        { declared: { name: d.name, origin: d.origin, ordinal, attributes, params: d.params, body: d.body }
        , signature: signature'
        }
    DeclData _ -> Nothing
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
    case runAttempt importedSession (elaborateSignature surface.synonyms c.declared.name c.signature) acc.state of
      Tuple (Done e) s
        | Array.null e.unsupported -> acc { state = s, read = Array.snoc acc.read (Tuple c.declared e) }
        | otherwise -> acc { errors = acc.errors <> map Unsupported e.unsupported }
      Tuple outcome _ -> acc { errors = Array.snoc acc.errors (failure outcome) }

  -- their schemes, once every kind is decided
  settled = map (\(Tuple d e) -> Tuple d (map (\scheme -> { scheme, spine: schemeOf e scheme }) (settledScheme read.state.tentative.metas e))) read.read
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

  -- the catalog the bodies are elaborated against: what the imports publish,
  -- and every value the module declares at its scheme, with its attributes
  own = map (\v -> { name: v.declared.name, sort: ValueEntry, scheme: { kindVars: v.scheme.kindVars, body: fromCore v.scheme.body }, attributes: v.declared.attributes }) schemes
  session = sessionEnvOf signature (imported <> own)
  -- what the bodies read beyond: the module's values taking a synthesized
  -- argument among those the imports declare
  withOwn = surface { synthesizing = surface.synthesizing <> Set.fromFoldable (map _.declared.name (Array.filter (takesSynthesized <<< _.spine) schemes)) }

  -- every body, as one attempt each, a body that does not elaborate leaving
  -- nothing behind
  bodies = foldl bodyOne { state: read.state, bodies: [], errors: [] } schemes
  bodyOne acc v =
    case runAttempt session (runSurf (elaborateValue internal withOwn v.declared.name v.declared.origin v.scheme v.declared.params v.declared.body)) acc.state of
      Tuple (Done (Right body)) s -> acc { state = s, bodies = Array.snoc acc.bodies { name: v.declared.name, origin: v.declared.origin, ordinal: v.declared.ordinal, attributes: v.declared.attributes, scheme: v.scheme, spine: v.spine, body } }
      Tuple (Done (Left problem)) _ -> acc { errors = Array.snoc acc.errors (Unsupported problem) }
      Tuple outcome _ -> acc { errors = Array.snoc acc.errors (failure outcome) }
  bodyErrors = bodies.errors

  settled' = settleBodies (attemptPending session) bodies.state bodies.bodies

-- | A signature with a data type the module declares, and its constructors.
addData :: ModuleName -> Signature -> DataDecl -> Signature
addData self sig decl =
  sig
    { types = Map.insert owner (dataEntry self decl) sig.types
    , ctors = foldl (\acc c -> Map.insert (Qualified self c.name) (ctorInfo owner decl c) acc) sig.ctors decl.constructors
    }
  where
  owner = Qualified self decl.name

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
  :: Attempter
  -> SolverState
  -> Array Elaborating
  -> { values :: Array ElaboratedValue, errors :: Array ElaborationError }
settleBodies attempter state bodies =
  { values: Array.catMaybes (map snd finished)
  , errors: loopErrors <> Array.concatMap fst finished
  }
  where
  Tuple report after = runAttempting attempter state

  -- what the loop stopped at, and the declarations it names; `Nothing` at a
  -- defect, which leaves nothing to trust
  Tuple loopErrors named = case report.result of
    Loop.Completed -> Tuple [] (Just Set.empty)
    Loop.Rejected d -> Tuple [ Rejected d ] (Just (Set.fromFoldable (diagnosticDeclarations d)))
    Loop.Blocked waiting -> Tuple (map (\p -> EquationUndecided p.origin) (NonEmptyArray.toArray waiting)) (Just (Set.fromFoldable (map (\p -> declarationOf p.origin) waiting)))
    Loop.Exhausted p -> Tuple [ EquationUndecided p.origin ] (Just (Set.singleton (declarationOf p.origin)))
    Loop.Halted d -> Tuple [ Broken d ] Nothing

  -- the declarations a job still waits for
  waiting = Set.fromFoldable (map (\p -> declarationOf p.site.origin) (Map.values after.tentative.scheduler.pending))

  finished = map finish bodies
  finish b = case named of
    Nothing -> Tuple [] Nothing
    Just names
      | Set.member b.name names -> Tuple [] Nothing
      | Set.member b.name waiting -> Tuple [ LeftUnchecked b.origin b.name ] Nothing
      | otherwise -> case toCoreExpr (zonkExpr after.tentative.metas b.body) of
          Right body -> Tuple [] (Just { name: b.name, origin: b.origin, ordinal: b.ordinal, attributes: b.attributes, scheme: b.scheme, spine: b.spine, body })
          -- a place is reported once, however many undecided types stand there
          Left residues -> Tuple (map TypeUndetermined (Array.nubEq (map residueOrigin (NonEmptyArray.toArray residues)))) Nothing

  residueOrigin = case _ of
    ResidualTypeMeta o _ -> o
    ResidualKindMeta o _ -> o
    ResidualTermMeta o _ -> o
    ResidualHole o _ -> o

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
-- | against the signature its imports give, its data declarations first.
-- |
-- | **Its values are grouped by what they refer to**, in a stable dependency
-- | order: a recursive group becomes a `DeclRec`, any other value a
-- | `DeclNonRec`. Core binds only function values recursively, so a recursive
-- | group with a member that is none is reported at that member as a form this
-- | version does not elaborate. **A Core module is made only of a module with
-- | no error**: one missing a declaration would refer to what it does not bind. It imports what
-- | the module imports, and exports each value it declares that is reached from
-- | outside — by its name, as a macro, or through an operator it exports —
-- | and each data type it declares and exports, with the constructors it
-- | exports of it. The Core part of its interface holds each data type it
-- | declares and the scheme of every value and constructor; a module this
-- | version elaborates declares no other type, and no effect or attribute.
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
  -- outside what this version lowers, whether or not the surface admits it
  recursiveValues = Array.concatMap
    ( \g ->
        if g.recursive then map (\v -> Unsupported (OutsideSubset v.origin "a recursive value that is no function")) (Array.filter (not <<< isFunVal <<< _.body) (members g))
        else []
    )
    grouped
  errors = elaborated.errors <> recursiveValues

  decls = map (\d -> Core.DeclData d.origin d.decl) elaborated.data <> map
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
        <> map (ExportValue <<< nameOf <<< _.name) (Array.filter (reachedFromOutside m.name exports operators <<< nameOf <<< _.name) values)
    , decls
    }
  result = case NonEmptyArray.fromArray errors of
    Just es -> Left es
    Nothing -> case declareAnnotated signature core of
      Right declared -> Right { core, declared, interface }
      -- an attribute's arguments are checked by Core alone
      Left { at, error: AttributeIllTyped err } -> Left (NonEmptyArray.singleton (AttributeRejected at err))
      Left refusal -> Left (NonEmptyArray.singleton (CoreRefused refusal))

  -- a data type exported, abstractly or with the constructors exported of it
  typeExports d
    | declaredHere (map (\e -> e.entity == TypeEntity (Qualified m.name d.decl.name) && e.via == Declared) (Map.lookup (tyNameText d.decl.name) exports.types)) =
        [ ExportType d.decl.name ] <> map (ExportCtor <<< _.name) (Array.filter (\c -> exportedValue c.name) d.decl.constructors)
    | otherwise = []
  exportedValue c = declaredHere (map (\e -> e.entity == Qualified m.name c && e.via == Declared) (Map.lookup (identText c) exports.values))
  declaredHere = case _ of
    Just true -> true
    _ -> false

  interface =
    { schemes: Map.fromFoldable
        ( map (\v -> Tuple (nameOf v.name) v.spine) values
            <> Array.concatMap (\d -> map (\c -> Tuple c.name (plainScheme (ctorInfo (Qualified m.name d.decl.name) d.decl c).scheme)) d.decl.constructors) elaborated.data
        )
    , types: Map.fromFoldable (map (\d -> Tuple d.decl.name { kind: dataKind d.decl, sort: CoreData { params: d.decl.params, fields: map _.fields d.decl.constructors } }) elaborated.data)
    , effects: Map.empty
    , attributes: Map.empty
    , implicitHandlers: Map.empty
    }

  nameOf (Qualified _ n) = n
  identText (Ident n) = n
  tyNameText (TyName n) = n

  -- `T : forall k̄. κ̄ -> Type`
  dataKind decl = case dataEntry m.name decl of
    DataTyCon kind _ -> kind
    IntrinsicTyCon kind _ -> kind
