-- | A module's value declarations elaborated into Core terms, against what its
-- | imports reach ([Elaboration](../../../../../docs/technical-references/02-Surface-Language/01-Elaboration.md)).
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
-- | **A value declaration needs a signature in this version**, and every other
-- | declaration is outside what it elaborates.
module Stella.Compiler.Elaborate.Surface.Module
  ( ElaborationError(..)
  , ElaboratedValue
  , Elaborating
  , elaborateValues
  , settleBodies
  ) where

import Prelude
import Prim hiding (Type)

import Data.Array as Array
import Data.Array.NonEmpty as NonEmptyArray
import Data.Either (Either(..))
import Data.Foldable (foldl)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Data.Tuple (Tuple(..), fst, snd)
import Stella.Compiler.Elaborate.CorePlus.Context (Origin(..))
import Stella.Compiler.Elaborate.CorePlus.Term (Residue(..), XExpr, toCoreExpr)
import Stella.Compiler.Elaborate.CorePlus.Type (fromCore)
import Stella.Compiler.Elaborate.Driver.Attempt (attemptPending, runAttempt)
import Stella.Compiler.Elaborate.Driver.Loop (Attempter, runAttempting)
import Stella.Compiler.Elaborate.Driver.Loop as Loop
import Stella.Compiler.Elaborate.Environment.Catalog (CatalogEntry, EntrySort(..))
import Stella.Compiler.Elaborate.Environment.Imported (sessionEnvOf)
import Stella.Compiler.Elaborate.Kernel.Elab (Outcome(..), SolverState, initialState)
import Stella.Compiler.Elaborate.Mechanism.TermMeta (zonkExpr)
import Stella.Compiler.Elaborate.Surface.Expr (elaborateValue, runSurf)
import Stella.Compiler.Elaborate.Surface.Type (Unsupported(..), elaborateSignature, settledScheme)
import Stella.Compiler.Elaborate.Vocabulary.Diagnostic (Defect, Diagnostic(..))
import Stella.Compiler.Elaborate.Vocabulary.Handle (SessionId(..))
import Stella.Compiler.Surface.Decl (Declaration(..), declarationOrigin)
import Stella.Compiler.Surface.Decl (Module) as Surface
import Stella.Compiler.Surface.Expr (Binder, Expr)
import Stella.Compiler.Surface.Origin (Origin) as Surface
import Stella.Compiler.TypedCore (Expr) as Core
import Stella.Compiler.TypedCore.Name (Ident, Qualified)
import Stella.Compiler.TypedCore.Signature (Signature)
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
  -- | An attempt that postponed itself, which nothing the elaborator states
  -- | does: it is the elaborator's fault.
  | AttemptPostponed

-- | A value declaration elaborated: its name, where it was declared, its
-- | scheme, and its definition as a Core term, located by the Surface AST.
type ElaboratedValue =
  { name :: Qualified Ident
  , origin :: Surface.Origin
  , scheme :: TypeScheme
  , body :: Core.Expr Surface.Origin
  }

-- | A value declaration whose body is elaborated, its equations not yet all
-- | decided: those left are jobs of the state it was elaborated into.
type Elaborating =
  { name :: Qualified Ident
  , origin :: Surface.Origin
  , scheme :: TypeScheme
  , body :: XExpr Surface.Origin
  }

type Declared = { name :: Qualified Ident, origin :: Surface.Origin, params :: Array Binder, body :: Expr }

-- | Elaborate the module's value declarations against the signature and the
-- | catalog its imports give.
elaborateValues
  :: Signature
  -> Array CatalogEntry
  -> Surface.Module
  -> { values :: Array ElaboratedValue, errors :: Array ElaborationError }
elaborateValues signature imported m =
  { values: settled'.values
  , errors: unsupported <> signatureErrors <> bodyErrors <> settled'.errors
  }
  where
  initial = initialState (SessionId 0) 1_000_000

  -- the value declarations, and what else the module declares
  candidates = map candidate m.declarations
  candidate = case _ of
    DeclValue d -> case d.signature of
      Just signature' -> Right { declared: { name: d.name, origin: d.origin, params: d.params, body: d.body }, signature: signature' }
      Nothing -> Left (WithoutSignature d.origin d.name)
    other -> Left (Unsupported (OutsideSubset (declarationOrigin other) "this declaration"))
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
    case runAttempt importedSession (elaborateSignature c.declared.name c.signature) acc.state of
      Tuple (Done e) s
        | Array.null e.unsupported -> acc { state = s, read = Array.snoc acc.read (Tuple c.declared e) }
        | otherwise -> acc { errors = acc.errors <> map Unsupported e.unsupported }
      Tuple outcome _ -> acc { errors = Array.snoc acc.errors (failure outcome) }

  -- their schemes, once every kind is decided
  settled = map (\(Tuple d e) -> Tuple d (settledScheme read.state.tentative.metas e)) read.read
  schemes = Array.mapMaybe
    ( \(Tuple d s) -> case s of
        Right scheme -> Just { declared: d, scheme }
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
  -- and every value the module declares at its scheme
  own = map (\v -> { name: v.declared.name, sort: ValueEntry, scheme: { kindVars: v.scheme.kindVars, body: fromCore v.scheme.body }, attributes: [] }) schemes
  session = sessionEnvOf signature (imported <> own)

  -- every body, as one attempt each, a body that does not elaborate leaving
  -- nothing behind
  bodies = foldl bodyOne { state: read.state, bodies: [], errors: [] } schemes
  bodyOne acc v =
    case runAttempt session (runSurf (elaborateValue v.declared.name v.declared.origin v.scheme v.declared.params v.declared.body)) acc.state of
      Tuple (Done (Right body)) s -> acc { state = s, bodies = Array.snoc acc.bodies { name: v.declared.name, origin: v.declared.origin, scheme: v.scheme, body } }
      Tuple (Done (Left problem)) _ -> acc { errors = Array.snoc acc.errors (Unsupported problem) }
      Tuple outcome _ -> acc { errors = Array.snoc acc.errors (failure outcome) }
  bodyErrors = bodies.errors

  settled' = settleBodies (attemptPending session) bodies.state bodies.bodies

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
          Right body -> Tuple [] (Just { name: b.name, origin: b.origin, scheme: b.scheme, body })
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
