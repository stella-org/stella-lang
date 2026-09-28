-- | Opaque handles: how a goal, a type, a term, and a metavariable reach a
-- | synthesizer without their representation doing so.
-- |
-- | A handle names an object in the **arena**, and carries four things: the
-- | session that issued it, the class of object it claims to name, the slot the
-- | object stands in, and the generation it was issued under.
-- |
-- | **The arena lives for one attempt, and its contents are transactional.** An
-- | attempt begins and commits with it empty, and a rollback restores it to what
-- | the checkpoint held, so a handle issued by a candidate `transact` discarded
-- | is gone while one issued before that `transact` stands. A synthesizer holds
-- | nothing across an attempt, and what it hands back is resolved before the
-- | attempt ends, so nothing needs a handle to outlive one.
-- |
-- | **Slots are reused and generations never are.** A slot freed by a rollback,
-- | or by the end of an attempt, is filled again by the next object issued; the
-- | generation comes from a counter no rollback restores, so the new object
-- | carries a generation no earlier handle does, and an old handle presented
-- | again matches nothing.
-- |
-- | **Every field of a presented handle is untrusted.** One crosses a transport
-- | as a token, so its class is checked against the object the arena holds as
-- | well as against the class the request expects.
module Stella.Compiler.Elaborate.Vocabulary.Handle
  ( SessionId(..)
  , HandleClass(..)
  , Handle(..)
  , GoalObject
  , TypeObject
  , ExprObject
  , ScopeObject
  , JoinSignature
  , JoinObject
  , TreeObject
  , OccurrenceObject
  , SwitchBranches(..)
  , BinderObject(..)
  , ScopeId(..)
  , rootScopeId
  , HandleObject(..)
  , Arena
  , HandleError(..)
  , emptyArena
  , objectClass
  , issueIn
  , resolveIn
  ) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.CorePlus.Context (XContext)
import Stella.Compiler.Elaborate.CorePlus.Kind (XKind)
import Stella.Compiler.Elaborate.Mechanism.Kinding (KindEvidence, KindingScope)
import Stella.Compiler.Elaborate.Mechanism.Pending (GoalRecord, PendingId)
import Stella.Compiler.Elaborate.CorePlus.Term (Region, XDecisionTree, XExpr)
import Stella.Compiler.Elaborate.CorePlus.Type (MetaVar, XConstraint, XRowEntry, XType)
import Stella.Compiler.TypedCore (Ident, JoinName, Literal, Occurrence, OpName, Qualified, RowKey, TyVar)
import Data.Either (Either(..))
import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Show.Generic (genericShow)
import Data.Tuple (Tuple(..))

-- | The compile-time session a handle belongs to. A session manager issues each
-- | one once for the life of the process running the guest.
newtype SessionId = SessionId P.Int

data HandleClass
  = GoalClass
  | TypeClass
  | ExprClass
  | MetaClass
  | ScopeClass
  | BinderClass
  | JoinClass
  | TreeClass
  | OccurrenceClass

newtype Handle = Handle
  { session :: SessionId
  , handleClass :: HandleClass
  , slot :: P.Int
  , generation :: P.Int
  }

-- | The goal the current attempt runs.
type GoalObject =
  { id :: PendingId
  , goal :: GoalRecord
  }

-- | A type, with the kind evidence it stands at and the scope it is kinded under:
-- | the rigid kind variables and the type variables it may mention free. A
-- | type from a site has the site's; one a view reached under a binder has that
-- | binder added; a catalog scheme has its own kind variables. Holding it is what
-- | lets a type be kinded again wherever it is taken apart.
type TypeObject =
  { type :: XType
  , kind :: KindEvidence
  , scope :: KindingScope
  , builtIn :: Maybe ScopeId
  }

-- | A build scope: where a builder assembles types and terms. `ancestors` are
-- | the scopes it was opened inside; `context` is what it binds, which is what a
-- | type built in it is kinded under; and `joins` is `Δ`, the join points a term
-- | built in it may jump to, each with its parameters' types and its result.
-- | `tree` is the `case` whose decision tree the scope stands in, where it stands
-- | in one: the scope a tree node is built in, and the only one an occurrence of
-- | that `case` is read in.
-- | `region` is the region of cells a term built in it reads and writes, where it
-- | stands in one: lexical, as a cell is named by its key and means the
-- | innermost region around it.
type ScopeObject =
  { id :: ScopeId
  , ancestors :: Set ScopeId
  , context :: XContext
  , joins :: Map JoinName JoinSignature
  , tree :: Maybe ScopeId
  , region :: Maybe Region
  }

-- | A decision tree, with the type the first leaf it reaches is claimed at, where
-- | it reaches one, the `case` it belongs to, named by the scope its tree is
-- | built in, and the build scope it was built in. Its occurrences are paths
-- | from that `case`'s scrutinees, so it means nothing in another's tree.
type TreeObject =
  { tree :: XDecisionTree Unit
  , inferred :: Maybe XType
  , case :: ScopeId
  , builtIn :: Maybe ScopeId
  }

-- | An occurrence of a `case`: its path from a scrutinee, the type it stands at
-- | there, the `case` it belongs to, named by the scope its tree is built in, and
-- | the build scope of the branch that established it.
type OccurrenceObject =
  { path :: Occurrence
  , type :: XType
  , case :: ScopeId
  , builtIn :: Maybe ScopeId
  }

-- | The branches a switch was opened with, each with the scope its tree is built
-- | in.
data SwitchBranches
  = CtorBranches (P.Array { ctor :: Qualified Ident, scope :: ScopeId })
  | LitBranches (P.Array { lit :: Literal, scope :: ScopeId })
  | KeyBranches (P.Array { key :: RowKey, scope :: ScopeId })

-- | What a join point takes and gives.
type JoinSignature =
  { params :: P.Array XType
  , result :: XType
  }

-- | A join point a `letjoin` binds: its name and signature, and the scope of
-- | the `letjoin` it belongs to, under which alone it can be jumped to.
type JoinObject =
  { name :: JoinName
  , signature :: JoinSignature
  , hub :: ScopeId
  }

-- | What an open operation hands back to be closed: what was opened, the scope
-- | it was opened in, and the scope its body is built in. The body's scope also
-- | identifies the binder among those an attempt holds open.
data BinderObject
  -- | A `forall (name : kind)`.
  = ForallBinder
      { name :: TyVar
      , kind :: XKind
      , parent :: ScopeId
      , body :: ScopeId
      }
  -- | A `constraint =>`, assumed in the body's scope.
  | AssumedConstraint
      { constraint :: XConstraint
      , parent :: ScopeId
      , body :: ScopeId
      }
  -- | A `λ(name : type)`.
  | LambdaBinder
      { name :: Ident
      , type :: XType
      , parent :: ScopeId
      , body :: ScopeId
      }
  -- | A `Λ(name : kind)`.
  | TypeAbsBinder
      { name :: TyVar
      , kind :: XKind
      , parent :: ScopeId
      , body :: ScopeId
      }
  -- | A `Λ(_ : constraint)`, assumed in the body's scope.
  | ConstraintAbsBinder
      { constraint :: XConstraint
      , parent :: ScopeId
      , body :: ScopeId
      }
  -- | A `let name : type = rhs in`, the right-hand side built in the parent.
  | LetBinder
      { name :: Ident
      , type :: XType
      , rhs :: XExpr Unit
      , parent :: ScopeId
      , body :: ScopeId
      }
  -- | A `letrec`, every name bound in every right-hand side and in the body.
  | LetRecGroup
      { bindings :: P.Array { name :: Ident, type :: XType }
      , parent :: ScopeId
      , body :: ScopeId
      }
  -- | A `case`, its scrutinees built in the parent. Its body is the scope its
  -- | decision tree is built in.
  | CaseBinder
      { scrutinees :: P.Array (XExpr Unit)
      , parent :: ScopeId
      , body :: ScopeId
      }
  -- | A `bind name = occurrence in`.
  | BindBinder
      { name :: Ident
      , occurrence :: Occurrence
      , parent :: ScopeId
      , body :: ScopeId
      }
  -- | A `handle`, its handled computation built in the parent. Its body scope
  -- | holds the return clause's scope and one for each operation clause.
  | HandleBinder
      { computation :: XExpr Unit
      , element :: XRowEntry
      , layout :: Maybe { var :: TyVar, cells :: P.Array { key :: RowKey, ty :: XType } }
      , answer :: XType
      , residual :: XType
      , returnClause :: { name :: Ident, type :: XType, scope :: ScopeId }
      , clauses ::
          P.Array
            { op :: OpName
            , tyBinders :: P.Array { name :: TyVar, kind :: XKind }
            , argument :: { name :: Ident, ty :: XType }
            , continuation :: Maybe { name :: Ident, ty :: XType }
            , scope :: ScopeId
            }
      , parent :: ScopeId
      , body :: ScopeId
      }
  -- | A switch on an occurrence. Its body scope holds one scope per branch, and
  -- | one for the default where it has one.
  | SwitchBinder
      { occurrence :: Occurrence
      , branches :: SwitchBranches
      , fallback :: Maybe ScopeId
      , parent :: ScopeId
      , body :: ScopeId
      }
  -- | A `letjoin`. Its body scope holds two scopes: the definition's, binding
  -- | the parameters and the join point, and the continuation's, binding the
  -- | join point alone.
  | JoinBinder
      { name :: JoinName
      , params :: P.Array { name :: Ident, type :: XType }
      , result :: XType
      , parent :: ScopeId
      , body :: ScopeId
      , definition :: ScopeId
      , continuation :: ScopeId
      }

-- | The identity of a build scope within an attempt. The root, opened on the
-- | site of the running job, is `rootScopeId`; every other is drawn from a
-- | supply starting after it.
newtype ScopeId = ScopeId P.Int

rootScopeId :: ScopeId
rootScopeId = ScopeId 0

-- | A term, held without annotations, with the type it is claimed to have, the
-- | scope that type is kinded under, the build scope the term was built in, and
-- | the region of cells that scope stands in. The build scope says where the
-- | term may be placed, as a type's says where it may be used; the region says
-- | which cells a `readCell` in it, or a goal it waits on, means.
type ExprObject =
  { term :: XExpr Unit
  , claimed :: XType
  , scope :: KindingScope
  , builtIn :: Maybe ScopeId
  , region :: Maybe Region
  }

-- | What a slot holds. Objects are immutable: what changes is issued anew.
-- |
-- | A metavariable a synthesizer can name is a type metavariable, that being
-- | what a job waits on.
data HandleObject
  = GoalObject GoalObject
  | TypeObject TypeObject
  | ExprObject ExprObject
  | MetaObject MetaVar
  | ScopeObject ScopeObject
  | BinderObject BinderObject
  | JoinObject JoinObject
  | TreeObject TreeObject
  | OccurrenceObject OccurrenceObject

type Arena =
  { slots :: Map P.Int { generation :: P.Int, object :: HandleObject }
  , nextSlot :: P.Int
  }

-- | Why a handle names no object. Each is a defect of whoever presented it.
data HandleError
  -- | A handle another session issued.
  = ForeignHandle
  -- | A generation this session never issued, which no handle it gave out
  -- | carries.
  | UnknownHandle
  -- | A handle to an object no longer held: deleted by a rollback or by the end
  -- | of the attempt that issued it, or its slot since filled by another.
  | StaleHandle
  -- | A handle presented where another class is expected, or whose class is not
  -- | the class of the object its slot holds.
  | HandleClassMismatch HandleClass

emptyArena :: Arena
emptyArena = { slots: Map.empty, nextSlot: 0 }

objectClass :: HandleObject -> HandleClass
objectClass = case _ of
  GoalObject _ -> GoalClass
  TypeObject _ -> TypeClass
  ExprObject _ -> ExprClass
  MetaObject _ -> MetaClass
  ScopeObject _ -> ScopeClass
  BinderObject _ -> BinderClass
  JoinObject _ -> JoinClass
  TreeObject _ -> TreeClass
  OccurrenceObject _ -> OccurrenceClass

-- | Place an object in the next slot, under the generation given. The caller
-- | supplies a generation no handle has carried before.
issueIn :: SessionId -> P.Int -> HandleObject -> Arena -> Tuple Handle Arena
issueIn session generation object arena =
  Tuple
    (Handle { session, handleClass: objectClass object, slot: arena.nextSlot, generation })
    arena
      { slots = Map.insert arena.nextSlot { generation, object } arena.slots
      , nextSlot = arena.nextSlot + 1
      }

-- | The object a handle names, where it names one of the class expected.
-- |
-- | Whether the generation was ever issued is decided before the slot is read,
-- | so a forged generation is reported as unknown rather than as stale; and the
-- | class is compared both as the handle states it and as the object is.
resolveIn :: SessionId -> P.Int -> HandleClass -> Handle -> Arena -> Either HandleError HandleObject
resolveIn session nextGeneration expected (Handle h) arena
  | h.session /= session = Left ForeignHandle
  | h.generation < 0 || h.generation >= nextGeneration = Left UnknownHandle
  | otherwise = case Map.lookup h.slot arena.slots of
      Nothing -> Left StaleHandle
      Just entry
        | entry.generation /= h.generation -> Left StaleHandle
        | h.handleClass /= expected || objectClass entry.object /= expected ->
            Left (HandleClassMismatch expected)
        | otherwise -> Right entry.object

derive instance Eq SessionId
derive instance Ord SessionId
derive newtype instance Show SessionId

derive instance Eq HandleClass
derive instance Ord HandleClass
derive instance Generic HandleClass _

instance Show HandleClass where
  show x = genericShow x

derive instance Eq Handle
derive instance Ord Handle
derive newtype instance Show Handle

derive instance Eq ScopeId
derive instance Ord ScopeId
derive newtype instance Show ScopeId

derive instance Eq SwitchBranches
derive instance Generic SwitchBranches _

instance Show SwitchBranches where
  show x = genericShow x

derive instance Eq BinderObject
derive instance Generic BinderObject _

instance Show BinderObject where
  show x = genericShow x

derive instance Eq HandleObject
derive instance Generic HandleObject _

instance Show HandleObject where
  show x = genericShow x

derive instance Eq HandleError
derive instance Generic HandleError _

instance Show HandleError where
  show x = genericShow x
