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
module Stella.Compiler.Elaborate.Handle
  ( SessionId(..)
  , HandleClass(..)
  , Handle(..)
  , GoalObject
  , TypeObject
  , ExprObject
  , ScopeObject
  , BinderObject(..)
  , ScopeId(..)
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

import Stella.Compiler.Elaborate.Context (XContext)
import Stella.Compiler.Elaborate.Kind (XKind)
import Stella.Compiler.Elaborate.Kinding (KindEvidence, KindingScope)
import Stella.Compiler.Elaborate.Pending (GoalRecord, PendingId)
import Stella.Compiler.Elaborate.Term (XExpr)
import Stella.Compiler.Elaborate.Type (MetaVar, XConstraint, XType)
import Stella.Compiler.TypedCore (TyVar)
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

-- | A build scope: where a builder assembles types. `ancestors` are the scopes
-- | it was opened inside, and `context` is what it binds, which is what a type
-- | built in it is kinded under.
type ScopeObject =
  { id :: ScopeId
  , ancestors :: Set ScopeId
  , context :: XContext
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

-- | The identity of a build scope within an attempt. The root, opened on the
-- | site of the running job, is 0.
newtype ScopeId = ScopeId P.Int

-- | A term, held without annotations, with the type it is claimed to have, the
-- | scope that type is kinded under, and the build scope the term was built in.
-- | The last is what says where the term may be placed, as a type's says where
-- | it may be used.
type ExprObject =
  { term :: XExpr Unit
  , claimed :: XType
  , scope :: KindingScope
  , builtIn :: Maybe ScopeId
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
derive newtype instance Show SessionId

derive instance Eq HandleClass
derive instance Generic HandleClass _

instance Show HandleClass where
  show x = genericShow x

derive instance Eq Handle
derive newtype instance Show Handle

derive instance Eq ScopeId
derive instance Ord ScopeId
derive newtype instance Show ScopeId

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
