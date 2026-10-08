-- | A module as loading leaves it
-- | ([Abstract Machine](../../../docs/technical-references/07-Runtime/01-Abstract-Machine.md)).
-- |
-- | **Every index a file writes is resolved here.** A `.dmo` names a constructor
-- | by an index into its own `CTORREFS` and a key by an index into its own
-- | `KEYS`, and those indices are that file's own; what a running program
-- | compares is the identity the registry assigned. So each table below stands in
-- | the order the file wrote it, holding what the file's index resolves to.
-- |
-- | **A join point is resolved here as well.** A file holds a name so that the
-- | structure survives the format, and what a running function reaches a `Join` by
-- | is the table built below — never a search of the function's join list.
module Steam.Module
  ( Registry
  , Loaded
  , CtorRef
  , ForeignRef
  , HandlerRef
  , ClauseRef
  , RegionRef
  , GlobalSlot
  , CalleeTarget(..)
  , Prepared
  , prepare
  ) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldM)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe)
import Effect.Ref (Ref)
import Steam.Value (CtorId, Foreign, KeyId, ModuleId, OpId, Value)
import Stella.Compiler.Primitive (PrimOp)
import Stella.Compiler.Bytecode.Instr (Function, Join, JoinName, Node)
import Stella.Compiler.MiddleEnd.IR (ClauseForm)
import Stella.Compiler.Bytecode.Module (Constant)

-- | The modules loaded, under the identities the registry assigned. A closure
-- | names the module its function belongs to, so what runs a closure reaches that
-- | module's tables through this.
type Registry = Map ModuleId Loaded

type Loaded =
  { id :: ModuleId
  -- | The literal pool, which `LOADK` and dispatch on a literal read.
  , constants :: P.Array Constant
  -- | One entry per `KEYS` index, as the key it resolves to.
  , keys :: P.Array KeyId
  -- | One entry per `OPS` index, as the operation name it resolves to. A clause of
  -- | a handler is found by one, and the `perform` and the handler need not be in
  -- | one module.
  , ops :: P.Array OpId
  -- | One entry per `CTORREFS` index: the constructors this module's code names,
  -- | its own and those of the modules it imports.
  , ctors :: P.Array CtorRef
  -- | One entry per `GLOBALREFS` index, as the slot of the module declaring it.
  , globals :: P.Array GlobalSlot
  -- | One entry per `FOREIGNREFS` index: what carries out the foreign this
  -- | module's code names.
  , foreigns :: P.Array ForeignRef
  -- | One entry per `CALLEES` index: what a partial application is over.
  , callees :: P.Array CalleeTarget
  -- | One entry per `PRIMS` index: the operations this module carries out.
  , prims :: P.Array PrimOp
  -- | One entry per `HANDLERS` index, with every key and operation resolved.
  , handlers :: P.Array HandlerRef
  -- | One entry per `REGIONS` index, with every key resolved.
  , regions :: P.Array RegionRef
  -- | `Prim.Unit`, which a write to a cell produces. Core names the constructor and
  -- | no module declares it, so the identity is the registry's like any other.
  , unit :: Value
  , functions :: P.Array Prepared
  }

-- | A handler as a file states it: the key it answers, and a clause per
-- | operation.
type HandlerRef =
  { key :: KeyId
  , opClauses :: P.Array ClauseRef
  }

-- | A region as a file states it: the keys of its cells, in the order of their
-- | positions.
type RegionRef =
  { cells :: P.Array KeyId
  }

type ClauseRef =
  { op :: OpId
  , form :: ClauseForm
  }

-- | Where a top-level value stands once its module is initialized. A slot holds
-- | nothing until then, and nothing reads one before: a module's imports are
-- | initialized before it is, and its own globals in declaration order.
type GlobalSlot = Ref (Maybe Value)

-- | What a `CALLEES` entry resolves to.
-- |
-- | A constructor's and a foreign's arity is what its declaration states. An
-- | operation's is the ABI's, with one definition in `arityOfOp`, so it is not
-- | carried here.
data CalleeTarget
  = TargetGlobal GlobalSlot
  | TargetCtor CtorId P.Int
  | TargetForeign Foreign P.Int
  | TargetPrim PrimOp

-- | A foreign a module's code names, with the arity its declaration states.
type ForeignRef =
  { carriedOutBy :: Foreign
  , arity :: P.Int
  }

-- | A constructor a module's code names, with the arity its declaration states.
-- | A constructor is applied all at once or through a partial application, so an
-- | application of any other length is a module no lowering produces.
type CtorRef =
  { id :: CtorId
  , arity :: P.Int
  }

-- | A function as loading leaves it: the body to enter, and the join points a
-- | transfer inside it reaches, under the names its transfers carry.
-- |
-- | `ncaptures` is how many capture slots a closure over this function has. A
-- | closure is built with that many and each is filled once, which is what a
-- | recursive group needs (D14).
type Prepared =
  { nparams :: P.Int
  , ncaptures :: P.Int
  , body :: Node
  , joins :: Map JoinName Join
  }

-- | What loading makes of a function: the body to enter, and its join points under
-- | the names its transfers carry.
-- |
-- | **A name stands over one join point of a function**, so a file writing two under
-- | one name has no reading and is refused; what comes back is the name it wrote
-- | twice.
prepare :: Function -> Either JoinName Prepared
prepare function = do
  joins <- foldM one Map.empty function.joins
  pure
    { nparams: function.nparams
    , ncaptures: Array.length function.captures
    , body: function.body
    , joins
    }
  where
  one acc join
    | Map.member join.name acc = Left join.name
    | otherwise = Right (Map.insert join.name join acc)
