-- | The type an operation is called at (D17), which an interface publishes for
-- | it and the surface elaborator calls it at
-- | ([Effects](../../../../docs/technical-references/03-Typed-Core/03-Effects.md)).
-- |
-- | **An operation is built at one type wherever it is declared**: from the
-- | arguments it is written with where its declaration is read from source, and
-- | from Core's one argument as its one argument where it is read from Core,
-- | which does not keep them — a record of positions is also what one argument
-- | of a tuple type is.
module Stella.Compiler.Interface.Operation
  ( Operation
  , operationElement
  , operationKey
  , operationOf
  , operationRest
  , operationRow
  , operationScheme
  ) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Foldable (foldr)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Set as Set
import Stella.Compiler.TypedCore.Kind (Kind(..), RowElemKind(..), monoScheme)
import Stella.Compiler.TypedCore.Name (EffName, OpName, Qualified, Symbol, TyVar(..))
import Stella.Compiler.TypedCore.Prim (fn, unitTy)
import Stella.Compiler.TypedCore.Type (Constraint(..), RowEntry(..), RowKey(..), TyBinder, Type(..), TypeScheme)

-- | An operation of an effect: the effect, the effect's parameters, the
-- | operation's own type variables, the arguments it is written with, at
-- | least one, and the type it resumes with.
type Operation =
  { effect :: Qualified EffName
  , name :: OpName
  , params :: P.Array TyBinder
  , binders :: P.Array TyBinder
  , arguments :: P.Array Type
  , resumesWith :: Type
  }

-- | An operation as its effect declares it. **An operation is written with at
-- | least one argument**, so one an interface gives none takes `Prim.Unit`, as
-- | Core's one argument does.
operationOf
  :: Qualified EffName
  -> P.Array TyBinder
  -> { name :: OpName, binders :: P.Array TyBinder, arguments :: P.Array Type, resumesWith :: Type }
  -> Operation
operationOf effect params o =
  { effect
  , name: o.name
  , params
  , binders: o.binders
  , arguments: if Array.null o.arguments then [ TCon unitTy [] ] else o.arguments
  , resumesWith: o.resumesWith
  }

-- | The key an operation is performed at: its effect's, or the label of the
-- | instance written.
operationKey :: Maybe Symbol -> Operation -> RowKey
operationKey label op = case label of
  Just l -> SymbolKey l
  Nothing -> EffectKey op.effect

-- | The element an operation is performed on, over the effect's parameters.
operationElement :: Maybe Symbol -> Operation -> RowEntry
operationElement label op = case label of
  Just l -> RowLabelledEffectEntry l op.effect params
  Nothing -> RowEffectEntry op.effect params
  where
  params = map (\b -> TVar b.name) op.params

-- | The type an operation is called at: the effect's parameters, the
-- | operation's own type variables, and the rest of the row, quantified in that
-- | order, the rest lacking the element's key. **Only the last arrow, the one
-- | `->*` writes, carries a row**: the element over the rest. Applying an
-- | operation short of its arguments performs nothing.
operationScheme :: Maybe Symbol -> Operation -> TypeScheme
operationScheme label op = monoScheme (foldr (\b t -> TForall b.name b.kind t) constrained (op.params <> op.binders <> [ { name: rest, kind: KRow RowEffect } ]))
  where
  rest = operationRest op
  constrained = TConstrained (Lacks (operationKey label op) (TVar rest)) body
  body = case Array.unsnoc op.arguments of
    Just { init, last } -> foldr (\a t -> fn a TRowEmpty t) (fn last (operationRow label op) op.resumesWith) init
    Nothing -> op.resumesWith

-- | The row the last arrow carries: the element over the rest.
operationRow :: Maybe Symbol -> Operation -> Type
operationRow label op = TRowExtend (operationElement label op) (TVar (operationRest op))

-- | The variable the rest of the row is quantified as: a name no variable of
-- | the operation's has.
operationRest :: Operation -> TyVar
operationRest op = fromMaybe (TyVar "e") (Array.find (\v -> not (Set.member v taken)) (map (\n -> TyVar ("e" <> if n == 0 then "" else show n)) (Array.range 0 (Array.length op.params + Array.length op.binders))))
  where
  taken = Set.fromFoldable (map (\b -> b.name) (op.params <> op.binders))
