-- | What a translation reads of the modules it is compiled against: the
-- | **definitional arity** of each value a module declares and exports that has
-- | one, which is what lets a saturated call to it be a `callk`
-- | ([Interface](../../../docs/technical-references/05-Backend/03-Interface.md)).
-- | A type does not determine that arity, so nothing else carries it; where it
-- | is absent the call is a `callu`, correct for every callee.
-- |
-- | **What translation reads is `Imports`, not an array of interfaces.** An
-- | interface in memory need not have come through a reader, and an arity
-- | translation cannot trust is worse than no arity at all, so `importsOf`
-- | checks the arities as a reader of the bytes checks them and `Imports` is the
-- | only thing that reaches a translation.
-- |
-- | **This module holds no bytes.** Translation reads an interface, and a stage
-- | upstream of a backend must not depend on one; the file is
-- | [Interface.File](Interface/File.purs).
module Stella.Compiler.Interface
  ( aritiesOf
  , Imports
  , InterfaceError(..)
  , noImports
  , importsOf
  , importedArities
  ) where

import Prelude

import Prim as P

import Stella.Compiler.MiddleEnd.IR as MIR
import Stella.Compiler.TypedCore.Name (Ident, ModuleName, Qualified(..))
import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldM)
import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Set as Set
import Data.Show.Generic (genericShow)
import Data.Tuple (Tuple(..))

-- | The definitional arity of each value a module declares and exports that
-- | has one, read off the module a lowering is handed.
-- |
-- | A global installed as a **function** has a definitional arity, which is the
-- | number of parameters of the function table entry it names; one evaluated at
-- | initialization has none. So the arity is read where the `.dmo`'s own entry
-- | was decided and nothing computes it twice.
-- |
-- | A global installed as a function of **no** parameters has no definitional
-- | arity either: a count of leading lambdas that is zero is what absence is.
aritiesOf :: MIR.Module -> Map Ident P.Int
aritiesOf m = Map.fromFoldable (Array.mapMaybe entry m.exports)
  where
  installed = Map.fromFoldable (map (\g -> Tuple g.ref g.init) m.globals)
  functions = Map.fromFoldable (map (\f -> Tuple f.id f) m.functions)

  -- a module speaks for its own values, so an export of another's name
  -- contributes nothing
  entry ref = case ref of
    Qualified moduleName name
      | moduleName /= m.name -> Nothing
      | otherwise -> case Map.lookup ref installed of
          Just (MIR.GFunc id) -> case Map.lookup id functions of
            Just f
              | Array.length f.params > 0 -> Just (Tuple name (Array.length f.params))
            _ -> Nothing
          _ -> Nothing

-- | The interfaces one translation is compiled against: each module's arities,
-- | under the qualified names a term carries, **checked** — every arity is at
-- | least one, and one module has one interface — and the modules each imports,
-- | which is what the dependencies of a module are read from. Only
-- | [importsOf](#v:importsOf) builds one.
newtype Imports = Imports
  { arities :: Map (Qualified Ident) P.Int
  , imports :: Map ModuleName (P.Array ModuleName)
  }

-- | What a translation is handed where it is compiled against nothing, which
-- | is also what an interface it was not given amounts to: every call to
-- | another module's value is a `callu`.
noImports :: Imports
noImports = Imports { arities: Map.empty, imports: Map.empty }

-- | What an interface may hold that no translation may act on.
data InterfaceError
  -- | An arity below one, under the module and the name it stands in. A
  -- | definitional arity counts leading lambdas, so a value with none is absent
  -- | from an interface rather than present at zero; translation splits an
  -- | application spine at the arity it is given, and at zero it would split a
  -- | saturated call into a `callk` of no arguments.
  = NotAnArity ModuleName Ident P.Int
  -- | Two interfaces of one module. Which arity each of that module's names has
  -- | would then depend on the order the two were read in.
  | ModuleTwice ModuleName

derive instance Eq InterfaceError
derive instance Generic InterfaceError _

instance Show InterfaceError where
  show = genericShow

-- | The interfaces given, as one environment, or what makes them no
-- | environment. An interface is read for its name, its imports, and its
-- | arities alone.
importsOf
  :: forall r
   . P.Array { name :: ModuleName, imports :: P.Array ModuleName, arities :: Map Ident P.Int | r }
  -> Either InterfaceError Imports
importsOf interfaces = map Imports (foldM one { arities: Map.empty, imports: Map.empty } interfaces)
  where
  one acc i
    | Map.member i.name acc.imports = Left (ModuleTwice i.name)
    | otherwise = do
        arities <- foldM (entry i.name) acc.arities (Map.toUnfoldable i.arities :: P.Array (Tuple Ident P.Int))
        pure { arities, imports: Map.insert i.name i.imports acc.imports }

  entry moduleName acc (Tuple name arity)
    | arity < 1 = Left (NotAnArity moduleName name arity)
    | otherwise = Right (Map.insert (Qualified moduleName name) arity acc)

-- | The arities the environment holds for the modules a translation depends on:
-- | those its module imports, and those each of them imports in turn, as far as
-- | the environment reaches.
-- |
-- | Each interface speaks for one module and a module has one interface, so what is
-- | looked up under a qualified name is the arity the declaring module published,
-- | whichever module a term reached the name through: a value another module
-- | re-exports is looked up under the module declaring it, which the module
-- | re-exporting it imports. **A module outside the dependencies sharpens
-- | nothing**, and nor does the module being translated, whose globals are read
-- | off their right-hand sides.
importedArities :: ModuleName -> P.Array ModuleName -> Imports -> Map (Qualified Ident) P.Int
importedArities self direct (Imports env) = Map.filterKeys (\(Qualified moduleName _) -> Set.member moduleName reached) env.arities
  where
  reached = Set.delete self (closure Set.empty direct)
  closure seen = case _ of
    [] -> seen
    pending -> case Array.uncons pending of
      Nothing -> seen
      Just { head, tail }
        | Set.member head seen -> closure seen tail
        | otherwise -> closure (Set.insert head seen) (tail <> fromMaybe [] (Map.lookup head env.imports))
