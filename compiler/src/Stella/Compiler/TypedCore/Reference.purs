-- | The global names a Core term refers to, and the modules a module's terms
-- | depend on when it runs.
-- |
-- | `globalsOf` is the one reading of what a term depends on as it is
-- | initialized. Declaration checking reads it to refuse a `nonrec` that
-- | refers forwards, and elaboration reads it off the right-hand sides it
-- | committed to compute the order of a module's value declarations; the two
-- | agree because they are the same function. `runtimeDependencies` reads the
-- | same walk, with the constructors a dispatch names beside it.
module Stella.Compiler.TypedCore.Reference
  ( globalsOf
  , runtimeDependencies
  ) where

import Prelude

import Prim as P

import Stella.Compiler.TypedCore.Domain (compareByScalar)
import Stella.Compiler.TypedCore.Name (Ident, ModuleName(..), Qualified(..))
import Stella.Compiler.TypedCore.Prim (primModule)
import Stella.Compiler.TypedCore.Term (DecisionTree(..), Expr(..), Handler, opClauseBody)
import Data.Array as Array
import Data.Foldable (foldMap)
import Data.Set (Set)
import Data.Set as Set

-- | Every name a `Global` of the term names.
-- |
-- | **`Global` is the only form that refers to a value.** Local names, join
-- | points, and operations are not global names; the constructor a `switchCtor`
-- | dispatches on, the effect a handler names, and a type constructor inside a
-- | type refer to no value declaration. A data constructor applied in the term is
-- | reached through `Global` and is among what this returns.
globalsOf :: forall a. Expr a -> Set (Qualified Ident)
globalsOf = namesOf false

-- | The modules the terms given depend on when they run, of the module named:
-- | each module, other than that one and `Prim`, declaring what a `Global` of
-- | them names or a constructor a `switchCtor` of them dispatches on, in the
-- | order of the names' scalar values (D51).
-- |
-- | An operation, an effect a handler names, a key, and a type name no module a
-- | program must hold to run: what they are compared by is an identity loading
-- | assigns them.
runtimeDependencies :: forall a. ModuleName -> P.Array (Expr a) -> P.Array ModuleName
runtimeDependencies self terms =
  Array.sortBy (\(ModuleName a) (ModuleName b) -> compareByScalar a b)
    (Array.filter (\m -> m /= self && m /= primModule) (Array.fromFoldable modules))
  where
  modules = Set.map (\(Qualified m _) -> m) (foldMap (namesOf true) terms)

-- | The names the term refers to: every `Global`'s, and, where the flag says so,
-- | every constructor a `switchCtor` dispatches on.
namesOf :: forall a. P.Boolean -> Expr a -> Set (Qualified Ident)
namesOf dispatched = go
  where
  go = case _ of
    Var _ _ -> Set.empty
    Global _ name _ -> Set.singleton name
    Lit _ _ -> Set.empty
    Lam _ _ _ _ body -> go body
    App _ f x -> go f <> go x
    TyLam _ _ _ body -> go body
    TyApp _ e _ -> go e
    ConstraintLam _ _ body -> go body
    ConstraintApp _ e -> go e
    Let _ _ _ value body -> go value <> go body
    LetRec _ bindings body -> foldMap (go <<< _.value) bindings <> go body
    Case _ scrutinees tree -> foldMap go scrutinees <> treeNames tree
    LetJoin _ _ _ _ value body -> go value <> go body
    Jump _ _ args -> foldMap go args
    RecordEmpty _ -> Set.empty
    RecordExtend _ _ value rest -> go value <> go rest
    RecordSelect _ _ e -> go e
    RecordRestrict _ _ e -> go e
    RecordUpdate _ _ rec value -> go rec <> go value
    RecordMerge _ left right -> go left <> go right
    VariantInject _ _ _ e -> go e
    VariantWeaken _ _ _ e -> go e
    VariantAbsurd _ _ e -> go e
    Perform _ _ _ _ e -> go e
    Handle _ e handler -> go e <> handlerNames handler
    Region _ _ _ initial body -> foldMap go initial <> go body
    ReadCell _ _ _ -> Set.empty
    WriteCell _ _ _ value -> go value
    OpenEff _ _ e -> go e

  treeNames = case _ of
    Leaf e -> go e
    Bind _ _ tree -> treeNames tree
    SwitchCtor _ branches fallback ->
      (if dispatched then Set.fromFoldable (map _.ctor branches) else Set.empty)
        <> foldMap (treeNames <<< _.tree) branches
        <> foldMap treeNames fallback
    SwitchLit _ branches fallback ->
      foldMap (treeNames <<< _.tree) branches <> treeNames fallback
    SwitchKey _ branches fallback ->
      foldMap (treeNames <<< _.tree) branches <> foldMap treeNames fallback
    Guard condition consequent alternative ->
      go condition <> treeNames consequent <> treeNames alternative

  handlerNames :: Handler a -> Set (Qualified Ident)
  handlerNames handler =
    go handler.returnClause.body <> foldMap (go <<< opClauseBody) handler.opClauses
