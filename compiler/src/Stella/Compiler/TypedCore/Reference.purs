-- | The global names a Core term refers to.
-- |
-- | This is the one reading of what a term depends on. Declaration checking
-- | reads it to refuse a `nonrec` that refers forwards, and elaboration reads it
-- | off the right-hand sides it committed to compute the order of a module's
-- | value declarations; the two agree because they are the same function.
module Stella.Compiler.TypedCore.Reference
  ( globalsOf
  ) where

import Prelude

import Stella.Compiler.TypedCore.Name (Ident, Qualified)
import Stella.Compiler.TypedCore.Term (DecisionTree(..), Expr(..), Handler, opClauseBody)
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
globalsOf = case _ of
  Var _ _ -> Set.empty
  Global _ name _ -> Set.singleton name
  Lit _ _ -> Set.empty
  Lam _ _ _ body -> globalsOf body
  App _ f x -> globalsOf f <> globalsOf x
  TyLam _ _ _ body -> globalsOf body
  TyApp _ e _ -> globalsOf e
  ConstraintLam _ _ body -> globalsOf body
  ConstraintApp _ e -> globalsOf e
  Let _ _ _ value body -> globalsOf value <> globalsOf body
  LetRec _ bindings body -> foldMap (globalsOf <<< _.value) bindings <> globalsOf body
  Case _ scrutinees tree -> foldMap globalsOf scrutinees <> treeGlobals tree
  LetJoin _ _ _ _ value body -> globalsOf value <> globalsOf body
  Jump _ _ args -> foldMap globalsOf args
  RecordEmpty _ -> Set.empty
  RecordExtend _ _ value rest -> globalsOf value <> globalsOf rest
  RecordSelect _ _ e -> globalsOf e
  RecordRestrict _ _ e -> globalsOf e
  RecordUpdate _ _ rec value -> globalsOf rec <> globalsOf value
  RecordMerge _ left right -> globalsOf left <> globalsOf right
  VariantInject _ _ e -> globalsOf e
  VariantWeaken _ _ _ e -> globalsOf e
  VariantAbsurd _ _ e -> globalsOf e
  Perform _ _ _ _ e -> globalsOf e
  Handle _ e handler initial -> globalsOf e <> handlerGlobals handler <> foldMap globalsOf initial
  ReadCell _ _ -> Set.empty
  WriteCell _ _ value -> globalsOf value
  OpenEff _ _ e -> globalsOf e

treeGlobals :: forall a. DecisionTree a -> Set (Qualified Ident)
treeGlobals = case _ of
  Leaf e -> globalsOf e
  Bind _ _ tree -> treeGlobals tree
  SwitchCtor _ branches fallback ->
    foldMap (treeGlobals <<< _.tree) branches <> foldMap treeGlobals fallback
  SwitchLit _ branches fallback ->
    foldMap (treeGlobals <<< _.tree) branches <> treeGlobals fallback
  SwitchKey _ branches fallback ->
    foldMap (treeGlobals <<< _.tree) branches <> foldMap treeGlobals fallback
  Guard condition consequent alternative ->
    globalsOf condition <> treeGlobals consequent <> treeGlobals alternative

handlerGlobals :: forall a. Handler a -> Set (Qualified Ident)
handlerGlobals handler =
  globalsOf handler.returnClause.body <> foldMap (globalsOf <<< opClauseBody) handler.opClauses
