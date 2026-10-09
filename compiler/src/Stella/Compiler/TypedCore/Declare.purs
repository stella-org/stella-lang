-- | Declaration well-formedness, and the `Σ` a module contributes.
-- |
-- | `Σ ⊢ decl ⊣ Σ'`. Type-level declarations are collected first, since `data`
-- | and `effect` declarations may be mutually recursive and a left fold cannot
-- | express that; interiors are checked under the collection. Value
-- | declarations are then folded leftwards, which their dependency order makes
-- | possible in one pass.
-- |
-- | A top-level right-hand side is checked at ambient effect row `()`: defining
-- | a value performs no effects, and effects occur when the value, being a
-- | function, is applied.
module Stella.Compiler.TypedCore.Declare
  ( DeclError(..)
  , DeclFailure
  , Declared
  , CheckedGroup
  , initialSignature
  , checkTyConEntries
  , checkEffectEntries
  , checkAttributeEntries
  , collectTypes
  , dataEntry
  , ctorInfo
  , declare
  , declareAnnotated
  , impureArrow
  , isEmptyRow
  ) where

import Prelude

import Prim as P

import Stella.Compiler.TypedCore.Check (CheckError, Typed, check, envOf, isFunVal)
import Stella.Compiler.TypedCore.Context (Context, bindKindVars, bindTyVar, emptyContext)
import Stella.Compiler.TypedCore.Decl (CtorDecl, DataDecl, Decl(..), EffectDecl, Export(..), Module, OpDecl, ValueBinding)
import Stella.Compiler.TypedCore.Kind (Kind(..))
import Stella.Compiler.TypedCore.Kinding (KindError, checkKind, producesType, quantifiableKind)
import Stella.Compiler.TypedCore.Name (EffName, Ident, KindVar, ModuleName, OpName, Qualified(..), TyName)
import Stella.Compiler.TypedCore.Prim (asFunction, primModule, primSignature, pureFn)
import Stella.Compiler.TypedCore.Reference (globalsOf)
import Stella.Compiler.TypedCore.Row (nf)
import Stella.Compiler.TypedCore.Signature (AttributeInfo, CtorInfo, EffectInfo, Signature, TyConInfo(..), ValueInfo, lookupAttribute, tyConKind)
import Stella.Compiler.TypedCore.AttributeCheck (AttributeError, checkAttribute, checkAttributeDecl)
import Stella.Compiler.TypedCore.Term (Expr)
import Stella.Compiler.TypedCore.Type (RowEntry(..), TyBinder, Type(..), TypeScheme)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldM, foldMap, foldl, foldr, traverse_)
import Data.Traversable (traverse)
import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Set as Set
import Data.Show.Generic (genericShow)
import Data.Tuple (Tuple(..))

-- | An error together with the declaration it is reported at. Types, kinds, and
-- | the interior structure of a declaration carry no span, so a diagnostic
-- | about one is located at the declaration.
type DeclFailure a =
  { at :: a
  , error :: DeclError
  }

data DeclError
  -- | `Prim` is reserved, so that nothing can supply a second `Prim.Int`.
  = ReservedModuleName ModuleName
  | DuplicateTyCon (Qualified TyName)
  | DuplicateEffect (Qualified EffName)
  -- | Data constructors and values share one namespace: a constructor is an
  -- | ordinary global name.
  | DuplicateName (Qualified Ident)
  | DuplicateOperation (Qualified EffName) OpName
  | DuplicateTag (Qualified TyName) P.Int
  -- | A `newtype` is one constructor with one field. A backend erases the
  -- | representation on the strength of the flag, so it is not trusted.
  | NewtypeShape (Qualified TyName)
  -- | An arrow of a `foreign` type carrying an effect (D23), with the row it
  -- | carries. A handler would be bypassed on the result side, and the calling
  -- | convention would leak on the argument side.
  | EffectfulForeign (Qualified Ident) Type
  -- | A `nonrec` right-hand side referring to itself or to a later value
  -- | declaration, naming what it refers to.
  | ForwardReference (Qualified Ident)
  | MissingExport Export
  -- | The right-hand side of a recursive declaration that is not a function
  -- | value (D14).
  | RecursiveNotFunctionValue (Qualified Ident)
  | IllTyped CheckError
  -- | A malformed type constructor entry, which no declaration produces.
  | TyConEntryError (Qualified TyName) KindError
  -- | The same for an effect entry, which no declaration produced either.
  | EffectEntryError (Qualified EffName) KindError
  -- | An effect entry keying an operation under a name other than the one its
  -- | declaration carries, as the key and the declared name. The table is keyed
  -- | by the declared name, so no declaration produces one.
  | OperationNameMismatch (Qualified EffName) OpName OpName
  -- | Two parts of an assembled signature carry different entries under one
  -- | name. A name belongs to the module that declares it, so an entry reaching
  -- | one name by several import paths is the same entry; differing ones mean
  -- | the parts were not built from one set of interfaces.
  | ConflictingTyCon (Qualified TyName)
  | ConflictingEffect (Qualified EffName)
  -- | The same for a constructor or a value, which share a namespace.
  | ConflictingValue (Qualified Ident)
  | IllKinded KindError
  | DuplicateAttribute (Qualified Ident)
  | ConflictingAttribute (Qualified Ident)
  -- | An attribute declaration, or an attribute attached to a declaration, that
  -- | does not check.
  | AttributeIllTyped AttributeError
  -- | An attribute entry, which no declaration of this module produced, that
  -- | does not check.
  | AttributeEntryError (Qualified Ident) AttributeError

-- | `Σ_Prim ∪ Σ_ABI(M) ∪ Σ_imp`, the signature a module is checked under.
-- |
-- | `Prim` is never imported, so it goes in before anything else. Every entry
-- | that no declaration produced arrives through here, which is why the table
-- | is checked at this point rather than trusted.
-- |
-- | Two import paths reaching one entry contribute the same entry, a name
-- | belonging to the module that declares it, so the union needs no tie-break.
initialSignature :: P.Array Signature -> Either DeclError Signature
initialSignature parts = do
  sig <- foldM merge primSignature parts
  checkTyConEntries sig
  checkEffectEntries sig
  checkAttributeEntries sig
  pure sig

-- | Two parts of a signature, agreeing wherever they meet.
-- |
-- | An entry arriving through two import paths is the same entry, so a
-- | duplicate is absorbed; differing entries under one name are not resolved by
-- | preferring either. Constructors and values are compared across both tables,
-- | a constructor being an ordinary global name.
merge :: Signature -> Signature -> Either DeclError Signature
merge acc part = do
  types <- mergeTable ConflictingTyCon acc.types part.types
  effects <- mergeTable ConflictingEffect acc.effects part.effects
  ctors <- mergeTable ConflictingValue acc.ctors part.ctors
  values <- mergeTable ConflictingValue acc.values part.values
  attributes <- mergeTable ConflictingAttribute acc.attributes part.attributes
  traverse_ (Left <<< ConflictingValue) (sharedKeys ctors values)
  pure { types, ctors, effects, values, attributes }

mergeTable
  :: forall k v e
   . Ord k
  => Eq v
  => (k -> e)
  -> Map k v
  -> Map k v
  -> Either e (Map k v)
mergeTable onConflict left right = foldM add left (Map.toUnfoldable right :: P.Array (Tuple k v))
  where
  add acc (Tuple key value) = case Map.lookup key acc of
    Just existing | existing /= value -> Left (onConflict key)
    _ -> Right (Map.insert key value acc)

sharedKeys :: forall k v w. Ord k => Map k v -> Map k w -> P.Array k
sharedKeys left right =
  Set.toUnfoldable (Set.intersection (Set.fromFoldable (Map.keys left)) (Set.fromFoldable (Map.keys right)))

-- | Every type constructor entry is a well-formed kind scheme producing `Type`.
-- |
-- | An entry derived from a declaration is so by construction. One arriving
-- | with `Prim` or through the manifest of the primitive surface is checked
-- | here: a scheme such as `forall k. k` passes every use site that
-- | instantiates it at `Type` while producing a row at another, and neither an
-- | unbound kind variable nor a domain that cannot be quantified is visible
-- | from one occurrence either.
checkTyConEntries :: Signature -> Either DeclError Unit
checkTyConEntries sig =
  traverse_ entryOk (Map.toUnfoldable sig.types :: P.Array (Tuple (Qualified TyName) TyConInfo))
  where
  entryOk (Tuple name info) = named name do
    let scheme = tyConKind info
    quantifiableKind (bindKindVars emptyContext scheme.kindVars) scheme.body
    producesType scheme.body

  named name = case _ of
    Left err -> Left (TyConEntryError name err)
    Right value -> Right value

-- | Every effect entry is what an `effect` declaration would have produced.
-- |
-- | The counterpart of `checkTyConEntries`, and it exists for the same reason:
-- | an entry derived from a declaration is well formed by construction, while
-- | one arriving through an assembled interface is checked here. What is
-- | re-checked is what the declaration rules ask of it — the parameters and an
-- | operation's own binders at a quantifiable kind (D24), the argument and the
-- | resumption type at `Type`, and every type variable in scope.
-- |
-- | An effect constructor binds no kind variable, so the context starts from
-- | the parameters alone (D3).
checkEffectEntries :: Signature -> Either DeclError Unit
checkEffectEntries sig =
  traverse_ entryOk (Map.toUnfoldable sig.effects :: P.Array (Tuple (Qualified EffName) EffectInfo))
  where
  entryOk (Tuple name info) = do
    named name (traverse_ (\binder -> quantifiableKind emptyContext binder.kind) info.params)
    traverse_ (operationOk name info)
      (Map.toUnfoldable info.operations :: P.Array (Tuple OpName OpDecl))

  -- The table is keyed by the name each operation declares, which is what a
  -- declaration produces and what `Σ(E).op` is looked up by. An entry keying
  -- one name to a declaration carrying another would answer a lookup with a
  -- signature belonging to something else.
  operationOk name info (Tuple key op) = do
    when (key /= op.name) (Left (OperationNameMismatch name key op.name))
    named name do
      let ctx = paramContext [] info.params
      traverse_ (\binder -> quantifiableKind ctx binder.kind) op.tyBinders
      let inner = foldl (\acc binder -> bindTyVar acc binder.name binder.kind) ctx op.tyBinders
      checkKind sig inner op.argument KType
      checkKind sig inner op.resumesWith KType

  named name = case _ of
    Left err -> Left (EffectEntryError name err)
    Right value -> Right value

-- | Every attribute entry is what an `attribute` declaration would have
-- | produced: its parameter types closed and of kind `Type`, and each default of
-- | its parameter's type. An entry arriving through an assembled interface is
-- | checked here, as a type constructor or an effect entry is.
checkAttributeEntries :: Signature -> Either DeclError Unit
checkAttributeEntries sig =
  traverse_ entryOk (Map.toUnfoldable sig.attributes :: P.Array (Tuple (Qualified Ident) AttributeInfo))
  where
  entryOk (Tuple name info) = case checkAttributeDecl sig info of
    Left err -> Left (AttributeEntryError name err)
    Right _ -> Right unit

-- | `Σ_ty`, the kinds of the type constructors and effect constructors a module
-- | declares, added to what `Prim`, the primitive surface, and the imports
-- | supply.
collectTypes :: forall a. Signature -> Module a -> Either (DeclFailure a) Signature
collectTypes sig m = foldM addType sig m.decls
  where
  addType acc = case _ of
    DeclData at decl -> do
      let name = Qualified m.name decl.name
      let ctx = bindKindVars emptyContext decl.kindVars
      traverse_ (\binder -> kinded at (quantifiableKind ctx binder.kind)) decl.params
      types <- insertUnique (\_ -> { at, error: DuplicateTyCon name }) name (dataEntry m.name decl) acc.types
      pure acc { types = types }

    DeclEffect at decl -> do
      let name = Qualified m.name decl.name
      traverse_ (\binder -> kinded at (quantifiableKind emptyContext binder.kind)) decl.params
      operations <- foldM (addOperation at name) Map.empty decl.operations
      effects <- insertUnique (\_ -> { at, error: DuplicateEffect name }) name
        { params: decl.params, operations }
        acc.effects
      pure acc { effects = effects }

    _ -> pure acc

  addOperation at name ops op =
    insertUnique (\_ -> { at, error: DuplicateOperation name op.name }) op.name op ops

-- | `T : forall k̄. κ̄ -> Type`, with the constructors the declaration gives it.
dataEntry :: ModuleName -> DataDecl -> TyConInfo
dataEntry moduleName decl =
  DataTyCon
    { kindVars: decl.kindVars
    , body: foldr KFun KType (map _.kind decl.params)
    }
    (map (\ctor -> Qualified moduleName ctor.name) decl.constructors)

-- | `Σ ⊢ module M ⊣ Σ'`, less the right-hand sides.
-- | A value binding group as checking leaves it: the right-hand sides carry the
-- | types checking gave them, and the groups are in the declaration order the
-- | module wrote.
type CheckedGroup a =
  { recursive :: P.Boolean
  , bindings :: P.Array (ValueBinding (Typed a))
  }

-- | What a module contributes to `Σ`, together with its checked value
-- | declarations.
-- |
-- | Data, effect, and foreign declarations are not among the groups: what they
-- | contribute is in the signature, and a declaration annotation is a source
-- | annotation rather than anything checking produces.
type Declared a =
  { signature :: Signature
  , values :: P.Array (CheckedGroup a)
  }

declare :: forall a. Signature -> Module a -> Either (DeclFailure a) Signature
declare imported m = _.signature <$> declareAnnotated imported m

declareAnnotated :: forall a. Signature -> Module a -> Either (DeclFailure a) (Declared a)
declareAnnotated imported m = do
  when (m.name == primModule)
    (Left { at: m.annotation, error: ReservedModuleName m.name })
  sigTy <- collectTypes imported m
  checkOrder m
  sigDecl <- foldM (addDecl m sigTy) sigTy m.decls
  declared <- foldM (addValue' m sigTy) { signature: sigDecl, values: [] } m.decls
  checkExports m declared.signature
  traverse_ (checkAttributes m declared.signature) m.decls
  pure declared

-- | `Σ_decl`: what a data, effect, or foreign declaration contributes, checked
-- | under `Σ_ty`.
-- |
-- | Constructors and foreigns are collected before any value declaration is
-- | checked, so a value may refer to one the text declares later.
addDecl :: forall a. Module a -> Signature -> Signature -> Decl a -> Either (DeclFailure a) Signature
addDecl m sigTy acc = case _ of
  DeclData at decl -> do
    let owner = Qualified m.name decl.name
    when (decl.isNewtype && not (isNewtypeShaped decl))
      (Left { at, error: NewtypeShape owner })
    let ctx = paramContext decl.kindVars decl.params
    { signature } <- foldM (addCtor at m.name sigTy ctx owner decl) { signature: acc, tags: Set.empty } decl.constructors
    pure signature

  DeclEffect at decl -> do
    traverse_ (checkOperation at sigTy decl) decl.operations
    pure acc

  DeclForeign at decl -> do
    checkScheme at sigTy decl.scheme
    checkPurity at (Qualified m.name decl.name) decl.scheme
    addValue at m.name decl.name { scheme: decl.scheme, isForeign: true } acc

  DeclNonRec _ _ -> pure acc

  DeclRec _ _ -> pure acc

  DeclAttribute at decl -> do
    attributes <- insertUnique (\name -> { at, error: DuplicateAttribute name }) (Qualified m.name decl.name)
      { positional: decl.positional, keyword: decl.keyword }
      acc.attributes
    pure acc { attributes = attributes }

-- | The attributes a declaration carries, and an attribute declaration's
-- | parameters, checked under the signature the whole module contributes: an
-- | argument may name a value or a constructor declared anywhere in it.
checkAttributes :: forall a. Module a -> Signature -> Decl a -> Either (DeclFailure a) Unit
checkAttributes m sig = case _ of
  DeclData at decl -> attached at decl.attributes
  DeclEffect at decl -> attached at decl.attributes
  DeclForeign at decl -> attached at decl.attributes
  DeclNonRec at binding -> attached at binding.attributes
  DeclRec at bindings -> traverse_ (attached at <<< _.attributes) bindings
  DeclAttribute at decl -> case lookupAttribute sig (Qualified m.name decl.name) of
    Just info -> failing at (checkAttributeDecl sig info)
    Nothing -> pure unit
  where
  attached at = traverse_ (failing at <<< checkAttribute sig)
  failing at = case _ of
    Left err -> Left { at, error: AttributeIllTyped err }
    Right _ -> Right unit

-- | The value declarations, folded leftwards from `Σ_decl`.
-- |
-- | A right-hand side is checked under the signature as it stands. Their
-- | dependency order is what makes that complete for each in turn, and what lets
-- | the fold close in one pass.
addValue'
  :: forall a
   . Module a
  -> Signature
  -> Declared a
  -> Decl a
  -> Either (DeclFailure a) (Declared a)
addValue' m sigTy acc = case _ of
  DeclNonRec at binding -> do
    checkScheme at sigTy binding.scheme
    value <- checkBody acc.signature binding
    signature <- addValue at m.name binding.name { scheme: binding.scheme, isForeign: false } acc.signature
    pure
      { signature
      , values: acc.values <> [ { recursive: false, bindings: [ binding { value = value } ] } ]
      }

  -- Every scheme of the group is registered before any right-hand side is
  -- checked, which is what lets its members carry different kind schemes.
  DeclRec at bindings -> do
    registered <- foldM (flip (addBinding at m.name sigTy)) acc.signature bindings
    traverse_ (guarded at m.name) bindings
    checked <- traverse (checkedBinding registered) bindings
    pure { signature: registered, values: acc.values <> [ { recursive: true, bindings: checked } ] }

  _ -> pure acc
  where
  checkedBinding registered binding = do
    value <- checkBody registered binding
    pure (binding { value = value })

addBinding
  :: forall a
   . a
  -> ModuleName
  -> Signature
  -> ValueBinding a
  -> Signature
  -> Either (DeclFailure a) Signature
addBinding at moduleName sigTy binding acc = do
  checkScheme at sigTy binding.scheme
  addValue at moduleName binding.name { scheme: binding.scheme, isForeign: false } acc

-- | `Σ ; ·, k̄ ; · ⊢ e : σ ! ()`.
checkBody :: forall a. Signature -> ValueBinding a -> Either (DeclFailure a) (Expr (Typed a))
checkBody sig binding =
  case check (envOf sig ctx) TRowEmpty binding.scheme.body binding.value of
    Left failure -> Left { at: failure.at, error: IllTyped failure.error }
    Right value -> Right value
  where
  ctx = bindKindVars emptyContext binding.scheme.kindVars

guarded :: forall a. a -> ModuleName -> ValueBinding a -> Either (DeclFailure a) Unit
guarded at moduleName binding =
  when (not (isFunVal binding.value))
    (Left { at, error: RecursiveNotFunctionValue (Qualified moduleName binding.name) })

-- | `Ctor : forall k̄. forall (ā : κ̄). τ1 -> … -> τn -> T [[k̄]] ā`, with pure
-- | arrows throughout.
addCtor
  :: forall a
   . a
  -> ModuleName
  -> Signature
  -> Context
  -> Qualified TyName
  -> DataDecl
  -> { signature :: Signature, tags :: Set P.Int }
  -> CtorDecl
  -> Either (DeclFailure a) { signature :: Signature, tags :: Set P.Int }
addCtor at moduleName sigTy ctx owner decl state ctor = do
  traverse_ (\field -> kinded at (checkKind sigTy ctx field KType)) ctor.fields
  when (Set.member ctor.tag state.tags) (Left { at, error: DuplicateTag owner ctor.tag })
  signature <- addCtorInfo at moduleName ctor.name (ctorInfo owner decl ctor) state.signature
  pure { signature, tags: Set.insert ctor.tag state.tags }

ctorInfo :: Qualified TyName -> DataDecl -> CtorDecl -> CtorInfo
ctorInfo owner decl ctor =
  { owner
  , tag: ctor.tag
  , params: decl.params
  , fields: ctor.fields
  , scheme:
      { kindVars: decl.kindVars
      , body: foldr quantify (foldr pureFn result ctor.fields) decl.params
      }
  }
  where
  quantify binder body = TForall binder.name binder.kind body
  result = foldl TApp (TCon owner (map KVar decl.kindVars)) (map (TVar <<< _.name) decl.params)

-- | `op : forall (b̄ : κ̄'). σ ->* τ`. An operation signature is not a function
-- | type: the argument and what the continuation resumes with are checked
-- | separately, there being no functional relationship between them.
checkOperation :: forall a. a -> Signature -> EffectDecl -> OpDecl -> Either (DeclFailure a) Unit
checkOperation at sigTy decl op = do
  traverse_ (\binder -> kinded at (quantifiableKind ctx binder.kind)) op.tyBinders
  kinded at (checkKind sigTy inner op.argument KType)
  kinded at (checkKind sigTy inner op.resumesWith KType)
  where
  ctx = paramContext [] decl.params
  inner = foldl (\acc binder -> bindTyVar acc binder.name binder.kind) ctx op.tyBinders

-- | `σκ = forall k̄. σ` with `·, k̄ ⊢ σ : Type`.
checkScheme :: forall a. a -> Signature -> TypeScheme -> Either (DeclFailure a) Unit
checkScheme at sigTy scheme =
  kinded at (checkKind sigTy (bindKindVars emptyContext scheme.kindVars) scheme.body KType)

-- | Every arrow in a runtime-bearing position of a `foreign` type is pure
-- | (D23). The rule is syntactic, and it holds of arrows nested anywhere a
-- | value passes through, the payload of a row element included.
-- |
-- | A constraint is an erased proposition and carries no value across the
-- | boundary, so the arrows inside one are not traversed: neither handler
-- | bypass nor a leaking calling convention can arise there.
checkPurity :: forall a. a -> Qualified Ident -> TypeScheme -> Either (DeclFailure a) Unit
checkPurity at name scheme = case impureArrow scheme.body of
  Just row -> Left { at, error: EffectfulForeign name row }
  Nothing -> Right unit

-- | The row of an arrow performing effects that the type holds where a value
-- | passes through, a constraint's own types aside.
impureArrow :: Type -> Maybe Type
impureArrow ty = case asFunction ty of
  Just parts | not (isEmptyRow parts.row) -> Just parts.row
  _ -> case ty of
    TApp f x -> orElse (impureArrow f) (impureArrow x)
    TForall _ _ body -> impureArrow body
    TConstrained _ body -> impureArrow body
    TRowExtend entry rest -> orElse (entryImpureArrow entry) (impureArrow rest)
    TRowUnion left right -> orElse (impureArrow left) (impureArrow right)
    _ -> Nothing

-- | An arrow reaches the boundary through the payload of a row element as
-- | readily as through an argument: `Record ( cb : a -{ρ}-> b )` hands a
-- | callback across it.
entryImpureArrow :: RowEntry -> Maybe Type
entryImpureArrow = case _ of
  RowTypeEntry _ ty -> impureArrow ty
  RowEffectEntry _ args -> Array.findMap impureArrow args
  RowLabelledEffectEntry _ _ args -> Array.findMap impureArrow args
  -- A region carries only its name, through which nothing crosses.
  RowRegionEntry _ -> Nothing

-- | Whether a row's normal form holds no element and no tail.
isEmptyRow :: Type -> P.Boolean
isEmptyRow row = case nf row of
  Right normal -> Map.isEmpty normal.known && Set.isEmpty normal.tail
  Left _ -> false

-- | Value declarations are in dependency order: a `nonrec` refers neither to
-- | itself nor to a later value declaration, and every cycle is contained in a
-- | `rec` group. Constructors and foreign implementations enter the environment
-- | before any value declaration is evaluated, so a reference to one is not a
-- | forward reference.
checkOrder :: forall a. Module a -> Either (DeclFailure a) Unit
checkOrder m = go (valueGroups m)
  where
  go groups = case Array.uncons groups of
    Nothing -> Right unit
    Just { head, tail } -> do
      let
        later = foldMap _.declares tail
        forbidden = if head.isRec then later else Set.union later head.declares
        offending =
          Set.toUnfoldable (Set.intersection head.refers forbidden) :: P.Array (Qualified Ident)
      traverse_ (\name -> Left { at: head.at, error: ForwardReference name }) offending
      go tail

-- | A `nonrec` or a `rec` group, as the order check reads it.
valueGroups
  :: forall a
   . Module a
  -> P.Array { at :: a, isRec :: P.Boolean, declares :: Set (Qualified Ident), refers :: Set (Qualified Ident) }
valueGroups m = Array.mapMaybe group m.decls
  where
  group = case _ of
    DeclNonRec at binding -> Just
      { at
      , isRec: false
      , declares: Set.singleton (Qualified m.name binding.name)
      , refers: globalsOf binding.value
      }
    DeclRec at bindings -> Just
      { at
      , isRec: true
      , declares: Set.fromFoldable (map (\b -> Qualified m.name b.name) bindings)
      , refers: foldMap (globalsOf <<< _.value) bindings
      }
    _ -> Nothing

checkExports :: forall a. Module a -> Signature -> Either (DeclFailure a) Unit
checkExports m sig = traverse_ present m.exports
  where
  present export = case export of
    ExportValue name
      | Map.member (Qualified m.name name) sig.values -> Right unit
      | otherwise -> missing export
    ExportType name
      | Map.member (Qualified m.name name) sig.types -> Right unit
      | otherwise -> missing export
    ExportCtor name
      | Map.member (Qualified m.name name) sig.ctors -> Right unit
      | otherwise -> missing export
    ExportEffect name
      | Map.member (Qualified m.name name) sig.effects -> Right unit
      | otherwise -> missing export

  missing export = Left { at: m.annotation, error: MissingExport export }

addValue :: forall a. a -> ModuleName -> Ident -> ValueInfo -> Signature -> Either (DeclFailure a) Signature
addValue at moduleName name info sig = do
  let qualified = Qualified moduleName name
  when (Map.member qualified sig.ctors) (Left { at, error: DuplicateName qualified })
  values <- insertUnique (\_ -> { at, error: DuplicateName qualified }) qualified info sig.values
  pure sig { values = values }

addCtorInfo :: forall a. a -> ModuleName -> Ident -> CtorInfo -> Signature -> Either (DeclFailure a) Signature
addCtorInfo at moduleName name info sig = do
  let qualified = Qualified moduleName name
  when (Map.member qualified sig.values) (Left { at, error: DuplicateName qualified })
  ctors <- insertUnique (\_ -> { at, error: DuplicateName qualified }) qualified info sig.ctors
  pure sig { ctors = ctors }

isNewtypeShaped :: DataDecl -> P.Boolean
isNewtypeShaped decl = case decl.constructors of
  [ ctor ] -> Array.length ctor.fields == 1
  _ -> false

paramContext :: P.Array KindVar -> P.Array TyBinder -> Context
paramContext kindVars params =
  foldl (\ctx binder -> bindTyVar ctx binder.name binder.kind) (bindKindVars emptyContext kindVars) params

insertUnique :: forall k v e. Ord k => (k -> e) -> k -> v -> Map k v -> Either e (Map k v)
insertUnique onDuplicate key value table
  | Map.member key table = Left (onDuplicate key)
  | otherwise = Right (Map.insert key value table)

kinded :: forall a b. a -> Either KindError b -> Either (DeclFailure a) b
kinded at = case _ of
  Left error -> Left { at, error: IllKinded error }
  Right value -> Right value

orElse :: forall x. Maybe x -> Maybe x -> Maybe x
orElse first second = case first of
  Just _ -> first
  Nothing -> second

derive instance Eq DeclError
derive instance Generic DeclError _

instance Show DeclError where
  show x = genericShow x
