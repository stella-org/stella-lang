-- | Checking attributes: an attribute declaration's parameters, and an
-- | attached attribute's arguments against them
-- | ([Attributes, Modifiers, and Directives](../../../../docs/technical-references/02-Surface-Language/07-Attributes-Modifiers-and-Directives.md)).
-- |
-- | **Checking an attribute is checking its arguments.** What an attribute
-- | means is its reader's, and nothing about the declaration it is attached to
-- | depends on it. What is checked is that it is declared, that its arguments
-- | are normalized — as many positional arguments as parameters, and every
-- | keyword argument in the order declared — and that each argument has the type
-- | its parameter declares.
-- |
-- | **A parameter's type is closed**, well kinded at `Type` with nothing in
-- | scope, so a constant is checked against a known type, and the check is a
-- | decision rather than an inference:
-- |
-- | - a literal has the `Prim` type of its kind;
-- | - a value, which no constructor is, has the type its scheme instantiates to, only the scheme's outer
-- |   quantifiers being instantiated, and only as the expected type determines
-- |   them; no constraint is discharged, no synthesizer runs, and nothing is
-- |   inserted;
-- | - a constructor applied to constants builds the type expected, whose head is
-- |   the constructor's type, and each argument is checked against its field at
-- |   the parameters the expected type gives;
-- | - a record has a closed record type, its labels exactly the row's.
module Stella.Compiler.TypedCore.AttributeCheck
  ( AttributeError(..)
  , checkAttributeDecl
  , checkAttribute
  , checkConstant
  ) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Either (Either(..), note)
import Data.Foldable (foldM, traverse_)
import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Set as Set
import Data.Show.Generic (genericShow)
import Data.Tuple (Tuple(..))
import Stella.Compiler.TypedCore.Context (emptyContext)
import Stella.Compiler.TypedCore.Decl (Attribute, Constant(..))
import Stella.Compiler.TypedCore.Equality (typeEquiv)
import Stella.Compiler.TypedCore.Kind (Kind(..))
import Stella.Compiler.TypedCore.Kinding (KindError, checkKind)
import Stella.Compiler.TypedCore.Name (Ident, KindVar, Qualified, TyName, TyVar)
import Stella.Compiler.TypedCore.Prim (booleanTy, charTy, intTy, numberTy, recordTy, stringTy)
import Stella.Compiler.TypedCore.Row (RowError, fromNormalForm, nf)
import Stella.Compiler.TypedCore.Signature (AttributeInfo, Signature, TyConInfo(..), lookupAttribute, lookupCtor, lookupTyCon, lookupValue)
import Stella.Compiler.TypedCore.Term (Literal(..))
import Stella.Compiler.TypedCore.Type (RowKey(..), RowPayload(..), Type(..), TypeScheme, substituteKindsInType, substituteType)

data AttributeError
  -- | A parameter type that is not closed, or not of kind `Type`.
  = ParameterIllKinded Type KindError
  | UndeclaredAttribute (Qualified Ident)
  -- | An attribute with another number of positional arguments than its
  -- | declaration has parameters: the attribute, the parameters, the arguments.
  | PositionalCount (Qualified Ident) P.Int P.Int
  -- | Keyword arguments that are not every keyword parameter in the order
  -- | declared: the attribute, the labels declared, and those given.
  | KeywordsNotNormalized (Qualified Ident) (P.Array P.String) (P.Array P.String)
  -- | A constant that does not have the type expected of it.
  | ConstantNotOfType Constant Type
  -- | A constant naming a global `Σ` does not hold.
  | UndeclaredGlobal (Qualified Ident)
  -- | A row the expected type holds that does not normalize.
  | MalformedRow RowError

derive instance Eq AttributeError
derive instance Generic AttributeError _

instance Show AttributeError where
  show = genericShow

-- | An attribute declaration: every parameter type closed and of kind `Type`,
-- | and every default of its parameter's type.
checkAttributeDecl :: Signature -> AttributeInfo -> Either AttributeError Unit
checkAttributeDecl sig info = do
  traverse_ closed (info.positional <> map _.type info.keyword)
  traverse_ (\k -> traverse_ (checkConstant sig k.type) k.default) info.keyword
  where
  closed t = lmap (ParameterIllKinded t) (checkKind sig emptyContext t KType)

-- | An attached attribute, against its declaration in `Σ`.
checkAttribute :: Signature -> Attribute -> Either AttributeError Unit
checkAttribute sig attribute = do
  info <- note (UndeclaredAttribute attribute.name) (lookupAttribute sig attribute.name)
  let
    declared = map _.label info.keyword
    given = map _.label attribute.keyword
  when (Array.length attribute.positional /= Array.length info.positional)
    (Left (PositionalCount attribute.name (Array.length info.positional) (Array.length attribute.positional)))
  when (given /= declared) (Left (KeywordsNotNormalized attribute.name declared given))
  traverse_ (\(Tuple t c) -> checkConstant sig t c) (Array.zip info.positional attribute.positional)
  traverse_ (\(Tuple k a) -> checkConstant sig k.type a.value) (Array.zip info.keyword attribute.keyword)

-- | A constant, against the closed type expected of it.
checkConstant :: Signature -> Type -> Constant -> Either AttributeError Unit
checkConstant sig expected c = case c of
  ConstantLiteral l -> same (TCon (literalType l) [])
  ConstantValue q -> do
    scheme <- note (UndeclaredGlobal q) (schemeOf q)
    case instantiate scheme expected of
      Just t -> same t
      Nothing -> mismatch
  ConstantConstructor q arguments -> do
    info <- note (UndeclaredGlobal q) (lookupCtor sig q)
    case spine expected [] of
      Just s
        | s.name == info.owner && Array.length s.arguments == Array.length info.params
            && Array.length arguments == Array.length info.fields -> do
            let
              kindVars = case lookupTyCon sig info.owner of
                Just (DataTyCon scheme _) -> scheme.kindVars
                _ -> []
              kinds = Map.fromFoldable (Array.zip kindVars s.kinds)
              types = Map.fromFoldable (Array.zip (map _.name info.params) s.arguments)
              field = substituteType types <<< substituteKindsInType kinds
            traverse_ (\(Tuple f a) -> checkConstant sig (field f) a) (Array.zip info.fields arguments)
      _ -> mismatch
  ConstantRecord fields -> case spine expected [] of
    Just { name, arguments: [ row ] } | name == recordTy -> do
      normal <- lmap MalformedRow (nf row)
      let
        labels = map (\f -> SymbolKey f.label) fields
        keys = Array.fromFoldable (Map.keys normal.known)
      if
        not (Set.isEmpty normal.tail) || Array.length (Array.nub labels) /= Array.length labels
          || Set.fromFoldable labels /= Set.fromFoldable keys then mismatch
      else traverse_
        ( \f -> case Map.lookup (SymbolKey f.label) normal.known of
            Just (TypePayload t) -> checkConstant sig t f.value
            _ -> mismatch
        )
        fields
    _ -> mismatch
  where
  mismatch :: forall b. Either AttributeError b
  mismatch = Left (ConstantNotOfType c expected)

  same t = do
    equal <- lmap MalformedRow (typeEquiv t expected)
    if equal then pure unit else mismatch

  -- A constructor is a `ConstantConstructor`, applied to as many constants as
  -- it has fields, and never a value.
  schemeOf q = map _.scheme (lookupValue sig q)

-- | An error of another kind, as this module reports it.
lmap :: forall e f b. (e -> f) -> Either e b -> Either f b
lmap f = case _ of
  Left e -> Left (f e)
  Right b -> Right b

literalType :: Literal -> Qualified TyName
literalType = case _ of
  LitInt _ -> intTy
  LitNumber _ -> numberTy
  LitString _ -> stringTy
  LitChar _ -> charTy
  LitBoolean _ -> booleanTy

-- | `T [[κ̄]] τ̄`: a type constructor applied to its arguments.
spine :: Type -> P.Array Type -> Maybe { name :: Qualified TyName, kinds :: P.Array Kind, arguments :: P.Array Type }
spine t arguments = case t of
  TApp f a -> spine f (Array.cons a arguments)
  TCon name kinds -> Just { name, kinds, arguments }
  _ -> Nothing

-- | The type a scheme instantiates to where the expected type determines it:
-- | the outer quantifiers, kind and type, are matched one way against the
-- | expected type. A variable the match does not determine stays as it is,
-- | and the type it leaves is then not the one expected.
instantiate :: TypeScheme -> Type -> Maybe Type
instantiate scheme expected = do
  let
    peeled = peel [] scheme.body
    vars = Set.fromFoldable peeled.vars
    kindVars = Set.fromFoldable scheme.kindVars
  s <- match vars kindVars { types: Map.empty, kinds: Map.empty } peeled.body expected
  pure (substituteType s.types (substituteKindsInType s.kinds peeled.body))
  where
  peel vars = case _ of
    TForall a _ body -> peel (Array.snoc vars a) body
    body -> { vars, body }

type Substitution =
  { types :: Map TyVar Type
  , kinds :: Map KindVar Kind
  }

-- | One-way matching of a pattern holding the variables given against a type.
-- | Where the two differ in a form matching does not look into, the pattern is
-- | left as it is, for equality to judge.
match :: Set TyVar -> Set KindVar -> Substitution -> Type -> Type -> Maybe Substitution
match vars kindVars = go
  where
  go s p t = case p, t of
    TVar a, _ | Set.member a vars -> case Map.lookup a s.types of
      Nothing -> Just s { types = Map.insert a t s.types }
      Just bound -> case typeEquiv bound t of
        Right true -> Just s
        _ -> Nothing
    TCon n ks, TCon n' ks' | n == n' && Array.length ks == Array.length ks' ->
      foldM (\acc (Tuple k k') -> goKind acc k k') s (Array.zip ks ks')
    TApp f a, TApp f' a' -> go s f f' >>= \s' -> go s' a a'
    _, _
      | isRow p && isRow t -> row s p t
      | otherwise -> Just s

  goKind s k k' = case k, k' of
    KVar v, _ | Set.member v kindVars -> case Map.lookup v s.kinds of
      Nothing -> Just s { kinds = Map.insert v k' s.kinds }
      Just bound -> if bound == k' then Just s else Nothing
    KFun a b, KFun a' b' -> goKind s a a' >>= \s' -> goKind s' b b'
    _, _ -> Just s

  -- The keys the pattern's row holds are matched by key, and a variable that
  -- is the pattern's whole tail takes what the type's row holds beyond them.
  row s p t = case nf p, nf t of
    Right np, Right nt -> do
      s' <- foldM (payload nt) s (Map.toUnfoldable np.known :: P.Array (Tuple RowKey RowPayload))
      case Set.toUnfoldable np.tail :: P.Array TyVar of
        [ v ] | Set.member v vars -> do
          rest <- fromNormalForm nt { known = Map.filterKeys (\k -> not (Map.member k np.known)) nt.known }
          go s' (TVar v) rest
        _ -> Just s'
    _, _ -> Just s

  payload nt s (Tuple key p) = case p, Map.lookup key nt.known of
    TypePayload a, Just (TypePayload b) -> go s a b
    EffectPayload e as, Just (EffectPayload e' bs) | e == e' && Array.length as == Array.length bs ->
      foldM (\acc (Tuple a b) -> go acc a b) s (Array.zip as bs)
    _, _ -> Just s

  isRow = case _ of
    TRowEmpty -> true
    TRowExtend _ _ -> true
    TRowUnion _ _ -> true
    _ -> false
