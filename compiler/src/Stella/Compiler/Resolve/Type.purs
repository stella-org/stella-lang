-- | Resolving kinds, types, and signatures into the Surface AST.
-- |
-- | A name of the type namespace becomes the type constructor, the type
-- | synonym, or the effect it stands for, and a type variable the binding it
-- | refers to. A chain of type operators is rebracketed by fixity, and a row
-- | keeps the items its bracket admits.
-- |
-- | **A signature quantifies implicitly** the type variables it mentions that
-- | nothing around it binds, outermost and in the order they first appear. The
-- | variables a signature quantifies, implicitly or by a `forall` on its spine,
-- | are in scope in the body of what it is the signature of, and in the
-- | signatures and annotations nested there. Any other type — an annotation,
-- | a field of a constructor, the right side of a synonym, an operation's
-- | signature — binds nothing implicitly, so a variable no binder binds is an
-- | error there.
-- |
-- | `->*`, a computation type anywhere but at the end of the spine of a
-- | computation declaration's signature, and a directive in a type are reported
-- | by `Stella.Compiler.CST.Check`, and leave an invalid type here with no
-- | second report.
module Stella.Compiler.Resolve.Type
  ( resolveKind
  , resolveType
  , resolveSignature
  , resolveComputationSignature
  , resolveOperationSignature
  , resolveHandlerSignature
  , bindTypeVariables
  , signatureScope
  , computationScope
  , handlerScope
  ) where

import Prelude
import Prim hiding (Type)

import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldM, foldMap)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), isJust, maybe)
import Data.Set (Set)
import Data.Set as Set
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Stella.Compiler.CST.Range (covering, kindRange, typeRange)
import Stella.Compiler.CST.Types as CST
import Stella.Compiler.Resolve.Fixity (rebracket)
import Stella.Compiler.Resolve.Label (reportLabelsTwice)
import Stella.Compiler.Resolve.Monad (Found(..), Resolve, ResolveReason(..), ResolveWarning(..), TypeReference(..), freshBinding, lookupType, lookupTypeOperator, lookupValue, report, typeVariable, typeVariables, warn, withTypeVariables)
import Stella.Compiler.Surface.Name (TypeVar(..))
import Stella.Compiler.Surface.Origin (Origin(..), spanning)
import Stella.Compiler.Surface.Type (ComputationType, EffectApplication, EffectRowItem(..), HandlerSignature(..), Kind(..), OperationSignature, RecordRowItem(..), Signature, SignaturePrefix(..), Type(..), TypeOperatorTarget(..), TypeVarBinder, VariantRowItem(..), typeOrigin)
import Stella.Compiler.TypedCore.Kind (RowElemKind(..))
import Stella.Compiler.TypedCore.Name (Ident(..), KindVar(..), Symbol(..), Tag(..), TyVar(..))
import Stella.Compiler.TypedCore.Prim (unitTy)

-- | A kind. A word other than `Type`, `Effect`, and `Row`, a qualified one,
-- | and `Row` applied to anything but `Type` or `Effect` are malformed.
resolveKind :: CST.Kind -> Resolve Kind
resolveKind k = case k of
  CST.KindName _
    | Just "Type" <- word k -> pure (KindType o)
    | Just "Effect" <- word k -> pure (KindEffect o)
  CST.KindApp f a
    | Just "Row" <- word f, Just "Type" <- word a -> pure (KindRow o RowType)
    | Just "Row" <- word f, Just "Effect" <- word a -> pure (KindRow o RowEffect)
  CST.KindVar n -> pure (KindVariable o (KindVar n.name))
  CST.KindArrow a b -> KindArrow o <$> resolveKind a <*> resolveKind b
  CST.KindParens inner -> resolveKind inner
  _ -> report (kindRange k) KindMalformed $> KindInvalid o
  where
  o = FromSource (kindRange k)
  word = case _ of
    CST.KindName n | n.qualifier == Nothing -> Just n.name
    CST.KindParens inner -> word inner
    _ -> Nothing

-- | A type standing anywhere but on the spine of a signature, with the type
-- | variables in scope it may mention.
resolveType :: CST.Type -> Resolve Type
resolveType t = case t of
  CST.TypeVar n -> typeVariable n.name >>= case _ of
    Just v -> pure (TypeVariable o v)
    Nothing -> invalid (UnknownTypeVariable n.name)
  CST.TypeConstructor n -> lookupType n >>= case _ of
    Found (TypeConstructorReference q) -> pure (TypeConstructor o q)
    Found (TypeSynonymReference q) -> pure (TypeSynonym o q)
    Found (EffectReference _) -> invalid (EffectNotType (written n))
    NotFound -> invalid (UnknownType (written n))
    Ambiguous -> invalid (AmbiguousType (written n))
  CST.TypeWildcard _ -> pure (TypeWildcard o)
  CST.TypeHole n -> pure (TypeHole o n.name)
  CST.TypeUnit _ -> pure (TypeConstructor o unitTy)
  CST.TypeApp f a -> TypeApp o <$> resolveType f <*> resolveType a
  CST.TypeOp _ _ _ -> operatorChain t
  CST.TypeArrow a (CST.TypeEffect b _ row) ->
    TypeFunction o <$> resolveType a <*> resolveType b <*> (Just <$> resolveType row)
  CST.TypeArrow a b -> TypeFunction o <$> resolveType a <*> resolveType b <*> pure Nothing
  CST.TypeOperationArrow _ _ _ -> pure (TypeInvalid o)
  CST.TypeEffect _ _ _ -> pure (TypeInvalid o)
  CST.TypeCapability _ _ -> invalid CapabilityMisplaced
  CST.TypeForall bs body -> do
    b <- bindTypeVariables bs
    TypeForall o b.binders <$> withTypeVariables b.scope (resolveType body)
  CST.TypeConstrained c body -> TypeConstrained o <$> resolveType c <*> resolveType body
  CST.TypeKinded inner k -> TypeKinded o <$> resolveType inner <*> resolveKind k
  CST.TypeParens inner -> resolveType inner
  CST.TypeTuple ts -> TypeTuple o <$> traverse resolveType ts
  CST.TypeRecord _ items -> do
    reportLabelsTwice (Array.mapMaybe fieldLabel items)
    TypeRecord o <$> rowItems recordItem items
  CST.TypeVariant _ items -> TypeVariant o <$> rowItems variantItem items
  CST.TypeEffectRow _ items -> TypeEffectRow o <$> rowItems effectItem items
  CST.TypeSynthesized _ _ _ -> invalid SynthesizedMisplaced
  CST.TypeDirective _ _ -> pure (TypeInvalid o)
  where
  o = FromSource (typeRange t)
  invalid reason = report (typeRange t) reason $> TypeInvalid o
  fieldLabel = case _ of
    CST.RowField n _ -> Just n
    _ -> Nothing

-- | The signature of a value, a foreign, or a `let` binding.
resolveSignature :: CST.Type -> Resolve (Signature Type)
resolveSignature t = quantify t (spine t)

-- | The signature of a computation declaration, whose spine ends in a
-- | computation type.
resolveComputationSignature :: CST.Type -> Resolve (Signature ComputationType)
resolveComputationSignature t = quantify t (go [] t)
  where
  go prefix x = case x of
    CST.TypeForall bs body -> do
      b <- bindTypeVariables bs
      withTypeVariables b.scope (go (Array.snoc prefix (PrefixForall (bindersOrigin x b.binders) b.binders)) body)
    CST.TypeConstrained c body -> do
      c' <- resolveType c
      go (Array.snoc prefix (PrefixConstraint c')) body
    CST.TypeParens inner -> go prefix inner
    CST.TypeArrow a rest | CST.isSynthesized a -> do
      a' <- synthesized a
      go (Array.snoc prefix (PrefixSynthesized a')) rest
    CST.TypeEffect result _ row -> do
      result' <- resolveType result
      row' <- resolveType row
      pure { origin, prefix, result: result', row: row' }
    other -> do
      result <- resolveType other
      pure { origin, prefix, result, row: TypeInvalid (FromSource (typeRange other)) }
  origin = FromSource (typeRange t)
  -- The binders of a `forall`, which are never none.
  bindersOrigin x bs = case Array.uncons bs of
    Just { head, tail } -> Array.foldl (\acc b -> spanning acc b.origin) head.origin tail
    Nothing -> FromSource (typeRange x)

-- | An operation's signature, with the parameters of its effect in scope. It
-- | quantifies nothing implicitly: its own type variables are written in a
-- | `forall`.
resolveOperationSignature :: CST.Type -> Resolve OperationSignature
resolveOperationSignature t = go [] [] t
  where
  origin = FromSource (typeRange t)
  go binders arguments x = case x of
    CST.TypeForall bs body -> do
      b <- bindTypeVariables bs
      withTypeVariables b.scope (go (binders <> b.binders) arguments body)
    CST.TypeParens inner -> go binders arguments inner
    CST.TypeArrow a rest -> do
      a' <- resolveType a
      go binders (Array.snoc arguments a') rest
    CST.TypeOperationArrow a _ b -> do
      a' <- resolveType a
      b' <- resolveType b
      pure { origin, binders, arguments: Array.snoc arguments a', resumesWith: b' }
    other -> do
      resumesWith <- resolveType other
      pure { origin, binders, arguments, resumesWith }

-- | A handler declaration's signature: `forall ā. E ~> ( t̄ )`, each `forall`
-- | in front of `~>` binding over the rest, or a type written in full.
resolveHandlerSignature :: CST.Type -> Resolve (Signature HandlerSignature)
resolveHandlerSignature t = quantify t
  if isCapability t then capability [] t else General <$> spine t
  where
  origin = FromSource (typeRange t)
  isCapability = case _ of
    CST.TypeForall _ body -> isCapability body
    CST.TypeParens inner -> isCapability inner
    CST.TypeCapability _ _ -> true
    _ -> false
  capability quantifiers = case _ of
    CST.TypeForall bs body -> do
      b <- bindTypeVariables bs
      withTypeVariables b.scope (capability (Array.snoc quantifiers b.binders) body)
    CST.TypeParens inner -> capability quantifiers inner
    CST.TypeCapability source target -> do
      source' <- effectApplication source
      targets <- capabilityTargets target
      pure case source' of
        Just s -> Capability { origin, quantifiers, source: s, targets }
        Nothing -> General (TypeInvalid origin)
    _ -> pure (General (TypeInvalid origin))

-- | Binds a group of type variables, each with its kind where one is written.
-- | A name bound twice in the group is reported, and the first binding is the
-- | one in scope. The scope is what to put in scope for what the group binds
-- | over.
bindTypeVariables
  :: Array CST.TypeVarBinding
  -> Resolve { binders :: Array TypeVarBinder, scope :: Array TypeVar }
bindTypeVariables bs = do
  binders <- foldM step [] bs
  pure { binders, scope: scopeOf binders }
  where
  step acc b = do
    let
      { name: n, kind: k } = case b of
        CST.BindName n' -> { name: n', kind: Nothing }
        CST.BindKinded n' k' -> { name: n', kind: Just k' }
      range = maybe n.range (covering n.range <<< kindRange) k
    outer <- typeVariable n.name
    if Array.any (\prior -> nameOf prior.var == n.name) acc then report n.range (BoundTwice n.name)
    else when (isJust outer) (warn (HidesTypeVariable n.range n.name))
    id <- freshBinding
    kind <- traverse resolveKind k
    pure (Array.snoc acc { origin: FromSource range, var: TypeVar { id, name: TyVar n.name }, kind })

-- | The type variables a signature puts in scope over the body of what it is
-- | the signature of: those it quantifies implicitly, then those the
-- | quantifiers on its spine bind.
signatureScope :: Signature Type -> Array TypeVar
signatureScope s = s.implicit <> spineBinders s.body
  where
  spineBinders = case _ of
    TypeForall _ bs body -> scopeOf bs <> spineBinders body
    TypeConstrained _ _ body -> spineBinders body
    TypeFunction _ (TypeSynthesized _ _ _ _) body Nothing -> spineBinders body
    _ -> []

computationScope :: Signature ComputationType -> Array TypeVar
computationScope s = s.implicit <> foldMap binders s.body.prefix
  where
  binders = case _ of
    PrefixForall _ bs -> scopeOf bs
    PrefixConstraint _ -> []
    PrefixSynthesized _ -> []

handlerScope :: Signature HandlerSignature -> Array TypeVar
handlerScope s = case s.body of
  Capability c -> s.implicit <> foldMap scopeOf c.quantifiers
  General t -> signatureScope { implicit: s.implicit, body: t }

-- | Quantifies a signature implicitly over the type variables it mentions that
-- | nothing binds, and resolves it with them in scope.
quantify :: forall a. CST.Type -> Resolve a -> Resolve (Signature a)
quantify t body = do
  inScope <- typeVariables
  implicit <- traverse fresh (freeVariables inScope t)
  b <- withTypeVariables implicit body
  pure { implicit, body: b }
  where
  fresh n = freshBinding <#> \id -> TypeVar { id, name: TyVar n.name }

-- | The spine of a signature: its quantifiers, its constraints, and its
-- | synthesized arguments, then the type it ends in. A synthesized argument
-- | stands here and nowhere else, behind a pure arrow.
spine :: CST.Type -> Resolve Type
spine t = case t of
  CST.TypeForall bs body -> do
    b <- bindTypeVariables bs
    TypeForall o b.binders <$> withTypeVariables b.scope (spine body)
  CST.TypeConstrained c body -> TypeConstrained o <$> resolveType c <*> spine body
  CST.TypeParens inner -> spine inner
  CST.TypeArrow a rest | CST.isSynthesized a -> case rest of
    -- A computation type, which only a computation declaration's signature
    -- ends in; `CST.Check` reports it elsewhere.
    CST.TypeEffect _ _ _ -> pure (TypeInvalid o)
    _ -> TypeFunction o <$> synthesized a <*> spine rest <*> pure Nothing
  _ -> resolveType t
  where
  o = FromSource (typeRange t)

synthesized :: CST.Type -> Resolve Type
synthesized t = case t of
  CST.TypeParens inner -> synthesized inner
  CST.TypeSynthesized n dictionary f -> do
    dictionary' <- resolveType dictionary
    lookupValue f >>= case _ of
      Found q -> pure (TypeSynthesized o (map (Ident <<< _.name) n) dictionary' q)
      NotFound -> report f.range (UnknownValue (written f)) $> TypeInvalid o
      Ambiguous -> report f.range (AmbiguousValue (written f)) $> TypeInvalid o
  _ -> resolveType t
  where
  o = FromSource (typeRange t)

-- | A chain of type operators, rebracketed by fixity. An operator nothing in
-- | scope stands for, or two that cannot be chained, leave the chain invalid.
operatorChain :: CST.Type -> Resolve Type
operatorChain t = do
  let chain = flatten t
  first <- resolveType chain.first
  rest <- traverse (\(Tuple n operand) -> Tuple <$> operator n <*> resolveType operand) chain.rest
  case traverse (\(Tuple op operand) -> map (\op' -> Tuple op' operand) op) rest of
    Nothing -> pure (TypeInvalid o)
    Just ops -> case rebracket _.fixity apply first ops of
      Right result -> pure result
      Left { first: a, second: b } ->
        report b.name.range (OperatorsUnordered (written b.name) (written a.name)) $> TypeInvalid o
  where
  o = FromSource (typeRange t)
  flatten = case _ of
    CST.TypeOp a n b -> let c = flatten a in c { rest = Array.snoc c.rest (Tuple n b) }
    x -> { first: x, rest: [] }
  operator n = lookupTypeOperator n >>= case _ of
    -- An operator whose target does not resolve is reported where it is
    -- declared, and leaves the chain invalid here.
    Found (Tuple _ f) ->
      pure (f.target <#> \target -> { name: n, target, fixity: { associativity: f.associativity, precedence: f.precedence } })
    NotFound -> report n.range (UnknownTypeOperator (written n)) $> Nothing
    Ambiguous -> report n.range (AmbiguousTypeOperator (written n)) $> Nothing
  apply op l r = TypeOperator (spanning (typeOrigin l) (typeOrigin r)) { origin: FromSource op.name.range, target: op.target } l r

rowItems :: forall a. (CST.RowItem -> Resolve (Maybe a)) -> Array CST.RowItem -> Resolve (Array a)
rowItems f items = Array.catMaybes <$> traverse f items

recordItem :: CST.RowItem -> Resolve (Maybe RecordRowItem)
recordItem item = case item of
  CST.RowField n t -> Just <<< RecordField (itemOrigin item) (Symbol n.name) <$> resolveType t
  CST.RowSpread _ t -> Just <<< RecordSpread (itemOrigin item) <$> traverse resolveType t
  _ -> misplaced item

variantItem :: CST.RowItem -> Resolve (Maybe VariantRowItem)
variantItem item = case item of
  CST.RowTag n t -> Just <<< VariantTag (itemOrigin item) (Tag n.name) <$> resolveType t
  CST.RowField n t -> Just <<< VariantLabel (itemOrigin item) (Symbol n.name) <$> resolveType t
  CST.RowSpread _ t -> Just <<< VariantSpread (itemOrigin item) <$> traverse resolveType t
  _ -> misplaced item

-- | An item of an effect row. One whose effect is not an effect applied to its
-- | arguments is dropped from the row.
effectItem :: CST.RowItem -> Resolve (Maybe EffectRowItem)
effectItem item = case item of
  CST.RowElement t -> map EffectElement <$> effectApplication t
  CST.RowField n t -> map (EffectInstance (itemOrigin item) (Symbol n.name)) <$> effectApplication t
  CST.RowSpread _ t -> Just <<< EffectSpread (itemOrigin item) <$> traverse resolveType t
  _ -> misplaced item

misplaced :: forall a. CST.RowItem -> Resolve (Maybe a)
misplaced item = report (itemRange item) RowItemMisplaced $> Nothing

itemOrigin :: CST.RowItem -> Origin
itemOrigin = FromSource <<< itemRange

itemRange :: CST.RowItem -> CST.SourceRange
itemRange = case _ of
  CST.RowField n t -> covering n.range (typeRange t)
  CST.RowTag n t -> covering n.range (typeRange t)
  CST.RowElement t -> typeRange t
  CST.RowSpread r t -> maybe r (covering r <<< typeRange) t

-- | An effect applied to its arguments: a name standing for an effect at the
-- | head of an application, or a type operator standing for one, applied to its
-- | two operands and then to whatever the application adds after them.
effectApplication :: CST.Type -> Resolve (Maybe EffectApplication)
effectApplication t = case application t of
  { head: CST.TypeConstructor n, arguments } -> lookupType n >>= case _ of
    Found (EffectReference effect) -> do
      arguments' <- traverse resolveType arguments
      pure (Just { origin: o, effect, arguments: arguments' })
    Found _ -> expected
    NotFound -> report n.range (UnknownType (written n)) $> Nothing
    Ambiguous -> report n.range (AmbiguousType (written n)) $> Nothing
  { head: head@(CST.TypeOp _ _ _), arguments } -> operatorChain head >>= case _ of
    TypeOperator _ { target: TargetEffect effect } l r -> do
      arguments' <- traverse resolveType arguments
      pure (Just { origin: o, effect, arguments: [ l, r ] <> arguments' })
    TypeInvalid _ -> pure Nothing
    _ -> expected
  _ -> expected
  where
  o = FromSource (typeRange t)
  expected = report (typeRange t) EffectExpected $> Nothing
  application x = case x of
    CST.TypeApp f a -> let s = application f in s { arguments = Array.snoc s.arguments a }
    CST.TypeParens inner -> application inner
    _ -> { head: x, arguments: [] }

-- | What `~>` translates into: `()`, or effects in parentheses.
capabilityTargets :: CST.Type -> Resolve (Array EffectApplication)
capabilityTargets t = case t of
  CST.TypeUnit _ -> pure []
  CST.TypeParens inner -> Array.fromFoldable <$> effectApplication inner
  CST.TypeTuple ts -> Array.catMaybes <$> traverse effectApplication ts
  _ -> report (typeRange t) CapabilityTargetMalformed $> []

-- | The variables a type mentions that neither a `forall` inside it nor the
-- | scope binds, each once, in the order they first appear.
freeVariables :: Map String TypeVar -> CST.Type -> Array CST.Name
freeVariables inScope = Array.nubByEq (\a b -> a.name == b.name) <<< go Set.empty
  where
  go :: Set String -> CST.Type -> Array CST.Name
  go bound t = case t of
    CST.TypeVar n
      | Set.member n.name bound || Map.member n.name inScope -> []
      | otherwise -> [ n ]
    CST.TypeForall bs body -> go (Set.union bound (Set.fromFoldable (map bindingName bs))) body
    _ -> foldMap (go bound) (children t)
  bindingName = case _ of
    CST.BindName n -> n.name
    CST.BindKinded n _ -> n.name

-- | The types a type is built from, in the order written.
children :: CST.Type -> Array CST.Type
children = case _ of
  CST.TypeVar _ -> []
  CST.TypeConstructor _ -> []
  CST.TypeWildcard _ -> []
  CST.TypeHole _ -> []
  CST.TypeUnit _ -> []
  CST.TypeApp f a -> [ f, a ]
  CST.TypeOp a _ b -> [ a, b ]
  CST.TypeArrow a b -> [ a, b ]
  CST.TypeOperationArrow a _ b -> [ a, b ]
  CST.TypeEffect a _ b -> [ a, b ]
  CST.TypeCapability a b -> [ a, b ]
  CST.TypeForall _ t -> [ t ]
  CST.TypeConstrained c t -> [ c, t ]
  CST.TypeKinded t _ -> [ t ]
  CST.TypeParens t -> [ t ]
  CST.TypeTuple ts -> ts
  CST.TypeRecord _ items -> foldMap item items
  CST.TypeEffectRow _ items -> foldMap item items
  CST.TypeVariant _ items -> foldMap item items
  CST.TypeSynthesized _ t _ -> [ t ]
  CST.TypeDirective _ t -> [ t ]
  where
  item = case _ of
    CST.RowField _ t -> [ t ]
    CST.RowTag _ t -> [ t ]
    CST.RowElement t -> [ t ]
    CST.RowSpread _ t -> Array.fromFoldable t

-- | The variables a group of binders puts in scope: one per name, the first
-- | binding of it.
scopeOf :: Array TypeVarBinder -> Array TypeVar
scopeOf = Array.nubByEq (\a b -> nameOf a == nameOf b) <<< map _.var

nameOf :: TypeVar -> String
nameOf (TypeVar v) = case v.name of
  TyVar n -> n

written :: CST.Name -> String
written n = maybe n.name (\q -> q <> "." <> n.name) n.qualifier
