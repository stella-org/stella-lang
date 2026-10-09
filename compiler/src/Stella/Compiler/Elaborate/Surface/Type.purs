-- | A type of the Surface AST elaborated into Core⁺, its kinds inferred
-- | ([Elaboration](../../../../../docs/technical-references/02-Surface-Language/01-Elaboration.md)).
-- |
-- | **A kind left unwritten is a kind metavariable**, and every kind a type is
-- | at is constrained by an equation as it is read: a constructor at an
-- | instance of its kind scheme, an application at the arrow its head must be,
-- | an arrow's sides and a `forall`'s body at `Type`. The equations are decided
-- | as they are met, kinds never waiting; whether every kind ended up solved is
-- | asked once the elaboration they belong to is done, of each place that left
-- | one unwritten: a binder, or a constructor instantiated at fresh kinds.
-- |
-- | **A type constructor the module declares is read at the kind its
-- | declaration is being given** while the module's data declarations are
-- | elaborated together: a kind variable written in the declaration is
-- | instantiated afresh where the constructor is used, and a metavariable
-- | standing for a kind left unwritten is the one kind every use shares.
-- |
-- | **A row is read in the bracket it is written in**: a record's and a
-- | variant's at `Row Type`, under `Prim.Record` and `Prim.Variant`, a tuple's
-- | as a record keyed by position, and an effect row at `Row Effect`, each
-- | effect applied at the kinds its parameters are declared at. An arrow
-- | carries the effect row `/` writes on it, and is pure otherwise.
-- |
-- | **What a row's sharpness needs of the rows it spreads is carried by the
-- | binder of their variables.** A key the row holds is absent from each row
-- | variable it spreads, and two such variables are apart: each condition
-- | stands as a constraint under the innermost binder that binds a variable it
-- | is about — a `forall` written in the type, or the signature's implicit
-- | quantifiers. One about none of them is left to whoever reads the type: an
-- | annotation requires it where it stands, and a data type's field, whose
-- | parameters carry no condition, refuses it.
-- |
-- | **A type synonym is expanded where it is used**, its whole spine of
-- | applications read at once: its parameters are replaced by as many
-- | arguments, and the arguments beyond them are applied to what it stands for.
-- |
-- | **This version reads a subset of types**: variables, constructors,
-- | applications, arrows, `forall`, kind annotations, tuples, rows and the rows
-- | they spread, where a spread row is read as the empty row, elements over a
-- | row, unions, and row variables, the type synonyms the imports declare, and
-- | type operators naming a type constructor or one of those synonyms.
-- | Anything else is reported as outside it, and stands meanwhile as a fresh
-- | metavariable, so what surrounds it is still read.
module Stella.Compiler.Elaborate.Surface.Type
  ( Unsupported(..)
  , Atom(..)
  , Implied
  , atomConstraint
  , Elaborated
  , Read
  , Scope
  , LocalHead
  , ReadBinder
  , elaborateSignature
  , elaborateType
  , readTypeAt
  , readBinder
  , readKind
  , siteOf
  , typeKindVars
  , xFunction
  , settledScheme
  , schemeOf
  , elaborateComputationSignature
  , SynthesizedMark
  ) where

import Prelude
import Prim hiding (Type)

import Data.Array as Array
import Data.Array.NonEmpty (NonEmptyArray)
import Data.Array.NonEmpty as NonEmptyArray
import Data.Foldable (foldM, foldMap, foldl, foldr, for_)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, isJust, maybe)
import Data.Set (Set)
import Data.Set as Set
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Data.Either (Either(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Stella.Compiler.Elaborate.CorePlus.Context (Origin(..), XContext, emptyXContext)
import Stella.Compiler.Elaborate.CorePlus.Kind (XKind(..), fromCoreKind, kindMetasOf)
import Data.Monoid.Disj (Disj(..))
import Stella.Compiler.Elaborate.CorePlus.Type (XConstraint(..), XRowEntry(..), XType(..), freeRigids, fromCore, toCore, xRowEntryKey)
import Stella.Compiler.Elaborate.Environment.Synonyms (SynonymEntry, SynonymEnv, lookupSynonym)
import Stella.Compiler.Elaborate.Kernel.Builder.Common (foldChildren, substituteKindVars, substituteTyVars)
import Stella.Compiler.Elaborate.Kernel.Elab (Elab, askEnv, equateKinds, freshBinderName, freshKindMeta, freshTypeMeta, raiseDiagnostic, require)
import Stella.Compiler.Elaborate.Vocabulary.Diagnostic (Diagnostic(..))
import Stella.Compiler.Elaborate.Mechanism.Kinding (instantiate)
import Stella.Compiler.Elaborate.Mechanism.Kinding (quantifiable) as Kinding
import Stella.Compiler.Elaborate.Mechanism.Pending (Site)
import Stella.Compiler.Elaborate.Mechanism.Unify (KindRequirement(..), MetaContext, UnifyError(..), substitute, substituteKind)
import Stella.Compiler.Surface.Name (TypeVar(..))
import Stella.Compiler.Surface.Origin as Surface
import Stella.Compiler.Surface.Type (ComputationType, EffectApplication, EffectRowItem(..), Kind(..), RecordRowItem(..), Signature, SignaturePrefix(..), Type(..), TypeOperatorTarget(..), TypeVarBinder, VariantRowItem(..), typeOrigin)
import Stella.Compiler.TypedCore.Kind (RowElemKind(..))
import Stella.Compiler.TypedCore.Name (EffName, Ident, KindVar, Qualified, TyName, TyVar(..))
import Stella.Compiler.Interface.Scheme (Scheme, SchemeBody(..))
import Stella.Compiler.TypedCore.Prim (asFunction, functionTy, recordTy, unitTy, variantTy)
import Stella.Compiler.TypedCore.Type (RowKey(..), TypeScheme)
import Stella.Compiler.TypedCore.Type (Type(..)) as Core

-- | A part of a type that is not read, where it stands: a form this version
-- | does not read, one resolution reported already, or an effect standing
-- | where a type does.
data Unsupported
  = OutsideSubset Surface.Origin String
  | ReportedAlready Surface.Origin
  -- | A type operator naming an effect, applied where no effect row's element
  -- | stands: an effect is no type.
  | EffectAsType Surface.Origin (Qualified EffName)
  -- | A row that would hold a key twice, one of them brought by a spread.
  | KeyTwice Surface.Origin RowKey
  -- | A row spreading one row variable twice.
  | SpreadTwice Surface.Origin TyVar
  -- | `...` with no row, where nothing quantifies the row it stands for.
  | AnonymousSpread Surface.Origin
  -- | A condition a row's sharpness puts on a variable bound where no
  -- | condition can be carried: a data type's parameter.
  | UnheldConstraint Surface.Origin Atom
  -- | A synonym applied to fewer arguments than it has parameters, which it
  -- | names with how many it has.
  | SynonymUnsaturated Surface.Origin (Qualified TyName) Int

-- | A condition the sharpness of a row written in a type puts on its tails:
-- | that a tail lacks a key the row holds beside it, or that two of its tails
-- | are apart. A row's tails are row variables, so the condition is atomic.
data Atom
  = LacksAtom RowKey TyVar
  | DisjointAtom TyVar TyVar

-- | An atom, and where the row requiring it stands.
type Implied = { origin :: Surface.Origin, atom :: Atom }

-- | The constraint an atom is.
atomConstraint :: Atom -> XConstraint
atomConstraint = case _ of
  LacksAtom key tail -> XLacks key (XVar tail)
  DisjointAtom a b -> XDisjoint (XVar a) (XVar b)

-- | The variables an atom is about.
atomVars :: Atom -> Set TyVar
atomVars = case _ of
  LacksAtom _ tail -> Set.singleton tail
  DisjointAtom a b -> Set.fromFoldable [ a, b ]

-- | `C̄ => τ`, the atoms given normalized: each once, in their order.
constrained :: Array Implied -> XType -> XType
constrained implied body = foldr (\a t -> XConstrained (atomConstraint a) t) body (Set.toUnfoldable (Set.fromFoldable (map _.atom implied)) :: Array Atom)

-- | `forall` of the binders given, outermost first, over the body: each atom
-- | about one of them stands directly under the innermost binder it is about,
-- | and the atoms about none of them are given back.
quantify :: Array { var :: TyVar, kind :: XKind } -> Array Implied -> XType -> { type :: XType, rest :: Array Implied }
quantify binders implied body = foldr bind { type: body, rest: implied } binders
  where
  bind b inner =
    let
      split = Array.partition (\i -> Set.member b.var (atomVars i.atom)) inner.rest
    in
      { type: XForall b.var b.kind (constrained split.yes inner.type), rest: split.no }

-- | Each atom once, the first given standing for it.
distinctAtoms :: Array Implied -> Array Implied
distinctAtoms = Array.nubByEq (\x y -> x.atom == y.atom)

-- | A signature elaborated: where its type stands; the kind variables its
-- | kinds mention, which its scheme binds; its type; each place a kind was
-- | left unwritten, with the kind standing for it; and what was outside the
-- | subset.
type Elaborated =
  { origin :: Surface.Origin
  , kindVars :: Array KindVar
  , type :: XType
  , unwritten :: Array { origin :: Surface.Origin, kind :: XKind }
  , unsupported :: Array Unsupported
  , synthesized :: Array SynthesizedMark
  , computation :: Boolean
  }

-- | A synthesized argument on a signature's spine, its dictionary's type read
-- | with the rest of the type: the name written for it, and its synthesizer.
type SynthesizedMark = { name :: Maybe Ident, synthesizer :: Qualified Ident }

-- | What a type is read under: the declaration it belongs to, the kind
-- | variables in scope, the kind of each type variable bound, the type
-- | constructors the module declares whose kinds are being decided, and the
-- | row variable `...` stands for at each row kind, where a signature
-- | quantifies one, and the type synonyms a type is read through.
type Scope =
  { declaration :: Qualified Ident
  , kindVars :: Set KindVar
  , tyVars :: Map TyVar XKind
  , localTypes :: Map (Qualified TyName) LocalHead
  , anonymous :: Map RowElemKind TyVar
  , synonyms :: SynonymEnv
  }

-- | The kind a type constructor of the module is read at while its declaration
-- | is elaborated: over the kind variables its declaration writes, and holding
-- | a metavariable for each kind it leaves unwritten.
type LocalHead = { kindVars :: Array KindVar, body :: XKind }

-- | A binder read: its variable, its kind, where its kind was left unwritten,
-- | and what was outside the subset.
type ReadBinder = { var :: TypeVar, kind :: XKind, unwritten :: Array { origin :: Surface.Origin, kind :: XKind }, unsupported :: Array Unsupported }

-- | What reading one type gave. `implied` are the atoms its rows require that
-- | no binder in it took: they are about variables bound around it.
type Read =
  { type :: XType
  , kind :: XKind
  , unwritten :: Array { origin :: Surface.Origin, kind :: XKind }
  , unsupported :: Array Unsupported
  , implied :: Array Implied
  }

-- | `forall ā. C̄ => τ`, at `Type`: `ā` the variables the signature quantifies
-- | implicitly, in the order they are first mentioned, and `C̄` what the rows
-- | of `τ` require of them that no `forall` inside `τ` took.
-- |
-- | **`...` with no row is a variable the signature quantifies implicitly**, one
-- | per row kind, so every `...` of one kind in the signature is the same row;
-- | it is named apart from every name source can write.
elaborateSignature :: SynonymEnv -> Qualified Ident -> Signature Type -> Elab Elaborated
elaborateSignature = elaborateSpine false

-- | The signature of a computation declaration, `forall ā. C => {{ … }} -> τ / ρ`,
-- | read as its Core type is, `∀ā. C => … -> Unit -{ρ}-> τ`, the computation
-- | marked on its spine.
elaborateComputationSignature :: SynonymEnv -> Qualified Ident -> Signature ComputationType -> Elab Elaborated
elaborateComputationSignature synonyms declaration signature =
  elaborateSpine true synonyms declaration { implicit: signature.implicit, body: computationAsType signature.body }

-- | A signature read, a computation's where the flag says it is one, each
-- | synthesized argument on its spine read as the type of its dictionary.
elaborateSpine :: Boolean -> SynonymEnv -> Qualified Ident -> Signature Type -> Elab Elaborated
elaborateSpine computation synonyms declaration signature = do
  let spine = synthesizedOnSpine signature.body
  let kindVars = foldr Set.insert Set.empty (typeKindVars signature.body)
  named <- traverse (\v -> { var: v, kind: _ } <$> freshKindMeta kindVars quantifiable) signature.implicit
  spreads <- traverse
    (\k -> { kind: k, var: _ } <$> freshBinderName (writtenTyVars signature.body) (hintOf k))
    (Array.nub (Array.mapMaybe spreadKind (mentions signature.body)))
  let
    quantified = Array.nub (Array.mapMaybe quantifier (mentions signature.body))
      <> map (\n -> { var: nameOf n.var, kind: n.kind }) (Array.filter (\n -> not (Array.elem (MentionVar n.var) (mentions signature.body))) named)
    quantifier = case _ of
      MentionVar v -> map (\n -> { var: nameOf n.var, kind: n.kind }) (Array.find (\n -> n.var == v) named)
      MentionSpread k -> map (\s -> { var: s.var, kind: XKRow k }) (Array.find (\s -> s.kind == k) spreads)
    scope =
      { declaration
      , kindVars
      , tyVars: Map.fromFoldable (map (\q -> Tuple q.var q.kind) quantified)
      , localTypes: Map.empty
      , anonymous: Map.fromFoldable (map (\s -> Tuple s.kind s.var) spreads)
      , synonyms
      }
  body <- checkAt scope XKType spine.type
  let taken = quantify quantified body.implied body.type
  pure
    { origin: typeOrigin signature.body
    , kindVars: Array.fromFoldable kindVars
    , type: taken.type
    -- an implicit variable is written first where it is first mentioned
    , unwritten: map (\i -> { origin: fromMaybe (typeOrigin signature.body) (firstMention i.var signature.body), kind: i.kind }) named <> body.unwritten
    , unsupported: body.unsupported <> map (\i -> UnheldConstraint i.origin i.atom) taken.rest
    , synthesized: spine.marks
    , computation
    }
  where
  spreadKind = case _ of
    MentionSpread k -> Just k
    MentionVar _ -> Nothing
  hintOf = case _ of
    RowType -> "r"
    RowEffect -> "e"

-- | A type written inside a declaration, at `Type`, under the kind variables and
-- | the type variables the context binds: an annotation, whose variables are
-- | those of the signature around it. What its rows require of those is
-- | required where the annotation stands, from what the context assumes, once
-- | every part of it is read.
elaborateType :: SynonymEnv -> Qualified Ident -> XContext -> Type -> Elab Read
elaborateType synonyms declaration context t = do
  r <- checkAt { declaration, kindVars: context.kindVars, tyVars: context.tyVars, localTypes: Map.empty, anonymous: Map.empty, synonyms } XKType t
  -- a form not read is reported before anything is required of what it stands in
  when (Array.null r.unsupported) do
    for_ r.implied \i -> require { context, origin: AtSource { declaration, origin: i.origin } } (atomConstraint i.atom)
  pure r { implied = [] }

-- | A type at the kind given, under the scope given.
readTypeAt :: Scope -> XKind -> Type -> Elab Read
readTypeAt = checkAt

-- | A binder, at the kind written or at a metavariable.
readBinder :: Scope -> TypeVarBinder -> Elab ReadBinder
readBinder = binder

-- | `τ1 -{ρ}-> τ2`.
xFunction :: XType -> XType -> XType -> XType
xFunction argument row result = XApp (XApp (XApp (XCon functionTy []) argument) row) result

-- | A type at the kind given.
checkAt :: Scope -> XKind -> Type -> Elab Read
checkAt scope expected t = do
  r <- readType scope t
  equateKinds (siteOf scope (typeOrigin t)) r.kind expected
  pure r

readType :: Scope -> Type -> Elab Read
readType scope t = case t of
  TypeVariable o v -> case Map.lookup (nameOf v) scope.tyVars of
    Just kind -> pure (plain (XVar (nameOf v)) kind)
    Nothing -> unsupported (OutsideSubset o "a type variable bound outside the signature")
  TypeConstructor o name | Just head <- Map.lookup name scope.localTypes -> do
    args <- traverse (\_ -> freshKindMeta scope.kindVars quantifiable) head.kindVars
    let instantiated = Map.fromFoldable (Array.zip head.kindVars args)
    pure
      { type: XCon name args
      , kind: instantiateKindVars instantiated head.body
      , unwritten: map (\kind -> { origin: o, kind }) args
      , unsupported: []
      , implied: []
      }
  TypeConstructor o name -> do
    env <- askEnv
    case Map.lookup name env.session.kinding.types of
      Just scheme -> do
        args <- traverse (\_ -> freshKindMeta scope.kindVars quantifiable) scheme.kindVars
        pure
          { type: XCon name args
          , kind: instantiate scheme args
          , unwritten: map (\kind -> { origin: o, kind }) args
          , unsupported: []
          , implied: []
          }
      Nothing -> unsupported (OutsideSubset o "a type constructor the signature does not hold")
  TypeApp _ _ _ | Just use <- synonymSpine t -> expandSynonym scope use
  TypeApp o f x -> do
    f' <- readType scope f
    x' <- readType scope x
    result <- freshKindMeta scope.kindVars Set.empty
    equateKinds (siteOf scope o) f'.kind (XKFun x'.kind result)
    pure (joined [ f', x' ] (XApp f'.type x'.type) result)
  TypeFunction _ a b Nothing -> do
    a' <- checkAt scope XKType a
    b' <- checkAt scope XKType b
    pure (joined [ a', b' ] (xFunction a'.type XRowEmpty b'.type) XKType)
  TypeFunction _ a b (Just row) -> do
    a' <- checkAt scope XKType a
    b' <- checkAt scope XKType b
    row' <- checkAt scope (XKRow RowEffect) row
    pure (joined [ a', b', row' ] (xFunction a'.type row'.type b'.type) XKType)
  TypeTuple _ components -> do
    read <- traverse (checkAt scope XKType) components
    let row = foldr (\(Tuple n c) rest -> XRowExtend (XRowTypeEntry (PositionKey n) c.type) rest) XRowEmpty (Array.mapWithIndex Tuple read)
    pure (joined read (XApp (XCon recordTy []) row) XKType)
  TypeRecord o items -> do
    row <- rowOf scope o RowType (map recordItem items)
    pure row { type = XApp (XCon recordTy []) row.type, kind = XKType }
  TypeVariant o items -> do
    row <- rowOf scope o RowType (map variantItem items)
    pure row { type = XApp (XCon variantTy []) row.type, kind = XKType }
  TypeEffectRow o items -> rowOf scope o RowEffect (map effectItem items)
  TypeOperator o op l r -> case op.target of
    TargetTypeConstructor name -> readType scope (TypeApp o (TypeApp o (TypeConstructor op.origin name) l) r)
    TargetTypeSynonym name -> expandSynonym scope { origin: o, name, arguments: [ l, r ] }
    TargetEffect effect -> unsupported (EffectAsType op.origin effect)
  TypeForall _ binders body -> do
    bound <- traverse (binder scope) binders
    let inner = scope { tyVars = foldr (\b m -> Map.insert (nameOf b.var) b.kind m) scope.tyVars bound }
    body' <- checkAt inner XKType body
    -- what the rows require of a variable this `forall` binds stands under it
    let taken = quantify (map (\b -> { var: nameOf b.var, kind: b.kind }) bound) body'.implied body'.type
    pure
      { type: taken.type
      , kind: XKType
      , unwritten: Array.concatMap _.unwritten bound <> body'.unwritten
      , unsupported: Array.concatMap _.unsupported bound <> body'.unsupported
      , implied: taken.rest
      }
  TypeKinded _ inner k -> do
    kind <- readKind k
    case kind of
      Right written -> checkAt scope written inner
      Left problem -> unsupported problem
  TypeInvalid o -> unsupported (ReportedAlready o)
  TypeSynonym o name -> expandSynonym scope { origin: o, name, arguments: [] }
  TypeConstrained o _ _ -> unsupported (OutsideSubset o "a constraint")
  TypeSynthesized o _ _ _ -> unsupported (OutsideSubset o "a synthesized argument")
  TypeWildcard o -> unsupported (OutsideSubset o "a wildcard")
  TypeHole o _ -> unsupported (OutsideSubset o "a typed hole")
  where
  plain ty kind = { type: ty, kind, unwritten: [], unsupported: [], implied: [] }

  unsupported = unreadType scope

-- | A synonym and the arguments it is applied to, where the type is one: the
-- | whole spine of applications headed by a synonym or by a type operator
-- | naming one, its operands the operator's first two arguments.
synonymSpine :: Type -> Maybe SynonymUse
synonymSpine t = go t []
  where
  go x arguments = case x of
    TypeApp _ f a -> go f (Array.cons a arguments)
    TypeSynonym _ name -> Just { origin: typeOrigin t, name, arguments }
    TypeOperator _ { target: TargetTypeSynonym name } l r -> Just { origin: typeOrigin t, name, arguments: [ l, r ] <> arguments }
    _ -> Nothing

-- | A synonym written applied to its arguments, and where the application
-- | stands.
type SynonymUse = { origin :: Surface.Origin, name :: Qualified TyName, arguments :: Array Type }

-- | A synonym applied to its arguments, expanded.
-- |
-- | **Saturation is judged on the whole spine.** A synonym applied to fewer
-- | arguments than it has parameters is refused; its parameters are replaced
-- | by as many arguments, each read at its parameter's kind, the synonym's kind
-- | variables instantiated afresh; and the arguments beyond them are applied to
-- | what it stands for. A `forall` of the synonym's body binding a name an
-- | argument mentions free is renamed, so the argument is not captured.
-- |
-- | A synonym whose body spreads a parameter into a row beside something else
-- | needs a condition of the row it is given, which a synonym carries none of,
-- | and is outside what this version reads.
expandSynonym :: Scope -> SynonymUse -> Elab Read
expandSynonym scope use = case lookupSynonym use.name scope.synonyms of
  Nothing -> unreadType scope (OutsideSubset use.origin "a type synonym the module declares")
  Just entry
    | Array.length use.arguments < Array.length entry.params -> unreadType scope (SynonymUnsaturated use.origin use.name (Array.length entry.params))
    | extendsParameter entry -> unreadType scope (OutsideSubset use.origin "a type synonym extending a row it is given")
    | otherwise -> do
        kinds <- traverse (\_ -> freshKindMeta scope.kindVars quantifiable) entry.kind.kindVars
        let
          byKind = Map.fromFoldable (Array.zip entry.kind.kindVars kinds)
          count = Array.length entry.params
        given <- traverse
          (\(Tuple p a) -> checkAt scope (instantiateKindVars byKind (fromCoreKind p.kind)) a)
          (Array.zip entry.params (Array.take count use.arguments))
        let
          body = substituteKindVars byKind (fromCore entry.body)
          captured = Set.intersection (bindersIn body) (foldMap (freeRigids <<< _.type) given)
          taken = Set.union (bindersIn body) (foldMap (freeRigids <<< _.type) given)
        renames <- traverse (\b@(TyVar hint) -> Tuple b <$> freshBinderName taken hint) (Array.fromFoldable captured)
        let
          expanded = substituteTyVars (Map.fromFoldable (Array.zip (map _.name entry.params) (map _.type given))) (Map.fromFoldable renames) body
          read = joined given expanded (dropArrows count (instantiateKindVars byKind (fromCoreKind entry.kind.body)))
        foldM (applied scope use.origin) (read { unwritten = map (\kind -> { origin: use.origin, kind }) kinds <> read.unwritten }) (Array.drop count use.arguments)
  where
  dropArrows n kind = case kind of
    XKFun _ result | n > 0 -> dropArrows (n - 1) result
    _ -> kind

-- | What is read, applied to one more argument.
applied :: Scope -> Surface.Origin -> Read -> Type -> Elab Read
applied scope origin f x = do
  x' <- readType scope x
  result <- freshKindMeta scope.kindVars Set.empty
  equateKinds (siteOf scope origin) f.kind (XKFun x'.kind result)
  pure (joined [ f, x' ] (XApp f.type x'.type) result)

-- | Whether a synonym's body spreads a parameter into a row holding a key or
-- | another row beside it. Below a `forall` binding a parameter's name, that
-- | name is the `forall`'s, whose conditions the `forall` carries.
extendsParameter :: SynonymEntry -> Boolean
extendsParameter entry = go (Set.fromFoldable (map _.name entry.params)) (fromCore entry.body)
  where
  go params t = case t of
    XForall b _ body -> go (Set.delete b params) body
    XRowExtend _ _ -> extends params t || descend params t
    XRowUnion _ _ -> extends params t || descend params t
    _ -> descend params t
  descend params t = case foldChildren (\c -> Disj (go params c)) t of
    Disj b -> b
  extends params t =
    let
      parts = partsOf t
    in
      Array.any (\v -> Set.member v params) parts.tails && (not (Array.null parts.keys) || Array.length parts.tails > 1)

-- | The type variables a `forall` inside the type binds.
bindersIn :: XType -> Set TyVar
bindersIn = case _ of
  XForall b _ body -> Set.insert b (bindersIn body)
  other -> foldChildren bindersIn other

-- | A form not read, standing as a metavariable of a kind of its own.
unreadType :: Scope -> Unsupported -> Elab Read
unreadType scope problem = do
  kind <- freshKindMeta scope.kindVars Set.empty
  meta <- freshTypeMeta (emptyXContext { kindVars = scope.kindVars }) kind
  pure { type: meta, kind, unwritten: [], unsupported: [ problem ], implied: [] }

joined :: Array Read -> XType -> XKind -> Read
joined parts ty kind =
  { type: ty
  , kind
  , unwritten: Array.concatMap _.unwritten parts
  , unsupported: Array.concatMap _.unsupported parts
  , implied: distinctAtoms (Array.concatMap _.implied parts)
  }

-- | An item of a row as written: an element, read by the action given, or a
-- | spread.
data RowItem
  = Element (Scope -> Elab { entry :: XRowEntry, read :: Read })
  | Spread Surface.Origin (Maybe Type)

recordItem :: RecordRowItem -> RowItem
recordItem = case _ of
  RecordField _ label t -> Element (typeEntry (SymbolKey label) t)
  RecordSpread o t -> Spread o t

variantItem :: VariantRowItem -> RowItem
variantItem = case _ of
  VariantTag _ tag t -> Element (typeEntry (TagKey tag) t)
  VariantLabel _ label t -> Element (typeEntry (SymbolKey label) t)
  VariantSpread o t -> Spread o t

effectItem :: EffectRowItem -> RowItem
effectItem = case _ of
  EffectElement application -> Element \scope -> do
    e <- effectApplication scope application
    pure { entry: XRowEffectEntry application.effect e.arguments, read: e.read }
  EffectInstance _ label application -> Element \scope -> do
    e <- effectApplication scope application
    pure { entry: XRowLabelledEffectEntry label application.effect e.arguments, read: e.read }
  EffectSpread o t -> Spread o t

-- | An element of a `Row Type`: its payload at `Type`, under its key.
typeEntry :: RowKey -> Type -> Scope -> Elab { entry :: XRowEntry, read :: Read }
typeEntry key t scope = do
  payload <- checkAt scope XKType t
  pure { entry: XRowTypeEntry key payload.type, read: payload }

-- | A row of the element kind given, written at the origin given: its
-- | elements in the order written, over the union of the rows it spreads, each
-- | read at the row's kind. `...` alone spreads the row variable the signature
-- | quantifies at that kind.
-- |
-- | **The row is sharp only under the atoms it implies**: each key it holds
-- | is absent from each row variable it spreads, and the row variables are
-- | apart, which `⊎` asks of what it joins. They are left for the binder of
-- | those variables to carry. A key held twice, a row variable spread twice,
-- | and a spread of a row this version does not take apart into the empty
-- | row, elements, unions, and row variables are reported where the row stands.
rowOf :: Scope -> Surface.Origin -> RowElemKind -> Array RowItem -> Elab Read
rowOf scope origin elementKind items = do
  read <- traverse
    ( case _ of
        Element element -> (\e -> { entry: Just e.entry, read: e.read }) <$> element scope
        Spread _ (Just t) -> { entry: Nothing, read: _ } <$> checkAt scope (XKRow elementKind) t
        Spread o Nothing -> case Map.lookup elementKind scope.anonymous of
          Just v -> pure { entry: Nothing, read: { type: XVar v, kind: XKRow elementKind, unwritten: [], unsupported: [], implied: [] } }
          Nothing -> { entry: Nothing, read: _ } <$> unreadRow o
    )
    items
  let
    entries = Array.mapMaybe _.entry read
    spread = Array.mapMaybe (\r -> if isJust r.entry then Nothing else Just r.read.type) read
    tail = case Array.uncons spread of
      Nothing -> XRowEmpty
      Just { head, tail: rest } -> foldl XRowUnion head rest
    row = foldr XRowExtend tail entries
    parts = partsOf row
    keys = Array.nub parts.keys
    tails = Array.nub parts.tails
    problems =
      map (KeyTwice origin) (Array.nub (twice parts.keys))
        <> map (SpreadTwice origin) (Array.nub (twice parts.tails))
        <> (if Array.null parts.other then [] else [ OutsideSubset origin "a spread of a row that is not made of the empty row, elements over rows, unions, and row variables" ])
    atoms =
      (LacksAtom <$> keys <*> tails)
        <> Array.concat (Array.mapWithIndex (\n a -> map (disjoint a) (Array.drop (n + 1) tails)) tails)
    joinedRead = joined (map _.read read) row (XKRow elementKind)
  pure joinedRead
    { unsupported = joinedRead.unsupported <> problems
    , implied = distinctAtoms (joinedRead.implied <> map { origin, atom: _ } atoms)
    }
  where
  -- a pair of row variables apart, the same condition however they are ordered
  disjoint a b = if a <= b then DisjointAtom a b else DisjointAtom b a
  unreadRow o = pure { type: XRowEmpty, kind: XKRow elementKind, unwritten: [], unsupported: [ AnonymousSpread o ], implied: [] }

  twice :: forall a. Eq a => Array a -> Array a
  twice xs = Array.filter (\x -> Array.length (Array.filter (_ == x) xs) > 1) xs

-- | What a row is made of: the keys it holds, the row variables it spreads,
-- | each as often as it does, and what else stands for a row in it. A
-- | metavariable is a form not read, reported where it stands.
partsOf :: XType -> { keys :: Array RowKey, tails :: Array TyVar, other :: Array XType }
partsOf = case _ of
  XRowEmpty -> none
  XRowExtend entry rest -> let r = partsOf rest in r { keys = Array.cons (xRowEntryKey entry) r.keys }
  XRowUnion l r ->
    let
      left = partsOf l
      right = partsOf r
    in
      { keys: left.keys <> right.keys, tails: left.tails <> right.tails, other: left.other <> right.other }
  XVar v -> none { tails = [ v ] }
  XMeta _ -> none
  other -> none { other = [ other ] }
  where
  none = { keys: [], tails: [], other: [] }

-- | An effect applied to its arguments, read as an application of something at
-- | the arrow of its parameters' kinds into `Effect`: each argument is read at
-- | the kind its parameter is declared at, and an effect applied to more or to
-- | fewer arguments than it has parameters is a kind that does not meet.
effectApplication :: Scope -> EffectApplication -> Elab { arguments :: Array XType, read :: Read }
effectApplication scope application = do
  env <- askEnv
  case Map.lookup application.effect env.session.kinding.effects of
    Nothing -> do
      r <- unreadEffect
      pure { arguments: [], read: r }
    Just params -> do
      read <- traverse (readType scope) application.arguments
      result <- foldM
        ( \kind argument -> do
            rest <- freshKindMeta scope.kindVars Set.empty
            equateKinds (siteOf scope (typeOrigin argument.written)) kind (XKFun argument.kind rest)
            pure rest
        )
        (foldr XKFun XKEffect (map fromCoreKind params))
        (Array.zipWith (\written r -> { written, kind: r.kind }) application.arguments read)
      equateKinds (siteOf scope application.origin) result XKEffect
      pure { arguments: map _.type read, read: joined read XRowEmpty XKEffect }
  where
  unreadEffect = pure
    { type: XRowEmpty
    , kind: XKEffect
    , unwritten: []
    , unsupported: [ OutsideSubset application.origin "an effect the signature does not hold" ]
    , implied: []
    }

-- | A kind with the kind variables given replaced.
instantiateKindVars :: Map KindVar XKind -> XKind -> XKind
instantiateKindVars by = case _ of
  XKVar k | Just kind <- Map.lookup k by -> kind
  XKFun a b -> XKFun (instantiateKindVars by a) (instantiateKindVars by b)
  other -> other

-- | A binder of a `forall`, at the kind written or at a metavariable.
binder :: Scope -> TypeVarBinder -> Elab ReadBinder
binder scope b = case b.kind of
  Just k -> readKind k >>= case _ of
    Right kind -> case Kinding.quantifiable kind of
      Right _ -> pure { var: b.var, kind, unwritten: [], unsupported: [] }
      -- a type variable stands at a kind it may be introduced at, `Effect` and
      -- what produces it being none
      Left _ -> raiseDiagnostic (EquationFailed (AtSource { declaration: scope.declaration, origin: b.origin }) (KindNotQuantifiable kind))
    Left problem -> pure { var: b.var, kind: XKType, unwritten: [], unsupported: [ problem ] }
  Nothing -> do
    kind <- freshKindMeta scope.kindVars quantifiable
    pure { var: b.var, kind, unwritten: [ { origin: b.origin, kind } ], unsupported: [] }

readKind :: Kind -> Elab (Either Unsupported XKind)
readKind k = pure (go k)
  where
  go = case _ of
    KindType _ -> Right XKType
    KindEffect _ -> Right XKEffect
    KindRow _ e -> Right (XKRow e)
    KindArrow _ a b -> XKFun <$> go a <*> go b
    KindVariable _ v -> Right (XKVar v)
    KindInvalid o -> Left (ReportedAlready o)

-- | What a kind a type variable is introduced at must be.
quantifiable :: Set KindRequirement
quantifiable = Set.singleton Quantifiable

-- | The site a node of the type is read at, under the kind variables in scope.
siteOf :: Scope -> Surface.Origin -> Site
siteOf scope origin =
  { context: emptyXContext { kindVars = scope.kindVars }
  , origin: AtSource { declaration: scope.declaration, origin }
  }

nameOf :: TypeVar -> TyVar
nameOf (TypeVar v) = v.name

-- | Where a type variable is first mentioned in a type, reading left to right.
firstMention :: TypeVar -> Type -> Maybe Surface.Origin
firstMention x = case _ of
  TypeVariable o y | x == y -> Just o
  t -> Array.findMap (firstMention x) (typeParts t)

-- | The kind variables the kinds written in a type mention.
typeKindVars :: Type -> Array KindVar
typeKindVars t = written <> Array.concatMap typeKindVars (typeParts t)
  where
  written = case t of
    TypeForall _ binders _ -> Array.concatMap (\b -> maybe [] kindVars b.kind) binders
    TypeKinded _ _ k -> kindVars k
    _ -> []
  kindVars = case _ of
    KindArrow _ a b -> kindVars a <> kindVars b
    KindVariable _ v -> [ v ]
    _ -> []

-- | What a signature may quantify implicitly, as a type mentions it: a type
-- | variable, or `...` alone at a row kind.
data Mention
  = MentionVar TypeVar
  | MentionSpread RowElemKind

derive instance Eq Mention

-- | Each variable and each `...` alone a type mentions, in the order written.
mentions :: Type -> Array Mention
mentions t = case t of
  TypeVariable _ v -> [ MentionVar v ]
  TypeRecord _ items -> Array.concatMap
    ( case _ of
        RecordField _ _ x -> mentions x
        RecordSpread _ x -> spreadMentions RowType x
    )
    items
  TypeVariant _ items -> Array.concatMap
    ( case _ of
        VariantTag _ _ x -> mentions x
        VariantLabel _ _ x -> mentions x
        VariantSpread _ x -> spreadMentions RowType x
    )
    items
  TypeEffectRow _ items -> Array.concatMap
    ( case _ of
        EffectElement application -> Array.concatMap mentions application.arguments
        EffectInstance _ _ application -> Array.concatMap mentions application.arguments
        EffectSpread _ x -> spreadMentions RowEffect x
    )
    items
  _ -> Array.concatMap mentions (typeParts t)
  where
  spreadMentions kind = case _ of
    Just x -> mentions x
    Nothing -> [ MentionSpread kind ]

-- | Every type variable a type writes, bound or mentioned.
writtenTyVars :: Type -> Set TyVar
writtenTyVars t = Set.fromFoldable own <> foldMap writtenTyVars (typeParts t)
  where
  own = case t of
    TypeVariable _ v -> [ nameOf v ]
    TypeForall _ binders _ -> map (nameOf <<< _.var) binders
    _ -> []

-- | The types a type is written with, in the order written.
typeParts :: Type -> Array Type
typeParts = case _ of
  TypeApp _ f x -> [ f, x ]
  TypeOperator _ _ l r -> [ l, r ]
  TypeFunction _ a b row -> [ a, b ] <> Array.fromFoldable row
  TypeForall _ _ body -> [ body ]
  TypeConstrained _ c body -> [ c, body ]
  TypeKinded _ inner _ -> [ inner ]
  TypeTuple _ components -> components
  TypeRecord _ items -> Array.concatMap
    ( case _ of
        RecordField _ _ t -> [ t ]
        RecordSpread _ t -> Array.fromFoldable t
    )
    items
  TypeVariant _ items -> Array.concatMap
    ( case _ of
        VariantTag _ _ t -> [ t ]
        VariantLabel _ _ t -> [ t ]
        VariantSpread _ t -> Array.fromFoldable t
    )
    items
  TypeEffectRow _ items -> Array.concatMap
    ( case _ of
        EffectElement application -> application.arguments
        EffectInstance _ _ application -> application.arguments
        EffectSpread _ t -> Array.fromFoldable t
    )
    items
  TypeSynthesized _ _ t _ -> [ t ]
  _ -> []

-- | The Core scheme of a signature once its kinds are decided: every
-- | metavariable solved, or each place whose kind was left undetermined, once
-- | however many kinds stand there. A metavariable left where no such place
-- | accounts for it is reported where the signature's type stands.
settledScheme :: MetaContext -> Elaborated -> Either (NonEmptyArray Surface.Origin) TypeScheme
settledScheme metas e =
  case NonEmptyArray.fromArray (Array.nubEq (map _.origin (Array.filter undetermined e.unwritten))) of
    Just places -> Left places
    Nothing -> case toCore (substitute metas e.type) of
      Just body -> Right { kindVars: e.kindVars, body }
      Nothing -> Left (NonEmptyArray.singleton e.origin)
  where
  undetermined u = not (Set.isEmpty (kindMetasOf (substituteKind metas u.kind)))

-- | A signature's spine with each synthesized argument on it read as the type
-- | of its dictionary, behind the pure arrow it stands behind, and the
-- | arguments in the order written. A synthesized argument stands only where
-- | quantifiers, constraints, and other synthesized arguments are all that
-- | stands before it.
synthesizedOnSpine :: Type -> { type :: Type, marks :: Array SynthesizedMark }
synthesizedOnSpine t = case t of
  TypeForall o binders body -> let r = synthesizedOnSpine body in r { type = TypeForall o binders r.type }
  TypeConstrained o c body -> let r = synthesizedOnSpine body in r { type = TypeConstrained o c r.type }
  TypeFunction o (TypeSynthesized _ name dictionary synthesizer) rest Nothing ->
    let
      r = synthesizedOnSpine rest
    in
      { type: TypeFunction o dictionary r.type Nothing, marks: Array.cons { name, synthesizer } r.marks }
  _ -> { type: t, marks: [] }

-- | A computation type written as the type it is in Core: its spine, then a
-- | thunk `Unit -{ρ}-> τ`.
computationAsType :: ComputationType -> Type
computationAsType c = foldr prefixed (TypeFunction c.origin (TypeConstructor c.origin unitTy) c.result (Just c.row)) c.prefix
  where
  prefixed prefix rest = case prefix of
    PrefixForall o binders -> TypeForall o binders rest
    PrefixConstraint constraint -> TypeConstrained (typeOrigin constraint) constraint rest
    PrefixSynthesized synthesized -> TypeFunction (typeOrigin synthesized) synthesized rest Nothing

-- | The scheme an interface publishes of a signature, from its Core scheme:
-- | each quantifier and constraint on the spine, each synthesized argument
-- | where its arrow stands, and a computation's thunk as the computation it is.
schemeOf :: Elaborated -> TypeScheme -> Scheme
schemeOf e s = { kindVars: s.kindVars, body: go e.synthesized s.body }
  where
  go marks t = case t, Array.uncons marks, asFunction t of
    Core.TForall a k body, _, _ -> Forall a k (go marks body)
    Core.TConstrained c body, _, _ -> Constrained c (go marks body)
    _, Just { head, tail }, Just f | f.row == Core.TRowEmpty ->
      Synthesized { name: head.name, dictionary: f.argument, synthesizer: head.synthesizer } (go tail f.result)
    _, Nothing, Just f | e.computation -> Computation f.result f.row
    _, _, _ -> Plain t

derive instance Eq Unsupported

derive instance Generic Unsupported _

instance Show Unsupported where
  show = genericShow

derive instance Eq Atom
derive instance Ord Atom
derive instance Generic Atom _

instance Show Atom where
  show = genericShow
