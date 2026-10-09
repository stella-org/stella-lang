-- | A module's type declarations — its data types, newtypes, type synonyms,
-- | foreign types, and effects — elaborated, their kinds inferred together
-- | ([Elaboration](../../../../../docs/technical-references/02-Surface-Language/01-Elaboration.md)).
-- |
-- | **Every head is read before anything a head names.** Each declaration's
-- | head is read first: a data type's or a newtype's parameters and the kind
-- | it writes for itself, a synonym's parameters and the kind of what it stands
-- | for, a foreign type's kind, and an effect's parameters. Then each synonym's
-- | body is read, after the bodies of the synonyms it is written in terms of;
-- | then every constructor's fields and every operation's types. Each is read with every head of the module in scope, so a
-- | declaration may name one written after it, and the kinds the heads leave
-- | unwritten are decided by the same equations, wherever they are met.
-- |
-- | **A synonym is read only after the synonyms it is written in terms of.**
-- | The synonyms of the module are taken in the strongly connected components
-- | of the references their bodies make to one another: one defined in terms of
-- | itself, directly or through others, is reported where it is declared, each
-- | of a cycle once, and none of them is read. A synonym whose body does not
-- | read, or extends a row it is given with what that row would need a
-- | condition for, is not read either, and a use of one is reported where it
-- | stands.
-- |
-- | **A kind is decided by what the declarations say of it, or not at all.**
-- | A kind variable a declaration writes is the declaration's own, and a use of
-- | the type or the synonym instantiates it afresh. A parameter whose kind
-- | nothing decided is outside what this version elaborates: deciding it is
-- | generalizing it, which this version does not do, so its kind must be
-- | written.
-- |
-- | **A field's rows are sharp under no condition on a parameter.** A row
-- | spreading a parameter needs it to lack the keys the row holds beside it,
-- | and a parameter carries no condition, so such a field is refused; a row
-- | variable a `forall` of the field binds carries its conditions there.
-- |
-- | **An effect has no kind scheme.** Its parameters, and an operation's own type
-- | variables, stand at kinds that mention no kind variable, and one whose kind
-- | nothing decided is to be written: nothing could generalize it. An
-- | operation's types need no condition of either, neither carrying one; a
-- | `forall` inside one of them carries its own. An operation takes its
-- | arguments as Core's one argument.
-- |
-- | A constructor's tag is its position among its declaration's constructors.
-- |
-- | **An attribute declaration's parameters are closed types at `Type`**,
-- | read against every type the module declares; one holding a kind nothing
-- | decided is refused where it stands, as nothing could generalize it.
module Stella.Compiler.Elaborate.Surface.Types
  ( TypeDeclarations
  , DataDeclaration
  , TypesRead
  , DataRead
  , Param
  , SynonymRead
  , ForeignTypeRead
  , EffectRead
  , OperationRead
  , SettledTypes
  , readTypes
  , settledTypes
  , AttributeRefused
  , readAttributeDeclaration
  ) where

import Prelude
import Prim hiding (Type)

import Data.Array as Array
import Data.Either (Either(..), either)
import Data.Foldable (foldM, foldr)
import Data.Map as Map
import Data.Maybe (Maybe(..), isNothing, maybe)
import Data.Set (Set)
import Data.Set as Set
import Data.Traversable (for, traverse)
import Data.Tuple (Tuple(..))
import Stella.Compiler.Elaborate.CorePlus.Kind (XKind(..), fromCoreKind, toCoreKind)
import Stella.Compiler.Elaborate.CorePlus.Type (XType(..), toCore)
import Stella.Compiler.Elaborate.Environment.Synonyms (SynonymEntry, SynonymEnv)
import Stella.Compiler.Elaborate.Kernel.Elab (Elab, currentMetas, equateKinds, freshKindMeta)
import Stella.Compiler.Elaborate.Mechanism.Unify (KindRequirement(..), MetaContext, substitute, substituteKind)
import Stella.Compiler.Elaborate.Surface.Group (groups)
import Stella.Compiler.Elaborate.CorePlus.Context (emptyXContext)
import Stella.Compiler.Elaborate.Surface.Type (LocalHead, Scope, SynonymShape, Unsupported(..), elaborateType, readBinder, readKind, readTypeAt, siteOf, typeKindVars, typeParts)
import Stella.Compiler.Interface.Assemble (coreAttribute, coreConstant)
import Stella.Compiler.Surface.Decl (AttributeDeclaration, ConstructorDeclaration, EffectDeclaration, ForeignTypeDeclaration, SynonymDeclaration)
import Stella.Compiler.Surface.Decl (Attribute) as Surface
import Stella.Compiler.Surface.Name (TypeVar(..))
import Stella.Compiler.Surface.Origin (Origin) as Surface
import Stella.Compiler.Surface.Type (Kind(..), OperationSignature, Type(..), TypeOperatorTarget(..), TypeVarBinder, typeOrigin)
import Stella.Compiler.TypedCore (AttributeDecl, DataDecl, EffectDecl)
import Stella.Compiler.Elaborate.Environment.Imported (operationArgument)
import Stella.Compiler.TypedCore.Type (Type) as Core
import Stella.Compiler.TypedCore.Kind (Kind(KFun)) as CoreKind
import Stella.Compiler.TypedCore.Kind (KindScheme)
import Stella.Compiler.TypedCore.Context (bindKindVars, emptyContext)
import Stella.Compiler.TypedCore.Kinding (producesType, quantifiableKind)
import Stella.Compiler.TypedCore.Type (TyBinder)
import Stella.Compiler.TypedCore.Name (EffName(..), Ident(..), KindVar, OpName(..), Qualified(..), TyName(..), TyVar, unqualified)

-- | The type declarations of a module, a newtype written as the data type of
-- | one constructor of one field it is.
type TypeDeclarations =
  { data :: Array DataDeclaration
  , synonyms :: Array SynonymDeclaration
  , foreignTypes :: Array ForeignTypeDeclaration
  , effects :: Array EffectDeclaration
  }

type DataDeclaration =
  { origin :: Surface.Origin
  , attributes :: Array Surface.Attribute
  , name :: Qualified TyName
  , kind :: Maybe Kind
  , params :: Array TypeVarBinder
  , constructors :: Array ConstructorDeclaration
  , isNewtype :: Boolean
  }

-- | A data declaration read, its kinds not yet decided: its kind variables, its
-- | parameters each with where it stands, and its constructors' fields.
type DataRead =
  { declaration :: DataDeclaration
  , kindVars :: Array KindVar
  , params :: Array Param
  , constructors :: Array { origin :: Surface.Origin, name :: Qualified Ident, fields :: Array XType }
  , unsupported :: Array Unsupported
  }

type Param = { var :: TypeVar, kind :: XKind, origin :: Surface.Origin }

-- | A synonym read, its kinds not yet decided: its kind variables, its
-- | parameters, the kind of what it stands for, and its body where it read.
type SynonymRead =
  { declaration :: SynonymDeclaration
  , kindVars :: Array KindVar
  , params :: Array Param
  , result :: XKind
  , body :: Maybe XType
  , unsupported :: Array Unsupported
  }

-- | A foreign type read: its kind scheme, or why it has none.
type ForeignTypeRead = { declaration :: ForeignTypeDeclaration, kind :: Either Unsupported KindScheme }

type TypesRead =
  { data :: Array DataRead
  , synonyms :: Array SynonymRead
  , foreignTypes :: Array ForeignTypeRead
  , effects :: Array EffectRead
  }

-- | An effect read, its kinds not yet decided: its parameters, and each
-- | operation's own type variables, its arguments, and the type it resumes with.
type EffectRead =
  { declaration :: EffectDeclaration
  , params :: Array Param
  , operations :: Array OperationRead
  , unsupported :: Array Unsupported
  }

type OperationRead =
  { origin :: Surface.Origin
  , name :: Qualified Ident
  , binders :: Array Param
  , arguments :: Array XType
  , resumesWith :: XType
  }

-- | Every type declaration given: the heads, then the synonyms' bodies in
-- | dependency order, then the fields and the operations.
readTypes :: SynonymEnv -> TypeDeclarations -> Elab TypesRead
readTypes imported declarations = do
  dataHeads <- traverse (readDataHead imported) declarations.data
  synonymHeads <- traverse (readSynonymHead imported) declarations.synonyms
  effectHeads <- traverse (readEffectHead imported) declarations.effects
  let
    foreignTypes = map (\d -> { declaration: d, kind: foreignKind d }) declarations.foreignTypes
    heads = Map.fromFoldable
      ( map (\h -> Tuple h.declaration.name { kindVars: h.kindVars, body: headKind h.params }) dataHeads
          <> Array.mapMaybe (\f -> map (\k -> Tuple f.declaration.name { kindVars: k.kindVars, body: fromCoreKind k.body }) (hushRight f.kind)) foreignTypes
      )
    -- an effect whose head is refused is no shape a use is read against, so no
    -- use of it decides anything of its parameters
    effects = Map.fromFoldable (map (\h -> Tuple h.declaration.name (if Array.null h.unsupported then Just (map _.kind h.params) else Nothing)) effectHeads)
    inScope declaration kindVars params = (scopeOf imported declaration kindVars)
      { tyVars = Map.fromFoldable (map (\p -> Tuple (nameOf p.var) p.kind) params)
      , localTypes = heads
      , localEffects = effects
      }
  -- each synonym's body, after those it refers to
  synonyms <- foldM (readSynonymGroup inScope synonymHeads) { read: Map.empty, shapes: Map.empty } (synonymOrder declarations.synonyms)
  let shapes = synonyms.shapes
  data' <- for dataHeads \h -> do
    let scope = (inScope (declarationIdent h.declaration.name) h.kindVars h.params) { localSynonyms = shapes }
    constructors <- for h.declaration.constructors \c -> do
      fields <- traverse (readTypeAt scope XKType) c.fields
      -- a parameter carries no condition, so a row needing one of it is refused
      let unheld = map (\i -> UnheldConstraint i.origin i.atom) (Array.concatMap _.implied fields)
      pure { constructor: { origin: c.origin, name: c.name, fields: map _.type fields }, unsupported: Array.concatMap _.unsupported fields <> unheld }
    pure h { constructors = map _.constructor constructors, unsupported = h.unsupported <> Array.concatMap _.unsupported constructors }
  -- an effect whose head is refused is refused whole, and its operations are
  -- not read: what they make of a parameter would only be refused beside it
  effects' <- for effectHeads \h ->
    if not (Array.null h.unsupported) then pure h
    else do
      operations <- for h.declaration.operations \o ->
        -- the effect has no kind scheme to bind a kind variable the operation
        -- writes, on a variable of its own or inside its types; such an
        -- operation is refused before anything is read of it, so no equation of
        -- the kind variable stands in the way of saying so
        if not (Array.null (operationKindVars o.signature)) then
          pure { operation: { origin: o.origin, name: o.name, binders: [], arguments: [], resumesWith: XRowEmpty }, unsupported: [ EffectKindVariable o.origin ] }
        else do
          let declaration = effectIdent h.declaration.name
          binders <- for o.signature.binders (readParam (scopeOf imported declaration []))
          let scope = (inScope declaration [] (h.params <> map _.param binders)) { localSynonyms = shapes }
          arguments <- traverse (readTypeAt scope XKType) o.signature.arguments
          resumesWith <- readTypeAt scope XKType o.signature.resumesWith
          let
            parts = Array.snoc arguments resumesWith
            -- neither the effect's parameters nor the operation's own variables
            -- carry a condition, so a row needing one of them is refused
            unheld = map (\i -> UnheldConstraint i.origin i.atom) (Array.concatMap _.implied parts)
          pure
            { operation: { origin: o.origin, name: o.name, binders: map _.param binders, arguments: map _.type arguments, resumesWith: resumesWith.type }
            , unsupported: Array.concatMap _.unsupported binders <> Array.concatMap _.unsupported parts <> unheld
            }
      pure h { operations = map _.operation operations, unsupported = h.unsupported <> Array.concatMap _.unsupported operations }
  pure
    { data: data'
    , synonyms: Array.mapMaybe (\s -> Map.lookup s.name synonyms.read) declarations.synonyms
    , foreignTypes
    , effects: effects'
    }
  where
  hushRight = case _ of
    Right x -> Just x
    Left _ -> Nothing

-- | The kind variables an operation's signature writes: on its own type
-- | variables, or inside its types.
operationKindVars :: OperationSignature -> Array KindVar
operationKindVars s = Array.concatMap (\b -> maybe [] kindVarsOf b.kind) s.binders <> Array.concatMap typeKindVars (Array.snoc s.arguments s.resumesWith)

-- | An effect's head: its parameters, each at the kind written or at a
-- | metavariable.
readEffectHead :: SynonymEnv -> EffectDeclaration -> Elab EffectRead
readEffectHead imported d = do
  params <- for d.params (readEffectParam (scopeOf imported (effectIdent d.name) []))
  pure { declaration: d, params: map _.param params, operations: [], unsupported: Array.concatMap _.unsupported params }

-- | A parameter of an effect or a type variable of an operation: at the kind
-- | written, which mentions no kind variable, an effect having no kind scheme
-- | to bind one, or at a metavariable.
readEffectParam :: Scope -> TypeVarBinder -> Elab { param :: Param, unsupported :: Array Unsupported }
readEffectParam scope b = case b.kind of
  -- reported here, and standing meanwhile at a kind of its own, so no use of
  -- the parameter is refused for the kind it was not given
  Just k | not (Array.null (kindVarsOf k)) -> do
    kind <- freshKindMeta Set.empty (Set.singleton Quantifiable)
    pure { param: { var: b.var, kind, origin: b.origin }, unsupported: [ EffectKindVariable b.origin ] }
  _ -> readParam scope b

-- | The synonyms of one strongly connected component read: a cycle's each
-- | reported where it is declared and none read, and a synonym on its own read
-- | in terms of those read before it.
readSynonymGroup
  :: (Qualified Ident -> Array KindVar -> Array Param -> Scope)
  -> Array SynonymRead
  -> { read :: Map.Map (Qualified TyName) SynonymRead, shapes :: Map.Map (Qualified TyName) (Maybe SynonymShape) }
  -> { members :: Array SynonymDeclaration, recursive :: Boolean }
  -> Elab { read :: Map.Map (Qualified TyName) SynonymRead, shapes :: Map.Map (Qualified TyName) (Maybe SynonymShape) }
readSynonymGroup inScope heads acc group = case group.recursive, Array.head group.members of
  true, _ -> pure (foldr cyclic acc group.members)
  false, Just d | Just h <- Array.find (\s -> s.declaration.name == d.name) heads -> do
    let scope = (inScope (declarationIdent h.declaration.name) h.kindVars h.params) { localSynonyms = acc.shapes }
    body <- readTypeAt scope h.result d.body
    let
      -- what a row of the body needs of a parameter, a synonym has no way to ask
      extending = if Array.null body.implied then [] else [ OutsideSubset d.origin "a type synonym extending a row it is given" ]
      problems = h.unsupported <> body.unsupported <> extending
      read = h { body = if Array.null problems then Just body.type else Nothing, unsupported = problems }
      shape = if Array.null problems then Just { kindVars: h.kindVars, params: map (\p -> { name: nameOf p.var, kind: p.kind }) h.params, result: h.result, body: body.type } else Nothing
    pure { read: Map.insert d.name read acc.read, shapes: Map.insert d.name shape acc.shapes }
  _, _ -> pure acc
  where
  cyclic d a = case Array.find (\s -> s.declaration.name == d.name) heads of
    Just h -> { read: Map.insert d.name h { unsupported = Array.snoc h.unsupported (SynonymCycle d.origin d.name) } a.read, shapes: Map.insert d.name Nothing a.shapes }
    Nothing -> a

-- | The module's synonyms in dependency order, each component with its
-- | members in the order declared and whether it is a cycle.
synonymOrder :: Array SynonymDeclaration -> Array { members :: Array SynonymDeclaration, recursive :: Boolean }
synonymOrder declarations = map (\g -> { members: Array.mapMaybe (Array.index declarations) g.members, recursive: g.recursive }) (groups (map refers declarations))
  where
  index = Map.fromFoldable (Array.mapWithIndex (\i d -> Tuple d.name i) declarations)
  refers d = Set.fromFoldable (Array.mapMaybe (\n -> Map.lookup n index) (Array.fromFoldable (synonymsNamed d.body)))

-- | The synonyms a type names, directly or through a type operator.
synonymsNamed :: Type -> Set (Qualified TyName)
synonymsNamed t = own <> Array.foldMap synonymsNamed (parts t)
  where
  own = case t of
    TypeSynonym _ name -> Set.singleton name
    TypeOperator _ { target: TargetTypeSynonym name } _ _ -> Set.singleton name
    _ -> Set.empty
  parts = typeParts

-- | A data declaration's head: its parameters, and the kind it writes for
-- | itself equated with the kind they give it.
readDataHead :: SynonymEnv -> DataDeclaration -> Elab DataRead
readDataHead imported d = do
  let
    -- a kind variable is bound by the declaration it is written in, wherever
    -- in it it is written
    kindVars = Array.nub
      ( Array.concatMap (\b -> maybe [] kindVarsOf b.kind) d.params
          <> maybe [] kindVarsOf d.kind
          <> Array.concatMap (Array.concatMap typeKindVars <<< _.fields) d.constructors
      )
    scope = scopeOf imported (declarationIdent d.name) kindVars
  params <- for d.params (readParam scope)
  let
    read =
      { declaration: d
      , kindVars
      , params: map _.param params
      , constructors: []
      , unsupported: Array.concatMap _.unsupported params
      }
  case d.kind of
    Nothing -> pure read
    Just k -> readKind k >>= case _ of
      Right written -> read <$ equateKinds (siteOf scope d.origin) (headKind read.params) written
      Left problem -> pure read { unsupported = Array.snoc read.unsupported problem }

-- | A synonym's head: its parameters, the kind of what it stands for, and the
-- | kind it writes for itself equated with the kind they give it.
readSynonymHead :: SynonymEnv -> SynonymDeclaration -> Elab SynonymRead
readSynonymHead imported d = do
  let
    kindVars = Array.nub
      ( Array.concatMap (\b -> maybe [] kindVarsOf b.kind) d.params
          <> maybe [] kindVarsOf d.kind
          <> typeKindVars d.body
      )
    scope = scopeOf imported (declarationIdent d.name) kindVars
  params <- for d.params (readParam scope)
  result <- freshKindMeta (Set.fromFoldable kindVars) Set.empty
  let
    read =
      { declaration: d
      , kindVars
      , params: map _.param params
      , result
      , body: Nothing
      , unsupported: Array.concatMap _.unsupported params
      }
  case d.kind of
    Nothing -> pure read
    Just k -> readKind k >>= case _ of
      Right written -> read <$ equateKinds (siteOf scope d.origin) (foldr (\p kind -> XKFun p.kind kind) result read.params) written
      Left problem -> pure read { unsupported = Array.snoc read.unsupported problem }

readParam :: Scope -> TypeVarBinder -> Elab { param :: Param, unsupported :: Array Unsupported }
readParam scope b = do
  read <- readBinder scope b
  pure { param: { var: read.var, kind: read.kind, origin: b.origin }, unsupported: read.unsupported }

-- | A foreign type's kind, as written: a kind scheme over the kind variables
-- | it writes. A type constructor's kind is held to what any is: its domains
-- | are kinds a type variable may stand at, and it produces `Type`.
foreignKind :: ForeignTypeDeclaration -> Either Unsupported KindScheme
foreignKind d = case readKindNow d.kind of
  Left problem -> Left problem
  Right kind -> case toCoreKind kind of
    Just body -> case quantifiableKind (bindKindVars emptyContext kindVars) body, producesType body of
      Right _, Right _ -> Right { kindVars, body }
      _, _ -> Left (ForeignKindInvalid d.origin kind)
    Nothing -> Left (ReportedAlready d.origin)
  where
  kindVars = Array.nub (kindVarsOf d.kind)
  readKindNow = case _ of
    KindType _ -> Right XKType
    KindEffect _ -> Right XKEffect
    KindRow _ e -> Right (XKRow e)
    KindArrow _ a b -> XKFun <$> readKindNow a <*> readKindNow b
    KindVariable _ v -> Right (XKVar v)
    KindInvalid o -> Left (ReportedAlready o)

-- | The kind a head is at: its parameters' kinds to `Type`.
headKind :: forall r. Array { kind :: XKind | r } -> XKind
headKind = foldr (\p k -> XKFun p.kind k) XKType

-- | The module's type declarations once every kind of them is decided: the
-- | Core declarations of its data types and its effects, the synonyms as an
-- | interface holds them, and the foreign types' kind schemes; or what keeps
-- | them from being so.
type SettledTypes =
  { data :: Array { origin :: Surface.Origin, decl :: DataDecl }
  , synonyms :: Array { origin :: Surface.Origin, attributes :: Array Surface.Attribute, name :: Qualified TyName, entry :: SynonymEntry }
  , foreignTypes :: Array { origin :: Surface.Origin, attributes :: Array Surface.Attribute, name :: Qualified TyName, kind :: KindScheme }
  , effects :: Array { origin :: Surface.Origin, name :: Qualified EffName, decl :: EffectDecl, arguments :: Array (Array Core.Type) }
  , unsupported :: Array Unsupported
  }

settledTypes :: MetaContext -> TypesRead -> SettledTypes
settledTypes metas r =
  { data: Array.mapMaybe (\{ read, settled } -> map { origin: read.declaration.origin, decl: _ } (hush settled)) data'
  , synonyms: Array.mapMaybe (\{ read, settled } -> map (\entry -> { origin: read.declaration.origin, attributes: read.declaration.attributes, name: read.declaration.name, entry }) (hush settled)) synonyms
  , foreignTypes: Array.mapMaybe (\f -> map (\kind -> { origin: f.declaration.origin, attributes: f.declaration.attributes, name: f.declaration.name, kind }) (hush f.kind)) r.foreignTypes
  , effects: Array.mapMaybe (\{ read, settled } -> map (\s -> { origin: read.declaration.origin, name: read.declaration.name, decl: s.decl, arguments: s.arguments }) (hush settled)) effects
  , unsupported: Array.concatMap (errorsOf <<< _.settled) data'
      <> Array.concatMap (errorsOf <<< _.settled) synonyms
      <> Array.concatMap (errorsOf <<< _.settled) effects
      <> Array.concatMap
        ( \f -> case f.kind of
            Left problem -> [ problem ]
            Right _ -> []
        )
        r.foreignTypes
  }
  where
  data' = map (\read -> { read, settled: settledData metas read }) r.data
  synonyms = map (\read -> { read, settled: settledSynonym metas read }) r.synonyms
  effects = map (\read -> { read, settled: settledEffect metas read }) r.effects

  hush :: forall e a. Either e a -> Maybe a
  hush = case _ of
    Right x -> Just x
    Left _ -> Nothing

  errorsOf :: forall a. Either (Array Unsupported) a -> Array Unsupported
  errorsOf = case _ of
    Left problems -> problems
    Right _ -> []

-- | A data declaration once every kind of it is decided: the Core declaration,
-- | or what keeps it from being one.
settledData :: MetaContext -> DataRead -> Either (Array Unsupported) DataDecl
settledData metas r
  | not (Array.null r.unsupported) = Left r.unsupported
  | otherwise = do
      params <- settledParams metas r.params
      constructors <- for (Array.mapWithIndex Tuple r.constructors) \(Tuple tag c) ->
        case traverse (toCore <<< substitute metas) c.fields of
          Just fields -> Right { name: local c.name, tag, fields }
          Nothing -> Left [ OutsideSubset c.origin "a constructor whose fields' kinds are decided only by generalizing them" ]
      attributes <- case traverse coreAttribute r.declaration.attributes of
        Right as -> Right as
        Left o -> Left [ ReportedAlready o ]
      pure
        { name: local r.declaration.name
        , kindVars: r.kindVars
        , params
        , constructors
        , isNewtype: r.declaration.isNewtype
        , attributes
        }

-- | A synonym once every kind of it is decided: what an interface holds of it,
-- | or what keeps it from being that.
settledSynonym :: MetaContext -> SynonymRead -> Either (Array Unsupported) SynonymEntry
settledSynonym metas r
  | not (Array.null r.unsupported) = Left r.unsupported
  | otherwise = do
      params <- settledParams metas r.params
      result <- case toCoreKind (substituteKind metas r.result) of
        Just k -> Right k
        Nothing -> Left [ OutsideSubset r.declaration.origin "a type synonym whose kind is decided only by generalizing it; its kind must be written" ]
      body <- case r.body >>= (toCore <<< substitute metas) of
        Just b -> Right b
        Nothing -> Left [ OutsideSubset r.declaration.origin "a type synonym whose body's kinds are decided only by generalizing them" ]
      pure { kind: { kindVars: r.kindVars, body: foldr (\p k -> CoreKind.KFun p.kind k) result params }, params, body }

-- | An effect once every kind of it is decided: the Core declaration, each
-- | operation's arguments as written beside it, or what keeps it from being
-- | one. An operation takes its arguments as Core's one argument: none is
-- | `Prim.Unit`, one is itself, and several are a record of them by position.
settledEffect :: MetaContext -> EffectRead -> Either (Array Unsupported) { decl :: EffectDecl, arguments :: Array (Array Core.Type) }
settledEffect metas r
  | not (Array.null r.unsupported) = Left r.unsupported
  | otherwise =
      do
        params <- effectParams r.params
        operations <- for r.operations \o -> do
          tyBinders <- effectParams o.binders
          types <- case traverse (toCore <<< substitute metas) (Array.snoc o.arguments o.resumesWith) of
            Just ts -> Right ts
            Nothing -> Left [ OutsideSubset o.origin "an operation whose types' kinds are decided only by generalizing them" ]
          let arguments = Array.take (Array.length o.arguments) types
          resumesWith <- case Array.last types of
            Just t -> Right t
            Nothing -> Left [ ReportedAlready o.origin ]
          pure { op: { name: opName o.name, tyBinders, argument: operationArgument arguments, resumesWith }, arguments }
        attributes <- case traverse coreAttribute r.declaration.attributes of
          Right as -> Right as
          Left o -> Left [ ReportedAlready o ]
        pure
          { decl: { name: local r.declaration.name, params, operations: map _.op operations, attributes }
          , arguments: map _.arguments operations
          }
      where
      -- an effect has no kind scheme, so a kind nothing decided is no limit of
      -- this version but a kind to be written
      effectParams = settledParamsReporting metas EffectKindUndetermined
      opName (Qualified _ (Ident n)) = OpName n

-- | Every parameter's kind decided, or each parameter whose kind is not
-- | reported where it stands.
settledParams :: MetaContext -> Array Param -> Either (Array Unsupported) (Array TyBinder)
settledParams metas = settledParamsReporting metas (\o -> OutsideSubset o "a type parameter whose kind is decided only by generalizing it; its kind must be written")

-- | `settledParams`, each parameter whose kind is undetermined reported as the
-- | function given says.
settledParamsReporting :: MetaContext -> (Surface.Origin -> Unsupported) -> Array Param -> Either (Array Unsupported) (Array TyBinder)
settledParamsReporting metas undeterminedAt params = case traverse decided params of
  Just ps -> Right ps
  Nothing -> Left (Array.mapMaybe undetermined params)
  where
  decided p = { name: nameOf p.var, kind: _ } <$> toCoreKind (substituteKind metas p.kind)
  undetermined p = case decided p of
    Just _ -> Nothing
    Nothing -> Just (undeterminedAt p.origin)

-- | What a declaration's types are read under: its kind variables, the
-- | synonyms the imports declare, and the declaration named as a value is, for
-- | locating what is reported of it.
scopeOf :: SynonymEnv -> Qualified Ident -> Array KindVar -> Scope
scopeOf imported declaration kindVars =
  { declaration
  , kindVars: Set.fromFoldable kindVars
  , tyVars: Map.empty
  , localTypes: Map.empty :: Map.Map (Qualified TyName) LocalHead
  , anonymous: Map.empty
  , synonyms: imported
  , localSynonyms: Map.empty
  , localEffects: Map.empty
  }

declarationIdent :: Qualified TyName -> Qualified Ident
declarationIdent (Qualified m (TyName n)) = Qualified m (Ident n)

effectIdent :: Qualified EffName -> Qualified Ident
effectIdent (Qualified m (EffName n)) = Qualified m (Ident n)

kindVarsOf :: Kind -> Array KindVar
kindVarsOf = case _ of
  KindArrow _ a b -> kindVarsOf a <> kindVarsOf b
  KindVariable _ v -> [ v ]
  _ -> []

local :: forall a. Qualified a -> a
local (Qualified _ a) = a

nameOf :: TypeVar -> TyVar
nameOf (TypeVar v) = v.name

-- | An attribute declaration: its parameters' types, closed and read at
-- | `Type`, and each keyword parameter's default as Core holds a constant; or
-- | what keeps it from being one: a form not read, or the place of each type
-- | holding a kind nothing decided, which nothing could generalize.
readAttributeDeclaration :: SynonymEnv -> AttributeDeclaration -> Elab (Either AttributeRefused AttributeDecl)
readAttributeDeclaration synonyms d = do
  positional <- for d.positional \t -> { written: t, read: _ } <$> elaborateType synonyms d.name emptyXContext t
  keyword <- for d.keyword \k -> { parameter: k, written: k.type, read: _ } <$> elaborateType synonyms d.name emptyXContext k.type
  metas <- currentMetas
  let
    unsupported = Array.concatMap (_.unsupported <<< _.read) positional <> Array.concatMap (_.unsupported <<< _.read) keyword
      <> Array.mapMaybe (\k -> either (Just <<< ReportedAlready) (const Nothing) (traverse coreConstant k.parameter.default)) keyword
    closed r = toCore (substitute metas r.type)
    undetermined = map (typeOrigin <<< _.written) (Array.filter (isNothing <<< closed <<< _.read) positional) <> map (typeOrigin <<< _.written) (Array.filter (isNothing <<< closed <<< _.read) keyword)
  pure case traverse (closed <<< _.read) positional, for keyword (\k -> { label: k.parameter.label, type: _, default: _ } <$> closed k.read <*> either (const Nothing) Just (traverse coreConstant k.parameter.default)) of
    Just positional', Just keyword' | Array.null unsupported -> Right { name: unqualified d.name, positional: positional', keyword: keyword' }
    -- a type not read holds nothing to decide
    _, _ -> Left { unsupported, undetermined: if Array.null unsupported then undetermined else [] }

-- | What keeps an attribute declaration from being one.
type AttributeRefused = { unsupported :: Array Unsupported, undetermined :: Array Surface.Origin }
