-- | A module's type declarations — its data types, newtypes, type synonyms,
-- | foreign types, and effects — elaborated, their kinds inferred together
-- | ([Elaboration](../../../../../docs/technical-references/02-Surface-Language/01-Elaboration.md)).
-- |
-- | **The data types, newtypes, and synonyms are read in groups**, the strongly
-- | connected components of the type constructors and synonyms they name, in
-- | dependency order, after the effects' heads and the foreign types' kinds.
-- | Each group's heads are read first — a data type's or a newtype's parameters
-- | and the kind it writes for itself, a synonym's parameters and the kind of
-- | what it stands for — then its synonyms' bodies, after those it is written
-- | in terms of, then its fields; every operation's types are read once every
-- | group is. A member of a group is referred to inside it at the kinds its
-- | head is being given, a kind variable it writes instantiated at each use as
-- | ever.
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
-- | **A kind a data type's head or a synonym's kind leaves undecided is
-- | generalized** once its group is read, into a kind variable of the
-- | declaration's own besides those it writes, and a use of the type or the
-- | synonym instantiates both afresh; a reference inside the group to a data
-- | type gains the kind arguments of the member it names. A kind only the
-- | fields hold is reported where the constructor holding it stands, and one
-- | only a synonym's body holds, or one its kind holds that must produce
-- | `Type`, where the synonym is declared, a later use of that synonym
-- | reported as one that cannot be expanded.
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
import Data.Foldable (foldM, foldl, foldr)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, isNothing, maybe)
import Data.Set (Set)
import Data.Set as Set
import Data.Traversable (for, traverse)
import Data.Tuple (Tuple(..))
import Stella.Compiler.Elaborate.CorePlus.Kind (KindMetaVar, XKind(..), fromCoreKind, kindMetasOf, toCoreKind)
import Stella.Compiler.Elaborate.CorePlus.Type (XType(..), kindMetasOfType, toCore)
import Stella.Compiler.Elaborate.Environment.Synonyms (SynonymEntry, SynonymEnv)
import Stella.Compiler.Elaborate.Kernel.Elab (Elab, Outcome(..), SessionEnv, SolverState, atLevel, currentMetas, equateKinds, freshKindMeta)
import Stella.Compiler.Elaborate.Driver.Attempt (runAttempt)
import Stella.Compiler.Elaborate.Vocabulary.Diagnostic (Defect(..))
import Stella.Compiler.Elaborate.Kernel.Builder.Common (mapChildren)
import Stella.Compiler.Elaborate.Mechanism.Unify (KindMetaBinding(..), KindRequirement(..), MetaBinding(..), MetaContext, substitute, substituteKind)
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
import Stella.Compiler.TypedCore.Name (EffName(..), Ident(..), KindVar(..), OpName(..), Qualified(..), TyName(..), TyVar, unqualified)

-- | The type declarations of a module, a newtype written as the data type of
-- | one constructor of one field it is, and the order its data types,
-- | newtypes, and synonyms are declared in.
type TypeDeclarations =
  { order :: Array (Qualified TyName)
  , data :: Array DataDeclaration
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

-- | What reading the type declarations gave, the data types and the synonyms
-- | in the order declared.
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

-- | Every type declaration given, each part as an attempt of its own: the
-- | effects' heads, then the data types, newtypes, and synonyms group by group
-- | in dependency order — each group's heads, its synonyms' bodies, and its
-- | fields, its kinds generalized before a later group uses it — and then the
-- | operations.
-- |
-- | **What a group settles is retired from `Ψ`**: each kind it generalizes,
-- | and each it reports a synonym for, nothing a later group reads naming one;
-- | `Ψ` naming one afterwards is the host's defect.
readTypes :: SessionEnv -> SynonymEnv -> TypeDeclarations -> SolverState -> Tuple (Outcome TypesRead) SolverState
readTypes session imported declarations s0 = case runAttempt session (traverse (readEffectHead imported) declarations.effects) s0 of
  Tuple (Done effectHeads) s1 ->
    let
      foreignTypes = map (\d -> { declaration: d, kind: foreignKind d }) declarations.foreignTypes
      fixed = Map.fromFoldable (Array.mapMaybe (\f -> map (\k -> Tuple f.declaration.name { kindVars: k.kindVars, body: fromCoreKind k.body }) (hushRight f.kind)) foreignTypes)
      -- an effect whose head is refused is no shape a use is read against, so
      -- no use of it decides anything of its parameters
      effects = Map.fromFoldable (map (\h -> Tuple h.declaration.name (if Array.null h.unsupported then Just (map _.kind h.params) else Nothing)) effectHeads)
      inScope acc declaration kindVars params = (scopeOf imported declaration kindVars)
        { tyVars = Map.fromFoldable (map (\p -> Tuple (nameOf p.var) p.kind) params)
        , localTypes = acc.heads
        , localEffects = effects
        , localSynonyms = acc.shapes
        }
      start = { heads: fixed, shapes: Map.empty, data: Map.empty, synonyms: Map.empty }
    in
      case readGroups session imported inScope (typeGroups declarations) start s1 of
        Tuple (Left stopped) s2 -> Tuple stopped s2
        Tuple (Right read) s2 -> case runAttempt session (readOperations imported (inScope read) effectHeads) s2 of
          Tuple (Done effects') s3 ->
            Tuple
              ( Done
                  { data: Array.mapMaybe (\d -> Map.lookup d.name read.data) declarations.data
                  , synonyms: Array.mapMaybe (\s -> Map.lookup s.name read.synonyms) declarations.synonyms
                  , foreignTypes
                  , effects: effects'
                  }
              )
              s3
          Tuple stopped s3 -> Tuple (abandoned stopped) s3
  Tuple stopped s1 -> Tuple (abandoned stopped) s1
  where
  hushRight = case _ of
    Right x -> Just x
    Left _ -> Nothing

-- | An outcome that is no result, as one of another type.
abandoned :: forall a b. Outcome a -> Outcome b
abandoned = case _ of
  Postponed cause -> Postponed cause
  Failed d -> Failed d
  Broke d -> Broke d
  -- unreachable: what is abandoned is no result
  Done _ -> Broke ResolutionPostponed

-- | What reading the groups so far gave: the head each type constructor of the
-- | module is read at, the synonyms' shapes, and each declaration read.
type GroupsRead =
  { heads :: Map.Map (Qualified TyName) LocalHead
  , shapes :: Map.Map (Qualified TyName) (Maybe SynonymShape)
  , data :: Map.Map (Qualified TyName) DataRead
  , synonyms :: Map.Map (Qualified TyName) SynonymRead
  }

type InScope = GroupsRead -> Qualified Ident -> Array KindVar -> Array Param -> Scope

-- | The groups given read, each as an attempt at level 1, and generalized
-- | before the next is read.
readGroups :: SessionEnv -> SynonymEnv -> InScope -> Array { data :: Array DataDeclaration, synonyms :: Array SynonymDeclaration } -> GroupsRead -> SolverState -> Tuple (Either (Outcome TypesRead) GroupsRead) SolverState
readGroups session imported inScope groups' acc s = case Array.uncons groups' of
  Nothing -> Tuple (Right acc) s
  Just { head: group, tail } -> case runAttempt session (atLevel 1 (readGroup imported inScope acc group)) s of
    Tuple (Done read) s' ->
      let
        metas = s'.tentative.metas
        generalized = generalizeKinds metas read.data read.synonyms
      in
        case retire metas generalized.settled of
          Nothing -> Tuple (Left (Broke RetiredMetavariableHeld)) s'
          Just released ->
            readGroups session imported inScope tail
              { heads: foldl (\m g -> Map.insert g.read.declaration.name g.head m) acc.heads generalized.data
              , shapes: foldl (\m g -> Map.insert g.read.declaration.name g.shape m) acc.shapes generalized.synonyms
              , data: foldl (\m g -> Map.insert g.read.declaration.name g.read m) acc.data generalized.data
              , synonyms: foldl (\m g -> Map.insert g.read.declaration.name g.read m) acc.synonyms generalized.synonyms
              }
              (s' { tentative { metas = released } })
    Tuple stopped s' -> Tuple (Left (abandoned stopped)) s'

-- | `Ψ` with the kind metavariables given retired, and every one whose solution
-- | names one of them; or nothing where what is left still names one.
retire :: MetaContext -> Set KindMetaVar -> Maybe MetaContext
retire metas generalized =
  if dangling then Nothing else Just released
  where
  retired = closure generalized
  closure acc =
    let
      next = Set.union acc
        ( Set.fromFoldable
            ( Array.mapMaybe
                ( \(Tuple k binding) -> case binding of
                    KindAssigned solution | not (Set.isEmpty (Set.intersection acc (kindMetasOf solution))) -> Just k
                    _ -> Nothing
                )
                (Map.toUnfoldable metas.kindBindings :: Array (Tuple KindMetaVar KindMetaBinding))
            )
        )
    in
      if next == acc then acc else closure next
  released = metas { kindBindings = Map.filterKeys (not <<< flip Set.member retired) metas.kindBindings }
  names kinds = not (Set.isEmpty (Set.intersection retired kinds))
  dangling = Array.any
    ( case _ of
        Unsolved info -> names (kindMetasOf info.kind)
        Assigned solution -> names (kindMetasOfType solution)
    )
    (Array.fromFoldable (Map.values released.bindings))

-- | Every operation of the effects whose heads were read, against the types
-- | every group gave.
readOperations :: SynonymEnv -> (Qualified Ident -> Array KindVar -> Array Param -> Scope) -> Array EffectRead -> Elab (Array EffectRead)
readOperations imported inScope effectHeads =
  -- an effect whose head is refused is refused whole, and its operations are
  -- not read: what they make of a parameter would only be refused beside it
  for effectHeads \h ->
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
          let scope = inScope declaration [] (h.params <> map _.param binders)
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

-- | The data types, newtypes, and synonyms in the strongly connected components
-- | of the type constructors and synonyms their bodies and fields name, in a
-- | stable dependency order by the order they are declared in, each with its
-- | members in that order.
typeGroups :: TypeDeclarations -> Array { data :: Array DataDeclaration, synonyms :: Array SynonymDeclaration }
typeGroups declarations = map members (groups (map refers nodes))
  where
  position = Map.fromFoldable (Array.mapWithIndex (\i n -> Tuple n i) declarations.order)
  nameOfNode = either _.name _.name
  nodes = Array.sortWith (\n -> Map.lookup (nameOfNode n) position) (map Left declarations.data <> map Right declarations.synonyms)
  index = Map.fromFoldable (Array.mapWithIndex (\i n -> Tuple (nameOfNode n) i) nodes)
  named = case _ of
    Left d -> Array.foldMap (Array.foldMap typesNamed <<< _.fields) d.constructors
    Right s -> typesNamed s.body
  refers n = Set.fromFoldable (Array.mapMaybe (\name -> Map.lookup name index) (Array.fromFoldable (named n)))
  members g =
    let
      ns = Array.mapMaybe (Array.index nodes) g.members
    in
      { data: Array.mapMaybe (either Just (const Nothing)) ns, synonyms: Array.mapMaybe (either (const Nothing) Just) ns }

-- | One group read: its heads, its synonyms' bodies after those of the group
-- | they are written in terms of, and its fields, every reference to a member
-- | at the kinds being inferred.
readGroup
  :: SynonymEnv
  -> InScope
  -> GroupsRead
  -> { data :: Array DataDeclaration, synonyms :: Array SynonymDeclaration }
  -> Elab { data :: Array DataRead, synonyms :: Array SynonymRead }
readGroup imported inScope acc group = do
  dataHeads <- traverse (readDataHead imported) group.data
  synonymHeads <- traverse (readSynonymHead imported) group.synonyms
  let
    inGroup = acc { heads = foldl (\m h -> Map.insert h.declaration.name { kindVars: h.kindVars, body: headKind h.params } m) acc.heads dataHeads }
    scoped = inScope inGroup
  -- each synonym's body, after those of the group it is written in terms of;
  -- a cycle of synonyms is one whatever else the group holds
  synonyms <- foldM (readSynonymGroup scoped synonymHeads) { read: Map.empty, shapes: acc.shapes } (synonymOrder group.synonyms)
  data' <- for dataHeads \h -> do
    let scope = (scoped (declarationIdent h.declaration.name) h.kindVars h.params) { localSynonyms = synonyms.shapes }
    constructors <- for h.declaration.constructors \c -> do
      fields <- traverse (readTypeAt scope XKType) c.fields
      -- a parameter carries no condition, so a row needing one of it is refused
      let unheld = map (\i -> UnheldConstraint i.origin i.atom) (Array.concatMap _.implied fields)
      pure { constructor: { origin: c.origin, name: c.name, fields: map _.type fields }, unsupported: Array.concatMap _.unsupported fields <> unheld }
    pure h { constructors = map _.constructor constructors, unsupported = h.unsupported <> Array.concatMap _.unsupported constructors }
  pure { data: data', synonyms: Array.mapMaybe (\s -> Map.lookup s.name synonyms.read) group.synonyms }

-- | A group's data types and synonyms, the kind metavariables of the group
-- | each one's kind leaves unsolved made kind variables of its own, named apart
-- | from those it writes in the order they first appear, and each reference
-- | inside the group to a data type given the member's kind arguments; with the
-- | head or the shape a later group reads each at, its kind variables
-- | instantiated at each use, and every kind metavariable the group settles.
-- | A synonym holding a kind no kind variable of it stands for is reported,
-- | and has no shape.
generalizeKinds
  :: MetaContext
  -> Array DataRead
  -> Array SynonymRead
  -> { data :: Array { read :: DataRead, head :: LocalHead }, synonyms :: Array { read :: SynonymRead, shape :: Maybe SynonymShape }, settled :: Set KindMetaVar }
generalizeKinds metas data' synonyms' =
  { data: map _.member data''
  , synonyms: map _.member synonyms''
  , settled: Set.fromFoldable (Array.concatMap _.settles data'' <> Array.concatMap _.settles synonyms'')
  }
  where
  open k = case Map.lookup k metas.kindBindings of
    Just (KindUnsolved info) -> info.level >= 1
    _ -> false
  candidatesOf kind = Array.nub (Array.filter open (kindMetaOrder (substituteKind metas kind)))
  candidates = Map.fromFoldable
    ( map (\d -> Tuple d.declaration.name (candidatesOf (headKind d.params))) data'
        <> map (\s -> Tuple s.declaration.name (candidatesOf (synonymKind s))) synonyms'
    )
  candidatesFor name = fromMaybe [] (Map.lookup name candidates)

  -- a member's candidates made the kind variables it gains, and a type it
  -- holds rewritten in them, a data type referred to given its kind arguments
  -- written in this member's
  generalizing name written =
    let
      own = candidatesFor name
      fresh = kindNames (Set.fromFoldable written) (Array.length own)
      ctx = metas { kindBindings = foldl (\b (Tuple m n) -> Map.insert m (KindAssigned (XKVar n)) b) metas.kindBindings (Array.zip own fresh) }
      kind = substituteKind ctx
      extra callee = map (kind <<< XKMeta) (candidatesFor callee)
    in
      { own, kindVars: written <> fresh, kind, type: withKindArguments kind extra <<< substitute ctx }

  data'' = map generalizedData data'
  synonyms'' = map generalizedSynonym synonyms'

  generalizedData d =
    let
      g = generalizing d.declaration.name d.kindVars
      -- a candidate that must produce `Type` is no kind variable, and is
      -- reported where a constructor's fields hold it
      producing = Array.filter (producesTypeIn metas) g.own
      holding k = Array.find (\c -> Array.any (Set.member k <<< kindMetasOfType <<< substitute metas) c.fields) d.constructors
      undecided = Array.nubEq (map (\k -> maybe d.declaration.origin _.origin (holding k)) producing)
    in
      { member:
          { read: d
              { kindVars = g.kindVars
              , params = map (\p -> p { kind = g.kind p.kind }) d.params
              , constructors = map (\c -> c { fields = map g.type c.fields }) d.constructors
              , unsupported = d.unsupported <> map KindNotDecided undecided
              }
          , head: { kindVars: g.kindVars, body: g.kind (headKind d.params) }
          }
      , settles: g.own
      }

  generalizedSynonym s =
    let
      g = generalizing s.declaration.name s.kindVars
      params = map (\p -> p { kind = g.kind p.kind }) s.params
      result = g.kind s.result
      body = map g.type s.body
      -- a kind only the body holds, and a candidate that must produce `Type`,
      -- are no kind variables of the synonym
      bodyOnly = maybe [] (Array.filter open <<< Set.toUnfoldable <<< kindMetasOfType) body
      producing = Array.filter (producesTypeIn metas) g.own
      undecided = if Array.null bodyOnly && Array.null producing then [] else [ SynonymKindNotDecided s.declaration.origin s.declaration.name ]
      read = s { kindVars = g.kindVars, params = params, result = result, body = body, unsupported = s.unsupported <> undecided }
    in
      { member:
          { read
          , shape: case body of
              Just b | Array.null read.unsupported -> Just { kindVars: g.kindVars, params: map (\p -> { name: nameOf p.var, kind: p.kind }) params, result, body: b }
              _ -> Nothing
          }
      , settles: g.own <> bodyOnly
      }

-- | The kind a synonym is at: its parameters' kinds to the kind of what it
-- | stands for.
synonymKind :: SynonymRead -> XKind
synonymKind s = foldr (\p k -> XKFun p.kind k) s.result s.params

-- | Whether a kind metavariable must produce `Type`, which no kind variable is.
producesTypeIn :: MetaContext -> KindMetaVar -> Boolean
producesTypeIn metas k = case Map.lookup k metas.kindBindings of
  Just (KindUnsolved info) -> Set.member ProducesType info.requirements
  _ -> false

-- | A type with the kind given put through every kind it writes, and each type
-- | constructor given the kind arguments the function gives it after its own.
withKindArguments :: (XKind -> XKind) -> (Qualified TyName -> Array XKind) -> XType -> XType
withKindArguments kind extra = go
  where
  go = case _ of
    XCon name kinds -> XCon name (map kind kinds <> extra name)
    XForall b k body -> XForall b (kind k) (go body)
    other -> mapChildren go other

-- | The kind metavariables a kind holds, left to right.
kindMetaOrder :: XKind -> Array KindMetaVar
kindMetaOrder = case _ of
  XKMeta k -> [ k ]
  XKFun a b -> kindMetaOrder a <> kindMetaOrder b
  _ -> []

-- | As many kind variables as given, `k`, then `k1`, and so on, named apart
-- | from those given.
kindNames :: Set KindVar -> Int -> Array KindVar
kindNames taken count = go 0 []
  where
  go i acc
    | Array.length acc >= count = acc
    | Set.member (name i) taken = go (i + 1) acc
    | otherwise = go (i + 1) (Array.snoc acc (name i))
  name i = KindVar (if i == 0 then "k" else "k" <> show i)

-- | The type constructors and synonyms a type names, directly or through a
-- | type operator.
typesNamed :: Type -> Set (Qualified TyName)
typesNamed t = own <> Array.foldMap typesNamed (typeParts t)
  where
  own = case t of
    TypeConstructor _ name -> Set.singleton name
    TypeSynonym _ name -> Set.singleton name
    TypeOperator _ { target: TargetTypeConstructor name } _ _ -> Set.singleton name
    TypeOperator _ { target: TargetTypeSynonym name } _ _ -> Set.singleton name
    _ -> Set.empty

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
    metas <- currentMetas
    let
      -- what a row of the body needs of a parameter, a synonym has no way to ask
      extending = if Array.null body.implied then [] else [ OutsideSubset d.origin "a type synonym extending a row it is given" ]
      problems = h.unsupported <> body.unsupported <> extending
      read = h { body = if Array.null problems then Just body.type else Nothing, unsupported = problems }
      -- the kind variables it writes stand in the shape where a solution put
      -- them, so a use instantiating them reaches each
      shape = if Array.null problems then Just { kindVars: h.kindVars, params: map (\p -> { name: nameOf p.var, kind: substituteKind metas p.kind }) h.params, result: substituteKind metas h.result, body: substitute metas body.type } else Nothing
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
  { data: Array.mapMaybe (hush <<< _.settled) data'
  , synonyms: Array.mapMaybe (hush <<< _.settled) synonyms
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
  data' = map (\read -> { settled: map { origin: read.declaration.origin, decl: _ } (settledData metas read) }) r.data
  synonyms = map (\read -> { settled: map (\e -> { origin: read.declaration.origin, attributes: read.declaration.attributes, name: read.declaration.name, entry: e }) (settledSynonym metas read) }) r.synonyms
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
          -- a kind only the fields hold is one no generalization of the head
          -- reaches
          Nothing -> Left [ KindNotDecided c.origin ]
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
-- | one. An operation is written with at least one argument, and takes them as
-- | Core's one argument: one is itself, and several are a record of them by
-- | position.
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
  , annotation: Nothing
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
