-- | The second stage of resolution: what a module's header and its top-level
-- | declarations put in scope, and what the module exports.
-- |
-- | **Names are resolved against export tables, and entities are not looked
-- | at.** An import brings the names the imported module's interface
-- | publishes, each as the entity it is another name for and the way it came;
-- | a top-level declaration brings its own name. Nothing here reads a scheme or
-- | a constructor's fields, which is what lets a module's scope be built before
-- | any of its right-hand sides is resolved.
-- |
-- | **A name may stand for several entities**, two imports bringing one name
-- | for different ones. That is not an error until something refers to the
-- | name, so a scope keeps every candidate and a reference decides. Two imports
-- | bringing one entity bring one candidate.
-- |
-- | `Prim` is a fixed dependency of every module. Where the header writes no
-- | `import Prim …`, its exports are opened unqualified as `import Prim` would
-- | open them; where it writes one, that import opens them instead. Either way
-- | `Prim` is not among the module's imports.
-- |
-- | Every problem found is reported, with where it stands, and resolution goes
-- | on past it.
module Stella.Compiler.Resolve.Scope
  ( Names
  , Candidates
  , emptyNames
  , Scope
  , ScopedModule
  , Namespace(..)
  , ScopeError(..)
  , ScopeReason(..)
  , ScopeWarning(..)
  , printScopeReason
  , printScopeWarning
  , resolveScope
  , elaborationOnlyEntries
  , elaborationOnlyEntry
  , writtenBare
  , actingUse
  ) where

import Prelude
import Prim hiding (Type)

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, isJust)
import Data.Set as Set
import Data.Tuple (Tuple(..))
import Stella.Compiler.CST.Types (Attribute, Decl(..), Import(..), ImportItem(..), Members(..), Name, SourceRange)
import Stella.Compiler.CST.Types as CST
import Stella.Compiler.Interface.Environment (BuildEnvironment, lookupInterface)
import Stella.Compiler.Interface.Module (Export, Exports, TypeEntity(..), TypeExport, Via(..), emptyExports)
import Stella.Compiler.Interface.Prim (primAttribute)
import Stella.Compiler.Resolve.Group (Declaration(..), GroupedModule, PrefixItem(..), Prefix)
import Stella.Compiler.Surface.Name (OperatorName(..))
import Stella.Compiler.TypedCore.Name (EffName(..), Ident(..), ModuleName(..), Qualified(..), TyName(..))
import Stella.Compiler.TypedCore.Prim (primModule)

-- | The candidates each name of a namespace stands for, keyed by the name as
-- | it is written.
type Candidates a = Map String (Array (Export a))

-- | Names in every namespace a module can bring into scope. A type keeps the
-- | members that came with it.
type Names =
  { values :: Candidates (Qualified Ident)
  , types :: Map String (Array TypeExport)
  , operators :: Candidates (Qualified OperatorName)
  , typeOperators :: Candidates (Qualified OperatorName)
  , macros :: Candidates (Qualified Ident)
  , attributes :: Candidates (Qualified Ident)
  }

emptyNames :: Names
emptyNames =
  { values: Map.empty
  , types: Map.empty
  , operators: Map.empty
  , typeOperators: Map.empty
  , macros: Map.empty
  , attributes: Map.empty
  }

-- | What is in scope at the top of a module.
-- |
-- | **An unqualified name is looked up in `declared` first, and in `imported`
-- | where the module declares none**, a top-level declaration hiding an
-- | imported name of its namespace. A qualified name is looked up under its
-- | alias in `qualified`; an alias of a lazy import is in `lazy`, and opens
-- | nowhere but in a local open.
-- |
-- | The module's own macros are in no namespace of its own: a macro is used by
-- | the modules importing it. Its own attributes are in `declared`, an attribute
-- | being attached where it is declared as anywhere else.
type Scope =
  { module :: ModuleName
  , declared :: Names
  , imported :: Names
  , qualified :: Map String Names
  , lazy :: Map String Names
  }

type ScopedModule =
  { name :: ModuleName
  -- | The modules the header imports, which are the module's dependencies.
  -- | `Prim` is never among them.
  , imports :: Array { range :: SourceRange, module :: ModuleName }
  , scope :: Scope
  , exports :: Exports
  }

data Namespace
  = ValueNamespace
  | TypeNamespace
  | OperatorNamespace
  | TypeOperatorNamespace
  | MacroNamespace
  | AttributeNamespace

data ScopeError = ScopeError SourceRange ScopeReason

data ScopeReason
  -- | An import of a module the build environment does not hold.
  = ModuleNotFound ModuleName
  -- | `import lazy M` without an alias, or with a list.
  | LazyImportNotQualified
  -- | An item of an import list, or of `hiding`, naming what the module does
  -- | not export.
  | NotExported ModuleName Namespace String
  -- | `T(A)` where `A` is not a member the type is published with.
  | NotAMember String String
  -- | A second top-level declaration of a name in one namespace.
  | DeclaredTwice Namespace String
  -- | `@[elaborationOnly]` on a declaration the compiler does not list.
  | ElaborationOnlyNotAllowed
  -- | An export of a name nothing in scope stands for.
  | ExportNotInScope Namespace String
  -- | An export of a name several entities in scope stand for.
  | ExportAmbiguous Namespace String
  -- | One exported name standing for two entities.
  | ExportedTwice Namespace String
  -- | `module M` in the export list of `M` itself.
  | ExportOwnModule
  -- | `module A` for an alias of a lazy import.
  | ExportLazyAlias String
  -- | `module N` for a name that is neither an alias nor an import without one.
  | ExportModuleNotImported String
  -- | An export naming an elaboration-only constructor, which no source names.
  | ExportElaborationOnly String

data ScopeWarning
  -- | A top-level declaration hiding a name an import brings unqualified.
  = HidesImport SourceRange Namespace String

derive instance Eq Namespace
derive instance Eq ScopeError
derive instance Eq ScopeReason
derive instance Eq ScopeWarning

instance Show Namespace where
  show = namespaceWord

instance Show ScopeError where
  show (ScopeError r reason) =
    "ScopeError " <> show r.start.line <> ":" <> show r.start.column <> " " <> printScopeReason reason

instance Show ScopeReason where
  show = printScopeReason

instance Show ScopeWarning where
  show = printScopeWarning

namespaceWord :: Namespace -> String
namespaceWord = case _ of
  ValueNamespace -> "value"
  TypeNamespace -> "type"
  OperatorNamespace -> "operator"
  TypeOperatorNamespace -> "type operator"
  MacroNamespace -> "macro"
  AttributeNamespace -> "attribute"

printScopeReason :: ScopeReason -> String
printScopeReason = case _ of
  ModuleNotFound (ModuleName m) -> "Module `" <> m <> "` is not found"
  LazyImportNotQualified -> "A lazy import needs an alias and takes no list"
  NotExported (ModuleName m) ns n -> "Module `" <> m <> "` exports no " <> namespaceWord ns <> " `" <> n <> "`"
  NotAMember t m -> "`" <> m <> "` is not a member of `" <> t <> "`"
  DeclaredTwice ns n -> "The " <> namespaceWord ns <> " `" <> n <> "` is already declared in this module"
  ElaborationOnlyNotAllowed -> "`elaborationOnly` cannot stand on this declaration"
  ExportNotInScope ns n -> "There is no " <> namespaceWord ns <> " `" <> n <> "` to export"
  ExportAmbiguous ns n -> "The " <> namespaceWord ns <> " `" <> n <> "` is ambiguous here; export it qualified"
  ExportedTwice ns n -> "The " <> namespaceWord ns <> " `" <> n <> "` is already exported for another entity"
  ExportOwnModule -> "A module does not name itself in its export list"
  ExportLazyAlias a -> "`" <> a <> "` is the alias of a lazy import, and is not re-exported"
  ExportModuleNotImported n -> "`" <> n <> "` names no import of this module"
  ExportElaborationOnly n -> "`" <> n <> "` cannot be exported; export its type alone"

printScopeWarning :: ScopeWarning -> String
printScopeWarning (HidesImport _ ns n) =
  "This declaration hides the imported " <> namespaceWord ns <> " `" <> n <> "`"

-- | The declarations that may carry `@[elaborationOnly]`: the module, the type,
-- | whether it is a newtype, its one constructor as source writes it, and the
-- | identity that constructor takes, a name no source grammar spells. A
-- | declaration carrying the attribute is admitted only where it is one of
-- | these exactly, its form and its constructors included.
elaborationOnlyEntries
  :: Array { module :: ModuleName, type :: String, newtype :: Boolean, constructor :: String, internal :: String }
elaborationOnlyEntries =
  [ { module: ModuleName "Base.Continuation", type: "Continuation", newtype: true, constructor: "Continuation", internal: "$Continuation" } ]

-- | Whether an attribute is written with no argument. `@[macro]` and
-- | `@[elaborationOnly]` take none, and the scope acts on one only where it is
-- | written so and stands on a declaration it is for: `macro` on a value
-- | declaration that is no computation, `elaborationOnly` on a data type or a
-- | newtype. Anywhere else the scope leaves it to be reported where the
-- | declaration's attributes are resolved.
writtenBare :: Attribute -> Boolean
writtenBare a = Array.null a.args

-- | The use of an attribute the scope acts on, among the uses written of it:
-- | the first, where it is written bare. A later use is a second one wherever
-- | the first stands, so it is never the one acted on.
actingUse :: (Attribute -> Boolean) -> Array Attribute -> Maybe Attribute
actingUse isIt uses = Array.find isIt uses >>= \a -> if writtenBare a then Just a else Nothing

-- | The entry the compiler lists for a data type or a newtype, where the
-- | declaration is exactly one: its module, its name, its form, and its
-- | constructors as written.
elaborationOnlyEntry
  :: ModuleName
  -> String
  -> Boolean
  -> Array String
  -> Maybe { module :: ModuleName, type :: String, newtype :: Boolean, constructor :: String, internal :: String }
elaborationOnlyEntry m t isNewtype ctors =
  Array.find (\e -> e.module == m && e.type == t && e.newtype == isNewtype && ctors == [ e.constructor ]) elaborationOnlyEntries

------------------------------------------------------------------------------
-- Candidates

-- | Adds a candidate, which is no new one where it stands for an entity the
-- | name already stands for.
addCandidate :: forall a. Eq a => String -> Export a -> Candidates a -> Candidates a
addCandidate name c = Map.alter (Just <<< add <<< fromMaybe []) name
  where
  add cs = if Array.any (\x -> x.entity == c.entity) cs then cs else Array.snoc cs c

-- | Adds a type, merging the members it came with into a candidate for the
-- | same entity.
addType :: String -> TypeExport -> Map String (Array TypeExport) -> Map String (Array TypeExport)
addType name c = Map.alter (Just <<< add <<< fromMaybe []) name
  where
  add cs = case Array.findIndex (\x -> x.entity == c.entity) cs of
    Nothing -> Array.snoc cs c
    Just i -> fromMaybe cs (Array.modifyAt i (\x -> x { members = x.members <> Array.filter (\m -> not (Array.elem m x.members)) c.members }) cs)

unionNames :: Names -> Names -> Names
unionNames a b =
  { values: foldCandidates a.values b.values
  , types: foldl (\acc (Tuple n cs) -> foldl (\acc' c -> addType n c acc') acc cs) a.types (entries b.types)
  , operators: foldCandidates a.operators b.operators
  , typeOperators: foldCandidates a.typeOperators b.typeOperators
  , macros: foldCandidates a.macros b.macros
  , attributes: foldCandidates a.attributes b.attributes
  }
  where
  foldCandidates :: forall x. Eq x => Candidates x -> Candidates x -> Candidates x
  foldCandidates x y = foldl (\acc (Tuple n cs) -> foldl (\acc' c -> addCandidate n c acc') acc cs) x (entries y)

entries :: forall v. Map String v -> Array (Tuple String v)
entries = Map.toUnfoldable

-- | Every name a module exports, each reached through an import of it.
exportedNames :: Via -> Exports -> Names
exportedNames via e =
  { values: one e.values
  , types: map (\t -> [ t { via = via } ]) e.types
  , operators: one e.operators
  , typeOperators: one e.typeOperators
  , macros: one e.macros
  , attributes: one e.attributes
  }
  where
  one :: forall x. Map String (Export x) -> Candidates x
  one = map (\x -> [ x { via = via } ])

------------------------------------------------------------------------------
-- Imports

type ImportState =
  { imported :: Names
  , qualified :: Map String Names
  , lazy :: Map String Names
  -- | What each import without an alias brings unqualified, for `module N`.
  , unqualifiedBy :: Map String Names
  -- | The modules the imports sharing an alias name, for `module A`.
  , aliasModules :: Map String (Array ModuleName)
  , imports :: Array { range :: SourceRange, module :: ModuleName }
  , errors :: Array ScopeError
  }

importAll :: BuildEnvironment -> Array Import -> ImportState
importAll env is = foldl step start withPrim
  where
  start =
    { imported: emptyNames
    , qualified: Map.empty
    , lazy: Map.empty
    , unqualifiedBy: Map.empty
    , aliasModules: Map.empty
    , imports: []
    , errors: []
    }

  writesPrim = Array.any (\(Import i) -> i.module.name == primName) is

  primName = case primModule of
    ModuleName m -> m

  -- `Prim` is opened as `import Prim` would open it where no import of it is
  -- written; its range is no position of the source.
  withPrim =
    if writesPrim then is
    else Array.cons (Import { lazy: false, module: { range: nowhere, qualifier: Nothing, name: primName }, names: Nothing, hiding: Nothing, alias: Nothing }) is

  step s (Import i) =
    let
      moduleName = ModuleName i.module.name
      isPrim = moduleName == primModule
    in
      case lookupInterface moduleName env of
        Nothing -> s { errors = Array.snoc s.errors (ScopeError i.module.range (ModuleNotFound moduleName)) }
        Just interface ->
          let
            plain = not i.lazy && i.alias == Nothing && i.names == Nothing
            selected = select moduleName i.names (if plain then i.hiding else Nothing) interface.exports
            s' = s
              { imports = if isPrim then s.imports else Array.snoc s.imports { range: i.module.range, module: moduleName }
              , errors = s.errors <> selected.errors
              }
          in
            case i.lazy, i.alias of
              true, Just a | i.names == Nothing ->
                s' { lazy = Map.alter (Just <<< unionNames selected.names <<< fromMaybe emptyNames) a.name s'.lazy }
              true, _ ->
                s' { errors = Array.snoc s'.errors (ScopeError i.module.range LazyImportNotQualified) }
              false, Just a ->
                s'
                  { qualified = Map.alter (Just <<< unionNames selected.names <<< fromMaybe emptyNames) a.name s'.qualified
                  , aliasModules = Map.alter (Just <<< (_ <> [ moduleName ]) <<< fromMaybe []) a.name s'.aliasModules
                  }
              false, Nothing ->
                s'
                  { imported = unionNames s'.imported selected.names
                  , unqualifiedBy = Map.alter (Just <<< unionNames selected.names <<< fromMaybe emptyNames) i.module.name s'.unqualifiedBy
                  }

-- | The names an import brings: everything its module exports, the items of
-- | its list, or everything but the items `hiding` names. `hiding` on any
-- | other import is reported where the tree is checked, and left out here.
select
  :: ModuleName
  -> Maybe (Array ImportItem)
  -> Maybe { range :: SourceRange, items :: Array ImportItem }
  -> Exports
  -> { names :: Names, errors :: Array ScopeError }
select moduleName list hiding exports = case list, hiding of
  Just items, _ -> foldl pick { names: emptyNames, errors: [] } items
  Nothing, Just h -> foldl drop { names: all, errors: [] } h.items
  Nothing, Nothing -> { names: all, errors: [] }
  where
  via = ThroughImport moduleName
  all = exportedNames via exports

  missing r ns n = ScopeError r (NotExported moduleName ns n)

  pick acc = case _ of
    ImportValue n -> single acc n ValueNamespace exports.values \c -> acc.names { values = addCandidate n.name c acc.names.values }
    ImportOperator n -> single acc n OperatorNamespace exports.operators \c -> acc.names { operators = addCandidate n.name c acc.names.operators }
    ImportTypeOperator n -> single acc n TypeOperatorNamespace exports.typeOperators \c -> acc.names { typeOperators = addCandidate n.name c acc.names.typeOperators }
    ImportMacro n -> single acc n MacroNamespace exports.macros \c -> acc.names { macros = addCandidate n.name c acc.names.macros }
    ImportAttribute n -> single acc n AttributeNamespace exports.attributes \c -> acc.names { attributes = addCandidate n.name c acc.names.attributes }
    ImportType n ms -> case Map.lookup n.name exports.types of
      Nothing -> acc { errors = Array.snoc acc.errors (missing n.range TypeNamespace n.name) }
      Just t ->
        let
          chosen = chooseMembers n t ms
          withMembers = foldl (\names m -> memberValue names m) acc.names chosen.members
        in
          { names: withMembers { types = addType n.name (t { via = via, members = chosen.members }) withMembers.types }
          , errors: acc.errors <> chosen.errors
          }

  single :: forall x. { names :: Names, errors :: Array ScopeError } -> Name -> Namespace -> Map String (Export x) -> (Export x -> Names) -> { names :: Names, errors :: Array ScopeError }
  single acc n ns table add = case Map.lookup n.name table of
    Nothing -> acc { errors = Array.snoc acc.errors (missing n.range ns n.name) }
    Just c -> acc { names = add (c { via = via }) }

  memberValue names (Ident m) = case Map.lookup m exports.values of
    Just c -> names { values = addCandidate m (c { via = via }) names.values }
    Nothing -> names

  chooseMembers n t = case _ of
    Nothing -> { members: [], errors: [] }
    Just MembersAll -> { members: t.members, errors: [] }
    Just (MembersOnly ns) ->
      foldl
        ( \acc m ->
            if Array.elem (Ident m.name) t.members then acc { members = withMember acc.members (Ident m.name) }
            else acc { errors = Array.snoc acc.errors (ScopeError m.range (NotAMember n.name m.name)) }
        )
        { members: [], errors: [] }
        ns

  drop acc = case _ of
    ImportValue n -> dropOne acc n ValueNamespace exports.values \names -> names { values = Map.delete n.name names.values }
    ImportOperator n -> dropOne acc n OperatorNamespace exports.operators \names -> names { operators = Map.delete n.name names.operators }
    ImportTypeOperator n -> dropOne acc n TypeOperatorNamespace exports.typeOperators \names -> names { typeOperators = Map.delete n.name names.typeOperators }
    ImportMacro n -> dropOne acc n MacroNamespace exports.macros \names -> names { macros = Map.delete n.name names.macros }
    ImportAttribute n -> dropOne acc n AttributeNamespace exports.attributes \names -> names { attributes = Map.delete n.name names.attributes }
    ImportType n ms -> case Map.lookup n.name exports.types of
      Nothing -> acc { errors = Array.snoc acc.errors (missing n.range TypeNamespace n.name) }
      Just t ->
        let
          chosen = chooseMembers n t ms
          hidden = foldl (\names (Ident m) -> names { values = Map.delete m names.values }) acc.names chosen.members
        in
          { names: hidden { types = Map.delete n.name hidden.types }, errors: acc.errors <> chosen.errors }

  dropOne :: forall x. { names :: Names, errors :: Array ScopeError } -> Name -> Namespace -> Map String (Export x) -> (Names -> Names) -> { names :: Names, errors :: Array ScopeError }
  dropOne acc n ns table remove
    | Map.member n.name table = acc { names = remove acc.names }
    | otherwise = acc { errors = Array.snoc acc.errors (missing n.range ns n.name) }

-- | A member added to those chosen, once: a member named twice is chosen at
-- | its first naming.
withMember :: Array Ident -> Ident -> Array Ident
withMember ms m = if Array.elem m ms then ms else Array.snoc ms m

nowhere :: SourceRange
nowhere = { start: { line: 0, column: 0 }, end: { line: 0, column: 0 } }

------------------------------------------------------------------------------
-- Declarations

type DeclaredState =
  { declared :: Names
  -- | The module's own macros, which its export list may name.
  , macros :: Candidates (Qualified Ident)
  -- | Where each declared name was declared, for what is reported about it.
  , ranges :: Array { namespace :: Namespace, name :: String, range :: SourceRange }
  , errors :: Array ScopeError
  }

declareAll :: ModuleName -> (Attribute -> Maybe (Qualified Ident)) -> Array Declaration -> DeclaredState
declareAll m attributeOf = foldl declaration { declared: emptyNames, macros: Map.empty, ranges: [], errors: [] }
  where
  own :: forall a. a -> Qualified a
  own = Qualified m

  declared :: forall a. a -> Export a
  declared = { entity: _, via: Declared }

  -- A name declared already in its namespace is reported, and the table keeps
  -- the entity it already holds, which is the same qualified name.
  enter ns (n :: Name) add s
    | Array.any (\x -> x.namespace == ns && x.name == n.name) s.ranges =
        s { errors = Array.snoc s.errors (ScopeError n.range (DeclaredTwice ns n.name)) }
    | otherwise =
        (add s) { ranges = Array.snoc s.ranges { namespace: ns, name: n.name, range: n.range } }

  value n s = enter ValueNamespace n (\st -> st { declared = st.declared { values = addCandidate n.name (declared (own (Ident n.name))) st.declared.values } }) s
  valueAs n entity s = enter ValueNamespace n (\st -> st { declared = st.declared { values = addCandidate n.name (declared entity) st.declared.values } }) s
  typeName n entity members s = enter TypeNamespace n (\st -> st { declared = st.declared { types = addType n.name { entity, via: Declared, members } st.declared.types } }) s

  -- The use of an attribute of `Prim` the scope acts on: its first use, where
  -- that one is written bare.
  carries attr prefix = Array.fromFoldable (actingUse (\a -> attributeOf a == Just (primAttribute attr)) (attributes prefix))

  attributes :: Prefix -> Array Attribute
  attributes = Array.mapMaybe case _ of
    PrefixAttribute a -> Just a
    _ -> Nothing

  declaration s = case _ of
    DeclarationValue p v
      | not v.computation && not (Array.null (carries "macro" p)) ->
          enter MacroNamespace v.name (\st -> st { macros = addCandidate v.name.name (declared (own (Ident v.name.name))) st.macros }) s
      | otherwise -> value v.name s
    DeclarationType p _ d -> case d of
      DeclData n _ ctors -> dataType p false n (map _.name ctors) s
      DeclNewtype n _ c _ -> dataType p true n [ c ] s
      DeclType n _ _ -> typeName n (TypeEntity (own (TyName n.name))) [] s
      _ -> s
    DeclarationOther _ d -> case d of
      DeclEffect n _ ops ->
        foldl (\st o -> value o.name st) (typeName n (EffectEntity (own (EffName n.name))) (map (Ident <<< _.name.name) ops) s) ops
      DeclHandler n _ _ _ -> value n s
      DeclForeign n _ -> value n s
      DeclForeignType n _ -> typeName n (TypeEntity (own (TyName n.name))) [] s
      DeclFixity _ _ _ o -> enter OperatorNamespace o (\st -> st { declared = st.declared { operators = addCandidate o.name (declared (own (OperatorName o.name))) st.declared.operators } }) s
      DeclTypeFixity _ _ _ o -> enter TypeOperatorNamespace o (\st -> st { declared = st.declared { typeOperators = addCandidate o.name (declared (own (OperatorName o.name))) st.declared.typeOperators } }) s
      DeclAttribute n _ -> enter AttributeNamespace n (\st -> st { declared = st.declared { attributes = addCandidate n.name (declared (own (Ident n.name))) st.declared.attributes } }) s
      _ -> s
    DeclarationMacro _ _ -> s

  -- A data type or newtype, and its constructors. One carrying
  -- `@[elaborationOnly]`, written bare, that is exactly a declaration the compiler lists has
  -- its constructor take the internal identity, and publishes it as no member
  -- of the type; on any other declaration the attribute is refused and the
  -- declaration is what it would be without it.
  dataType p isNewtype n ctors s =
    let
      marked = carries "elaborationOnly" p
      listed = elaborationOnlyEntry m n.name isNewtype (map _.name ctors)
      internal c = case listed of
        Just e | not (Array.null marked) && e.constructor == c.name -> Just (own (Ident e.internal))
        _ -> Nothing
      refused = case listed of
        Nothing -> map (\a -> ScopeError a.range ElaborationOnlyNotAllowed) marked
        Just _ -> []
      members = Array.mapMaybe (\c -> if isJust (internal c) then Nothing else Just (Ident c.name)) ctors
      withType = typeName n (TypeEntity (own (TyName n.name))) members (s { errors = s.errors <> refused })
    in
      foldl (\st c -> valueAs c (fromMaybe (own (Ident c.name)) (internal c)) st) withType ctors

------------------------------------------------------------------------------
-- The module

resolveScope
  :: BuildEnvironment
  -> GroupedModule
  -> { scoped :: ScopedModule, errors :: Array ScopeError, warnings :: Array ScopeWarning }
resolveScope env g =
  { scoped: { name: moduleName, imports: imported.imports, scope, exports: exported.exports }
  , errors: imported.errors <> declared.errors <> exported.errors
  , warnings
  }
  where
  moduleName = ModuleName g.name.name
  imported = importAll env g.imports

  -- The attributes a declaration's prefix names resolve against the module's
  -- own attribute declarations and the attributes its imports bring, which
  -- is all that deciding a macro and an elaboration-only entry needs here.
  ownAttributes = Set.fromFoldable (Array.mapMaybe ownAttribute g.declarations)
  ownAttribute = case _ of
    DeclarationOther _ (DeclAttribute n _) -> Just n.name
    _ -> Nothing

  attributeOf :: Attribute -> Maybe (Qualified Ident)
  attributeOf a = case a.name.qualifier of
    Nothing
      | Set.member a.name.name ownAttributes -> Just (Qualified moduleName (Ident a.name.name))
      | otherwise -> unique (Map.lookup a.name.name imported.imported.attributes)
    Just q -> unique (Map.lookup q imported.qualified >>= \names -> Map.lookup a.name.name names.attributes)

  unique = case _ of
    Just [ c ] -> Just c.entity
    _ -> Nothing

  declared = declareAll moduleName attributeOf g.declarations

  scope =
    { module: moduleName
    , declared: declared.declared
    , imported: imported.imported
    , qualified: imported.qualified
    , lazy: imported.lazy
    }

  warnings = Array.mapMaybe hides declared.ranges
  hides r =
    let
      present = case r.namespace of
        ValueNamespace -> Map.member r.name imported.imported.values
        TypeNamespace -> Map.member r.name imported.imported.types
        OperatorNamespace -> Map.member r.name imported.imported.operators
        TypeOperatorNamespace -> Map.member r.name imported.imported.typeOperators
        AttributeNamespace -> Map.member r.name imported.imported.attributes
        MacroNamespace -> false
    in
      if present then Just (HidesImport r.range r.namespace r.name) else Nothing

  exported = exportAll env moduleName scope declared.macros imported g.exports

------------------------------------------------------------------------------
-- Exports

type ExportState = { exports :: Exports, errors :: Array ScopeError }

exportAll
  :: BuildEnvironment
  -> ModuleName
  -> Scope
  -> Candidates (Qualified Ident)
  -> ImportState
  -> Maybe (Array CST.Export)
  -> ExportState
exportAll env m scope ownMacros imported = case _ of
  Nothing ->
    { exports: (namesAsExports (scope.declared { values = Map.filter (not <<< Array.any (isInternal <<< _.entity)) scope.declared.values })) { macros = map firstOf ownMacros }, errors: [] }
  Just items -> foldl item { exports: emptyExports, errors: [] } items
  where
  firstOf cs = fromMaybe { entity: Qualified m (Ident ""), via: Declared } (Array.head cs)

  -- What a candidate is published as: declared where this module declares the
  -- entity, and otherwise through the import that brought it.
  published :: forall a. Qualified a -> Export (Qualified a) -> Export (Qualified a)
  published (Qualified owner _) c = if owner == m then c { via = Declared } else c

  lookupIn :: forall a. (Names -> Candidates a) -> Name -> Array (Export a)
  lookupIn field n = case n.qualifier of
    Nothing -> case Map.lookup n.name (field scope.declared) of
      Just cs -> cs
      Nothing -> fromMaybe [] (Map.lookup n.name (field scope.imported))
    Just q -> fromMaybe [] (Map.lookup q scope.qualified >>= Map.lookup n.name <<< field)

  -- One exported name stands for one entity: a second export of it for
  -- another entity is reported and the first kept.
  put :: forall a. Eq a => Namespace -> Name -> Export a -> Map String (Export a) -> ExportState -> (Map String (Export a) -> Exports) -> ExportState
  put ns n c table s set = case Map.lookup n.name table of
    Just existing
      | existing.entity /= c.entity -> s { errors = Array.snoc s.errors (ScopeError n.range (ExportedTwice ns n.name)) }
      | otherwise -> s
    Nothing -> s { exports = set (Map.insert n.name c table) }

  resolved :: forall a. Namespace -> Name -> Array (Export (Qualified a)) -> ExportState -> (Export (Qualified a) -> ExportState) -> ExportState
  resolved ns n cs s k = case cs of
    [ c ] -> k (published c.entity c)
    [] -> s { errors = Array.snoc s.errors (ScopeError n.range (ExportNotInScope ns n.name)) }
    _ -> s { errors = Array.snoc s.errors (ScopeError n.range (ExportAmbiguous ns n.name)) }

  item s = case _ of
    CST.ExportValue n -> resolved ValueNamespace n (lookupIn _.values n) s \c ->
      if isInternal c.entity then s { errors = Array.snoc s.errors (ScopeError n.range (ExportElaborationOnly n.name)) }
      else put ValueNamespace n c s.exports.values s \t -> s.exports { values = t }
    CST.ExportOperator n -> resolved OperatorNamespace n (lookupIn _.operators n) s \c ->
      put OperatorNamespace n c s.exports.operators s \t -> s.exports { operators = t }
    CST.ExportTypeOperator n -> resolved TypeOperatorNamespace n (lookupIn _.typeOperators n) s \c ->
      put TypeOperatorNamespace n c s.exports.typeOperators s \t -> s.exports { typeOperators = t }
    CST.ExportAttribute n -> resolved AttributeNamespace n (lookupIn _.attributes n) s \c ->
      put AttributeNamespace n c s.exports.attributes s \t -> s.exports { attributes = t }
    CST.ExportMacro n ->
      let
        own = case n.qualifier of
          Nothing -> Map.lookup n.name ownMacros
          Just _ -> Nothing
      in
        resolved MacroNamespace n (fromMaybe (lookupIn _.macros n) own) s \c ->
          put MacroNamespace n c s.exports.macros s \t -> s.exports { macros = t }
    CST.ExportType n ms -> exportType s n ms
    CST.ExportModule n -> exportModule s n

  exportType s n ms = case typesIn n of
    [ t ] ->
      let
        owner = case t.entity of
          TypeEntity (Qualified o _) -> o
          EffectEntity (Qualified o _) -> o
        via = if owner == m then Declared else t.via
        -- A member is in scope where a value of its name, qualified as the
        -- type is, stands for that member; it is published the way that value
        -- came, which need not be the way the type did.
        memberInScope (Ident mn) =
          Array.find (\c -> c.entity == Qualified owner (Ident mn)) (lookupIn _.values (n { name = mn }))
        inScope = isJust <<< memberInScope
        everyMember = membersOf t
        chosen = case ms of
          Nothing -> { members: [], errors: [] }
          Just MembersAll -> { members: Array.filter inScope everyMember, errors: [] }
          Just (MembersOnly names) ->
            foldl
              ( \acc mn ->
                  if not (Array.elem (Ident mn.name) everyMember) then acc { errors = Array.snoc acc.errors (ScopeError mn.range (NotAMember n.name mn.name)) }
                  else if not (inScope (Ident mn.name)) then acc { errors = Array.snoc acc.errors (ScopeError mn.range (ExportNotInScope ValueNamespace mn.name)) }
                  else acc { members = withMember acc.members (Ident mn.name) }
              )
              { members: [], errors: [] }
              names
        withType = mergeType s (n { qualifier = Nothing }) { entity: t.entity, via, members: chosen.members }
        withMembers = foldl (\st member@(Ident mn) -> putValue st { range: n.range, qualifier: Nothing, name: mn } (memberExport member)) withType chosen.members
        memberExport member = case memberInScope member of
          Just c -> published c.entity c
          Nothing -> { entity: Qualified owner member, via }
      in
        withMembers { errors = withMembers.errors <> chosen.errors }
    [] -> s { errors = Array.snoc s.errors (ScopeError n.range (ExportNotInScope TypeNamespace n.name)) }
    _ -> s { errors = Array.snoc s.errors (ScopeError n.range (ExportAmbiguous TypeNamespace n.name)) }

  typesIn :: Name -> Array TypeExport
  typesIn n = case n.qualifier of
    Nothing -> case Map.lookup n.name scope.declared.types of
      Just cs -> cs
      Nothing -> fromMaybe [] (Map.lookup n.name scope.imported.types)
    Just q -> fromMaybe [] (Map.lookup q scope.qualified >>= Map.lookup n.name <<< _.types)

  -- Every member of a type: as this module declares it, or as the module
  -- declaring it publishes it, whatever any import brought of them.
  membersOf :: TypeExport -> Array Ident
  membersOf t = case t.entity of
    TypeEntity q@(Qualified owner (TyName name)) -> declaredMembers owner name (TypeEntity q)
    EffectEntity q@(Qualified owner (EffName name)) -> declaredMembers owner name (EffectEntity q)
    where
    declaredMembers owner name entity
      | owner == m = t.members
      | otherwise = case lookupInterface owner env >>= Map.lookup name <<< _.exports.types of
          Just e | e.entity == entity -> e.members
          _ -> t.members

  putValue s n c = put ValueNamespace n c s.exports.values s \t -> s.exports { values = t }

  -- A type exported under a name it is exported under already: the same
  -- entity again adds the members it brings, in order; another is reported.
  mergeType s n t = case Map.lookup n.name s.exports.types of
    Just existing
      | existing.entity /= t.entity -> s { errors = Array.snoc s.errors (ScopeError n.range (ExportedTwice TypeNamespace n.name)) }
      | otherwise ->
          s { exports = s.exports { types = Map.insert n.name (existing { members = existing.members <> Array.filter (\x -> not (Array.elem x existing.members)) t.members }) s.exports.types } }
    Nothing -> s { exports = s.exports { types = Map.insert n.name t s.exports.types } }

  exportModule s n
    | ModuleName n.name == m = s { errors = Array.snoc s.errors (ScopeError n.range ExportOwnModule) }
    | Just names <- Map.lookup n.name scope.qualified =
        whole s (fromMaybe [] (Map.lookup n.name imported.aliasModules)) names n.range
    | Map.member n.name scope.lazy = s { errors = Array.snoc s.errors (ScopeError n.range (ExportLazyAlias n.name)) }
    | Just names <- Map.lookup n.name imported.unqualifiedBy =
        whole s [ ModuleName n.name ] names n.range
    | otherwise = s { errors = Array.snoc s.errors (ScopeError n.range (ExportModuleNotImported n.name)) }

  -- Every name of a whole re-exported module, each standing for the one
  -- entity it does there.
  whole s modules names r =
    let
      at name = { range: r, qualifier: Nothing, name }

      each :: forall a. Eq a => (Exports -> Map String (Export a)) -> (Exports -> Map String (Export a) -> Exports) -> Namespace -> Candidates a -> ExportState -> ExportState
      each get set ns table st = foldl (\acc (Tuple name cs) -> foldl (\acc' c -> put ns (at name) c (get acc'.exports) acc' (set acc'.exports)) acc cs) st (entries table)
      typed st = foldl (\acc (Tuple name ts) -> foldl (\acc' t -> mergeType acc' (at name) t) acc ts) st (entries names.types)
      s1 = s { exports = s.exports { modules = s.exports.modules <> Array.filter (\x -> not (Array.elem x s.exports.modules)) modules } }
    in
      typed
        ( each _.values (\e t -> e { values = t }) ValueNamespace names.values
            $ each _.operators (\e t -> e { operators = t }) OperatorNamespace names.operators
            $ each _.typeOperators (\e t -> e { typeOperators = t }) TypeOperatorNamespace names.typeOperators
            $ each _.macros (\e t -> e { macros = t }) MacroNamespace names.macros
            $ each _.attributes (\e t -> e { attributes = t }) AttributeNamespace names.attributes s1
        )

-- | Whether an entity is an elaboration-only constructor under its internal
-- | identity.
isInternal :: Qualified Ident -> Boolean
isInternal (Qualified owner (Ident n)) = Array.any (\e -> e.module == owner && e.internal == n) elaborationOnlyEntries

-- | The exports of a module with no export list: every declaration it makes,
-- | and nothing it imports.
namesAsExports :: Names -> Exports
namesAsExports names = emptyExports
  { values = firstOf names.values
  , types = Map.mapMaybe Array.head names.types
  , operators = firstOf names.operators
  , typeOperators = firstOf names.typeOperators
  , attributes = firstOf names.attributes
  }
  where
  firstOf :: forall a. Candidates a -> Map String (Export a)
  firstOf = Map.mapMaybe Array.head
