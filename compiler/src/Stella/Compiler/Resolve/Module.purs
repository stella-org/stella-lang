-- | Name resolution of a module as a whole: its items grouped into
-- | declarations, its scope and exports, and each declaration resolved into
-- | the Surface AST, in the order written.
-- |
-- | Every problem is reported, with where it stands, and resolution goes on
-- | past it. A declaration whose problem leaves nothing to hold is left out —
-- | a handler whose effect is not decided, a fixity declaration whose target
-- | does not resolve, a computation with parameters, a macro called at a
-- | declaration's position — and its name stays in scope
-- | ([Surface AST](../../../../docs/technical-references/02-Surface-Language/08-Surface-AST.md)).
module Stella.Compiler.Resolve.Module
  ( ResolutionError(..)
  , ResolutionWarning(..)
  , Resolved
  , resolveModule
  , resolveModuleExpanding
  ) where

import Prelude
import Prim hiding (Type)

import Data.Array as Array
import Data.Maybe (Maybe(..), isJust, maybe)
import Data.Traversable (traverse)
import Stella.Compiler.CST.Range (binderRange, covering, exprRange, kindRange, nonEmpty, typeRange)
import Stella.Compiler.CST.Types as CST
import Stella.Compiler.Interface.Environment (BuildEnvironment)
import Stella.Compiler.Interface.Module (Exports)
import Stella.Compiler.Macro.Expand (ExpansionError, expandModule)
import Stella.Compiler.Macro.Run (ExpansionSettings, RunParser)
import Stella.Compiler.Resolve.Attribute (DeclarationSort(..), resolveAttributeDeclaration, resolveAttributes)
import Stella.Compiler.Resolve.Expr (resolveHandler, resolveTopDefinition)
import Stella.Compiler.Resolve.Group (Declaration(..), GroupError, GroupedModule, Prefix, ValueDeclaration, attributesOf, directivesOf, groupModule, modifiersOf)
import Stella.Compiler.Resolve.Monad (Found(..), Resolve, ResolveError, ResolveReason(..), ResolveWarning, TypeReference(..), ValueKind(..), context, contextOf, lookupType, lookupValue, ownValue, report, runResolve, valueKind, withTypeVariables)
import Stella.Compiler.Resolve.Scope (ScopeError, ScopeWarning, elaborationOnlyEntry, resolveScope)
import Stella.Compiler.Resolve.Type (bindTypeVariables, computationScope, resolveComputationSignature, resolveKind, resolveOperationSignature, resolveSignature, resolveType, signatureScope)
import Stella.Compiler.Surface.Decl (Associativity(..), Declaration(..), FixityTarget(..), Module, Observation(..)) as Surface
import Stella.Compiler.Surface.Name (OperatorName(..))
import Stella.Compiler.Surface.Origin (originOf)
import Stella.Compiler.Surface.Type (TypeOperatorTarget(..))
import Stella.Compiler.TypedCore.Name (EffName(..), Ident(..), ModuleName, Qualified(..), TyName(..))

data ResolutionError
  = GroupingError GroupError
  | ExpandingError ExpansionError
  | ScopingError ScopeError
  | ResolvingError ResolveError

data ResolutionWarning
  = ScopingWarning ScopeWarning
  | ResolvingWarning ResolveWarning

derive instance Eq ResolutionError
derive instance Eq ResolutionWarning

instance Show ResolutionError where
  show = case _ of
    GroupingError e -> show e
    ExpandingError e -> show e
    ScopingError e -> show e
    ResolvingError e -> show e

type Resolved = { module :: Surface.Module, exports :: Exports, errors :: Array ResolutionError, warnings :: Array ResolutionWarning }

-- | Resolve a module whose macro calls are left unexpanded, each reported as
-- | what this resolution does not do.
resolveModule :: BuildEnvironment -> CST.Module -> Resolved
resolveModule env m = resolveGrouped env (groupModule m) []

-- | Resolve a module, expanding every macro call standing where an expression
-- | does first, with the parsers run as given: the imports' macro namespace
-- | is fixed once the items are grouped, so the calls are expanded before the
-- | declarations are collected, and what was expanded is resolved as written
-- | source is.
resolveModuleExpanding :: forall m. Monad m => RunParser m -> ExpansionSettings -> BuildEnvironment -> CST.Module -> m Resolved
resolveModuleExpanding run settings env m = do
  let grouped = groupModule m
  expanded <- expandModule run settings env grouped.grouped
  pure (resolveGrouped env (grouped { grouped = expanded.grouped }) expanded.errors)

resolveGrouped
  :: BuildEnvironment
  -> { grouped :: GroupedModule, errors :: Array GroupError }
  -> Array ExpansionError
  -> Resolved
resolveGrouped env grouped expansionErrors =
  { module:
      { origin: originOf grouped.grouped.name.range
      , name: scoped.scoped.name
      , imports: map (\i -> { origin: originOf i.range, module: i.module }) scoped.scoped.imports
      , declarations: ran.result
      }
  , exports: scoped.scoped.exports
  , errors: map GroupingError grouped.errors <> map ExpandingError expansionErrors <> map ScopingError scoped.errors <> map ResolvingError ran.errors
  , warnings: map ScopingWarning scoped.warnings <> map ResolvingWarning ran.warnings
  }
  where
  scoped = resolveScope env grouped.grouped
  ran = runResolve (contextOf env grouped.grouped scoped.scoped) 0
    (Array.catMaybes <$> traverse declaration grouped.grouped.declarations)

declaration :: Declaration -> Resolve (Maybe Surface.Declaration)
declaration = case _ of
  DeclarationValue p v -> value p v
  DeclarationType p kind d -> typeDeclaration p kind d
  DeclarationOther p d -> other p d
  DeclarationMacro _ macro -> report macro.name.range (NotYetSupported "A macro call at a declaration's position") $> Nothing

value :: Prefix -> ValueDeclaration -> Resolve (Maybe Surface.Declaration)
value p v = do
  ctx <- context
  let name = Qualified ctx.module (Ident v.name.name)
  case v.computation, v.signature of
    true, Just t
      | Array.null v.binders -> do
          attributes <- resolveAttributes OnComputation false (attributesOf p)
          signature <- resolveComputationSignature t
          d <- withTypeVariables (computationScope signature) (resolveTopDefinition [] v.body v.localBindings)
          pure (Just (Surface.DeclComputation { origin, attributes, name, signature, body: d.body }))
      | otherwise -> report v.name.range (ComputationWithParameters v.name.name) $> Nothing
    _, _ -> do
      attributes <- resolveAttributes OnValue false (attributesOf p)
      signature <- traverse resolveSignature v.signature
      d <- withTypeVariables (maybe [] signatureScope signature) (resolveTopDefinition v.binders v.body v.localBindings)
      pure (Just (Surface.DeclValue { origin, attributes, name, signature, params: d.params, body: d.body }))
  where
  origin = originOf (nonEmpty ([ v.name.range, exprRange v.body ] <> map binderRange v.binders))

typeDeclaration :: Prefix -> Maybe CST.Kind -> CST.Decl -> Resolve (Maybe Surface.Declaration)
typeDeclaration p kindSignature d = do
  ctx <- context
  kind <- traverse resolveKind kindSignature
  case d of
    CST.DeclData n params ctors -> do
      attributes <- resolveAttributes OnData (listed ctx.module n false (map _.name ctors)) (attributesOf p)
      b <- bindTypeVariables params
      constructors <- withTypeVariables b.scope $ traverse
        ( \c -> do
            name <- ownValue c.name.name
            fields <- traverse resolveType c.fields
            pure { origin: originOf (nonEmpty ([ c.name.range ] <> map typeRange c.fields)), name, fields }
        )
        ctors
      pure (Just (Surface.DeclData { origin, attributes, name: tyName ctx.module n, kind, params: b.binders, constructors }))
    CST.DeclNewtype n params c field -> do
      attributes <- resolveAttributes OnNewtype (listed ctx.module n true [ c ]) (attributesOf p)
      b <- bindTypeVariables params
      name <- ownValue c.name
      field' <- withTypeVariables b.scope (resolveType field)
      let constructor = { origin: originOf (covering c.range (typeRange field)), name, field: field' }
      pure (Just (Surface.DeclNewtype { origin, attributes, name: tyName ctx.module n, kind, params: b.binders, constructor }))
    CST.DeclType n params body -> do
      attributes <- resolveAttributes OnSynonym false (attributesOf p)
      b <- bindTypeVariables params
      body' <- withTypeVariables b.scope (resolveType body)
      pure (Just (Surface.DeclSynonym { origin, attributes, name: tyName ctx.module n, kind, params: b.binders, body: body' }))
    _ -> pure Nothing
  where
  origin = originOf (declarationRange d)
  listed m n isNewtype ctors = isJust (elaborationOnlyEntry m n.name isNewtype (map _.name ctors))

other :: Prefix -> CST.Decl -> Resolve (Maybe Surface.Declaration)
other p d = do
  ctx <- context
  case d of
    CST.DeclEffect n params ops -> do
      attributes <- resolveAttributes OnEffect false (attributesOf p)
      b <- bindTypeVariables params
      operations <- withTypeVariables b.scope $ traverse
        ( \op -> do
            signature <- resolveOperationSignature op.type
            pure { origin: originOf (covering op.name.range (typeRange op.type)), name: Qualified ctx.module (Ident op.name.name), signature }
        )
        ops
      pure (Just (Surface.DeclEffect { origin, attributes, name: Qualified ctx.module (EffName n.name), params: b.binders, operations }))
    CST.DeclHandler n params t items -> do
      attributes <- resolveAttributes OnHandler false (attributesOf p)
      h <- resolveHandler params t items
      pure $ h.effect <#> \effect -> Surface.DeclHandler
        { origin
        , attributes
        , implicit: not (Array.null (modifiersOf p))
        , name: Qualified ctx.module (Ident n.name)
        , params: h.params
        , signature: h.signature
        , effect
        , body: h.body
        }
    CST.DeclForeign n t -> do
      attributes <- resolveAttributes OnForeign false (attributesOf p)
      signature <- resolveSignature t
      let observation = if Array.null (directivesOf p) then Surface.MayObserve else Surface.ObservesNone
      pure (Just (Surface.DeclForeign { origin, attributes, observation, name: Qualified ctx.module (Ident n.name), signature }))
    CST.DeclForeignType n k -> do
      attributes <- resolveAttributes OnForeignType false (attributesOf p)
      kind <- resolveKind k
      pure (Just (Surface.DeclForeignType { origin, attributes, name: tyName ctx.module n, kind }))
    CST.DeclFixity f precedence target op -> do
      _ <- resolveAttributes OnFixity false (attributesOf p)
      lookupValue target >>= case _ of
        Found q -> valueKind q <#> \k -> Just $ Surface.DeclFixity
          { origin
          , associativity: associativityOf f
          , precedence: precedence.value
          , target: case k of
              ConstructorValue -> Surface.FixityConstructor q
              _ -> Surface.FixityValue q
          , operator: OperatorName op.name
          }
        NotFound -> report target.range (UnknownValue (written target)) $> Nothing
        Ambiguous -> report target.range (AmbiguousValue (written target)) $> Nothing
    CST.DeclTypeFixity f precedence target op -> do
      _ <- resolveAttributes OnFixity false (attributesOf p)
      lookupType target >>= case _ of
        Found reference -> pure $ Just $ Surface.DeclTypeFixity
          { origin
          , associativity: associativityOf f
          , precedence: precedence.value
          , target: case reference of
              TypeConstructorReference q -> TargetTypeConstructor q
              TypeSynonymReference q -> TargetTypeSynonym q
              EffectReference e -> TargetEffect e
          , operator: OperatorName op.name
          }
        NotFound -> report target.range (UnknownType (written target)) $> Nothing
        Ambiguous -> report target.range (AmbiguousType (written target)) $> Nothing
    CST.DeclAttribute n params -> do
      _ <- resolveAttributes OnAttribute false (attributesOf p)
      r <- resolveAttributeDeclaration params
      pure (Just (Surface.DeclAttribute { origin, name: Qualified ctx.module (Ident n.name), positional: r.positional, keyword: r.keyword }))
    _ -> pure Nothing
  where
  origin = originOf (declarationRange d)
  associativityOf = case _ of
    CST.Infix -> Surface.AssociateNone
    CST.Infixl -> Surface.AssociateLeft
    CST.Infixr -> Surface.AssociateRight

tyName :: ModuleName -> CST.Name -> Qualified TyName
tyName m n = Qualified m (TyName n.name)

-- | The range of a declaration other than a value: from its name to the last
-- | thing it holds.
declarationRange :: CST.Decl -> CST.SourceRange
declarationRange = case _ of
  CST.DeclData n _ ctors -> nonEmpty ([ n.range ] <> Array.concatMap (\c -> [ c.name.range ] <> map typeRange c.fields) ctors)
  CST.DeclNewtype n _ _ t -> covering n.range (typeRange t)
  CST.DeclType n _ t -> covering n.range (typeRange t)
  CST.DeclEffect n _ ops -> nonEmpty ([ n.range ] <> map (\op -> covering op.name.range (typeRange op.type)) ops)
  CST.DeclHandler n _ t items -> nonEmpty ([ n.range, typeRange t ] <> Array.concatMap itemRanges items)
  CST.DeclForeign n t -> covering n.range (typeRange t)
  CST.DeclForeignType n k -> covering n.range (kindRange k)
  CST.DeclFixity _ p _ op -> covering p.range op.range
  CST.DeclTypeFixity _ p _ op -> covering p.range op.range
  CST.DeclAttribute n params -> nonEmpty ([ n.range ] <> map parameterRange params)
  CST.DeclSignature n t -> covering n.range (typeRange t)
  CST.DeclValue n _ body _ -> covering n.range (exprRange body)
  CST.DeclKindSignature _ n k -> covering n.range (kindRange k)
  where
  itemRanges = case _ of
    CST.HandlerCell n e -> [ n.range, exprRange e ]
    CST.HandlerClauses _ cs -> map clauseRange cs
  clauseRange = case _ of
    CST.ClauseOperation _ n _ e -> covering n.range (exprRange e)
    CST.ClauseReturn b e -> covering (binderRange b) (exprRange e)
  parameterRange = case _ of
    CST.AttributePositional t -> typeRange t
    CST.AttributeKeyword l t d -> covering l.range (maybe (typeRange t) exprRange d)

written :: CST.Name -> String
written n = maybe n.name (\q -> q <> "." <> n.name) n.qualifier
