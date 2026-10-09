-- | A module's data declarations elaborated into Core's, their kinds inferred
-- | together ([Elaboration](../../../../../docs/technical-references/02-Surface-Language/01-Elaboration.md)).
-- |
-- | **The declarations are read in two steps, every head before any field.**
-- | Each head is read first: its parameters, each at the kind written or at a
-- | metavariable, and the kind the declaration writes for it, where it writes
-- | one. Then every constructor's fields are read at `Type`, under the
-- | parameters of their declaration, with every head of the module in scope,
-- | so declarations referring to one another are read together and their
-- | kinds decided by the same equations.
-- |
-- | **A kind is decided by what the declarations say of it, or not at all.**
-- | A kind variable a declaration writes — on a parameter, on the declaration,
-- | or in a constructor's field — is the declaration's own, and a use of the
-- | type instantiates it afresh. A parameter whose kind nothing decided is outside
-- | what this version elaborates: deciding it is generalizing it, which this
-- | version does not do, so its kind must be written.
-- |
-- | **A field's rows are sharp under no condition on a parameter.** A row
-- | spreading a parameter needs it to lack the keys the row holds beside it,
-- | and a parameter carries no condition, so such a field is refused; a row
-- | variable a `forall` of the field binds carries its conditions there.
-- |
-- | A constructor's tag is its position among its declaration's constructors.
module Stella.Compiler.Elaborate.Surface.Data
  ( DataRead
  , readData
  , settledData
  ) where

import Prelude
import Prim hiding (Type)

import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldr)
import Data.Map as Map
import Data.Maybe (Maybe(..), maybe)
import Data.Set as Set
import Data.Traversable (for, traverse)
import Data.Tuple (Tuple(..))
import Stella.Compiler.Elaborate.CorePlus.Kind (XKind(..), toCoreKind)
import Stella.Compiler.Elaborate.CorePlus.Type (XType, toCore)
import Stella.Compiler.Elaborate.Kernel.Elab (Elab, equateKinds)
import Stella.Compiler.Elaborate.Mechanism.Unify (MetaContext, substitute, substituteKind)
import Stella.Compiler.Elaborate.Surface.Type (LocalHead, Scope, Unsupported(..), readBinder, readKind, readTypeAt, siteOf, typeKindVars)
import Stella.Compiler.Interface.Assemble (coreAttribute)
import Stella.Compiler.Surface.Decl (DataDeclaration)
import Stella.Compiler.Surface.Name (TypeVar(..))
import Stella.Compiler.Surface.Origin as Surface
import Stella.Compiler.Surface.Type (Kind(..))
import Stella.Compiler.TypedCore (DataDecl)
import Stella.Compiler.TypedCore.Name (Ident(..), KindVar, Qualified(..), TyName(..), TyVar)

-- | A data declaration read, its kinds not yet decided: its kind variables, its
-- | parameters each with where it stands, and its constructors' fields.
type DataRead =
  { declaration :: DataDeclaration
  , kindVars :: Array KindVar
  , params :: Array { var :: TypeVar, kind :: XKind, origin :: Surface.Origin }
  , constructors :: Array { origin :: Surface.Origin, name :: Qualified Ident, fields :: Array XType }
  , unsupported :: Array Unsupported
  }

-- | Every data declaration given, each head first, then each one's fields.
readData :: Array DataDeclaration -> Elab (Array DataRead)
readData declarations = do
  heads <- traverse readHead declarations
  let
    inModule = Map.fromFoldable (map (\h -> Tuple h.declaration.name { kindVars: h.kindVars, body: headKind h.params }) heads)
  for heads \h -> do
    let
      scope = (scopeOf h.declaration h.kindVars)
        { tyVars = Map.fromFoldable (map (\p -> Tuple (nameOf p.var) p.kind) h.params)
        , localTypes = inModule
        }
    constructors <- for h.declaration.constructors \c -> do
      fields <- traverse (readTypeAt scope XKType) c.fields
      -- a parameter carries no condition, so a row needing one of it is refused
      let unheld = map (\i -> UnheldConstraint i.origin i.atom) (Array.concatMap _.implied fields)
      pure { constructor: { origin: c.origin, name: c.name, fields: map _.type fields }, unsupported: Array.concatMap _.unsupported fields <> unheld }
    pure h { constructors = map _.constructor constructors, unsupported = h.unsupported <> Array.concatMap _.unsupported constructors }

-- | A declaration's head: its parameters, and the kind it writes for itself
-- | equated with the kind they give it.
readHead :: DataDeclaration -> Elab DataRead
readHead d = do
  let
    -- a kind variable is bound by the declaration it is written in, wherever
    -- in it it is written
    kindVars = Array.nub
      ( Array.concatMap (\b -> maybe [] kindVarsOf b.kind) d.params
          <> maybe [] kindVarsOf d.kind
          <> Array.concatMap (Array.concatMap typeKindVars <<< _.fields) d.constructors
      )
    scope = scopeOf d kindVars
  params <- for d.params \b -> do
    read <- readBinder scope b
    pure { param: { var: read.var, kind: read.kind, origin: b.origin }, unsupported: read.unsupported }
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

-- | The kind a head is at: its parameters' kinds to `Type`.
headKind :: forall r. Array { kind :: XKind | r } -> XKind
headKind = foldr (\p k -> XKFun p.kind k) XKType

-- | A declaration once every kind of it is decided: the Core declaration, or
-- | what keeps it from being one.
settledData :: MetaContext -> DataRead -> Either (Array Unsupported) DataDecl
settledData metas r
  | not (Array.null r.unsupported) = Left r.unsupported
  | otherwise =
      do
        -- every parameter whose kind is undetermined is reported
        params <- case traverse decided r.params of
          Just ps -> Right ps
          Nothing -> Left (Array.mapMaybe undetermined r.params)
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
          , isNewtype: false
          , attributes
          }
      where
      decided p = { name: nameOf p.var, kind: _ } <$> toCoreKind (substituteKind metas p.kind)
      undetermined p = case decided p of
        Just _ -> Nothing
        Nothing -> Just (OutsideSubset p.origin "a type parameter whose kind is decided only by generalizing it; its kind must be written")

-- | What a declaration's types are read under: its kind variables, and the
-- | declaration named as a value is, for locating what is reported of it.
scopeOf :: DataDeclaration -> Array KindVar -> Scope
scopeOf d kindVars =
  { declaration: case d.name of Qualified m (TyName n) -> Qualified m (Ident n)
  , kindVars: Set.fromFoldable kindVars
  , tyVars: Map.empty
  , localTypes: Map.empty :: Map.Map (Qualified TyName) LocalHead
  , anonymous: Map.empty
  }

kindVarsOf :: Kind -> Array KindVar
kindVarsOf = case _ of
  KindArrow _ a b -> kindVarsOf a <> kindVarsOf b
  KindVariable _ v -> [ v ]
  _ -> []

local :: forall a. Qualified a -> a
local (Qualified _ a) = a

nameOf :: TypeVar -> TyVar
nameOf (TypeVar v) = v.name
