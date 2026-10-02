-- | The first stage of resolution: the items of a module grouped into
-- | declarations, before any name is looked up.
-- |
-- | An attribute, a directive, and a modifier are items of their own in the
-- | concrete syntax tree; here each joins the declaration after it, its
-- | prefix. A signature joins the definition that follows it, and a kind
-- | signature the declaration it gives a kind to, each bringing the prefix
-- | written before it. A macro called at a declaration's position keeps its
-- | prefix as a unit with it: what an attribute before one means is the
-- | macro's to settle, so nothing passes on to the declarations after it.
-- |
-- | Every problem found is reported, with where it stands, and grouping goes
-- | on past it.
module Stella.Compiler.Resolve.Group
  ( PrefixItem(..)
  , Prefix
  , attributesOf
  , directivesOf
  , modifiersOf
  , Declaration(..)
  , ValueDeclaration
  , LocalBinding(..)
  , GroupedModule
  , GroupError(..)
  , GroupReason(..)
  , groupModule
  , groupBindings
  , isComputationSignature
  , printGroupReason
  ) where

import Prelude
import Prim hiding (Type)

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Maybe (Maybe(..), maybe)
import Data.Set as Set
import Stella.Compiler.CST.Types (Attribute, Binder(..), Decl(..), DeclKeyword(..), Directive, Export, Expr, Import(..), Item(..), Kind, LetBinding(..), Macro, Module(..), Name, RecordBinder(..), SourceRange, Type(..), isSynthesized)

data PrefixItem
  = PrefixAttribute Attribute
  | PrefixDirective Directive
  -- | `implicit`.
  | PrefixModifier Name

-- | What stands before a declaration, in the order written, whatever kind
-- | each item is.
type Prefix = Array PrefixItem

attributesOf :: Prefix -> Array Attribute
attributesOf = Array.mapMaybe case _ of
  PrefixAttribute a -> Just a
  _ -> Nothing

directivesOf :: Prefix -> Array Directive
directivesOf = Array.mapMaybe case _ of
  PrefixDirective d -> Just d
  _ -> Nothing

modifiersOf :: Prefix -> Array Name
modifiersOf = Array.mapMaybe case _ of
  PrefixModifier n -> Just n
  _ -> Nothing

prefixItemRange :: PrefixItem -> SourceRange
prefixItemRange = case _ of
  PrefixAttribute a -> a.range
  PrefixDirective d -> d.name.range
  PrefixModifier n -> n.range

data Declaration
  = DeclarationValue Prefix ValueDeclaration
  -- | A `data`, `newtype`, or `type` declaration, with its kind signature.
  | DeclarationType Prefix (Maybe Kind) Decl
  -- | An effect, a handler, a foreign, a foreign type, or a fixity.
  | DeclarationOther Prefix Decl
  -- | A macro called at a declaration's position, with the prefix before it.
  | DeclarationMacro Prefix Macro

-- | A value declaration, with its signature. A computation is one whose
-- | signature is a computation type at its top.
type ValueDeclaration =
  { name :: Name
  , signature :: Maybe Type
  , computation :: Boolean
  , binders :: Array Binder
  , body :: Expr
  , localBindings :: Array LocalBinding
  }

-- | A binding of a `let` block or of a declaration's `where`.
data LocalBinding
  = LocalValue { name :: Name, signature :: Maybe Type, binders :: Array Binder, body :: Expr }
  | LocalPattern Binder Expr

type GroupedModule =
  { name :: Name
  , exports :: Maybe (Array Export)
  , imports :: Array Import
  , declarations :: Array Declaration
  }

data GroupError = GroupError SourceRange GroupReason

data GroupReason
  -- | An attribute, a directive, or a modifier with no declaration after it.
  = NothingToAttachTo
  -- | `implicit` before anything but a handler declaration.
  | ModifierNotBeforeHandler
  -- | A signature not followed by the definition of its name.
  | SignatureWithoutDefinition
  -- | A second signature for the name a signature has just given one.
  | SignatureTwice
  -- | A kind signature not followed by a declaration of its name and keyword.
  | KindSignatureWithoutDeclaration
  -- | An import after a declaration has begun. The imports are the module's
  -- | header.
  | ImportAfterDeclaration
  -- | A name bound twice by one block of bindings.
  | BoundTwice
  -- | `#observ(none)` before anything but a `foreign` declaration.
  | DirectiveNotBeforeForeign
  -- | A second `#observ(none)` before one declaration.
  | DirectiveTwice

derive instance Eq PrefixItem
derive instance Eq GroupError
derive instance Eq GroupReason

instance Show GroupError where
  show (GroupError r reason) =
    "GroupError " <> show r.start.line <> ":" <> show r.start.column <> " " <> printGroupReason reason

instance Show GroupReason where
  show = case _ of
    NothingToAttachTo -> "NothingToAttachTo"
    ModifierNotBeforeHandler -> "ModifierNotBeforeHandler"
    SignatureWithoutDefinition -> "SignatureWithoutDefinition"
    SignatureTwice -> "SignatureTwice"
    KindSignatureWithoutDeclaration -> "KindSignatureWithoutDeclaration"
    ImportAfterDeclaration -> "ImportAfterDeclaration"
    BoundTwice -> "BoundTwice"
    DirectiveNotBeforeForeign -> "DirectiveNotBeforeForeign"
    DirectiveTwice -> "DirectiveTwice"

printGroupReason :: GroupReason -> String
printGroupReason = case _ of
  NothingToAttachTo -> "An attribute, a directive, or a modifier must stand before a declaration"
  ModifierNotBeforeHandler -> "`implicit` can stand only before a handler declaration"
  SignatureWithoutDefinition -> "A signature must be followed directly by the definition of its name"
  SignatureTwice -> "This name already has a signature"
  KindSignatureWithoutDeclaration ->
    "A kind signature must be followed directly by the declaration it gives a kind to"
  ImportAfterDeclaration -> "Imports must come before every declaration"
  BoundTwice -> "This name is already bound in the same block"
  DirectiveNotBeforeForeign -> "`#observ(none)` can stand only before a foreign declaration"
  DirectiveTwice -> "This declaration already has this directive"

-- | Whether a signature makes its declaration a computation: a computation
-- | type at the end of its spine, after its quantifiers, constraints, and
-- | synthesized arguments. The arrow after a synthesized argument is pure, so a
-- | `/` following it belongs to the computation type. Parentheses around the
-- | rest of the spine change nothing, there being no arrow for them to part it
-- | from.
isComputationSignature :: Type -> Boolean
isComputationSignature = case _ of
  TypeForall _ t -> isComputationSignature t
  TypeConstrained _ t -> isComputationSignature t
  TypeParens t -> isComputationSignature t
  TypeArrow a t | isSynthesized a -> isComputationSignature t
  TypeEffect _ _ _ -> true
  _ -> false

-- | A signature, or a kind signature, waiting for the declaration it belongs
-- | to, with the prefix written before it.
type PendingSignature = { prefix :: Prefix, name :: Name, type :: Type }

type PendingKind = { prefix :: Prefix, keyword :: DeclKeyword, name :: Name, kind :: Kind }

type State =
  { prefix :: Prefix
  , signature :: Maybe PendingSignature
  , kindSignature :: Maybe PendingKind
  , imports :: Array Import
  , declarations :: Array Declaration
  -- | Whether a declaration has begun, which closes the header.
  , inBody :: Boolean
  , errors :: Array GroupError
  }

groupModule :: Module -> { grouped :: GroupedModule, errors :: Array GroupError }
groupModule (Module m) =
  { grouped: { name: m.name, exports: m.exports, imports: final.imports, declarations: final.declarations }
  , errors: final.errors
  }
  where
  -- What is still pending at the end of the module has nothing after it.
  final = unattached (foldl step initial m.items)
  initial =
    { prefix: [], signature: Nothing, kindSignature: Nothing, imports: [], declarations: [], inBody: false, errors: [] }

step :: State -> Item -> State
step s = case _ of
  ItemImport i@(Import r) ->
    let
      s' = unattached s
    in
      s'
        { imports = Array.snoc s'.imports i
        , errors = s'.errors <> if s.inBody then [ GroupError r.module.range ImportAfterDeclaration ] else []
        }
  ItemAttribute a -> s { prefix = Array.snoc s.prefix (PrefixAttribute a) }
  ItemDirective d -> s { prefix = Array.snoc s.prefix (PrefixDirective d) }
  ItemModifier n -> s { prefix = Array.snoc s.prefix (PrefixModifier n) }
  ItemMacro mac -> declare (DeclarationMacro s.prefix mac) (unmatched s)
  -- An item the parser could not read parts what stands on either side of
  -- it. Whatever it would have been is reported where it was read, so what
  -- was waiting for it is dropped without a report of its own.
  ItemBroken _ -> s { prefix = [], signature = Nothing, kindSignature = Nothing }
  ItemDecl d -> decl d s

decl :: Decl -> State -> State
decl d s = case d of
  DeclSignature n t -> case s.signature of
    Just sig | sig.name.name == n.name ->
      -- The second signature is dropped, and the prefix written before it with it.
      s { prefix = [], inBody = true, errors = Array.snoc s.errors (GroupError n.range SignatureTwice) }
    _ ->
      let
        s' = unmatched s
      in
        s' { prefix = [], signature = Just { prefix: s.prefix, name: n, type: t }, inBody = true }
  DeclKindSignature keyword n k ->
    let
      s' = unmatched s
    in
      s' { prefix = [], kindSignature = Just { prefix: s.prefix, keyword, name: n, kind: k }, inBody = true }
  DeclValue n binders body localBindings -> case s.signature of
    Just sig | sig.name.name == n.name ->
      value (sig.prefix <> s.prefix) (Just sig.type) (unmatched (s { signature = Nothing }))
    _ -> value s.prefix Nothing (unmatched s)
    where
    value prefix signature s' =
      let
        grouped = maybe { bindings: [], errors: [] } groupBindings localBindings
      in
        declare
          ( DeclarationValue prefix
              { name: n
              , signature
              , computation: maybe false isComputationSignature signature
              , binders
              , body
              , localBindings: grouped.bindings
              }
          )
          (s' { errors = s'.errors <> grouped.errors })
  DeclData n _ _ -> typeLevel KeywordData n
  DeclNewtype n _ _ _ -> typeLevel KeywordNewtype n
  DeclType n _ _ -> typeLevel KeywordType n
  _ -> declare (DeclarationOther s.prefix d) (unmatched s)
  where
  typeLevel keyword n = case s.kindSignature of
    Just ks | ks.keyword == keyword && ks.name.name == n.name ->
      declare (DeclarationType (ks.prefix <> s.prefix) (Just ks.kind) d) (unmatched (s { kindSignature = Nothing }))
    _ -> declare (DeclarationType s.prefix Nothing d) (unmatched s)

-- | Records a declaration, the pending prefix having gone into it.
declare :: Declaration -> State -> State
declare d s = s
  { declarations = Array.snoc s.declarations d
  , inBody = true
  , prefix = []
  , errors = s.errors <> modifierErrors d <> directiveErrors d
  }

-- | A modifier is `implicit`, which stands before a handler declaration alone.
-- | One before a macro call is kept with the call, its meaning the macro's.
modifierErrors :: Declaration -> Array GroupError
modifierErrors = case _ of
  DeclarationValue p _ -> misplaced p
  DeclarationType p _ _ -> misplaced p
  DeclarationOther _ (DeclHandler _ _ _ _) -> []
  DeclarationOther p _ -> misplaced p
  DeclarationMacro _ _ -> []
  where
  misplaced p = map (\n -> GroupError n.range ModifierNotBeforeHandler) (modifiersOf p)

-- | `#observ(none)`, the one directive a declaration may have, stands before a
-- | foreign declaration, once. One before a macro call is kept with the call.
directiveErrors :: Declaration -> Array GroupError
directiveErrors = case _ of
  DeclarationOther p (DeclForeign _ _) -> map (\d -> GroupError d.name.range DirectiveTwice) (Array.drop 1 (directivesOf p))
  DeclarationMacro _ _ -> []
  DeclarationValue p _ -> misplaced p
  DeclarationType p _ _ -> misplaced p
  DeclarationOther p _ -> misplaced p
  where
  misplaced p = map (\d -> GroupError d.name.range DirectiveNotBeforeForeign) (directivesOf p)

-- | A signature or a kind signature still waiting where something other than
-- | its own declaration comes belongs to nothing. It is reported, and the
-- | prefix written before it goes with it.
unmatched :: State -> State
unmatched s = s
  { signature = Nothing
  , kindSignature = Nothing
  , errors = s.errors <> signatureError <> kindError
  }
  where
  signatureError = case s.signature of
    Just sig -> [ GroupError sig.name.range SignatureWithoutDefinition ]
    Nothing -> []
  kindError = case s.kindSignature of
    Just ks -> [ GroupError ks.name.range KindSignatureWithoutDeclaration ]
    Nothing -> []

-- | A prefix and signatures with nothing after them to attach to.
unattached :: State -> State
unattached s =
  let
    s' = unmatched s
  in
    s'
      { prefix = []
      , errors = s'.errors <> map (\p -> GroupError (prefixItemRange p) NothingToAttachTo) s.prefix
      }

-- | The bindings of a `let` block or a `where`, each signature joined to the
-- | definition after it. Every name of the block is bound once, whether by a
-- | definition or by a variable of a pattern.
groupBindings :: Array LetBinding -> { bindings :: Array LocalBinding, errors :: Array GroupError }
groupBindings items = finish (foldl stepBinding start items)
  where
  start = { pendingSignature: Nothing, bindings: [], errors: [], bound: Set.empty }

  finish b = { bindings: b.bindings, errors: b.errors <> unused b.pendingSignature }

  unused = case _ of
    Just sig -> [ GroupError sig.name.range SignatureWithoutDefinition ]
    Nothing -> []

  stepBinding b = case _ of
    LetSignature n t -> case b.pendingSignature of
      Just sig | sig.name.name == n.name -> b { errors = Array.snoc b.errors (GroupError n.range SignatureTwice) }
      pending -> b { pendingSignature = Just { name: n, type: t }, errors = b.errors <> unused pending }
    LetValue n binders body ->
      let
        signature = case b.pendingSignature of
          Just sig | sig.name.name == n.name -> Just sig.type
          _ -> Nothing
        errors = if signature == Nothing then unused b.pendingSignature else []
      in
        binding [ n ] (LocalValue { name: n, signature, binders, body }) (b { errors = b.errors <> errors })
    LetPattern binder body ->
      binding (variablesOf binder) (LocalPattern binder body) (b { errors = b.errors <> unused b.pendingSignature })

  binding names lb b =
    let
      bound = foldl (\acc n -> acc { seen = Set.insert n.name acc.seen, twice = acc.twice <> if Set.member n.name acc.seen then [ n ] else [] })
        { seen: b.bound, twice: [] }
        names
    in
      b
        { pendingSignature = Nothing
        , bindings = Array.snoc b.bindings lb
        , bound = bound.seen
        , errors = b.errors <> map (\n -> GroupError n.range BoundTwice) bound.twice
        }

-- | The variables a pattern binds, in the order written.
variablesOf :: Binder -> Array Name
variablesOf = case _ of
  BinderVar n -> [ n ]
  BinderAs n b -> [ n ] <> variablesOf b
  BinderConstructor _ bs -> Array.concatMap variablesOf bs
  BinderTag _ bs -> Array.concatMap variablesOf bs
  BinderParens b -> variablesOf b
  BinderTuple bs -> Array.concatMap variablesOf bs
  -- An or-pattern binds nothing; one that would is rejected where patterns are
  -- resolved.
  BinderOr _ -> []
  BinderRecord _ fs -> Array.concatMap field fs
  BinderTyped b _ -> variablesOf b
  BinderApp _ _ -> []
  BinderInvalid _ -> []
  BinderWildcard _ -> []
  BinderBoolean _ _ -> []
  BinderInt _ -> []
  BinderNumber _ -> []
  BinderChar _ -> []
  BinderString _ -> []
  BinderUnit _ -> []
  where
  field = case _ of
    RecordBinderField _ b -> variablesOf b
    RecordBinderPun n -> [ n ]
    RecordBinderRest _ (Just n) -> [ n ]
    RecordBinderRest _ Nothing -> []
