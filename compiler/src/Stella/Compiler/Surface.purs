-- | The Surface AST.
-- |
-- | What name resolution builds from the concrete syntax tree and elaboration
-- | reads. It is expanded and resolved: it holds no macro call and no
-- | unresolved name, every global is qualified by the module declaring it, and
-- | every local is the binding it refers to. Every node carries its origin.
-- |
-- | Resolution goes on past an error and reports every one. An error in an
-- | expression, a type, a kind, a pattern, or a constant leaves an invalid node
-- | of that class; any other drops the smallest member of a sequence around it,
-- | a declaration or a clause among them. A module with an error is not
-- | elaborated.
module Stella.Compiler.Surface
  ( module Stella.Compiler.Surface.Origin
  , module Stella.Compiler.Surface.Name
  , module Stella.Compiler.Surface.Type
  , module Stella.Compiler.Surface.Expr
  , module Stella.Compiler.Surface.Decl
  ) where

-- Re-exporting `Type` shadows the `Prim` name of that spelling, so `Prim` is
-- imported qualified here as well.
import Prim as P

import Stella.Compiler.Surface.Decl (Associativity(..), Attribute, AttributeDeclaration, ComputationDeclaration, Constant(..), ConstructorDeclaration, DataDeclaration, Declaration(..), EffectDeclaration, FixityDeclaration, FixityTarget(..), ForeignDeclaration, ForeignTypeDeclaration, HandlerDeclaration, Import, KeywordArgument, KeywordParameter, Module, NewtypeDeclaration, Observation(..), OperationDeclaration, SynonymDeclaration, TypeFixityDeclaration, ValueDeclaration, constantOrigin, declarationOrigin)
import Stella.Compiler.Surface.Expr (Alternative, AlternativeBody(..), Binder(..), CellDeclaration, ClauseForm(..), Expr(..), Group, GuardLine(..), HandlerBody, HandlerItem(..), LetBinding(..), OperationClause, RecordBinderField, RecordField(..), RecordRest, ReturnClause, binderOrigin, exprOrigin)
import Stella.Compiler.Surface.Name (BindingId(..), CellVar(..), LocalVar(..), OperatorName(..), TypeVar(..))
import Stella.Compiler.Surface.Origin (Origin(..), rangeOf, spanning)
import Stella.Compiler.Surface.Type (ComputationType, EffectApplication, EffectRowItem(..), HandlerSignature(..), Kind(..), OperationSignature, RecordRowItem(..), Signature, SignaturePrefix(..), Type(..), TypeOperatorTarget(..), TypeVarBinder, VariantRowItem(..), kindOrigin, typeOrigin)
