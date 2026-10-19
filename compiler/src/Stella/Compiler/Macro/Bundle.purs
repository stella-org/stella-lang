-- | `Stella.Syntax`: what a macro is written against
-- | ([Syntax Extensions and Parsers](../../../../docs/proposals/09-Syntax-Extensions-and-Parsers.md)),
-- | as the compiler and a host refer to it. The module is written in source
-- | (`stella-packages/compiler-lib/src/Stella/Syntax.stel`), and the compiler
-- | carries what a build of it writes ([Compiled](Compiled.purs)).
-- |
-- | **A macro is a parser**, a value of type `Parser (Syntax c)`: it reads the
-- | token tree of its call and produces syntax of the category `c`. The types
-- | there mirror the host's ([Tree](Tree.purs)) constructor for constructor.
-- |
-- | **An origin says where a token or a node came from, for diagnostics
-- | alone**: the input of the call, by a reference the host issued for it,
-- | `InputOrigin`, which nothing a parser writes can make; or a quotation,
-- | `$QuotedOrigin`, by the module and the range it declares. `OriginRef` is
-- | exported abstract. `$QuotedOrigin` and `$spliced`, which a quotation is
-- | written with, are elaboration-only entries: their names are no identifier,
-- | and they are in no export of the module's interface, so neither source nor
-- | a synthesizer reaches them.
module Stella.Compiler.Macro.Bundle
  ( syntaxModuleName
  , originRefTy
  , issuedOriginTy
  , describeSyntax
  ) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Either (Either)
import Stella.Compiler.Elaborate.Protocol.Guest.Shape (Descriptor, describeInterface)
import Stella.Compiler.Interface.Module (ModuleInterface)
import Stella.Compiler.TypedCore (ModuleName(..), Qualified(..), TyName(..))

syntaxModuleName :: ModuleName
syntaxModuleName = ModuleName "Stella.Syntax"

-- | `Stella.Syntax.OriginRef`: where a token or a node came from.
originRefTy :: Qualified TyName
originRefTy = Qualified syntaxModuleName (TyName "OriginRef")

-- | `Stella.Syntax.IssuedOrigin`, an opaque foreign type: a reference the host
-- | issues for a token of a call's input, which nothing a parser writes can
-- | make.
issuedOriginTy :: Qualified TyName
issuedOriginTy = Qualified syntaxModuleName (TyName "IssuedOrigin")

-- | The shape descriptor of the types a value crossing to the host has, read
-- | off the interface of `Stella.Syntax`: the token tree a parser reads, the
-- | syntax it builds, and how it came out. A parser itself is a function, and
-- | never crosses, nor does the state it runs over.
describeSyntax :: ModuleInterface -> Either P.String Descriptor
describeSyntax = describeInterface issuedOriginTy crossing
  where
  crossing name = not (Array.elem name (map TyName [ "State", "Reply", "Parser", "LayoutItem", "Block", "ItemRun" ]))
