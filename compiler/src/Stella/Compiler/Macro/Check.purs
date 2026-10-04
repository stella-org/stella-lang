-- | Whether a macro a module imports is one a call may run
-- | ([Syntax Extensions and Parsers](../../../../docs/proposals/09-Syntax-Extensions-and-Parsers.md)).
-- |
-- | **A macro is a value carrying `Prim.macro` whose scheme is exactly
-- | `Stella.Syntax.Parser (Stella.Syntax.Syntax Stella.Syntax.Term)`**: no kind
-- | variable, no quantifier, no constraint, and nothing on its spine beyond Core.
-- | The scheme is read from the interface of the module declaring the value,
-- | where every synonym it mentions is expanded, and the category of what the
-- | macro produces, `Term`, is read from it.
-- |
-- | This is the compiler's half of the check. The session running the macro
-- | holds no type, and checks what the value is at run time instead.
module Stella.Compiler.Macro.Check
  ( Category(..)
  , MacroRefusal(..)
  , checkMacro
  ) where

import Prelude
import Prim hiding (Type)

import Data.Array as Array
import Data.Either (Either(..))
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..))
import Data.Show.Generic (genericShow)
import Stella.Compiler.Interface.Environment (ModuleView, lookupValue)
import Stella.Compiler.Interface.Module (ValueSort(..))
import Stella.Compiler.Interface.Scheme (Scheme, SchemeBody(..))
import Stella.Compiler.Macro.Bundle (syntaxModuleName)
import Stella.Compiler.TypedCore.Name (Ident(..), Qualified(..), TyName(..))
import Stella.Compiler.TypedCore.Prim (primModule)
import Stella.Compiler.TypedCore.Type (Type(..))

-- | What a macro produces.
data Category = TermCategory

-- | Why the value a macro name stands for is not a macro a call may run, as
-- | that value.
data MacroRefusal
  -- | No module the view reaches declares it.
  = MacroUndeclared (Qualified Ident)
  -- | It is declared, and is not a value: a constructor, a foreign, an
  -- | operation, or a handler.
  | MacroNotAValue (Qualified Ident)
  -- | It is a value that does not carry `Prim.macro`.
  | MacroNotMarked (Qualified Ident)
  -- | Its scheme is not exactly that of a parser of terms.
  | MacroNotAParser (Qualified Ident) Scheme

checkMacro :: ModuleView -> Qualified Ident -> Either MacroRefusal Category
checkMacro view name = case lookupValue name view of
  Nothing -> Left (MacroUndeclared name)
  Just entry -> case entry.sort of
    SortValue
      | not (Array.any (\a -> a.name == primMacro) entry.attributes) -> Left (MacroNotMarked name)
      | Array.null entry.scheme.kindVars, Plain ty <- entry.scheme.body, isTermParser ty -> Right TermCategory
      | otherwise -> Left (MacroNotAParser name entry.scheme)
    _ -> Left (MacroNotAValue name)

primMacro :: Qualified Ident
primMacro = Qualified primModule (Ident "macro")

-- | `Parser (Syntax Term)`, each of the three applied to no kind.
isTermParser :: Type -> Boolean
isTermParser = case _ of
  TApp (TCon parser []) (TApp (TCon syntax []) (TCon term []))
  -> parser == syntaxType "Parser" && syntax == syntaxType "Syntax" && term == syntaxType "Term"
  _ -> false

syntaxType :: String -> Qualified TyName
syntaxType = Qualified syntaxModuleName <<< TyName

derive instance Eq Category
derive instance Generic Category _
instance Show Category where
  show = genericShow

derive instance Eq MacroRefusal
derive instance Generic MacroRefusal _
instance Show MacroRefusal where
  show = genericShow
