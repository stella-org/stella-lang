-- | Names of Typed Core.
-- |
-- | Name resolution and hygiene are complete by the time a term reaches Core,
-- | so these types carry neither scope information nor expansion traces.
module Stella.Compiler.TypedCore.Name
  ( ModuleName(..)
  , Ident(..)
  , TyName(..)
  , TyVar(..)
  , KindVar(..)
  , Symbol(..)
  , Tag(..)
  , EffName(..)
  , OpName(..)
  , JoinName(..)
  , RegionName(..)
  , Qualified(..)
  , qualifier
  , unqualified
  ) where

import Prelude

-- `Prim` is imported qualified, which replaces its implicit open import. `Symbol`
-- here is a written name, not the `Prim` kind of that spelling.
import Prim as P

import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

-- | A fully qualified module name, written with its segments joined by dots.
newtype ModuleName = ModuleName P.String

-- | A value-level identifier.
-- |
-- | Data constructors live in this namespace: a constructor is an ordinary
-- | global name whose type, tag, and arity the declaration table records.
newtype Ident = Ident P.String

-- | A type constructor name.
newtype TyName = TyName P.String

-- | A type variable.
newtype TyVar = TyVar P.String

-- | A kind variable. Kind schemes are prenex, so a kind variable is bound only
-- | by a declaration (D3).
newtype KindVar = KindVar P.String

-- | A written field or instance name, which is the `Symbol` of a `SymbolKey`.
-- |
-- | Not a kind: the `Symbol` D13 speaks of is the spelling itself, written in
-- | the row and nowhere else.
newtype Symbol = Symbol P.String

-- | A structural constructor of a variant, which is the `Tag` of a `TagKey`.
-- |
-- | Nothing declares a tag. Two occurrences of one spelling, in modules that
-- | know nothing of each other, are the same key (D16).
newtype Tag = Tag P.String

-- | An effect constructor name. It heads the payload of every `Row Effect`
-- | element, and is the key of one for which none is written.
newtype EffName = EffName P.String

-- | An effect operation name, unique within its effect declaration.
newtype OpName = OpName P.String

-- | A join point name. Join points are not first class and do not cross a
-- | function boundary.
newtype JoinName = JoinName P.String

-- | A region name, written `ℓ`. It is not a type and has no kind: it is bound by
-- | the `region` binder of a term, and names the region whose cells a `readCell`
-- | or `writeCell` reaches. No type or term abstracts over one, so a region name
-- | is never the target of an instantiation.
newtype RegionName = RegionName P.String

-- | A name owned by a module. Every Core name that refers to a declaration is
-- | qualified; local names introduced by binders are not.
data Qualified a = Qualified ModuleName a

qualifier :: forall a. Qualified a -> ModuleName
qualifier (Qualified m _) = m

unqualified :: forall a. Qualified a -> a
unqualified (Qualified _ a) = a

derive instance Eq ModuleName
derive instance Ord ModuleName
derive newtype instance Show ModuleName

derive instance Eq Ident
derive instance Ord Ident
derive newtype instance Show Ident

derive instance Eq TyName
derive instance Ord TyName
derive newtype instance Show TyName

derive instance Eq TyVar
derive instance Ord TyVar
derive newtype instance Show TyVar

derive instance Eq KindVar
derive instance Ord KindVar
derive newtype instance Show KindVar

derive instance Eq Symbol
derive instance Ord Symbol
derive newtype instance Show Symbol

derive instance Eq Tag
derive instance Ord Tag
derive newtype instance Show Tag

derive instance Eq EffName
derive instance Ord EffName
derive newtype instance Show EffName

derive instance Eq OpName
derive instance Ord OpName
derive newtype instance Show OpName

derive instance Eq JoinName
derive instance Ord JoinName
derive newtype instance Show JoinName

derive instance Eq RegionName
derive instance Ord RegionName
derive newtype instance Show RegionName

derive instance Eq a => Eq (Qualified a)
derive instance Ord a => Ord (Qualified a)
derive instance Functor Qualified
derive instance Generic (Qualified a) _

instance Show a => Show (Qualified a) where
  show = genericShow
