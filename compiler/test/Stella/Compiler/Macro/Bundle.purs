-- | `Stella.Syntax`: the module checks as Core against a signature holding its
-- | opaque origin type and `Base.Int`, and the types a value crossing to the host
-- | has mirror the host's constructor for constructor.
module Test.Stella.Compiler.Macro.Bundle (spec) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Either (Either(..), isLeft)
import Data.Generic.Rep (class Generic, Argument, Constructor, NoArguments, Product, Sum)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Symbol (class IsSymbol, reflectSymbol)
import Data.Tuple (Tuple(..))
import Stella.Compiler.Elaborate.Protocol.Guest.Shape (Descriptor, Shape(..))
import Stella.Compiler.Elaborate.Surface.Internal (internalEntries)
import Stella.Compiler.Macro.Bundle (bundle, syntaxModule, syntaxModuleName, withSyntax)
import Stella.Compiler.Macro.Compiled (compiled)
import Stella.Compiler.Macro.Tree (Delimiter, Failure, IssuedOrigin, OriginRef, Position, Range, Result, Syntax, SyntaxItem, SyntaxNode, Token, TokenKind, TokenTree, Trivia)
import Stella.Compiler.TypedCore (Ident(..), Qualified(..), TyName(..), Type(..), declare, declareAnnotated, primSignature)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)
import Test.Stella.Compiler.Fixtures.Programs (intModule)
import Type.Proxy (Proxy(..))

-- The shape of a host type's field ---------------------------------------------------------

class HostShape :: P.Type -> P.Constraint
class HostShape a where
  hostShape :: Proxy a -> Shape

twin :: P.String -> Shape
twin n = ShapeData (Qualified syntaxModuleName (TyName n)) []

instance HostShape P.Int where
  hostShape _ = ShapeInt

instance HostShape P.Number where
  hostShape _ = ShapeNumber

instance HostShape P.String where
  hostShape _ = ShapeString

instance HostShape IssuedOrigin where
  hostShape _ = ShapeToken

instance HostShape OriginRef where
  hostShape _ = twin "OriginRef"

instance HostShape a => HostShape (Maybe a) where
  hostShape _ = ShapeData (Qualified syntaxModuleName (TyName "Maybe")) [ hostShape (Proxy :: Proxy a) ]

instance HostShape a => HostShape (P.Array a) where
  hostShape _ = ShapeData (Qualified syntaxModuleName (TyName "List")) [ hostShape (Proxy :: Proxy a) ]

instance HostShape Position where
  hostShape _ = twin "Position"

instance HostShape Range where
  hostShape _ = twin "Range"

instance HostShape Trivia where
  hostShape _ = twin "Trivia"

instance HostShape TokenKind where
  hostShape _ = twin "TokenKind"

instance HostShape Token where
  hostShape _ = twin "Token"

instance HostShape Delimiter where
  hostShape _ = twin "Delimiter"

instance HostShape TokenTree where
  hostShape _ = twin "TokenTree"

instance HostShape SyntaxNode where
  hostShape _ = twin "SyntaxNode"

instance HostShape SyntaxItem where
  hostShape _ = twin "SyntaxItem"

instance HostShape Failure where
  hostShape _ = twin "Failure"

-- | The parameter of a mirrored type, at the position given.
data Param0

instance HostShape Param0 where
  hostShape _ = ShapeParam 0

type CtorEntry = { name :: P.String, fields :: P.Array Shape }

class Ctors :: forall k. k -> P.Constraint
class Ctors rep where
  ctors :: Proxy rep -> P.Array CtorEntry

instance (Ctors a, Ctors b) => Ctors (Sum a b) where
  ctors _ = ctors (Proxy :: Proxy a) <> ctors (Proxy :: Proxy b)

instance (IsSymbol name, Fields a) => Ctors (Constructor name a) where
  ctors _ = [ { name: reflectSymbol (Proxy :: Proxy name), fields: fields (Proxy :: Proxy a) } ]

class Fields :: forall k. k -> P.Constraint
class Fields rep where
  fields :: Proxy rep -> P.Array Shape

instance Fields NoArguments where
  fields _ = []

instance HostShape a => Fields (Argument a) where
  fields _ = [ hostShape (Proxy :: Proxy a) ]

instance (Fields a, Fields b) => Fields (Product a b) where
  fields _ = fields (Proxy :: Proxy a) <> fields (Proxy :: Proxy b)

hostCtors :: forall a rep. Generic a rep => Ctors rep => Proxy a -> P.Array CtorEntry
hostCtors _ = ctors (Proxy :: Proxy rep)

guestCtors :: Descriptor -> P.String -> Maybe (P.Array CtorEntry)
guestCtors descriptor n = Map.lookup (Qualified syntaxModuleName (TyName n)) descriptor <#>
  \t -> map (\c -> { name: unIdent c.name, fields: c.fields }) t.constructors
  where
  unIdent (Qualified _ (Ident x)) = x

-- | Every host type a value crossing to the host is built of, and its twin's name.
mirrored :: P.Array (Tuple P.String (P.Array CtorEntry))
mirrored =
  [ Tuple "Position" (hostCtors (Proxy :: Proxy Position))
  , Tuple "Range" (hostCtors (Proxy :: Proxy Range))
  , Tuple "Trivia" (hostCtors (Proxy :: Proxy Trivia))
  , Tuple "TokenKind" (hostCtors (Proxy :: Proxy TokenKind))
  -- the host's `QuotedOrigin` is the elaboration-only `$QuotedOrigin`
  , Tuple "OriginRef" (map (\c -> if c.name == "QuotedOrigin" then c { name = "$QuotedOrigin" } else c) (hostCtors (Proxy :: Proxy OriginRef)))
  , Tuple "Token" (hostCtors (Proxy :: Proxy Token))
  , Tuple "Delimiter" (hostCtors (Proxy :: Proxy Delimiter))
  , Tuple "TokenTree" (hostCtors (Proxy :: Proxy TokenTree))
  , Tuple "SyntaxNode" (hostCtors (Proxy :: Proxy SyntaxNode))
  , Tuple "SyntaxItem" (hostCtors (Proxy :: Proxy SyntaxItem))
  , Tuple "Syntax" (hostCtors (Proxy :: Proxy (Syntax Param0)))
  , Tuple "Failure" (hostCtors (Proxy :: Proxy Failure))
  , Tuple "Result" (hostCtors (Proxy :: Proxy (Result Param0)))
  ]

spec :: Spec Unit
spec = describe "Stella.Compiler.Macro.Bundle" do
  it "declares against a signature holding its origin type and Base.Int" do
    case declare primSignature intModule of
      Left e -> fail (show e)
      Right withInt -> do
        case declareAnnotated (withSyntax withInt) syntaxModule of
          Left e -> fail (show e)
          Right _ -> pure unit
        isLeft (declareAnnotated withInt syntaxModule) `shouldEqual` true

  it "describes what crosses to the host, and the host's types mirror it constructor for constructor" do
    case bundle of
      Left e -> fail e
      Right b -> do
        Array.filter (\(Tuple n host) -> guestCtors b.descriptor n /= Just host) mirrored `shouldEqual` []
        -- the category has no value, on either side
        guestCtors b.descriptor "Term" `shouldEqual` Just []
        -- a parser is a function, and its types do not cross
        Map.member (Qualified syntaxModuleName (TyName "Parser")) b.descriptor `shouldEqual` false

  it "holds what a quotation is written with at the schemes the compiler lists, and lacking either or holding another is its fault" do
    case compiled of
      Left e -> fail e
      Right c -> do
        map (Array.fromFoldable <<< Map.keys) (internalEntries c.signature)
          `shouldEqual` Right (map (Qualified syntaxModuleName <<< Ident) [ "$QuotedOrigin", "$spliced" ])
        let
          spliced = Qualified syntaxModuleName (Ident "$spliced")
          changed = c.signature { values = Map.update (\v -> Just v { scheme = { kindVars: [], body: TCon (Qualified syntaxModuleName (TyName "Term")) [] } }) spliced c.signature.values }
        internalEntries changed `shouldEqual` Left spliced
        -- reaching Stella.Syntax, a signature lacking either entry is as wrong
        let
          quotedOrigin = Qualified syntaxModuleName (Ident "$QuotedOrigin")
        internalEntries c.signature { values = Map.delete spliced c.signature.values } `shouldEqual` Left spliced
        internalEntries c.signature { ctors = Map.delete quotedOrigin c.signature.ctors } `shouldEqual` Left quotedOrigin
        -- a signature that does not reach Stella.Syntax holds none
        map Map.isEmpty (internalEntries primSignature) `shouldEqual` Right true
