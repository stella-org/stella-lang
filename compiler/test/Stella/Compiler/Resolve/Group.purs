-- | The items of a module grouped into declarations, and what grouping reports.
module Test.Stella.Compiler.Resolve.Group (spec) where

import Prelude
import Prim hiding (Type)

import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.String (joinWith)
import Effect.Aff (Aff)
import Stella.Compiler.CST (parseModule, printSyntaxError)
import Stella.Compiler.CST.Types (Decl(..), Item(..), Module(..), Name)
import Stella.Compiler.Resolve.Group (Declaration(..), GroupError(..), GroupReason(..), LocalBinding(..), Prefix, PrefixItem(..), groupModule)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

-- | A module whose body is the lines given, grouped: each declaration in a
-- | line, and each error with where it stands.
grouped
  :: Array String
  -> Array String
  -> Array { line :: Int, column :: Int, reason :: GroupReason }
  -> Aff Unit
grouped body declarations errors = case parseModule (joinWith "\n" ([ "module M where" ] <> body)) of
  Left e -> fail (printSyntaxError e)
  Right m -> do
    let g = groupModule m
    map sketch g.grouped.declarations `shouldEqual` declarations
    map found g.errors `shouldEqual` errors
  where
  found (GroupError r reason) = { line: r.start.line, column: r.start.column, reason }

sketch :: Declaration -> String
sketch = case _ of
  DeclarationValue p v ->
    words
      ( prefix p <> [ "value", v.name.name ]
          <> (if v.signature == Nothing then [] else [ "signed" ])
          <> (if v.computation then [ "computation" ] else [])
          <> map local v.localBindings
      )
  DeclarationType p kind d ->
    words (prefix p <> [ keyword d, nameOf d ] <> if kind == Nothing then [] else [ "kinded" ])
  DeclarationOther p d -> words (prefix p <> [ "other", nameOf d ])
  DeclarationMacro p m -> words (prefix p <> [ "macro", m.name.name ])
  where
  words = joinWith " "
  local = case _ of
    LocalValue l -> "[" <> l.name.name <> (if l.signature == Nothing then "" else " signed") <> "]"
    LocalPattern _ _ -> "[pattern]"
  keyword = case _ of
    DeclData _ _ _ -> "data"
    DeclNewtype _ _ _ _ -> "newtype"
    _ -> "type"

prefix :: Prefix -> Array String
prefix = map case _ of
  PrefixAttribute a -> "@" <> written a.name
  PrefixDirective d -> "#" <> d.name.name
  PrefixModifier n -> n.name

nameOf :: Decl -> String
nameOf = case _ of
  DeclSignature n _ -> n.name
  DeclValue n _ _ _ -> n.name
  DeclData n _ _ -> n.name
  DeclNewtype n _ _ _ -> n.name
  DeclType n _ _ -> n.name
  DeclKindSignature _ n _ -> n.name
  DeclEffect n _ _ -> n.name
  DeclHandler n _ _ _ -> n.name
  DeclForeign n _ -> n.name
  DeclForeignType n _ -> n.name
  DeclFixity _ _ _ (n :: Name) -> n.name
  DeclAttribute n _ -> n.name

written :: Name -> String
written n = case n.qualifier of
  Nothing -> n.name
  Just q -> q <> "." <> n.name

spec :: Spec Unit
spec = describe "Stella.Compiler.Resolve.Group" do
  describe "prefixes" do
    it "join the declaration after them, from before its signature and before its definition" do
      grouped
        [ "@[entrypoint]"
        , "main :: Unit / {| Console |}"
        , "@[other]"
        , "main = log \"x\""
        , "#observ(none) foreign sqrt :: Number -> Number"
        , "implicit"
        , "handler h :: E ~> () where"
        , "  fast | op _ -> 0"
        ]
        [ "@entrypoint @other value main signed computation"
        , "#observ other sqrt"
        , "implicit other h"
        ]
        []

    it "are reported where nothing follows them, or an import does" do
      grouped
        [ "@[a]"
        , "import N"
        , "x = 1"
        , "#inline"
        ]
        [ "value x" ]
        [ { line: 2, column: 1, reason: NothingToAttachTo }
        , { line: 5, column: 1, reason: NothingToAttachTo }
        ]

    it "report `implicit` before anything but a handler" do
      grouped
        [ "implicit"
        , "x = 1"
        ]
        [ "implicit value x" ]
        [ { line: 2, column: 1, reason: ModifierNotBeforeHandler } ]

    it "keep the order they were written in, whatever kind each is" do
      grouped
        [ "@[a]"
        , "#observ(none)"
        , "@[b]"
        , "foreign f :: Int -> Int"
        ]
        [ "@a #observ @b other f" ]
        []

    it "before a signature go with it, and to nothing else where its definition does not follow" do
      grouped
        [ "@[a]"
        , "x :: Int"
        , "@[b]"
        , "y = 1"
        , "@[c]"
        , "type T :: Type"
        , "data U = U"
        ]
        [ "@b value y", "data U" ]
        [ { line: 3, column: 1, reason: SignatureWithoutDefinition }
        , { line: 7, column: 6, reason: KindSignatureWithoutDeclaration }
        ]

    it "stay with a macro called at a declaration's position, and pass on to nothing after it" do
      grouped
        [ "@[a]"
        , "implicit"
        , "class%{ Show a where show :: a -> String }"
        , "x = 1"
        ]
        [ "@a implicit macro class", "value x" ]
        []

  describe "signatures" do
    it "make a declaration a computation only with a computation type at their top" do
      grouped
        [ "f :: Int -> Int / {| E |}"
        , "f x = x"
        , "c :: forall a. Show a => a / {| E |}"
        , "c = 1"
        , "v = 1"
        , "p :: ((Int / {| E |}))"
        , "p = 1"
        ]
        [ "value f signed", "value c signed computation", "value v", "value p signed computation" ]
        []

    it "are reported where the definition of their name does not follow them directly" do
      grouped
        [ "x :: Int"
        , "y = 1"
        , "x = 2"
        , "z :: Int"
        ]
        [ "value y", "value x" ]
        [ { line: 2, column: 1, reason: SignatureWithoutDefinition }
        , { line: 5, column: 1, reason: SignatureWithoutDefinition }
        ]

    it "are reported given twice, the second dropped with the prefix before it" do
      grouped
        [ "@[a]"
        , "x :: Int"
        , "@[b]"
        , "x :: Int"
        , "x = 1"
        ]
        [ "@a value x signed" ]
        [ { line: 5, column: 1, reason: SignatureTwice } ]

    it "of a kind join a declaration of their keyword and name" do
      grouped
        [ "data Proxy :: k -> Type"
        , "data Proxy a = Proxy"
        , "type T :: Type"
        , "data T = T"
        ]
        [ "data Proxy kinded", "data T" ]
        [ { line: 4, column: 6, reason: KindSignatureWithoutDeclaration } ]

  describe "directives" do
    it "report `#observ(none)` before anything but a foreign, and given twice" do
      grouped
        [ "#observ(none)"
        , "x = 1"
        , "#observ(none)"
        , "#observ(none)"
        , "foreign f :: Int -> Int"
        ]
        [ "#observ value x", "#observ #observ other f" ]
        [ { line: 2, column: 1, reason: DirectiveNotBeforeForeign }
        , { line: 5, column: 1, reason: DirectiveTwice }
        ]

  describe "imports" do
    it "are reported after a declaration" do
      grouped
        [ "import A"
        , "x = 1"
        , "import B"
        ]
        [ "value x" ]
        [ { line: 4, column: 8, reason: ImportAfterDeclaration } ]

    it "are reported after a signature, which begins a declaration" do
      grouped
        [ "x :: Int"
        , "import A"
        , "x = 1"
        ]
        [ "value x" ]
        [ { line: 2, column: 1, reason: SignatureWithoutDefinition }
        , { line: 3, column: 8, reason: ImportAfterDeclaration }
        ]

  describe "an item the parser could not read" do
    it "parts a signature from the definition after it, and drops what waited without a report" do
      case parseModule (joinWith "\n" [ "module M where", "@[a]", "x :: Int", "x = 1" ]) of
        Left e -> fail (printSyntaxError e)
        Right (Module m) -> do
          let
            broken = Module m { items = Array.take 2 m.items <> [ ItemBroken Nothing ] <> Array.drop 2 m.items }
            g = groupModule broken
          map sketch g.grouped.declarations `shouldEqual` [ "value x" ]
          g.errors `shouldEqual` []

  describe "a block of bindings" do
    it "joins each signature to its definition, and reports a name bound twice" do
      grouped
        [ "f x = y"
        , "  where"
        , "  y :: Int"
        , "  y = 1"
        , "  (a, { b, c: a }) = p"
        , "  b = 2"
        ]
        [ "value f [y signed] [pattern] [b]" ]
        [ { line: 6, column: 15, reason: BoundTwice }
        , { line: 7, column: 3, reason: BoundTwice }
        ]

    it "reports a signature the definition of its name does not follow" do
      grouped
        [ "f = 1"
        , "  where"
        , "  y :: Int"
        , "  z = 1"
        ]
        [ "value f [z]" ]
        [ { line: 4, column: 3, reason: SignatureWithoutDefinition } ]

  describe "the items it keeps whole" do
    it "keeps effects, fixities, and foreign types" do
      grouped
        [ "effect E where"
        , "  op :: Unit ->* Int"
        , "infixl 6 add as +"
        , "foreign type Window :: Type"
        ]
        [ "other E", "other +", "other Window" ]
        []
    it "keeps a kind signature apart from the keywords of others" do
      grouped
        [ "newtype N :: Type"
        , "newtype N = N Int"
        ]
        [ "newtype N kinded" ]
        []
