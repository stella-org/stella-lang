-- | Resolving the attributes attached to a declaration, the constants their
-- | arguments are, and attribute declarations.
-- |
-- | **An attached attribute is normalized**: it has as many positional
-- | arguments as its declaration has parameters, and every keyword argument in
-- | the order the declaration gives them, a default standing for one left out
-- | and carrying the origin of the attribute it was filled into. One that does
-- | not resolve or whose arguments do not match its declaration is reported and
-- | left out.
-- |
-- | **An argument is a constant**: a literal, a global value, a constructor
-- | applied to constants, or a record of constants. Anything else is reported
-- | and left an invalid constant, the attribute kept. Whether a constant has its
-- | parameter's type is the Core type checker's to decide.
-- |
-- | **The attributes the compiler reads stand at most once, on the declarations
-- | they are for**
-- | ([Attributes, Modifiers, and Directives](../../../../docs/technical-references/02-Surface-Language/07-Attributes-Modifiers-and-Directives.md)).
-- | No attribute stands on a fixity declaration or an attribute declaration.
module Stella.Compiler.Resolve.Attribute
  ( DeclarationSort(..)
  , resolveAttributes
  , resolveConstant
  , resolveAttributeDeclaration
  ) where

import Prelude
import Prim hiding (Type)

import Data.Array as Array
import Data.Enum (fromEnum)
import Data.Foldable (foldM, traverse_)
import Data.Maybe (Maybe(..), maybe)
import Data.String.CodePoints (toCodePointArray)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Stella.Compiler.CST.Range (covering, exprRange, typeRange)
import Stella.Compiler.CST.Types as CST
import Stella.Compiler.TypedCore.Decl as Core
import Stella.Compiler.Resolve.Label (reportLabelsTwice)
import Stella.Compiler.Resolve.Monad (AttributeDefault(..), Found(..), Resolve, ResolveReason(..), ValueKind(..), attributeShape, constructorOf, lookupAttribute, lookupValue, report, speculatively, valueKind)
import Stella.Compiler.Resolve.Scope (writtenBare)
import Stella.Compiler.Resolve.Type (resolveType)
import Stella.Compiler.Surface.Decl (Attribute, Constant(..), KeywordParameter)
import Stella.Compiler.Surface.Origin (Origin, originOf)
import Stella.Compiler.Surface.Type (Type)
import Stella.Compiler.TypedCore.Domain (scalarString, scalarValue)
import Stella.Compiler.TypedCore.Name (Ident(..), ModuleName(..), Qualified(..), Symbol(..))
import Stella.Compiler.TypedCore.Prim (unitCtor)
import Stella.Compiler.TypedCore.Term (Literal(..))

-- | What a declaration is, which decides the attributes it may carry.
data DeclarationSort
  = OnValue
  | OnComputation
  | OnData
  | OnNewtype
  | OnSynonym
  | OnForeignType
  | OnEffect
  | OnHandler
  | OnForeign
  | OnFixity
  | OnAttribute

derive instance Eq DeclarationSort

-- | The attributes the compiler reads, each with the declarations it stands on.
compilerRead :: Array { attribute :: Qualified Ident, on :: Array DeclarationSort }
compilerRead =
  [ { attribute: prim "macro", on: [ OnValue ] }
  , { attribute: prim "entrypoint", on: [ OnValue, OnComputation ] }
  , { attribute: elaborationOnly, on: [ OnData, OnNewtype ] }
  , { attribute: Qualified (ModuleName "Stella.Elab") (Ident "synthesizedBy"), on: [ OnData, OnNewtype, OnSynonym, OnForeignType ] }
  ]
  where
  prim = Qualified (ModuleName "Prim") <<< Ident

elaborationOnly :: Qualified Ident
elaborationOnly = Qualified (ModuleName "Prim") (Ident "elaborationOnly")

-- | The attributes of a declaration of the sort given, in the order written.
-- | An attribute the compiler reads counts once it resolves and stands where
-- | it may, whether or not its arguments match, and a later use of it is a
-- | second one: the order the scope acts in, which acts on a first use written
-- | bare alone. Where the declaration is no entry the compiler lists, a first
-- | `@[elaborationOnly]` written bare was refused where the scope was built,
-- | and is left out here without a second report.
resolveAttributes :: DeclarationSort -> Boolean -> Array CST.Attribute -> Resolve (Array Attribute)
resolveAttributes sort listed = map _.attributes <<< foldM step { seen: [], attributes: [] }
  where
  step acc a = lookupAttribute a.name >>= case _ of
    NotFound -> report a.name.range (UnknownAttribute (written a.name)) $> acc
    Ambiguous -> report a.name.range (AmbiguousAttribute (written a.name)) $> acc
    Found q
      | sort == OnFixity || sort == OnAttribute -> report a.range (AttributeMisplaced (written a.name)) $> acc
      | otherwise -> case Array.find (\c -> c.attribute == q) compilerRead of
          Just c
            | not (Array.elem sort c.on) -> report a.range (AttributeMisplaced (written a.name)) $> acc
            | Array.elem q acc.seen -> report a.range (AttributeTwice (written a.name)) $> acc
            | q == elaborationOnly && not listed && writtenBare a -> pure acc { seen = Array.snoc acc.seen q }
            | otherwise -> kept (acc { seen = Array.snoc acc.seen q }) q a
          Nothing -> kept acc q a
  kept acc q a = normalize q a <#> case _ of
    Just attribute -> acc { attributes = Array.snoc acc.attributes attribute }
    Nothing -> acc

-- | An attribute's arguments against its declaration. Every argument written
-- | is resolved, so a constant's problem is reported whatever else is wrong.
normalize :: Qualified Ident -> CST.Attribute -> Resolve (Maybe Attribute)
normalize q a = attributeShape q >>= case _ of
  Nothing -> report a.name.range (UnknownAttribute (written a.name)) $> Nothing
  Just shape -> do
    let
      positional = Array.mapMaybe positionalOf a.args
      keyed = Array.mapMaybe keyedOf a.args
    positional' <- traverse resolveConstant positional
    keyed' <- traverse (\(Tuple n e) -> Tuple n <$> resolveConstant e) keyed
    arityOk <-
      if Array.length positional == shape.positional then pure true
      else report a.range (AttributeArity (written a.name) shape.positional (Array.length positional)) $> false
    labelsOk <- foldM (checkLabel shape) { ok: true, seen: [] } keyed
    keyword <- traverse (argument keyed') shape.keyword
    pure case arityOk && labelsOk.ok, Array.catMaybes keyword of
      true, keyword' | Array.length keyword' == Array.length shape.keyword ->
        Just { origin: o, name: q, positional: positional', keyword: keyword' }
      _, _ -> Nothing
  where
  o = originOf a.range
  positionalOf = case _ of
    CST.ArgumentPositional e -> Just e
    CST.ArgumentKeyed _ _ -> Nothing
  keyedOf = case _ of
    CST.ArgumentKeyed n e -> Just (Tuple n e)
    CST.ArgumentPositional _ -> Nothing
  checkLabel shape acc (Tuple n _)
    | not (Array.any (\k -> k.label == n.name) shape.keyword) =
        report n.range (KeywordUnknown (written a.name) n.name) $> acc { ok = false }
    | Array.elem n.name acc.seen = report n.range (KeywordTwice n.name) $> acc { ok = false }
    | otherwise = pure acc { seen = Array.snoc acc.seen n.name }
  argument keyed k = case Array.find (\(Tuple n _) -> n.name == k.label) keyed of
    Just (Tuple _ value) -> pure (Just { label: k.label, value })
    Nothing -> case k.default of
      Just (OwnDefault e) -> speculatively (resolveConstant e) <#> \c -> Just { label: k.label, value: reorigin o c }
      Just (ImportedDefault c) -> pure (Just { label: k.label, value: fromInterface o c })
      Nothing -> report a.range (KeywordMissing (written a.name) k.label) $> Nothing

-- | A constant, read off the expression written.
resolveConstant :: CST.Expr -> Resolve Constant
resolveConstant e = case e of
  CST.ExprBoolean _ b -> pure (ConstantLiteral o (LitBoolean b))
  CST.ExprInt l -> pure (ConstantLiteral o (LitInt l.value))
  CST.ExprNumber l -> pure (ConstantLiteral o (LitNumber l.value))
  CST.ExprChar l -> case toCodePointArray l.value of
    [ c ] | Just v <- scalarValue (fromEnum c) -> pure (ConstantLiteral o (LitChar v))
    _ -> invalid LiteralNotScalar
  CST.ExprString l -> case scalarString l.value of
    Just s -> pure (ConstantLiteral o (LitString s))
    Nothing -> invalid LiteralNotScalar
  CST.ExprUnit _ -> pure (ConstantConstructor o unitCtor [])
  CST.ExprParens inner -> resolveConstant inner
  CST.ExprRecord _ fields -> case traverse field fields of
    Just fs -> do
      reportLabelsTwice (map (\f -> f.name) fs)
      ConstantRecord o <$> traverse (\f -> { label: Symbol f.name.name, value: _ } <$> f.value) fs
    Nothing -> invalid NotAConstant
  CST.ExprMacro _ -> invalid (NotYetSupported "A macro call")
  _ -> case application e of
    { head: CST.ExprConstructor n, arguments } -> lookupValue n >>= case _ of
      Found q -> constructorOf q >>= case _ of
        Just c
          | c.arity == Array.length arguments -> ConstantConstructor o q <$> traverse resolveConstant arguments
          | otherwise -> invalid (ConstructorArity (written n) c.arity (Array.length arguments))
        Nothing -> invalid NotAConstant
      NotFound -> invalid (UnknownConstructor (written n))
      Ambiguous -> invalid (AmbiguousValue (written n))
    { head: CST.ExprVar n, arguments: [] } -> global n
    _ -> invalid NotAConstant
  where
  o = originOf (exprRange e)
  invalid reason = report (exprRange e) reason $> ConstantInvalid o
  global n = lookupValue n >>= case _ of
    Found q -> valueKind q >>= case _ of
      PlainValue -> pure (ConstantValue o q)
      _ -> invalid NotAConstant
    NotFound -> invalid (UnknownValue (written n))
    Ambiguous -> invalid (AmbiguousValue (written n))
  field = case _ of
    CST.FieldValue n v -> Just { name: n, value: resolveConstant v }
    CST.FieldPun n -> Just { name: n, value: resolveConstant (CST.ExprVar n) }
    _ -> Nothing
  application x = case x of
    CST.ExprApp f a -> let s = application f in s { arguments = Array.snoc s.arguments a }
    CST.ExprParens inner -> application inner
    _ -> { head: x, arguments: [] }

-- | An attribute declaration's parameters: the positional ones, closed types
-- | that come first, and the keyword ones, each declared once, with their
-- | defaults.
resolveAttributeDeclaration
  :: Array CST.AttributeParameter
  -> Resolve { positional :: Array Type, keyword :: Array KeywordParameter }
resolveAttributeDeclaration params = do
  traverse_ misplaced (Array.drop 1 (Array.dropWhile isPositional params))
  foldM step { positional: [], keyword: [] } params
  where
  isPositional = case _ of
    CST.AttributePositional _ -> true
    CST.AttributeKeyword _ _ _ -> false
  misplaced = case _ of
    CST.AttributePositional t -> report (typeRange t) PositionalAfterKeyword
    CST.AttributeKeyword _ _ _ -> pure unit
  step acc = case _ of
    CST.AttributePositional t -> resolveType t <#> \t' -> acc { positional = Array.snoc acc.positional t' }
    CST.AttributeKeyword l t d
      | Array.any (\k -> k.label == l.name) acc.keyword -> report l.range (KeywordParameterTwice l.name) $> acc
      | otherwise -> do
          t' <- resolveType t
          d' <- traverse resolveConstant d
          let range = maybe (covering l.range (typeRange t)) (covering l.range <<< exprRange) d
          pure acc { keyword = Array.snoc acc.keyword { origin: originOf range, label: l.name, type: t', default: d' } }

-- | A constant as an interface holds it, given the origin of the attribute it
-- | is filled into.
fromInterface :: Origin -> Core.Constant -> Constant
fromInterface o = case _ of
  Core.ConstantLiteral l -> ConstantLiteral o l
  Core.ConstantValue q -> ConstantValue o q
  Core.ConstantConstructor q cs -> ConstantConstructor o q (map (fromInterface o) cs)
  Core.ConstantRecord fs -> ConstantRecord o (map (\f -> f { value = fromInterface o f.value }) fs)

-- | A constant with every origin in it replaced by the one given.
reorigin :: Origin -> Constant -> Constant
reorigin o = case _ of
  ConstantLiteral _ l -> ConstantLiteral o l
  ConstantValue _ q -> ConstantValue o q
  ConstantConstructor _ q cs -> ConstantConstructor o q (map (reorigin o) cs)
  ConstantRecord _ fs -> ConstantRecord o (map (\f -> f { value = reorigin o f.value }) fs)
  ConstantInvalid _ -> ConstantInvalid o

written :: CST.Name -> String
written n = maybe n.name (\q -> q <> "." <> n.name) n.qualifier
