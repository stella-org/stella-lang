-- | Resolving patterns into the Surface AST, and binding the variables of a
-- | binding group.
-- |
-- | **A binding group is what binds together**, and this module is what binds
-- | one: it numbers every binding of the group, reports a name the group binds
-- | twice, and decides what the group puts in scope. A group is the parameters
-- | of one declaration, lambda, or clause; the patterns of one `case`
-- | alternative; one binding of a guard block; or one `let` block or `where`,
-- | whose members are the names its definitions bind and the patterns of its
-- | pattern bindings.
-- |
-- | Every binding of a group is numbered, in the order written, before
-- | anything in it is resolved, so a pattern left invalid still binds the
-- | variables written in it. A name the group binds twice is an error, and the
-- | group puts the first binding of each name in scope.
-- |
-- | A constructor is matched with one pattern per field, and a tag with one
-- | pattern for its payload or none. An or-pattern binds no variable, and a
-- | `Number` is matched by no literal, its identity as a literal not being
-- | numeric equality.
-- |
-- | **A binding position takes only an irrefutable pattern**: a variable, `_`,
-- | a tuple, a record, or a constructor of a type with one constructor, each of
-- | whose parts is irrefutable, and an as-pattern or an annotated pattern
-- | around one. Which constructors a type has is read from the constructor
-- | table alone
-- | ([Pattern Matching](../../../../docs/proposals/03-Pattern-Matching-Syntax.md)).
module Stella.Compiler.Resolve.Binder
  ( Member(..)
  , ResolvedMember(..)
  , resolveGroup
  , resolveBinders
  , resolveAlternative
  , irrefutable
  , requireIrrefutable
  ) where

import Prelude
import Prim hiding (Type)

import Data.Array as Array
import Data.Enum (fromEnum)
import Data.Foldable (foldM, foldMap, traverse_)
import Data.Maybe (Maybe(..), maybe)
import Data.String.CodePoints (toCodePointArray)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Stella.Compiler.CST.Range (binderRange, covering)
import Stella.Compiler.CST.Types as CST
import Stella.Compiler.Resolve.Label (reportLabelsTwice)
import Stella.Compiler.Resolve.Monad (Found(..), Resolve, ResolveReason(..), ResolveWarning(..), constructorOf, freshBinding, lookupValue, report, valueInScope, warn)
import Stella.Compiler.Resolve.Type (resolveType)
import Stella.Compiler.Surface.Expr (Binder(..), RecordBinderField)
import Stella.Compiler.Surface.Name (LocalVar(..))
import Stella.Compiler.Surface.Origin (Origin(..), rangeOf)
import Stella.Compiler.TypedCore.Domain (scalarString, scalarValue)
import Stella.Compiler.TypedCore.Name (Ident(..), Symbol(..), Tag(..))
import Stella.Compiler.TypedCore.Prim (unitCtor)
import Stella.Compiler.TypedCore.Term (Literal(..))

-- | A member of a binding group: a name a definition binds, or a pattern.
data Member
  = MemberName CST.Name
  | MemberPattern CST.Binder

data ResolvedMember
  = ResolvedName LocalVar
  | ResolvedPattern Binder

-- | The bindings of a group not yet handed to what binds them, in the order
-- | the group's members write them.
type Supply = Array LocalVar

-- | Binds a group: each member resolved, and what the group puts in scope for
-- | what it binds over, one variable per name, the first binding of it.
resolveGroup :: Array Member -> Resolve { members :: Array ResolvedMember, bound :: Array LocalVar }
resolveGroup ms = do
  vars <- foldM number [] (Array.concatMap namesOf ms)
  resolved <- foldM step { members: [], supply: map _.var vars } ms
  pure { members: resolved.members, bound: Array.nubByEq (\a b -> nameOf a == nameOf b) (map _.var vars) }
  where
  namesOf = case _ of
    MemberName n -> [ n ]
    MemberPattern b -> variablesOf b
  number acc n = do
    if Array.any (\prior -> prior.name.name == n.name) acc then report n.range (BoundTwice n.name)
    else do
      hides <- valueInScope n.name
      when hides (warn (HidesValue n.range n.name))
    id <- freshBinding
    pure (Array.snoc acc { name: n, var: LocalVar { id, name: Ident n.name } })
  step acc = case _ of
    MemberName n -> case Array.uncons acc.supply of
      Just { head, tail } -> pure { members: Array.snoc acc.members (ResolvedName head), supply: tail }
      Nothing -> freshBinding <#> \id -> acc { members = Array.snoc acc.members (ResolvedName (LocalVar { id, name: Ident n.name })) }
    MemberPattern b -> do
      r <- binder acc.supply b
      pure { members: Array.snoc acc.members (ResolvedPattern r.binder), supply: r.supply }

-- | Binds a group of patterns alone.
resolveBinders :: Array CST.Binder -> Resolve { binders :: Array Binder, bound :: Array LocalVar }
resolveBinders bs = resolveGroup (map MemberPattern bs) <#> \r ->
  { binders: Array.mapMaybe patternOf r.members, bound: r.bound }
  where
  patternOf = case _ of
    ResolvedPattern b -> Just b
    ResolvedName _ -> Nothing

-- | Binds the patterns of a `case` alternative: a row per or-choice at its
-- | top, one pattern per scrutinee in each. Where there are several choices,
-- | none may bind a variable, as in any or-pattern; a pattern that would is
-- | reported and left invalid, and still binds what it writes.
resolveAlternative :: Array (Array CST.Binder) -> Resolve { patterns :: Array (Array Binder), bound :: Array LocalVar }
resolveAlternative rows = do
  r <- resolveBinders (Array.concat rows)
  patterns <- regroup r.binders (Array.concat rows) rows
  pure { patterns, bound: r.bound }
  where
  several = Array.length rows > 1
  regroup resolved asWritten =
    foldM
      ( \acc row -> do
          let n = Array.length row
          checked <- traverse checkChoice (Array.zip (Array.slice acc.at (acc.at + n) asWritten) (Array.slice acc.at (acc.at + n) resolved))
          pure { at: acc.at + n, rows: Array.snoc acc.rows checked }
      )
      { at: 0, rows: [] } >>> map _.rows
  checkChoice (Tuple w b)
    | several && not (Array.null (variablesOf w)) = report (binderRange w) OrPatternBinds $> BinderInvalid (FromSource (binderRange w))
    | otherwise = pure b

binder :: Supply -> CST.Binder -> Resolve { binder :: Binder, supply :: Supply }
binder supply b = case b of
  CST.BinderWildcard _ -> done (BinderWildcard o)
  CST.BinderVar _ -> pure (variable supply (BinderVar o))
  CST.BinderAs _ inner -> case Array.uncons supply of
    Just { head, tail } -> binder tail inner <#> \r -> r { binder = BinderAs o head r.binder }
    Nothing -> pure { binder: BinderInvalid o, supply }
  CST.BinderConstructor n args -> constructor n args
  CST.BinderTag n args -> case args of
    [] -> done (BinderTag o (Tag n.name) Nothing)
    [ payload ] -> binder supply payload <#> \r -> r { binder = BinderTag o (Tag n.name) (Just r.binder) }
    _ -> invalid TagPayloadMany
  CST.BinderBoolean _ v -> done (BinderLiteral o (LitBoolean v))
  CST.BinderInt l -> done (BinderLiteral o (LitInt l.value))
  CST.BinderNumber _ -> invalid NumberPattern
  CST.BinderChar l -> case toCodePointArray l.value of
    [ c ] | Just v <- scalarValue (fromEnum c) -> done (BinderLiteral o (LitChar v))
    _ -> invalid LiteralNotScalar
  CST.BinderString l -> case scalarString l.value of
    Just s -> done (BinderLiteral o (LitString s))
    Nothing -> invalid LiteralNotScalar
  CST.BinderUnit _ -> done (BinderConstructor o unitCtor [])
  CST.BinderParens inner -> binder supply inner
  CST.BinderTuple bs -> many supply bs <#> \r -> { binder: BinderTuple o r.binders, supply: r.supply }
  CST.BinderOr bs
    | Array.null (Array.concatMap variablesOf bs) -> many supply bs <#> \r -> { binder: BinderOr o r.binders, supply: r.supply }
    | otherwise -> invalid OrPatternBinds
  CST.BinderRecord _ items -> do
    reportLabelsTwice (Array.mapMaybe labelOf items)
    r <- foldM item { fields: [], rest: Nothing, supply } items
    pure { binder: BinderRecord o r.fields r.rest, supply: r.supply }
  CST.BinderTyped inner t -> do
    r <- binder supply inner
    t' <- resolveType t
    pure r { binder = BinderTyped o r.binder t' }
  CST.BinderApp _ _ -> invalid NotAPattern
  CST.BinderInvalid _ -> invalid NotAPattern
  where
  o = FromSource (binderRange b)
  done x = pure { binder: x, supply }
  -- A pattern left invalid passes over the bindings it writes, which stay
  -- bound.
  invalid reason = do
    report (binderRange b) reason
    pure { binder: BinderInvalid o, supply: Array.drop (Array.length (variablesOf b)) supply }

  constructor n args = lookupValue n >>= case _ of
    Found q -> constructorOf q >>= case _ of
      Just c
        | c.arity == Array.length args -> many supply args <#> \r -> { binder: BinderConstructor o q r.binders, supply: r.supply }
        | otherwise -> invalid (ConstructorArity (written n) c.arity (Array.length args))
      Nothing -> invalid (NotAConstructor (written n))
    NotFound -> invalid (UnknownConstructor (written n))
    Ambiguous -> invalid (AmbiguousValue (written n))

  item acc = case _ of
    CST.RecordBinderField n p -> do
      r <- binder acc.supply p
      let f = { origin: FromSource (covering n.range (binderRange p)), label: Symbol n.name, binder: r.binder }
      pure acc { fields = Array.snoc acc.fields f, supply = r.supply }
    CST.RecordBinderPun n ->
      let
        r = variable acc.supply (BinderVar (FromSource n.range))

        f :: RecordBinderField
        f = { origin: FromSource n.range, label: Symbol n.name, binder: r.binder }
      in
        pure acc { fields = Array.snoc acc.fields f, supply = r.supply }
    CST.RecordBinderRest r n -> pure case n of
      Just n' -> case Array.uncons acc.supply of
        Just { head, tail } -> acc { rest = Just { origin: FromSource (covering r n'.range), var: Just head }, supply = tail }
        Nothing -> acc
      Nothing -> acc { rest = Just { origin: FromSource r, var: Nothing } }

  labelOf = case _ of
    CST.RecordBinderField n _ -> Just n
    CST.RecordBinderPun n -> Just n
    CST.RecordBinderRest _ _ -> Nothing

  variable s k = case Array.uncons s of
    Just { head, tail } -> { binder: k head, supply: tail }
    Nothing -> { binder: BinderInvalid o, supply: s }

many :: Supply -> Array CST.Binder -> Resolve { binders :: Array Binder, supply :: Supply }
many supply = foldM
  (\acc b -> binder acc.supply b <#> \r -> { binders: Array.snoc acc.binders r.binder, supply: r.supply })
  { binders: [], supply }

-- | Whether a pattern always matches a value of its type.
irrefutable :: Binder -> Resolve Boolean
irrefutable b = Array.null <$> refutableParts b

-- | Reports each largest part of a pattern that can fail to match.
requireIrrefutable :: Binder -> Resolve Unit
requireIrrefutable b = refutableParts b >>= traverse_ \o -> report (rangeOf o) RefutablePattern

-- | The largest parts of a pattern that can fail to match. An invalid pattern
-- | was reported where it was resolved, and is taken to match.
refutableParts :: Binder -> Resolve (Array Origin)
refutableParts b = case b of
  BinderWildcard _ -> pure []
  BinderVar _ _ -> pure []
  BinderAs _ _ inner -> refutableParts inner
  BinderTyped _ inner _ -> refutableParts inner
  BinderTuple _ bs -> parts bs
  BinderRecord _ fs _ -> parts (map _.binder fs)
  BinderConstructor o q args -> constructorOf q >>= case _ of
    Just c | c.siblings == 1 -> parts args
    _ -> pure [ o ]
  BinderTag o _ _ -> pure [ o ]
  BinderLiteral o _ -> pure [ o ]
  BinderOr o _ -> pure [ o ]
  BinderInvalid _ -> pure []
  where
  parts bs = Array.concat <$> traverse refutableParts bs

-- | The variables a pattern writes, in the order written, an invalid pattern's
-- | among them.
variablesOf :: CST.Binder -> Array CST.Name
variablesOf = case _ of
  CST.BinderVar n -> [ n ]
  CST.BinderAs n b -> [ n ] <> variablesOf b
  CST.BinderConstructor _ bs -> foldMap variablesOf bs
  CST.BinderTag _ bs -> foldMap variablesOf bs
  CST.BinderParens b -> variablesOf b
  CST.BinderTuple bs -> foldMap variablesOf bs
  CST.BinderOr bs -> foldMap variablesOf bs
  CST.BinderRecord _ items -> foldMap item items
  CST.BinderTyped b _ -> variablesOf b
  CST.BinderApp f as -> variablesOf f <> foldMap variablesOf as
  _ -> []
  where
  item = case _ of
    CST.RecordBinderField _ b -> variablesOf b
    CST.RecordBinderPun n -> [ n ]
    CST.RecordBinderRest _ n -> Array.fromFoldable n

nameOf :: LocalVar -> Ident
nameOf (LocalVar v) = v.name

written :: CST.Name -> String
written n = maybe n.name (\q -> q <> "." <> n.name) n.qualifier

