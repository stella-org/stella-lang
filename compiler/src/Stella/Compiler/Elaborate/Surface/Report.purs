-- | What an error of the surface elaborator says to an author, and where.
-- |
-- | **An error names every place it is about.** Most name one; an assignment
-- | that broke a row constraint names the equation that made it and the site
-- | the constraint came from. A place named only by its declaration, and a
-- | fault of the elaborator's own, name none.
-- |
-- | **A fault of the elaborator's is said to be one**, so that an author tells
-- | a program to correct from a compiler to report.
module Stella.Compiler.Elaborate.Surface.Report
  ( elaborationOrigins
  , printElaborationError
  , printType
  , printKind
  ) where

import Prelude
import Prim hiding (Type)

import Data.Array as Array
import Data.Foldable (foldl, foldr)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.String (joinWith)
import Fmt (fmt)
import Stella.Compiler.Elaborate.CorePlus.Context (Origin(..))
import Stella.Compiler.Elaborate.CorePlus.Kind (XKind(..))
import Stella.Compiler.Elaborate.CorePlus.Row (XRowNormalForm)
import Stella.Compiler.Elaborate.CorePlus.Type (XRowEntry(..), XType(..))
import Stella.Compiler.Elaborate.Mechanism.Unify (UnifyError(..))
import Stella.Compiler.Elaborate.Surface.Module (ElaborationError(..))
import Stella.Compiler.Elaborate.Surface.Type (Unsupported(..))
import Stella.Compiler.Elaborate.Vocabulary.Diagnostic (Diagnostic(..))
import Stella.Compiler.Surface.Origin as Surface
import Stella.Compiler.TypedCore.Kind (RowElemKind(..))
import Stella.Compiler.TypedCore.Name (EffName(..), Ident(..), KindVar(..), Qualified(..), RegionName(..), Symbol(..), Tag(..), TyName(..), TyVar(..))
import Stella.Compiler.TypedCore.Prim (functionTy, recordTy, variantTy)
import Stella.Compiler.TypedCore.Type (RowKey(..))

-- | The places an error is about, the one it is chiefly about first.
elaborationOrigins :: ElaborationError -> Array Surface.Origin
elaborationOrigins = case _ of
  Unsupported (OutsideSubset o _) -> [ o ]
  Unsupported (ReportedAlready o) -> [ o ]
  Unsupported (EffectAsType o _) -> [ o ]
  WithoutSignature o _ -> [ o ]
  KindUndetermined o -> [ o ]
  Rejected d -> diagnosticOrigins d
  EquationUndecided o -> sourceOf o
  TypeUndetermined o -> [ o ]
  LeftUnchecked o _ -> [ o ]
  AttributeRejected o _ -> [ o ]
  CoreRefused failure -> [ failure.at ]
  InternalEntryMismatch _ -> []
  Broken _ -> []
  AttemptPostponed -> []

diagnosticOrigins :: Diagnostic -> Array Surface.Origin
diagnosticOrigins = case _ of
  EquationFailed o _ -> sourceOf o
  ObligationBroken b -> sourceOf b.equation <> sourceOf b.obligation
  ObligationRejected r -> sourceOf r.obligation
  TermAssignmentFailed o _ -> sourceOf o
  SynthesisFailed s -> sourceOf s.goal.origin

sourceOf :: Origin -> Array Surface.Origin
sourceOf = case _ of
  AtSource s -> [ s.origin ]
  InDeclaration _ -> []

printElaborationError :: ElaborationError -> String
printElaborationError = case _ of
  Unsupported (OutsideSubset _ what) -> fmt @"This version of the compiler does not elaborate {what} yet" { what }
  Unsupported (ReportedAlready _) -> "This was not read, as reported already"
  Unsupported (EffectAsType _ (Qualified _ (EffName e))) -> fmt @"This names the effect `{e}`, which stands as an element of an effect row and is no type" { e }
  WithoutSignature _ name -> fmt @"`{name}` needs a type signature in this version of the compiler" { name: nameOf name }
  KindUndetermined _ -> "Nothing here determines the kind of this type"
  Rejected d -> printDiagnostic d
  EquationUndecided _ -> "Nothing determines the types this equation is about"
  TypeUndetermined _ -> "Nothing determines the type here"
  LeftUnchecked _ name -> fmt @"`{name}` was not checked, as checking stopped at an error elsewhere" { name: nameOf name }
  AttributeRejected _ err -> "The arguments of this attribute do not match its declaration: " <> show err
  CoreRefused failure -> internal ("the Core checker refused what was elaborated: " <> show failure.error)
  InternalEntryMismatch name -> internal ("an entry the compiler refers to is missing or at another scheme than listed: " <> show name)
  Broken defect -> internal (show defect)
  AttemptPostponed -> internal "an elaboration attempt postponed itself"
  where
  internal what = "Internal compiler error: " <> what
  nameOf (Qualified _ (Ident n)) = n

printDiagnostic :: Diagnostic -> String
printDiagnostic = case _ of
  EquationFailed _ err -> printUnifyError err
  ObligationBroken _ -> "A row constraint no longer holds once this is solved"
  ObligationRejected _ -> "A row constraint does not hold here"
  TermAssignmentFailed _ _ -> "A term filled in here is not valid where it stands"
  SynthesisFailed _ -> "A synthesizer failed here"

printUnifyError :: UnifyError -> String
printUnifyError = case _ of
  TypeNotEqual a b -> fmt @"`{a}` and `{b}` are different types" { a: printType a, b: printType b }
  KindNotEqual a b -> fmt @"`{a}` and `{b}` are different kinds" { a: printKind a, b: printKind b }
  KindMismatch _ a b -> fmt @"`{a}` and `{b}` are different kinds" { a: printKind a, b: printKind b }
  OccursCheck _ t -> fmt @"A type would have to contain itself, as `{t}` does" { t: printType t }
  KindOccursCheck _ k -> fmt @"A kind would have to contain itself, as `{k}` does" { k: printKind k }
  RowMismatch a b -> rowsDiffer (rowOf a) (rowOf b)
  -- each side shown as the one element it holds at the key they share
  PayloadMismatch _ a b -> rowsDiffer (XRowExtend a XRowEmpty) (XRowExtend b XRowEmpty)
  RigidTailRemains vars -> fmt @"`{vars}` stands for whatever row the signature is used at, and cannot be made to hold what the other row holds" { vars: joinWith "`, `" (map (\(TyVar v) -> v) (Array.fromFoldable vars)) }
  NotARow _ -> "Two rows do not match"
  ConstraintNotEqual _ _ -> "Two constraints do not match"
  EscapingVariable _ (TyVar v) -> fmt @"The type variable `{v}` would be used outside its scope" { v }
  EscapingKindVariable _ (KindVar k) -> fmt @"The kind variable `{k}` would be used outside its scope" { k }
  EscapingRegion _ _ -> "A cell would be reached outside the handling expression declaring it"
  KindEscapingVariable _ (KindVar k) -> fmt @"The kind variable `{k}` would be used outside its scope" { k }
  KindNotQuantifiable k -> fmt @"A type variable cannot stand at the kind `{k}`" { k: printKind k }
  KindDoesNotProduceType k -> fmt @"`{k}` does not produce `Type`" { k: printKind k }
  CannotSolveAcrossForall _ (TyVar v) -> fmt @"A type here would have to mention `{v}`, which a `forall` binds; an annotation may say what is meant" { v }
  MetaUnbound _ -> misuse
  MetaAlreadyAssigned _ -> misuse
  KindMetaUnbound _ -> misuse
  AssignmentsUnread _ -> misuse
  where
  misuse = "Internal compiler error: the unifier was used against its contract"
  rowsDiffer a b = fmt @"`{a}` and `{b}` are different rows" { a: printType a, b: printType b }

-- | The row a normal form stands for: its elements, then its tails.
rowOf :: XRowNormalForm -> XType
rowOf n = foldr XRowExtend tail (Array.fromFoldable (Map.values n.known))
  where
  tails = map XVar (Array.fromFoldable n.rigid) <> map XMeta (Array.fromFoldable n.flexible)
  tail = case Array.uncons tails of
    Nothing -> XRowEmpty
    Just { head, tail: rest } -> foldl XRowUnion head rest

-- | A type as an author would write it, a metavariable as `?`: an arrow with
-- | the row `/` puts on it, a record, a variant, and an effect row in their
-- | brackets, and a record keyed by its positions as a tuple.
printType :: XType -> String
printType = go 0
  where
  -- 0: anywhere; 1: the function of an application, an arrow's argument, or
  -- the result of an arrow carrying a row; 2: an argument of an application
  go :: Int -> XType -> String
  go p = case _ of
    XVar (TyVar v) -> v
    XMeta _ -> "?"
    XCon (Qualified _ (TyName n)) _ -> n
    XApp (XApp (XApp (XCon f _) a) row) b | f == functionTy -> parenthesized (p > 0) case row of
      XRowEmpty -> fmt @"{a} -> {b}" { a: go 1 a, b: go 0 b }
      _ -> fmt @"{a} -> {b} / {row}" { a: go 1 a, b: go 1 b, row: effectRow row }
    XApp (XCon r _) row | r == recordTy -> record row
    XApp (XCon v _) row | v == variantTy -> bracketed "[" "]" (rowItems row)
    XApp f x -> parenthesized (p > 1) (fmt @"{f} {x}" { f: go 1 f, x: go 2 x })
    XForall (TyVar v) _ body -> parenthesized (p > 0) (fmt @"forall {v}. {body}" { v, body: go 0 body })
    XConstrained _ body -> parenthesized (p > 0) ("… => " <> go 0 body)
    row -> bareRow row

  -- the row of an arrow: a variable or a metavariable standing alone, and
  -- otherwise its elements in the brackets of an effect row
  effectRow = case _ of
    row@(XVar _) -> go 0 row
    row@(XMeta _) -> go 0 row
    row -> bracketed "{|" "|}" (rowItems row)

  record row =
    let
      items = rowElements row
      positions = Array.mapMaybe position items.entries
    in
      if Array.null items.spreads && Array.length positions >= 2 && Array.length positions == Array.length items.entries && positions == Array.mapWithIndex (\n p -> p { at = n }) positions then fmt @"({components})" { components: joinWith ", " (map (\p -> go 0 p.payload) positions) }
      else bracketed "{" "}" (rowItems row)

  position = case _ of
    XRowTypeEntry (PositionKey n) payload -> Just { at: n, payload }
    _ -> Nothing

  -- a row standing alone: an effect row's brackets where it holds an effect or
  -- a region, and parentheses otherwise
  bareRow row =
    let
      items = rowElements row
    in
      if Array.any isEffect items.entries then bracketed "{|" "|}" (rowItems row)
      else bracketed "(" ")" (rowItems row)

  isEffect = case _ of
    XRowTypeEntry _ _ -> false
    _ -> true

  rowItems row =
    let
      items = rowElements row
    in
      map entry items.entries <> map (\t -> "..." <> go 2 t) items.spreads

  -- a row's elements in the order it holds them, and the rows spread into it
  rowElements = case _ of
    XRowEmpty -> { entries: [], spreads: [] }
    XRowExtend e rest -> let r = rowElements rest in r { entries = Array.cons e r.entries }
    XRowUnion l r ->
      let
        left = rowElements l
        right = rowElements r
      in
        { entries: left.entries <> right.entries, spreads: left.spreads <> right.spreads }
    tail -> { entries: [], spreads: [ tail ] }

  entry = case _ of
    XRowTypeEntry key payload -> fmt @"{key} :: {payload}" { key: keyText key, payload: go 0 payload }
    XRowEffectEntry e args -> effectText e args
    XRowLabelledEffectEntry (Symbol s) e args -> fmt @"{s} :: {effect}" { s, effect: effectText e args }
    XRowRegionEntry (RegionName r) -> fmt @"region {r}" { r }

  effectText (Qualified _ (EffName e)) args = joinWith " " (Array.cons e (map (go 2) args))

  keyText = case _ of
    SymbolKey (Symbol s) -> s
    TagKey (Tag t) -> "'" <> t
    PositionKey n -> show n
    EffectKey (Qualified _ (EffName e)) -> e
    RegionKey (RegionName r) -> "region " <> r

  bracketed open close = case _ of
    [] -> open <> close
    items -> fmt @"{open} {items} {close}" { open, items: joinWith ", " items, close }

-- | A kind as an author would write it, a metavariable as `?`.
printKind :: XKind -> String
printKind = go false
  where
  go inArgument = case _ of
    XKVar (KindVar k) -> k
    XKMeta _ -> "?"
    XKType -> "Type"
    XKEffect -> "Effect"
    XKRow RowType -> "Row Type"
    XKRow RowEffect -> "Row Effect"
    XKFun a b -> parenthesized inArgument (fmt @"{a} -> {b}" { a: go true a, b: go false b })

parenthesized :: Boolean -> String -> String
parenthesized yes s = if yes then fmt @"({s})" { s } else s
