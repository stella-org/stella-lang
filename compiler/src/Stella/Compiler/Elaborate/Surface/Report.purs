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
  , printEffectRow
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
import Stella.Compiler.Elaborate.CorePlus.Row (XRowNormalForm, rebuild)
import Stella.Compiler.Elaborate.CorePlus.Type (XRowEntry(..), XType(..), fromCore)
import Stella.Compiler.Elaborate.Mechanism.Obligation (Breach(..))
import Stella.Compiler.Elaborate.Mechanism.Unify (UnifyError(..))
import Stella.Compiler.Elaborate.Surface.Module (ElaborationError(..))
import Stella.Compiler.Elaborate.Surface.Type (Atom(..), Unsupported(..))
import Stella.Compiler.Elaborate.Vocabulary.Diagnostic (Diagnostic(..))
import Stella.Compiler.ForeignBoundary (Position(..), Refusal(..), Refused)
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
  Unsupported (KeyTwice o _) -> [ o ]
  Unsupported (SpreadTwice o _) -> [ o ]
  Unsupported (AnonymousSpread o) -> [ o ]
  Unsupported (UnheldConstraint o _) -> [ o ]
  Unsupported (SynonymUnsaturated o _ _) -> [ o ]
  Unsupported (SynonymCycle o _) -> [ o ]
  Unsupported (SynonymUnexpandable o _) -> [ o ]
  Unsupported (ForeignKindInvalid o _) -> [ o ]
  Unsupported (EffectKindVariable o) -> [ o ]
  Unsupported (EffectKindUndetermined o) -> [ o ]
  WithoutSignature o _ -> [ o ]
  KindUndetermined o -> [ o ]
  Rejected d -> diagnosticOrigins d
  EquationUndecided o -> sourceOf o
  TypeUndetermined o -> [ o ]
  LeftUnchecked o _ -> [ o ]
  AttributeRejected o _ -> [ o ]
  ForeignRefused o _ _ -> [ o ]
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
  RowNotContained o _ -> sourceOf o

sourceOf :: Origin -> Array Surface.Origin
sourceOf = case _ of
  AtSource s -> [ s.origin ]
  InDeclaration _ -> []

printElaborationError :: ElaborationError -> String
printElaborationError = case _ of
  Unsupported (OutsideSubset _ what) -> fmt @"This version of the compiler does not elaborate {what} yet" { what }
  Unsupported (ReportedAlready _) -> "This was not read, as reported already"
  Unsupported (EffectAsType _ (Qualified _ (EffName e))) -> fmt @"This names the effect `{e}`, which stands as an element of an effect row and is no type" { e }
  Unsupported (KeyTwice _ key) -> fmt @"This row would hold `{k}` twice, once through a row it spreads; a row holds each key once" { k: keyName key }
  Unsupported (SpreadTwice _ (TyVar v)) -> fmt @"This row spreads `{v}` twice; a row holds each key once, so a row variable is spread into it once" { v }
  Unsupported (AnonymousSpread _) -> "`...` alone stands for a row a signature quantifies, and nothing quantifies one here; name the row"
  Unsupported (UnheldConstraint _ (LacksAtom key (TyVar v))) -> fmt @"This row needs `{v}` not to hold `{k}`, and `{v}` is bound where no such condition can be carried; a `forall` written in this type can bind the row instead" { v, k: keyName key }
  Unsupported (UnheldConstraint _ (DisjointAtom (TyVar a) (TyVar b))) -> fmt @"This row needs `{a}` and `{b}` to hold no key in common, and they are bound where no such condition can be carried; a `forall` written in this type can bind them instead" { a, b }
  Unsupported (SynonymUnsaturated _ (Qualified _ (TyName n)) count) -> fmt @"`{n}` is a type synonym of {count} {parameters}, and stands for a type only applied to every one of them" { n, count, parameters: if count == 1 then "parameter" else "parameters" }
  Unsupported (SynonymCycle _ (Qualified _ (TyName n))) -> fmt @"The type synonym `{n}` is defined in terms of itself, and stands for no type" { n }
  Unsupported (SynonymUnexpandable _ (Qualified _ (TyName n))) -> fmt @"The type synonym `{n}` cannot be expanded, as reported where it is declared" { n }
  Unsupported (ForeignKindInvalid _ k) -> fmt @"A foreign type takes types at kinds a type variable may stand at and produces `Type`, and `{k}` is no such kind" { k: printKind k }
  Unsupported (EffectKindVariable _) -> "An effect has no kind scheme, so a parameter of it, or a type variable of an operation, stands at a kind with no kind variable"
  Unsupported (EffectKindUndetermined _) -> "Nothing here determines the kind of this parameter, and an effect has no kind scheme to leave it open in; write its kind"
  WithoutSignature _ name -> fmt @"`{name}` needs a type signature in this version of the compiler" { name: nameOf name }
  KindUndetermined _ -> "Nothing here determines the kind of this type"
  Rejected d -> printDiagnostic d
  EquationUndecided _ -> "Nothing determines the types this equation is about"
  TypeUndetermined _ -> "Nothing determines the type here"
  LeftUnchecked _ name -> fmt @"`{name}` was not checked, as checking stopped at an error elsewhere" { name: nameOf name }
  AttributeRejected _ err -> "The arguments of this attribute do not match its declaration: " <> show err
  ForeignRefused _ name refused -> printRefused (nameOf name) refused
  CoreRefused failure -> internal ("the Core checker refused what was elaborated: " <> show failure.error)
  InternalEntryMismatch name -> internal ("an entry the compiler refers to is missing or at another scheme than listed: " <> show name)
  Broken defect -> internal (show defect)
  AttemptPostponed -> internal "an elaboration attempt postponed itself"
  where
  internal what = "Internal compiler error: " <> what
  nameOf (Qualified _ (Ident n)) = n

-- | Why a foreign's type does not cross to the host, and what does.
printRefused :: String -> Refused -> String
printRefused name refused = case refused.refusal of
  ConstrainedType -> fmt @"The type of the foreign `{name}` holds a constraint, and the host cannot be handed evidence for one" { name }
  PerformingArrow -> fmt @"The foreign `{name}` has an arrow performing effects where its {place} stands; the arrows of a foreign's type are pure, and a foreign that performs effects returns an `IO` action instead" { name, place: placeOf refused.position }
  refusal -> fmt @"The {place} of the foreign `{name}` cannot cross to the host, as {why}; only `Int`, `Number`, `Char`, `String`, `Boolean`, `Unit`, and a foreign type cross, and as the result an `IO` action producing one of them" { name, place: placeOf refused.position, why: reason refusal }
  where
  placeOf = case _ of
    Argument n -> fmt @"argument {n}" { n }
    Result -> "result"
  reason = case _ of
    DataType (Qualified _ (TyName n)) -> fmt @"`{n}` is a data type" { n }
    RecordType -> "it is a record"
    VariantType -> "it is a variant"
    FunctionType -> "it is a function"
    TypeVariable (TyVar v) -> fmt @"`{v}` is a type variable" { v }
    ActionArgument -> "it is an `IO` action, which crosses only as the result"
    ActionOfAction -> "it is an `IO` action producing an `IO` action"
    NoValue t -> fmt @"`{t}` is none of these" { t: printType (fromCore t) }
    -- the refusals of the whole type are said above
    ConstrainedType -> "it holds a constraint"
    PerformingArrow -> "it performs effects"

printDiagnostic :: Diagnostic -> String
printDiagnostic = case _ of
  EquationFailed _ err -> printUnifyError err
  ObligationBroken b -> printBreach b.breach
  ObligationRejected r -> printBreach r.breach
  TermAssignmentFailed _ _ -> "A term filled in here is not valid where it stands"
  SynthesisFailed _ -> "A synthesizer failed here"
  RowNotContained _ r -> fmt @"This performs `{s}`, which is not among the effects allowed here" { s: printEffectRow (rebuild r.source) }

-- | Why a row's sharpness does not hold: the key or the row variables it is
-- | about.
printBreach :: Breach -> String
printBreach = case _ of
  SolutionCarriesKey key -> fmt @"A row here would hold `{k}` twice" { k: keyName key }
  LacksUnprovenAtSite key (TyVar v) -> fmt @"Nothing here says that `{v}` does not hold `{k}`, which a row holding `{k}` beside `{v}` needs" { v, k: keyName key }
  SidesShareKey key -> fmt @"Two rows joined here would both hold `{k}`" { k: keyName key }
  DisjointUnprovenAtSite (TyVar a) (TyVar b) -> fmt @"Nothing here says that `{a}` and `{b}` hold no key in common, which a row holding both needs" { a, b }
  SiteFactsFailed _ -> "The rows the signature here describes need conditions that contradict each other"
  ObligationNotARow _ -> "Internal compiler error: a row constraint was decided of what is no row"

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
printType = (printers unit).type

-- | An effect row, in the brackets of one where it is more than a variable.
printEffectRow :: XType -> String
printEffectRow = (printers unit).effectRow

printers :: Unit -> { type :: XType -> String, effectRow :: XType -> String }
printers _ = { type: go 0, effectRow }
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
    XRowTypeEntry key payload -> fmt @"{key} :: {payload}" { key: keyName key, payload: go 0 payload }
    XRowEffectEntry e args -> effectText e args
    XRowLabelledEffectEntry (Symbol s) e args -> fmt @"{s} :: {effect}" { s, effect: effectText e args }
    XRowRegionEntry (RegionName r) -> fmt @"region {r}" { r }

  effectText (Qualified _ (EffName e)) args = joinWith " " (Array.cons e (map (go 2) args))

  bracketed open close = case _ of
    [] -> open <> close
    items -> fmt @"{open} {items} {close}" { open, items: joinWith ", " items, close }

-- | A row's key as source writes it.
keyName :: RowKey -> String
keyName = case _ of
  SymbolKey (Symbol s) -> s
  TagKey (Tag t) -> "'" <> t
  PositionKey n -> show n
  EffectKey (Qualified _ (EffName e)) -> e
  RegionKey (RegionName r) -> "region " <> r

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
