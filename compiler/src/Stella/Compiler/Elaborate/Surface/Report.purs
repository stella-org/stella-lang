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

import Fmt (DefaultConfig, SetOpenClose, fmt, fmtWith)
import Stella.Compiler.Elaborate.CorePlus.Context (Origin(..))
import Stella.Compiler.Elaborate.CorePlus.Kind (XKind(..))
import Stella.Compiler.Elaborate.CorePlus.Type (XType(..))
import Stella.Compiler.Elaborate.Mechanism.Unify (UnifyError(..))
import Stella.Compiler.Elaborate.Surface.Module (ElaborationError(..))
import Stella.Compiler.Elaborate.Surface.Type (Unsupported(..))
import Stella.Compiler.Elaborate.Vocabulary.Diagnostic (Diagnostic(..))
import Stella.Compiler.Surface.Origin as Surface
import Stella.Compiler.TypedCore.Kind (RowElemKind(..))
import Stella.Compiler.TypedCore.Name (Ident(..), KindVar(..), Qualified(..), TyName(..), TyVar(..))
import Stella.Compiler.TypedCore.Prim (functionTy)

-- | The places an error is about, the one it is chiefly about first.
elaborationOrigins :: ElaborationError -> Array Surface.Origin
elaborationOrigins = case _ of
  Unsupported (OutsideSubset o _) -> [ o ]
  Unsupported (ReportedAlready o) -> [ o ]
  WithoutSignature o _ -> [ o ]
  KindUndetermined o -> [ o ]
  Rejected d -> diagnosticOrigins d
  EquationUndecided o -> sourceOf o
  TypeUndetermined o -> [ o ]
  LeftUnchecked o _ -> [ o ]
  AttributeRejected o _ -> [ o ]
  CoreRefused failure -> [ failure.at ]
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
  WithoutSignature _ name -> fmt @"`{name}` needs a type signature in this version of the compiler" { name: nameOf name }
  KindUndetermined _ -> "Nothing here determines the kind of this type"
  Rejected d -> printDiagnostic d
  EquationUndecided _ -> "Nothing determines the types this equation is about"
  TypeUndetermined _ -> "Nothing determines the type here"
  LeftUnchecked _ name -> fmt @"`{name}` was not checked, as checking stopped at an error elsewhere" { name: nameOf name }
  AttributeRejected _ err -> "The arguments of this attribute do not match its declaration: " <> show err
  CoreRefused failure -> internal ("the Core checker refused what was elaborated: " <> show failure.error)
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
  RowMismatch _ _ -> "Two rows do not match"
  PayloadMismatch _ _ _ -> "Two rows do not match"
  RigidTailRemains _ -> "Two rows do not match"
  NotARow _ -> "Two rows do not match"
  ConstraintNotEqual _ _ -> "Two constraints do not match"
  EscapingVariable _ (TyVar v) -> fmt @"The type variable `{v}` would be used outside its scope" { v }
  EscapingKindVariable _ (KindVar k) -> fmt @"The kind variable `{k}` would be used outside its scope" { k }
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

-- | A type as an author would write it, a metavariable as `?`.
printType :: XType -> String
printType = go 0
  where
  -- 0: anywhere; 1: the function of an application or an arrow's argument;
  -- 2: an argument of an application
  go :: Int -> XType -> String
  go p = case _ of
    XVar (TyVar v) -> v
    XMeta _ -> "?"
    XCon (Qualified _ (TyName n)) _ -> n
    XApp (XApp (XApp (XCon f _) a) row) b | f == functionTy ->
      parenthesized (p > 0) (fmt @"{a}{arrow}{b}" { a: go 1 a, arrow: arrow row, b: go 0 b })
    XApp f x -> parenthesized (p > 1) (fmt @"{f} {x}" { f: go 1 f, x: go 2 x })
    XForall (TyVar v) _ body -> parenthesized (p > 0) (fmt @"forall {v}. {body}" { v, body: go 0 body })
    XConstrained _ body -> parenthesized (p > 0) ("… => " <> go 0 body)
    XRowEmpty -> "()"
    XRowExtend _ _ -> "( … )"
    XRowUnion _ _ -> "( … )"

  arrow = case _ of
    XRowEmpty -> " -> "
    row -> fmtWith @(SetOpenClose "<" ">" DefaultConfig) @" -{ <row> }-> " { row: go 0 row }

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
