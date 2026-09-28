-- | The kernel's builders of records, variants, and `openEff`.
-- |
-- | **Each is claimed at the type the Core rule gives it, read off the claims of
-- | its parts**; a type the term writes — the payload of a `weaken`, the result
-- | of an `absurd`, the row an `openEff` adds — is the synthesizer's to give, as
-- | a type the scope may use. A row is read at a key by the one procedure every
-- | builder shares: known, it is there; absent with a flexible tail, the tails
-- | are waited on; otherwise it is a misuse.
-- |
-- | **A row a term builds is sharp by construction**, as a row a type builder
-- | builds is: `extend` and `weaken` require the key absent from the rest, and
-- | `merge` and `openEff` the two rows apart, each introducing the requirement
-- | together with the term. What else the Core rules ask — that the row a
-- | `select` reads from is the one its term is claimed at, that an `absurd`'s
-- | variant is empty — is the Core type checker's.
module Stella.Compiler.Elaborate.Kernel.Builder.Record
  ( recordEmpty
  , recordExtend
  , recordSelect
  , recordRestrict
  , recordUpdate
  , recordMerge
  , variantInject
  , variantWeaken
  , variantAbsurd
  , openEff
  ) where

import Prelude

import Stella.Compiler.Elaborate.Kernel.Builder.Common (Shape(..), functionShape, issueTerm, recordShape, rejected, requiredIn, rowAt, usableIn, usableTermIn, valueType, variantShape)
import Stella.Compiler.Elaborate.Vocabulary.Diagnostic (BuildError(..))
import Stella.Compiler.Elaborate.Kernel.Elab (Elab, askEnv, currentMetas, postpone, resolveScope)
import Stella.Compiler.Elaborate.Vocabulary.Handle (ExprObject, Handle)
import Stella.Compiler.Elaborate.CorePlus.Kind (XKind(..))
import Stella.Compiler.Elaborate.Mechanism.Kinding (KindEvidence(..), wellFormedKey)
import Stella.Compiler.Elaborate.CorePlus.Term (XExpr(..))
import Stella.Compiler.Elaborate.CorePlus.Type (XConstraint(..), XRowEntry(..), XType(..))
import Stella.Compiler.TypedCore (RowElemKind(..), RowKey)
import Stella.Compiler.TypedCore.Prim (functionTy, recordTy, variantTy)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))

-- | `{}`, at `Record ()`.
recordEmpty :: Handle -> Elab Handle
recordEmpty scopeHandle = do
  scope <- resolveScope scopeHandle
  issueTerm scope (ERecordEmpty unit) (record XRowEmpty)

-- | `extend k e1 e2`, at `Record ( k : τ1 | r )` where `e2` is claimed at
-- | `Record r`, requiring `k ∉ r`.
recordExtend :: Handle -> RowKey -> Handle -> Handle -> Elab Handle
recordExtend scopeHandle key valueHandle restHandle = do
  scope <- resolveScope scopeHandle
  typeKey key
  value <- usableTermIn scope valueHandle
  rest <- usableTermIn scope restHandle
  row <- recordRowOf rest restHandle
  requiredIn scope (XLacks key row)
  issueTerm scope (ERecordExtend unit key value.term rest.term) (record (XRowExtend (XRowTypeEntry key value.claimed) row))

-- | `select k e`, at the type the record's row carries at `k`.
recordSelect :: Handle -> RowKey -> Handle -> Elab Handle
recordSelect scopeHandle key termHandle = do
  scope <- resolveScope scopeHandle
  term <- usableTermIn scope termHandle
  row <- recordRowOf term termHandle
  at <- rowAt (NotARecord termHandle) termHandle row key
  issueTerm scope (ERecordSelect unit key term.term) at.payload

-- | `restrict k e`, at the record without `k`.
recordRestrict :: Handle -> RowKey -> Handle -> Elab Handle
recordRestrict scopeHandle key termHandle = do
  scope <- resolveScope scopeHandle
  term <- usableTermIn scope termHandle
  row <- recordRowOf term termHandle
  at <- rowAt (NotARecord termHandle) termHandle row key
  issueTerm scope (ERecordRestrict unit key term.term) (record at.rest)

-- | `update k e1 e2`, at the record with `k` carrying what `e2` is claimed at,
-- | the type a field holds being free to change.
recordUpdate :: Handle -> RowKey -> Handle -> Handle -> Elab Handle
recordUpdate scopeHandle key termHandle valueHandle = do
  scope <- resolveScope scopeHandle
  term <- usableTermIn scope termHandle
  value <- usableTermIn scope valueHandle
  row <- recordRowOf term termHandle
  at <- rowAt (NotARecord termHandle) termHandle row key
  issueTerm scope (ERecordUpdate unit key term.term value.term) (record (XRowExtend (XRowTypeEntry key value.claimed) at.rest))

-- | `merge e1 e2`, at `Record ( r1 ⊎ r2 )`, requiring `r1 # r2`.
recordMerge :: Handle -> Handle -> Handle -> Elab Handle
recordMerge scopeHandle leftHandle rightHandle = do
  scope <- resolveScope scopeHandle
  left <- usableTermIn scope leftHandle
  right <- usableTermIn scope rightHandle
  l <- recordRowOf left leftHandle
  r <- recordRowOf right rightHandle
  requiredIn scope (XDisjoint l r)
  issueTerm scope (ERecordMerge unit left.term right.term) (record (XRowUnion l r))

-- | `inject k e`, at `Variant ( k : τ )`: a variant of one element. It is
-- | widened by `weaken`, and by nothing written here.
variantInject :: Handle -> RowKey -> Handle -> Elab Handle
variantInject scopeHandle key termHandle = do
  scope <- resolveScope scopeHandle
  typeKey key
  term <- usableTermIn scope termHandle
  issueTerm scope (EVariantInject unit key term.term) (variant (XRowExtend (XRowTypeEntry key term.claimed) XRowEmpty))

-- | `weaken k [τ] e`, at `Variant ( k : τ | r )` where `e` is claimed at
-- | `Variant r`, requiring `k ∉ r`. `τ` is a type the scope may use, at `Type`.
variantWeaken :: Handle -> RowKey -> Handle -> Handle -> Elab Handle
variantWeaken scopeHandle key payloadHandle termHandle = do
  scope <- resolveScope scopeHandle
  typeKey key
  payload <- valueType scope payloadHandle
  term <- usableTermIn scope termHandle
  row <- variantRowOf term termHandle
  requiredIn scope (XLacks key row)
  issueTerm scope (EVariantWeaken unit key payload term.term) (variant (XRowExtend (XRowTypeEntry key payload) row))

-- | `absurd [τ] e`, at `τ`, a type the scope may use at `Type`, where `e` is
-- | claimed at a variant. That the variant is empty is the Core type checker's.
variantAbsurd :: Handle -> Handle -> Handle -> Elab Handle
variantAbsurd scopeHandle resultHandle termHandle = do
  scope <- resolveScope scopeHandle
  result <- valueType scope resultHandle
  term <- usableTermIn scope termHandle
  _ <- variantRowOf term termHandle
  issueTerm scope (EVariantAbsurd unit result term.term) result

-- | `openEff [r'] e`, at `τ1 -{r1 ⊎ r'}-> τ2` where `e` is claimed at
-- | `τ1 -{r1}-> τ2`, requiring `r1 # r'`. `r'` is a type the scope may use, at
-- | `Row Effect`.
openEff :: Handle -> Handle -> Handle -> Elab Handle
openEff scopeHandle rowHandle termHandle = do
  scope <- resolveScope scopeHandle
  added <- usableIn scope rowHandle
  case added.kind of
    ExactKind (XKRow RowEffect) -> pure unit
    AnyRow -> pure unit
    _ -> rejected (NotAnEffectRow rowHandle)
  term <- usableTermIn scope termHandle
  metas <- currentMetas
  fn <- case functionShape metas term.claimed of
    Seen fn -> pure fn
    Blocked ms -> postpone ms
    Otherwise -> rejected (NotAFunction termHandle)
  requiredIn scope (XDisjoint fn.row added.type)
  issueTerm scope (EOpenEff unit added.type term.term)
    (XApp (XApp (XApp (XCon functionTy []) fn.argument) (XRowUnion fn.row added.type)) fn.result)

-- The row of the record a term is claimed at.
recordRowOf :: ExprObject -> Handle -> Elab XType
recordRowOf term handle = do
  metas <- currentMetas
  case recordShape metas term.claimed of
    Seen row -> pure row
    Blocked ms -> postpone ms
    Otherwise -> rejected (NotARecord handle)

-- The row of the variant a term is claimed at.
variantRowOf :: ExprObject -> Handle -> Elab XType
variantRowOf term handle = do
  metas <- currentMetas
  case variantShape metas term.claimed of
    Seen row -> pure row
    Blocked ms -> postpone ms
    Otherwise -> rejected (NotAVariant handle)

-- A key a record's or a variant's row may carry: well-formed at `Row Type`.
typeKey :: RowKey -> Elab Unit
typeKey key = do
  env <- askEnv
  case wellFormedKey env.session.kinding key (Just RowType) of
    Left fault -> rejected (IllKinded fault)
    Right _ -> pure unit

record :: XType -> XType
record row = XApp (XCon recordTy []) row

variant :: XType -> XType
variant row = XApp (XCon variantTy []) row
