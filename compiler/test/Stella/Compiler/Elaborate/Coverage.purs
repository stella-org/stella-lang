-- | Every form of a Core⁺ term, decision tree, occurrence, and operation clause,
-- | reached by the kernel's requests alone.
-- |
-- | What this case is for is that **no form of Core⁺ is out of a synthesizer's
-- | reach except the one that is so by design**: a typed hole, which is the
-- | Surface elaborator's for reporting and recovery. A term metavariable is
-- | reached too, by `subgoal` alone, which makes it together with the job that
-- | fills it. The forms are named by a function that matches every constructor,
-- | so a form added to Core⁺ does not compile here until it is named, and is not
-- | reached until a request builds it.
module Test.Stella.Compiler.Elaborate.Coverage (spec) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.Build (emptyRow, rootScope, typeConstructor)
import Stella.Compiler.Elaborate.BuildHandler (closeHandle, openHandle, perform, readCell, writeCell)
import Stella.Compiler.Elaborate.BuildRecord (openEff, recordEmpty, recordExtend, recordMerge, recordRestrict, recordSelect, recordUpdate, variantAbsurd, variantInject, variantWeaken)
import Stella.Compiler.Elaborate.BuildTerm (closeConstraintAbs, closeJoin, closeLambda, closeLet, closeLetRec, closeTypeAbs, constraintApply, globalRef, jump, literal, localVariable, openConstraintAbs, openJoin, openLambda, openLet, openLetRec, openTypeAbs, termApply, typeApply)
import Stella.Compiler.Elaborate.BuildTree (closeBind, closeCase, closeSwitch, guard, leaf, openBind, openCase, openSwitchCtor, openSwitchKey, openSwitchLit, recordField)
import Stella.Compiler.Elaborate.Catalog (EntrySort(..), catalogOf)
import Stella.Compiler.Elaborate.Constructors (constructorsOf)
import Stella.Compiler.Elaborate.Context (Origin(..), XContext, bindVar, emptyXContext)
import Stella.Compiler.Elaborate.Diagnostic (Diagnostic(..))
import Stella.Compiler.Elaborate.Effects (effectsOf)
import Stella.Compiler.Elaborate.Elab (Elab, Frame, Outcome(..), SessionEnv, initialState, resolveExpr, runElabIn, throw, withFrame)
import Stella.Compiler.Elaborate.Handle (Handle, SessionId(..))
import Stella.Compiler.Elaborate.Kinding (kindingOf)
import Stella.Compiler.Elaborate.Pending (Site)
import Stella.Compiler.Elaborate.Solve (subgoal)
import Stella.Compiler.Elaborate.Term (XDecisionTree(..), XExpr(..), XOpClause(..))
import Stella.Compiler.Elaborate.Type (XRowEntry(..), XType(..))
import Stella.Compiler.Elaborate.Unify (UnifyError(..))
import Stella.Compiler.Elaborate.View (ConstraintView(..), KindView(..), PayloadView(..))
import Stella.Compiler.TypedCore (Decl(..), EffName(..), Ident(..), Literal(..), Module, ModuleName(..), Occurrence(..), OpName(..), Qualified(..), RowKey(..), Symbol(..), TyName(..), Type(..))
import Stella.Compiler.TypedCore.Declare (declare)
import Stella.Compiler.TypedCore.Prim (booleanTy, intTy, primSignature, recordTy, unitTy, variantTy)
import Stella.Compiler.TypedCore.Signature (Signature)
import Data.Array as Array
import Data.Either (either)
import Data.Foldable (foldMap)
import Data.Maybe (Maybe(..), maybe)
import Data.Set as Set
import Data.Traversable (traverse)
import Data.Tuple (fst)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)
import Test.Stella.Compiler.TypedCore.VerticalSlice (listDecl)

main :: ModuleName
main = ModuleName "Main"

qualified :: P.String -> Qualified Ident
qualified name = Qualified main (Ident name)

counter :: Qualified EffName
counter = Qualified main (EffName "Counter")

next :: OpName
next = OpName "next"

keyN :: RowKey
keyN = SymbolKey (Symbol "n")

keyM :: RowKey
keyM = SymbolKey (Symbol "m")

xInt :: XType
xInt = XCon intTy []

-- | `List`, and `effect Counter { next : Unit ->* Int }`.
dataModule :: Module P.Int
dataModule =
  { annotation: 0
  , name: main
  , imports: []
  , exports: []
  , decls:
      [ listDecl
      , DeclEffect 2
          { name: EffName "Counter"
          , params: []
          , operations: [ { name: next, tyBinders: [], argument: TCon unitTy [], resumesWith: TCon intTy [] } ]
          , attributes: []
          }
      ]
  }

signature :: Signature
signature = either (const primSignature) identity (declare primSignature dataModule)

session :: SessionEnv
session =
  { catalog: catalogOf [ { name: qualified "one", sort: ValueEntry, scheme: { kindVars: [], body: xInt }, attributes: [] } ]
  , kinding: kindingOf signature
  , constructors: constructorsOf signature
  , effects: effectsOf signature
  }

-- | A site binding a list, a variant, the empty variant, and a unit.
context :: XContext
context =
  Array.foldl (\ctx b -> bindVar ctx (Ident b.name) b.ty) emptyXContext
    [ { name: "xs", ty: XApp (XCon (Qualified main (TyName "List")) []) xInt }
    , { name: "var", ty: XApp (XCon variantTy []) (XRowExtend (XRowTypeEntry keyN xInt) XRowEmpty) }
    , { name: "none", ty: XApp (XCon variantTy []) XRowEmpty }
    , { name: "u", ty: XCon unitTy [] }
    , { name: "rec", ty: XApp (XCon recordTy []) (XRowExtend (XRowTypeEntry keyN xInt) XRowEmpty) }
    ]

site :: Site
site = { context, origin: InDeclaration (qualified "decl") }

frame :: Frame
frame = { site, goal: Nothing }

failure :: Diagnostic
failure = EquationFailed site.origin (TypeNotEqual xInt xInt)

var :: Handle -> P.String -> Elab Handle
var scope name = localVariable scope (Ident name)

int :: Handle -> Elab Handle
int scope = typeConstructor scope intTy []

lit :: Handle -> P.Int -> Elab Handle
lit scope n = literal scope (LitInt n)

only :: forall a. P.Array a -> Elab a
only = case _ of
  [ x ] -> pure x
  _ -> throw failure

-- | Terms together holding every form but a typed hole, each built by the
-- | kernel's requests at the root.
everyForm :: Elab (P.Array Handle)
everyForm = do
  root <- rootScope
  i <- int root
  one <- lit root 1
  xs <- var root "xs"
  global <- globalRef root (qualified "one") []
  -- λ and its application
  lam <- openLambda root "x" i
  f <- emptyRow root >>= closeLambda root lam.binder lam.variable
  applied <- termApply root f one
  -- Λ(t) and its application
  tAbs <- openTypeAbs root "t" KindType
  tLam <- lit tAbs.bodyScope 0 >>= closeTypeAbs root tAbs.binder
  tApplied <- typeApply root tLam i
  -- Λ(_ : n ∉ ()) and its application
  cAbs <- emptyRow root >>= \e -> openConstraintAbs root (LacksView keyN e)
  cLam <- lit cAbs.bodyScope 0 >>= closeConstraintAbs root cAbs.binder
  cApplied <- constraintApply root cLam
  -- let and letrec
  bound <- openLet root "v" one
  letTerm <- closeLet root bound.binder bound.variable
  group <- openLetRec root [ { hint: "r", type: i } ]
  recursive <- only group.variables >>= \v -> closeLetRec root group.binder [ v ] v
  -- letjoin and jump
  j <- openJoin root "j" [ { hint: "p", type: i } ] i
  jumped <- lit j.bodyScope 0 >>= \n -> jump j.bodyScope j.join [ n ]
  joined <- only j.params >>= \p -> closeJoin root j.binder p jumped
  -- a case switching on constructors, binding, and guarding
  onList <- openCase root [ xs ]
  listOccurrence <- only onList.scrutinees
  byCtor <- openSwitchCtor onList.treeScope listOccurrence [ qualified "Nil", qualified "Cons" ] false
  ctorTrees <- case byCtor.branches of
    [ nilBranch, consBranch ] -> do
      condition <- literal nilBranch.scope (LitBoolean true)
      zero <- lit nilBranch.scope 0 >>= leaf nilBranch.scope
      two <- lit nilBranch.scope 2 >>= leaf nilBranch.scope
      guarded <- guard nilBranch.scope condition zero two
      headField <- Array.head consBranch.fields # maybe (throw failure) pure
      b <- openBind consBranch.scope headField "h"
      bindTree <- leaf b.bodyScope b.variable >>= closeBind consBranch.scope b.binder
      pure [ guarded, bindTree ]
    _ -> throw failure
  listCase <- closeSwitch onList.treeScope byCtor.binder ctorTrees Nothing >>= closeCase root onList.binder Nothing
  -- a case switching on a literal
  onLit <- openCase root [ one ]
  litOccurrence <- only onLit.scrutinees
  byLit <- openSwitchLit onLit.treeScope litOccurrence [ LitInt 1 ]
  litBranch <- only byLit.branches
  litTrees <- traverse (\scope -> lit scope 0 >>= leaf scope) [ litBranch ]
  litFallback <- lit byLit.fallback 1 >>= leaf byLit.fallback
  litCase <- closeSwitch onLit.treeScope byLit.binder litTrees (Just litFallback) >>= closeCase root onLit.binder Nothing
  -- a case switching on a key
  variant <- var root "var"
  onKey <- openCase root [ variant ]
  keyOccurrence <- only onKey.scrutinees
  byKey <- openSwitchKey onKey.treeScope keyOccurrence [ keyN ] false
  keyBranch <- only byKey.branches
  payloadBound <- openBind keyBranch.scope keyBranch.payload "p"
  keyTree <- leaf payloadBound.bodyScope payloadBound.variable >>= closeBind keyBranch.scope payloadBound.binder
  keyCase <- closeSwitch onKey.treeScope byKey.binder [ keyTree ] Nothing >>= closeCase root onKey.binder Nothing
  -- a case reading a record's field, which needs no dispatch
  record <- var root "rec"
  onRecord <- openCase root [ record ]
  recordOccurrence <- only onRecord.scrutinees
  field <- recordField onRecord.treeScope recordOccurrence keyN
  fieldBound <- openBind onRecord.treeScope field "f"
  recordCase <-
    leaf fieldBound.bodyScope fieldBound.variable
      >>= closeBind onRecord.treeScope fieldBound.binder
      >>= closeCase root onRecord.binder Nothing
  -- records and variants
  empty <- recordEmpty root
  extended <- recordExtend root keyN one empty
  selected <- recordSelect root keyN extended
  restricted <- recordRestrict root keyN extended
  updated <- recordUpdate root keyN extended one
  merged <- recordExtend root keyM one empty >>= recordMerge root extended
  injected <- variantInject root keyN one
  boolean <- typeConstructor root booleanTy []
  weakened <- variantWeaken root keyM boolean injected
  absurd <- var root "none" >>= variantAbsurd root i
  opened <- emptyRow root >>= \row -> openEff root row f
  -- perform, and handlers with a fast clause over cells and a full one
  performed <- var root "u" >>= perform root (EffectKey counter) (EffectPayload counter []) next []
  withCells <- do
    rho <- emptyRow root
    h <- openHandle root one (EffectKey counter) (EffectPayload counter []) (Just [ { key: keyN, type: i } ]) i rho [ { op: next, full: false } ]
    clause <- only h.clauses
    written <- lit clause.scope 1 >>= writeCell clause.scope keyN
    w <- openLet clause.scope "w" written
    body <- readCell w.bodyScope keyN >>= closeLet clause.scope w.binder
    initial <- lit root 0
    closeHandle root h.binder h.returnClause.variable [ body ] [ initial ]
  withContinuation <- do
    rho <- emptyRow root
    h <- openHandle root one (EffectKey counter) (EffectPayload counter []) Nothing i rho [ { op: next, full: true } ]
    clause <- only h.clauses
    k <- clause.continuation # maybe (throw failure) pure
    body <- lit clause.scope 0 >>= termApply clause.scope k
    closeHandle root h.binder h.returnClause.variable [ body ] []
  -- a goal
  goal <- subgoal root i (qualified "resolve")
  pure
    [ one
    , xs
    , global
    , applied
    , tApplied
    , cApplied
    , letTerm
    , recursive
    , joined
    , listCase
    , litCase
    , keyCase
    , recordCase
    , selected
    , restricted
    , updated
    , merged
    , weakened
    , absurd
    , opened
    , performed
    , withCells
    , withContinuation
    , goal
    ]

-- | The forms a term holds, each by the name of its constructor.
forms :: forall a. XExpr a -> P.Array P.String
forms = case _ of
  EVar _ _ -> [ "EVar" ]
  EGlobal _ _ _ -> [ "EGlobal" ]
  ELit _ _ -> [ "ELit" ]
  ELam _ _ _ body -> [ "ELam" ] <> forms body
  EApp _ f x -> [ "EApp" ] <> forms f <> forms x
  ETyLam _ _ _ body -> [ "ETyLam" ] <> forms body
  ETyApp _ e _ -> [ "ETyApp" ] <> forms e
  EConstraintLam _ _ body -> [ "EConstraintLam" ] <> forms body
  EConstraintApp _ e -> [ "EConstraintApp" ] <> forms e
  ELet _ _ _ v body -> [ "ELet" ] <> forms v <> forms body
  ELetRec _ bindings body -> [ "ELetRec" ] <> foldMap (forms <<< _.value) bindings <> forms body
  ECase _ scrutinees dt -> [ "ECase" ] <> foldMap forms scrutinees <> treeForms dt
  ELetJoin _ _ _ _ v body -> [ "ELetJoin" ] <> forms v <> forms body
  EJump _ _ args -> [ "EJump" ] <> foldMap forms args
  ERecordEmpty _ -> [ "ERecordEmpty" ]
  ERecordExtend _ _ v rest -> [ "ERecordExtend" ] <> forms v <> forms rest
  ERecordSelect _ _ e -> [ "ERecordSelect" ] <> forms e
  ERecordRestrict _ _ e -> [ "ERecordRestrict" ] <> forms e
  ERecordUpdate _ _ r v -> [ "ERecordUpdate" ] <> forms r <> forms v
  ERecordMerge _ l r -> [ "ERecordMerge" ] <> forms l <> forms r
  EVariantInject _ _ v -> [ "EVariantInject" ] <> forms v
  EVariantWeaken _ _ _ e -> [ "EVariantWeaken" ] <> forms e
  EVariantAbsurd _ _ e -> [ "EVariantAbsurd" ] <> forms e
  EPerform _ _ _ _ arg -> [ "EPerform" ] <> forms arg
  EHandle _ body h initial ->
    [ "EHandle" ] <> forms body <> forms h.returnClause.body <> foldMap clauseForms h.opClauses <> foldMap forms initial
  EReadCell _ _ -> [ "EReadCell" ]
  EWriteCell _ _ v -> [ "EWriteCell" ] <> forms v
  EOpenEff _ _ e -> [ "EOpenEff" ] <> forms e
  ETermMeta _ _ -> [ "ETermMeta" ]
  EHole _ _ -> [ "EHole" ]
  where
  treeForms = case _ of
    XLeaf e -> [ "XLeaf" ] <> forms e
    XBind _ o dt -> [ "XBind" ] <> occurrenceForms o <> treeForms dt
    XSwitchCtor o branches d -> [ "XSwitchCtor" ] <> occurrenceForms o <> foldMap (treeForms <<< _.tree) branches <> foldMap treeForms d
    XSwitchLit o branches d -> [ "XSwitchLit" ] <> occurrenceForms o <> foldMap (treeForms <<< _.tree) branches <> treeForms d
    XSwitchKey o branches d -> [ "XSwitchKey" ] <> occurrenceForms o <> foldMap (treeForms <<< _.tree) branches <> foldMap treeForms d
    XGuard e yes no -> [ "XGuard" ] <> forms e <> treeForms yes <> treeForms no

  clauseForms = case _ of
    XFullClause c -> [ "XFullClause" ] <> forms c.body
    XFastClause c -> [ "XFastClause" ] <> forms c.body

  occurrenceForms = case _ of
    OccScrutinee _ -> [ "OccScrutinee" ]
    OccField o _ _ -> [ "OccField" ] <> occurrenceForms o
    OccRecordField o _ -> [ "OccRecordField" ] <> occurrenceForms o
    OccVariantPayload o _ -> [ "OccVariantPayload" ] <> occurrenceForms o

-- | Every form of Core⁺ but the typed hole.
reachable :: P.Array P.String
reachable =
  [ "EVar"
  , "EGlobal"
  , "ELit"
  , "ELam"
  , "EApp"
  , "ETyLam"
  , "ETyApp"
  , "EConstraintLam"
  , "EConstraintApp"
  , "ELet"
  , "ELetRec"
  , "ECase"
  , "ELetJoin"
  , "EJump"
  , "ERecordEmpty"
  , "ERecordExtend"
  , "ERecordSelect"
  , "ERecordRestrict"
  , "ERecordUpdate"
  , "ERecordMerge"
  , "EVariantInject"
  , "EVariantWeaken"
  , "EVariantAbsurd"
  , "EPerform"
  , "EHandle"
  , "EReadCell"
  , "EWriteCell"
  , "EOpenEff"
  , "ETermMeta"
  , "XLeaf"
  , "XBind"
  , "XSwitchCtor"
  , "XSwitchLit"
  , "XSwitchKey"
  , "XGuard"
  , "XFullClause"
  , "XFastClause"
  , "OccScrutinee"
  , "OccField"
  , "OccRecordField"
  , "OccVariantPayload"
  ]

spec :: Spec Unit
spec = describe "Elaborate, the kernel's reach over Core⁺" do
  it "builds every form but the typed hole by its requests alone" do
    case fst (runElabIn session (initialState (SessionId 0) 10) (withFrame frame (everyForm >>= traverse resolveExpr))) of
      Done objects -> do
        let
          found = Set.fromFoldable (foldMap (forms <<< _.term) objects)
        Set.toUnfoldable found `shouldEqual` Array.sort reachable
        Set.member "EHole" found `shouldEqual` false
      other -> fail (show other)
