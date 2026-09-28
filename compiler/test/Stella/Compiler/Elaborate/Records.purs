-- | The kernel's record, variant, and `openEff` builders.
-- |
-- | Three things are what these cases are for. **Each term is claimed at the
-- | type its Core rule gives it**, read off its parts, a type the term writes
-- | being given. **A row is read at a key by one procedure**, so `select`,
-- | `restrict`, and `update` agree on what is there, what is waited on, and
-- | what is a misuse. And **a row a term builds is sharp**: the requirement
-- | that makes it so comes with the term.
module Test.Stella.Compiler.Elaborate.Records (spec) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.Build (emptyRow, rootScope, typeConstructor)
import Stella.Compiler.Elaborate.BuildRecord (openEff, recordEmpty, recordExtend, recordMerge, recordRestrict, recordSelect, recordUpdate, variantAbsurd, variantInject, variantWeaken)
import Stella.Compiler.Elaborate.BuildTerm (literal, localVariable)
import Stella.Compiler.Elaborate.Catalog (catalogOf)
import Stella.Compiler.Elaborate.Constructors (constructorsOf)
import Stella.Compiler.Elaborate.Effects (effectsOf)
import Stella.Compiler.Elaborate.Context (Origin(..), XContext, bindTyVar, bindVar, emptyXContext)
import Stella.Compiler.Elaborate.Diagnostic (BuildError(..), Defect(..), Diagnostic(..))
import Stella.Compiler.Elaborate.Elab (Cause(..), Elab, Frame, Outcome(..), SessionEnv, SolverState, initialState, resolveExpr, runElabIn, withFrame)
import Stella.Compiler.Elaborate.Handle (Handle, SessionId(..))
import Stella.Compiler.Elaborate.Kind (XKind(..))
import Stella.Compiler.Elaborate.Kinding (kindingOf)
import Stella.Compiler.Elaborate.Obligation (Basis(..), Breach(..))
import Stella.Compiler.Elaborate.Pending (Site)
import Stella.Compiler.Elaborate.Row (xnf)
import Stella.Compiler.Elaborate.Solve (freshMetaType)
import Stella.Compiler.Elaborate.Term (toCoreExpr)
import Stella.Compiler.Elaborate.Type (MetaVar, XRowEntry(..), XType(..), toCore)
import Stella.Compiler.Elaborate.Unify (emptyContext, freshMeta)
import Stella.Compiler.Elaborate.View (KindView(..))
import Stella.Compiler.TypedCore (Decl(..), EffName(..), Ident(..), Literal(..), ModuleName(..), Qualified(..), RowElemKind(..), RowKey(..), Symbol(..), TyVar(..), monoScheme)
import Stella.Compiler.TypedCore.Declare (declare)
import Stella.Compiler.TypedCore.Prim (booleanTy, functionTy, intTy, primSignature, recordTy, variantTy)
import Data.Array as Array
import Data.Either (Either(..), isRight)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..), fst, snd)
import Effect.Aff (Aff)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

xInt :: XType
xInt = XCon intTy []

xBoolean :: XType
xBoolean = XCon booleanTy []

record :: XType -> XType
record row = XApp (XCon recordTy []) row

variant :: XType -> XType
variant row = XApp (XCon variantTy []) row

fnType :: XType -> XType -> XType -> XType
fnType argument row result = XApp (XApp (XApp (XCon functionTy []) argument) row) result

keyN :: RowKey
keyN = SymbolKey (Symbol "n")

keyM :: RowKey
keyM = SymbolKey (Symbol "m")

keyK :: RowKey
keyK = SymbolKey (Symbol "k")

r :: TyVar
r = TyVar "r"

field :: RowKey -> XType -> XType -> XType
field key ty rest = XRowExtend (XRowTypeEntry key ty) rest

-- | A flexible row tail `?t`, and the state holding it.
tailed :: Tuple MetaVar SolverState
tailed =
  let
    Tuple t metas = freshMeta { kind: XKRow RowType, scope: { types: Set.singleton r, kinds: Set.empty } } emptyContext
    initial = initialState (SessionId 0) 10
  in
    Tuple t (initial { tentative = initial.tentative { metas = metas } })

tail :: MetaVar
tail = fst tailed

-- | A site binding `r : Row Type`, records closed, open, and ending in `r`, the
-- | empty variant, and a pure function on `Int`.
context :: XContext
context =
  Array.foldl (\ctx (Tuple name ty) -> bindVar ctx (Ident name) ty) (bindTyVar emptyXContext r (XKRow RowType))
    [ Tuple "rec" (record (field keyN xInt (field keyM xInt XRowEmpty)))
    , Tuple "open" (record (field keyN xInt (XMeta tail)))
    , Tuple "rigid" (record (field keyN xInt (XVar r)))
    , Tuple "none" (variant XRowEmpty)
    , Tuple "f" (fnType xInt XRowEmpty xInt)
    ]

session :: SessionEnv
session = { catalog: catalogOf [], kinding: kindingOf primSignature, constructors: constructorsOf primSignature, effects: effectsOf primSignature }

site :: Site
site = { context, origin: InDeclaration (Qualified (ModuleName "Main") (Ident "decl")) }

frame :: Frame
frame = { site, goal: Nothing }

outcomeOf :: forall a. Elab a -> Outcome a
outcomeOf action = fst (runElabIn session (snd tailed) (withFrame frame action))

claims :: Elab Handle -> (XType -> Aff Unit) -> Aff Unit
claims action check = case outcomeOf (action >>= resolveExpr <#> _.claimed) of
  Done ty -> check ty
  other -> fail ("the builder did not complete: " <> show other)

refuses :: forall a. Show a => Elab a -> (BuildError -> P.Boolean) -> Aff Unit
refuses action test = case outcomeOf action of
  Broke (BuildRejected err) | test err -> pure unit
  other -> fail ("not the refusal expected: " <> show other)

rejects :: forall a. Show a => Elab a -> Basis -> Breach -> Aff Unit
rejects action basis breach = case outcomeOf action of
  Failed (ObligationRejected rejected) -> do
    rejected.basis `shouldEqual` basis
    rejected.breach `shouldEqual` breach
  other -> fail ("expected a rejected obligation: " <> show other)

-- | The known keys of the row a record's or a variant's claim holds, with the
-- | type each carries, and whether a tail remains.
known :: XType -> Maybe (Tuple (P.Array (Tuple RowKey XType)) P.Boolean)
known = case _ of
  XApp (XCon _ []) row -> case xnf row of
    Right n -> Just
      ( Tuple
          (Array.mapMaybe payload (Map.toUnfoldable n.known))
          (not (Set.isEmpty n.rigid && Set.isEmpty n.flexible))
      )
    Left _ -> Nothing
  _ -> Nothing
  where
  payload (Tuple key entry) = case entry of
    XRowTypeEntry _ ty -> Just (Tuple key ty)
    _ -> Nothing

var :: P.String -> Elab Handle
var name = rootScope >>= \root -> localVariable root (Ident name)

lit :: Literal -> Elab Handle
lit l = rootScope >>= \root -> literal root l

-- | `extend k 1 e`.
extendWith :: RowKey -> Elab Handle -> Elab Handle
extendWith key rest = do
  root <- rootScope
  e <- rest
  one <- literal root (LitInt 1)
  recordExtend root key one e

empty :: Elab Handle
empty = rootScope >>= recordEmpty

spec :: Spec Unit
spec = describe "Elaborate.BuildRecord" do
  describe "records" do
    it "are built from the empty record, one field at a time" do
      claims empty (_ `shouldEqual` record XRowEmpty)
      claims (extendWith keyN empty) (_ `shouldEqual` record (field keyN xInt XRowEmpty))

    it "refuse by the requirement they come with a key the rest carries or may carry" do
      rejects (extendWith keyN (var "rec")) Required (SolutionCarriesKey keyN)
      rejects (extendWith keyK (var "rigid")) Required (LacksUnprovenAtSite keyK r)
      refuses (extendWith (EffectKey (Qualified (ModuleName "Main") (EffName "Absent"))) empty) case _ of
        IllKinded _ -> true
        _ -> false

    it "are read at a key by select, restrict, and update alike" do
      let
        at builder = rootScope >>= \root -> var "rec" >>= builder root
      claims (at \root e -> recordSelect root keyN e) (_ `shouldEqual` xInt)
      claims (at \root e -> recordRestrict root keyN e) \ty ->
        known ty `shouldEqual` Just (Tuple [ Tuple keyM xInt ] false)
      claims (at \root e -> literal root (LitBoolean true) >>= recordUpdate root keyN e) \ty ->
        known ty `shouldEqual` Just (Tuple [ Tuple keyM xInt, Tuple keyN xBoolean ] false)

    it "wait on a flexible tail for a key they lack, and refuse one a closed or rigid row lacks" do
      let
        selectK name = rootScope >>= \root -> var name >>= recordSelect root keyK
        absent = case _ of
          FieldAbsent _ _ -> true
          _ -> false
      case outcomeOf (selectK "open") of
        Postponed (ExplicitPostponement ms) -> ms `shouldEqual` Set.singleton tail
        other -> fail ("expected a postponement: " <> show other)
      refuses (selectK "rec") absent
      refuses (rootScope >>= \root -> var "open" >>= recordSelect root (PositionKey (-1))) case _ of
        IllKinded _ -> true
        _ -> false
      refuses (selectK "rigid") absent
      refuses (rootScope >>= \root -> lit (LitInt 0) >>= recordSelect root keyN) case _ of
        NotARecord _ -> true
        _ -> false

    it "merge at the union of their rows, requiring the rows apart" do
      claims (rootScope >>= \root -> join (recordMerge root <$> extendWith keyN empty <*> extendWith keyM empty)) \ty ->
        known ty `shouldEqual` Just (Tuple [ Tuple keyM xInt, Tuple keyN xInt ] false)
      rejects (rootScope >>= \root -> join (recordMerge root <$> var "rec" <*> extendWith keyN empty)) Required (SidesShareKey keyN)

  describe "variants" do
    it "are injected at one element and widened by weaken" do
      let
        injected = rootScope >>= \root -> lit (LitInt 1) >>= variantInject root keyN
        weakened key = do
          root <- rootScope
          boolean <- typeConstructor root booleanTy []
          injected >>= variantWeaken root key boolean
      claims injected (_ `shouldEqual` variant (field keyN xInt XRowEmpty))
      claims (weakened keyM) (_ `shouldEqual` variant (field keyM xBoolean (field keyN xInt XRowEmpty)))
      rejects (weakened keyN) Required (SolutionCarriesKey keyN)
      refuses (rootScope >>= \root -> emptyRow root >>= \row -> injected >>= variantWeaken root keyM row) case _ of
        NotAType _ -> true
        _ -> false

    it "are eliminated by absurd at the type given" do
      claims (rootScope >>= \root -> typeConstructor root intTy [] >>= \i -> var "none" >>= variantAbsurd root i) (_ `shouldEqual` xInt)
      refuses (rootScope >>= \root -> typeConstructor root intTy [] >>= \i -> lit (LitInt 0) >>= variantAbsurd root i) case _ of
        NotAVariant _ -> true
        _ -> false

  describe "openEff" do
    it "adds the row given to a function's arrow, requiring the two apart" do
      claims (rootScope >>= \root -> emptyRow root >>= \row -> var "f" >>= openEff root row) (_ `shouldEqual` fnType xInt (XRowUnion XRowEmpty XRowEmpty) xInt)
      refuses (rootScope >>= \root -> freshMetaType root (KindRow RowType) >>= \row -> var "f" >>= openEff root row) case _ of
        NotAnEffectRow _ -> true
        _ -> false
      refuses (rootScope >>= \root -> emptyRow root >>= \row -> lit (LitInt 0) >>= openEff root row) case _ of
        NotAFunction _ -> true
        _ -> false

  describe "the Core type checker" do
    it "accepts records and variants the kernel built, at the types they are claimed at" do
      let
        built =
          traverse (\action -> action >>= resolveExpr)
            [ extendWith keyN empty
            , rootScope >>= \root -> extendWith keyN empty >>= recordSelect root keyN
            , do
                root <- rootScope
                boolean <- typeConstructor root booleanTy []
                lit (LitInt 1) >>= variantInject root keyN >>= variantWeaken root keyM boolean
            ]
        declOf i o = case toCore o.claimed, toCoreExpr o.term of
          Just scheme, Right value ->
            Just (DeclNonRec unit { name: Ident ("d" <> show i), scheme: monoScheme scheme, value, attributes: [] })
          _, _ -> Nothing
      case outcomeOf built of
        Done objects -> case traverse (\(Tuple i o) -> declOf i o) (Array.mapWithIndex Tuple objects) of
          Just decls -> isRight (declare primSignature { annotation: unit, name: ModuleName "Main", imports: [], exports: [], decls }) `shouldEqual` true
          Nothing -> fail "a term did not cross the boundary"
        other -> fail (show other)
