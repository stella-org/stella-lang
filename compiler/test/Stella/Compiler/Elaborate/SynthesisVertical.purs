-- | Hand-written Core⁺ with a synthesis hole in it, the hole filled by the
-- | reference synthesizer through the scheduler, and the term zonked.
-- |
-- | ```text
-- | Core⁺ with ?m → a goal queued → the loop → the reference synthesizer
-- |   → the target assigned → Completed → zonk
-- | ```
-- |
-- | Two things are what these cases are for. **A goal is answered from where it
-- | was asked**: the synthesizer reads the goal's type and the bindings of the
-- | site it was created at, however late the loop runs it, each goal its own.
-- | And **the answer lands where the hole stood**: zonked, the hole is the term
-- | the synthesizer built, carrying the hole's annotation.
module Test.Stella.Compiler.Elaborate.SynthesisVertical (spec) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.CorePlus.Context (Origin(..), bindVar, emptyXContext)
import Stella.Compiler.Elaborate.CorePlus.Term (TermMetaVar, XExpr(..))
import Stella.Compiler.Elaborate.CorePlus.Type (XType(..))
import Stella.Compiler.Elaborate.Driver.Loop (RunResult(..))
import Stella.Compiler.Elaborate.Driver.Synthesis (Registry, runSynthesis)
import Stella.Compiler.Elaborate.Environment.Catalog (EntrySort(..), catalogOf)
import Stella.Compiler.Elaborate.Environment.Constructors (constructorsOf)
import Stella.Compiler.Elaborate.Environment.Effects (effectsOf)
import Stella.Compiler.Elaborate.Kernel.Elab (Outcome(..), SessionEnv, SolverState, createSynthesis, initialState, runElabIn)
import Stella.Compiler.Elaborate.Mechanism.Kinding (kindingOf)
import Stella.Compiler.Elaborate.Mechanism.Pending (Site)
import Stella.Compiler.Elaborate.Mechanism.TermMeta (zonkExpr)
import Stella.Compiler.Elaborate.Mechanism.Unify (TermBinding(..), lookupTermMeta)
import Stella.Compiler.Elaborate.Vocabulary.Diagnostic (Diagnostic(..))
import Stella.Compiler.Elaborate.Vocabulary.Handle (SessionId(..))
import Stella.Compiler.Elaborate.Vocabulary.Trace (Tracing(..))
import Stella.Compiler.TypedCore (Decl(..), Expr(..), Ident(..), Literal(..), Module, ModuleName(..), Qualified(..), Type(..), monoScheme)
import Stella.Compiler.TypedCore.Declare (declare)
import Stella.Compiler.TypedCore.Prim (booleanTy, intTy, primSignature)
import Stella.Compiler.TypedCore.Signature (Signature)
import Data.Either (Either(..), either)
import Data.Foldable (foldl)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Effect.Aff (Aff)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)
import Test.Stella.Compiler.Elaborate.Reference (reference)

main :: ModuleName
main = ModuleName "Main"

mainOne :: Qualified Ident
mainOne = Qualified main (Ident "one")

xInt :: XType
xInt = XCon intTy []

xBoolean :: XType
xBoolean = XCon booleanTy []

-- | `one = 1`, a monomorphic global at `Int`.
valuesModule :: Module P.Int
valuesModule =
  { annotation: 0
  , name: main
  , imports: []
  , exports: []
  , decls: [ DeclNonRec 1 { name: Ident "one", scheme: monoScheme (TCon intTy []), value: Lit 1 (LitInt 1), attributes: [] } ]
  }

signature :: Signature
signature = either (const primSignature) identity (declare primSignature valuesModule)

session :: SessionEnv
session =
  { catalog: catalogOf [ { name: mainOne, sort: ValueEntry, scheme: { kindVars: [], body: xInt }, attributes: [] } ]
  , kinding: kindingOf signature
  , constructors: constructorsOf signature
  , effects: effectsOf signature
  , tracing: TraceDisabled
  }

resolver :: Qualified Ident
resolver = Qualified (ModuleName "Synth") (Ident "reference")

registry :: Registry
registry = Map.singleton resolver (reference [ mainOne ])

x :: Ident
x = Ident "x"

y :: Ident
y = Ident "y"

-- | A site binding the variables given.
siteBinding :: P.Array (Tuple Ident XType) -> Site
siteBinding bindings =
  { context: foldl (\ctx (Tuple name ty) -> bindVar ctx name ty) emptyXContext bindings
  , origin: InDeclaration (Qualified main (Ident "decl"))
  }

-- | Goals asked of the reference synthesizer at the sites and types given,
-- | queued in that order from one action, and the loop run over them.
answered :: P.Array (Tuple Site XType) -> Either P.String (Tuple (P.Array TermMetaVar) (Tuple RunResult SolverState))
answered asks = case runElabIn session (initialState (SessionId 0) 10) (traverse ask asks) of
  Tuple (Done targets) queued -> case runSynthesis session registry queued of
    Tuple report s -> Right (Tuple targets (Tuple report.result s))
  Tuple other _ -> Left (show other)
  where
  ask (Tuple site ty) = createSynthesis site ty resolver Nothing <#> \(Tuple _ target) -> target

givenAnswered :: P.Array (Tuple Site XType) -> (P.Array TermMetaVar -> RunResult -> SolverState -> Aff Unit) -> Aff Unit
givenAnswered asks check = case answered asks of
  Right (Tuple targets (Tuple result s)) -> check targets result s
  Left err -> fail err

spec :: Spec Unit
spec = describe "Elaborate, a synthesis hole filled by the reference synthesizer" do
  it "is answered from what its site binds, and zonks to the variable where the hole stood" do
    givenAnswered [ Tuple (siteBinding [ Tuple x xInt ]) xInt ] \targets result s -> case targets of
      [ m ] -> do
        result `shouldEqual` Completed
        -- `λ(x : Int). ?m`, the hole annotated 7 and the rest 0.
        zonkExpr s.tentative.metas (ELam 0 x xInt (ETermMeta 7 m)) `shouldEqual` ELam 0 x xInt (EVar 7 x)
      other -> fail (show other)

  it "is answered from the globals given where nothing its site binds has its type" do
    givenAnswered [ Tuple (siteBinding [ Tuple x xBoolean ]) xInt ] \targets result s -> case targets of
      [ m ] -> do
        result `shouldEqual` Completed
        -- `λ(x : Boolean). ?m`.
        zonkExpr s.tentative.metas (ELam 0 x xBoolean (ETermMeta 7 m)) `shouldEqual` ELam 0 x xBoolean (EGlobal 7 mainOne [])
      other -> fail (show other)

  it "reads the site each goal was created at, however late the loop runs it" do
    let
      -- Two goals queued together, each at a site binding one variable at
      -- `Int`: each is answered with its own.
      asks = [ Tuple (siteBinding [ Tuple x xInt ]) xInt, Tuple (siteBinding [ Tuple y xInt ]) xInt ]
    givenAnswered asks \targets result s -> do
      result `shouldEqual` Completed
      map (\m -> zonkExpr s.tentative.metas (ETermMeta 3 m)) targets `shouldEqual` [ EVar 3 x, EVar 3 y ]

  it "fails where nothing its site binds, and no global given, has its type, the hole left" do
    givenAnswered [ Tuple (siteBinding []) xBoolean ] \targets result s -> case targets of
      [ m ] -> do
        case result of
          Rejected (SynthesisFailed _) -> pure unit
          other -> fail (show other)
        case lookupTermMeta s.tentative.metas m of
          Just (TermUnsolved _) -> pure unit
          other -> fail ("the hole was not left: " <> show other)
      other -> fail (show other)
