-- | Expressions resolved against a module's scope, each shown as a compact
-- | rendering of the Surface AST it becomes.
module Test.Stella.Compiler.Resolve.Expr (spec, renderExpr) where

import Prelude
import Prim hiding (Type)

import Data.Array as Array
import Data.Either (Either(..))
import Data.Map as Map
import Data.Maybe (Maybe(..), maybe)
import Data.Set as Set
import Data.String (joinWith)
import Data.Tuple (Tuple(..), fst)
import Effect.Aff (Aff)
import Stella.Compiler.CST (parseModule, printSyntaxError)
import Stella.Compiler.CST.Types as CST
import Stella.Compiler.Interface.Environment (BuildEnvironment, addInterface, initialEnvironment)
import Stella.Compiler.Interface.Module (ModuleInterface, TypeEntity(..), TypeSort(..), ValueSort(..), Via(..), emptyDeclarations, emptyExports)
import Stella.Compiler.Interface.Scheme (SchemeBody(..), plainScheme)
import Stella.Compiler.Resolve.Expr (resolveDefinition, resolveExpr, resolveHandler)
import Stella.Compiler.Resolve.Group (groupModule)
import Stella.Compiler.Resolve.Monad (CellClosure(..), HandledEffectProblem(..), Resolve, ResolveError(..), ResolveReason(..), ResolveWarning(..), ResumeBlock(..), contextOf, runResolve)
import Stella.Compiler.Resolve.Scope (resolveScope)
import Stella.Compiler.Surface.Decl (Associativity(..), FixityTarget(..))
import Stella.Compiler.Surface.Origin (Origin(..))
import Stella.Compiler.Surface.Expr (exprOrigin, AlternativeBody(..), Binder(..), ClauseForm(..), Expr(..), GuardLine(..), HandlerBody, HandlerItem(..), LetBinding(..), RecordField(..))
import Stella.Compiler.Surface.Name (BindingId(..), CellVar(..), LocalVar(..), OperatorName(..))
import Stella.Compiler.TypedCore.Domain (codePointOf, textOf)
import Stella.Compiler.TypedCore.Kind (Kind(..), RowElemKind(..), monoScheme)
import Stella.Compiler.TypedCore.Name (EffName(..), Ident(..), ModuleName(..), Qualified(..), Symbol(..), Tag(..), TyName(..))
import Stella.Compiler.TypedCore.Prim (intTy)
import Stella.Compiler.TypedCore.Term (Literal(..))
import Stella.Compiler.TypedCore.Type (RowEntry(..), Type(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

moduleA :: ModuleName
moduleA = ModuleName "A"

moduleB :: ModuleName
moduleB = ModuleName "B"

inA :: forall a. a -> Qualified a
inA = Qualified moduleA

-- | `A` declares the values `x`, `plus`, `times`, `eq`, and `append`, the
-- | computation `comp`, `data Maybe = Nothing | Just Int`, `data List = Nil |
-- | Cons Int List`, the effect `E` with its operations `get :: Int ->* Int` and
-- | `put :: Int -> Int ->* Int`, and the operators
-- | `+` (`infixl 6 plus`), `*` (`infixl 7 times`), `<>` (`infixr 6 append`),
-- | `==` (`infix 4 eq`), and `:|` (`infixr 5 Cons`). `B` declares `len`, and
-- | `Base.Continuation` nothing. `A` also declares `type Effects = {| E |}`.
environment :: BuildEnvironment
environment = case addInterface interfaceA initialEnvironment >>= addInterface interfaceB >>= addInterface continuation of
  Right env -> env
  Left _ -> initialEnvironment
  where
  interfaceA = withEffects $ interfaceOf moduleA
    { values: [ "x", "plus", "times", "eq", "append" ]
    , computations: [ "comp" ]
    , types: [ Tuple "Maybe" [ Tuple "Nothing" 0, Tuple "Just" 1 ], Tuple "List" [ Tuple "Nil" 0, Tuple "Cons" 2 ] ]
    , operations: [ Tuple "get" 1, Tuple "put" 2 ]
    , operators:
        [ Tuple "+" { associativity: AssociateLeft, precedence: 6, target: FixityValue (inA (Ident "plus")) }
        , Tuple "*" { associativity: AssociateLeft, precedence: 7, target: FixityValue (inA (Ident "times")) }
        , Tuple "<>" { associativity: AssociateRight, precedence: 6, target: FixityValue (inA (Ident "append")) }
        , Tuple "==" { associativity: AssociateNone, precedence: 4, target: FixityValue (inA (Ident "eq")) }
        , Tuple ":|" { associativity: AssociateRight, precedence: 5, target: FixityConstructor (inA (Ident "Cons")) }
        ]
    }
  interfaceB = interfaceOf moduleB { values: [ "len" ], computations: [], types: [], operations: [], operators: [] }
  continuation = interfaceOf (ModuleName "Base.Continuation") { values: [], computations: [], types: [], operations: [], operators: [] }
  -- `type Effects = {| E |}`, a row synonym.
  withEffects i = i
    { exports = i.exports { types = Map.insert "Effects" { entity: TypeEntity (inA (TyName "Effects")), via: Declared, members: [] } i.exports.types }
    , declarations = i.declarations
        { types = Map.insert (TyName "Effects")
            { kind: monoScheme (KRow RowEffect)
            , sort: Synonym { params: [], body: TRowExtend (RowEffectEntry (inA (EffName "E")) []) TRowEmpty }
            , attributes: []
            }
            i.declarations.types
        }
    }

interfaceOf
  :: ModuleName
  -> { values :: Array String
     , computations :: Array String
     , types :: Array (Tuple String (Array (Tuple String Int)))
     , operations :: Array (Tuple String Int)
     , operators :: Array (Tuple String { associativity :: Associativity, precedence :: Int, target :: FixityTarget })
     }
  -> ModuleInterface
interfaceOf name d =
  { name
  , imports: []
  , exports: emptyExports
      { values = Map.fromFoldable (map (\n -> Tuple n (declared (Qualified name (Ident n)))) (d.values <> d.computations <> map fst d.operations <> constructors))
      , types = Map.fromFoldable
          ( map (\(Tuple t _) -> Tuple t { entity: TypeEntity (Qualified name (TyName t)), via: Declared, members: [] }) d.types
              <> (if Array.null d.operations then [] else [ Tuple "E" { entity: EffectEntity (Qualified name (EffName "E")), via: Declared, members: [] } ])
          )
      , operators = Map.fromFoldable (map (\(Tuple op _) -> Tuple op (declared (Qualified name (OperatorName op)))) d.operators)
      }
  , declarations: emptyDeclarations
      { values = Map.fromFoldable
          ( map (\n -> Tuple (Ident n) { sort: SortValue, scheme: plain, attributes: [] }) d.values
              <> map (\n -> Tuple (Ident n) { sort: SortValue, scheme: { kindVars: [], body: Computation int TRowEmpty }, attributes: [] }) d.computations
              <> map (\(Tuple n _) -> Tuple (Ident n) { sort: SortOperation (Qualified name (EffName "E")), scheme: plain, attributes: [] }) d.operations
              <> Array.concatMap (\(Tuple t cs) -> map (\(Tuple c _) -> Tuple (Ident c) { sort: SortConstructor (Qualified name (TyName t)), scheme: plain, attributes: [] }) cs) d.types
          )
      , types = Map.fromFoldable
          ( map
              ( \(Tuple t cs) -> Tuple (TyName t)
                  { kind: monoScheme KType
                  , sort: DataType { params: [], constructors: map (\(Tuple c n) -> { name: Ident c, fields: Array.replicate n int }) cs, isNewtype: false }
                  , attributes: []
                  }
              )
              d.types
          )
      , effects =
          if Array.null d.operations then Map.empty
          else Map.singleton (EffName "E")
            { params: []
            , operations: map (\(Tuple n arity) -> { name: Ident n, binders: [], arguments: Array.replicate arity int, resumesWith: int }) d.operations
            , attributes: []
            }
      , operators = Map.fromFoldable (map (\(Tuple op entry) -> Tuple (OperatorName op) entry) d.operators)
      }
  , implicitHandlers: []
  , catalogOnly: Set.empty
  , arities: Map.empty
  }
  where
  int = TCon intTy []
  plain = plainScheme (monoScheme int)
  constructors = Array.concatMap (\(Tuple _ cs) -> map (\(Tuple c _) -> c) cs) d.types

  declared :: forall a. a -> { entity :: a, via :: Via }
  declared e = { entity: e, via: Declared }

type Ran = { result :: String, reasons :: Array ResolveReason, warnings :: Array String }

-- | The definition of `f` in the module `M`, which imports `A` unqualified
-- | and as `M`, and `B` lazily as `L`, and declares the computation `c`, the
-- | effect `Own` with its operation `tick`, and `<+>` (`infixl 4 own`).
definition :: Array String -> (Ran -> Aff Unit) -> Aff Unit
definition = definitionIn []

-- | The same, the module importing what the lines given import besides.
definitionIn :: Array String -> Array String -> (Ran -> Aff Unit) -> Aff Unit
definitionIn imports body = inModule imports body definitionOfF \d ->
  resolveDefinition d.params d.body d.local <#> \r -> renderExpr r.body
  where
  definitionOfF = case _ of
    CST.ItemDecl (CST.DeclValue n params rhs local) | n.name == "f" -> Just { params, body: rhs, local }
    _ -> Nothing

-- | The handler declaration `h` in the module `M`, shown as the effect it
-- | handles and its body.
handlerDeclaration :: Array String -> (Ran -> Aff Unit) -> Aff Unit
handlerDeclaration body = inModule [] body handlerOfH \d ->
  resolveHandler d.params d.signature d.items <#> \r ->
    maybe "?" effectWord r.effect <> renderBody r.body
  where
  handlerOfH = case _ of
    CST.ItemDecl (CST.DeclHandler n params signature items) | n.name == "h" -> Just { params, signature, items }
    _ -> Nothing

inModule
  :: forall d
   . Array String
  -> Array String
  -> (CST.Item -> Maybe d)
  -> (d -> Resolve String)
  -> (Ran -> Aff Unit)
  -> Aff Unit
inModule imports body pick resolve k = case parseModule (joinWith "\n" (header <> body)) of
  Left e -> fail (printSyntaxError e)
  Right m@(CST.Module cst) -> case Array.findMap pick cst.items of
    Nothing -> fail "no declaration to resolve"
    Just d -> do
      let
        grouped = (groupModule m).grouped
        ran = runResolve (contextOf environment grouped (resolveScope environment grouped).scoped) 0 (resolve d)
      k
        { result: ran.result
        , reasons: map (\(ResolveError _ reason) -> reason) ran.errors
        , warnings: map warningName ran.warnings
        }
  where
  header =
    [ "module M where"
    , "import A"
    , "import A as M"
    , "import lazy B as L"
    ]
      <> imports
      <>
        [ "c :: Int / {| |}"
        , "c = 1"
        , "effect Own where"
        , "  tick :: Unit ->* Unit"
        , "infixl 4 own as <+>"
        , "own a b = a"
        ]
  warningName = case _ of
    HidesTypeVariable _ n -> n
    HidesValue _ n -> n
    OpenHidesLocal _ n -> n

shows :: Array String -> String -> Array ResolveReason -> Aff Unit
shows body expected reasons = definition body \r -> do
  r.result `shouldEqual` expected
  r.reasons `shouldEqual` reasons

handles :: Array String -> String -> Array ResolveReason -> Aff Unit
handles body expected reasons = handlerDeclaration body \r -> do
  r.result `shouldEqual` expected
  r.reasons `shouldEqual` reasons

spec :: Spec Unit
spec = describe "Stella.Compiler.Resolve.Expr" do
  describe "what an expansion produced" do
    let
      call = CST.inSource { line: 9, column: 5 } { line: 9, column: 12 }
      space = CST.Expansion { id: CST.ExpansionId 0, macro: inA (Ident "m"), call, written: [ CST.inSource { line: 9, column: 8 } { line: 9, column: 11 } ] }
      inExpansion c = { space, start: { line: 1, column: c }, end: { line: 1, column: c + 1 } }
      resolving e k = inModule [] [ "f = 1" ] (const (Just unit)) (\_ -> renderExpr <$> resolveExpr e) k

    it "is resolved where the call stands, located in the expansion and through it at the call" do
      let expanded = CST.ExprExpanded { call, expr: CST.ExprVar { range: inExpansion 1, qualifier: Nothing, name: "own" } }
      inModule [] [ "f = 1" ] (const (Just unit)) (\_ -> resolveExpr expanded <#> \e -> show (exprOrigin e)) \r -> do
        r.reasons `shouldEqual` []
        r.result `shouldEqual` show (FromExpansion { range: inExpansion 1, macro: inA (Ident "m"), call: FromSource call, written: FromSource (CST.inSource { line: 9, column: 8 } { line: 9, column: 11 }) })
      resolving expanded \r -> r.result `shouldEqual` "M.own"

    it "leaves a call whose expansion failed invalid, and reports nothing more" do
      resolving (CST.ExprInvalid call) \r -> do
        r.result `shouldEqual` "!"
        r.reasons `shouldEqual` []

  describe "references" do
    it "become the node of what they name" do
      shows [ "f a = (a, x, comp, c, Just, Nothing?, get, tick, own, 'T, ?h, 1, true, 'c', \"s\", 1.5, ())" ]
        "(a#0, A.x, comp:A.comp, comp:M.c, A.Just, A.Nothing?, op:A.get, op:M.tick, M.own, 'T, ?h, 1, true, char99, \"s\", 1.5, Prim.Unit)"
        []

    it "report a name nothing in scope stands for" do
      shows [ "f = (nope, Nope, Nope?, Just.x)" ] "(!, !, !, !)"
        [ UnknownValue "nope", UnknownConstructor "Nope", UnknownConstructor "Nope", UnknownValue "Just.x" ]

    it "select an operation's instance by a label" do
      shows [ "f = (get@cache, x@cache, get@Cache)" ] "(op:A.get@cache, !, !)" [ NotAnOperation "x", LabelExpected ]

  describe "operators" do
    it "are rebracketed by fixity, a constructor's among them, and a name used infix binds as infixl 9" do
      shows [ "f = 1 + 2 * 3 + 4 <+> 5" ] "<M.own <A.plus <A.plus 1 <A.times 2 3>> 4> 5>" []
      shows [ "f = 1 :| 2 :| Nil" ] "<A.Cons 1 <A.Cons 2 A.Nil>>" []
      shows [ "f = 1 `plus` 2 * 3" ] "<A.times <A.plus 1 2> 3>" []
      shows [ "f = (+) 1 (:|)" ] "((A.plus 1) A.Cons)" []

    it "of one precedence that cannot be chained, and one nothing stands for, leave the chain invalid" do
      shows [ "f = 1 + 2 <> 3" ] "!" [ OperatorsUnordered "<>" "+" ]
      shows [ "f = 1 == 2 == 3" ] "!" [ OperatorsUnordered "==" "==" ]
      shows [ "f = 1 %% 2" ] "!" [ UnknownOperator "%%" ]
      shows [ "f = 1 `missing` 2 * 3" ] "!" [ UnknownValue "missing" ]
      shows [ "infixl 4 nope as <!>", "f = 1 <!> 2" ] "!" []

  describe "local scopes" do
    it "of a `let` block are recursive, every binding in scope in every right-hand side" do
      shows [ "f = let", "      g y = h y", "      h z = g z", "    in g" ]
        "(let g#0 y#2 = (h#1 y#2); h#1 z#3 = (g#0 z#3) in g#0)"
        []

    it "of a `where` see the parameters, and the body sees the `where`" do
      shows [ "f a = b", "  where", "  b = a" ] "(let b#1 = a#0 in b#1)" []

    it "put a local signature's type variables in scope over its definition" do
      definition [ "f = let", "      g :: a -> a", "      g y = (y :: a)", "    in g" ] \r -> r.reasons `shouldEqual` []

    it "take irrefutable patterns, and report a block whose bindings do not pair up" do
      shows [ "f = let Just y = x in \\(Just z) -> z" ] "(let (A.Just y#0) = A.x in (\\(A.Just z#1) -> z#1))" [ RefutablePattern, RefutablePattern ]
      shows [ "f = let", "      a = 1", "      a = 2", "    in a" ] "(let a#0 = 1; a#1 = 2 in a#0)" [ BoundTwice "a" ]

    it "of a `case` alternative bind its patterns, and a guard block's bindings the lines after them" do
      shows
        [ "f p = case p of"
        , "  Just y where"
        , "      z = y"
        , "      z == y -> z"
        , "      otherwise -> y"
        , "  Nothing -> 0"
        ]
        "(case p#0 of (A.Just y#1) where z#2 = y#1 | <A.eq z#2 y#1> -> z#2 | otherwise -> y#1 ; A.Nothing -> 0)"
        []

    it "of an open bring an alias's names, a lazy one's among them, ahead of everything outside it" do
      shows [ "f = (L.( len ), import L in len, M.( x ))" ] "(B.len, B.len, A.x)" []
      shows [ "f = (len, L.len, Q.( 1 ))" ] "(!, !, !)" [ UnknownValue "len", UnknownValue "L.len", UnknownAlias "Q" ]
      definition [ "f len = L.( len )" ] \r -> do
        r.result `shouldEqual` "B.len"
        r.warnings `shouldEqual` [ "len" ]
      definition [ "f = L.( \\len -> len )" ] \r -> do
        r.result `shouldEqual` "(\\len#0 -> len#0)"
        r.warnings `shouldEqual` [ "len" ]

  describe "records" do
    it "hold their fields, a pun being a field, and report a label written twice" do
      shows [ "f a r = ({ a, b: 1 }, { c = 2, ...r }, r.a.b)" ] "({ a: a#0, b: 1 }, { c = 2, ...r#1 }, r#1.a.b)" []
      shows [ "f a = { a, a: 1, b: 2, b: 3 }" ] "{ a: a#0, a: 1, b: 2, b: 3 }" [ LabelTwice "a", LabelTwice "b" ]

  describe "groups written in place" do
    it "headed by an effect name its operations among the effect's, whatever is in scope" do
      shows [ "f get = handle x with", "  E fast | get _ -> get", "  x" ]
        "(handle A.x with A.E{fast A.get _ -> get#0}, A.x)"
        []
      shows [ "f = handle x with", "  E | M.get a -> a", "    | return r -> r" ]
        "(handle A.x with A.E{full A.get a#0 -> a#0; return r#1 -> r#1})"
        []

    it "headed by an effect report a clause naming no operation of it, and leave the clause out" do
      shows [ "f = handle x with", "  E | tick _ -> 0", "    | M.x _ -> 0", "    | get _ -> 1" ]
        "(handle A.x with A.E{full A.get _ -> 1})"
        [ NotAnOperationOf "tick" "E", NotAnOperationOf "M.x" "E" ]

    it "headed by a label handle the effect of the operations in scope they name" do
      shows [ "f get = handle x with", "  cache full | get _ -> resume 0" ]
        "(handle A.x with cache:A.E{full A.get _ -> (resume 0)})"
        []

    it "headed by a label report clauses of several effects, and one with no operation clause" do
      shows [ "f = handle x with", "  cache | get _ -> 0", "        | tick _ -> 0" ]
        "(handle A.x with cache:A.E{full A.get _ -> 0})"
        [ OperationOfOtherEffect "tick" "Own" "E" ]
      shows [ "f = handle x with", "  cache | return r -> r", "  x" ] "(handle A.x with A.x)" [ LabelledGroupEmpty "cache" ]
      shows [ "f = handle x with", "  cache | nope _ -> 0", "  x" ] "(handle A.x with A.x)" [ UnknownOperation "nope" ]

    it "report a head that is no effect" do
      shows [ "f = handle x with", "  Maybe | get _ -> 0", "  Nope | get _ -> 0", "  x" ] "(handle A.x with A.x)"
        [ NotAnEffect "Maybe", UnknownType "Nope" ]

    it "bind a clause's patterns as one group of irrefutable patterns, one per argument" do
      shows [ "f = handle x with", "  E | put a b -> a", "    | get a b -> a" ]
        "(handle A.x with A.E{full A.put a#0 b#1 -> a#0})"
        [ ClauseArity "get" 1 2 false ]
      shows [ "f = handle x with", "  E | get (Just a) -> a", "    | put a a -> a" ]
        "(handle A.x with A.E{full A.get (A.Just a#0) -> a#0; full A.put a#1 a#2 -> a#1})"
        [ RefutablePattern, BoundTwice "a" ]

    it "report a second clause for one operation and a second return clause" do
      shows [ "f = handle x with", "  E | get _ -> 0", "    | M.get _ -> 1", "    | return r -> r", "    | return s -> s" ]
        "(handle A.x with A.E{full A.get _ -> 0; return r#0 -> r#0})"
        [ ClauseTwice "M.get", ReturnTwice ]

    it "take a `reifiable full` clause's continuation as its last pattern where `Base.Continuation` is imported" do
      definitionIn [ "import Base.Continuation" ] [ "f = handle x with", "  E reifiable full | get a k -> a" ] \r -> do
        r.result `shouldEqual` "(handle A.x with A.E{reifiable A.get a#0 k#1 -> a#0})"
        r.reasons `shouldEqual` []
      definitionIn [ "import lazy Base.Continuation as C" ] [ "f = handle x with", "  E reifiable full | get a k -> a" ] \r ->
        r.reasons `shouldEqual` []
      shows [ "f = handle x with", "  E reifiable full | get a -> a" ] "(handle A.x with A.E{})"
        [ ContinuationNotImported, ClauseArity "get" 1 1 true ]

  describe "cells" do
    it "are one group, open in the operation clauses, beside a value of their name" do
      shows [ "f n = handle x with", "  E", "    var n := n", "    var n := 1", "    | fast get _ -> n := n! + n" ]
        "(handle A.x with A.E{var n#1 := n#0; var n#2 := 1; fast A.get _ -> (n#1 := <A.plus n#1! n#0>)})"
        [ BoundTwice "n" ]

    it "are closed in their handler's initial values and return clause, and unknown elsewhere" do
      shows [ "f = handle n! with", "  E", "    var a := 0", "    var b := a!", "    | get _ -> a!", "    | return r -> a!" ]
        "(handle ! with A.E{var a#0 := 0; var b#1 := !; full A.get _ -> a#0!; return r#2 -> !})"
        [ CellClosedHere "a" InInitialValue, CellClosedHere "a" InReturnClause, UnknownCell "n" ]

    it "of a group hide an outer cell of their name in the whole group, and others stay in scope" do
      shows
        [ "f = handle x with"
        , "  E"
        , "    var n := 0"
        , "    var m := 0"
        , "    | fast get _ -> handle x with"
        , "      Own"
        , "        var n := m!"
        , "        var k := n!"
        , "        | fast tick _ -> n! + m!"
        ]
        "(handle A.x with A.E{var n#0 := 0; var m#1 := 0; fast A.get _ -> (handle A.x with M.Own{var n#2 := m#1!; var k#3 := !; fast M.tick _ -> <A.plus n#2! m#1!>})})"
        [ CellClosedHere "n" InInitialValue ]

  describe "`resume`" do
    it "stands applied in the immediate body of a `full` clause" do
      shows [ "f = handle x with", "  E | get _ -> let z = resume 1 in (resume) z", "    | put _ _ -> (resume 1) 2" ]
        "(handle A.x with A.E{full A.get _ -> (let z#0 = (resume 1) in (resume z#0)); full A.put _ _ -> ((resume 1) 2)})"
        []

    it "is reported outside a `full` clause, a `fast` and a `reifiable full` one among them" do
      shows [ "f = resume 1" ] "(! 1)" [ ResumeMisplaced OutsideFullClause ]
      definitionIn [ "import Base.Continuation" ] [ "f = handle x with", "  E fast | get _ -> resume 0", "    | reifiable full put _ _ k -> resume 0" ] \r ->
        r.reasons `shouldEqual` [ ResumeMisplaced InFastClause, ResumeMisplaced InReifiableClause ]

    it "is reported inside a lambda, a local function, or a handling expression within its clause" do
      shows
        [ "f = handle x with"
        , "  E | get _ -> (\\y -> resume y) 1"
        , "    | put _ _ -> let g y = resume y in using (resume 1) handle resume 2"
        ]
        "(handle A.x with A.E{full A.get _ -> ((\\y#0 -> (! y#0)) 1); full A.put _ _ -> (let g#1 y#2 = (! y#2) in (handle (! 2) with (! 1)))})"
        [ ResumeMisplaced InsideLambda, ResumeMisplaced InsideLocalFunction, ResumeMisplaced InsideHandling, ResumeMisplaced InsideHandling ]

    it "of a `full` clause of a group inside a clause is that clause's own" do
      shows [ "f = handle x with", "  E | get _ -> handle x with", "      Own | tick _ -> resume ()" ]
        "(handle A.x with A.E{full A.get _ -> (handle A.x with M.Own{full M.tick _ -> (resume Prim.Unit)})})"
        []

    it "is reported where it is not applied" do
      shows [ "f = handle x with", "  E | get _ -> let k = resume in plus resume 1" ]
        "(handle A.x with A.E{full A.get _ -> (let k#0 = ! in ((A.plus !) 1))})"
        [ ResumeNotApplied, ResumeNotApplied ]

  describe "handler declarations" do
    it "handle the left of `~>`, or the one element a signature in full removes" do
      handles [ "handler h :: E ~> () where", "  fast | get _ -> 0" ] "A.E{fast A.get _ -> 0}" []
      handles [ "handler h :: (Unit -> a / {| E |}) -> a where", "  | get _ -> resume 0" ] "A.E{full A.get _ -> (resume 0)}" []
      handles [ "handler h :: (Unit -> a / {| E, Own, ... |}) -> a / {| Own, ... |} where", "  | return r -> r" ] "A.E{return r#1 -> r#1}" []

    it "report a signature in full the effect handled is not read from" do
      handles [ "handler h :: Int -> Int where", "  | return r -> r" ] "?{return r#0 -> r#0}" [ HandledEffect HandlerShape ]
      handles [ "handler h :: (Int -> a / {| E |}) -> a where", "  | return r -> r" ] "?{return r#1 -> r#1}" [ HandledEffect HandlerShape ]
      handles [ "handler h :: (Unit -> a / {| E |}) -> a / {| E |} where", "  | return r -> r" ] "?{return r#1 -> r#1}" [ HandledEffect HandlesNothing ]
      handles [ "handler h :: (Unit -> a / {| E, Own |}) -> a where", "  | return r -> r" ] "?{return r#1 -> r#1}" [ HandledEffect HandlesSeveral ]
      handles [ "handler h :: (Unit -> a / {| cache :: E |}) -> a where", "  | return r -> r" ] "?{return r#1 -> r#1}" [ HandledEffect (HandlesInstance "cache") ]

    it "read a row a type synonym without parameters names, its own or an imported one, and the rows it spreads" do
      handles
        [ "type Program = {| E, Own |}"
        , "type Runtime = {| Own |}"
        , "handler h :: (Unit -> a / Program) -> a / Runtime where"
        , "  | return r -> r"
        ]
        "A.E{return r#1 -> r#1}"
        []
      handles [ "type Program = {| ...Effects, Own |}", "handler h :: (Unit -> a / {| ...Program, ... |}) -> a / {| Own, ... |} where", "  | return r -> r" ]
        "A.E{return r#1 -> r#1}"
        []
      handles [ "handler h :: (Unit -> a / Effects) -> a where", "  | return r -> r" ] "A.E{return r#1 -> r#1}" []
      handles [ "type Program = ({| E |} :: Row Effect)", "handler h :: (Unit -> a / Program) -> a where", "  | return r -> r" ] "A.E{return r#1 -> r#1}" []
      handles [ "type Program = ({| E |} :: Row Effect)", "handler h :: (Unit -> a / {| ...Program |}) -> a where", "  | return r -> r" ] "A.E{return r#1 -> r#1}" []

    it "do not read a row a synonym with parameters names, nor one naming itself" do
      handles [ "type P x = {| E |}", "handler h :: (Unit -> a / (P Int)) -> a where", "  | return r -> r" ] "?{return r#1 -> r#1}" [ HandledEffect HandlerShape ]
      handles [ "type C = {| ...D |}", "type D = {| E, ...C |}", "handler h :: (Unit -> a / C) -> a where", "  | return r -> r" ] "?{return r#1 -> r#1}"
        [ HandledEffect HandlerShape ]

    it "see their parameters in every initial value and clause, and report a `var` after a clause" do
      handles [ "handler h (n :: Int) :: E ~> () where", "  var c := n", "  fast | get _ -> n", "  var d := 0", "  | return r -> c!" ]
        "A.E{var c#1 := n#0; fast A.get _ -> n#0; return r#2 -> !}"
        [ CellAfterClause "d", CellClosedHere "c" InReturnClause ]
      handles [ "handler h (Just n) :: E ~> () where", "  fast | get _ -> n" ] "A.E{fast A.get _ -> n#0}" [ RefutablePattern ]

  describe "row synonyms" do
    it "stand for a whole row, or are spread into one, and are no effect, in a row or on either side of `~>`" do
      shows [ "type Program = {| E |}", "f = (x :: Unit -> Int / Program, x :: Unit -> Int / {| Own, ...Program |})" ] "((A.x :: τ), (A.x :: τ))" []
      shows [ "type Program = {| E |}", "f = (x :: Unit -> Int / {| Program |})" ] "(A.x :: τ)" [ SynonymAsEffect "Program" ]
      handles [ "type S = {| E |}", "handler h :: S ~> () where", "  | return r -> r" ] "?{return r#0 -> r#0}" [ SynonymAtCapability "S" ]
      handles [ "type S = {| E |}", "handler h :: E ~> ( S ) where", "  | return r -> r" ] "A.E{return r#0 -> r#0}" [ SynonymAtCapability "S" ]

  describe "what is not supported yet" do
    it "is reported where it stands" do
      shows [ "f = (_ + 1, m%(1), case _ of", "  _ -> 1)" ] "(<A.plus ! 1>, !, (case ! of _ -> 1))"
        [ NotYetSupported "The anonymous argument `_`", NotYetSupported "A macro call", NotYetSupported "`case _ of`" ]

renderVar :: LocalVar -> String
renderVar (LocalVar v) = case v.name, v.id of
  Ident n, BindingId i -> n <> "#" <> show i

renderExpr :: Expr -> String
renderExpr = case _ of
  ExprLocal _ v -> renderVar v
  ExprValue _ q -> qualified q
  ExprComputation _ q -> "comp:" <> qualified q
  ExprConstructor _ q -> qualified q
  ExprOperation _ q label -> "op:" <> qualified q <> maybe "" (\(Symbol l) -> "@" <> l) label
  ExprDiscriminator _ q -> qualified q <> "?"
  ExprTag _ (Tag t) -> "'" <> t
  ExprLiteral _ l -> literal l
  ExprHole _ h -> "?" <> h
  ExprApp _ f a -> "(" <> renderExpr f <> " " <> renderExpr a <> ")"
  ExprOperator _ op l r -> "<" <> renderExpr op <> " " <> renderExpr l <> " " <> renderExpr r <> ">"
  ExprTyped _ e _ -> "(" <> renderExpr e <> " :: τ)"
  ExprSelect _ e (Symbol l) -> renderExpr e <> "." <> l
  ExprTuple _ es -> "(" <> joinWith ", " (map renderExpr es) <> ")"
  ExprRecord _ fs -> "{ " <> joinWith ", " (map field fs) <> " }"
  ExprLambda _ ps body -> "(\\" <> joinWith " " (map renderBinder ps) <> " -> " <> renderExpr body <> ")"
  ExprLet _ bs body -> "(let " <> joinWith "; " (map binding bs) <> " in " <> renderExpr body <> ")"
  ExprCase _ ss alts -> "(case " <> joinWith ", " (map renderExpr ss) <> " of " <> joinWith " ; " (map alternative alts) <> ")"
  ExprHandle _ items e -> "(handle " <> renderExpr e <> " with " <> joinWith ", " (map item items) <> ")"
  ExprCellRead _ c -> renderCell c <> "!"
  ExprCellWrite _ c e -> "(" <> renderCell c <> " := " <> renderExpr e <> ")"
  ExprResume _ -> "resume"
  ExprInvalid _ -> "!"
  where
  field = case _ of
    FieldValue _ (Symbol l) e -> l <> ": " <> renderExpr e
    FieldUpdate _ (Symbol l) e -> l <> " = " <> renderExpr e
    FieldSpread _ e -> "..." <> renderExpr e
  binding = case _ of
    LetValue b -> joinWith " " ([ renderVar b.var ] <> map renderBinder b.params) <> " = " <> renderExpr b.body
    LetPattern b -> renderBinder b.binder <> " = " <> renderExpr b.body
  alternative alt =
    joinWith " | " (map (joinWith ", " <<< map renderBinder) alt.patterns) <> case alt.body of
      Unconditional e -> " -> " <> renderExpr e
      Guarded lines -> " where " <> joinWith " | " (map guard lines)
  guard = case _ of
    GuardBinding _ b e -> renderBinder b <> " = " <> renderExpr e
    GuardWhen _ c e -> renderExpr c <> " -> " <> renderExpr e
    GuardOtherwise _ e -> "otherwise -> " <> renderExpr e
  item = case _ of
    HandlerApplied e -> renderExpr e
    HandlerGroup g -> maybe "" (\(Symbol l) -> l <> ":") g.label <> effectWord g.effect <> renderBody g.body

renderCell :: CellVar -> String
renderCell (CellVar v) = case v.name, v.id of
  Ident n, BindingId i -> n <> "#" <> show i

-- | A handler's body: its cells, its operation clauses, and its return
-- | clause, in braces.
renderBody :: HandlerBody -> String
renderBody b = "{" <> joinWith "; " (map cell b.cells <> map operation b.operations <> Array.fromFoldable (map return b.return)) <> "}"
  where
  cell c = "var " <> renderCell c.cell <> " := " <> renderExpr c.initial
  operation o = joinWith " " ([ form o.form, qualified o.operation ] <> map renderBinder o.arguments <> continuation o.form) <> " -> " <> renderExpr o.body
  form = case _ of
    ClauseFast -> "fast"
    ClauseFull -> "full"
    ClauseReifiable _ -> "reifiable"
  continuation = case _ of
    ClauseReifiable k -> [ renderBinder k ]
    _ -> []
  return r = "return " <> renderBinder r.binder <> " -> " <> renderExpr r.body

effectWord :: Qualified EffName -> String
effectWord (Qualified (ModuleName m) (EffName e)) = m <> "." <> e

renderBinder :: Binder -> String
renderBinder = case _ of
  BinderWildcard _ -> "_"
  BinderVar _ v -> renderVar v
  BinderAs _ v b -> renderVar v <> "@" <> renderBinder b
  BinderConstructor _ q [] -> qualified q
  BinderConstructor _ q bs -> "(" <> qualified q <> " " <> joinWith " " (map renderBinder bs) <> ")"
  BinderTag _ (Tag t) b -> "'" <> t <> maybe "" (\p -> " " <> renderBinder p) b
  BinderLiteral _ l -> literal l
  BinderTuple _ bs -> "(" <> joinWith ", " (map renderBinder bs) <> ")"
  BinderRecord _ _ _ -> "{…}"
  BinderOr _ bs -> "(" <> joinWith " | " (map renderBinder bs) <> ")"
  BinderTyped _ b _ -> "(" <> renderBinder b <> " :: τ)"
  BinderInvalid _ -> "!"

literal :: Literal -> String
literal = case _ of
  LitInt i -> show i
  LitBoolean b -> show b
  LitChar c -> "char" <> show (codePointOf c)
  LitString s -> show (textOf s)
  LitNumber n -> show n

qualified :: Qualified Ident -> String
qualified (Qualified (ModuleName m) (Ident n)) = m <> "." <> n
