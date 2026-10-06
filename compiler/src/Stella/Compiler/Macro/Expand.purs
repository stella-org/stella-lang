-- | The expansion stage: every macro call standing where an expression does is
-- | replaced by what expanding it produced
-- | ([Name Resolution](../../../../docs/technical-references/02-Surface-Language/06-Name-Resolution.md)).
-- |
-- | **A call's name is all this stage resolves**, in the macro namespace: what
-- | the imports bring, and within a local open what its alias brings besides,
-- | the innermost open first. Nothing the module declares is in it, so the
-- | namespace is fixed before any declaration is collected.
-- |
-- | **A call is run, and what it produced is read and expanded in turn.** The
-- | macro is checked to be a parser of terms, its parser run on the token tree of
-- | the call, and the syntax it returns read back as an expression of the
-- | expansion's own text and checked as written source is. A call in it is
-- | expanded where the call it came from stands, one expansion deeper: a call
-- | written in the source is at depth 1, and none deeper than the settings allow
-- | is run. The outer call is expanded before what it produced, and what it
-- | produced in the order written.
-- |
-- | **A call that fails is reported once, where it stands, and replaced** by an
-- | invalid expression the rest of resolution passes over in silence.
module Stella.Compiler.Macro.Expand
  ( ExpansionError(..)
  , ExpansionReason(..)
  , Expanded
  , expandModule
  , printExpansionReason
  ) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.List (List(..), (:))
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Set (Set)
import Data.Set as Set
import Data.String (joinWith)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Stella.Compiler.CST.Check (CheckError(..), checkExpr, printCheckReason)
import Stella.Compiler.CST.Range (exprRange)
import Stella.Compiler.CST.Types (CaseBody(..), Clause(..), Decl(..), Expr(..), GuardLine(..), HandlerItem(..), HandlerListItem(..), Import(..), LetBinding(..), Macro, Name, RecordField(..), SourceRange)
import Stella.Compiler.CST.Types as CST
import Stella.Compiler.Interface.Environment (BuildEnvironment, ModuleView, lookupInterface, reachable, viewFor)
import Stella.Compiler.Macro.Check (MacroRefusal(..), checkMacro)
import Stella.Compiler.Macro.Reparse (SyntaxProblem, reparse)
import Stella.Compiler.Macro.Run (ExecutionReason, ExpansionSettings, ParseFailure, ParseOutcome(..), RunParser)
import Stella.Compiler.Macro.Tree (Position(..), Range(..), Token(..), TokenTree(..), treeOf)
import Stella.Compiler.Resolve.Group (Declaration(..), GroupedModule, LocalBinding(..))
import Stella.Compiler.Resolve.Scope (Candidates, ImportScope, declaredMacros, importScope)
import Stella.Compiler.TypedCore.Name (Ident(..), ModuleName(..), Qualified(..))

type Expanded = { grouped :: GroupedModule, errors :: Array ExpansionError }

-- | A call that was not expanded, at the call's range, and why.
data ExpansionError = ExpansionError SourceRange ExpansionReason

data ExpansionReason
  -- | No macro of the name is in scope.
  = MacroNotInScope String
  -- | The macro named is the module's own, which no call of the module runs.
  | MacroOfThisModule String
  -- | The name stands for several macros.
  | MacroAmbiguous String (Array (Qualified Ident))
  -- | A qualified call under an alias no import declares.
  | AliasUnknown String
  -- | What the name stands for is no parser of terms.
  | MacroRefused MacroRefusal
  -- | The parser failed, at a position of the call's input, expecting what it
  -- | expected.
  | ParserFailed SourceRange ParseFailure
  -- | The parser did not run to an answer, as why.
  | ParserNotRun ExecutionReason String
  -- | The parser took the steps it may and needed another.
  | BudgetSpent Int
  -- | What the parser returned cannot be read.
  | SyntaxInvalid SyntaxProblem
  -- | What it returned reads as an expression that is not well formed, as how.
  | ExpansionIllFormed (Array CheckError)
  -- | The call is deeper in a chain of expansions than the settings allow.
  | DepthExceeded Int

-- Running the stage --------------------------------------------------------------------

type State = { nextExpansion :: Int, nextOrigin :: Int, errors :: Array ExpansionError }

-- | The stage's state threaded through the host's monad.
newtype Ex m a = Ex (State -> m (Tuple a State))

runEx :: forall m a. Ex m a -> State -> m (Tuple a State)
runEx (Ex f) = f

instance Functor m => Functor (Ex m) where
  map f (Ex g) = Ex \s -> map (\(Tuple a s') -> Tuple (f a) s') (g s)

instance Monad m => Apply (Ex m) where
  apply = ap

instance Monad m => Applicative (Ex m) where
  pure a = Ex \s -> pure (Tuple a s)

instance Monad m => Bind (Ex m) where
  bind (Ex g) k = Ex \s -> g s >>= \(Tuple a s') -> runEx (k a) s'

instance Monad m => Monad (Ex m)

lift :: forall m a. Monad m => m a -> Ex m a
lift ma = Ex \s -> map (\a -> Tuple a s) ma

modify :: forall m. Monad m => (State -> State) -> Ex m Unit
modify f = Ex \s -> pure (Tuple unit (f s))

gets :: forall m a. Monad m => (State -> a) -> Ex m a
gets f = Ex \s -> pure (Tuple (f s) s)

-- | What a call is resolved and run against: the imports' scope, the macros each
-- | enclosing local open brings, innermost first, the macros the module
-- | declares, the view of the modules its imports reach, and the depth of the
-- | chain of expansions the expression stands in.
type Context m =
  { run :: RunParser m
  , environment :: BuildEnvironment
  , settings :: ExpansionSettings
  , scope :: ImportScope
  , opens :: List (Candidates (Qualified Ident))
  , own :: Set String
  , view :: Maybe ModuleView
  , depth :: Int
  }

expandModule :: forall m. Monad m => RunParser m -> ExpansionSettings -> BuildEnvironment -> GroupedModule -> m Expanded
expandModule run settings env g = do
  Tuple declarations s <- runEx (traverse (declaration ctx) g.declarations) { nextExpansion: 0, nextOrigin: 0, errors: [] }
  pure { grouped: g { declarations = declarations }, errors: s.errors }
  where
  ctx =
    { run
    , environment: env
    , settings
    , scope: importScope env g
    , opens: Nil
    , own: declaredMacros env g
    , view: case viewFor (Array.filter (\m -> lookupInterface m env /= Nothing) importedModules) env of
        Right view -> Just view
        Left _ -> Nothing
    , depth: 1
    }
  importedModules = map (\(Import i) -> ModuleName i.module.name) g.imports

-- Walking the module --------------------------------------------------------------------

declaration :: forall m. Monad m => Context m -> Declaration -> Ex m Declaration
declaration ctx = case _ of
  DeclarationValue prefix v -> do
    body <- expr ctx v.body
    localBindings <- traverse (localBinding ctx) v.localBindings
    pure (DeclarationValue prefix v { body = body, localBindings = localBindings })
  DeclarationOther prefix (DeclHandler n params signature items) ->
    DeclarationOther prefix <<< DeclHandler n params signature <$> traverse (handlerItem ctx) items
  other -> pure other

localBinding :: forall m. Monad m => Context m -> LocalBinding -> Ex m LocalBinding
localBinding ctx = case _ of
  LocalValue v -> (\body -> LocalValue v { body = body }) <$> expr ctx v.body
  LocalPattern b e -> LocalPattern b <$> expr ctx e

handlerItem :: forall m. Monad m => Context m -> HandlerItem -> Ex m HandlerItem
handlerItem ctx = case _ of
  HandlerCell n e -> HandlerCell n <$> expr ctx e
  HandlerClauses marker clauses -> HandlerClauses marker <$> traverse (clause ctx) clauses

clause :: forall m. Monad m => Context m -> Clause -> Ex m Clause
clause ctx = case _ of
  ClauseOperation marker n params body -> ClauseOperation marker n params <$> expr ctx body
  ClauseReturn b body -> ClauseReturn b <$> expr ctx body

expr :: forall m. Monad m => Context m -> Expr -> Ex m Expr
expr ctx e = case e of
  ExprParens inner -> ExprParens <$> go inner
  ExprTuple es -> ExprTuple <$> traverse go es
  ExprRecord r fields -> ExprRecord r <$> traverse field fields
  ExprApp f x -> ExprApp <$> go f <*> go x
  ExprOp l op r -> (\l' r' -> ExprOp l' op r') <$> go l <*> go r
  ExprTyped inner t -> (\i -> ExprTyped i t) <$> go inner
  ExprAccess inner labels -> (\i -> ExprAccess i labels) <$> go inner
  ExprLambda params body -> ExprLambda params <$> go body
  ExprLet bindings body -> ExprLet <$> traverse letBinding bindings <*> go body
  ExprCase scrutinees alternatives -> ExprCase <$> traverse go scrutinees <*> traverse alternative alternatives
  ExprHandle inner items -> ExprHandle <$> go inner <*> traverse listItem items
  ExprUsing items inner -> ExprUsing <$> traverse listItem items <*> go inner
  ExprLocalOpen alias inner -> opened alias inner (ExprLocalOpen alias)
  ExprImportIn alias inner -> opened alias inner (ExprImportIn alias)
  ExprMacro m -> call ctx m
  ExprAt n inner -> ExprAt n <$> go inner
  ExprCellWrite n inner -> ExprCellWrite n <$> go inner
  _ -> pure e
  where
  go = expr ctx

  field = case _ of
    FieldValue n v -> FieldValue n <$> go v
    FieldUpdate n v -> FieldUpdate n <$> go v
    FieldSpread v -> FieldSpread <$> go v
    other -> pure other

  letBinding = case _ of
    LetValue n params body -> LetValue n params <$> go body
    LetPattern b body -> LetPattern b <$> go body
    other -> pure other

  alternative a = (\body -> a { body = body }) <$> case a.body of
    Unconditional body -> Unconditional <$> go body
    GuardBlock lines -> GuardBlock <$> traverse guardLine lines

  guardLine = case _ of
    GuardBinding b v -> GuardBinding b <$> go v
    Guard condition v -> Guard <$> go condition <*> go v

  listItem = case _ of
    ListGroup g -> do
      cells <- traverse (\c -> c { value = _ } <$> go c.value) g.cells
      clauses <- traverse (clause ctx) g.clauses
      pure (ListGroup g { cells = cells, clauses = clauses })
    ListHandler h -> ListHandler <$> go h

  -- an open whose alias no import declares is invalid as a whole, and what it
  -- encloses is resolved nowhere, so nothing in it is expanded
  opened alias inner rebuild = case openedBy ctx.scope alias.name of
    Just macros -> rebuild <$> expr (ctx { opens = macros : ctx.opens }) inner
    Nothing -> pure (rebuild inner)

-- | The macros an alias opens: what the imports declaring it reach through it,
-- | a lazy alias's among them.
openedBy :: ImportScope -> String -> Maybe (Candidates (Qualified Ident))
openedBy scope alias = case Map.lookup alias scope.qualified, Map.lookup alias scope.lazy of
  Nothing, Nothing -> Nothing
  a, b -> Just (Map.unionWith (<>) (macrosOf a) (macrosOf b))
  where
  macrosOf = case _ of
    Just names -> names.macros
    Nothing -> Map.empty

-- Expanding one call --------------------------------------------------------------------

call :: forall m. Monad m => Context m -> Macro -> Ex m Expr
call ctx m = case resolveMacro ctx m.name of
  Left reason -> failed reason
  Right macro
    | ctx.depth > ctx.settings.maxDepth -> failed (DepthExceeded ctx.settings.maxDepth)
    | Just view <- ctx.view, Left refusal <- checkMacro view macro -> failed (MacroRefused refusal)
    | otherwise -> do
        first <- gets _.nextOrigin
        let tree = treeOf first m.body
        modify (_ { nextOrigin = tree.next })
        outcome <- lift (ctx.run macro { input: { trees: tree.trees, end: endOf tree.trees }, budget: ctx.settings.budget })
        case outcome of
          FailedAs f -> failed (ParserFailed (at f.position) f)
          ExecutionFailedAs x -> failed (ParserNotRun x.reason x.detail)
          BudgetExceededAs -> failed (BudgetSpent ctx.settings.budget)
          ParsedAs syntax -> do
            id <- gets _.nextExpansion
            modify (\s -> s { nextExpansion = s.nextExpansion + 1 })
            case reparse { id: CST.ExpansionId id, macro, call: range, issued: tree.origins, quotable: quotableFor macro } syntax of
              Left problem -> failed (SyntaxInvalid problem)
              Right produced -> case checkExpr produced of
                [] -> do
                  inner <- expr (ctx { depth = ctx.depth + 1 }) produced
                  pure (ExprExpanded { call: range, expr: inner })
                problems -> failed (ExpansionIllFormed problems)
  where
  range = exprRange (ExprMacro m)

  failed reason = do
    modify (\s -> s { errors = Array.snoc s.errors (ExpansionError range reason) })
    pure (ExprInvalid range)

  -- the modules a quotation the macro returns may be written in: its own, and
  -- those it reaches through its imports
  quotableFor (Qualified declaring _) = case viewFor [ declaring ] ctx.environment of
    Right view -> reachable view
    Left _ -> Set.singleton declaring

  -- a position of the input is one of the text the call stands in
  at (Position line column) = { space: range.space, start: { line, column }, end: { line, column } }

-- | Where the input of a call ends: at its closing delimiter where it is a
-- | bracket, and at the end of the string where it is one.
endOf :: Array TokenTree -> Position
endOf trees = case trees of
  [ Group _ _ _ closes ] | Just (Token _ _ (Range start _) _ _) <- Array.head closes -> start
  [ Leaf (Token _ _ (Range _ end) _ _) ] -> end
  _ -> Position 0 0

-- | The macro a call names. A qualified call is looked up under its alias; an
-- | unqualified one in the innermost open bringing the name, and in the imports
-- | where none does.
resolveMacro :: forall m. Context m -> Name -> Either ExpansionReason (Qualified Ident)
resolveMacro ctx n = case n.qualifier of
  Just alias -> case Map.lookup alias ctx.scope.qualified of
    Just names -> chosen (Map.lookup n.name names.macros)
    Nothing -> Left (AliasUnknown alias)
  Nothing -> case Array.find (Map.member n.name) (Array.fromFoldable ctx.opens) of
    Just macros -> chosen (Map.lookup n.name macros)
    Nothing -> case Map.lookup n.name ctx.scope.imported.macros of
      Just candidates -> chosen (Just candidates)
      Nothing
        | Set.member n.name ctx.own -> Left (MacroOfThisModule n.name)
        | otherwise -> Left (MacroNotInScope n.name)
  where
  chosen candidates = case Array.nub (map _.entity (fromMaybe [] candidates)) of
    [ one ] -> Right one
    [] -> Left (MacroNotInScope (written n))
    several -> Left (MacroAmbiguous (written n) several)

  written name = case name.qualifier of
    Just q -> q <> "." <> name.name
    Nothing -> name.name

derive instance Eq ExpansionError
derive instance Eq ExpansionReason

instance Show ExpansionError where
  show (ExpansionError r reason) =
    "ExpansionError " <> show r.start.line <> ":" <> show r.start.column <> " " <> show reason

instance Show ExpansionReason where
  show = case _ of
    MacroNotInScope n -> "MacroNotInScope " <> show n
    MacroOfThisModule n -> "MacroOfThisModule " <> show n
    MacroAmbiguous n qs -> "MacroAmbiguous " <> show n <> " " <> show qs
    AliasUnknown a -> "AliasUnknown " <> show a
    MacroRefused r -> "MacroRefused (" <> show r <> ")"
    ParserFailed r f -> "ParserFailed " <> show r.start.line <> ":" <> show r.start.column <> " " <> show (Set.toUnfoldable f.expected :: Array String) <> " " <> show f.labels
    ParserNotRun reason detail -> "ParserNotRun " <> show reason <> " " <> show detail
    BudgetSpent n -> "BudgetSpent " <> show n
    SyntaxInvalid p -> "SyntaxInvalid (" <> show p <> ")"
    ExpansionIllFormed es -> "ExpansionIllFormed " <> show (map (\(CheckError _ reason) -> show reason) es)
    DepthExceeded n -> "DepthExceeded " <> show n

printExpansionReason :: ExpansionReason -> String
printExpansionReason = case _ of
  MacroNotInScope n -> "No macro `" <> n <> "` is in scope"
  MacroOfThisModule n -> "The macro `" <> n <> "` is declared in this module, and a macro is used by the modules importing it"
  MacroAmbiguous n qs -> "The macro `" <> n <> "` is ambiguous: it stands for " <> joinWith ", " (map qualified qs)
  AliasUnknown a -> "No import declares the alias `" <> a <> "`"
  MacroRefused r -> case r of
    MacroUndeclared q -> "The macro `" <> qualified q <> "` is not declared where its module says"
    MacroNotAValue q -> "`" <> qualified q <> "` is not a value, and only a value can be a macro"
    MacroNotMarked q -> "`" <> qualified q <> "` is not declared `@[macro]`"
    MacroNotAParser q _ -> "The macro `" <> qualified q <> "` is not a `Parser (Syntax Term)`"
  ParserFailed _ f ->
    "The macro could not read its input"
      <> (if Set.isEmpty f.expected then "" else "; it expected " <> joinWith ", " (Set.toUnfoldable f.expected))
  ParserNotRun reason detail -> "The macro did not run to an answer (" <> show reason <> "): " <> detail
  BudgetSpent n -> "The macro took the " <> show n <> " steps it may and needed more"
  SyntaxInvalid p -> "The macro returned syntax that cannot be read: " <> show p
  ExpansionIllFormed es -> "The macro produced an expression that is not well formed: " <> joinWith "; " (map (\(CheckError _ reason) -> printCheckReason reason) es)
  DepthExceeded n -> "This call is more than " <> show n <> " expansions deep"
  where
  qualified (Qualified (ModuleName m) (Ident x)) = m <> "." <> x
