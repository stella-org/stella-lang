-- | The offside rule.
-- |
-- | Indentation is turned into block tokens before parsing, from the tokens
-- | alone: a block opens after `where`, `let`, `of`, `with` and `using`, at the
-- | column of the token that follows; a token standing at that column on a later
-- | line begins a new item; and a token standing left of it closes the block.
-- | The grammar then matches `TokLayoutStart`, `TokLayoutSep` and
-- | `TokLayoutEnd` as it would explicit braces and semicolons.
-- |
-- | The rule follows PureScript's, which is settled by the tokens rather than
-- | by what the parser can accept.
module Stella.Compiler.CST.Layout
  ( insertLayout
  ) where

import Prelude

import Data.Array as Array
import Data.Foldable (find)
import Data.List (List(..), (:))
import Data.List as List
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..), snd)
import Stella.Compiler.CST.Types (SourcePos, SourceToken, Token(..))

data Delim
  = LytRoot
  -- | Between `case` and `of`, where commas separate scrutinees.
  | LytCase
  -- | The patterns of a case alternative, before its `->` or its guard block.
  | LytCaseBinders
  | LytLambdaBinders
  | LytParen
  | LytBrace
  | LytSquare
  -- | Directly inside `@[ … ]`, where a keyword is a name or a label.
  | LytAttribute
  -- | A place where a keyword is a record label and opens nothing.
  | LytProperty
  | LytForall
  -- | A macro's bracket, whose tokens pass through untouched.
  | LytRaw
  | LytLet
  | LytWhere
  | LytGuard
  | LytOf
  | LytWith
  | LytUsing

derive instance Eq Delim

type Stack = List (Tuple SourcePos Delim)

type State = { stack :: Stack, acc :: List SourceToken, afterMacro :: Boolean }

isIndented :: Delim -> Boolean
isIndented = case _ of
  LytLet -> true
  LytWhere -> true
  LytGuard -> true
  LytOf -> true
  LytWith -> true
  LytUsing -> true
  _ -> false

lytToken :: SourcePos -> Token -> SourceToken
lytToken pos value = { range: { start: pos, end: pos }, leading: [], value }

-- | Inserts the block tokens the offside rule calls for.
insertLayout :: Array SourceToken -> Array SourceToken
insertLayout tokens =
  let
    root = { stack: Tuple { line: 0, column: 0 } LytRoot : Nil, acc: Nil, afterMacro: false }
    final = Array.foldl step root (Array.mapWithIndex Tuple tokens)
    endPos = case Array.last tokens of
      Just tok -> tok.range.end
      Nothing -> { line: 1, column: 1 }
    closing = List.mapMaybe
      (\(Tuple pos lyt) -> if isIndented lyt then Just (lytToken endPos (TokLayoutEnd pos.column)) else Nothing)
      final.stack
  in
    Array.fromFoldable (List.reverse (List.reverse closing <> final.acc))
  where
  step :: State -> Tuple Int SourceToken -> State
  step st (Tuple ix tok) =
    let
      nextPos = case Array.index tokens (ix + 1) of
        Just next -> next.range.start
        Nothing -> tok.range.end
    in
      insert tok nextPos st

insert :: SourceToken -> SourcePos -> State -> State
insert src nextPos state = case state.stack of
  Tuple _ LytRaw : _ -> raw
  _ | state.afterMacro && opens src.value -> state { afterMacro = false } # insertToken src # pushRaw
  _ -> cooked (state { afterMacro = false })
  where
  tokPos = src.range.start

  -- Inside a macro's bracket every token is passed on as it is, and only the
  -- brackets are counted.
  raw
    | opens src.value = state # insertToken src # pushRaw
    | closes src.value = state # insertToken src # popStack (_ == LytRaw)
    | otherwise = state # insertToken src

  pushRaw st = case src.value of
    TokLeftSynth -> st # pushStack tokPos LytRaw # pushStack tokPos LytRaw
    _ -> st # pushStack tokPos LytRaw

  cooked st = case src.value of
    TokMacro _ _ -> st # insertDefault # _ { afterMacro = true }

    TokLowerName Nothing "where" -> case st.stack of
      Tuple _ LytProperty : stk' -> st { stack = stk' } # insertToken src
      Tuple _ LytAttribute : _ -> st # insertToken src
      -- After the patterns of a case alternative, `where` opens a guard block.
      Tuple _ LytCaseBinders : stk' -> st { stack = stk' } # insertToken src # insertStart LytGuard
      _ -> st # collapse offsideEndP # insertToken src # insertStart LytWhere

    TokLowerName Nothing "in" -> case collapse inP st of
      st'@{ stack: Tuple pos lyt : stk' } | lyt == LytLet ->
        st' { stack = stk' } # insertEnd pos.column # insertToken src
      _ -> st # insertDefault # popStack (_ == LytProperty)

    TokLowerName Nothing "handle" -> case collapse usingP st of
      st'@{ stack: Tuple pos LytUsing : stk' } ->
        st' { stack = stk' } # insertEnd pos.column # insertToken src
      _ -> st # insertKwProperty identity

    TokLowerName Nothing "let" -> st # insertKwProperty (insertStart LytLet)
    TokLowerName Nothing "with" -> st # insertKwProperty (insertStart LytWith)
    TokLowerName Nothing "using" -> st # insertKwProperty (insertStart LytUsing)
    TokLowerName Nothing "case" -> st # insertKwProperty (pushStack tokPos LytCase)
    TokLowerName Nothing "forall" -> st # insertKwProperty (pushStack tokPos LytForall)

    TokLowerName Nothing "of" -> case collapse indentedP st of
      st'@{ stack: Tuple _ LytCase : stk' } ->
        st' { stack = stk' } # insertToken src # insertStart LytOf # pushStack nextPos LytCaseBinders
      _ -> st # insertDefault # popStack (_ == LytProperty)

    TokBackslash -> st # insertDefault # pushStack tokPos LytLambdaBinders

    TokOperator Nothing "->" -> st # collapse arrowP # popStack binderP # insertToken src

    TokOperator Nothing "." -> case st # insertDefault of
      st'@{ stack: Tuple _ LytForall : stk' } -> st' { stack = stk' }
      st' -> st' # pushStack tokPos LytProperty

    -- `|` begins a handler clause, which may stand at the column of the block
    -- it belongs to, so it closes nothing that is not left of it.
    TokOperator Nothing "|" -> st # insertDefault

    TokComma -> case st # collapse indentedP of
      st'@{ stack: Tuple _ LytBrace : _ } -> st' # insertToken src # pushStack tokPos LytProperty
      st' -> st' # insertToken src

    TokLeftParen -> st # insertDefault # pushStack tokPos LytParen
    TokLocalOpen _ -> st # insertDefault # pushStack tokPos LytParen
    TokLeftSquare -> st # insertDefault # pushStack tokPos LytSquare
    TokLeftAttribute -> st # insertDefault # pushStack tokPos LytAttribute
    TokLeftBrace -> st # insertDefault # pushStack tokPos LytBrace # pushStack tokPos LytProperty
    TokLeftBar -> st # insertDefault # pushStack tokPos LytBrace # pushStack tokPos LytProperty
    TokLeftSynth ->
      st # insertDefault # pushStack tokPos LytBrace # pushStack tokPos LytBrace # pushStack tokPos LytProperty

    TokRightParen -> st # collapse indentedP # popStack (_ == LytParen) # insertToken src
    TokRightSquare ->
      st # collapse indentedP # popStack (\d -> d == LytSquare || d == LytAttribute) # insertToken src
    TokRightBrace ->
      st # collapse indentedP # popStack (_ == LytProperty) # popStack (_ == LytBrace) # insertToken src
    TokRightBar ->
      st # collapse indentedP # popStack (_ == LytProperty) # popStack (_ == LytBrace) # insertToken src

    TokLowerName Nothing _ -> st # insertDefault # popStack (_ == LytProperty)
    TokString _ _ _ -> st # insertDefault # popStack (_ == LytProperty)

    TokOperator _ _ -> st # collapse offsideEndP # insertSep # insertToken src
    TokInfixName _ _ -> st # collapse offsideEndP # insertSep # insertToken src

    _ -> st # insertDefault

  insertDefault st = st # collapse offsideP # insertSep # insertToken src

  -- A block opens only where it is indented further than the one it stands in.
  insertStart lyt st = case find (isIndented <<< snd) st.stack of
    Just (Tuple pos _) | nextPos.column <= pos.column -> st
    _ -> st # pushStack nextPos lyt # insertToken (lytToken nextPos (TokLayoutStart nextPos.column))

  insertSep st = case st.stack of
    Tuple lytPos lyt : _ | isIndented lyt && sepP lytPos -> case lyt of
      LytOf -> st # insertToken sepTok # pushStack tokPos LytCaseBinders
      _ -> st # insertToken sepTok
    _ -> st
    where
    sepTok = lytToken tokPos (TokLayoutSep tokPos.column)

  -- A keyword standing where a record label may, or directly inside an
  -- attribute, is a name.
  insertKwProperty k st = case st # insertDefault of
    st'@{ stack: Tuple _ LytProperty : stk' } -> st' { stack = stk' }
    st'@{ stack: Tuple _ LytAttribute : _ } -> st'
    st' -> k st'

  insertEnd indent = insertToken (lytToken tokPos (TokLayoutEnd indent))

  collapse p st = go st.stack st.acc
    where
    go (Tuple lytPos lyt : stk') acc
      | p lytPos lyt =
          go stk'
            if isIndented lyt then lytToken tokPos (TokLayoutEnd lytPos.column) : acc
            else acc
    go stk acc = st { stack = stk, acc = acc }

  indentedP _ lyt = isIndented lyt

  offsideP lytPos lyt = isIndented lyt && tokPos.column < lytPos.column

  offsideEndP lytPos lyt = isIndented lyt && tokPos.column <= lytPos.column

  arrowP lytPos lyt = lyt /= LytOf && offsideEndP lytPos lyt

  inP _ lyt = lyt /= LytLet && isIndented lyt

  usingP _ lyt = lyt /= LytUsing && isIndented lyt

  binderP lyt = lyt == LytCaseBinders || lyt == LytLambdaBinders

  sepP lytPos = tokPos.column == lytPos.column && tokPos.line /= lytPos.line

insertToken :: SourceToken -> State -> State
insertToken tok st = st { acc = tok : st.acc }

pushStack :: SourcePos -> Delim -> State -> State
pushStack pos lyt st = st { stack = Tuple pos lyt : st.stack }

popStack :: (Delim -> Boolean) -> State -> State
popStack p st = case st.stack of
  Tuple _ lyt : stk' | p lyt -> st { stack = stk' }
  _ -> st

opens :: Token -> Boolean
opens = case _ of
  TokLeftParen -> true
  TokLeftSquare -> true
  TokLeftBrace -> true
  TokLeftBar -> true
  TokLeftSynth -> true
  TokLeftAttribute -> true
  TokLocalOpen _ -> true
  _ -> false

closes :: Token -> Boolean
closes = case _ of
  TokRightParen -> true
  TokRightSquare -> true
  TokRightBrace -> true
  TokRightBar -> true
  _ -> false
