-- | The compiler of a `case`'s patterns into a decision plan, after Maranget,
-- | "Compiling Pattern Matching to Good Decision Trees" (ML Workshop 2008).
-- |
-- | **The input is a matrix**: one row per alternative, or per choice of an
-- | alternative written as several rows, holding one pattern per value matched.
-- | The output is a plan of the decision tree Core holds: a dispatch on the
-- | value at an occurrence — a path from a matched value through the fields of
-- | constructors — and, at each leaf, the alternative taken with the variables
-- | its patterns bind, each at its occurrence. A place no row covers is a leaf
-- | of its own. The compiler reads no type and binds no name; the elaborator
-- | builds the tree from the plan.
-- |
-- | **Which column is dispatched on first changes nothing observable**, since
-- | reading an occurrence performs nothing and cannot fail; the choice is made
-- | for the size of the tree: the column the most leading rows need, then the
-- | one with the fewest branches, then the one whose constructors take the
-- | fewest fields, then the leftmost.
-- |
-- | **What a column covers is its domain** (`coverageDomain`): the constructors
-- | of a data type, the finite literals of `Boolean`, or an open set of
-- | literals. A dispatch that exhausts its domain has no default.
-- |
-- | **An alternative may fail once its patterns match**, where a guard block
-- | falls through. Its row is taken where it matches as any other's is, and
-- | where it fails the alternatives after it are matched afresh, by a plan of
-- | their own; it covers nothing the rows after it would otherwise take.
module Stella.Compiler.Elaborate.Surface.Match
  ( Pattern(..)
  , Row
  , Constructors
  , Head(..)
  , Domain(..)
  , coverageDomain
  , Plan(..)
  , Binding
  , Compiled
  , MatchError(..)
  , compile
  , Witness(..)
  , witness
  ) where

import Prelude
import Prim hiding (Row)

import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldM, foldl, sum)
import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.Show.Generic (genericShow)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Stella.Compiler.TypedCore.Name (Ident, Qualified, TyName)
import Stella.Compiler.TypedCore.Prim (booleanTy, litType)
import Stella.Compiler.TypedCore.Term (Literal(..), Occurrence(..))
import Stella.Compiler.TypedCore.Type (Type(..))

-- | A pattern as the compiler reads it. A choice of an or-pattern carries a
-- | label, by which a choice no value reaches is told.
data Pattern c
  = PAny
  | PVar Ident
  | PAs Ident (Pattern c)
  | PCtor (Qualified Ident) (Array (Pattern c))
  | PLit Literal
  | POr (Array { label :: c, pattern :: Pattern c })

-- | A row of the matrix: the alternative it belongs to, the label of the
-- | choice it is where its alternative writes several rows, its patterns, and
-- | whether its alternative may fail once they match — a guard block that may
-- | fall through to the alternatives after it.
type Row c =
  { alternative :: Int
  , choice :: Maybe c
  , patterns :: Array (Pattern c)
  , fallible :: Boolean
  }

-- | Every constructor the patterns may name: the data type it builds, its
-- | position among that type's constructors, and its number of fields.
type Constructors = Map (Qualified Ident) { owner :: Qualified TyName, tag :: Int, arity :: Int }

-- | What a pattern dispatches on.
data Head
  = HeadConstructor (Qualified Ident)
  | HeadLiteral Literal

-- | The values a column of one head ranges over.
data Domain
  -- | The constructors of a data type, in the order its declaration writes
  -- | them.
  = Constructors (Array { name :: Qualified Ident, arity :: Int })
  -- | A finite set of literals, in a fixed order.
  | Literals (Array Literal)
  -- | Literals no dispatch exhausts.
  | Open

-- | The domain of the column a head stands in. A constructor the table does
-- | not hold has none.
coverageDomain :: Constructors -> Head -> Maybe Domain
coverageDomain table = case _ of
  HeadConstructor name -> do
    entry <- Map.lookup name table
    let siblings = Array.filter (\(Tuple _ e) -> e.owner == entry.owner) (Map.toUnfoldable table)
    pure (Constructors (map (\(Tuple n e) -> { name: n, arity: e.arity }) (Array.sortWith (\(Tuple _ e) -> e.tag) siblings)))
  HeadLiteral literal
    | litType literal == TCon booleanTy [] -> Just (Literals [ LitBoolean false, LitBoolean true ])
    | otherwise -> Just Open

-- | What a `case` compiles to.
data Plan
  -- | The alternative taken, and the variables its patterns bind.
  = Leaf Int (Array Binding)
  -- | A place no row covers.
  | Uncovered
  | SwitchCtor Occurrence (Array { ctor :: Qualified Ident, plan :: Plan }) (Maybe Plan)
  | SwitchLit Occurrence (Array { lit :: Literal, plan :: Plan }) Plan

-- | A variable a pattern binds, and the occurrence of the value it is bound to.
type Binding = { name :: Ident, occurrence :: Occurrence }

-- | The plan; for each alternative that may fail and that some leaf takes, the
-- | plan of the alternatives after it, matched afresh where it fails; how many
-- | leaves of these take each alternative; and what no value reaches: the
-- | alternatives no leaf takes, and the choices of an or-pattern no leaf takes
-- | in an alternative some leaf does.
type Compiled c =
  { plan :: Plan
  , falls :: Map Int Plan
  , references :: Map Int Int
  , redundant :: { alternatives :: Array Int, choices :: Array c }
  }

-- | A matrix no well-typed `case` gives: a column whose heads belong to
-- | different domains, a constructor the table does not hold, or one matched
-- | with other than one pattern per field. Each names the occurrence of the
-- | column.
data MatchError
  = IncompatibleHeads Occurrence
  | UnknownConstructor Occurrence (Qualified Ident)
  | ArityMismatch Occurrence (Qualified Ident)

-- | A row being compiled: its patterns, one per occurrence of the matrix, and
-- | what it has bound and passed through so far.
type Work c =
  { alternative :: Int
  , patterns :: Array (Pattern c)
  , bindings :: Array Binding
  , labels :: Array c
  }

-- | The column a dispatch takes apart, and what it ranges over.
type Column =
  { index :: Int
  , occurrence :: Occurrence
  , heads :: Array Head
  , domain :: Domain
  }

compile :: forall c. Eq c => Constructors -> Int -> Array (Row c) -> Either MatchError (Compiled c)
compile table width rows = do
  main <- go occurrences (started rows)
  -- an alternative that may fail falls through to a plan of those after it,
  -- which a leaf of an earlier plan taking it makes reachable
  falling <- foldM fall { plans: Map.empty, selected: main.selected } (Array.sort (Array.nub (map _.alternative (Array.filter _.fallible rows))))
  let
    live = map _.alternative falling.selected
    taken = Array.concatMap _.labels falling.selected
    alternatives = Array.nub (map _.alternative rows)
    choices = Array.nubEq do
      r <- rows
      if Array.elem r.alternative live then Array.filter (\l -> not (Array.elem l taken)) (rowLabels r) else []
  pure
    { plan: main.plan
    , falls: falling.plans
    , references: foldl (\m p -> Map.unionWith (+) m (leaves p)) (leaves main.plan) (Map.values falling.plans)
    , redundant: { alternatives: Array.filter (\a -> not (Array.elem a live)) alternatives, choices }
    }
  where
  occurrences = Array.mapWithIndex (\i _ -> OccScrutinee i) (Array.replicate width unit)

  started = Array.concatMap (normalize occurrences <<< start)

  start r = { alternative: r.alternative, patterns: r.patterns, bindings: [], labels: maybe [] pure r.choice }

  fall acc i
    | Array.elem i (map _.alternative acc.selected) = do
        built <- go occurrences (started (Array.filter (\r -> r.alternative > i) rows))
        pure { plans: Map.insert i built.plan acc.plans, selected: acc.selected <> built.selected }
    | otherwise = pure acc

  go :: Array Occurrence -> Array (Work c) -> Either MatchError (Built c)
  go occs work = case Array.head work of
    Nothing -> pure { plan: Uncovered, selected: [] }
    Just first
      | Array.all isAny first.patterns -> pure { plan: Leaf first.alternative first.bindings, selected: [ { alternative: first.alternative, labels: first.labels } ] }
      | otherwise -> choose table occs work >>= dispatch occs work

  dispatch :: Array Occurrence -> Array (Work c) -> Column -> Either MatchError (Built c)
  dispatch occs work column = case column.domain of
    Constructors domain -> do
      let present = Array.filter (\c -> Array.elem (HeadConstructor c.name) column.heads) domain
      branches <- traverse (\c -> { ctor: c.name, built: _ } <$> constructor c.name c.arity) present
      fallback <-
        if Array.length present == Array.length domain then pure Nothing
        else Just <$> defaulted
      pure
        { plan: SwitchCtor column.occurrence (map (\b -> { ctor: b.ctor, plan: b.built.plan }) branches) (map _.plan fallback)
        , selected: Array.concatMap _.built.selected branches <> maybe [] _.selected fallback
        }
    -- a finite set exhausted takes its last literal as the default
    Literals domain -> do
      let present = Array.filter (\l -> Array.elem (HeadLiteral l) column.heads) domain
      case Array.unsnoc present of
        Just { init, last } | Array.length present == Array.length domain ->
          switchLit <$> traverse literalBranch init <*> literal last
        _ -> switchLit <$> traverse literalBranch present <*> defaulted
    Open -> switchLit <$> traverse literalBranch (Array.sort (Array.mapMaybe headLiteral column.heads)) <*> defaulted
    where
    removed = without column.index occs

    switchLit branches fallback =
      { plan: SwitchLit column.occurrence (map (\b -> { lit: b.lit, plan: b.built.plan }) branches) fallback.plan
      , selected: Array.concatMap _.built.selected branches <> fallback.selected
      }

    literalBranch l = { lit: l, built: _ } <$> literal l

    literal l = go removed (Array.concatMap (normalize removed) (specializeLiteral column.index l work))

    constructor name arity = do
      let occs' = splice column.index (fieldsOf column.occurrence name arity) occs
      rows' <- specializeConstructor column.occurrence column.index name arity work
      go occs' (Array.concatMap (normalize occs') rows')

    defaulted = go removed (Array.concatMap (normalize removed) (defaultRows column.index work))

-- | A plan, and the rows its leaves take: each the alternative, and the labels
-- | of the choices it passed through.
type Built c = { plan :: Plan, selected :: Array { alternative :: Int, labels :: Array c } }

-- | The occurrences of a constructor's fields.
fieldsOf :: Occurrence -> Qualified Ident -> Int -> Array Occurrence
fieldsOf o name arity = Array.mapWithIndex (\k _ -> OccField o name k) (Array.replicate arity unit)

-- | The rows a row stands for once every variable and as-pattern at the top of
-- | a column is bound and every or-pattern there is taken apart into its
-- | choices, in the order written.
normalize :: forall c. Array Occurrence -> Work c -> Array (Work c)
normalize occs row = map finish (foldl step [ { done: [], bindings: row.bindings, labels: row.labels } ] (Array.zip occs row.patterns))
  where
  step partials (Tuple o p) = do
    q <- partials
    e <- expand o p
    pure { done: Array.snoc q.done e.pattern, bindings: q.bindings <> e.bindings, labels: q.labels <> e.labels }
  finish q = row { patterns = q.done, bindings = q.bindings, labels = q.labels }

expand :: forall c. Occurrence -> Pattern c -> Array { pattern :: Pattern c, bindings :: Array Binding, labels :: Array c }
expand o = case _ of
  PVar x -> [ { pattern: PAny, bindings: [ { name: x, occurrence: o } ], labels: [] } ]
  PAs x inner -> map (\e -> e { bindings = Array.cons { name: x, occurrence: o } e.bindings }) (expand o inner)
  POr choices -> do
    c <- choices
    e <- expand o c.pattern
    pure (e { labels = Array.cons c.label e.labels })
  other -> [ { pattern: other, bindings: [], labels: [] } ]

-- | The column to dispatch on: one the first row does not match whatever it
-- | holds, chosen as the module header says.
choose :: forall r c. Constructors -> Array Occurrence -> Array { patterns :: Array (Pattern c) | r } -> Either MatchError Column
choose table occs rows = do
  candidates <- traverse column (Array.filter needed (Array.mapWithIndex Tuple occs))
  case Array.head (Array.sortWith score candidates) of
    Just best -> pure best.column
    Nothing -> Left (IncompatibleHeads (fromMaybe (OccScrutinee 0) (Array.head occs)))
  where
  needed (Tuple j _) = maybe false (not <<< isAny) (Array.head rows >>= \r -> Array.index r.patterns j)
  column (Tuple j o) = do
    c <- columnAt table j o rows
    let
      prefix = Array.length (Array.takeWhile (\r -> maybe false (not <<< isAny) (Array.index r.patterns j)) rows)
      branches = Array.length c.heads + (if complete c then 0 else 1)
      fields = sum (map (headArity table) c.heads)
    pure { column: c, key: { prefix, branches, fields, index: j } }
  score candidate = Tuple (negate candidate.key.prefix) (Tuple candidate.key.branches (Tuple candidate.key.fields candidate.key.index))

-- | The heads of a column in the order the rows first write them, and their
-- | domain, every head belonging to it.
columnAt :: forall r c. Constructors -> Int -> Occurrence -> Array { patterns :: Array (Pattern c) | r } -> Either MatchError Column
columnAt table j o rows = do
  let heads = Array.nubEq (Array.mapMaybe (\r -> Array.index r.patterns j >>= headOf) rows)
  case Array.head heads of
    Nothing -> pure { index: j, occurrence: o, heads, domain: Open }
    Just first -> do
      domain <- case coverageDomain table first of
        Just d -> pure d
        Nothing -> Left (unknown first)
      if Array.all (belongs domain first) heads then pure { index: j, occurrence: o, heads, domain }
      else Left (IncompatibleHeads o)
  where
  unknown = case _ of
    HeadConstructor name -> UnknownConstructor o name
    HeadLiteral _ -> IncompatibleHeads o
  belongs domain first h = case domain, h, first of
    Constructors all, HeadConstructor name, _ -> Array.any (\c -> c.name == name) all
    Literals all, HeadLiteral l, _ -> Array.elem l all
    Open, HeadLiteral l, HeadLiteral l0 -> litType l == litType l0
    _, _, _ -> false

complete :: Column -> Boolean
complete c = case c.domain of
  Constructors all -> Array.all (\e -> Array.elem (HeadConstructor e.name) c.heads) all
  Literals all -> Array.all (\l -> Array.elem (HeadLiteral l) c.heads) all
  Open -> false

headArity :: Constructors -> Head -> Int
headArity table = case _ of
  HeadConstructor name -> maybe 0 _.arity (Map.lookup name table)
  HeadLiteral _ -> 0

headOf :: forall c. Pattern c -> Maybe Head
headOf = case _ of
  PCtor name _ -> Just (HeadConstructor name)
  PLit l -> Just (HeadLiteral l)
  _ -> Nothing

headLiteral :: Head -> Maybe Literal
headLiteral = case _ of
  HeadLiteral l -> Just l
  HeadConstructor _ -> Nothing

isAny :: forall c. Pattern c -> Boolean
isAny = case _ of
  PAny -> true
  _ -> false

-- | The rows that match the constructor given at column `j`, its fields in the
-- | column's place: a row with that constructor there contributes its
-- | patterns of the fields, and one matching anything as many wildcards.
specializeConstructor :: forall r c. Occurrence -> Int -> Qualified Ident -> Int -> Array { patterns :: Array (Pattern c) | r } -> Either MatchError (Array { patterns :: Array (Pattern c) | r })
specializeConstructor o j name arity rows = Array.catMaybes <$> traverse row rows
  where
  row r = case Array.index r.patterns j of
    Just (PCtor name' ps)
      | name' == name ->
          if Array.length ps == arity then pure (Just (r { patterns = splice j ps r.patterns }))
          else Left (ArityMismatch o name)
      | otherwise -> pure Nothing
    Just PAny -> pure (Just (r { patterns = splice j (Array.replicate arity PAny) r.patterns }))
    _ -> pure Nothing

-- | The rows that match the literal given at column `j`, the column removed.
specializeLiteral :: forall r c. Int -> Literal -> Array { patterns :: Array (Pattern c) | r } -> Array { patterns :: Array (Pattern c) | r }
specializeLiteral j l = Array.mapMaybe \r -> case Array.index r.patterns j of
  Just (PLit l') | l' == l -> Just (r { patterns = without j r.patterns })
  Just PAny -> Just (r { patterns = without j r.patterns })
  _ -> Nothing

-- | The rows that match whatever stands at column `j`, the column removed.
defaultRows :: forall r c. Int -> Array { patterns :: Array (Pattern c) | r } -> Array { patterns :: Array (Pattern c) | r }
defaultRows j = Array.mapMaybe \r -> case Array.index r.patterns j of
  Just PAny -> Just (r { patterns = without j r.patterns })
  _ -> Nothing

splice :: forall a. Int -> Array a -> Array a -> Array a
splice j xs ys = Array.take j ys <> xs <> Array.drop (j + 1) ys

without :: forall a. Int -> Array a -> Array a
without j ys = splice j [] ys

-- | Every label a row passes through: its own as a choice, and those of the
-- | or-patterns it holds.
rowLabels :: forall c. Row c -> Array c
rowLabels r = maybe [] pure r.choice <> Array.concatMap labelsOf r.patterns
  where
  labelsOf = case _ of
    POr choices -> Array.concatMap (\c -> Array.cons c.label (labelsOf c.pattern)) choices
    PAs _ inner -> labelsOf inner
    PCtor _ ps -> Array.concatMap labelsOf ps
    _ -> []

-- | How many leaves take each alternative.
leaves :: Plan -> Map Int Int
leaves = go Map.empty
  where
  go acc = case _ of
    Leaf a _ -> Map.insertWith (+) a 1 acc
    Uncovered -> acc
    SwitchCtor _ branches fallback -> maybe identity (flip go) fallback (foldl (\m b -> go m b.plan) acc branches)
    SwitchLit _ branches fallback -> go (foldl (\m b -> go m b.plan) acc branches) fallback

-- | A value a `case` does not match, as patterns: a constructor applied to
-- | what its fields hold, a literal, or anything at all.
data Witness
  = WitnessAny
  | WitnessConstructor (Qualified Ident) (Array Witness)
  | WitnessLiteral Literal

-- | One vector of values no row matches, where there is one, a row that may
-- | fail once its patterns match covering nothing, found by a fixed rule: the leftmost column first, the constructors of a data type in the
-- | order the declaration writes them, a finite set of literals in its order
-- | (`false` before `true`), and of an open set the literals the rows write, in
-- | the fixed order of literals, before anything else, written `_`.
witness :: forall c. Constructors -> Int -> Array (Row c) -> Either MatchError (Maybe (Array Witness))
witness table width rows = search occurrences (Array.concatMap (\r -> plain r.patterns) (Array.filter (not <<< _.fallible) rows))
  where
  occurrences = Array.mapWithIndex (\i _ -> OccScrutinee i) (Array.replicate width unit)

  search :: Array Occurrence -> Array (Array (Pattern c)) -> Either MatchError (Maybe (Array Witness))
  search occs patterns = case Array.head occs of
    Nothing -> pure (if Array.null patterns then Just [] else Nothing)
    Just o -> do
      let rows' = map (\ps -> { patterns: ps }) patterns
      column <- columnAt table 0 o rows'
      let rest = Array.drop 1 occs
      case column.domain of
        _ | Array.null column.heads -> map (Array.cons WitnessAny) <$> search rest (map _.patterns (defaultRows 0 rows'))
        Constructors all -> firstJust all \c -> do
          specialized <- specializeConstructor o 0 c.name c.arity rows'
          found <- search (fieldsOf o c.name c.arity <> rest) (Array.concatMap (plain <<< _.patterns) specialized)
          pure (map (\w -> Array.cons (WitnessConstructor c.name (Array.take c.arity w)) (Array.drop c.arity w)) found)
        Literals all -> firstJust all \l ->
          map (Array.cons (WitnessLiteral l)) <$> search rest (map _.patterns (specializeLiteral 0 l rows'))
        Open -> do
          found <- firstJust (Array.sort (Array.mapMaybe headLiteral column.heads)) \l ->
            map (Array.cons (WitnessLiteral l)) <$> search rest (map _.patterns (specializeLiteral 0 l rows'))
          case found of
            Just w -> pure (Just w)
            Nothing -> map (Array.cons WitnessAny) <$> search rest (map _.patterns (defaultRows 0 rows'))

  firstJust :: forall a. Array a -> (a -> Either MatchError (Maybe (Array Witness))) -> Either MatchError (Maybe (Array Witness))
  firstJust candidates f = case Array.uncons candidates of
    Nothing -> pure Nothing
    Just { head, tail } -> f head >>= case _ of
      Just w -> pure (Just w)
      Nothing -> firstJust tail f

-- | The rows of plain patterns a row of patterns stands for: its variables
-- | matching anything and its or-patterns taken apart.
plain :: forall c. Array (Pattern c) -> Array (Array (Pattern c))
plain = foldl
  ( \acc p -> do
      pre <- acc
      q <- flat p
      pure (Array.snoc pre q)
  )
  [ [] ]
  where
  flat = case _ of
    PVar _ -> [ PAny ]
    PAs _ inner -> flat inner
    POr choices -> Array.concatMap (flat <<< _.pattern) choices
    PCtor name ps -> map (PCtor name) (plain ps)
    other -> [ other ]

derive instance Eq c => Eq (Pattern c)
derive instance Generic (Pattern c) _

instance Show c => Show (Pattern c) where
  show x = genericShow x

derive instance Eq Head
derive instance Generic Head _

instance Show Head where
  show = genericShow

derive instance Eq Domain
derive instance Generic Domain _

instance Show Domain where
  show = genericShow

derive instance Eq Plan
derive instance Generic Plan _

instance Show Plan where
  show x = genericShow x

derive instance Eq MatchError
derive instance Generic MatchError _

instance Show MatchError where
  show = genericShow

derive instance Eq Witness
derive instance Generic Witness _

instance Show Witness where
  show x = genericShow x
