-- | The compiler of a `case`'s patterns into a decision plan, after Maranget,
-- | "Compiling Pattern Matching to Good Decision Trees" (ML Workshop 2008).
-- |
-- | **The input is a matrix**: one row per alternative, or per choice of an
-- | alternative written as several rows, holding one pattern per value matched.
-- | The output is a plan of the decision tree Core holds: a dispatch on the
-- | value at an occurrence — a path from a matched value through the fields of
-- | constructors and records — and, at each leaf, the alternative taken with
-- | the variables its patterns bind, each at its occurrence. A place no row
-- | covers is a leaf of its own. The compiler reads no type and binds no name;
-- | the elaborator builds the tree from the plan.
-- |
-- | **A record is taken apart without a dispatch**: its type decides its keys,
-- | so a column a record or a tuple pattern stands in becomes a column for
-- | each key the rows write, in the order they first write them, before any
-- | column is dispatched on. It tests nothing, and leaves nothing uncovered.
-- |
-- | **Which column is dispatched on first changes nothing observable**, since
-- | reading an occurrence performs nothing and cannot fail; the choice is made
-- | for the size of the tree: the column the most leading rows need, then the
-- | one with the fewest branches, then the one whose constructors take the
-- | fewest fields, then the leftmost.
-- |
-- | **What a column covers is its domain** (`coverageDomain`): the constructors
-- | of a data type, the finite literals of `Boolean`, an open set of literals,
-- | or the tags of a variant's row. A dispatch that exhausts its domain has no
-- | default. The tags a variant may hold are read off its type, which the
-- | compiler does not read: each tag pattern carries the domain of the column
-- | it stands in, with the type of each tag's payload as a token the caller
-- | gives (`t`), and every tag pattern of a column carries the same domain.
-- |
-- | **The default of a dispatch on tags holds the variant without those
-- | tags**, so a variable bound to the variant there is bound to it widened
-- | back by the tags the dispatch took, in the order taken (`Weaken`).
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
  , Tags
  , Tail(..)
  , coverageDomain
  , Plan(..)
  , Binding
  , Transform(..)
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
import Data.Foldable (foldM, foldMap, foldl, sum, traverse_)
import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, isJust, maybe)
import Data.Show.Generic (genericShow)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Stella.Compiler.TypedCore.Name (Ident, Qualified, TyName)
import Stella.Compiler.TypedCore.Prim (booleanTy, litType)
import Stella.Compiler.TypedCore.Term (Literal(..), Occurrence(..))
import Stella.Compiler.TypedCore.Type (RowKey, Type(..))

-- | A pattern as the compiler reads it. A choice of an or-pattern carries a
-- | label, by which a choice no value reaches is told.
data Pattern t c
  = PAny
  | PVar Ident
  | PAs Ident (Pattern t c)
  | PCtor (Qualified Ident) (Array (Pattern t c))
  | PLit Literal
  | POr (Array { label :: c, pattern :: Pattern t c })
  -- | A record, or a tuple keyed by positions: a pattern for each key it
  -- | writes, in the order written; the variable bound to the record without
  -- | those keys, where one is; and whether the record may have other keys.
  | PRecord { fields :: Array { key :: RowKey, pattern :: Pattern t c }, rest :: Maybe Ident, open :: Boolean }
  -- | A tag and the pattern of its payload, with the tags of the variant
  -- | matched.
  | PTag { key :: RowKey, payload :: Pattern t c, domain :: Tags t }

-- | The tags of a variant's row, in the order of their keys, each with the
-- | type of its payload, and what the row holds besides them.
type Tags t = { keys :: Array { key :: RowKey, payload :: t }, tail :: Tail }

-- | What a variant's row holds besides its known tags: nothing; a row
-- | variable bound by a quantifier, which may stand for any other tags; or a
-- | metavariable not yet solved.
data Tail = Closed | Rigid | Flexible

-- | A row of the matrix: the alternative it belongs to, the label of the
-- | choice it is where its alternative writes several rows, its patterns, and
-- | whether its alternative may fail once they match — a guard block that may
-- | fall through to the alternatives after it.
type Row t c =
  { alternative :: Int
  , choice :: Maybe c
  , patterns :: Array (Pattern t c)
  , fallible :: Boolean
  }

-- | Every constructor the patterns may name: the data type it builds, its
-- | position among that type's constructors, and its number of fields.
type Constructors = Map (Qualified Ident) { owner :: Qualified TyName, tag :: Int, arity :: Int }

-- | What a pattern dispatches on.
data Head
  = HeadConstructor (Qualified Ident)
  | HeadLiteral Literal
  | HeadTag RowKey

-- | The values a column of one head ranges over.
data Domain t
  -- | The constructors of a data type, in the order its declaration writes
  -- | them.
  = Constructors (Array { name :: Qualified Ident, arity :: Int })
  -- | A finite set of literals, in a fixed order.
  | Literals (Array Literal)
  -- | Literals no dispatch exhausts.
  | Open
  -- | The tags of a variant.
  | Variant (Tags t)

-- | The domain of the column a constructor or a literal stands in. A
-- | constructor the table does not hold has none, and the domain of a tag is
-- | carried by its pattern.
coverageDomain :: forall t. Constructors -> Head -> Maybe (Domain t)
coverageDomain table = case _ of
  HeadConstructor name -> do
    entry <- Map.lookup name table
    let siblings = Array.filter (\(Tuple _ e) -> e.owner == entry.owner) (Map.toUnfoldable table)
    pure (Constructors (map (\(Tuple n e) -> { name: n, arity: e.arity }) (Array.sortWith (\(Tuple _ e) -> e.tag) siblings)))
  HeadLiteral literal
    | litType literal == TCon booleanTy [] -> Just (Literals [ LitBoolean false, LitBoolean true ])
    | otherwise -> Just Open
  HeadTag _ -> Nothing

-- | What a `case` compiles to.
data Plan t
  -- | The alternative taken, and the variables its patterns bind.
  = Leaf Int (Array (Binding t))
  -- | A place no row covers.
  | Uncovered
  | SwitchCtor Occurrence (Array { ctor :: Qualified Ident, plan :: Plan t }) (Maybe (Plan t))
  | SwitchLit Occurrence (Array { lit :: Literal, plan :: Plan t }) (Plan t)
  -- | A dispatch on the tag of a variant, with what the variant's row holds
  -- | besides its known tags.
  | SwitchKey Occurrence Tail (Array { key :: RowKey, plan :: Plan t }) (Maybe (Plan t))

-- | A variable a pattern binds, the occurrence of the value it is bound to,
-- | and how that value is made what the variable holds.
type Binding t = { name :: Ident, occurrence :: Occurrence, transform :: Transform t }

-- | How the value at a binding's occurrence is made what the variable holds:
-- | as it is; without the keys given, in the order given, where a record
-- | pattern binds the fields it does not write; or widened by the tags given,
-- | each with the type of its payload, where the variable is bound in the
-- | default of dispatches that took those tags, in the order taken.
data Transform t
  = Identity
  | Restrict (Array RowKey)
  | Weaken (Array { key :: RowKey, payload :: t })

-- | The plan; for each alternative that may fail and that some leaf takes, the
-- | plan of the alternatives after it, matched afresh where it fails; how many
-- | leaves of these take each alternative; and what no value reaches: the
-- | alternatives no leaf takes, and the choices of an or-pattern no leaf takes
-- | in an alternative some leaf does.
type Compiled t c =
  { plan :: Plan t
  , falls :: Map Int (Plan t)
  , references :: Map Int Int
  , redundant :: { alternatives :: Array Int, choices :: Array c }
  }

-- | A matrix no well-typed `case` gives: a column whose heads belong to
-- | different domains, or whose tag patterns carry different domains; a
-- | constructor the table does not hold, or one matched with other than one
-- | pattern per field; or a tag its domain does not hold. Each names the
-- | occurrence of the column.
data MatchError
  = IncompatibleHeads Occurrence
  | UnknownConstructor Occurrence (Qualified Ident)
  | ArityMismatch Occurrence (Qualified Ident)
  | DomainMismatch Occurrence
  | UnknownTag Occurrence RowKey

-- | A row being compiled: its patterns, one per occurrence of the matrix, and
-- | what it has bound and passed through so far.
type Work t c =
  { alternative :: Int
  , patterns :: Array (Pattern t c)
  , bindings :: Array (Binding t)
  , labels :: Array c
  }

-- | The column a dispatch takes apart, and what it ranges over.
type Column t =
  { index :: Int
  , occurrence :: Occurrence
  , heads :: Array Head
  , domain :: Domain t
  }

compile :: forall t c. Eq c => Constructors -> Int -> Array (Row t c) -> Either MatchError (Compiled t c)
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

  go :: Array Occurrence -> Array (Work t c) -> Either MatchError (Built t c)
  go occs work = case Array.head work of
    Nothing -> pure { plan: Uncovered, selected: [] }
    Just first
      | Array.all isAny first.patterns -> pure { plan: Leaf first.alternative first.bindings, selected: [ { alternative: first.alternative, labels: first.labels } ] }
      | Just j <- productColumn work -> do
          apart <- takenApart j occs work
          go apart.occurrences (Array.concatMap (normalize apart.occurrences) apart.rows)
      | otherwise -> choose table occs work >>= dispatch occs work

  dispatch :: Array Occurrence -> Array (Work t c) -> Column t -> Either MatchError (Built t c)
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
    -- a variant whose row is closed, every tag of it taken, has no default
    Variant tags -> do
      let present = Array.filter (\k -> Array.elem (HeadTag k.key) column.heads) tags.keys
      branches <- traverse (\k -> { key: k.key, built: _ } <$> tagged k.key) present
      fallback <-
        if tags.tail == Closed && Array.length present == Array.length tags.keys then pure Nothing
        else Just <$> widened present
      pure
        { plan: SwitchKey column.occurrence tags.tail (map (\b -> { key: b.key, plan: b.built.plan }) branches) (map _.plan fallback)
        , selected: Array.concatMap _.built.selected branches <> maybe [] _.selected fallback
        }
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

    tagged key = do
      let occs' = splice column.index [ OccVariantPayload column.occurrence key ] occs
      go occs' (Array.concatMap (normalize occs') (specializeTag column.index key work))

    widened taken = go removed (Array.concatMap (normalize removed) (map (weakenAt column.occurrence taken) (defaultRows column.index work)))

-- | A plan, and the rows its leaves take: each the alternative, and the labels
-- | of the choices it passed through.
type Built t c = { plan :: Plan t, selected :: Array { alternative :: Int, labels :: Array c } }

-- | A row in the default of a dispatch on the tags given at the occurrence
-- | given, each variable bound there widened by those tags after any it was
-- | widened by already.
weakenAt :: forall t c. Occurrence -> Array { key :: RowKey, payload :: t } -> Work t c -> Work t c
weakenAt o taken row = row { bindings = map binding row.bindings }
  where
  binding b
    | b.occurrence == o = b { transform = widen b.transform }
    | otherwise = b
  widen = case _ of
    Identity -> Weaken taken
    Weaken earlier -> Weaken (earlier <> taken)
    Restrict keys -> Restrict keys

-- | The occurrences of a constructor's fields.
fieldsOf :: Occurrence -> Qualified Ident -> Int -> Array Occurrence
fieldsOf o name arity = Array.mapWithIndex (\k _ -> OccField o name k) (Array.replicate arity unit)

-- | The leftmost column a record pattern stands in.
productColumn :: forall r t c. Array { patterns :: Array (Pattern t c) | r } -> Maybe Int
productColumn rows = Array.findIndex (\j -> Array.any (\r -> isRecord (Array.index r.patterns j)) rows) (Array.range 0 (width - 1))
  where
  width = maybe 0 (Array.length <<< _.patterns) (Array.head rows)
  isRecord = case _ of
    Just (PRecord _) -> true
    _ -> false

-- | The keys the record patterns of column `j` write, in the order the rows
-- | first write them. A column holding a record pattern holds no constructor
-- | and no literal.
productKeys :: forall r t c. Occurrence -> Int -> Array { patterns :: Array (Pattern t c) | r } -> Either MatchError (Array RowKey)
productKeys o j rows = Array.nub <<< Array.concat <$> traverse keysOf rows
  where
  keysOf r = case Array.index r.patterns j of
    Just (PRecord p) -> pure (map _.key p.fields)
    Just PAny -> pure []
    _ -> Left (IncompatibleHeads o)

-- | The rows with column `j` a column for each key its record patterns write,
-- | each record pattern binding its rest.
takenApart :: forall t c. Int -> Array Occurrence -> Array (Work t c) -> Either MatchError { occurrences :: Array Occurrence, rows :: Array (Work t c) }
takenApart j occs rows = productKeys o j rows <#> \keys ->
  { occurrences: splice j (map (OccRecordField o) keys) occs, rows: map (row keys) rows }
  where
  o = fromMaybe (OccScrutinee j) (Array.index occs j)
  row keys r = r
    { patterns = keyed j keys r.patterns
    , bindings = r.bindings <> case Array.index r.patterns j of
        Just (PRecord p) -> foldMap (\x -> [ { name: x, occurrence: o, transform: Restrict (map _.key p.fields) } ]) p.rest
        _ -> []
    }

-- | A row's patterns with column `j` a pattern for each key given: a record
-- | pattern's of the key, matching anything at a key it does not write, and
-- | anything at every key where the row matches anything there.
keyed :: forall t c. Int -> Array RowKey -> Array (Pattern t c) -> Array (Pattern t c)
keyed j keys patterns = splice j parts patterns
  where
  parts = case Array.index patterns j of
    Just (PRecord p) -> map (\k -> maybe PAny _.pattern (Array.find (\f -> f.key == k) p.fields)) keys
    _ -> Array.replicate (Array.length keys) PAny

-- | The rows a row stands for once every variable and as-pattern at the top of
-- | a column is bound and every or-pattern there is taken apart into its
-- | choices, in the order written.
normalize :: forall t c. Array Occurrence -> Work t c -> Array (Work t c)
normalize occs row = map finish (foldl step [ { done: [], bindings: row.bindings, labels: row.labels } ] (Array.zip occs row.patterns))
  where
  step partials (Tuple o p) = do
    q <- partials
    e <- expand o p
    pure { done: Array.snoc q.done e.pattern, bindings: q.bindings <> e.bindings, labels: q.labels <> e.labels }
  finish q = row { patterns = q.done, bindings = q.bindings, labels = q.labels }

expand :: forall t c. Occurrence -> Pattern t c -> Array { pattern :: Pattern t c, bindings :: Array (Binding t), labels :: Array c }
expand o = case _ of
  PVar x -> [ { pattern: PAny, bindings: [ { name: x, occurrence: o, transform: Identity } ], labels: [] } ]
  PAs x inner -> map (\e -> e { bindings = Array.cons { name: x, occurrence: o, transform: Identity } e.bindings }) (expand o inner)
  POr choices -> do
    c <- choices
    e <- expand o c.pattern
    pure (e { labels = Array.cons c.label e.labels })
  other -> [ { pattern: other, bindings: [], labels: [] } ]

-- | The column to dispatch on: one the first row does not match whatever it
-- | holds, chosen as the module header says.
choose :: forall r t c. Constructors -> Array Occurrence -> Array { patterns :: Array (Pattern t c) | r } -> Either MatchError (Column t)
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
-- | domain, every head belonging to it. The domain of a column of tags is the
-- | one its tag patterns carry, which they all carry alike: the same keys and
-- | the same tail.
columnAt :: forall r t c. Constructors -> Int -> Occurrence -> Array { patterns :: Array (Pattern t c) | r } -> Either MatchError (Column t)
columnAt table j o rows = do
  let heads = Array.nubEq (Array.mapMaybe (\r -> Array.index r.patterns j >>= headOf) rows)
  case Array.head heads of
    Nothing -> pure { index: j, occurrence: o, heads, domain: Open }
    Just (HeadTag _) -> do
      let carried = Array.mapMaybe (\r -> Array.index r.patterns j >>= tagsOf) rows
      tags <- case Array.head carried of
        Just tags | Array.all (sameTags tags) carried -> pure tags
        _ -> Left (DomainMismatch o)
      traverse_ (holds tags) heads
      pure { index: j, occurrence: o, heads, domain: Variant tags }
    Just first -> do
      domain <- case coverageDomain table first of
        Just d -> pure d
        Nothing -> Left (unknown first)
      if Array.all (belongs domain first) heads then pure { index: j, occurrence: o, heads, domain }
      else Left (IncompatibleHeads o)
  where
  unknown = case _ of
    HeadConstructor name -> UnknownConstructor o name
    _ -> IncompatibleHeads o
  belongs domain first h = case domain, h, first of
    Constructors all, HeadConstructor name, _ -> Array.any (\c -> c.name == name) all
    Literals all, HeadLiteral l, _ -> Array.elem l all
    Open, HeadLiteral l, HeadLiteral l0 -> litType l == litType l0
    _, _, _ -> false
  sameTags a b = map _.key a.keys == map _.key b.keys && a.tail == b.tail
  holds tags = case _ of
    HeadTag key
      | Array.any (\k -> k.key == key) tags.keys -> pure unit
      | otherwise -> Left (UnknownTag o key)
    _ -> Left (IncompatibleHeads o)

complete :: forall t. Column t -> Boolean
complete c = case c.domain of
  Constructors all -> Array.all (\e -> Array.elem (HeadConstructor e.name) c.heads) all
  Literals all -> Array.all (\l -> Array.elem (HeadLiteral l) c.heads) all
  Open -> false
  Variant tags -> tags.tail == Closed && Array.all (\k -> Array.elem (HeadTag k.key) c.heads) tags.keys

headArity :: Constructors -> Head -> Int
headArity table = case _ of
  HeadConstructor name -> maybe 0 _.arity (Map.lookup name table)
  HeadLiteral _ -> 0
  HeadTag _ -> 1

headOf :: forall t c. Pattern t c -> Maybe Head
headOf = case _ of
  PCtor name _ -> Just (HeadConstructor name)
  PLit l -> Just (HeadLiteral l)
  PTag p -> Just (HeadTag p.key)
  _ -> Nothing

tagsOf :: forall t c. Pattern t c -> Maybe (Tags t)
tagsOf = case _ of
  PTag p -> Just p.domain
  _ -> Nothing

headLiteral :: Head -> Maybe Literal
headLiteral = case _ of
  HeadLiteral l -> Just l
  _ -> Nothing

isAny :: forall t c. Pattern t c -> Boolean
isAny = case _ of
  PAny -> true
  _ -> false

-- | The rows that match the constructor given at column `j`, its fields in the
-- | column's place: a row with that constructor there contributes its
-- | patterns of the fields, and one matching anything as many wildcards.
specializeConstructor :: forall r t c. Occurrence -> Int -> Qualified Ident -> Int -> Array { patterns :: Array (Pattern t c) | r } -> Either MatchError (Array { patterns :: Array (Pattern t c) | r })
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
specializeLiteral :: forall r t c. Int -> Literal -> Array { patterns :: Array (Pattern t c) | r } -> Array { patterns :: Array (Pattern t c) | r }
specializeLiteral j l = Array.mapMaybe \r -> case Array.index r.patterns j of
  Just (PLit l') | l' == l -> Just (r { patterns = without j r.patterns })
  Just PAny -> Just (r { patterns = without j r.patterns })
  _ -> Nothing

-- | The rows that match the tag given at column `j`, its payload in the
-- | column's place.
specializeTag :: forall r t c. Int -> RowKey -> Array { patterns :: Array (Pattern t c) | r } -> Array { patterns :: Array (Pattern t c) | r }
specializeTag j key = Array.mapMaybe \r -> case Array.index r.patterns j of
  Just (PTag p) | p.key == key -> Just (r { patterns = splice j [ p.payload ] r.patterns })
  Just PAny -> Just (r { patterns = splice j [ PAny ] r.patterns })
  _ -> Nothing

-- | The rows that match whatever stands at column `j`, the column removed.
defaultRows :: forall r t c. Int -> Array { patterns :: Array (Pattern t c) | r } -> Array { patterns :: Array (Pattern t c) | r }
defaultRows j = Array.mapMaybe \r -> case Array.index r.patterns j of
  Just PAny -> Just (r { patterns = without j r.patterns })
  _ -> Nothing

splice :: forall a. Int -> Array a -> Array a -> Array a
splice j xs ys = Array.take j ys <> xs <> Array.drop (j + 1) ys

without :: forall a. Int -> Array a -> Array a
without j ys = splice j [] ys

-- | Every label a row passes through: its own as a choice, and those of the
-- | or-patterns it holds.
rowLabels :: forall t c. Row t c -> Array c
rowLabels r = maybe [] pure r.choice <> Array.concatMap labelsOf r.patterns
  where
  labelsOf = case _ of
    POr choices -> Array.concatMap (\c -> Array.cons c.label (labelsOf c.pattern)) choices
    PAs _ inner -> labelsOf inner
    PCtor _ ps -> Array.concatMap labelsOf ps
    PRecord p -> Array.concatMap (labelsOf <<< _.pattern) p.fields
    PTag p -> labelsOf p.payload
    _ -> []

-- | How many leaves take each alternative.
leaves :: forall t. Plan t -> Map Int Int
leaves = go Map.empty
  where
  go acc = case _ of
    Leaf a _ -> Map.insertWith (+) a 1 acc
    Uncovered -> acc
    SwitchCtor _ branches fallback -> maybe identity (flip go) fallback (foldl (\m b -> go m b.plan) acc branches)
    SwitchLit _ branches fallback -> go (foldl (\m b -> go m b.plan) acc branches) fallback
    SwitchKey _ _ branches fallback -> maybe identity (flip go) fallback (foldl (\m b -> go m b.plan) acc branches)

-- | A value a `case` does not match, as patterns: a constructor applied to
-- | what its fields hold, a literal, or anything at all.
data Witness t
  = WitnessAny
  | WitnessConstructor (Qualified Ident) (Array (Witness t))
  | WitnessLiteral Literal
  -- | A record, or a tuple keyed by positions: what each key the rows write
  -- | holds, in the order of the keys, and whether no row closes it.
  | WitnessRecord { fields :: Array { key :: RowKey, witness :: Witness t }, open :: Boolean }
  -- | A tag, what its payload holds, and the type of its payload.
  | WitnessTag RowKey (Witness t) t

-- | One vector of values no row matches, where there is one, a row that may
-- | fail once its patterns match covering nothing, found by a fixed rule: the
-- | leftmost column first, a record taken apart where it stands and shown in
-- | the order of its keys, the constructors of a data type in the
-- | order the declaration writes them, a finite set of literals in its order
-- | (`false` before `true`), the tags of a variant in the order of their keys,
-- | and of an open set the literals the rows write, in the fixed order of
-- | literals, before anything else, written `_`; a variant whose row holds
-- | more than its known tags holds anything else, written `_`.
witness :: forall t c. Constructors -> Int -> Array (Row t c) -> Either MatchError (Maybe (Array (Witness t)))
witness table width rows = search occurrences (Array.concatMap (\r -> plain r.patterns) (Array.filter (not <<< _.fallible) rows))
  where
  occurrences = Array.mapWithIndex (\i _ -> OccScrutinee i) (Array.replicate width unit)

  search :: Array Occurrence -> Array (Array (Pattern t c)) -> Either MatchError (Maybe (Array (Witness t)))
  search occs patterns = case Array.head occs of
    Nothing -> pure (if Array.null patterns then Just [] else Nothing)
    Just o
      | Array.any (isJust <<< recordFirst) patterns -> do
          keys <- productKeys o 0 (map (\ps -> { patterns: ps }) patterns)
          let
            open = not (Array.any (maybe false (not <<< _.open) <<< recordFirst) patterns)
            n = Array.length keys
          found <- search (map (OccRecordField o) keys <> Array.drop 1 occs) (Array.concatMap (plain <<< keyed 0 keys) patterns)
          pure $ found <#> \w ->
            Array.cons
              (WitnessRecord { fields: Array.sortWith _.key (Array.zipWith { key: _, witness: _ } keys (Array.take n w)), open })
              (Array.drop n w)
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
        Variant tags -> do
          found <- firstJust (Array.sortWith _.key tags.keys) \k -> do
            payload <- search (Array.cons (OccVariantPayload o k.key) rest) (Array.concatMap (plain <<< _.patterns) (specializeTag 0 k.key rows'))
            pure (map (\w -> Array.cons (WitnessTag k.key (fromMaybe WitnessAny (Array.head w)) k.payload) (Array.drop 1 w)) payload)
          case found, tags.tail of
            Just w, _ -> pure (Just w)
            Nothing, Closed -> pure Nothing
            Nothing, _ -> map (Array.cons WitnessAny) <$> search rest (map _.patterns (defaultRows 0 rows'))

  -- the record pattern a row's first column holds, where it holds one; one
  -- that is closed writes every key its record has
  recordFirst ps = case Array.head ps of
    Just (PRecord p) -> Just p
    _ -> Nothing

  firstJust :: forall a. Array a -> (a -> Either MatchError (Maybe (Array (Witness t)))) -> Either MatchError (Maybe (Array (Witness t)))
  firstJust candidates f = case Array.uncons candidates of
    Nothing -> pure Nothing
    Just { head, tail } -> f head >>= case _ of
      Just w -> pure (Just w)
      Nothing -> firstJust tail f

-- | The rows of plain patterns a row of patterns stands for: its variables
-- | matching anything and its or-patterns taken apart.
plain :: forall t c. Array (Pattern t c) -> Array (Array (Pattern t c))
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
    PRecord p -> map (\ps -> PRecord p { fields = Array.zipWith (\f q -> f { pattern = q }) p.fields ps }) (plain (map _.pattern p.fields))
    PTag p -> map (\q -> PTag p { payload = q }) (flat p.payload)
    other -> [ other ]

derive instance (Eq t, Eq c) => Eq (Pattern t c)
derive instance Generic (Pattern t c) _

instance (Show t, Show c) => Show (Pattern t c) where
  show x = genericShow x

derive instance Eq Tail
derive instance Generic Tail _

instance Show Tail where
  show = genericShow

derive instance Eq Head
derive instance Generic Head _

instance Show Head where
  show = genericShow

derive instance Eq t => Eq (Domain t)
derive instance Generic (Domain t) _

instance Show t => Show (Domain t) where
  show = genericShow

derive instance Eq t => Eq (Transform t)
derive instance Generic (Transform t) _

instance Show t => Show (Transform t) where
  show = genericShow

derive instance Eq t => Eq (Plan t)
derive instance Generic (Plan t) _

instance Show t => Show (Plan t) where
  show x = genericShow x

derive instance Eq MatchError
derive instance Generic MatchError _

instance Show MatchError where
  show = genericShow

derive instance Eq t => Eq (Witness t)
derive instance Functor Witness
derive instance Generic (Witness t) _

instance Show t => Show (Witness t) where
  show x = genericShow x
