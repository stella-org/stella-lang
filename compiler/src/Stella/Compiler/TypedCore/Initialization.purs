-- | Whether a recursive binding group is initialization-safe: each right-hand
-- | side, evaluated in the order the group is written, reads only the members
-- | written before it ([Initialization Safety](../../../../docs/technical-references/03-Typed-Core/10-Initialization.md)).
-- |
-- | **The judgement is an abstract interpretation of Core.** For each
-- | expression it finds what evaluating it reads of the group's members
-- | before it has a value, and what its value may read later, a closure it
-- | holds reading them when applied. An application, a `perform`, and a
-- | `writeCell` promote what their parts may read later to what is read now; a
-- | constructor, a record, a variant, and a foreign build or take apart a value
-- | without running what it holds; a handling expression and a region count
-- | everything they hold as read. A join point is read where it is jumped to.
-- |
-- | **A read is seen through a witness**: the position of the occurrence read,
-- | and the position of the form that made the read immediate, if any. The
-- | positions number the group's right-hand sides in the order written, each
-- | read left to right, so the witnesses reported are the same whatever order
-- | the fixed point is reached in, and need no source position.
-- |
-- | **A variable resolves to a member or to a local**, binders shadowing as
-- | they bind. A variable bound outside the group's right-hand sides holds
-- | nothing of the group, and a group nested in them is judged as locals at
-- | what their values may read later.
module Stella.Compiler.TypedCore.Initialization
  ( Violation
  , topLevelViolations
  , localViolations
  , LocalViolation
  , localGroupViolations
  ) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Foldable (foldMap, foldl)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.Set (Set)
import Data.Set as Set
import Data.Tuple (Tuple(..))
import Stella.Compiler.TypedCore.Name (Ident, JoinName, Qualified)
import Stella.Compiler.TypedCore.Prim (foreignArity)
import Stella.Compiler.TypedCore.Signature (GlobalEntry(..), Signature, lookupGlobal)
import Stella.Compiler.TypedCore.Term (DecisionTree(..), Expr(..), OpClause(..), Occurrence(..), exprAnnotation, opClauseBody)

-- | A member's right-hand side reading a member it may not: the right-hand
-- | side and the member read, by their positions in the group, where the
-- | reference stands, and where the form that made the read immediate stands.
type Violation a =
  { initializer :: P.Int
  , read :: P.Int
  , at :: a
  , through :: Maybe a
  }

-- | A top-level group, its members in the order written: each refers to
-- | another by its global name.
topLevelViolations :: forall a. Signature -> P.Array { name :: Qualified Ident, value :: Expr a } -> P.Array (Violation a)
topLevelViolations sig members =
  violations sig (Map.fromFoldable (Array.mapWithIndex (\i m -> Tuple m.name i) members)) Map.empty (map _.value members)

-- | A local group, its members in the order written: each refers to another
-- | by a local name its group binds.
localViolations :: forall a. Signature -> P.Array { name :: Ident, value :: Expr a } -> P.Array (Violation a)
localViolations sig members =
  violations sig Map.empty (Map.fromFoldable (Array.mapWithIndex (\i m -> Tuple m.name (Member i)) members)) (map _.value members)

-- | A local group's right-hand side reading a member it may not, the two by
-- | the names the group binds them to.
type LocalViolation a =
  { initializer :: Ident
  , read :: Ident
  , at :: a
  , through :: Maybe a
  }

-- | Every local group an expression holds, wherever it stands, each judged
-- | apart: a group before the groups its right-hand sides hold, taken in the
-- | order written, and those before the groups its body holds.
localGroupViolations :: forall a. Signature -> Expr a -> P.Array (LocalViolation a)
localGroupViolations sig = groups
  where
  groups = case _ of
    Var _ _ -> []
    Global _ _ _ -> []
    Lit _ _ -> []
    Lam _ _ _ _ body -> groups body
    App _ f x -> groups f <> groups x
    TyLam _ _ _ body -> groups body
    TyApp _ e _ -> groups e
    ConstraintLam _ _ body -> groups body
    ConstraintApp _ e -> groups e
    Let _ _ _ value body -> groups value <> groups body
    LetRec _ bindings body ->
      Array.mapMaybe (named bindings) (localViolations sig (map (\b -> { name: b.name, value: b.value }) bindings))
        <> foldMap (groups <<< _.value) bindings
        <> groups body
    Case _ scrutinees tree -> foldMap groups scrutinees <> treeGroups tree
    LetJoin _ _ _ _ value body -> groups value <> groups body
    Jump _ _ args -> foldMap groups args
    RecordEmpty _ -> []
    RecordExtend _ _ value rest -> groups value <> groups rest
    RecordSelect _ _ e -> groups e
    RecordRestrict _ _ e -> groups e
    RecordUpdate _ _ record value -> groups record <> groups value
    RecordMerge _ left right -> groups left <> groups right
    VariantInject _ _ _ e -> groups e
    VariantWeaken _ _ _ e -> groups e
    VariantAbsurd _ _ e -> groups e
    Perform _ _ _ _ e -> groups e
    Handle _ e handler -> groups e <> groups handler.returnClause.body <> foldMap (groups <<< opClauseBody) handler.opClauses
    Region _ _ _ initial body -> foldMap groups initial <> groups body
    ReadCell _ _ _ -> []
    WriteCell _ _ _ value -> groups value
    OpenEff _ _ e -> groups e
  treeGroups = case _ of
    Leaf e -> groups e
    Bind _ _ tree -> treeGroups tree
    SwitchCtor _ branches fallback -> foldMap (treeGroups <<< _.tree) branches <> foldMap treeGroups fallback
    SwitchLit _ branches fallback -> foldMap (treeGroups <<< _.tree) branches <> treeGroups fallback
    SwitchKey _ branches fallback -> foldMap (treeGroups <<< _.tree) branches <> foldMap treeGroups fallback
    Guard condition yes no -> groups condition <> treeGroups yes <> treeGroups no
  named bindings v = do
    initializer <- Array.index bindings v.initializer
    read <- Array.index bindings v.read
    pure { initializer: initializer.name, read: read.name, at: v.at, through: v.through }

-- | What may be read of the group: for each member, by its position, the
-- | witnesses through which it is.
type Reads = Map P.Int (Set Witness)

-- | The position of the occurrence read, and of the form that made the read
-- | immediate. A read as it stands comes before a promoted one at the same
-- | occurrence.
type Witness = Tuple P.Int (Maybe P.Int)

data Bound
  = Member P.Int
  | Local Reads

type Env =
  { sig :: Signature
  , globals :: Map (Qualified Ident) P.Int
  , locals :: Map Ident Bound
  , joins :: Map JoinName { imm :: Reads, lat :: Reads }
  , summaries :: P.Array Reads
  }

-- | What an expression reads now and may read later; every subexpression's,
-- | for a form counting everything it holds; what each jump hands each join
-- | point; the annotation at each position; and the position after it.
type Res a =
  { imm :: Reads
  , lat :: Reads
  , deepImm :: Reads
  , deepLat :: Reads
  , jumps :: Map JoinName (P.Array Reads)
  , notes :: Map P.Int a
  , next :: P.Int
  }

violations :: forall a. Signature -> Map (Qualified Ident) P.Int -> Map Ident Bound -> P.Array (Expr a) -> P.Array (Violation a)
violations sig globals locals values = Array.concat (Array.mapWithIndex refused final.results)
  where
  final = settle (map (const Map.empty) values)
  -- the members' summaries, the least fixed point of what each value may
  -- read later
  settle summaries =
    let
      round = inTurn { sig, globals, locals, joins: Map.empty, summaries } values 0
      summaries' = map _.lat round.results
    in
      if summaries' == summaries then round else settle summaries'
  notes = foldl (\m r -> Map.union m r.notes) Map.empty final.results
  refused i r = Array.mapMaybe
    ( \(Tuple member witnesses) ->
        if member < i then Nothing
        else do
          Tuple ref form <- Set.findMin witnesses
          at <- Map.lookup ref notes
          pure { initializer: i, read: member, at, through: form >>= \p -> Map.lookup p notes }
    )
    (Map.toUnfoldable r.imm)

-- | Expressions read in turn, each from where the last ended.
inTurn :: forall a. Env -> P.Array (Expr a) -> P.Int -> { results :: P.Array (Res a), next :: P.Int }
inTurn env es start = foldl (\acc e -> let r = go env e acc.next in { results: Array.snoc acc.results r, next: r.next }) { results: [], next: start } es

go :: forall a. Env -> Expr a -> P.Int -> Res a
go env e pos = case e of
  Var _ x -> case Map.lookup x env.locals of
    Just (Member i) -> leaf (member i)
    Just (Local r) -> leaf { imm: Map.empty, lat: r }
    Nothing -> leaf none
  Global _ name _ -> leaf (maybe none member (Map.lookup name env.globals))
  Lit _ _ -> leaf none
  RecordEmpty _ -> leaf none
  ReadCell _ _ _ -> leaf none
  Lam _ x _ _ body ->
    let
      r = go (local x Map.empty env) body (pos + 1)
    in
      node { imm: Map.empty, lat: union r.imm r.lat } [ r ] r.next
  TyLam _ _ _ body -> through body
  TyApp _ inner _ -> through inner
  ConstraintLam _ _ body -> through body
  ConstraintApp _ inner -> through inner
  OpenEff _ _ inner -> through inner
  RecordSelect _ _ inner -> through inner
  RecordRestrict _ _ inner -> through inner
  VariantWeaken _ _ _ inner -> through inner
  VariantAbsurd _ _ inner -> through inner
  App _ f x
    | building env e -> built [ f, x ]
    | otherwise -> promoting [ f, x ]
  RecordExtend _ _ value rest -> built [ value, rest ]
  RecordUpdate _ _ record value -> built [ record, value ]
  RecordMerge _ left right -> built [ left, right ]
  VariantInject _ _ _ value -> built [ value ]
  Perform _ _ _ _ argument -> promoting [ argument ]
  WriteCell _ _ _ value -> promoting [ value ]
  Let _ y _ value body ->
    let
      r1 = go env value (pos + 1)
      r2 = go (local y r1.lat env) body r1.next
    in
      node { imm: union r1.imm r2.imm, lat: r2.lat } [ r1, r2 ] r2.next
  LetRec _ bindings body ->
    let
      -- the nested group's members, locals at what their values may read
      -- later, the least fixed point over the nested group
      nested reads =
        let
          inner = foldl (\en (Tuple b r) -> local b.name r en) env (Array.zip bindings reads)
          values = inTurn inner (map _.value bindings) (pos + 1)
          reads' = map _.lat values.results
        in
          if reads' == reads then { inner, values } else nested reads'
      settled = nested (map (const Map.empty) bindings)
      rb = go settled.inner body settled.values.next
      parts = Array.snoc settled.values.results rb
    in
      node { imm: unions (map _.imm parts), lat: rb.lat } parts rb.next
  Case _ scrutinees tree ->
    let
      rs = inTurn env scrutinees (pos + 1)
      rt = goTree env (map _.lat rs.results) tree rs.next
      parts = Array.snoc rs.results rt
    in
      node { imm: unions (map _.imm parts), lat: rt.lat } parts rt.next
  LetJoin _ j params _ value body ->
    let
      -- the join point's body under what every jump hands its parameters, and
      -- what it reads, the least fixed point over its jumps, its own among them
      joined summary args =
        let
          withJoin = env { joins = Map.insert j summary env.joins }
          r1 = go (foldl (\en (Tuple p a) -> local p.name a en) withJoin (Array.zip params args)) value (pos + 1)
          r2 = go withJoin body r1.next
          handed = fromMaybe [] (Map.lookup j (mergeJumps r1.jumps r2.jumps))
          args' = Array.zipWith union args (handed <> map (const Map.empty) (Array.drop (Array.length handed) args))
          summary' = { imm: r1.imm, lat: r1.lat }
        in
          if args' == args && summary' == summary then { r1, r2 } else joined summary' args'
      settled = joined { imm: Map.empty, lat: Map.empty } (map (const Map.empty) params)
      parts = [ settled.r1, settled.r2 ]
    in
      (node { imm: settled.r2.imm, lat: settled.r2.lat } parts settled.r2.next)
        { jumps = Map.delete j (mergeJumps settled.r1.jumps settled.r2.jumps) }
  Jump _ j arguments ->
    let
      rs = inTurn env arguments (pos + 1)
      summary = fromMaybe { imm: Map.empty, lat: Map.empty } (Map.lookup j env.joins)
      r = node { imm: union (unions (map _.imm rs.results)) summary.imm, lat: summary.lat } rs.results rs.next
    in
      r { jumps = mergeJumps r.jumps (Map.singleton j (map _.lat rs.results)) }
  Handle _ body handler ->
    let
      rb = go env body (pos + 1)
      rr = go (local handler.returnClause.binder Map.empty env) handler.returnClause.body rb.next
      clauses = foldl
        ( \acc clause ->
            let
              r = case clause of
                FullClause c -> go (local c.contBinder.name Map.empty (local c.argBinder.name Map.empty env)) c.body acc.next
                FastClause c -> go (local c.argBinder.name Map.empty env) c.body acc.next
            in
              { results: Array.snoc acc.results r, next: r.next }
        )
        { results: [], next: rr.next }
        handler.opClauses
    in
      whole ([ rb, rr ] <> clauses.results) clauses.next
  Region _ _ _ initial body ->
    let
      rs = inTurn env initial (pos + 1)
      rb = go env body rs.next
    in
      whole (Array.snoc rs.results rb) rb.next
  where
  none = { imm: Map.empty, lat: Map.empty }
  member i = { imm: Map.singleton i (Set.singleton (Tuple pos Nothing)), lat: fromMaybe Map.empty (Array.index env.summaries i) }

  -- this form, its reads, the results of its parts, and the position after it
  node :: { imm :: Reads, lat :: Reads } -> P.Array (Res a) -> P.Int -> Res a
  node own parts next =
    { imm: own.imm
    , lat: own.lat
    , deepImm: union own.imm (unions (map _.deepImm parts))
    , deepLat: union own.lat (unions (map _.deepLat parts))
    , jumps: foldl (\m r -> mergeJumps m r.jumps) Map.empty parts
    , notes: Map.insert pos (exprAnnotation e) (foldl (\m r -> Map.union m r.notes) Map.empty parts)
    , next
    }
  leaf own = node own [] (pos + 1)
  through inner =
    let
      r = go env inner (pos + 1)
    in
      node { imm: r.imm, lat: r.lat } [ r ] r.next
  -- what builds a value of its parts without running anything they hold
  built parts =
    let
      rs = inTurn env parts (pos + 1)
    in
      node { imm: unions (map _.imm rs.results), lat: unions (map _.lat rs.results) } rs.results rs.next
  -- what may apply anything its parts hold
  promoting parts =
    let
      rs = inTurn env parts (pos + 1)
    in
      node
        { imm: unions (map (\r -> union r.imm (promote pos r.lat)) rs.results)
        , lat: unions (map _.lat rs.results)
        }
        rs.results
        rs.next
  -- what counts everything it holds, at any depth, as read through it, beside
  -- what its parts read as they stand
  whole parts next = node
    { imm: union (unions (map _.imm parts)) (promote pos (unions (map (\r -> union r.deepImm r.deepLat) parts)))
    , lat: unions (map _.deepLat parts)
    }
    parts
    next

-- | A decision tree, each variable it binds at what the scrutinee its
-- | occurrence starts from may read later.
goTree :: forall a. Env -> P.Array Reads -> DecisionTree a -> P.Int -> Res a
goTree env scrutinees tree pos = case tree of
  Leaf e -> go env e pos
  Bind y occurrence rest -> goTree (local y (fromMaybe Map.empty (Array.index scrutinees (rootOf occurrence))) env) scrutinees rest pos
  SwitchCtor _ branches fallback -> branching (map _.tree branches <> Array.fromFoldable fallback)
  SwitchLit _ branches fallback -> branching (Array.snoc (map _.tree branches) fallback)
  SwitchKey _ branches fallback -> branching (map _.tree branches <> Array.fromFoldable fallback)
  Guard e yes no ->
    let
      rg = go env e pos
      ry = goTree env scrutinees yes rg.next
      rn = goTree env scrutinees no ry.next
    in
      combine [ rg, ry, rn ] (union ry.lat rn.lat) rn.next
  where
  branching trees =
    let
      rs = foldl (\acc t -> let r = goTree env scrutinees t acc.next in { results: Array.snoc acc.results r, next: r.next }) { results: [], next: pos } trees
    in
      combine rs.results (unions (map _.lat rs.results)) rs.next
  -- a tree is no expression, and holds no position of its own
  combine parts lat next =
    { imm: unions (map _.imm parts)
    , lat
    , deepImm: unions (map _.deepImm parts)
    , deepLat: unions (map _.deepLat parts)
    , jumps: foldl (\m r -> mergeJumps m r.jumps) Map.empty parts
    , notes: foldl (\m r -> Map.union m r.notes) Map.empty parts
    , next
    }

-- | The scrutinee an occurrence starts from.
rootOf :: Occurrence -> P.Int
rootOf = case _ of
  OccScrutinee i -> i
  OccField o _ _ -> rootOf o
  OccRecordField o _ -> rootOf o
  OccVariantPayload o _ -> rootOf o

-- | Whether an application is part of a constructor's or a foreign's chain,
-- | with no more value arguments than its arity: what builds a value, or a
-- | foreign that may carry a function but not apply one.
building :: forall a. Env -> Expr a -> P.Boolean
building env e = case spine e 0 of
  Just { name, depth } -> case arityOf name of
    Just arity -> depth <= arity
    Nothing -> false
  Nothing -> false
  where
  spine expr depth = case expr of
    App _ f _ -> spine f (depth + 1)
    TyApp _ inner _ -> spine inner depth
    ConstraintApp _ inner -> spine inner depth
    Global _ name _ | not (Map.member name env.globals) -> Just { name, depth }
    _ -> Nothing
  arityOf name = case lookupGlobal env.sig name of
    Just (GlobalCtor info) -> Just (Array.length info.fields)
    Just (GlobalValue info) | info.isForeign -> Just (foreignArity info.scheme)
    _ -> Nothing

local :: Ident -> Reads -> Env -> Env
local name reads env = env { locals = Map.insert name (Local reads) env.locals }

union :: Reads -> Reads -> Reads
union = Map.unionWith Set.union

unions :: P.Array Reads -> Reads
unions = foldl union Map.empty

-- | What may be read later, read now, through the form at the position given.
promote :: P.Int -> Reads -> Reads
promote p = map (Set.map (\(Tuple ref _) -> Tuple ref (Just p)))

mergeJumps :: Map JoinName (P.Array Reads) -> Map JoinName (P.Array Reads) -> Map JoinName (P.Array Reads)
mergeJumps = Map.unionWith (\a b -> Array.zipWith union a b <> Array.drop (Array.length a) b <> Array.drop (Array.length b) a)
