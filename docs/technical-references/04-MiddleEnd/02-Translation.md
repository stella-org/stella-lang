# Translation: Typed Core to Mid IR

`translate` takes a Core module together with what checking made of it — the
signature it contributes and its value declarations, annotated — and produces a
Mid IR module. The module supplies the header and the type-level declarations,
which checking does not annotate because a data declaration has no type; the
value groups supply the terms. It performs the erasures of
[Semantics](../03-Typed-Core/06-Semantics.md), names every intermediate result,
folds application spines, materializes occurrences, and lifts every function
body out of its nesting.

**Translation checks nothing.** Every property it relies on the Core type
checker has already established, and a term that has not been type checked never
reaches it ([Elaboration](../02-Surface-Language/01-Elaboration.md)). What
translation owes in return is the invariants of
[Mid IR](01-Mid-IR.md), which a verifier over its output checks.

## What it needs besides the term

| From `Σ` | Used for |
| --- | --- |
| A constructor's tag and arity | `ctor`, `pap`, and the constructor table |
| A type constructor's entry, data or intrinsic | `rep` |
| An effect's operations | The effect table |
| A `foreign`'s declared type | Its arity, which is the number of arrows on the spine |
| A binding's type | `rep` of that binding |

One thing is not in `Σ`: the **definitional arity** of a top-level value, which
is a property of its right-hand side and not something its type says.

```text
arity(M.x) = |x̄|   where the erased right-hand side of M.x is  λ x̄. e  and e is not a lambda
arity(M.x) = absent  where the erased right-hand side is not a lambda
```

**Arity is absent, not zero, where the right-hand side is not a lambda.**
`nonrec alias = Main.f` has no leading lambda, yet what it stores is whatever
`Main.f` evaluates to, which is a function of `Main.f`'s arity and not a
function of none. Reading zero there would have every call to `alias` treated as
an over-application of a nullary function. Absent means `callu`, which is
correct for every callee.

**The arity is the number of parameters the function table entry has**, because
translation collapses a run of adjacent lambdas into one entry with that many
parameters ([closure conversion](#closure-conversion)). The two must agree:
`callk` supplies exactly the callee's parameters, so an entry of one parameter
called with two is a contradiction rather than a partial application.

For a value of the module being translated the arity is read off the right-hand
side; for an imported one it comes from that module's `.dmi`, the interface file
paired with its `.dmo`, which must therefore publish it
([Bytecode](../05-Backend/01-Bytecode.md)).

**The arities of the imports reach translation checked.** An arity below one, and
two interfaces of one module, are refused where the interfaces are gathered into
the environment translation reads, and an arity is taken from that environment
only for a module this one imports. A wrong arity is unsound rather than slow,
and a `.dmi` file is not the only way one arrives
([Interface](../05-Backend/03-Interface.md)).

**Unknown arity is always safe.** Where an interface does not supply one,
translation emits `callu`, which resolves application at run time and is correct
for every callee. Arity is what allows the sharper `callk`, never what makes a
call correct.

## Where a representation type comes from

Every `let` in Mid IR carries a `Rep`, and `rep` is a function of a Core type
([Mid IR](01-Mid-IR.md)). Three sources supply one, and they differ in how much
they know.

| Source | Supplies |
| --- | --- |
| A binder Core annotates — a `Lam` parameter, a `Let`, a `LetJoin` parameter, a clause binder | The type, written in the term |
| `Σ` | The result of a `callk`, an `ffi`, or a `ctor`, and the owner of a constructor |
| The shape of the computation | `Clos` for a `closure` and a `pap`, `Rec` and `Variant` for the record and variant operations |

What none of the three supplies is the result of a `callu`, the type a `field`
or a `recSelect` projects, or the type an operation resumes with. Each of those
is determined by the type of something else in the term — the callee, the
occurrence, the effect row element — and recovering it means synthesizing the
type of an arbitrary subterm.

**`Val` is sound wherever a type is not to hand.** It says the representation is
unknown, which every backend already has to handle, so the cost of a missing
annotation is precision and never correctness.

Precision is therefore a function of what the Core term's annotation carries,
and **translation consumes a Core term annotated with types**. Core's `Expr` is
parameterized over its annotation precisely so that it may carry more than a
source span.

**The producer is the Core type checker**, which already threads the local
context and the ambient effect row and so has computed every type above by the
time it accepts a term. A separate pass could compute them too, by threading the
same context and the same ambient row — the result type of a `perform` is read
from the effect at the head of the row element its key selects, and only the
ambient row says what that element is — but it would be the checker's work done
twice. **Not discarding what is already computed is the reason**, not
impossibility.

Two things follow about what the annotation must be.

**It records the type the checker used, not one re-inferred afterwards.**
Running inference over each subexpression independently once checking is done is
a different judgement from what the checker performed: checking uses an expected
type at a lambda and at a variant injection, among others, and a term accepted
in the first sense need not be annotatable in the second. Whatever produces the
annotation leaves the set of accepted and rejected terms unchanged, and leaves
the term's own source annotations as they were.

**It covers the occurrences of a decision tree, which are not expressions.** An
occurrence is a path, and `DecisionTree` holds paths rather than `Expr`s
([Terms and Matching](../03-Typed-Core/04-Terms-and-Matching.md)), so annotating
expressions alone gives the `field`, `payload`, and `recSelect` computations
derived from one no type at all. **The checker emits `Ω` instead**, for the same
reason as above: it built one to check the tree with, and deriving a second from
the scrutinee and `Σ` would repeat the work.

`Ω` is carried at the `Case` and not at each node of the tree. A decision tree
has no annotation of its own — it carries no source span either, an error inside
one being reported at the `case` that contains it
([Kinds and Types](../03-Typed-Core/01-Kinds-and-Types.md)) — and one map per
`case` loses nothing, because within one tree a path has one type.

**The one exception is not recorded.** In the default branch of a `switchKey`
the occurrence stands at the residual variant rather than the whole, and what
`Ω` holds is the type it has elsewhere. The two differ in the row alone, so they
have the same representation type, and a payload the tree goes on to project
from either is `F(k)` of the same payload — the residual row removes keys and
rewrites none.

An occurrence the map does not hold takes `Val`, as any other binding does.

## Erasure

The forms below carry no run-time content and disappear. This is the erasure
`⌊·⌋` of [Semantics](../03-Typed-Core/06-Semantics.md), performed as translation
descends rather than as a pass of its own.

```text
TyLam a v          ⟹  translate v
TyApp e τ          ⟹  translate e
ConstraintLam C v  ⟹  translate v
ConstraintApp e    ⟹  translate e
Global M.x [[κ̄]]   ⟹  the global, without the kind vector
OpenEff ρ e        ⟹  translate e
VariantWeaken k τ e ⟹ translate e
```

Erasing `TyLam` and `ConstraintLam` moves no evaluation, because the body of
either is a value form — the value restriction is what makes the abstraction
erasable at all.

The result type written on a `LetJoin`, the payload of the row element a
`Handle` writes, and the types of a `Region`'s layout go the same way: all three
were written for the checker.

## Naming intermediate results

Translation is two mutually recursive functions over a Core term.

```text
go     : Core.Expr -> Dest -> expr           the term's value reaches Dest
atomize: Core.Expr -> (atom -> expr) -> expr the term's value is named, then used

Dest ::= ret | jump j
```

`Dest` is where a term's value goes. At the root of a function body it is `ret`;
inside a branch it is whatever the branch inherited; and `atomize` introduces
`jump j` when it has to.

`atomize` has three cases, and which one applies is decided by the shape of the
term alone.

| The term is | What `atomize e k` produces |
| --- | --- |
| A variable, a literal, a top-level value, or a nullary constructor | `k(atom)`, binding nothing |
| Anything translating to a single computation | `let x : Rep = c in k(local x)` |
| A control construct — a `Case` — or a `Jump` | `letjoin j (x : Rep) = k(local x) in go e (jump j)` |

The third case is what keeps every control construct in tail position. Its
alternative, duplicating `k` into each branch, duplicates code, and a join point
is exactly the construct Core carries so that it need not be duplicated
([Terms and Matching](../03-Typed-Core/04-Terms-and-Matching.md)).

A `Let` or a `LetRec` in argument position needs neither: its binding is emitted
and its body is atomized in turn, so the binding scopes over `k` as it must.

### The order of evaluation is preserved, not chosen

Core fixes the order in which subterms are evaluated, and the order is
observable because any subterm may perform an effect
([Effects](../03-Typed-Core/03-Effects.md)). Translation emits `let` bindings in
that order and introduces no other.

```text
App …                  the spine's arguments right to left, then its head (D35)
RecordExtend k e1 e2   atomize e1 (\a1 -> atomize e2 (\a2 -> ... ))
Case (e1 … en) dt      each scrutinee in turn, then the tree
Jump j (e1 … en)       each argument in turn, then the transfer
Perform k op e         the argument, then the operation
WriteCell ℓ.k e        the value, then the write
Handle e h             install, then the body
Region [ℓ] ( k̄ : σ̄ ) @ ( ē ) e
                       each initial value in turn, then open, then the body
```

**Application is the one construct that reads right to left**, and it is why a
spine can be folded at all: every argument reaches a value before any
application happens, so one multi-argument call performs exactly what the nested
applications did. Under the opposite order the evaluation of `f x` would stand
between the arguments of `f x y`, and folding would move whatever it performs.

## Application spines

An application in Core is a chain of unary `App` nodes, with `TyApp`,
`ConstraintApp`, and `OpenEff` interleaved anywhere along it. Translation peels
the whole chain at once.

```text
peel : Core.Expr -> { head : Core.Expr, args : [Core.Expr] }

peel e  |  erased(e) = App e1 e2  =  let h = peel e1 in { head: h.head, args: h.args <> [e2] }
        |  otherwise            =  { head: e, args: [] }

erased   removes every wrapper erasure removes: Λ, [τ], [•], openEff, weaken
```

**All six go, not the four that wrap a function.** `weaken k [τ] (f x)` produces a
variant rather than a function, so nothing else in the translation strips it,
and a peel stopping there hands back the term it was given with no argument
taken off — leaving the head to be named, which is the same term again.

**Peeling looks through `OpenEff`**, which matters more than it appears to.
Effect widening is inserted once per argument consumed, because currying makes
each argument an arrow of its own ([Examples](../03-Typed-Core/08-Examples.md)),
so a saturated call to a pure global under a non-empty ambient row arrives
wrapped several times over. A spine that stopped at the first `OpenEff` would
emit a chain of `callu`s where one `callk` belongs.

**Every argument is atomized before the head, and the arguments right to left**
(D35). Only then is the head atomized, and only then is any call emitted.

```text
atomize a_n (\v_n -> … atomize a_1 (\v_1 -> atomize head (\h -> …)))
```

The **vector handed to the call keeps the source order** `[v_1, …, v_n]`. What
runs backwards is the evaluation, not the argument list.

The head then decides which computation is emitted.

| Head, after erasure | Arity `n` from | `\|args\| = n` | `\|args\| < n` | `\|args\| > n` |
| --- | --- | --- | --- | --- |
| A top-level value `M.x` | its definitional arity | `callk` | `pap` | `callk` with the first `n`, then `callu` with the rest |
| A `foreign` `M.f` the ABI manifest holds as an **operation** | arrows on its declared type's spine | `prim` | `pap` over the operation | `prim` with the first `n`, then `callu` with the rest |
| Any other `foreign` `M.f` | arrows on its declared type's spine | `ffi` | `pap` | `ffi` with the first `n`, then `callu` with the rest |
| A constructor `M.Ctor` | its arity in `Σ` | `ctor` | `pap` | does not arise |
| Anything else | not known | — | — | `callu` |

Over-application of a constructor does not arise because a constructor's
declared result is `T ā` and never an arrow, so a saturated one is a completed
structure rather than something further arguments could be applied to
([Semantics](../03-Typed-Core/06-Semantics.md)).

**Splitting an over-applied spine moves nothing**, all of its arguments being
values by the time the first call runs. Where that call performs an operation,
the applications still to come are part of the continuation it captures, which
is what the nested applications would have given.

`callu` applies its arguments left to right for the same reason: they are values
already, so the only effects left are those of the callees, and those happen in
the order the nested applications put them in.

A head with no arguments at all is the degenerate case of the same table: a
top-level value becomes the atom `global M.x`, a constructor of arity 0 the atom
`const M.Ctor`, a constructor of greater arity a `pap`, a `foreign` of arity 0 an
`ffi` or a `prim` with no arguments — **which carries it out**, the spine being
saturated as soon as it is formed — and a `foreign` of greater arity a `pap`.

**Both paths read the manifest at the same point.** Whether an entry is an
operation is settled where the head is classified, so the bare reference and the
saturated call cannot disagree, and a declaration whose arity the manifest does
not give that entry is reported rather than fallen back from: an operation run
with the wrong number of operands is not something a consumer can detect
([Mid IR](01-Mid-IR.md)).

## Decision trees

A Core decision tree dispatches on occurrences, which are paths from a
scrutinee. Mid IR dispatches on atoms. Translation carries a finite map from
occurrences to the atoms holding them.

```text
occ : Occurrence ⇀ atom
```

`case (e1 … en) of dt` atomizes each scrutinee in turn and seeds the map with
`OccScrutinee i ↦ a_i`, then descends the tree with the destination it was given.

### Materializing an occurrence

```text
materialize o k
  | o ∈ occ            = k(occ(o))
  | o = OccField o' Ctor j      = materialize o' (\a -> let x = field a Ctor j   in k(local x))
  | o = OccRecordField o' key   = materialize o' (\a -> let x = recSelect key a  in k(local x))
  | o = OccVariantPayload o' key = materialize o' (\a -> let x = payload key a   in k(local x))
```

Each result extends `occ` for the rest of the branch it was emitted in.

**An occurrence is materialized where it is first used, never before.** A field
of a constructor exists only under the `switchCtor` that selected that
constructor, and a variant's payload only under the `switchKey` that selected
that key — projecting either earlier would read a value that is not there.
Materializing at the point of use, with the map scoped to the branch, is what
keeps that correct without any analysis. A record needs no such branch, having
an element at every key of its row, so `recSelect` may be emitted wherever the
record itself is available.

The map is what keeps a repeated occurrence from being projected twice. An
occurrence has no effect, so naming one once and referring to it is sound, and
it is the only sharing translation performs.

### Node by node

| Core | Mid IR |
| --- | --- |
| `Leaf e` | `go e dest` |
| `Bind x o dt` | `materialize o (\a -> …)`, with `x` bound to `a`. A `let` is emitted only where `o` was not already materialized |
| `SwitchCtor o bs d` | `materialize o`, then `switchCtor`. In each branch `occ` is extended lazily with that constructor's fields |
| `SwitchLit o bs d` | `materialize o`, then `switchLit`. The default is mandatory and is always present |
| `SwitchKey o bs d` | `materialize o`, then `switchKey`. In each branch `o ? k_i` becomes available; in the default `o` keeps its atom, standing at the residual variant |
| `Guard e dt1 dt2` | `atomize e (\a -> if a then … else …)` |

`Bind` does not always emit an instruction. Where the occurrence is already
held by an atom — a scrutinee, or a projection an earlier node needed — the
binder is an alias and translation records it in its local environment.

In the default branch of `switchCtor` and of `switchLit` the occurrence keeps
the atom it had, Core tracking no refinement there. In the default branch of
`switchKey` the atom is the same value at the residual variant type; only its
`Rep` would differ, and `Variant` is one class.

## Effects

`Perform k op e` atomizes its argument and produces `perform k.op a`.
`ReadCell ℓ.k` is `readCell r i`, and `WriteCell ℓ.k e` atomizes the value and
produces `writeCell r i a`, where `r` is the atom holding the identity of the
region `ℓ` names and `i` the position of `k` in its layout. Each is one
computation, bound where any other is. **The region name and the key do not
survive**: a cell is named by the identity of an opening and a position (D36), the
erasure of [Semantics](../03-Typed-Core/06-Semantics.md).

The type binders of a `Perform` are erased with every other type application, and
its key is carried through. Nothing consults the ambient effect row, which is
gone: the operation is named by its own name, and the key is what a handler is
found by ([Mid IR](01-Mid-IR.md)).

## Handlers

`Handle e h` produces the computation `handle h f [ā]`. **The handled computation
becomes a function, as every clause does.**

```text
for the handled computation e:
  lift it into a Function of no parameters, whose body is  go e ret
  its captures are the free locals of e
  that function and those captures are the f and ā of the handle

for the return clause and each operation clause:
  lift its body into a Function whose parameters are the clause's binders
    return clause : one parameter, the value the body produced
    fast clause   : one parameter, the operation's argument
    full clause   : two parameters, the argument and the continuation
  its captures are the free locals of the body, less its parameters
  emit a ClauseRef naming the function and supplying those captures as atoms
```

The operation's own type binders `b̄_i` are erased with every other type
abstraction. The handler keeps `key(ent)` and drops the payload.

**Lifting the body is what lets the result of a `handle` be used.** The
computation is a `handle`, so `atomize` binds it with a `let` like any other and
whatever consumes the value is reached in the ordinary way. Translating the body
in place instead would leave the return clause — a function, entered when the
body produces its value — with the value of the whole `handle` and no way to
deliver it: it cannot `jump` to a join point of the enclosing scope, a join
point not crossing a function boundary, and `ret` from it would return from the
wrong thing.

Nothing has to be carried across the boundary either. Core discards the join
point context at a `handle`, and a function boundary discards it anyway, so the
two agree without translation doing anything to make them.

**A clause's form is copied, never inferred.** Core writes `full` or `fast` on
every clause (D28), and whether a `full` clause happens to resume once cannot be
read off its syntax. Translation reads the marker and writes it out.

## Regions

`Region [ℓ] ( k̄ : σ̄ ) @ ( ē ) e` produces the computation `region k̄ f [ā] @ [v̄]`.
**The body becomes a function of one parameter, the region's identity.**

```text
for the initial values ē:
  atomize each in turn, before anything else of the region is emitted
  the atoms are the [v̄], one per key of the layout and in the order it writes them

for the body e:
  lift it into a Function whose one parameter is a fresh local of Rep Val,
    which ℓ stands for within the body
  its captures are the free locals of e, then the identities of the regions
    other than ℓ whose cells it reaches
  that function and those captures are the f and ā of the region
```

**Of the layout, the keys survive and nothing else does.** `k̄` is the keys in the
order the layout writes them, which is what positions the cells and pairs them with
the initial values; the types the layout assigns are annotations the checker used
and are erased (D36).

**A region name stands for an atom.** Within a function, translation maps each
region name in scope to the local holding its identity and to its layout's keys.
`ReadCell ℓ.k` and `WriteCell ℓ.k e` read the atom and the position of `k` from
there. A name the map does not hold, or a key its layout does not declare, is
input a checked term cannot be, and translation stops on it rather than emitting
a cell of no region.

**The initial values are atomized ahead of everything else the `region` emits.**
They are evaluated before the region opens, so the bindings that name them stand
outside the `region` — and they are not among the body's captures, the body naming
none of them.

**The identity is captured like a local.** A function whose body reaches the cells
of a region it does not open — a handler clause, a lambda written in one, the body
of a nested `handle` — takes the identity among its captures, and the site that
builds it supplies the atom the enclosing function holds. That is the identity of
the opening the closure is made under, which is what a closure called later, or in
a copy of the region, reaches the cells of ([Mid IR](01-Mid-IR.md)).

The identity is created for no name, so the debug table names no local for it.

## Closure conversion

A **run of adjacent lambdas** becomes one entry of the function table.

```text
λ x1 : τ1. … λ xn : τn. body       where body is not a lambda

  ⟹  emit Function { params:   [(x1, rep τ1), …, (xn, rep τn)]
                    , captures: fv(body) ∖ {x1 … xn}
                    , body:     go body ret }
      and, at the site, the computation  closure f [captures]
```

**The run is taken after erasure**, so a `Λ` or a constraint abstraction
standing between two lambdas does not break it: `Λa. λx. Λb. λy. e` erases to
`λx. λy. e` and yields one entry of two parameters.

Collapsing the run is what makes arity mean one thing. `f = λx. λy. x` has
definitional arity 2, so a saturated call site emits `callk f [a, b]`; were the
entry a function of one parameter returning another closure, that call would
supply two parameters to a function that has one. Applying `f` to one argument
is a `pap`, and applying a `pap` that saturates it performs the call — which is
the same computation, β-reduction on an inner lambda being pure.

A lambda whose body is not a lambda is the degenerate case, `n = 1`.

`fv` is the free **locals** of a body: neither globals, which are named
directly, nor join points, which cannot be captured because a join point does
not cross a function boundary. **The identity of every region whose cells the body
reaches and does not open is among them**, a region name being free in a term
exactly where a `ReadCell` or a `WriteCell` names it outside the `Region` binding
it ([Regions](#regions)).

Captures are ordered, and the order the function entry records is the order
`closure` supplies them in: translation puts the value variables first and the
region identities after them. Nothing depends on which order translation picks, so
long as it picks one and uses it on both sides.

A lambda nested inside a run's body lifts in turn, an inner one's free variables
becoming captures of the outer as well where it needs them.

`LetRec` produces a group of closures. Each right-hand side is guarded and so is
syntactically a function value (D14), which is what allows every closure of the
group to be allocated before any capture list is filled.

## Declarations and module initialization

| Core declaration | Mid IR |
| --- | --- |
| `DeclData` | One constructor table entry per constructor: its reference, owner, tag, and arity. `isNewtype` is carried through for a backend that erases the representation |
| `DeclEffect` | One effect table entry, listing the operations |
| `DeclForeign` | One foreign table entry, with the arity counted off the declared type's spine |
| `DeclNonRec`, `DeclRec` | One function per binding, and one entry in `globals` per binding: `func` where the right-hand side is a lambda, `run` otherwise |

**Which entry a binding gets is decided by the shape of its right-hand side and
not by the form of its declaration**, the shape being what is left once erasure
has looked through the wrappers. A right-hand side that is a lambda becomes that
function, installed as a closure over an empty capture list: at the top level
every free name is a global, so there is nothing to capture and nothing to
evaluate. Anything else becomes a function of no parameters that initialization
evaluates once, in declaration order
([Semantics](../03-Typed-Core/06-Semantics.md)).

A `rec` group's members are function values already (D14), so each is a `func`.
A `nonrec` is one or the other according to what it holds.

**This is the same test the definitional arity is read by**, and the two have to
agree: a `nonrec` holding a lambda has a definitional arity, so a call to it is
`callk`, and the global that call reaches has to hold the function whose arity
it supplied rather than the result of evaluating a thunk. Reading one property
off the declaration and the other off the term is what lets them disagree.

The order of `globals` is the dependency order Core required of value
declarations, preserved rather than recomputed.

## A worked example

The vertical slice of [Examples](../03-Typed-Core/08-Examples.md), in Core:

```text
rec {
  Main.sum : List Int -{()}-> Int
    = λ (xs : List Int).
        case (xs) of
          switchCtor s0 {
            Main.Nil  -> leaf 0
            Main.Cons -> bind x  = s0 ! Main.Cons . 0 in
                         bind ys = s0 ! Main.Cons . 1 in
                         leaf (Base.Int.add x (Main.sum ys))
          }
}

nonrec Main.result : Int
  = Main.sum ( Main.Cons [Int] 1
                 ( Main.Cons [Int] 2
                     ( Main.Cons [Int] 3 ( Main.Nil [Int] ) ) ) )
```

and in Mid IR:

```text
ctors    Main.Nil  of Main.List  tag 0  arity 0
         Main.Cons of Main.List  tag 1  arity 2

function #0 params [ xs : Data Main.List ] captures []
  switchCtor (local xs) {
    Main.Nil  -> ret (lit 0)
    Main.Cons -> let x  : Int            = field (local xs) Main.Cons 0 in
                 let ys : Data Main.List = field (local xs) Main.Cons 1 in
                 let s  : Int            = callk Main.sum [ local ys ] in
                 tail (prim IntAdd [ local x, local s ])
  }

function #1 params [] captures []
  let c0 : Data Main.List = ctor Main.Cons [ lit 3, const Main.Nil ] in
  let c1 : Data Main.List = ctor Main.Cons [ lit 2, local c0 ] in
  let c2 : Data Main.List = ctor Main.Cons [ lit 1, local c1 ] in
  tail (callk Main.sum [ local c2 ])

globals  Main.sum    func #0
         Main.result run  #1
```

Seven things in that output are worth naming.

- **`Main.Nil [Int]` became the atom `const Main.Nil`.** The type application erased, and a saturated constructor of arity 0 is a constant.
- **`Base.Int.add x (Main.sum ys)` folded into one `prim`.** Core applies it one argument at a time, and the spine collapsed to a single saturated call.
- **The head classified as the operation `IntAdd`, and the operand is that operation and not a name.** The manifest holds `Base.Int.add` as an operation, and what the term carries is the operation alone: the entry it realizes is derived from it and written in one place, so nothing downstream can check one entry while running another. `Main` declares no foreign either — the entry is `Base.Int`'s, and that `Main` carries the operation out is recorded where lowering interns the use ([Bytecode](../05-Backend/01-Bytecode.md)).
- **`Main.sum ys` is emitted before `x` is read, because arguments are evaluated right to left** (D35). Nothing is visible here, `x` being a local and `Base.Int.add` a head that no binding names, but the order is what makes the fold on the line above sound.
- **`Main.sum ys` is not a tail call and `Base.Int.add` is.** The recursive call's value is an argument, so it is named; the addition stands at the function's `Dest` and so is emitted as `tail`.
- **The fields of `Main.Cons` are projected inside the branch that selected it**, and nowhere else.
- **`x : Int` needs the type of the occurrence.** A constructor's field types are written in terms of the owning declaration's parameters, so `Main.Cons`'s first field is `a`, and only `xs : List Int` makes it `Int`. Without that annotation both fields are `Val`, and the module is correct either way.
- **The `rec` group became a plain function entry.** `Main.sum` refers to itself by global name, so its capture list is empty and installing it evaluates nothing.
