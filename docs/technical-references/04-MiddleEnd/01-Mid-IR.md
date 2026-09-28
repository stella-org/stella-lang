# Mid IR

Mid IR is the backend-independent stage between Typed Core and a target. It is
an **A-normal form**: every intermediate result is named by a binding, every
argument is an atom, and every control construct stands in tail position.

Core defines what a program means. Mid IR fixes what a program *does*, in terms
every backend can carry out: allocating a closure, calling a known function,
building and taking apart a data value, jumping to a join point, installing a
handler, capturing a continuation. It commits to none of how a target
represents those things. JavaScript functions and objects, Wasm GC structs, and
layouts in linear memory belong past this stage and must not appear in it.

Bytecode is the lowering that consumes Mid IR ([Bytecode](../05-Backend/01-Bytecode.md)).
The JavaScript backend reads the `.dmo` that lowering produces rather than Mid IR
(D45, [JavaScript](../05-Backend/05-JavaScript.md)), and the WebAssembly backend's
input is fixed when that backend is designed. What this stage settles therefore
reaches JavaScript through the file, and a property that does not survive lowering
does not reach it at all.

## What Mid IR settles, and what it leaves open

| Settled here | Left to a backend |
| --- | --- |
| Which functions exist, and what each captures | How a closure is laid out |
| Where a call is known and where it is not | The calling convention |
| Which values are data, records, variants, closures, or opaque | How each is represented |
| Where control transfers, and whether a transfer is a jump or a call | Which machine construct realizes it |
| Which handler clause binds a continuation | How a continuation is captured |
| The order in which effects occur | Nothing; the order is normative |

## Representation types

Every binding in Mid IR carries a **representation type**, written `Rep`. A
`Rep` says which class of value flows through a binding. It is not a type in the
sense of Core: it has no rows, no quantifiers, no constraints, and no effect
row.

```text
Rep ::= Int | Number | Char | String | Boolean     the literal classes
      | Clos                                        anything callable
      | Rec                                         a record
      | Variant                                     a variant
      | Data T                                      a value of the data type T
      | Opaque                                      a value only a foreign observes
      | Val                                         unknown
```

The classes correspond one for one to the canonical-value classes `Σ` records
of an intrinsic type constructor ([Prim and Base](../06-Modules/02-Prim-and-Base.md)),
with two additions: `Data T` for a declared data type, which has constructors
rather than a canonical class, and `Val` for a position whose Core type is a
variable and so says nothing.

`Clos` covers every callable value alike: a closure, a partially applied
constructor or foreign, and a continuation a handler clause received. What
unites them is that applying one is the only thing to do with it.

`Rep Int` names a class and not a representation. What `Int` and `Number` range
over is fixed — a 32-bit signed integer and IEEE 754 binary64 (D37) — and how a
backend holds one is its own choice, which is what a descriptive `Rep` leaves it.

### The map from a Core type

`rep` is total on well-kinded types of kind `Type`.

```text
rep( Prim.Int )                     = Int            and likewise for the other literal types
rep( Prim.Function τ ρ σ )          = Clos
rep( Prim.Record ρ )                = Rec
rep( Prim.Variant ρ )               = Variant
rep( T τ̄ )   where T is a data entry of Σ        = Data T
rep( T τ̄ )   where T is intrinsic opaque         = Opaque
rep( forall (a : κ). τ )            = rep( τ )
rep( C => τ )                       = rep( τ )
rep( a τ̄ )                          = Val
```

A `forall` and a constraint arrow contribute nothing, because the abstractions
they type are erased and a value of such a type is a value of its body. Applying
a type variable leaves the head unknown, which is `Val`.

### A representation type is descriptive

**A `Rep` records what the Core type already said; it obliges a backend to
nothing.** Mid IR has no coercion node, and no instruction converts between
representation types. A backend that keeps one uniform representation ignores
`Rep` entirely. A backend that wants an unboxed `Int` or a Wasm GC struct per
data type reads `Rep` to decide where it may, and inserts whatever conversions
its own choice requires.

Making `Rep` prescriptive instead would mean deciding boxing in Mid IR, which is
a representation decision and therefore the one thing this stage exists not to
make.

## Names

```text
Local     a binding within one function; unique within that function
JoinName  a join point; unique within the function that binds it
FuncId    an entry of the module's function table
GlobalRef a fully qualified top-level value or foreign, as Core names it
CtorRef   a fully qualified data constructor
```

Locals are unique within a function rather than globally, so a backend may map
them onto a flat frame without renaming. Core's names are already unique up to
α-equivalence ([Kinds and Types](../03-Typed-Core/01-Kinds-and-Types.md)), and
translation preserves that.

**A `Local` and a `JoinId` are identities and not names.** Nothing compares one
for anything but equality, and a Core name reaching this stage carries no
meaning a backend needs, so translation issues them in sequence. The examples in
these documents write them as the source called them, which is legible and is
not what the representation holds.

## Atoms

An atom denotes a value without computing, allocating, or performing anything.
Atoms are what every other form takes as an argument, and that is the whole of
A-normal form.

```text
atom ::= local x                   a binding in scope
       | lit c                     a literal
       | global M.x                a top-level value, by reference
       | const M.Ctor              a constructor of arity 0
```

`global M.x` reads a top-level value that module initialization has already
stored, which is a load and not a call. **A foreign is never an atom**: a
foreign whose declared arity is 0 saturates as soon as its spine is formed and
therefore calls its implementation ([Semantics](../03-Typed-Core/06-Semantics.md)),
and one of arity `n > 0` referenced bare is a partial application.

`const M.Ctor` is a saturated constructor of arity 0, which allocates nothing
new: `Prim.Unit`, `Prelude.Nothing`, a `Nil`. A backend builds one value per
constructor per module and shares it.

## Computations

A computation is bound by a `let` or stands in tail position. It is the only
place an effect, an allocation, or a call occurs.

```text
comp ::= pure atom                                 name a value

       -- operations and calls
       | prim  op [ā]                             a `Base` ABI operation, saturated
       | callk M.x [ā]                             |ā| equals M.x's arity
       | callu a [ā]                               the callee is not known statically
       | ffi   M.f [ā]                             a saturated foreign; may fault
       | ctor  M.Ctor [ā]                          |ā| equals the constructor's arity
       | pap   callee [ā]                          0 ≤ |ā| < callee's arity
       | closure f [ā]                             allocate a closure over function f

       -- data
       | field a M.Ctor j                          the j-th field of a constructor value
       | payload k a                               what a variant carries at key k

       -- records
       | recEmpty
       | recExtend k a_value a_record     | recSelect k a
       | recRestrict k a                  | recUpdate k a_record a_value
       | recMerge a1 a2

       -- variants
       | inject k a          | absurd a

       -- effects
       | perform k.op a                            invoke an operation of the element keyed k
       | handle h f [ā] @ [v̄]                      install h and call the body
       | readCell k                                the cell keyed k of the innermost region
       | writeCell k a                             replace what that cell holds

callee ::= M.x | M.f | M.Ctor | prim op
```

**`handle` is a computation, and its body is a function of no parameters.** Its
value is what the handler's return clause produces, so binding it with a `let`
is all that is needed to use it, and no other form has to carry a destination
for it.

`[ā]` is what the body closure captures and `[v̄]` the initial value of each cell
of the handler's region, one per key of its `cells` and in that order. **The two
are separate fields because they are neither the same values nor evaluated at
the same time**: a capture list holds what the body names, so mixing the initial
values into it would have the body capture what it never names, and the initial
values are evaluated before the handler is installed while a capture list is
collected when the closure is built. `[v̄]` is empty for a handler declaring no
region; `[ā]` holds the body's free locals whether one is declared or not.

**A cell is reached by its key alone, and `writeCell` produces `Prim.Unit`.**
Neither form says which region: the innermost one declaring the key is the one
reached, and a write is done for its effect on that cell rather than for a result
of its own (D36). Which region that is is settled where the computation runs
rather than where it stands — a clause is a function of its own, so no scope
within a function says what frame is installed around it.

**`recExtend` and `recUpdate` take their operands the other way about**, as Core
writes them: the value first for one and the record first for the other
([Typing Rules](../03-Typed-Core/05-Typing-Rules.md)). The order is not a
spelling — it is the order the two are evaluated in, so an implementation that
reads either the wrong way about reverses the effects of the two operands.

### Calls

**A call whose callee and arity are both known statically is a different
instruction from one that is not.** `callk` names a top-level value whose
definitional arity — the number of leading lambdas its erased right-hand side
has — equals the number of arguments supplied. `ffi` and `ctor` are the same
case for a foreign and a constructor, whose arities come from their declarations.

`callu` covers everything else: applying a local, applying a closure, applying a
continuation, and supplying more arguments than a callee takes. It is where
under- and over-application are resolved, and a backend implements it once.

**Folding a spine into one call is sound because an application evaluates its
argument before its function** (D35). Every argument of a spine reaches a value
before any application happens, so one multi-argument call performs exactly what
the nested applications performed, in the same order. Under the opposite order
the evaluation of `f x` would stand between the arguments of `f x y`, and
whatever it performed would move.

What the known/unknown split buys is that `callk` is a transfer to an entry
point whose arity is settled — no arity test, no under- or over-application to
resolve — where `callu` needs all three. `pap` has to exist either way, so the
split costs no machinery that avoiding it would save.

### Partial application

`pap` is a value. A constructor or a foreign applied to fewer arguments than its
arity, and a known global applied to fewer than its definitional arity, produce
one; applying it produces either another `pap` or, once saturated, the call.

Retaining this form is what keeps a partially applied constructor representable
([Implementation Plan](../01-Introduction/04-Implementation-Plan.md)). A backend
lowers a `pap` to a curried function or to an object carrying the callee, the
arity, and the arguments collected so far, as it prefers.

### Primitive operations

**A `Base` ABI entry whose meaning the ABI fixes is an operation, not an
implementation.** A consumer carries one out directly rather than calling
something a backend supplied separately, which is what lets a machine add two
integers in its dispatch loop and a JavaScript backend emit `a + b` — neither of
them recognizing a qualified name to find out what it was handed.

What divides the two is what the name means rather than what it costs. A `Base`
entry returning no `IO` has a meaning the ABI fixes for every backend
([Prim and Base](../06-Modules/02-Prim-and-Base.md)), so naming the operation
loses nothing. A native leaf action returns `IO` and names an implementation, as
does an entry of a target namespace, whose meaning is one target's rather than
the ABI's; both stay `ffi`.

**Which entries are operations is the ABI manifest's to say**, fixed by an ABI
version alongside the surface and the profiles. Nothing in Core or in this stage
privileges a name of its own choosing.

**Whether an operation may fault is the ABI specification's to say as well**, and
is not read off the operation. The ABI fixes one observable meaning for every
backend: `stella-base-0.1` has `Base.Int.add` wrap, so a backend on a host that
traps on overflow owes the wrapping form, and it has the entries carrying an index
fault outside their range and `Base.Int.quot` fault on a zero divisor ([Prim and Base](../06-Modules/02-Prim-and-Base.md)). For an
entry the ABI has not yet fixed, a consumer treats the operation as one that may
fault ([Open Questions](../99-Open-Questions/01-Open-Questions.md)).

**An operation is how an entry is carried out, not a way of not using it.** A
backend still owes the entry at the profile that holds it, so a `.dmo` records
which entries its operations realize and target validation reads them
([Bytecode](../05-Backend/01-Bytecode.md)).

**An operation stays an operation through a partial application.** A `Base`
entry applied to fewer arguments than its arity produces a `pap` whose callee is
the operation, so saturating that `pap` carries the operation out. Were the
callee the qualified name instead, the same entry would run as an operation
where it was saturated at once and as an implementation where it was not, and a
backend supplying only what the ABI obliged it to would have nothing to call.

### Faults

`ffi` and `prim` are the computations that may produce a fault. A fault is not
an effect:
no handler intercepts it, it appears in no row, and it is not the `Partial`
effect ([Semantics](../03-Typed-Core/06-Semantics.md)). It propagates out of every
construct including a handler, and a backend implements it as an abrupt
termination of the whole reduction.

## Expressions

An expression is the body of a function, of a join point, or of a branch.
Control constructs stand in tail position only; a `case` whose value is consumed
by a surrounding context is expressed by binding that context as a join point
and jumping to it. A `handle` needs none of that, being a computation.

```text
expr ::= ret a                                     the value of the enclosing function
       | let x : Rep = comp in expr
       | letrec { x_i : Rep = closure f_i [ā_i] } in expr
       | letjoin j (x̄ : Rep) = expr in expr
       | jump j [ā]
       | tail comp                                 a computation in tail position
       | switchCtor a { M.Ctor_i -> expr_i } [ default -> expr ]
       | switchLit  a { c_i -> expr_i }   default -> expr
       | switchKey  a { k_i -> expr_i }   [ default -> expr ]
       | if a then expr else expr
```

`tail comp` is what makes a tail call visible: a backend reads it as an
obligation to transfer control rather than to push a frame. Whether it can
honour that obligation for a given target is the backend's affair, but Mid IR
never hides which calls are in tail position.

**`tail` carries no `Rep`.** A call returns its value and wants no register for
it, so for the calls this form exists to mark there is nothing to record. A
computation that is not a call does take a register on the way to returning, and
the class of that register has nowhere to come from: a consumer gives it `Val`,
which every consumer already handles and which costs precision rather than
correctness.

`if` is `guard` with its condition already named. Core's `guard` is the one
sequential test in a decision tree; every `switch*` is a single dispatch whose
branches are mutually exclusive and whose written order carries no meaning
([Terms and Matching](../03-Typed-Core/04-Terms-and-Matching.md)).

`switchLit` has a mandatory default and `switchCtor` and `switchKey` have one
unless their branches exhaust, exactly as in Core. **Mid IR does not re-derive
local totality; it preserves it.** The Core type checker established it, and a
verifier over Mid IR checks the syntactic condition and nothing more.

### Occurrences are gone

Core dispatches on an **occurrence**, a path from a scrutinee such as
`s0 ! Main.Cons . 1`. Mid IR dispatches on an atom, and every step of such a
path is an explicit `field`, `payload`, or `recSelect` bound by a `let`.

Making projections explicit is what lets a backend see each one, and it costs
nothing: an occurrence is a projection, has no effect, and may be named once and
referenced any number of times.

### Join points

`letjoin` and `jump` carry over from Core unchanged but for the loss of types.
A join point is not a value, forms no closure, is jumped to only from tail
position, and **does not cross a function boundary**. Translation preserves
those properties rather than establishing them, Core having required them
already.

A join point lowers to a named block and a `jump` to a transfer naming it. That
correspondence is the reason Core carries join points at all
([Terms and Matching](../03-Typed-Core/04-Terms-and-Matching.md)).

## Functions and closures

**Mid IR has no nested function.** Every lambda of Core, the body of every
`handle`, every handler clause, and every return clause becomes an entry of the
module's function table, and the free variables it needed become an explicit
capture list.

```text
Function ::= { id       : FuncId
             , params   : [ (Local, Rep) ]
             , captures : [ (Local, Rep) ]
             , body     : expr
             }
```

`closure f [ā]` allocates a value of the function `f` over the atoms `ā`, which
fill its captures in order. Applying that value binds the parameters and makes
the captures available.

Closure conversion happens here rather than in a backend because a target may
have no nested function to fall back on: Wasm has none, and a Wasm GC backend
must be handed the capture list rather than have to compute it. A backend with
nested functions, such as JavaScript, may ignore the capture list and let its
host close over the variables; the list stays correct either way.

`letrec` binds a group of closures that may capture one another. A backend
allocates every closure of the group before filling any capture list, which is
what a mutually recursive group requires. Guardedness (D14) is what makes this
safe: each right-hand side is a function value, so no capture is read while the
group is still being built.

**A top-level recursive group captures nothing.** Its members refer to one
another by global name, so each is a closure over an empty capture list
([Semantics](../03-Typed-Core/06-Semantics.md)).

## Handlers and continuations

```text
handle h f [ā] @ [v̄]

h ::= { key      : RowKey
      , cells    : [RowKey]
      , return   : ClauseRef
      , clauses  : [ { op : OpName, form : full | fast, clause : ClauseRef } ]
      }

ClauseRef ::= { func : FuncId, captures : [atom] }
```

**The handler carries the key alone.** Core's handler writes the row element
whole because typing needs its payload to say which operations the clauses must
exhaust; reduction consults `key(ent)` and nothing else, so erasure keeps the
key ([Semantics](../03-Typed-Core/06-Semantics.md)).

**A region is a frame of the continuation, not a store.** `cells` names the keys
a handler's region declares and `[v̄]` gives their initial values, one per key;
`readCell` and `writeCell` reach the innermost frame declaring the key, and a
write replaces what that frame holds (D36).

**A captured continuation carries the frame where the frame is inside it**, which
is where the handler capturing it was installed *outside* the region. Two
applications of such a continuation then begin from the same cell contents, and a
write under the first is invisible to the second. A backend implementing a cell
as a mutable location shared between resumptions would be non-conformant for
that reason, exactly as a one-shot continuation is.

Where the capturing handler is the one that owns the region, the frame stands
outside what it captured and the cells stay live across its resumptions. That is
the semantics, not a concession: a handler's cells are its state across the
operations it handles.

`cells` is empty for every handler that declares no region, and then no frame is
installed and the form is the one it always was.

### Everything a handler runs is a function

The body `f` is a function of no parameters, over the captures `[ā]`. So is each
clause, and so is the return clause: a clause is entered from a `perform` site
that lies at an arbitrary depth inside the body and in general in another
activation, and the return clause is entered when the body produces its value.
A `full` clause takes two parameters, the operation's argument and the
continuation; a `fast` clause and the return clause take one.

**The handler stands between the caller and the body, not inside either.**
Installing it and calling `f` is one step, and the value the whole `handle`
produces is what the return clause gives back. Three things follow, and each
would otherwise need a rule of its own.

**The result of a `handle` reaches its context by ordinary means.** It is the
value of a computation, so a `let` binds it. A body that instead ran in the
enclosing activation would have to say where the return clause's value goes,
and the return clause — being a function entered later — could not simply jump
to a join point of that activation to deliver it.

**Returning needs no special rule of the body's.** A function returns from its
activation; the handler is below the body's activation, so the body's return
reaches it, runs the return clause, and the return clause's own value goes on to
whatever called the `handle`. Where the handler declares no region that is the
whole of it, and it is `handle v with h → e_r[x := v]` read as a machine step.

**Where the handler owns a region, three paths reach a value and a consumer tells
them apart.** An installed handler closes its region before its return clause
runs, a handler a continuation reinstalled leaves the region of the one that owns
it open, and a `full` clause's answer reaches the region with no return clause
left to run. Mid IR fixes where the region stands and no more than that; which
path a value takes is what a lowering settles
([Bytecode](../05-Backend/01-Bytecode.md)).

**A tail call inside the body keeps the handler.** It replaces the body's
activation, which the handler does not stand in, so the path from wherever
control ends up back to the marker and its return clause is unchanged. The same
holds of a tail call inside a clause.

Join points do not enter a `handle`. A function boundary already discards them,
so this is a consequence of the shape above rather than a restriction Mid IR
imposes; Core discards the join point context at a `handle` for the same reason.

### The two clause forms stay apart

`full` and `fast` are recorded on every clause, as Core records them (D28).
They carry no type information; what they say is which reduction applies, and a
backend lowers them differently.

| Form | What the backend does |
| --- | --- |
| `fast` | Call the clause with the operation's argument, the handler still installed. Control returns to the `perform` with the clause's value. **No continuation is constructed** |
| `full` | Capture the continuation up to and including this handler, call the clause with the argument and that continuation. The clause's value is the value of the `handle` |

**A `fast` clause is the reason the two are kept apart.** Implementing one asks
nothing of a backend beyond an ordinary call, so the cost of a continuation is
reserved for `full` alone.

### Continuations are not one-shot

**Nothing in Mid IR bounds how often a continuation may be applied.** A
continuation is a value of `Rep Clos`, applied by `callu` like any other, and no
form marks it or counts its uses.

This is a constraint on the representation and not merely an omission. Mid IR is
designed before effect lowering is written ([Implementation Plan](../01-Introduction/04-Implementation-Plan.md)),
so a representation admitting only one resumption would settle D18 by accident,
in a stage that has no standing to settle it. A backend whose continuations are
one-shot is non-conforming and says so; Mid IR records no such limitation on its
behalf.

## Modules

```text
MidModule ::= { name      : ModuleName
              , imports   : [ModuleName]
              , ctors     : [ { ref : CtorRef, owner : TyName, tag : Int, arity : Int
                             , isNewtype : Boolean } ]
              , effects   : [ { ref : QEffName, ops : [OpName] } ]
              , foreigns  : [ { ref : GlobalRef, arity : Int } ]
              , functions : [Function]
              , globals   : [ { ref : GlobalRef, init : GlobalInit } ]
              , exports   : [GlobalRef]
              }

GlobalInit ::= run  FuncId        evaluate a function of no parameters and store the result
             | func FuncId        store a closure over an empty capture list
```

The constructor table is what survives of the data declarations: a tag, an
arity, the type that owns them, and whether that type is a `newtype`. Field
types do not survive, `Rep` on each binding carrying what a backend needs of
them.

**`isNewtype` is carried because nothing else recovers it.** A `newtype` is one
constructor of one field, which an ordinary data declaration may also be, so a
backend that erases the representation cannot tell the two apart from the shape
of the table. Mid IR is all that `lower` receives, so the flag has to reach it
here or it reaches no backend at all. The Core type checker is what verified the
shape the flag claims ([Modules](../06-Modules/01-Modules.md)), so nothing
downstream re-checks it.

The effect table records which operations each effect declares. No signature
survives: an operation's argument and resume types were consumed by type
checking.

**A `perform` and a handler clause name an operation by its own name alone**,
and the effect it belongs to appears in neither. A `perform` finds its handler
by key, and a handler's clauses are the operations of exactly one effect, so the
name cannot be ambiguous where it is looked up. A row key is likewise compared
for equality and nothing else. Both are interned, so that a backend compares
integers rather than strings.

Identifying an operation this way is what keeps translation from needing the
ambient effect row: the row is erased, and the key at a `perform` site does not
by itself say which effect the element carries.

**`globals` is an ordered list, and the order is the dependency order Core
required.** Evaluating eagerly in declaration order is observable, a divergent
right-hand side hanging initialization whether or not anything refers to it, and
Mid IR preserves that rather than deferring to first reference
([Semantics](../03-Typed-Core/06-Semantics.md)).

**Which entry a value gets is decided by the shape of its right-hand side and
not by the form of its declaration.** A right-hand side that is a lambda once
erasure has looked through the wrappers becomes that function, installed as a
`func`: at the top level every free name is a global, so there is nothing to
capture and nothing to evaluate. Anything else becomes a `run`, evaluated once.
A member of a top-level `rec` group is a function value and therefore always a
`func`; a `nonrec` is one or the other according to what it holds.

This is the same test the **definitional arity** is read by, and the two have to
agree. A `nonrec` holding a lambda has a definitional arity, so a call to it is
`callk`; were it installed as a `run` instead, the global reached by that
`callk` would be the result of evaluating a thunk rather than the function whose
arity the call supplied. Reading one property off the declaration and the other
off the term is what lets them disagree.

## The debug table

A `.dmo` carries source spans, function names, and local names in a `DEBUG`
section that a consumer may strip ([Bytecode](../05-Backend/01-Bytecode.md)).
Nothing in the terms above holds any of it, so translation produces a **side
table** beside the module and `lower` reads both.

```text
Debug ::= { functions : FuncId ⇀ { name : QIdent?, source : span? }
          , locals    : FuncId ⇀ ( Local ⇀ Ident )
          }
```

**A local is named within its function**, a `Local` being unique within one and
not beyond it. Nothing but a function and a local together identifies a binding,
so the table is keyed by both.

Three things decide what a name means here.

**A function's `name` is the global it is installed from**, and a lambda lifted
out of a body has none.

**A function's `source` is the term the function was made from** — the node as it
stands, wrappers included. Not the body left once the lambdas come off, which
would put the span at the first expression rather than at the definition; and
not the lambda left once the wrappers come off, which would start it inside what
it belongs to. A translation looks through the wrappers to find the lambda and
keeps the outer node for this.

**A local is named where one was created for a name.** A `let` whose right-hand
side is already an atom binds an alias and makes no local, so `let z = y` leaves
`y`'s own name in place rather than renaming it, and a pattern binding an
occurrence an earlier one already materialized aliases that local the same way.
A local holding an intermediate result of a folded spine, or a projection no
pattern gave a name to, was created for no name at all.

**It is a side table and not an annotation on the terms.** A Mid IR node has no
identity of its own, and most nodes come from no single Core node: one
application folds a whole spine, and a projection is emitted where a branch
first needs it. A function and a local do have identities, and those are what
can be named.

A span finer than a function therefore has nowhere to go. **Instruction-level
spans, which a source map wants, would need Mid IR nodes to carry identities**,
and nothing here gives them one; that is open.

The table is the one part of Mid IR a consumer may discard, and nothing about
the module depends on it.

## What Mid IR does not have

Each of the following is present in Core and absent here. The right-hand column
says what became of it.

| Absent | Where it went |
| --- | --- |
| Types, kinds, rows, constraints | `Rep` on each binding; everything else was consumed by type checking |
| `Λ`, `e [τ]`, `e [•]`, `T [[κ̄]]`, `M.x [[κ̄]]` | Erased |
| `openEff`, `openEffC` | Erased. Both are the identity at run time |
| `weaken` | Erased. A `switchKey` dispatches on the key a variant actually carries |
| Occurrences | Explicit `field`, `payload`, and `recSelect` bindings |
| Nested lambdas | The function table, with explicit captures |
| `fail` | It was never a node: Core writes `perform Partial.abort`, and translation carries that through |
| The payload of a handled row element | The handler's key |
| Curried application chains | `callk`, `callu`, `ffi`, `ctor`, and `pap` |

## Invariants

**A lowering verifies these rather than accommodating a breach**, because the
numbering is what it reads: a register is a local's number, and a function is
reached by its place in the table. A gap displaces every slot after it, a
parameter out of place has the caller write one slot and the body read another,
and an entry out of place is reached under another's name. Filling a hole would
produce a module that runs and computes something else.

None of it re-derives anything the Core type checker established; each is a
property translation is obliged to produce and a later pass is obliged to
preserve.

### What the representation already holds

Four of them need no check, there being no term of Mid IR in which they fail:
every argument of every computation is an atom, every branch of every `switch*`
and `if` ends in a transfer, `switchLit` has a default, and a `jump` stands in
tail position.

### What a verifier checks

**The function table.** Each function stands at its own identifier, so the table
is `0 … n-1` and holds no identifier twice. Every global names a function the
table holds, and that function takes no captures — initialization installs one
over an empty capture list — and takes no parameters where initialization
evaluates it.

**Join points.** Every `jump` names a join point of an enclosing scope in the
same function and supplies the number of arguments that join point takes. A join
point is in scope in its own definition, which is what lets one stand for a
loop, and is declared once in a function: scope alone would let an inner one
shadow an outer, but a lowering puts them in one flat table, so a second
declaration would leave a jump with two destinations. Nothing requires the
numbering to be dense.

**Registers.** No local is bound twice in one function. The locals are numbered
`0 … n-1` without a gap, the parameters first and the captures immediately after
them, each in declaration order. Every local a term reads is bound at the point
that reads it: one never bound and one bound in a branch that does not enclose
the read are both rejected, and the second passes every check of layout alone.

**Functions a term names.** Every `closure`, `letrec` binding, `handle` body,
and handler clause names a function of the table and supplies exactly the
captures that function takes. Each function a handler reaches has the arity its
form gives it: none for the body, two for a `full` clause, one for a `fast`
clause and for the return clause. A handler names no operation twice and no cell
key twice, and a `handle` supplies one initial value per key of its `cells` — a
lowering pairs the two by position, so a count that disagrees leaves a cell
holding another's value.

**Arities and fields.** A saturated `prim` supplies the arity the ABI manifest
fixes, and a `pap` over one supplies fewer. A saturated `callk`, `ctor`, or
`ffi` naming something **this module declares** supplies that declaration's
arity, and a `pap` over one supplies fewer. A `callk`, and a `pap` over a
top-level value, names a global installed as a function rather than one
evaluated at initialization, an absent definitional arity not being zero. A
`field` names a field the constructor has.

**Dispatch.** A `switchCtor`'s branches name constructors of one type, each
once, and where there is no default they leave no constructor of that type
without a destination.

### What one module cannot decide

The arity of a constructor, foreign, or global **another module declares** is
that module's to state, and a `.dmo` deliberately carries no copy of it
([Bytecode](../05-Backend/01-Bytecode.md)). Those references are checked where
the modules are together, which is what a loader does. Everything a module does
declare is checked here.

**That check is also what a wrong `.dmi` runs into.** A `callk` is a transfer to an
entry point whose arity is settled, and the arity a translation used for an
imported value came from that module's interface file; a loader reading the
declaring module's own entry against the call is what turns a stale interface into a
rejected build rather than a call that supplies the wrong number of arguments
([Interface](../05-Backend/03-Interface.md)).

That a `readCell` or a `writeCell` names a key of the region it reaches is not
checked here either, and not for want of the declaration: the region is the one a
walk of the continuation finds, and the function the form stands in says nothing
about what frame is installed around it. The Core type checker established it
while the row still carried the region ([Typing Rules](../03-Typed-Core/05-Typing-Rules.md)).

That a handler's clauses **exhaust** the operations of the effect its element
carried is not checked at all. The element's payload is what said which
operations those are, and it was erased; the Core type checker established
exhaustiveness while the payload was still there ([Typing Rules](../03-Typed-Core/05-Typing-Rules.md)).
