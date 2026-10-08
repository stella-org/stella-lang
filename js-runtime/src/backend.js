// What code the JavaScript backend generates runs on.
//
// A Stella function is generated as a set of *segments*: an entry segment, and one
// for what follows each non-tail call, perform, handler installation, and region
// opening. A segment
// runs to the next of those and returns a code saying what the run loop does next,
// so the host's call stack never holds more than one segment. Activations live in
// frames on a stack of the runtime's own, which is what lets a tail call push
// nothing, a deep recursion run in bounded host stack, and a continuation be a run
// of that stack taken off and re-pushed.
//
// Values are held as follows. The representation is this runtime's own and is not
// a published ABI.
//
//   Int, Number        a JavaScript number
//   Char               the number of a Unicode scalar value
//   String, Boolean    a JavaScript string, a JavaScript boolean
//   data               a `Data`, whose `c` is the constructor's descriptor object
//   record             an object keyed by a key's canonical string
//   variant            a `Variant`
//   closure            a `Closure` over a function descriptor
//   partial app        a `Pap`
//   continuation       a `Continuation`
//   IO                 an `IOPure`, an `IOBind`, or an `IONative`
//   region identity    a `RegionId`
//   opaque             the host value itself

import { refusalReason } from "./interpreter.js";

// The codes a segment returns --------------------------------------------------

// `m.value` holds a value for the entry below.
export const RET = 0;
// Call `m.callee` with `m.args`; the value goes into register `m.dest` of the
// current frame, which then continues at segment `m.resume`.
export const CALL = 1;
// The same, replacing the current frame and pushing nothing.
export const TAIL = 2;
// Continue the current frame at segment `m.seg`.
export const RUN = 3;
// Perform operation `m.op` of the effect keyed `m.key` with the argument `m.value`;
// the value it gives goes into register `m.dest`, and the frame continues at
// `m.resume`.
export const PERF = 4;
// Install the handler `m.handler` with the return clause `m.ret` and the operation
// clauses `m.args`, and call the body `m.callee`; the value goes into register
// `m.dest`, and the frame continues at `m.resume`.
export const HNDL = 5;
// The same in tail position, pushing nothing for the current frame.
export const TAILHNDL = 6;
// Open the region `m.region` with the initial cell values `m.cells`, and call the
// body `m.callee` with the region's identity; the value goes into register
// `m.dest`, and the frame continues at `m.resume`.
export const RGN = 7;
// The same in tail position, pushing nothing for the current frame.
export const TAILRGN = 8;

// Values ------------------------------------------------------------------------

export class Closure {
  constructor(fn, caps) {
    this.fn = fn;
    this.caps = caps;
  }
}

// A callee applied below its arity, with the arguments collected so far.
export class Pap {
  constructor(callee, args) {
    this.callee = callee;
    this.args = args;
  }
}

export class Data {
  constructor(c, f) {
    this.c = c;
    this.f = f;
  }
}

export class Variant {
  constructor(k, v) {
    this.k = k;
    this.v = v;
  }
}

// The identity of one opening of a region, unequal to every other opening's, which
// the copies a continuation makes of the region's frame keep. A cell is reached by
// an identity and a position, and the frame it is in is the innermost of that
// identity on the stack.
export class RegionId {}

// A captured run of stack entries, from the frame that performed an operation up to
// and including the marker that answered it. The last entry is the top, so index 0
// is that marker. It takes one argument, the value the perform gives.
//
// The captured entries are never the ones that run: each application re-pushes a
// copy of them (`reinstate`), so a continuation may be applied any number of times
// and each application proceeds from the state that was captured (D33).
export class Continuation {
  constructor(entries) {
    this.entries = entries;
  }
}

// A state no well-formed `.dmo` admits: a defect in this runtime, in the code
// generator, or in the stages before it. It is not a Stella fault.
export class Bug extends Error {
  constructor(message) {
    super(message);
    this.name = "StellaBug";
  }
}

const bug = (message) => {
  throw new Bug(message);
};

// A failure the ABI admits: an operation failing on an input it is specified to
// fail on, or a foreign failing at the boundary. It is not an effect — no handler
// intercepts one — and it discards the whole run. `global` names the global being
// initialized when one ends a module's initialization.
//
// `kind` says where it arose: `operation` for an operation of the ABI, and for the
// boundary one of `refused`, `threw`, `breached` (a foreign) or `actionRefused`,
// `actionThrew`, `actionBreached` (an action a foreign returned, as it is
// performed). `foreign` names the foreign, where the kind carries one, and `detail`
// is the reason a refusal gave, the message a throw carried, or what a breach was.
export class Fault extends Error {
  constructor(message, kind = "operation", foreign = undefined, detail = undefined) {
    super(message);
    this.name = "StellaFault";
    this.global = undefined;
    this.kind = kind;
    this.foreign = foreign;
    this.detail = detail;
  }
}

const fault = (message) => {
  throw new Fault(message);
};

// An entry point that holds no action: the program does not start. Any global of a
// well-formed module can be named as the entry, so this is neither a fault, which
// ends a run that began, nor a bug.
export class StartFailure extends Error {
  constructor(entry) {
    super(`the entry point ${entry} holds no action`);
    this.name = "StellaStartFailure";
    this.entry = entry;
  }
}

// Descriptors -------------------------------------------------------------------

// A function of the function table: its arity, how many registers a frame of it
// holds, and the segment it is entered at.
export const fn = (name, arity, nregs, entry) => ({ kind: "fn", name, arity, nregs, entry });

// A data constructor. **Its identity is this object**: the declaring module creates
// it and every other module imports it, so dispatch compares references and never a
// tag, which is only unique within one type. A constructor of arity 0 allocates
// nothing new, so its one value is created with it.
export const ctor = (name, arity) => {
  const c = { kind: "ctor", name, arity };
  if (arity === 0) c.value = new Data(c, []);
  return c;
};

// A handler of the handler table: the key of the effect it answers, and its
// operation clauses in the order a `HNDL` supplies them, each `[op, fast]` with
// `fast` true for a `fast` clause.
export const handler = (key, clauses) => ({
  key,
  clauses: clauses.map(([op, fast]) => ({ op, fast })),
});

// A region of the region table: the key of each of its cells, in the order of their
// positions.
export const region = (cells) => ({ cells });

// A `Base` operation standing as a callee, for a partial application of it.
export const prim = (name, arity, apply) => ({ kind: "prim", name, arity, apply });

// `Prim.Unit`, which no module declares and every module may name.
export const PrimUnit = ctor("Prim.Unit", 0);

// Foreigns ---------------------------------------------------------------------------
//
// A foreign that is not an operation is a descriptor `{kind: "foreign", name, arity,
// call}`, `call` taking the arguments as an array. Its body is synchronous and applies
// no Stella function, so a call is an expression of the segment it stands in.

// `Base.IO.pure` and `Base.IO.bind`, which the runtime carries out itself. Each
// constructs, and neither runs anything (D25).
export const ioPure = { kind: "foreign", name: "Base.IO.pure", arity: 1, call: ([value]) => new IOPure(value) };

export const ioBind = {
  kind: "foreign",
  name: "Base.IO.bind",
  arity: 2,
  call: ([io, k]) => {
    if (!isIO(io)) bug("Base.IO.bind given what is not an IO");
    return new IOBind(io, k);
  },
};

// The result kind of a foreign returning an action producing a value of `kind`.
export const action = (kind) => ({ action: kind });

// A foreign a host implements, reached through the declaring module's manifest
// entry: the implementation, the kind of each parameter, and the kind of the result,
// as the manifest spells them. The arity is the number of parameters. Only the
// declaring module creates one; every other module imports it.
//
// **The export must be callable**, the one shape of it that can be checked, and it
// is checked as the declaring module is loaded.
export const foreign = (name, impl, params, result) => {
  if (typeof impl !== "function") bug(`the implementation of ${name} is not callable`);
  return { kind: "foreign", name, arity: params.length, call: (args) => hosted(name, impl, params, result, args) };
};

// A call of a foreign declared elsewhere supplies the arity its declaration states,
// and a partial application of one fewer; either is checked as the calling module is
// loaded.
export const expectForeignCall = (desc, count) => {
  if (count !== desc.arity) bug(`${desc.name} is called with ${count} argument(s) but is declared at arity ${desc.arity}`);
};

export const expectForeignPartial = (desc, count) => {
  if (count >= desc.arity) {
    bug(`${desc.name} is partially applied to ${count} argument(s) but is declared at arity ${desc.arity}`);
  }
};

export const callForeign = (desc, args) => desc.call(args);

// Calling a hosted foreign: each argument unwrapped by the kind of its position, the
// host function called, and what it returned wrapped by the result kind.
//
// **Only the host function's call is inside the `try`.** Whatever it throws is its
// throw, a runtime `Fault` or `Bug` included, so a host cannot pass itself off as the
// runtime; the marshalling around it is the runtime's, and what it throws is not.
const hosted = (name, impl, params, result, args) => {
  const given = args.map((v, i) => unwrap(params[i], v));
  let answered;
  try {
    answered = impl(...given);
  } catch (e) {
    throw boundaryFault("threw", name, thrownMessage(e));
  }
  const reason = refusalReason(answered);
  if (reason !== undefined) throw boundaryFault("refused", name, reason);
  if (typeof result === "object") {
    // the host returns the action and constructs no `IO` value
    if (typeof answered !== "function") throw boundaryFault("breached", name, "declared an action, and the value is not a function");
    return new IONative(name, answered, result.action);
  }
  const wrapped = wrap(result, answered);
  if (wrapped.breach !== undefined) throw boundaryFault("breached", name, wrapped.breach);
  return wrapped.value;
};

// A value as the host sees it. A `char` is a string of its one scalar value, and a
// `unit` parameter keeps its place and is not read: the host sees `undefined` there.
const unwrap = (kind, value) => {
  switch (kind) {
    case "char":
      return String.fromCodePoint(value);
    case "unit":
      return undefined;
    default:
      return value;
  }
};

const MIN_INT32 = -2147483648;
const MAX_INT32 = 2147483647;

// A host value as a Stella value of the kind it is owed as, by the kind and not by
// the value: a whole number owed as a `number` stays one. **Wrapping is a check**:
// what does not fit is `{breach}`, saying why.
const wrap = (kind, value) => {
  const owing = (why) => ({ breach: `declared \`${kind}\`, and the value is ${why}` });
  switch (kind) {
    case "int":
      if (typeof value !== "number") return owing("not a number");
      // `| 0` takes `-0` to `0`, an `Int` having one zero
      if (!Number.isInteger(value) || value < MIN_INT32 || value > MAX_INT32) return owing("not a whole number within 32 bits");
      return { value: value | 0 };
    case "number":
      return typeof value === "number" ? { value } : owing("not a number");
    case "char": {
      if (typeof value !== "string") return owing("not a string");
      if (!value.isWellFormed()) return owing("a string holding an unpaired surrogate");
      const scalars = Array.from(value);
      return scalars.length === 1 ? { value: scalars[0].codePointAt(0) } : owing("not one scalar value");
    }
    case "string":
      if (typeof value !== "string") return owing("not a string");
      return value.isWellFormed() ? { value } : owing("a string holding an unpaired surrogate");
    case "boolean":
      return typeof value === "boolean" ? { value } : owing("not a boolean");
    // nothing of the host value is read
    case "unit":
      return { value: PrimUnit.value };
    case "opaque":
      return { value };
    default:
      return bug(`no value kind ${kind}`);
  }
};

const boundaryFault = (kind, name, detail) => {
  const where = name === undefined ? "an action" : name;
  return new Fault(`${where}: ${kind}: ${detail}`, kind, name, detail);
};

const thrownMessage = (e) => (e instanceof Error ? e.message : String(e));

// IO --------------------------------------------------------------------------------
//
// Reduction halts once it has constructed an `IO` value (D25); executing one is a
// second entry point, and nothing in a segment reaches it.

export class IOPure {
  constructor(value) {
    this.value = value;
  }
}

export class IOBind {
  constructor(io, k) {
    this.io = io;
    this.k = k;
  }
}

// An action a hosted foreign returned: the foreign's name, the host function of no
// arguments that performs it, and the kind what it produces is owed as.
export class IONative {
  constructor(foreign, perform, kind) {
    this.foreign = foreign;
    this.perform = perform;
    this.kind = kind;
  }
}

const isIO = (v) => v instanceof IOPure || v instanceof IOBind || v instanceof IONative;

// Run an `IO` to the value it produces.
//
// **The loop is iterative and holds its own stack of pending functions.** A chain
// has no bound and the shape a program builds is left-nested, so the outermost
// `Bind` stands above every other. Applying a pending function is a run of its own
// (`applyFunction`), finished before the loop goes round again.
export const execute = (initial) => {
  const pending = [];
  let io = initial;
  for (;;) {
    while (io instanceof IOBind) {
      pending.push(io.k);
      io = io.io;
    }
    let value;
    if (io instanceof IOPure) value = io.value;
    else if (io instanceof IONative) value = performAction(io);
    else bug("executing what is not an IO");
    if (pending.length === 0) return value;
    io = applyFunction(pending.pop(), [value]);
    // `k` has type `a -> IO b`, and a `.dmo` carries no type to hold it to that
    if (!isIO(io)) bug("the function of a bind returned what is not an IO");
  }
};

// Perform an action: call the host function, and wrap what it produced by the kind
// it was declared with. Only the call is inside the `try`, as with a foreign.
const performAction = (n) => {
  let produced;
  try {
    produced = n.perform();
  } catch (e) {
    throw boundaryFault("actionThrew", undefined, thrownMessage(e));
  }
  const reason = refusalReason(produced);
  if (reason !== undefined) throw boundaryFault("actionRefused", undefined, reason);
  const wrapped = wrap(n.kind, produced);
  if (wrapped.breach !== undefined) throw boundaryFault("actionBreached", n.foreign, wrapped.breach);
  return wrapped.value;
};

// Execute the action the entry point holds, named `entry`. A value that is not an
// action is a program that does not start.
export const runMain = (entry, value) => {
  if (!isIO(value)) throw new StartFailure(entry);
  return execute(value);
};

// Checks a module makes of what it imports ----------------------------------------

// A module's own table of definitional arities, keyed by the unqualified name of
// each global installed as a function. A global evaluated at initialization has
// none and is absent.
export const arityOf = (table, name) =>
  Object.prototype.hasOwnProperty.call(table, name) ? table[name] : undefined;

// A known call is a transfer to an entry whose arity is settled, so a call
// supplying another count, or one reaching a global with no definitional arity, is
// refused where the module is loaded rather than where the call runs.
export const expectCall = (table, module, name, count) => {
  const arity = arityOf(table, name);
  if (arity !== count) {
    bug(`${module}.${name} is called with ${count} argument(s) but its definitional arity is ${arity ?? "absent"}`);
  }
};

// A partial application supplies fewer arguments than its callee takes.
export const expectPartial = (table, module, name, count) => {
  const arity = arityOf(table, name);
  if (arity === undefined || count >= arity) {
    bug(`${module}.${name} is partially applied to ${count} argument(s) but its definitional arity is ${arity ?? "absent"}`);
  }
};

export const expectCtor = (c, count, saturated) => {
  if (saturated ? count !== c.arity : count >= c.arity) {
    bug(`${c.name} takes ${c.arity} field(s) and is given ${count}`);
  }
};

// Stack entries -------------------------------------------------------------------

// Write the value into register `dest` of `frame` and continue it at `seg`.
class Resume {
  constructor(frame, dest, seg) {
    this.frame = frame;
    this.dest = dest;
    this.seg = seg;
  }
}

// Apply the value to `args`. An over-application leaves one behind, and so does a
// continuation applied to more than one argument.
class ApplyRemaining {
  constructor(args) {
    this.args = args;
  }
}

// An installed handler: the key it answers, a clause per operation name, and the
// return clause every value passes through.
class Marker {
  constructor(key, clauses, ret) {
    this.key = key;
    this.clauses = clauses;
    this.ret = ret;
  }
}

// An open region: its identity, and what its cells hold, by position. It is part of
// the stack and not a store, so a captured segment carries the values its cells held
// at the capture, and each application of the continuation starts from those.
class Region {
  constructor(id, cells) {
    this.id = id;
    this.cells = cells;
  }
}

// Where a `fast` clause's body begins. Core binds that body outside the handler
// that answered and outside everything between that handler and the `perform`
// (D28), so a search for a marker or a region that reaches this entry continues
// directly below that handler's marker, which stands `dist` entries further down.
//
// The distance is relative, not a position: a `full` operation the body performs
// may capture a segment holding this entry and re-push it anywhere, and the
// handler's marker travels in the same segment. A value reaching it passes down
// unchanged.
class Boundary {
  constructor(dist) {
    this.dist = dist;
  }
}

// The machine ---------------------------------------------------------------------

// One run: its stack, the frame running, and the registers segments talk to the run
// loop through.
export class Machine {
  constructor() {
    this.stack = [];
    this.frame = null;
    this.seg = null;
    this.value = undefined;
    this.callee = undefined;
    this.args = undefined;
    this.dest = 0;
    this.resume = null;
    this.key = undefined;
    this.op = undefined;
    this.handler = undefined;
    this.ret = undefined;
    this.region = undefined;
    this.cells = undefined;
  }
}

// The first entry, from the top down, at which `test` answers with something, with
// where it stands.
//
// **A `Boundary` is jumped over, together with everything below it down to and
// including the marker of the handler whose `fast` clause is running**: the walk
// continues directly below that marker, so what stood between the handler and the
// `perform` is not seen, while what stands below the marker is. A marker search and
// a region search read the stack by this one walk, which is what keeps a perform
// and a cell access reaching the same context.
const visible = (stack, test) => {
  for (let i = stack.length - 1; i >= 0; ) {
    const e = stack[i];
    if (e instanceof Boundary) {
      i -= e.dist + 1;
      continue;
    }
    const found = test(e);
    if (found !== undefined) return { at: i, found };
    i--;
  }
  return undefined;
};

// The region whose identity is `id`, with a cell at position `i`: the innermost
// visible frame of the identity. Copies of one opening share its identity, and the
// innermost is the one the running code belongs to.
const regionOf = (m, id, i) => {
  if (!(id instanceof RegionId)) bug("a cell reached through what is no region's identity");
  const hit = visible(m.stack, (e) => (e instanceof Region && e.id === id ? e : undefined));
  if (hit === undefined) bug("a cell of a region no longer open");
  if (!(i >= 0 && i < hit.found.cells.length)) bug(`a region has no cell ${i}`);
  return hit.found;
};

// The entries one application of a continuation pushes.
//
// What a segment holds that an application can change is the register array of
// each frame in it and the cell slots of each region, so each is copied, holding
// what it held at the capture; copying the array of entries alone would leave every
// application sharing them, and the second would begin where the first stopped.
// This relies on a frame being referred to by nothing but the one `Resume` holding
// it and, while it runs, `m.frame`. The values those slots hold are shared, never
// copied: an application reads the same value whichever copy holds it, and a value
// written into in place, such as an array, is one value before the capture and
// after.
//
// **A region frame's copy keeps the identity of the frame it copies.** The code the
// segment holds names its regions by identity, and so does every closure made before
// the capture, so each copy is what they reach while it runs. A region standing below
// the marker the segment ends at is not in the segment: the capture leaves it where
// it is, and every application shares its cells.
const reinstate = (entries) =>
  entries.map((e) => {
    if (e instanceof Resume) return new Resume({ caps: e.frame.caps, r: e.frame.r.slice() }, e.dest, e.seg);
    if (e instanceof Region) return new Region(e.id, e.cells.slice());
    return e;
  });

// Install a handler and call its body, the marker standing between them.
const install = (m) => {
  const h = m.handler;
  const clauseValues = m.args;
  if (clauseValues.length !== h.clauses.length) {
    bug(`the handler of ${h.key} installed with ${clauseValues.length} clause(s)`);
  }
  const clauses = new Map(h.clauses.map((c, i) => [c.op, { fast: c.fast, clause: clauseValues[i] }]));
  m.stack.push(new Marker(h.key, clauses, m.ret));
  return apply(m, m.callee, []);
};

// Open a region and call its body with the region's identity, one no other opening
// has had, the region's frame standing between them.
const open = (m) => {
  const initial = m.cells;
  if (initial.length !== m.region.cells.length) {
    bug(`a region of ${m.region.cells.length} cell(s) opened with ${initial.length} value(s)`);
  }
  const id = new RegionId();
  m.stack.push(new Region(id, initial.slice()));
  return apply(m, m.callee, [id]);
};

// Perform an operation: the innermost visible marker of the key answers, and the
// form of its clause for the operation decides how (D28).
const perform = (m) => {
  const arg = m.value;
  const hit = visible(m.stack, (e) => (e instanceof Marker && e.key === m.key ? e : undefined));
  if (hit === undefined) bug(`no handler of ${m.key} is installed`);
  const clause = hit.found.clauses.get(m.op);
  if (clause === undefined) bug(`the handler of ${m.key} has no clause for ${m.op}`);
  if (clause.fast) {
    // the clause returns to the perform with its value, its body running outside
    // the handler and outside what stands above it; the distance is measured from
    // where the boundary stands, above the `Resume` just pushed
    m.stack.push(new Boundary(m.stack.length - hit.at));
    return apply(m, clause.clause, [arg]);
  }
  // the continuation begins at the perform, so the frame's `Resume` is part of it
  const segment = m.stack.splice(hit.at);
  return apply(m, clause.clause, [arg, new Continuation(segment)]);
};

// Apply a value to arguments, entering a frame or producing a value.
//
// **The count decides before the kind does.** Too few arguments build a partial
// application, whatever the callee; too many call it with the arity it takes and
// leave the rest for what comes back.
const apply = (m, callee, args) => {
  for (;;) {
    if (callee instanceof Closure) {
      const f = callee.fn;
      const n = f.arity;
      if (args.length < n) {
        m.value = new Pap(callee, args);
        return RET;
      }
      if (args.length > n) {
        m.stack.push(new ApplyRemaining(args.slice(n)));
        args = args.slice(0, n);
      }
      const r = new Array(f.nregs);
      for (let i = 0; i < n; i++) r[i] = args[i];
      m.frame = { caps: callee.caps, r };
      m.seg = f.entry;
      return RUN;
    }
    if (callee instanceof Pap) {
      // the arguments a partial application holds stand before the ones it is given
      args = callee.args.concat(args);
      callee = callee.callee;
      continue;
    }
    // the segment is re-pushed and the first argument reaches its top, the frame
    // that performed; the rest is work pending on what the segment returns, so it
    // stands below
    if (callee instanceof Continuation) {
      if (args.length === 0) bug("a continuation applied to nothing");
      if (args.length > 1) m.stack.push(new ApplyRemaining(args.slice(1)));
      for (const e of reinstate(callee.entries)) m.stack.push(e);
      m.value = args[0];
      return RET;
    }
    if (callee === null || typeof callee !== "object") bug("applying what is not callable");
    switch (callee.kind) {
      case "ctor": {
        if (args.length < callee.arity) {
          m.value = new Pap(callee, args);
          return RET;
        }
        // a saturated constructor is a completed structure, so over-applying one does
        // not arise
        if (args.length > callee.arity) bug(`${callee.name} applied to more than its arity`);
        m.value = callee.arity === 0 ? callee.value : new Data(callee, args);
        return RET;
      }
      case "prim":
      case "foreign": {
        const n = callee.arity;
        if (args.length < n) {
          m.value = new Pap(callee, args);
          return RET;
        }
        if (args.length > n) {
          m.stack.push(new ApplyRemaining(args.slice(n)));
          args = args.slice(0, n);
        }
        m.value = callee.kind === "prim" ? callee.apply(...args) : callee.call(args);
        return RET;
      }
      default:
        bug("applying what is not callable");
    }
  }
};

// Run until the stack is empty, and answer with the value the run produced.
const run = (m, code) => {
  for (;;) {
    switch (code) {
      case RUN:
        code = m.seg(m, m.frame);
        break;
      case CALL:
        m.stack.push(new Resume(m.frame, m.dest, m.resume));
        code = apply(m, m.callee, m.args);
        break;
      case TAIL:
        code = apply(m, m.callee, m.args);
        break;
      case PERF:
        m.stack.push(new Resume(m.frame, m.dest, m.resume));
        code = perform(m);
        break;
      case HNDL:
        m.stack.push(new Resume(m.frame, m.dest, m.resume));
        code = install(m);
        break;
      // in tail position nothing waits for the return clause's value
      case TAILHNDL:
        code = install(m);
        break;
      case RGN:
        m.stack.push(new Resume(m.frame, m.dest, m.resume));
        code = open(m);
        break;
      case TAILRGN:
        code = open(m);
        break;
      case RET: {
        const entry = m.stack.pop();
        if (entry === undefined) return m.value;
        if (entry instanceof Resume) {
          entry.frame.r[entry.dest] = m.value;
          m.frame = entry.frame;
          m.seg = entry.seg;
          code = RUN;
        } else if (entry instanceof ApplyRemaining) {
          code = apply(m, m.value, entry.args);
        } else if (entry instanceof Marker) {
          code = apply(m, entry.ret, [m.value]);
        }
        // a region closes as the value passes it, and a `fast` clause's value passes
        // its boundary on to the perform below
        break;
      }
      default:
        bug(`a segment returned ${String(code)}`);
    }
  }
};

// Apply a function value to arguments, as a run of its own.
export const applyFunction = (callee, args) => {
  const m = new Machine();
  return run(m, apply(m, callee, args));
};

// Evaluate a global installed as a run: a function of no parameters, evaluated
// once where the module is initialized.
export const runGlobal = (f) => applyFunction(new Closure(f, []), []);

// Initialize the named global by evaluating its function. A fault ends the module's
// initialization, and it says which global it ended at.
export const initialize = (name, f) => {
  try {
    return runGlobal(f);
  } catch (e) {
    if (e instanceof Fault && e.global === undefined) e.global = name;
    throw e;
  }
};

// What segments call ----------------------------------------------------------------

// The `j`-th field of a data value, whose constructor must be the one the
// instruction names and which must have that field.
export const field = (value, c, j) => {
  if (!(value instanceof Data) || value.c !== c) bug(`a field of ${c.name} read from another value`);
  if (!(j >= 0 && j < value.f.length)) bug(`${c.name} has no field ${j}`);
  return value.f[j];
};

// The record of no fields. Records are never written in place, so one serves every
// module.
export const emptyRecord = Object.freeze({});

// Rows are sharp (D4): no key stands in a record twice. So an extension adds a key
// the record lacks, a restriction and an update touch one it holds, and a merge
// joins two records sharing none. Each operation checks its precondition: a breach
// is a defect upstream, and passing it would turn it into an ordinary value here.
const has = (record, key) => Object.prototype.hasOwnProperty.call(record, key);

export const extend = (record, key, value) => {
  if (has(record, key)) bug(`extending a record that holds ${key}`);
  return { ...record, [key]: value };
};

export const select = (record, key) => {
  if (!has(record, key)) bug(`no field ${key}`);
  return record[key];
};

export const restrict = (record, key) => {
  if (!has(record, key)) bug(`restricting a record that lacks ${key}`);
  const copy = { ...record };
  delete copy[key];
  return copy;
};

export const update = (record, key, value) => {
  if (!has(record, key)) bug(`updating a record that lacks ${key}`);
  return { ...record, [key]: value };
};

export const merge = (left, right) => {
  for (const key of Object.keys(right)) {
    if (has(left, key)) bug(`merging two records that both hold ${key}`);
  }
  return { ...left, ...right };
};

// What a variant carries at a key, which must be the key it was injected at.
export const payload = (variant, key) => {
  if (!(variant instanceof Variant) || variant.k !== key) bug(`no payload at ${key}`);
  return variant.v;
};

export const unreachable = (what) => bug(what);

// What the cell at position `i` of the region whose identity is `id` holds. The
// region is found afresh each time: an application of a continuation copies the
// regions it re-pushes, so a frame found before it is not the one after.
export const cget = (m, id, i) => regionOf(m, id, i).cells[i];

// Replace what that cell holds. A write has no result of its own, so it gives
// `Prim.Unit`.
export const cset = (m, id, i, value) => {
  regionOf(m, id, i).cells[i] = value;
  return PrimUnit.value;
};

// Literal identity of a `Number` (D37): the bit pattern, with every NaN taken as one.
// `0.0` and `-0.0` are two literals and a NaN is one, which strict equality gets wrong
// on both counts.
export const sameNumber = (a, b) => (Number.isNaN(a) ? Number.isNaN(b) : Object.is(a, b));

// The operations that are not one expression ---------------------------------------
//
// What each means is the ABI's (stella-base-0.1). An `Int` is an int32 held as a
// number, a `Char` the number of a scalar value, and a `String` a JavaScript string
// holding scalar values only; lengths and indices count scalar values (D27).

const MIN_INT = -2147483648;
const MAX_INT = 2147483647;

// Division truncated towards zero. `minInt / -1` is one past `maxInt`, and `| 0`
// wraps it to `minInt`, which is what the ABI fixes.
export const quot = (a, b) => {
  if (b === 0) fault(`Base.Int.quot: a zero divisor, dividing ${a}`);
  return (a / b) | 0;
};

// The remainder `quot` leaves, whose sign is the dividend's. `minInt % -1` is `-0`,
// which `| 0` makes `0`.
export const rem = (a, b) => {
  if (b === 0) fault(`Base.Int.rem: a zero divisor, dividing ${a}`);
  return (a % b) | 0;
};

// Truncated towards zero and saturating: NaN gives 0, and what is outside the range
// gives its nearer end.
export const numberToInt = (x) =>
  x !== x ? 0 : x >= MAX_INT ? MAX_INT : x <= MIN_INT ? MIN_INT : Math.trunc(x) | 0;

const scalars = (s) => Array.from(s);

export const stringLength = (s) => {
  let n = 0;
  for (const _ of s) n++;
  return n;
};

export const codePointAt = (i, s) => {
  const cs = scalars(s);
  if (!(i >= 0 && i < cs.length)) fault(`Base.String.codePointAt: index ${i} outside a string of ${cs.length}`);
  return cs[i].codePointAt(0);
};

// The scalar values from `start` up to but not including `end`; nothing counts from
// the end, and no bound is clamped.
export const slice = (start, end, s) => {
  const cs = scalars(s);
  if (!(start >= 0 && start <= end && end <= cs.length)) {
    fault(`Base.String.slice: bounds ${start}..${end} outside a string of ${cs.length}`);
  }
  return cs.slice(start, end).join("");
};

// Lexicographic by scalar value, a proper prefix preceding what it prefixes.
export const stringLt = (a, b) => {
  const x = a[Symbol.iterator]();
  const y = b[Symbol.iterator]();
  for (;;) {
    const p = x.next();
    const q = y.next();
    if (p.done) return !q.done;
    if (q.done) return false;
    const c = p.value.codePointAt(0);
    const d = q.value.codePointAt(0);
    if (c !== d) return c < d;
  }
};

export const fromCodePoint = (n) => {
  if (!(n >= 0 && n <= 0x10ffff) || (n >= 0xd800 && n <= 0xdfff)) {
    fault(`Base.Char.fromCodePoint: ${n} is no scalar value`);
  }
  return n;
};

// An array is a JavaScript array held as an opaque value. A slot nothing wrote is
// reached only by a read violating the precondition of `unsafeIndex` (D42).
export const arrayNew = (n) => {
  if (n < 0) fault(`Base.Array.unsafeNew: a negative count ${n}`);
  return new Array(n);
};

export const arraySet = (i, x, xs) => {
  if (!(i >= 0 && i < xs.length)) fault(`Base.Array.unsafeSet: index ${i} outside an array of ${xs.length}`);
  xs[i] = x;
  return PrimUnit.value;
};

export const arrayIndex = (xs, i) => {
  if (!(i >= 0 && i < xs.length)) fault(`Base.Array.unsafeIndex: index ${i} outside an array of ${xs.length}`);
  return xs[i];
};
