// What code the JavaScript backend generates runs on.
//
// A Stella function is generated as a set of *segments*: an entry segment, and one
// for what follows each non-tail call. A segment runs to the next call and returns
// a code saying what the run loop does next, so the host's call stack never holds
// more than one segment. Activations live in frames on a stack of the runtime's
// own, which is what lets a tail call push nothing and a deep recursion run in
// bounded host stack.
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
// fail on. It is not an effect — no handler intercepts one — and it discards the
// whole run. `global` names the global being initialized when one ends a module's
// initialization.
export class Fault extends Error {
  constructor(message) {
    super(message);
    this.name = "StellaFault";
    this.global = undefined;
  }
}

const fault = (message) => {
  throw new Fault(message);
};

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

// A `Base` operation standing as a callee, for a partial application of it.
export const prim = (name, arity, apply) => ({ kind: "prim", name, arity, apply });

// `Prim.Unit`, which no module declares and every module may name.
export const PrimUnit = ctor("Prim.Unit", 0);

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

// Apply the value to `args`. An over-application leaves one behind.
class ApplyRemaining {
  constructor(args) {
    this.args = args;
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
  }
}

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
      case "prim": {
        const n = callee.arity;
        if (args.length < n) {
          m.value = new Pap(callee, args);
          return RET;
        }
        if (args.length > n) {
          m.stack.push(new ApplyRemaining(args.slice(n)));
          args = args.slice(0, n);
        }
        m.value = callee.apply(...args);
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
      case RET: {
        const entry = m.stack.pop();
        if (entry === undefined) return m.value;
        if (entry instanceof Resume) {
          entry.frame.r[entry.dest] = m.value;
          m.frame = entry.frame;
          m.seg = entry.seg;
          code = RUN;
        } else {
          code = apply(m, m.value, entry.args);
        }
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
