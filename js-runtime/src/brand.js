// The brand a refusal carries. It is a symbol of this package's own and not a
// registered one, so nothing an implementation could have obtained elsewhere carries
// it: `Symbol.for` would hand the same symbol to any code that asked for its name.
//
// This file is not among the package's exports. An implementation builds a refusal
// through `./foreign` and the interpreter reads one through `./interpreter`, and
// neither can reach the symbol itself.
export const refusal = Symbol("stella.refuse");
