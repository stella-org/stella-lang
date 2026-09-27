import { refusalReason } from "@stella-lang/runtime/interpreter";

// The reason a refusal carries. The brand is the runtime package's own, and this is
// the one instance of that package the build supplies, so a refusal an
// implementation built through `@stella-lang/runtime/foreign` is recognised here.
export const refusalOfImpl = (nothing) => (just) => (value) => {
  const reason = refusalReason(value);
  return reason === undefined ? nothing : just(reason);
};

export const numberOfImpl = (nothing) => (just) => (value) =>
  typeof value === "number" ? just(value) : nothing;

export const stringOfImpl = (nothing) => (just) => (value) =>
  typeof value === "string" ? just(value) : nothing;

export const booleanOfImpl = (nothing) => (just) => (value) =>
  typeof value === "boolean" ? just(value) : nothing;

// The one shape of an export that can be checked, and of an action. An arity cannot:
// `Function.length` counts neither a rest parameter nor one with a default.
export const isCallable = (value) => typeof value === "function";

// What a `unit` parameter is handed: it keeps its place, and holds nothing.
export const nothingAtAll = undefined;

// An implementation is uncurried, so the arguments arrive as arguments.
export const applyImpl = (implementation, args) => implementation(...args);

// An action is performed with no arguments.
export const performImpl = (action) => action();
