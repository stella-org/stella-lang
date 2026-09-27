// The one shape that can be checked. An arity cannot: a manifest carries none, and
// `Function.length` counts neither a rest parameter nor one with a default — which is
// how an adapter is usually written.
export const isCallable = (value) => typeof value === "function";

const refuse = Symbol.for("stella.refuse");

// An adapter returns what it produces, and refuses by handing back an object carrying
// the reason under that symbol. Constructing the interpreter's own outcome is asked of
// no one: the two constructors come from the caller, and this is where they are put on.
//
// A symbol rather than a string key because an adapter may legitimately return an
// opaque host value it got from elsewhere, and a key one of those happened to carry
// would be read as a refusal.
export const wrapAdapterImpl = (produced) => (refused) => (adapter) => (args) => {
  const result = adapter(args);
  if (result !== null && typeof result === "object" && refuse in result) {
    return refused(result[refuse]);
  }
  return produced(result);
};
