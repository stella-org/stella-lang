// A promise, which is what a host hands back where nothing marshals it: Stella
// fixes no meaning for asynchrony, so one crosses as an opaque value like any
// other.
//
// **It resolves to something that is not a Stella value**, so a loop that awaited
// it would be caught by what came back rather than by a case that happened to pass.
export const aPromise = Promise.resolve(42);

export const isThePromise = (o) => o === aPromise;
