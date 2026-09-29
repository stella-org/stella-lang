// A host token inside the interpreter: the JSON object the host handed over, under a
// brand this module keeps to itself. Only a value built here reads back as a token,
// so an opaque value of any other kind — an array, a host's own object — does not.
const brand = Symbol("stella session token");

export const wrap = (token) => ({ [brand]: token });

export const unwrapImpl = (nothing) => (just) => (value) =>
  value !== null && typeof value === "object" && Object.prototype.hasOwnProperty.call(value, brand)
    ? just(value[brand])
    : nothing;
