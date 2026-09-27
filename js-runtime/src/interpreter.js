import { refusal } from "./brand.js";

// The reason a refusal carries, or `undefined` for any other value.
//
// A refusal is recognised by the brand alone, never by shape: an opaque host value
// may be any object at all. A refusal built by a second copy of this package carries
// a brand this copy does not know, so it reads as an ordinary value.
export const refusalReason = (value) =>
  value !== null && typeof value === "object" && refusal in value
    ? value[refusal]
    : undefined;
