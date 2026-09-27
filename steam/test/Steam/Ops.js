// A bare host array standing as an opaque value, which is what a different entry
// might hand back. `Array.isArray` accepts it; the brand the payload carries does
// not, and that difference is what the check exists for.
export const notAnArray = [ 1, 2, 3 ];

// A number as a case compares it: `-0` apart from `0`, and NaN by name, neither of
// which `String` or `==` tells apart.
export const describeNumber = (x) => (Object.is(x, -0) ? "-0" : String(x));

export const nan = NaN;
