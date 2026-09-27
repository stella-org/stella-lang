// A bare host array standing as an opaque value, which is what a different entry
// might hand back. `Array.isArray` accepts it; the brand the payload carries does
// not, and that difference is what the check exists for.
export const notAnArray = [ 1, 2, 3 ];
