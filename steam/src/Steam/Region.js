// A region's identity is an object of this class, compared by reference. Every
// opening allocates one, so no two openings share an identity, whichever run or
// machine they belong to; a copy a continuation makes of a region frame holds the
// same object. The class is the brand that tells one from another opaque payload.
class StellaRegion {}

export const fresh = () => new StellaRegion();

export const isRegion = (opaque) => opaque instanceof StellaRegion;

export const same = (a) => (b) => a === b;
