// The arithmetic whose meaning the host's own operators do not give directly.

// Multiplication modulo 2³². `(a * b) | 0` is not this: the exact product of two
// int32s needs up to 62 bits, and binary64 keeps 53, so the low bits it wraps to
// are already lost.
export const mulImpl = (a) => (b) => Math.imul(a, b);

// Division truncated towards zero. `minInt / -1` is one past `maxInt`, and `| 0`
// wraps it to `minInt`, which is what the ABI fixes. The divisor is not zero here.
export const quotImpl = (a) => (b) => (a / b) | 0;

// The remainder `quot` leaves, whose sign is the dividend's. `minInt % -1` is `-0`,
// which `| 0` makes `0`.
export const remImpl = (a) => (b) => (a % b) | 0;

// Truncated towards zero and saturating: NaN gives 0, and what is outside the
// range gives its nearer end.
export const toIntImpl = (x) =>
  x !== x
    ? 0
    : x >= 2147483647
      ? 2147483647
      : x <= -2147483648
        ? -2147483648
        : Math.trunc(x) | 0;

// The host's conversion is ECMAScript's `Number::toString(x, 10)`, which is the
// meaning the ABI fixes by naming the 15th edition of ECMA-262.
export const numberToStringImpl = (x) => String(x);

export const intToStringImpl = (n) => String(n);

// Each exact in binary64, and each returning NaN, an infinity, or a zero as it was.
export const floorImpl = Math.floor;
export const ceilImpl = Math.ceil;
export const truncImpl = Math.trunc;
