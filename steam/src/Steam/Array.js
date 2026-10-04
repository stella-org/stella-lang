// The payload carries a brand of its own rather than being a bare host array.
// `Array.isArray` would accept any array a different entry happened to hand back —
// another intrinsic opaque, or a hosted foreign's own payload — and writing through
// one of those is exactly what the check exists to stop. The class is that brand,
// and it is intrinsic to the object rather than a side table.
//
// Nothing records which slots have been written: reading an unwritten one is a
// violated precondition, and the check the alternative needs would stand on every
// read. This brand is not that check — it is asked once where an operation takes
// its array apart, not once per slot.
class StellaArray {
  constructor(n) {
    this.slots = new Array(n);
  }
}

export const isArray = (opaque) => opaque instanceof StellaArray;

export const allocate = (n) => new StellaArray(n);

export const length = (array) => array.slots.length;

export const read = (array, i) => array.slots[i];

export const write = (array, i, value) => {
  array.slots[i] = value;
};

export const newOwned = () => new WeakSet();

export const ownImpl = (owned, array) => {
  owned.add(array);
};

export const ownsImpl = (owned, array) => owned.has(array);
