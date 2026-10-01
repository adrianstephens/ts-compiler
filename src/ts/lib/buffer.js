/// <reference path="./lib.d.ts" />
import { TypedArray, f64FromBits } from './typedarray';
// Node's `Buffer` IS a `Uint8Array` subclass, and so is this one: indexing, `length` and the byte storage
// are `TypedArray<u8>`'s, inherited rather than restated. A GLOBAL (`lib/*.ts`, not `lib/node/*`), because
// node's `Buffer` is one -- code uses it without importing anything.
//
// Only what this runtime's own callers need is implemented. `Buffer` carries a large API in node, and a
// member that is absent fails loudly at the call site, which is far better than one that quietly answers
// something else.
export class Buffer extends TypedArray {
    constructor(length) {
        super(length);
    }
    // Copies, as node's does. Allocates by LENGTH and fills, rather than delegating to `TypedArray`'s own
    // `number[]` constructor: that is one of its multiple implementations, which only tison can see, so
    // `super(elements)` would not type-check against the single signature TS resolves.
    static from(array) {
        const buf = new Buffer(array.length);
        for (let i = 0; i < array.length; i++)
            buf[i] = array[i];
        return buf;
    }
    // Node's big-endian IEEE-754 double (tableCache.ts's own stamp read). Assembled from this buffer's own bytes:
    // its storage is a wasm-GC array, and `DataView` reads linear memory, which a `TypedArray` never uses.
    readDoubleBE(offset = 0) {
        const hi = (this[offset] << 24) | (this[offset + 1] << 16) | (this[offset + 2] << 8) | this[offset + 3];
        const lo = (this[offset + 4] << 24) | (this[offset + 5] << 16) | (this[offset + 6] << 8) | this[offset + 7];
        return f64FromBits(lo, hi);
    }
    // 'latin1'/'binary' ONLY, and every other encoding throws rather than answering something else. This
    // runtime's strings are one code unit per byte (see `console.ts`), which IS latin1, so the decode is
    // the identity; 'utf8' -- node's default, hence no default here -- would need a real decoder, and
    // returning latin1 for it would silently corrupt every byte above 0x7f.
    toString(encoding, start, end) {
        if (encoding !== 'latin1' && encoding !== 'binary')
            throw new Error(`Buffer.toString: only 'latin1'/'binary' are supported, not '${encoding}'`);
        const from = start ?? 0;
        const to = end ?? this.length;
        const codes = [];
        for (let i = from; i < to; i++)
            codes.push(this[i]);
        return String.fromCodePoint(...codes);
    }
}
