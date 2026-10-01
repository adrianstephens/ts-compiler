/// <reference path="./lib.d.ts" />
//-----------------------------------------------------------------------------
//	GC Array
//-----------------------------------------------------------------------------
// The raw fixed-length wasm-GC array -- exactly what `Array<T>` used to be, and the ONLY array the
// compiler itself knows (`WasmType`'s `{arr}`). A string and an `ArrayBuffer` are this too. Fixed length
// is the point: with no mutators it needs no identity of its own, so it stays the bare wasm array.
export class RawArray {
    get length() { return __asm('array.len')(); }
    // A packed element (`u8`, `i16`) is read widened, by its own sign.
    __get(i) { return __asm(`(switch $T (($u8 $u16) array.get_u $this) (($i8 $i16) array.get_s $this) (else array.get $this))`)(i); }
    __set(i, v) { return __asm('array.set $this')(i, v); }
    // `$this` IS the array type here, so these need no `TYPEINDEX`, and the operand order a receiver
    // gives (`this` first) is exactly `array.copy`'s and `array.fill`'s own.
    copyFrom(dstStart, src, srcStart, len) {
        return __asm('array.copy $this $this')(dstStart, src, srcStart, len);
    }
    fillWith(start, val, len) {
        return __asm('array.fill $this')(start, val, len);
    }
    constructor(n) {
        return __asm('array.new_default $this')(n);
    }
}
// The one supertype every `Array<T>` instantiation shares, whatever its storage kind -- so `Array.isArray` is a single
// `instanceof`, and never mistakes raw storage (a string, a bigint's limbs, a `RawArray`) for an array.
export class ArrayBase {
    constructor() { }
}
export class Array extends ArrayBase {
    // An `Array<T>` OWNS its storage instead of being it. A wasm-GC array has a fixed length, so a mutator
    // must reallocate; replacing `data` is an ordinary field write, so every alias of the array observes
    // it -- which `this = result` could never do, since it reached only the receiver's own lvalue.
    // Nothing here reassigns `this`, so `Array` no longer needs `assignsToThis`/`reassignsThis` at all.
    data;
    get length() { return this.data.length; }
    // Truncates, or grows with the element's default -- the holes `new Array(n)` already models that way.
    set length(n) {
        const result = new RawArray(n);
        result.copyFrom(0, this.data, 0, Math.min(n, this.data.length));
        this.data = result;
    }
    __get(i) { return this.data[i]; }
    __set(i, v) { this.data[i] = v; }
    static _make(n) { return new Array(n); }
    static _raw(a) { return a.data; }
    // `for (const k in x)` over anything read by position enumerates its INDICES, as strings. towasm desugars it into a `for...of`
    // over this, given `x.length`, so the conversion happens in typed lib code rather than in an unstamped synthesized AST.
    static _indexKeys(n) {
        const result = Array._make(n);
        for (let i = 0; i < n; i++)
            result[i] = i.toString();
        return result;
    }
    static isArray(x) {
        return x instanceof ArrayBase;
    }
    // @ts-expect-error - tison extension: multiple implementations
    static from(arrayLike) {
        const n = arrayLike.length;
        const r = Array._make(n);
        for (let i = 0; i < n; i++)
            r[i] = arrayLike[i];
        return r;
    }
    // @ts-expect-error - tison extension: multiple implementations
    static from(arrayLike, mapfn, thisArg) {
        const n = arrayLike.length;
        const r = Array._make(n);
        for (let i = 0; i < n; i++)
            r[i] = mapfn(arrayLike[i], i);
        return r;
    }
    // @ts-expect-error - tison extension: multiple implementations
    static from(iterable) {
        const result = [];
        for (const e of iterable)
            result.push(e);
        return result;
    }
    // @ts-expect-error - tison extension: multiple implementations
    static from(iterable, mapfn, thisArg) {
        const result = [];
        for (const e of iterable)
            result.push(mapfn(e, result.length));
        return result;
    }
    static of(...items) {
        return Array.from(items);
    }
    // @ts-expect-error - tison extension: multiple constructor implementations
    constructor(n) {
        super();
        this.data = new RawArray(n);
    }
    // Adopts storage the caller already built.
    // @ts-expect-error - tison extension: multiple constructor implementations
    constructor(d) {
        super();
        this.data = d;
    }
    grow(n) {
        const len = this.length;
        const result = new RawArray(len + n);
        result.copyFrom(0, this.data, 0, len);
        this.data = result;
        return len;
    }
    // `push`/`pop`/`shift`/`unshift`: real bodies -- growing/shrinking means allocating a fresh physical array
    // (a wasm-GC array's length is fixed at `array.new_default` time), and assigning it to `this` is how this
    // compiler's subset spells "replace my own receiver's physical value" (real TS never allows assigning to
    // `this`, so `backend.ts`'s `ensureMethod` treats a body that does it as this method's own explicit,
    // general signal to compile it that way -- not a hardcoded list of method names -- and rewrites every
    // call site to write the result back to the receiver's real lvalue; see `assignsToThis`/`reassignsThis`).
    pop() {
        const len = this.length;
        if (len) {
            const last = this[len - 1];
            const result = new RawArray(len - 1);
            result.copyFrom(0, this.data, 0, len - 1);
            this.data = result;
            return last;
        }
        return undefined;
    }
    push(...items) {
        const len = this.length;
        const n = items.length;
        const result = new RawArray(len + n);
        result.copyFrom(0, this.data, 0, len);
        result.copyFrom(len, items.data, 0, n);
        this.data = result;
        return len + n;
    }
    shift() {
        const len = this.length;
        if (len) {
            const first = this[0];
            const result = new RawArray(len - 1);
            result.copyFrom(0, this.data, 1, len - 1);
            this.data = result;
            return first;
        }
        return undefined;
    }
    unshift(...items) {
        const len = this.length;
        const n = items.length;
        const result = new RawArray(len + n);
        result.copyFrom(0, items.data, 0, n);
        result.copyFrom(n, this.data, 0, len);
        this.data = result;
        return len + n;
    }
    splice(start, deleteCount = 0, ...items) {
        const len = this.length;
        const n = items.length;
        const result = new RawArray(len - deleteCount + n);
        result.copyFrom(0, this.data, 0, start);
        result.copyFrom(start, items.data, 0, n);
        result.copyFrom(start + n - deleteCount, this.data, start + deleteCount, len - start - deleteCount);
        this.data = result;
        return this;
    }
    indexOf(x, fromIndex = 0) {
        for (let i = relativeIndex(fromIndex, this.length); i < this.length; i++) {
            if (this[i] === x)
                return i;
        }
        return -1;
    }
    lastIndexOf(x, fromIndex = 0x7fffffff) {
        for (let i = fromIndex < 0 ? this.length + fromIndex : fromIndex >= this.length ? this.length - 1 : fromIndex; i >= 0; --i) {
            if (this[i] === x)
                return i;
        }
        return -1;
    }
    // SameValueZero, NOT `indexOf(x) !== -1`: the two genuinely differ on NaN -- `indexOf` uses strict
    // equality and can never find one (correctly), while `[NaN].includes(NaN)` is true.
    // A negative index counts back from the end; out of range is `undefined`.
    at(index) {
        const i = index < 0 ? this.length + index : index;
        return i >= 0 && i < this.length ? this[i] : undefined;
    }
    includes(x, fromIndex = 0) {
        for (let i = relativeIndex(fromIndex, this.length); i < this.length; i++) {
            const v = this[i];
            if (v === x || (v !== v && x !== x))
                return true;
        }
        return false;
    }
    // `end`'s "omitted" default can't be `this.length` (towasm's call-site defaults must be plain
    // literals -- see backend.ts's `paramWasmType`), and a nullable `number` isn't supported either (no
    // boxing) -- so a large literal sentinel stands in for "omitted", clamped down to `len` below,
    // same as real JS already clamps an over-long `end` to the array's length.
    slice(start = 0, end = 0x7fffffff) {
        const len = this.length;
        // CLAMPED at both ends, and a reversed or out-of-range range is empty. `rlen` could go negative
        // (`slice(5)` on length 3, `slice(2, 1)`) and reached `_alloc` as a huge unsigned length --
        // "requested new array is too large" -- where JS simply gives `[]`.
        const from = relativeIndex(start, len), to = relativeIndex(end, len);
        const rlen = to > from ? to - from : 0;
        const result = Array._make(rlen);
        Array._raw(result).copyFrom(0, this.data, from, rlen);
        return result;
    }
    concat(b) {
        const result = Array._make(this.length + b.length);
        Array._raw(result).copyFrom(0, this.data, 0, this.length);
        Array._raw(result).copyFrom(this.length, Array._raw(b), 0, b.length);
        return result;
    }
    fill(x, start = 0, end = 0x7fffffff) {
        const len = this.length;
        start = relativeIndex(start, len);
        end = relativeIndex(end, len);
        if (end > start)
            this.data.fillWith(start, x, end - start);
        return this;
    }
    copyWithin(target, start, end = 0x7fffffff) {
        const len = this.length;
        if (end > len)
            end = len;
        if (target < 0)
            target += len;
        if (start < 0)
            start += len;
        if (end < 0)
            end += len;
        const me = this.data;
        me.copyFrom(target, me, start, end - start);
        return this;
    }
    every(callback, thisArg) {
        for (let i = 0; i < this.length; i++) {
            if (!callback(this[i], i, this))
                return false;
        }
        return true;
    }
    filter(callback, thisArg) {
        // Collected into a full-length scratch first, then copied down to the real count: a wasm-GC array's
        // length is fixed at allocation, and the old code returned the SCRATCH, so `.length` was always the
        // input's. Counting in a first pass instead would call `callback` twice per element, which is
        // observable whenever the predicate has a side effect.
        const scratch = Array._make(this.length);
        let n = 0;
        for (let i = 0; i < this.length; i++) {
            if (callback(this[i], i, this))
                scratch[n++] = this[i];
        }
        const result = Array._make(n);
        Array._raw(result).copyFrom(0, Array._raw(scratch), 0, n);
        return result;
    }
    find(callback, thisArg) {
        for (let i = 0; i < this.length; i++) {
            if (callback(this[i], i, this))
                return this[i];
        }
        // Explicit: falling off the end reached `unreachable` rather than returning the `undefined` JS
        // specifies for no match.
        return undefined;
    }
    findIndex(callback, thisArg) {
        for (let i = 0; i < this.length; i++) {
            if (callback(this[i], i, this))
                return i;
        }
        return -1;
    }
    // One level, TS's default depth: an element that is itself an array contributes its elements. The element type is
    // what TS's `FlatArray<T[], 1>` reduces to. `flat(depth)` beyond 1 is not declared, so the checker rejects it.
    flat() {
        const out = [];
        for (let i = 0; i < this.length; i++) {
            const el = this[i];
            if (Array.isArray(el)) {
                // Typed, so its elements are read as an array's: a ref-element Array<T> is compiled as Array<any>, where `el` is `any`.
                const inner = el;
                for (let j = 0; j < inner.length; j++)
                    out.push(inner[j]);
            }
            else
                out.push(el); // compiled only when `T` is no array (towasm `staticGuard`), where this is `T`
        }
        return out;
    }
    // Grown through `push` rather than sized up front by a first pass: the callback must run exactly ONCE
    // per element (they have effects), and holding the parts to measure them would need a `U[][]`, whose
    // `arr:ref` elements a concrete `number[]` part has no conversion into.
    flatMap(callback, thisArg) {
        const result = Array._make(0);
        for (let i = 0; i < this.length; i++) {
            const part = callback(this[i], i, this);
            if (Array.isArray(part)) {
                const inner = part;
                for (let j = 0; j < inner.length; j++)
                    result.push(inner[j]);
            }
            else
                result.push(part);
        }
        return result;
    }
    forEach(callback, thisArg) {
        for (let i = 0; i < this.length; i++)
            callback(this[i], i, this);
    }
    // What a value known only as an `Iterable` iterates by; a `for...of` over a known array still reads by position.
    [Symbol.iterator]() {
        return __towasm_indexed(() => this.length, i => this[i]);
    }
    join(separator = ',') {
        let result = '';
        for (let i = 0; i < this.length; i++) {
            if (i > 0)
                result = result.concat(separator);
            result = result.concat(this[i].toString());
        }
        return result;
    }
    map(callback, thisArg) {
        //result.push(callback.call(thisArg, array[i], i, array));
        const result = Array._make(this.length);
        for (let i = 0; i < this.length; i++)
            result[i] = callback(this[i], i, this);
        return result;
    }
    reduce(callback, initial) {
        const len = this.length;
        let i = 0;
        let result = initial;
        if (initial === undefined) {
            if (len === 0)
                throw new Error('Reduce of empty array with no initial value');
            result = this[0];
            i = 1;
        }
        for (; i < len; i++)
            result = callback(result, this[i], i, this);
        return result;
    }
    reduceRight(callback, initial) {
        const len = this.length;
        let i = len - 1;
        let result = initial;
        if (initial === undefined) {
            if (len === 0)
                throw new Error('Reduce of empty array with no initial value');
            result = this[len - 1];
            i = len - 2;
        }
        for (; i >= 0; i--)
            result = callback(result, this[i], i, this);
        return result;
    }
    reverse() {
        const len = this.length;
        for (let i = 0; i < len / 2; i++) {
            const tmp = this[i];
            this[i] = this[len - 1 - i];
            this[len - 1 - i] = tmp;
        }
        return this;
    }
    some(callback, thisArg) {
        for (let i = 0; i < this.length; i++) {
            if (callback(this[i], i, this))
                return true;
        }
        return false;
    }
    sort(compareFn = (a, b) => (a < b ? -1 : a > b ? 1 : 0)) {
        // Make a copy so we don't mutate the original
        const input = this.slice();
        function merge(left, right) {
            const result = Array._make(left.length + right.length);
            let i = 0, j = 0, k = 0;
            while (i < left.length && j < right.length)
                result[k++] = compareFn(left[i], right[j]) <= 0 ? left[i++] : right[j++];
            // Append remaining items
            Array._raw(result).copyFrom(k, Array._raw(left), i, left.length - i);
            Array._raw(result).copyFrom(k + left.length - i, Array._raw(right), j, right.length - j);
            return result;
        }
        function mergeSort(items) {
            if (items.length <= 1)
                return items;
            const mid = Math.floor(items.length / 2);
            return merge(mergeSort(items.slice(0, mid)), mergeSort(items.slice(mid)));
        }
        return mergeSort(input);
    }
    toString() {
        return this.join(',');
    }
    // Real JS calls `toLocaleString` on each element; with no locale support here that is exactly
    // `toString`, so this is an alias rather than a stub. Same reasoning as `String.toLocaleLowerCase`.
    toLocaleString() {
        return this.toString();
    }
}
