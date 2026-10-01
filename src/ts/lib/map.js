/// <reference path="./lib.d.ts" />
//-----------------------------------------------------------------------------
//	Map -- linear-scan implementation
//-----------------------------------------------------------------------------
// O(n) get/set/has/delete over a parallel keys_/values_ pair -- real `===` for key equality, which
// is already correct per-type in this compiler (content-based for `string`, reference-based for a
// class instance), matching real Map's own key semantics for both without any special-casing here.
// A real hash table (O(1) for string keys, the common case) is a legitimate later optimization, not
// attempted yet -- this project's own actual Map usage (checker.ts/type-utils.ts/etc, the reason
// this file exists) isn't at a scale where O(n) lookup matters.
class Map {
    keys_ = [];
    values_ = [];
    // @ts-expect-error - tison extension: multiple constructor implementations
    constructor(entries = []) {
        const n = entries.length;
        for (let i = 0; i < n; i++)
            this.set(entries[i][0], entries[i][1]);
    }
    // @ts-expect-error - tison extension: multiple constructor implementations
    constructor(other) {
        if (other) {
            const keys = other.keys(), values = other.values();
            for (let i = 0; i < keys.length; i++)
                this.set(keys[i], values[i]);
        }
    }
    // TS's own constructor; the two above are fast paths for the commonest arguments.
    // @ts-expect-error - tison extension: multiple constructor implementations
    constructor(entries) {
        if (entries)
            for (const [k, v] of entries)
                this.set(k, v);
    }
    get size() { return this.keys_.length; }
    indexOf(key) {
        const n = this.keys_.length;
        for (let i = 0; i < n; i++) {
            if (this.keys_[i] === key)
                return i;
        }
        return -1;
    }
    get(key) {
        const i = this.indexOf(key);
        return i === -1 ? undefined : this.values_[i];
    }
    has(key) {
        return this.indexOf(key) !== -1;
    }
    set(key, value) {
        const i = this.indexOf(key);
        if (i === -1) {
            this.keys_.push(key);
            this.values_.push(value);
        }
        else {
            this.values_[i] = value;
        }
        return this;
    }
    // Shifts every later entry down one slot -- O(n), same as the scan that found `key`, and keeps
    // the remaining entries in their original relative (insertion) order, matching real Map.
    delete(key) {
        const i = this.indexOf(key);
        if (i === -1)
            return false;
        const n = this.keys_.length;
        for (let j = i; j < n - 1; j++) {
            this.keys_[j] = this.keys_[j + 1];
            this.values_[j] = this.values_[j + 1];
        }
        this.keys_.pop();
        this.values_.pop();
        return true;
    }
    clear() {
        this.keys_ = [];
        this.values_ = [];
    }
    // Snapshots (plain arrays), not live iterators; iterating the Map itself (`[Symbol.iterator]`) is the live path.
    keys() { return this.keys_.slice(); }
    values() { return this.values_.slice(); }
    entries() { return this.keys_.map((k, i) => [k, this.values_[i]]); }
    [Symbol.iterator]() {
        return __towasm_indexed(() => this.keys_.length, i => [this.keys_[i], this.values_[i]]);
    }
    // `thisArg` is ignored (not needed for the few real call sites this project has, and not supported by the `for...of` loop either).
    forEach(callbackfn, thisArg) {
        const n = this.keys_.length;
        for (let i = 0; i < n; i++)
            callbackfn(this.values_[i], this.keys_[i], this);
    }
}
//-----------------------------------------------------------------------------
//	DynamicObject -- a plain object with no fixed layout
//-----------------------------------------------------------------------------
// What `{[k: string]: V}` compiles to. A struct of its own, not a `Map`: through `any` it must read as its keys, never as a Map's members.
class DynamicObject {
    map_ = new Map();
    get(key) { return this.map_.get(key); }
    has(key) { return this.map_.has(key); }
    set(key, value) { this.map_.set(key, value); return this; }
    delete(key) { return this.map_.delete(key); }
    keys() { return this.map_.keys(); }
    values() { return this.map_.values(); }
    entries() { return this.map_.entries(); }
    // `Object.keys/values/entries` of an erased receiver: the raw `any[]` every representation answers with.
    anyEntries(which) {
        const keys = this.map_.keys();
        const out = new RawArray(keys.length);
        for (let i = 0; i < keys.length; i++)
            out[i] = which === 'keys' ? keys[i] : which === 'values' ? this.map_.get(keys[i]) : [keys[i], this.map_.get(keys[i])];
        return out;
    }
}
//-----------------------------------------------------------------------------
//	Set -- linear-scan implementation (see lib/map.ts's header comment for the tradeoff)
//-----------------------------------------------------------------------------
class Set {
    items_ = [];
    // @ts-expect-error - tison extension: multiple constructor implementations
    constructor(values = []) {
        const n = values.length;
        for (let i = 0; i < n; i++)
            this.add(values[i]);
    }
    // @ts-expect-error - tison extension: multiple constructor implementations
    constructor(other) {
        if (other) {
            const values = other.values();
            for (let i = 0; i < values.length; i++)
                this.add(values[i]);
        }
    }
    // As `Map`'s: TS's own constructor, after the fast paths.
    // @ts-expect-error - tison extension: multiple constructor implementations
    constructor(values) {
        if (values)
            for (const v of values)
                this.add(v);
    }
    get size() { return this.items_.length; }
    indexOf(value) {
        const n = this.items_.length;
        for (let i = 0; i < n; i++) {
            if (this.items_[i] === value)
                return i;
        }
        return -1;
    }
    has(value) {
        return this.indexOf(value) !== -1;
    }
    add(value) {
        if (this.indexOf(value) === -1)
            this.items_.push(value);
        return this;
    }
    // See Map.delete's own comment -- same shift-down-then-pop, same order guarantee.
    delete(value) {
        const i = this.indexOf(value);
        if (i === -1)
            return false;
        const n = this.items_.length;
        for (let j = i; j < n - 1; j++)
            this.items_[j] = this.items_[j + 1];
        this.items_.pop();
        return true;
    }
    clear() {
        this.items_ = [];
    }
    // A snapshot (plain array), not a live iterator -- see Map.keys's own comment.
    values() { return this.items_.slice(); }
    keys() { return this.values(); }
    entries() { return this.items_.map(k => [k, k]); }
    [Symbol.iterator]() {
        return __towasm_indexed(() => this.items_.length, i => this.items_[i]);
    }
    forEach(callbackfn, thisArg) {
        const n = this.items_.length;
        for (let i = 0; i < n; i++)
            callbackfn(this.items_[i], this.items_[i], this);
    }
}
//-----------------------------------------------------------------------------
//	WeakMap -- backed by Map, and not actually weak
//-----------------------------------------------------------------------------
// Nothing is collected: an entry lives as long as the WeakMap does, since there's no finalization to
// hook. Every use in this project is a cache keyed by an immutable Type/AST node, so it costs only
// retention, never correctness.
class WeakMap {
    map_;
    constructor(entries = []) {
        this.map_ = new Map(entries);
    }
    get(key) { return this.map_.get(key); }
    has(key) { return this.map_.has(key); }
    set(key, value) { this.map_.set(key, value); return this; }
    delete(key) { return this.map_.delete(key); }
}
// Backed by `Set`, and not weak either -- same reasoning as `WeakMap` above.
class WeakSet {
    set_;
    constructor(values = []) {
        this.set_ = new Set(values);
    }
    has(value) { return this.set_.has(value); }
    add(value) { this.set_.add(value); return this; }
    delete(value) { return this.set_.delete(value); }
}
// `at(i)` while `i < size()`, both read on every step: how `Map`/`Set` iterate their own backing arrays live.
export function* __towasm_indexed(size, at) {
    for (let i = 0; i < size(); i++)
        yield at(i);
}
