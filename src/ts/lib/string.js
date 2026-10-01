/// <reference path="./lib.d.ts" />
import { expandReplacement } from './regexp';
//-----------------------------------------------------------------------------
//	String
//-----------------------------------------------------------------------------
export function strIsSpace(code) {
    return code === 32 || code === 9 || code === 10 || code === 13;
}
export class StringParser {
    str;
    pos;
    n;
    constructor(str, pos = 0) {
        this.str = str;
        this.pos = pos;
        this.n = str.length;
    }
    remaining() { return this.n - this.pos; }
    remainder() { return this.str.slice(this.pos); }
    processed() { return this.str.slice(0, this.pos); }
    code() { return this.pos < this.n ? this.str.charCodeAt(this.pos) : 0; }
    skipCode(c) {
        if (this.code() === c) {
            ++this.pos;
            return true;
        }
        return false;
    }
    skipWhitespace() {
        while (this.pos < this.n && strIsSpace(this.code()))
            ++this.pos;
    }
}
export function stringTemplate(strings, ...values) {
    const n = values.length;
    let result = strings[0];
    for (let i = 0; i < n; ++i)
        result = result.concat(values[i].toString()).concat(strings[i + 1]);
    return result;
}
export class String {
    get length() { return __asm('array.len')(); }
    // @ts-expect-error - tison extension: multiple constructor implementations
    constructor() {
        return String._alloc(0);
    }
    // @ts-expect-error - tison extension: multiple constructor implementations
    constructor(s) {
        return s.toString();
    }
    static _alloc = __asm('array.new_default $this');
    static _setChar = __asm('array.set $this');
    static _copy = __asm('array.copy $this $this');
    // @ts-expect-error - tison extension: multiple implementations
    static fromCharCode(c) {
        const result = String._alloc(1);
        String._setChar(result, 0, c);
        return result;
    }
    // @ts-expect-error - tison extension: multiple implementations
    static fromCharCode(...codes) {
        const result = String._alloc(codes.length);
        for (let i = 0; i < codes.length; i++)
            String._setChar(result, i, codes[i]);
        return result;
    }
    // Each code point above 0xFFFF is its UTF-16 surrogate pair; an invalid one is a RangeError, as in JS.
    static fromCodePoint(...codePoints) {
        let n = 0;
        for (let i = 0; i < codePoints.length; i++) {
            const c = codePoints[i];
            if (c < 0 || c > 0x10ffff || c !== Math.floor(c))
                throw new RangeError('Invalid code point ' + c);
            n += c > 0xffff ? 2 : 1;
        }
        const result = String._alloc(n);
        let j = 0;
        for (let i = 0; i < codePoints.length; i++) {
            const c = codePoints[i];
            if (c > 0xffff) {
                String._setChar(result, j++, 0xd800 + ((c - 0x10000) >> 10));
                String._setChar(result, j++, 0xdc00 + ((c - 0x10000) & 0x3ff));
            }
            else {
                String._setChar(result, j++, c);
            }
        }
        return result;
    }
    // One `array.new_default` up front, then a straight fill -- the point is precisely to avoid
    // `concat`'s per-call fresh-array-and-copy-both-sides cost when a caller has `len` bytes in hand.
    static fromCharCodesAt(ptr, len) {
        const result = String._alloc(len);
        for (let i = 0; i < len; i++)
            String._setChar(result, i, __asm('i32.load8_u')(ptr + i));
        return result;
    }
    toString() { return this; }
    charCodeAt = __asm('array.get_u $this');
    // Out of range is `''`, not a trap -- so this cannot be the bare `array.get_u`/`array.new_fixed` pair
    // it used to be. `charCodeAt` stays raw: every caller in this file guards its own index.
    charAt(pos) {
        return pos < 0 || pos >= this.length ? '' : String.fromCharCode(this.charCodeAt(pos));
    }
    // `s[i]`. Was its own asm pair that read with `array.get` (illegal on a packed `i16` array -- V8
    // rejected the whole module) and then wrote through `$this`, i.e. into the receiver rather than the
    // fresh one-character result.
    __get(i) {
        return this.charAt(i);
    }
    indexOf(needle, position = 0) {
        const n = this.length;
        const m = needle.length;
        for (let i = clampIndex(position, n); i <= n - m; i++) {
            let j = 0;
            while (j < m && this.charCodeAt(i + j) === needle.charCodeAt(j))
                j++;
            if (j === m)
                return i;
        }
        return -1;
    }
    lastIndexOf(needle, position = 0x7fffffff) {
        const n = this.length;
        const m = needle.length;
        const p = clampIndex(position, n);
        for (let i = p < n - m ? p : n - m; i >= 0; --i) {
            let j = 0;
            while (j < m && this.charCodeAt(i + j) === needle.charCodeAt(j))
                j++;
            if (j === m)
                return i;
        }
        return -1;
    }
    includes(needle, position = 0) {
        return this.indexOf(needle, position) !== -1;
    }
    startsWith(prefix, position = 0) {
        const m = prefix.length;
        const p = clampIndex(position, this.length);
        if (p + m > this.length)
            return false;
        for (let j = 0; j < m; j++) {
            if (this.charCodeAt(p + j) !== prefix.charCodeAt(j))
                return false;
        }
        return true;
    }
    endsWith(suffix, endPosition = 0x7fffffff) {
        const m = suffix.length;
        const n = clampIndex(endPosition, this.length);
        if (m > n)
            return false;
        const offset = n - m;
        for (let j = 0; j < m; ++j) {
            if (this.charCodeAt(offset + j) !== suffix.charCodeAt(j))
                return false;
        }
        return true;
    }
    // CLAMPED at both ends, and a reversed or out-of-range range is empty: `rlen` could otherwise go
    // negative (`slice(3, 1)`, `slice(9)`) and reach `_alloc` as a huge unsigned length -- "requested new
    // array is too large" -- where JS simply gives `''`.
    slice(start = 0, end = 0x7fffffff) {
        const len = this.length;
        const from = relativeIndex(start, len), to = relativeIndex(end, len);
        const rlen = to > from ? to - from : 0;
        const result = String._alloc(rlen);
        String._copy(result, 0, this, from, rlen);
        return result;
    }
    trim() {
        const len = this.length;
        let start = 0;
        while (start < len && strIsSpace(this.charCodeAt(start)))
            start++;
        let end = len;
        while (end > start && strIsSpace(this.charCodeAt(end - 1)))
            end--;
        return this.slice(start, end);
    }
    toUpperCase() {
        const n = this.length;
        const result = String._alloc(n);
        for (let i = 0; i < n; i++) {
            const code = this.charCodeAt(i);
            String._setChar(result, i, (code >= 97 && code <= 122) ? code - 32 : code);
        }
        return result;
    }
    toLowerCase() {
        const n = this.length;
        const result = String._alloc(n);
        for (let i = 0; i < n; i++) {
            const code = this.charCodeAt(i);
            String._setChar(result, i, (code >= 65 && code <= 90) ? code + 32 : code);
        }
        return result;
    }
    // No locale support exists in this runtime, so the locale-aware forms ARE the plain ones -- an alias
    // is the honest implementation, not a stub. Declared without a `locales` parameter for the same
    // reason: taking one and ignoring it would be a lie the signature tells.
    toLocaleUpperCase() { return this.toUpperCase(); }
    toLocaleLowerCase() { return this.toLowerCase(); }
    valueOf() { return this; }
    repeat(count) {
        const len = this.length;
        const result = String._alloc(len * count);
        for (let i = 0; i < count; i++)
            String._copy(result, i * len, this, 0, len);
        return result;
    }
    // @ts-expect-error - tison extension: multiple implementations
    concat(b) {
        const result = String._alloc(this.length + b.length);
        String._copy(result, 0, this, 0, this.length);
        String._copy(result, this.length, b, 0, b.length);
        return result;
    }
    // @ts-expect-error - tison extension: multiple implementations
    concat(...strings) {
        let result = this;
        for (const s of strings)
            result = result.concat(s);
        return result;
    }
    match(regexp) {
        return regexp.exec(this);
    }
    search(regexp) {
        const s = this;
        const m = regexp.exec(s);
        return m === null ? -1 : m.index;
    }
    // `$1`.."$9"/`$&`/`$$` substitution (see regexp.ts's `expandReplacement`), or the FUNCTION replacer,
    // which real JS calls as `(match, ...captures, offset, input)`. Honors `g` (all matches) vs first-only.
    replace(regexp, replacement) {
        const s = this;
        let result = '';
        let last = 0;
        let go = true;
        regexp.lastIndex = 0;
        while (go) {
            const m = regexp.exec(s);
            if (m === null) {
                go = false;
            }
            else {
                let piece = '';
                if (typeof replacement === 'string') {
                    piece = expandReplacement(replacement, m);
                }
                else {
                    // A group that did not participate is `undefined` in real JS, not the empty string
                    // `group` itself returns -- callers routinely test the arguments with `!== undefined`.
                    const args = [];
                    for (let i = 1; i < m.length; i++)
                        args.push(m.groupStart(i) === -1 ? undefined : m.group(i));
                    args.push(m.index);
                    args.push(s);
                    piece = replacement(m.group(0), ...args);
                }
                result = result.concat(s.slice(last, m.index)).concat(piece);
                last = m.groupEnd(0);
                if (!regexp.global)
                    go = false;
            }
        }
        return result.concat(s.slice(last, s.length));
    }
    // Capture groups aren't interleaved into the result (unlike real JS's `split(/(\d)/)`) -- explicit
    // scope simplification (see StringParts's own comment), not an oversight.
    // ES `SplitMatcher`, which is not "find the next separator": the separator must match starting
    // EXACTLY at the cursor, and an empty match at the previous split point never splits again. The old
    // loop pushed each SEPARATOR match instead of the text between them, so `'a,b,c'.split(/,/)` was
    // `[',', ',', 'c']` -- with the right length, which is why only a value comparison caught it.
    // `string | RegExp`, narrowed by `typeof`: lib.d.ts always declared the union, but only the RegExp
    // half existed, so `'a.b'.split('.')` type-checked and then failed codegen converting the string to
    // a `RegExp`.
    split(separator, limit = 0x7fffffff) {
        const s = this;
        const result = [];
        const size = s.length;
        if (limit === 0)
            return result;
        if (typeof separator === 'string') {
            const sep = separator;
            const m = sep.length;
            // An empty subject splits to `[]` only when the separator matches it -- i.e. is itself empty.
            if (size === 0) {
                if (m !== 0)
                    result.push(s);
                return result;
            }
            // An empty separator splits into single characters; the general scan below would match at
            // every position and make no progress.
            if (m === 0) {
                for (let i = 0; i < size; i++) {
                    result.push(s.slice(i, i + 1));
                    if (result.length >= limit)
                        return result;
                }
                return result;
            }
            let p = 0;
            let q = 0;
            while (q + m <= size) {
                let j = 0;
                while (j < m && s.charCodeAt(q + j) === sep.charCodeAt(j))
                    j++;
                if (j === m) {
                    result.push(s.slice(p, q));
                    if (result.length >= limit)
                        return result;
                    q = q + m;
                    p = q;
                }
                else {
                    q = q + 1;
                }
            }
            result.push(s.slice(p, size));
            return result;
        }
        // An empty subject is `[]` when the separator matches it, `['']` otherwise.
        if (size === 0) {
            // `execFrom`, not `exec` -- split scans regardless of `separator`'s own `g`/`lastIndex`
            // state, the same way real JS split() ignores them.
            if (separator.execFrom(s, 0) === null)
                result.push(s);
            return result;
        }
        let p = 0;
        let q = 0;
        while (q < size) {
            const m = separator.execFrom(s, q);
            if (m === null || m.groupStart(0) !== q) {
                q = q + 1;
                continue;
            }
            const e = m.groupEnd(0);
            if (e === p) {
                q = q + 1;
                continue;
            }
            result.push(s.slice(p, q));
            if (result.length >= limit)
                return result;
            p = e;
            q = p;
        }
        result.push(s.slice(p));
        return result;
    }
    // NOT `slice`: `substring` clamps a negative (or NaN) argument to 0 rather than counting from the
    // end, and SWAPS the two when `start > end`.
    substring(start, end = 0x7fffffff) {
        const len = this.length;
        let from = start < 0 ? 0 : start > len ? len : start;
        let to = end < 0 ? 0 : end > len ? len : end;
        if (from > to) {
            const t = from;
            from = to;
            to = t;
        }
        const result = String._alloc(to - from);
        String._copy(result, 0, this, from, to - from);
        return result;
    }
    add(b) { return this.concat(b); }
    compare(b) {
        const len = Math.min(this.length, b.length);
        for (let i = 0; i < len; i++) {
            const d = this.charCodeAt(i) - b.charCodeAt(i);
            if (d)
                return d;
        }
        return this.length - b.length;
    }
    lt(b) { return this.compare(b) < 0; }
    gt(b) { return this.compare(b) > 0; }
    le(b) { return this.compare(b) <= 0; }
    ge(b) { return this.compare(b) >= 0; }
    eq(b) { return this.compare(b) === 0; }
    ne(b) { return this.compare(b) !== 0; }
}
