/* eslint-disable @typescript-eslint/no-inferrable-types */
/* eslint-disable @typescript-eslint/triple-slash-reference */
/* eslint-disable @typescript-eslint/prefer-for-of */
/// <reference path="./lib.d.ts" />
//-----------------------------------------------------------------------------
//	BigInt
//-----------------------------------------------------------------------------
// Limbs are backed by a real `RawArray<u32>` (wasm-GC array, reclaimed by the host's GC when unreachable --
// unlike the old `Uint32Array`/linear-memory backing, which never freed). Every indexed read below is
// still bound to an explicit `number` local before use in further arithmetic, rather than mixed directly
// with a `number` local in one expression -- `arithInline` in backend.ts dispatches purely on the *left*
// operand's physical kind, so e.g. `someArr[i] * someLargeNumberLocal` would silently truncate the right
// side toward `i32`/`u32` (lossy/saturating) if the left side stays a raw indexed read. Bitwise results
// need their own care in the other direction: real JS (and this compiler) gives `&`/`|`/`^`/`<<`/`>>` a
// *signed* 32-bit result even for an unsigned-meaning operand -- see `toU32`.
// The exact 64-bit product of two limbs (`(2^32-1)^2 < 2^64`, past what a `number` holds exactly), as its low and high halves.
const mulLo = __asm(`
	(local $b i32)
	local.set $b
	i64.extend_i32_u
	(i64.extend_i32_u (local.get $b))
	i64.mul
	i32.wrap_i64
`);
const mulHi = __asm(`
	(local $b i32)
	local.set $b
	i64.extend_i32_u
	(i64.extend_i32_u (local.get $b))
	i64.mul
	(i64.shr_u (i64.const 32))
	i32.wrap_i64
`);
export function bigFromNumber(n) {
    // The limb loop below builds a MAGNITUDE (its `Math.floor(m / 0x100000000)` walk assumes `n >= 0`),
    // so a negative goes round once on its absolute value and is negated at the end -- otherwise
    // `BigInt(-5)` produced garbage that compared as positive.
    if (n < 0)
        return -bigFromNumber(-n);
    let count = 1;
    for (let t = Math.floor(n / 0x100000000); t > 0; t = Math.floor(t / 0x100000000))
        ++count;
    const r = new RawArray(count + 1);
    for (let i = 0, m = n; i < count; i++) {
        const t = Math.floor(m / 0x100000000);
        r[i] = m - t * 0x100000000;
        m = t;
    }
    return bigTrim(r);
}
// `BigInt('123')`. Real JS accepts optional surrounding whitespace, an optional sign and decimal
// digits (an empty or all-whitespace string is `0n`), and throws a SyntaxError on anything else --
// there is no NaN to fall back on the way `Number('abc')` has. Digits are accumulated through the
// ordinary bigint operators, so this is exact at any length rather than going via `number`.
export function bigFromString(s) {
    const n = s.length;
    let i = 0;
    while (i < n && strIsSpace(s.charCodeAt(i)))
        i++;
    let neg = false;
    if (i < n) {
        const c = s.charCodeAt(i);
        if (c === 45 || c === 43) {
            neg = c === 45;
            i++;
        }
    }
    const start = i;
    let result = bigFromNumber(0);
    const ten = bigFromNumber(10);
    while (i < n) {
        const d = s.charCodeAt(i) - 48;
        if (d < 0 || d > 9)
            break;
        result = result.mul(ten).add(bigFromNumber(d));
        i++;
    }
    const digits = i - start;
    while (i < n && strIsSpace(s.charCodeAt(i)))
        i++;
    // Trailing garbage, or a sign with no digits after it. A bare '' or all-whitespace is `0n`, which
    // is why the emptiness test is on `digits` only when something else was actually consumed.
    if (i < n || (digits === 0 && start > 0))
        throw new Error('Cannot convert ' + s + ' to a BigInt');
    return neg ? -result : result;
}
export function bigToNumber(a) {
    const raw = a;
    const neg = (raw[raw.length - 1] & 0x80000000) !== 0;
    const limbs = bigApplySign(raw, neg);
    let result = 0;
    let scale = 1;
    for (let i = 0; i < limbs.length; i++) {
        result = result + limbs[i] * scale;
        scale = scale * 4294967296;
    }
    if (neg)
        return -result;
    return result;
}
// The `i`th 32-bit word of `a`'s two's complement, past its limbs its sign: what a 64-bit typed-array element stores, two of them.
export function bigWord(a, i) {
    const raw = a;
    return i < raw.length ? raw[i] : bigSign(raw) ? 0xffffffff : 0;
}
function bigSign(a) {
    return (a[a.length - 1] & 0x80000000) !== 0;
}
// The low `bits` of `a`'s two's complement (past its limbs, its sign), read as signed or unsigned: the top limb is shifted up
// and back, arithmetically or logically, and one more limb holds the result's sign for `bigTrim` to keep or drop.
function bigTruncate(a, bits, signed) {
    const n = (bits + 31) >> 5;
    const shift = n * 32 - bits;
    const fill = bigSign(a) ? 0xffffffff : 0;
    const r = new RawArray(n + 1);
    for (let i = 0; i < n; i++) {
        const limb = i < a.length ? a[i] : fill;
        r[i] = limb;
    }
    if (n > 0) {
        const top = r[n - 1];
        r[n - 1] = signed ? (top << shift) >> shift : (top << shift) >>> shift;
        const high = r[n - 1];
        r[n] = signed && high >= 0x80000000 ? 0xffffffff : 0;
    }
    return bigTrim(r);
}
export function bigTrim(a) {
    let n = a.length;
    while (n > 1 && a[n - 1] === ((a[n - 2] & 0x80000000) !== 0 ? 0xffffffff : 0))
        n = n - 1;
    if (n === a.length)
        return a;
    const r = new RawArray(n);
    for (let i = 0; i < n; i++)
        r[i] = a[i];
    return r;
}
// `x`'s only call site (`toU32(b[i] ^ bx)`) already passes a genuine `i32` (`^`'s declared result type),
// so this takes/returns the real pseudo-types directly rather than `number` -- `i32`->`u32` is a free tag
// reinterpretation in backend.ts's `coerceTop` (wasm has no separate unsigned storage), so the body compiles
// to nothing but a return, and the caller's `number` context does one unsigned widen (`f64.convert_i32_u`)
// at the very end instead of a signed widen in and a truncate back out around a branch.
function toU32(x) {
    return x;
}
function bigAdd(a, b, negb) {
    const bx = negb ? 0xffffffff : 0;
    let carry = negb ? 1 : 0;
    const na = a.length;
    const nb = b.length;
    const n = na > nb ? na : nb;
    const at = bigSign(a) ? 0xffffffff : 0;
    const bt = bigSign(b) !== negb ? 0xffffffff : 0;
    const r = new RawArray(n + 1);
    for (let i = 0; i <= n; ++i) {
        const sum = (i < na ? a[i] : at) + (i < nb ? toU32(b[i] ^ bx) : bt) + carry;
        carry = sum > 0xffffffff ? 1 : 0;
        r[i] = sum & 0xffffffff;
    }
    return r;
}
function bigCompare(a, b) {
    // SIGN FIRST. These limbs are two's complement -- `bigToNumber` reads the sign off the top bit of the
    // highest limb -- so an unsigned walk gets every mixed-sign comparison wrong: `0n > -1n` was false,
    // because `0 < 0xffffffff` as unsigned. Every `<`/`>`/`<=`/`>=`/`==`/`!=` on bigints comes through
    // here, so that one line was wrong for all of them.
    const an = a.length > 0 && (a[a.length - 1] & 0x80000000) !== 0;
    const bn = b.length > 0 && (b[b.length - 1] & 0x80000000) !== 0;
    if (an !== bn)
        return an ? -1 : 1;
    // SIGN-EXTENDED, so this compares VALUES rather than representations. Length alone cannot decide it:
    // a `bigint` has two physical forms here -- a literal emits `i64.const`, the `BigInt` class holds
    // `RawArray<u32>` -- so the same number reaches this with different limb counts, and `BigInt(0) === 0n` was
    // false purely because one zero was one limb longer than the other.
    let i = a.length > b.length ? a.length : b.length;
    while (i--) {
        const av = i < a.length ? a[i] : (an ? 0xffffffff : 0);
        const bv = i < b.length ? b[i] : (bn ? 0xffffffff : 0);
        if (av !== bv)
            return av < bv ? -1 : 1;
    }
    return 0;
}
function bigNeg(a) {
    return bigAdd(new RawArray(1), a, true);
}
function bigApplySign(a, neg) {
    if (neg)
        return bigNeg(a);
    return a;
}
// Unsigned magnitude multiply (`mul`'s sign is handled by its caller). Schoolbook/operand-scanning, one exact 32x32->64 product
// per limb pair (`mulLo`/`mulHi`).
function bigMulMag(a, b) {
    const na = a.length;
    const nb = b.length;
    const r = new RawArray(na + nb + 1);
    for (let i = 0; i < na; i++) {
        let carry = 0;
        let j = 0;
        while (j < nb) {
            // Each limb bound to its own `number` local FIRST -- the idiom this file's header describes,
            // and the reason for it: two limb reads added directly are both `u32`-kinded, so the add is
            // done in `i32` and WRAPS. `t` then went negative, `Math.floor(t / 2^32)` gave -1 instead of
            // 0, and the row lost a carry -- `1000000n * 1000000n` came out exactly 2^32 short.
            const acc = r[i + j];
            const lo = mulLo(a[i], b[j]);
            const hi = mulHi(a[i], b[j]);
            const t = acc + lo + carry;
            r[i + j] = t & 0xffffffff;
            carry = hi + Math.floor(t / 4294967296);
            j = j + 1;
        }
        // Flushes the row's leftover carry into the columns above it -- a ripple, not a single add, since
        // a column here can receive contributions from both this row's flush and the next row's own pass.
        for (let k = i + nb, c = carry; c > 0; ++k) {
            const at = r[k];
            const tf = at + c;
            r[k] = tf & 0xffffffff;
            c = Math.floor(tf / 4294967296);
        }
    }
    return r;
}
// `a >= b` by magnitude, MSB-first, where `a` may be longer than `b` (`bigDivModMag`'s remainder buffer
// always carries one guard limb past the divisor's own length).
function bigGeMag(a, b) {
    const nb = b.length;
    let i = a.length;
    while (i > nb) {
        i = i - 1;
        if (a[i] !== 0)
            return true;
    }
    while (i--) {
        if (a[i] !== b[i])
            return a[i] > b[i];
    }
    return true;
}
// `a - b` by magnitude, assuming `a >= b` (no borrow past `a`'s own top limb) and `a.length >= b.length`.
function bigSubMag(a, b) {
    const n = a.length;
    const nb = b.length;
    const r = new RawArray(n);
    let borrow = 0;
    for (let i = 0; i < n; i++) {
        const t = a[i] - (i < nb ? b[i] : 0) - borrow;
        if (t < 0) {
            r[i] = t + 4294967296;
            borrow = 1;
        }
        else {
            r[i] = t;
            borrow = 0;
        }
    }
    return r;
}
// Shifts a non-negative magnitude left by one bit, inserting `bit` (0 or 1) at the LSB -- stays the same
// length as `a` (any overflow past the top limb is discarded), only ever used on `bigDivModMag`'s
// fixed-capacity remainder buffer, which is sized with enough guard headroom that the discarded bit is
// always 0 by construction (the remainder never exceeds twice the divisor, and the buffer holds one full
// extra limb beyond the divisor's own length).
function bigShl1(a, bit) {
    const n = a.length;
    const r = new RawArray(n);
    let carry = bit;
    for (let i = 0; i < n; i++) {
        const v = a[i];
        r[i] = ((v << 1) | carry) & 0xffffffff;
        carry = v >>> 31;
    }
    return r;
}
// Magnitude of `2^k`, with one guard limb above the set bit so it's unambiguously non-negative even when
// the set bit lands exactly on a limb's own top bit (e.g. `k=31` sets `0x80000000` in limb 0, which
// needs a zero limb 1 above it to still read as +2147483648, not -2147483648).
function bigPow2(k) {
    const limb = k >> 5;
    const r = new RawArray(limb + 2);
    r[limb] = 1 << (k & 0x1f);
    return r;
}
// Unsigned magnitude division (`div`/`mod`'s sign is handled by their caller): `mod ? a mod b : floor(a/b)`.
// Binary (bit-at-a-time) restoring division -- ~32x more iterations than a multi-limb quotient-digit
// estimate (Knuth's algorithm D), but nothing here needs a digit *estimate* (and the correction step
// that comes with one) -- each step's decision is an exact compare, so this is the version that's
// actually easy to get right.
function bigDivModMag(a, b, mod) {
    const na = a.length;
    const q = new RawArray(na);
    let r = new RawArray(b.length + 1);
    let bit = na * 32;
    while (bit--) {
        const limb = bit >> 5;
        const off = bit & 31;
        r = bigShl1(r, (a[limb] >>> off) & 1);
        if (bigGeMag(r, b)) {
            r = bigSubMag(r, b);
            q[limb] = q[limb] | (1 << off);
        }
    }
    return mod ? r : q;
}
export class BigInt {
    // A REAL conversion, not a placeholder: `BigInt(5)` is a call, and towasm lowers a call on a class to
    // its constructor, so a constructor that ignored `value` silently produced zero for every input.
    // The `as unknown as` is for tsc's benefit only -- towasm reads the last statement's type with the
    // casts stripped, so `bigFromNumber`'s own `bigint` is what determines this class's physical form
    // (a `RawArray<u32>`, the same representation the arithmetic below reinterprets `this` as).
    // @ts-expect-error - tison extension: multiple constructor implementations
    constructor(value) {
        return value;
    }
    // @ts-expect-error - tison extension: multiple constructor implementations
    constructor(value) {
        return bigFromString(value);
    }
    // @ts-expect-error - tison extension: multiple constructor implementations
    constructor(value) {
        return bigFromNumber(value);
    }
    // @ts-expect-error - tison extension: multiple constructor implementations
    constructor(value) {
        return bigFromNumber(value ? 1 : 0);
    }
    // TS's own signature: one argument of any of the four, told apart at run time (`BigInt(v)` with `v: number | bigint`).
    // @ts-expect-error - tison extension: multiple constructor implementations
    constructor(value) {
        return (typeof value === 'bigint' ? value
            : typeof value === 'number' ? bigFromNumber(value)
                : typeof value === 'string' ? bigFromString(value)
                    : bigFromNumber(value ? 1 : 0));
    }
    static asIntN(bits, int) { return bigTruncate(int, bits, true); }
    static asUintN(bits, int) { return bigTruncate(int, bits, false); }
    valueOf() { return this; }
    //	static readonly [Symbol.toStringTag]: "BigInt";
    neg() {
        return bigTrim(bigNeg(this));
    }
    add(b) {
        return bigTrim(bigAdd(this, b, false));
    }
    sub(b) {
        return bigTrim(bigAdd(this, b, true));
    }
    mul(b) {
        const av = this;
        const bv = b;
        const nega = bigSign(av);
        const negb = bigSign(bv);
        return bigTrim(bigApplySign(bigMulMag(bigApplySign(av, nega), bigApplySign(bv, negb)), nega !== negb));
    }
    div(b) {
        const av = this;
        const bv = b;
        const nega = bigSign(av);
        const negb = bigSign(bv);
        return bigTrim(bigApplySign(bigDivModMag(bigApplySign(av, nega), bigApplySign(bv, negb), false), nega !== negb));
    }
    mod(b) {
        const av = this;
        const bv = b;
        const nega = bigSign(av);
        const negb = bigSign(bv);
        return bigTrim(bigApplySign(bigDivModMag(bigApplySign(av, nega), bigApplySign(bv, negb), true), nega));
    }
    // `this << b` -- `b` is itself a `bigint` (real TS only allows shifting a `bigint` by a `bigint`),
    // converted via `bigToNumber` since a shift count too large for that to round-trip exactly isn't a
    // realistic amount to shift by anyway. Reuses `mul` (`x << k` is exactly `x * 2^k`, for either sign)
    // rather than hand-rolling its own sign-extension.
    shl(b) {
        return this.mul(bigTrim(bigPow2(bigToNumber(b))));
    }
    // Arithmetic (signed) right shift -- `this >> b`, floor-rounding like real `bigint` `>>` (which
    // rounds toward -Infinity, *not* toward zero the way `div` does: `-5n >> 1n === -3n`, not `-2n`).
    // That's exactly what a bit-level shift with sign-extension from the top gives for free, so this
    // shifts limbs directly rather than going through `div`/`bigPow2`.
    shr_s(b) {
        const k = bigToNumber(b);
        const limbShift = k >>> 5;
        const bitShift = k & 31;
        const a = this;
        const na = a.length;
        const ext = bigSign(a) ? 0xffffffff : 0;
        const r = new RawArray(na);
        for (let i = 0; i < na; i++) {
            const srcLo = i + limbShift;
            const lo = srcLo < na ? a[srcLo] : ext;
            r[i] = bitShift === 0 ? lo : ((lo >>> bitShift) | ((srcLo + 1 < na ? a[srcLo + 1] : ext) << (32 - bitShift))) & 0xffffffff;
        }
        return bigTrim(r);
    }
    // Logical (unsigned) right shift -- real `bigint` has no `>>>` at all (arbitrary precision has no
    // fixed width to be unsigned *within*, so real JS throws). This library defines it anyway: shift the
    // current two's-complement bit pattern right, zero-filling from the top regardless of sign, treating
    // `this` as if it were a fixed-width unsigned integer exactly as wide as its own current limbs. One
    // guard limb above the result (unlike `shrs`) forces a non-negative read even when a negative input's
    // shifted-down bits leave the new top limb's own top bit set.
    shr_u(b) {
        const k = bigToNumber(b);
        const limbShift = k >>> 5;
        const bitShift = k & 31;
        const a = this;
        const na = a.length;
        const r = new RawArray(na + 1);
        for (let i = 0; i < na; i++) {
            const srcLo = i + limbShift;
            const lo = srcLo < na ? a[srcLo] : 0;
            r[0] = bitShift === 0 ? lo : ((lo >>> bitShift) | ((srcLo + 1 < na ? a[srcLo + 1] : 0) << (32 - bitShift))) & 0xffffffff;
        }
        return bigTrim(r);
    }
    // `&`/`|`/`^` limb-wise over the two's-complement bit patterns, each operand sign-extended to the
    // wider length plus one guard limb -- which is what makes the infinite sign extension real JS
    // specifies fall out for free, including for a negative operand. `toU32` because this compiler (like
    // JS) gives a bitwise op a *signed* 32-bit result even for unsigned-meaning limbs.
    static bitwise(a, b, op) {
        const na = a.length;
        const nb = b.length;
        const n = (na > nb ? na : nb) + 1;
        const aext = bigSign(a) ? 0xffffffff : 0;
        const bext = bigSign(b) ? 0xffffffff : 0;
        const r = new RawArray(n);
        for (let i = 0; i < n; i++) {
            const x = i < na ? a[i] : aext;
            const y = i < nb ? b[i] : bext;
            r[i] = op === 0 ? toU32(x & y) : op === 1 ? toU32(x | y) : toU32(x ^ y);
        }
        return bigTrim(r);
    }
    and(b) { return BigInt.bitwise(this, b, 0); }
    or(b) { return BigInt.bitwise(this, b, 1); }
    xor(b) { return BigInt.bitwise(this, b, 2); }
    // `~x` inverts every bit of the infinite two's-complement pattern, which is `-x - 1`.
    not() {
        const a = this;
        const n = a.length;
        const r = new RawArray(n + 1);
        const ext = bigSign(a) ? 0xffffffff : 0;
        for (let i = 0; i < n + 1; i++)
            r[i] = toU32(~(i < n ? a[i] : ext));
        return bigTrim(r);
    }
    // Exponentiation by squaring. A negative exponent is a RangeError in real JS; there is no useful
    // integer answer, so it comes back as zero rather than looping forever.
    pow(b) {
        let e = bigToNumber(b);
        if (e < 0)
            return bigFromNumber(0);
        let base = this;
        let result = bigFromNumber(1);
        while (e > 0) {
            if ((e & 1) !== 0)
                result = result.mul(base);
            base = base.mul(base);
            e = Math.floor(e / 2);
        }
        return result;
    }
    // -1/0/1, comparing by magnitude.
    compare(b) {
        return bigCompare(this, b);
    }
    // `<`/`>`/`<=`/`>=`/`==`/`!=` on two `bigint`s all lower to one of these (see backend.ts's
    // `BIGINT_OPS`) -- each just wraps `compare` rather than re-walking the limbs, so the actual
    // comparison logic exists exactly once.
    lt(b) { return this.compare(b) < 0; }
    gt(b) { return this.compare(b) > 0; }
    le(b) { return this.compare(b) <= 0; }
    ge(b) { return this.compare(b) >= 0; }
    eq(b) { return this.compare(b) === 0; }
    ne(b) { return this.compare(b) !== 0; }
    toString(radix) {
        const self = this;
        // Zero has no digits to walk, so the loop below produced '' for it rather than '0'.
        if (self === 0n)
            return '0';
        // A NEGATIVE walks its own magnitude and prefixes '-': the digit loop below is `i > 0`, so
        // anything negative came back as '' too.
        if (self < 0n)
            return '-'.concat((-self).toString(radix));
        let s = '';
        const radixb = radix ? bigFromNumber(radix) : 10n;
        for (let i = self; i > 0; i /= radixb) {
            const d = Number(i % radixb);
            // LOWERCASE above 9, matching JS -- and `Number.prototype.toString`, which had the same bug.
            s = String.fromCharCode(d < 10 ? 48 + d : 97 + d - 10).concat(s);
        }
        return s;
    }
}
