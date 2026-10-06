/* eslint-disable @typescript-eslint/no-this-alias */
import * as TS from './ts-parser';
import * as JS from './js-parser';
import { Literal, hasMod } from '@isopodlabs/tison/ast';
import { Expr, BindingTarget } from './js-parser';
import { Type } from './ts-parser';
import { walker, walkerB, WalkerB } from './walker';
import { printer } from './printer';

// The type model shared by every source language, in TypeScript's vocabulary. What a language's runtime adds to it
// comes from the `Semantics` its root `Scope` carries; `type-utils.ts` is TypeScript's.

// ===================================================================
//  Type names and well-known types
// ===================================================================

const _PRIMITIVES		= ['number', 'string', 'symbol', 'boolean', 'bigint', 'undefined', 'object', 'never', 'void', 'null'] as const;
type PRIMITIVES			= (typeof _PRIMITIVES)[number];

class TypeSet<T extends string> {
	set;
	constructor(public values: ReadonlyArray<T>) {
		this.set = new Set<string>(values);
	}
	has(name: string): name is T {
		return this.set.has(name);
	}
	or<U extends string>(other: TypeSet<U>): TypeSet<T | U> {
		return new TypeSet([...this.values, ...other.values]);
	}
}

const KEY_TYPES			= new TypeSet(['number', 'string', 'symbol']);
export const LITERAL_PRIMITIVES	= new TypeSet(['string', 'number', 'boolean', 'bigint']);
export const SIMPLE_TYPES		= new TypeSet(['number', 'string', 'symbol', 'boolean', 'bigint', 'undefined']);
const PRIMITIVE_DOMAINS	= SIMPLE_TYPES.or(new TypeSet(['null']));
const PRIMITIVES		= new TypeSet(_PRIMITIVES);
const TOP_TYPES			= new TypeSet(['any', 'unknown']);
export const INTRINSIC_TYPES	= PRIMITIVES.or(TOP_TYPES);


const OPAQUE		= new Set(['keyof', 'indexed_access', 'conditional', 'infer', 'mapped', 'this', 'predicate']);

// The subset of `OPAQUE` that is a genuinely unevaluated computation (`this`/`predicate` are opaque by design): under `strict`, either side
// being one fails the comparison instead of passing it.
const OPAQUE_GAP	= new Set(['keyof', 'indexed_access', 'conditional', 'infer', 'mapped']);

export const NUMBER		= TS.RefType('number');
export const STRING		= TS.RefType('string');
export const BOOLEAN	= TS.RefType('boolean');
export const BIGINT		= TS.RefType('bigint');
export const REGEXP		= TS.RefType('RegExp');
export const ANY		= TS.RefType('any');
export const VOID		= TS.RefType('void');
export const UNDEFINED	= TS.RefType('undefined');
export const NEVER		= TS.RefType('never');
export const UNKNOWN	= TS.RefType('unknown');
export const NUMERIC	= TS.UnionType([NUMBER, BIGINT]);

// ===================================================================
//  Keys: printed types, expression paths, member and binding names
// ===================================================================

export const tocode = printer({newline:'', indent:'', spaceAfterColon: false, spaceAfterComma: false, spaceAroundOps: false});
// For messages: `typeKey` is an identity key, and a fluent builder's type prints exponentially larger than it is.
export const show		= () => printer({ typeBudget: 4096 });
export const showType	= (t: Type) => show().type(t);
export function typeKey(t: Type) { return tocode.type(t); }

// A type's structural identity, linear in its DAG where `typeKey` prints the tree: a type naming a part twice at each of n steps
// (`B<T & F<T>>`, chained) prints 2^n of it. Two independent 53-bit hashes over what `typeKey` prints, memoized on the node.
// What `typeKey` never prints: scopes, origins, freshness, and the checker's stamps on AST nodes inside a type (a default's `checkedType`).
const UNPRINTED	= new Set(['declScope', 'origin', 'fresh', 'frozen', 'pos', 'scope', 'memo', 'checkedType', 'checkedCall', 'contextualType',
	'flowSlot', 'flowType', 'instanceOf', 'inferredReturn', 'testedForAbsence', 'expectedType']);
// Memoized ON the node, under symbols `Object.keys` never lists: a WeakMap entry per node cost more than the node itself.
const TYPE_ID	= [Symbol('typeId'), Symbol('scopedTypeId')];
const scopeIds	= new WeakMap<Scope, number>();
let nextScopeId	= 0;
// `scoped`: declaration scopes count too, each by identity -- equal ids then RESOLVE equally (`resolve`'s structural cache).
export function typeId(t: Type, scoped = false): string {
	const memo	= TYPE_ID[+scoped];
	const known	= (t as Record<symbol, string | undefined>)[memo];
	if (known !== undefined)
		return known;
	const scopeId = (sc: Scope) => scopeIds.get(sc) ?? (scopeIds.set(sc, nextScopeId), nextScopeId++);
	// A string is length-prefixed, so no content can read as structure.
	const part = (v: unknown): string => typeof v === 'bigint' ? `${v}n` : typeof v === 'string' ? `${v.length}"${v}` : typeof v !== 'object' || v === null ? String(v)
		: Array.isArray(v) ? `[${v.map(part).join(',')}]`
		: v instanceof Scope ? (scoped ? `$${scopeId(v)}` : '')
		: typeof (v as { type?: unknown }).type === 'string' ? `#${typeId(v as Type, scoped)}`
		: `{${fields(v).join(',')}}`;
	const fields = (o: object) => Object.keys(o).filter(k => !(scoped && k === 'declScope' ? false : UNPRINTED.has(k)) && typeof (o as Record<string, unknown>)[k] !== 'function').sort()
		.map(k => `${k}:${part((o as Record<string, unknown>)[k])}`);
	// A node reached again while its own id is computed (`f` returning `f`) reads as a provisional id unique to it, which ends the cycle.
	Object.defineProperty(t, memo, { value: `~${++cyclicIds}`, configurable: true });
	const sig	= fields(t).join(';') + (scoped ? '' : declaredAs(t));
	const id	= `${hash53(sig, 0).toString(36)}.${hash53(sig, 0x9e3779b9).toString(36)}`;
	Object.defineProperty(t, memo, { value: id });
	return id;
}
let cyclicIds = 0;
// A stamped ref is also WHAT it names, by identity: two modules' same-spelled classes (binary's sync and async `_stream`) are two types,
// while refs to one class from different modules stay one. An unstamped ref names whatever its reader's scope does.
const declIds	= new WeakMap<object, number>();
let nextDeclId	= 0;
function declaredAs(t: Type): string {
	if (t.type !== 'ref' || !t.declScope || INTRINSIC_TYPES.has(t.name))
		return '';
	const [ns, last] = (t.declScope as Scope).qualified(t.name);
	const target: object | undefined = ns?.classDecl(last) ?? ns?.type(last);
	return target ? `@${declIds.get(target) ?? (declIds.set(target, nextDeclId), nextDeclId++)}` : '';
}
// cyrb53: a well-mixed 53-bit string hash.
function hash53(str: string, seed: number): number {
	let h1 = 0xdeadbeef ^ seed, h2 = 0x41c6ce57 ^ seed;
	for (let i = 0; i < str.length; i++) {
		const ch = str.charCodeAt(i);
		h1 = Math.imul(h1 ^ ch, 2654435761);
		h2 = Math.imul(h2 ^ ch, 1597334677);
	}
	h1 = Math.imul(h1 ^ (h1 >>> 16), 2246822507) ^ Math.imul(h2 ^ (h2 >>> 13), 3266489909);
	h2 = Math.imul(h2 ^ (h2 >>> 16), 2246822507) ^ Math.imul(h1 ^ (h1 >>> 13), 3266489909);
	return 4294967296 * (2097151 & h2) + (h1 >>> 0);
}
export function exprKey(e: Expr) { return tocode.expression(e); }

// A stable key for narrowing a property chain (`a.b.c`), in the scope's narrowings map beside plain names (a dotted key collides with no binding).
export function pathKey(e: Expr): string | undefined {
	switch (e.type) {
		case 'identifier':	return e.name;
		case 'this':		return 'this';
		// `x!` names `x`'s storage, as TS's reference matching skips a non-null assertion.
		case 'unary_post':	return e.operator === '!' ? pathKey(e.operand) : undefined;
		case 'member': {
			const k = pathKey(e.object);
			return k && k + '.' + e.property;
		}
		// A literal index names one element, so `a[0].k` is as stable a path as `a.b.k`; so does a NAMED one (`a[i]`, TS 5.5) until `i` is assigned
		// (the checker's `forgetPathsThrough`). Any other computed index may evaluate differently between the guard and the read.
		case 'index': {
			const k = pathKey(e.object);
			if (k === undefined)
				return undefined;
			if (e.index.type === 'identifier')
				return `${k}[${e.index.name}]`;
			const v = e.index.type === 'literal' ? e.index.value : undefined;
			return typeof v === 'number' ? `${k}[${v}]` : typeof v === 'string' ? `${k}["${v}"]` : undefined;
		}
		default:			return undefined;
	}
}

// A member key's static name: a string key as written, a literal computed key as its value, and one naming an entity
// (`[Symbol.iterator]`) by that path, spelled as TS prints it. Any other computed key has no static name.
export function memberKey(key: JS.Key<Type>): string | undefined {
	if (typeof key !== 'object')
		return String(key);
	const e = key.computed;
	if (e.type === 'literal' && (typeof e.value === 'string' || typeof e.value === 'number'))
		return String(e.value);
	const path = e.type === 'identifier' || e.type === 'member' ? pathKey(e) : undefined;
	return path && `[${path}]`;
}

export function bindingNames(t: BindingTarget): string[] {
	return typeof t === 'string' ? [t]
		: t.type === 'object_pattern' ? [...t.properties.flatMap(p => bindingNames(p.value)), ...(t.rest ? [t.rest] : [])]
		: [...t.elements.flatMap(e => e ? bindingNames(e.target) : []), ...(t.rest ? bindingNames(t.rest) : [])];
}

// ===================================================================
//  Shallow tests (no resolution)
// ===================================================================

export function isRef<T extends string>(t: Type, name: T): t is TS.RefType<T>							{ return t.type === 'ref' && t.name === name; }
export function isRefOf<T extends string>(t: Type, set: { has: (n: T)=> boolean }): t is TS.RefType<T>	{ return t.type === 'ref' && set.has(t.name as any); }

export function isPrimitive(t: Type){ return t.type === 'ref' && PRIMITIVES.has(t.name); }
export function isKeyable(t: Type)	{ return t.type === 'ref' && KEY_TYPES.has(t.name); }
export function isAny(t: Type)		{ return t.type === 'ref' && TOP_TYPES.has(t.name); }
export function isBoolean(t: Type)	{ return isRef(t, 'boolean'); }
export function isString(t: Type)	{ return isRef(t, 'string'); }

function isNullOrUndefined(t: Type): boolean {
	return t.type === 'literal' ? t.value === null : t.type === 'ref' && (t.name === 'null' || t.name === 'undefined');
}

// ===================================================================
//  Literals and widening
// ===================================================================

interface TypeOfMap {
	string: string;	number: number;	boolean: boolean;
	bigint: string; symbol: string; object: string; undefined: string; function: string;
	null:		null;
	template:	JS.TemplatePart<Type>[]
}

export function literalType(t: Literal<any>) {
	return Array.isArray(t.value) ? 'string' : t.value === null ? 'null' : typeof t.value;
}
export function isLiteral<K extends keyof TypeOfMap>(t: Type|Expr, type: K): t is Literal<TypeOfMap[K]> {
	return t.type === 'literal' && literalType(t) === type;
}

// A string literal's text, as a property key: a template counts only without substitutions (its parts' text); any other is `undefined`.
export function literalString(t: Type|Expr): string | undefined {
	if (t.type !== 'literal')
		return undefined;
	if (typeof t.value === 'string')
		return t.value;
	if (!Array.isArray(t.value))
		return undefined;
	const parts: readonly JS.TemplatePart<unknown>[] = t.value;
	let text = '';
	for (const p of parts) {
		if (p.exp)
			return undefined;
		text += p.str;
	}
	return text;
}

// The property a literal key type names: a number names the key it prints as (`T[1]` is `T["1"]`).
export function literalKey(t: Type): string | undefined {
	return t.type === 'literal' && typeof t.value === 'number' ? String(t.value)
		: t.type === 'range' && t.base === 'number' && t.min !== undefined && t.min === t.max ? String(t.min)
		: literalString(t);
}

// The possible values of a pure literal or union of literals (a real discriminant, e.g. `type: 'method'|'get'|'set'`);
// `undefined` for anything wider, meaning "no signal".
export function literalValues(t: Type): unknown[] | undefined {
	return t.type === 'literal' ? [t.value]
		: t.type === 'union' && t.types.every((m): m is Literal<string | number | boolean | null | JS.TemplatePart<Type>[]> => m.type === 'literal') ? t.types.map(m => m.value)
		: undefined;
}

// Deep: literal element and property types nested in an array or object widen too, as TS widens a fresh literal's members; a `frozen` leaf
// (`as const`) stays at any depth. `ignoreFrozen`: for a physical representation, where a frozen `'foo'` is stored as any other.
const widenCache = new Map<number, WeakMap<Type, Type>>();
// `shallow`: only the value's own literal (or union of them) widens. Memoized per type object and flags: a DAG rewritten once per node.
export function widenLiterals(t: Type, keepBoolean = false, ignoreFrozen = false, shallow = false): Type {
	const flags = (keepBoolean ? 1 : 0) | (ignoreFrozen ? 2 : 0) | (shallow ? 4 : 0);
	let cache = widenCache.get(flags);
	if (!cache)
		widenCache.set(flags, cache = new WeakMap());
	let r = cache.get(t);
	if (!r)
		cache.set(t, r = widen(t, keepBoolean, ignoreFrozen, shallow));
	return r;
}
function widen(t: Type, keepBoolean: boolean, ignoreFrozen: boolean, shallow: boolean): Type {
	return	(t.type === 'literal' || t.type === 'range') && t.frozen && !ignoreFrozen ? t
		:	t.type === 'literal' && t.value !== null && (!keepBoolean || typeof t.value !== 'boolean')
			&& (t.fresh || ignoreFrozen || typeof t.value === 'number' || typeof t.value === 'bigint') ? TS.RefType(literalType(t))
		:	t.type === 'range' ? TS.RefType(t.base)
		:	t.type === 'union' ? combineTypes(t.types.map(m => widenLiterals(m, keepBoolean, ignoreFrozen, shallow)))
		:	shallow ? t
		:	t.type === 'array' ? TS.ArrayType(widenLiterals(t.element, keepBoolean, ignoreFrozen), t.readonly)
		:	t.type === 'object' ? TS.ObjectType(t.members.map(m => m.type === 'property' ? TS.TypeProperty(m.key, widenLiterals(m.typeAnnotation, keepBoolean, ignoreFrozen), m.modifiers, m.writeType) : m))
		:	t;
}

// `widenLiterals`' inverse shape: every literal/range leaf marked `frozen`, as an `as const` assertion makes it.
export function freeze(t: Type): Type {
	return	t.type === 'literal' || t.type === 'range' ? { ...t, frozen: true }
		:	t.type === 'union' ? TS.UnionType(t.types.map(freeze))
		:	t.type === 'array' ? TS.ArrayType(freeze(t.element), t.readonly)
		:	t.type === 'object' ? TS.ObjectType(t.members.map(m => m.type === 'property' ? TS.TypeProperty(m.key, freeze(m.typeAnnotation), m.modifiers) : m))
		:	t;
}

// ===================================================================
//  Numeric ranges
// ===================================================================

// How much is known about a number/bigint value, for `narrow()`'s relational and equality handling: `min`/`max` undefined is unbounded on that
// side; `integer` (always true for `bigint`) means never a fraction nor -0, what an `i32` holds.
export interface NumRange { base: 'number' | 'bigint'; min?: number | bigint; max?: number | bigint; integer: boolean }

export const isIntValue	= (v: number) => Number.isInteger(v) && !Object.is(v, -0);
const holdsNegative	= (r: NumRange) => r.min === undefined || r.min < 0;

// A machine type: what an application of the lib's `Int<Bits, Signed>` or `Float<Bits>` denotes.
export type Machine = 'i8' | 'u8' | 'i16' | 'u16' | 'i32' | 'u32' | 'i64' | 'u64' | 'f32' | 'f64';

// The lib's `Int`/`Float`, declared in the ROOT scope (the lib's), have their meaning built in, as TS's `intrinsic` aliases do; a user's `Int` is an alias.
const isIntrinsic = (name: string, scope: Scope) => (name === 'Int' || name === 'Float') && scope.typeDeclaredIn(name) === scope.root();

function intrinsicMachine(name: string, args: readonly Type[] | undefined): Machine | undefined {
	const arg		= (i: number) => { const a = args?.[i]; return a?.type === 'literal' ? a.value : undefined; };
	const bits		= arg(0), signed = arg(1);
	return name === 'Int' && (bits === 8 || bits === 16 || bits === 32 || bits === 64) && typeof signed === 'boolean' ? `${signed ? 'i' : 'u'}${bits}` as const
		: name === 'Float' && (bits === 32 || bits === 64) ? `f${bits}` as const
		: undefined;
}

// The machine type `t` names: its alias chain from its declaration to an `Int`/`Float` application, by DECLARATION, never by name. Follows
// aliases only, resolving nothing, so it is safe while declarations are still being hoisted.
export function machineOf(t: Type, scope: Scope, depth = 8): Machine | undefined {
	if (t.type !== 'ref' || depth < 0 || INTRINSIC_TYPES.has(t.name))
		return undefined;
	const [ns, name]	= declScopeOf(t, scope).qualified(t.name);
	const entry			= ns?.type(name);
	return !ns || !entry ? undefined
		: isIntrinsic(name, ns) ? intrinsicMachine(name, t.typeArgs)
		: !entry.typeParams?.length && entry.type.type === 'ref' ? machineOf(entry.type, ns, depth - 1)
		: undefined;
}

// What a value in a machine type's slot can hold. Above 53 bits a value is a `bigint`: a `number` cannot hold it exactly.
export function machineRange(m: Machine): NumRange {
	if (m[0] === 'f')
		return { base: 'number', integer: false };
	const bits = Number(m.slice(1));
	if (bits > 53) {
		const b = BigInt(bits);
		return m[0] === 'i' ? { base: 'bigint', integer: true, min: -(2n ** (b - 1n)), max: 2n ** (b - 1n) - 1n } : { base: 'bigint', integer: true, min: 0n, max: 2n ** b - 1n };
	}
	return m[0] === 'i'
		? { base: 'number', integer: true, min: -(2 ** (bits - 1)), max: 2 ** (bits - 1) - 1 }
		: { base: 'number', integer: true, min: 0, max: 2 ** bits - 1 };
}

// Reduces any resolved numeric-ish `Type` to a `NumRange`, or `undefined` if `t` isn't one at all.
export function toRange(t?: Type): NumRange | undefined {
	if (t) {
		if (t.type === 'range')
			return { base: t.base, min: t.min, max: t.max, integer: t.base === 'bigint' || !!t.integer };
		if (t.type === 'literal' && typeof t.value === 'number')
			return { base: 'number', min: t.value, max: t.value, integer: isIntValue(t.value) };
		if (t.type === 'literal' && typeof t.value === 'bigint')
			return { base: 'bigint', min: t.value, max: t.value, integer: true };
		if (t.type === 'ref' && t.name === 'number')
			return { base: 'number', integer: false };
		if (t.type === 'ref' && t.name === 'bigint')
			return { base: 'bigint', integer: true };
	}
	return undefined;
}

// `toRange`'s inverse: a `Literal` for an exactly known number, a bare ref when nothing is known, else a `RangeType` (an exact bigint stays a range).
export function rangeToType(r: NumRange): Type;
export function rangeToType(r?: NumRange): Type | undefined;
export function rangeToType(r?: NumRange): Type | undefined {
	if (!r)
		return undefined;
	if (r.base === 'number') {
		return	r.min !== undefined && r.min === r.max ?  Literal(r.min as number)
			:	r.min !== undefined || r.max !== undefined || r.integer ?  TS.RangeType('number', r.min, r.max, r.integer)
			:	NUMBER;
	}
	return	r.min !== undefined || r.max !== undefined ? TS.RangeType('bigint', r.min, r.max)
		:	BIGINT;
}

// Intersects two same-based ranges; undefined when provably empty (a comparison contradicting what is known).
export function rangeIntersect(a: NumRange, b: NumRange): NumRange | undefined {
	if (a.base !== b.base)
		return undefined;
	const min = a.min === undefined ? b.min : b.min === undefined ? a.min : a.min > b.min ? a.min : b.min;
	const max = a.max === undefined ? b.max : b.max === undefined ? a.max : a.max < b.max ? a.max : b.max;
	if (min !== undefined && max !== undefined && min > max)
		return undefined;
	return { base: a.base, min, max, integer: a.integer || b.integer };
}

// Widens a range to cover both `a` and `b` -- the union counterpart of `rangeIntersect`. Same-base only.
export function rangeUnion(a: NumRange, b: NumRange): NumRange | undefined {
	if (a.base !== b.base)
		return undefined;
	return {
		base:	a.base,
		min:	a.min === undefined || b.min === undefined ? undefined : a.min < b.min ? a.min : b.min,
		max:	a.max === undefined || b.max === undefined ? undefined : a.max > b.max ? a.max : b.max,
		integer: a.integer && b.integer
	};
}

// Same-typed `number`/`bigint` arithmetic on a `number | bigint`-typed value, without mixing the two at the type level.
function negValue(v: number | bigint): number | bigint { return typeof v === 'bigint' ? -v : -v; }
function addValue(a: number | bigint, b: number | bigint): number | bigint { return typeof a === 'bigint' ? a + BigInt(b) : a + Number(b); }
function subValue(a: number | bigint, b: number | bigint): number | bigint { return typeof a === 'bigint' ? a - BigInt(b) : a - Number(b); }
function mulValue(a: number | bigint, b: number | bigint): number | bigint { return typeof a === 'bigint' ? a * BigInt(b) : a * Number(b); }
function divValue(a: number | bigint, b: number | bigint): number | bigint { return typeof a === 'bigint' ? a / BigInt(b) : a / Number(b); }
function minOfValues(vs: (number | bigint)[]): number | bigint { return vs.reduce((a, b) => a < b ? a : b); }
function maxOfValues(vs: (number | bigint)[]): number | bigint { return vs.reduce((a, b) => a > b ? a : b); }

// The range of `Math.max`/`Math.min` over values in each of `a`: each bound picked across all of them, unbounded if any is.
function rangeExtreme(a: NumRange[], pick: (vs: (number | bigint)[]) => number | bigint): NumRange | undefined {
	const bound = (vs: (number | bigint | undefined)[]) => vs.every(v => v !== undefined) ? pick(vs) : undefined;
	return a.length ? { base: a[0].base, min: bound(a.map(r => r.min)), max: bound(a.map(r => r.max)), integer: a.every(r => r.integer) } : undefined;
}
export function rangeMax(a: NumRange[]) { return rangeExtreme(a, maxOfValues); }
export function rangeMin(a: NumRange[]) { return rangeExtreme(a, minOfValues); }

// Whether `r`'s span may include `0`, as a plain `number`/`bigint` always may: truthiness of a narrowed numeric type.
export function rangeIncludesZero(r: { min?: number | bigint; max?: number | bigint }): boolean {
	return (r.min === undefined || r.min <= 0) && (r.max === undefined || r.max >= 0);
}

export function rangeClamp(a: NumRange, bound: number|bigint, isUpper: boolean, strict?: boolean): NumRange | undefined {
	if (isUpper) {
		if (strict && a.integer)
			--bound;
		if (a.min !== undefined && a.min > bound)
			return undefined;
		return {...a, max: a.max !== undefined && a.max < bound ? a.max : bound};
	} else {
		if (strict && a.integer)
			++bound;
		if (a.max !== undefined && a.max < bound)
			return undefined;
		return {...a, min: a.min !== undefined && a.min > bound ? a.min : bound};
	}
}

// Interval arithmetic over possibly-unbounded ranges, so `x + 1` for a bounded `x` stays bounded. An unbounded side
// of an operand leaves the result unbounded on that side too: a conservative over-approximation.
export function rangeUnOp(op: JS.unaryOps, a: NumRange): NumRange | undefined {
	const base	= a.base;
	const shift	= (d: number) => ({ base, integer: a.integer,
		min: a.min !== undefined ? addValue(a.min, d) : undefined,
		max: a.max !== undefined ? addValue(a.max, d) : undefined
	});
	switch (op) {
		case '+':	return a;
		case '-':	return {
			base, integer: a.integer && (base === 'bigint' || !rangeIncludesZero(a)),
			min: a.max !== undefined ? negValue(a.max) : undefined,
			max: a.min !== undefined ? negValue(a.min) : undefined
		};
		case '~':	return { base, integer: a.integer};
		case '++':	return shift(1);
		case '--':	return shift(-1);
	}
}

export function rangeBinOp(op: JS.binaryOps, a: NumRange, b: NumRange): NumRange | undefined {
	const base = a.base;
	if (b.base !== base)
		return undefined;

	function add(a: NumRange, b: NumRange): NumRange | undefined {
		return { base, integer: a.integer && b.integer,
			min: a.min !== undefined && b.min !== undefined ? addValue(a.min, b.min) : undefined,
			max: a.max !== undefined && b.max !== undefined ? addValue(a.max, b.max) : undefined };
	}
	function sub(a: NumRange, b: NumRange): NumRange | undefined {
		return { base, integer: a.integer && b.integer,
			min: a.min !== undefined && b.max !== undefined ? subValue(a.min, b.max) : undefined,
			max: a.max !== undefined && b.min !== undefined ? subValue(a.max, b.min) : undefined };
	}
	function mul(a: NumRange, b: NumRange): NumRange | undefined {
		const integer = a.integer && b.integer && (base === 'bigint' || !((rangeIncludesZero(a) && holdsNegative(b)) || (rangeIncludesZero(b) && holdsNegative(a))));
		if (a.min === undefined || a.max === undefined || b.min === undefined || b.max === undefined)
			return { base, integer };
		const corners = [mulValue(a.min, b.min), mulValue(a.min, b.max), mulValue(a.max, b.min), mulValue(a.max, b.max)];
		return { base, integer, min: minOfValues(corners), max: maxOfValues(corners) };
	}
	function div(a: NumRange, b: NumRange): NumRange | undefined {
		if (a.min === undefined || a.max === undefined || b.min === undefined || b.max === undefined || (b.min <= 0 && b.max >= 0))
			return { base, integer: base === 'bigint' };
		const corners = [divValue(a.min, b.min), divValue(a.min, b.max), divValue(a.max, b.min), divValue(a.max, b.max)];
		return { base, integer: base === 'bigint', min: minOfValues(corners), max: maxOfValues(corners) };
	}

	switch (op) {
		case '+':	return add(a, b);
		case '-':	return sub(a, b);
		case '*':	return mul(a, b);
		case '/':	return div(a, b);
		case '&':	case '|': case '^': case '<<': case '>>':
			return base === 'number' ? { base, integer: true, min: -0x80000000, max: 0x7fffffff} : {base, integer: true};
		case '>>>':
			return base === 'number' ? { base, integer: true, min: 0, max: 0xffffffff} : {base, integer: true};
	}
}

// The machine-int limits a counter may sit in: i32, then i64.
const machineLimits = (base: NumRange['base']): [number | bigint, number | bigint][] => base === 'bigint'
	? [[-(2n ** 31n), 2n ** 31n - 1n], [-(2n ** 63n), 2n ** 63n - 1n]]
	: [[-(2 ** 31), 2 ** 31 - 1], [-(2 ** 63), 2 ** 63 - 1]];
const withinLimit = (r: NumRange, [lo, hi]: [number | bigint, number | bigint]) => r.min !== undefined && r.max !== undefined && r.min >= lo && r.max <= hi;

// `r + delta` for a step (`++`, `+= a`, `-= a`): by the user's rule it never overflows the machine int both `r` and `delta` fit,
// so a bound crossing that limit stops at it.
export function rangeStep(r: NumRange, delta: NumRange): NumRange | undefined {
	const sum	= rangeBinOp('+', r, delta);
	const limit	= r.integer && delta.integer ? machineLimits(r.base).find(l => withinLimit(r, l) && withinLimit(delta, l)) : undefined;
	return sum && limit ? { ...sum, min: sum.min! < limit[0] ? limit[0] : sum.min, max: sum.max! > limit[1] ? limit[1] : sum.max } : sum;
}

// A loop head's range `next` against the previous head's `prev`: a bound still moving jumps to the next machine limit, else to
// unbounded, so iteration terminates. Integer ranges only have limits worth stopping at.
export function rangeWiden(prev: NumRange, next: NumRange): NumRange {
	const limits	= next.integer ? machineLimits(next.base) : [];
	const up		= (p?: number | bigint, n?: number | bigint) => p === undefined || n === undefined || n <= p ? n : limits.find(([, hi]) => n <= hi)?.[1];
	const down		= (p?: number | bigint, n?: number | bigint) => p === undefined || n === undefined || n >= p ? n : limits.find(([lo]) => n >= lo)?.[0];
	return { ...next, min: down(prev.min, next.min), max: up(prev.max, next.max) };
}

// ===================================================================
//  Building unions and intersections
// ===================================================================

// `types` with every nested union (or intersection) spread into its members, as written -- nothing is resolved.
export function flatParts(types: readonly Type[], kind: 'union' | 'intersection'): Type[] {
	return types.flatMap(t => (t.type === 'union' || t.type === 'intersection') && t.type === kind ? flatParts(t.types, kind) : [t]);
}

// The first of `types` with each `key`.
function dedupe(types: Type[], key: (t: Type) => unknown): Type[] {
	const seen = new Set<unknown>();
	return types.filter(t => {
		const k = key(t);
		return !seen.has(k) && !!seen.add(k);
	});
}

// De-dupes structurally-identical types and folds what's left into a `union`
export function combineTypes(types: Type[]): Type {
	const seen = new Map<string, number>();
	const unique: Type[] = [];
	// `never` is a union's identity element, and left in it makes the union unanswerable ("one owner or many"), as `unionMembers` also drops it.
	for (const t of flatParts(types, 'union').filter(t => !isRef(t, 'never'))) {
		const key = typeId(t);
		const at = seen.get(key);
		if (at === undefined) {
			seen.set(key, unique.length);
			unique.push(t);
		} else if (t.type === 'literal' && t.fresh) {
			unique[at] = t;	// a fresh twin is kept: it widens, as TS keeps the fresh one
		}
	}
	// TS's removeRedundantLiteralTypes: a literal (or one of this checker's ranges) whose primitive is a member adds nothing.
	const primitives = new Set<string>(unique.flatMap(t => t.type === 'ref' && !t.typeArgs && LITERAL_PRIMITIVES.has(t.name) ? [t.name] : []));
	if (primitives.size) {
		const redundant = (t: Type) => t.type === 'literal' ? t.value !== null && primitives.has(literalType(t)) : t.type === 'range' && primitives.has(t.base);
		for (let i = unique.length; i--; )
			if (redundant(unique[i]))
				unique.splice(i, 1);
	}
	// One base's intervals are their hull, as a flow join merges them: a representation holds one range. A degenerate range is a literal and stays apart.
	for (const base of ['number', 'bigint'] as const) {
		const at = unique.flatMap((t, i) => t.type === 'range' && t.base === base && !t.frozen && t.min !== t.max ? [i] : []);
		if (at.length > 1) {
			unique[at[0]] = rangeToType(at.map(i => toRange(unique[i])!).reduce((a, b) => rangeUnion(a, b)!));
			for (const i of at.slice(1).reverse())
				unique.splice(i, 1);
		}
	}
	// TS's union reduction: `any` absorbs every member, `unknown` every member but `any`.
	return	unique.some(t => isRef(t, 'any')) ? ANY
		:	unique.some(t => isRef(t, 'unknown')) ? UNKNOWN
		:	!unique.length ? NEVER : unique.length === 1 ? unique[0] : TS.UnionType(unique);
}

// What an instantiation owes a rebuilt union or intersection (flattened, `never` dropped from a union, `any` absorbing, `unknown` dropped from an
// intersection), without `combineTypes`' structural dedupe, which costs as much as the types are large.
function reduceInstantiated(t: TS.UnionType | TS.IntersectionType): Type {
	const flat = flatParts(t.types, t.type);
	if (flat.some(m => isRef(m, 'any')))
		return ANY;
	// An intersection holding `never` IS `never`, as TS reduces it, so a phantom parameter (`string & { hack?: P & never }`) infers nothing for `P`.
	if (t.type === 'intersection' && flat.some(m => isRef(m, 'never')))
		return NEVER;
	const kept = t.type === 'union'
		? (flat.some(m => isRef(m, 'unknown')) ? [UNKNOWN] : flat.filter(m => !isRef(m, 'never')))
		: flat.filter(m => !isRef(m, 'unknown'));
	return !kept.length ? (t.type === 'union' ? NEVER : UNKNOWN) : kept.length === 1 ? kept[0]
		: kept.length === t.types.length && kept.every((m, i) => m === t.types[i]) ? t
		: t.type === 'union' ? TS.UnionType(kept) : TS.IntersectionType(kept);
}

export function optional(type:Type, optional?: boolean) {
	return optional ? combineTypes([type, UNDEFINED]) : type;
}

export function intersectTypes(types: Type[]): Type {
	if (types.length === 1)
		return types[0];
	const unique = dedupe(flatParts(types, 'intersection'), t => typeId(t));
	// TS's intersection reduction: `any` absorbs every member.
	return unique.some(t => isRef(t, 'any')) ? ANY : unique.length === 1 ? unique[0] : TS.IntersectionType(unique);
}

// Declaration merging's intersect: deduped by IDENTITY only, as TS merges declarations without resolving their members. `intersectTypes`'
// `typeKey` dedupe would force a class's lazily inferred field types mid-`hoist`.
export function joinTypes(types: Type[]): Type {
	const parts = dedupe(flatParts(types, 'intersection'), t => t);
	return parts.length === 1 ? parts[0] : TS.IntersectionType(parts);
}

// The `object` parts of an intersection merged into one flat `object`, other parts kept beside it. A key in several parts intersects its types,
// optional only if every part says so, readonly if any does.
export function mergeIntersection(t: Type): Type {
	if (t.type !== 'intersection')
		return t;

	const nonObject:	Type[] = [];
	const otherMembers: TS.TypeMember[] = [];
	const byKey = new Map<string, { types: Type[]; optional: boolean; readonly: boolean }>();

	for (const part of flatParts([t], 'intersection')) {
		if (part.type === 'object') {
			for (const m of part.members) {
				const name = m.type === 'property' ? JS.keyName(m.key) : undefined;
				if (m.type === 'property' && name !== undefined) {
					const entry = byKey.get(name) ?? { types: [], optional: true, readonly: false };
					entry.types.push(m.typeAnnotation);
					entry.optional &&= hasMod(m, 'optional');
					entry.readonly ||= hasMod(m, 'readonly');
					byKey.set(name, entry);
				} else {
					otherMembers.push(m);
				}
			}
		} else if (part.type === 'function') {
			otherMembers.push({ ...part, type: 'call' });
		} else {
			nonObject.push(part);
		}
	}

	return intersectTypes([TS.ObjectType([
		...[...byKey].map(([key, { types, optional, readonly }]): TS.TypeMember => {
			const modifiers = [...(optional ? ['optional'] : []), ...(readonly ? ['readonly'] : [])];
			return TS.TypeProperty(key, intersectTypes(types), modifiers.length ? modifiers : undefined);
		}),
		...otherMembers,
	]), ...nonObject]);
}

// ===================================================================
//  Declaring scopes of types
// ===================================================================

export function withScope<T extends {declScope?: any}>(t: T, scope: Scope): T {
	t.declScope = scope;
	return t;
}
export function declScopeOf<T extends {declScope?: any}>(t: T, scope: Scope) {
	return (t.declScope as Scope) ?? scope;
}
export function ownScope(t: Type, scope: Scope) {
	return t.type === 'ref' ? declScopeOf(t, scope) : scope;
}

// Tags every `ref`/signature reachable from `t` with `scope`, in place, skipping what already carries one. `exclude`: names bound inside, not free
// (a nested function's own type parameters, `stampSig`), which must resolve where they are later registered.
export function stampScope<T extends Type>(t: T, scope: Scope, exclude?: Set<string>): T {
	walkerB(undefined, undefined,
		searchOnce((x: Type, process: (x: Type) => boolean) => {
			// Primitives resolve the same everywhere -- stamping them would only add dead weight and dedup-key noise for no gain.
			if (x.type === 'ref') {
				if (!x.declScope && !INTRINSIC_TYPES.has(x.name) && !exclude?.has(x.name))
					x.declScope = scope;
			} else if (x.type === 'typeof') {
				// A `typeof X` names a VALUE, which needs its declaring scope as a ref does: exported `Partial<typeof Defaults>` resolves in an importer.
				x.declScope ??= scope;
			} else if (x.type === 'function' || x.type === 'constructor') {
				x.declScope ??= scope;
				// A nested generic signature binds its own type parameters: they are not the outer scope's names.
				if (x.typeParams?.length) {
					stampSig(x, scope, exclude);
					return false;
				}
			}
			return process(x);
		}),
		searchOnce((m: TS.TypeMember | TS.ClassMember, process: (x: TS.TypeMember | TS.ClassMember) => boolean) => {
			if (m.type === 'method' || m.type === 'call' || m.type === 'construct') {
				// A generic member binds its own type parameters, as a nested generic signature does above.
				if (m.typeParams?.length) {
					stampSig(m, scope, exclude);
					return false;
				}
				m.declScope ??= scope;
			}
			return process(m);
		})
	).type(t);
	return t;
}

// Stamps a `CallSig`'s params/rest/return, which is no `Type` node `stampScope` could take.
export function stampSig<T extends TS.CallSig>(sig: T, scope: Scope, exclude?: Set<string>): T {
	// The signature itself too: a bare interface method has no other `declScope` source.
	sig.declScope ??= scope;
	// Its own type parameters are excluded, bound within the signature: a hoisted nested function's `T` stamped with the enclosing scope would,
	// first-stamp-wins, resolve as the OUTER function's `T` throughout its body.
	const ownTypeParams = sig.typeParams?.length ? new Set([...exclude ?? [], ...sig.typeParams.map(p => p.name)]) : exclude;
	sig.params.forEach(p => p.typeAnnotation && stampScope(p.typeAnnotation as Type, scope, ownTypeParams));
	if (sig.rest?.typeAnnotation)
		stampScope(sig.rest.typeAnnotation as Type, scope, ownTypeParams);
	if (sig.thisType)
		stampScope(sig.thisType, scope, ownTypeParams);
	if (sig.returnType)
		stampScope(sig.returnType, scope, ownTypeParams);
	// A type param's constraint/default too, or a constraint declared here but invisible to the caller cannot resolve (`isLiteralOnly` then widens
	// a literal argument). Still excluding `ownTypeParams`: an F-bounded constraint (`T extends hasop<'x', T>`) names its own `T`.
	sig.typeParams?.forEach(p => {
		if (p.constraint)
			stampScope(p.constraint as Type, scope, ownTypeParams);
		if (p.default)
			stampScope(p.default as Type, scope, ownTypeParams);
	});
	return sig;
}

// ===================================================================
//  Substitution and type-parameter hygiene
// ===================================================================

// A type is a DAG -- one subtree reached through many parents -- so a walk over it visits each node once, or its cost
// is the number of paths, exponential in how deeply generic instantiations nest. For a search, a node seen before is no hit.
function searchOnce<X extends object, P, R>(on: (x: X, process: P, recurse: R) => boolean) {
	const seen = new Set<X>();
	return (x: X, process: P, recurse: R) => {
		if (seen.has(x))
			return false;
		seen.add(x);
		return on(x, process, recurse);
	};
}
// For a rewrite, a node seen before maps to what it mapped to, which also keeps the shared subtree shared in the result.
function rewriteOnce<X extends object, P, R>(on: (x: X, process: P, recurse: R) => X | undefined) {
	const done = new Map<X, X | undefined>();
	return (x: X, process: P, recurse: R) => {
		if (!done.has(x))
			done.set(x, on(x, process, recurse));
		return done.get(x);
	};
}

// `t` (a written cast's type) with each `typeof` naming a function's local replaced by that local's type: an inferred return built from it
// outlives the names (`group`'s `as (keyof typeof inv)[]`), and a query would hide from substitution the type parameters it mentions.
// So is a type alias declared in a function body (`type R = ...` in `Optional`): its body, in which the function's own type parameters are still
// names, so the caller's instantiation reaches them, as TS instantiates a local type with the outer mapper.
export function expandLocalQueries(t: Type, scope: Scope, seen = new Set<TypeEntry>()): Type {
	const local		= (s: Scope | undefined): boolean => !!s && (!!s.functionKind || local(s.parent));
	const alias		= (name: string, sc: Scope) => (d => (e => d && local(d) && e && !e.isTypeParam && !seen.has(e) ? { d, e } : undefined)(d?.type(name)))(sc.typeDeclaring(name));
	return walker(undefined, undefined, rewriteOnce((x: Type, process: <T extends Type>(x: T) => T) => {
		const names = refNames(x);
		if (!names.has(QUERY) && ![...names].some(n => n !== INDEXED && alias(n, scope)))
			return x;
		if (x.type === 'ref') {
			const sc = declScopeOf(x, scope), a = alias(x.name, sc);
			if (!a)
				return process(x);
			// Its other names resolve where it was declared; the function's type parameters stay free for the caller's substitution.
			const params	= new Set([...refNames(a.e.type)].filter(n => a.d.type(n)?.isTypeParam));
			const stamped	= stampScope(a.e.type, a.d, params);
			const body		= a.e.typeParams?.length ? substituteType(stamped, new Map(a.e.typeParams.map((p, i) => [p.name, x.typeArgs?.[i] ?? p.default ?? ANY]))) : stamped;
			return expandLocalQueries(body, a.d, new Set([...seen, a.e]));
		}
		if (x.type !== 'typeof')
			return process(x);
		const sc = declScopeOf(x, scope);
		return local(sc.declaring(x.name.split('.')[0])) ? resolve(sc, x) : process(x);
	})).type(t) ?? t;
}

// A synthetic type-parameter name: the apostrophe can never appear in a real identifier, so it collides with nothing in scope.
let freshTypeParamId = 0;
export function freshTypeParamName(base: string) { return `${base}'${freshTypeParamId++}`; }
// A relation key that expands nothing: a ref by name (a fresh parameter under the name it was copied from) and arguments, a
// union by its members, anything else by identity. Printing instead (`typeKey`) can build strings too long for V8.
const nodeIds	= new WeakMap<Type, number>();
let nextNodeId	= 0;
const nodeId	= (t: Type) => nodeIds.get(t) ?? (nodeIds.set(t, ++nextNodeId), nextNodeId);
function relationKey(t: Type): string {
	return t.type === 'ref' ? t.name.replace(/'\d+$/, '') + (t.typeArgs ? `<${t.typeArgs.map(relationKey).join(',')}>` : '')
		: t.type === 'union' ? t.types.map(relationKey).join('|')
		: `#${nodeId(t)}`;
}

// `sig` with every type in it -- parameters, rest, return, its own type parameters' bounds -- mapped through `f`.
function mapSigTypes<S extends TS.CallSig>(sig: S, f: (t: Type) => Type): S {
	return {
		...sig,
		params:		sig.params.map(p => p.typeAnnotation ? { ...p, typeAnnotation: f(p.typeAnnotation) } : p),
		rest:		sig.rest?.typeAnnotation ? { ...sig.rest, typeAnnotation: f(sig.rest.typeAnnotation) } : sig.rest,
		returnType:	sig.returnType && f(sig.returnType),
		typeParams:	sig.typeParams?.map(p => ({ ...p, constraint: p.constraint && f(p.constraint), default: p.default && f(p.default) })),
	};
}

// A nested signature's own type parameter (`Array<T>.map<U>`'s `U`) would capture a same-named one in a value substituted into it
// (`T := U[]` from a caller's own `U`). Alpha-renames each such bound parameter first, so the outer substitution is capture-free.
function avoidCapture<S extends TS.CallSig>(sig: S, map: Map<string, Type>): S {
	if (!sig.typeParams?.length)
		return sig;
	const values = [...map.values()];
	const rename = new Map(sig.typeParams.filter(p => values.some(v => mentionsTypeParam(v, p.name))).map(p => [p.name, freshTypeParamName(p.name)] as const));
	if (!rename.size)
		return sig;
	const renameRefs	= new Map([...rename].map(([from, to]) => [from, TS.RefType(to)] as const));
	const renamed		= mapSigTypes(sig, t => substituteType(t, renameRefs));
	return { ...renamed, typeParams: renamed.typeParams?.map(p => ({ ...p, name: rename.get(p.name) ?? p.name })) };
}

// A mapped type's key is a binder too: `Partial<{p: P}>` would capture a caller's `P` under `[P in keyof T]`, or let an outer same-named substitution in.
function renameMappedKey(m: TS.MappedType): TS.MappedType {
	const keyName	= freshTypeParamName(m.keyName);
	const rename	= new Map([[m.keyName, TS.RefType(keyName)]]);
	return { ...m, keyName, valueType: substituteType(m.valueType, rename), nameType: m.nameType && substituteType(m.nameType, rename) };
}

// Chained generic calls (`TableBuilder<T & X>`) substitute each previous result back in as `T`: without sharing, each step embeds a fresh copy and
// node counts double per call. Keyed by identity per binding, since a `typeKey` key only moved the exponential cost into printing.
const substituteTypeCache = new WeakMap<Type, Map<string, WeakMap<Type, Type>>>();

// A signature's own type parameters SHADOW the same outer names (`class G<T> { foo<T>(t: X<T>) }`: G's T never reaches foo's).
// Undefined when nothing is shadowed; otherwise `sig` with only the outer names it doesn't redeclare substituted.
function substituteShadowed<S extends TS.CallSig>(sig: S, map: Map<string, Type>): S | undefined {
	const own = sig.typeParams;
	if (!own?.some(p => map.has(p.name)))
		return undefined;
	const outer = new Map([...map].filter(([name]) => !own.some(p => p.name === name)));
	return outer.size ? mapSigTypes(sig, t => substituteType(t, outer)) : sig;
}

// TS's rule for a missing type argument: a parameter's DEFAULT may name the parameters before it (`Call<E, A = E>` in common.ts),
// so each default is instantiated with the arguments already chosen -- otherwise the bare parameter escapes into the member types.
export function typeArgMap(typeParams: readonly TS.TypeParam[], typeArgs: readonly Type[] | undefined, fallback: Type = ANY): Map<string, Type> {
	const map = new Map<string, Type>();
	typeParams.forEach((p, i) => map.set(p.name, typeArgs?.[i] ?? (p.default ? substituteType(p.default, map) : fallback)));
	return map;
}

// A method member read as a value: its signature, `this` included, with an unwritten return as `any`.
function methodSignature(m: TS.CallSig): TS.CallSig {
	return { params: m.params, rest: m.rest, thisType: m.thisType, returnType: m.returnType ?? ANY, typeParams: m.typeParams };
}

// Replaces type-parameter references with their instantiating arguments (`Foo<string>` is Foo's body with `T := string`).
// Every name a ref anywhere in `t` spells (bound ones included), plus `QUERY`/`INDEXED` if it holds a `typeof`/`T[K]`, memoized on each node:
// a rewrite skips a subtree holding nothing it rewrites.
const refNamesCache = new WeakMap<Type, ReadonlySet<string>>();
const QUERY = '\0typeof', INDEXED = '\0indexed';
function refNames(t: Type): ReadonlySet<string> {
	let names = refNamesCache.get(t);
	if (!names) {
		// Cached before the walk: a type reaching itself (`f` returning `f`) shares the set still being filled.
		const out = new Set<string>();
		refNamesCache.set(t, out);
		if (t.type === 'ref')
			out.add(t.name);
		else if (t.type === 'typeof')
			out.add(QUERY);
		else if (t.type === 'indexed_access')
			out.add(INDEXED);
		walkerB(undefined, undefined, (x: Type, process: (x: Type) => boolean) => x === t ? process(x) : (refNames(x).forEach(n => out.add(n)), false)).type(t);
		names = out;
	}
	return names;
}

export function substituteType(t: Type, map: Map<string, Type>): Type {
	if (map.size === 1) {
		const [[name, arg]] = map;
		let byName = substituteTypeCache.get(t);
		if (!byName)
			substituteTypeCache.set(t, byName = new Map());
		let byArg = byName.get(name);
		if (!byArg)
			byName.set(name, byArg = new WeakMap());
		const cached = byArg.get(arg);
		if (cached)
			return cached;
		const result = uncached();
		byArg.set(arg, result);
		return result;
	}
	return uncached();

	function uncached(): Type {
		return walker(undefined, undefined,
			rewriteOnce((x: Type, process: <T extends Type>(x: T) => T) => {
				const names = refNames(x);
				if (![...map.keys()].some(k => names.has(k)))
					return x;
				if (x.type === 'ref' && !x.typeArgs && map.has(x.name))
					return map.get(x.name);
				if (x.type === 'function' || x.type === 'constructor') {
					x = { ...x, ...avoidCapture(x, map) };
					const shadowed = substituteShadowed(x, map);
					if (shadowed)
						return shadowed;
				}
				if (x.type === 'mapped') {
					const key = x.keyName;
					if (map.has(key) || [...map.values()].some(v => mentionsTypeParam(v, key)))
						x = renameMappedKey(x);
				}
				// A rebuilt union or intersection is reduced as TS reduces an instantiated one: `T & U` at `{}` and `any` is `any`.
				const r = process(x);
				// A conditional over a naked type parameter DISTRIBUTES over the union it is instantiated with, each arm seeing its member: only the
				// pre-substitution node can produce that, so it is kept for `resolve`.
				if (x.type === 'conditional' && r.type === 'conditional') {
					const orig = x, check = x.checkType;
					const arm = check.type === 'ref' && !check.typeArgs && map.has(check.name) ? (m: Type) => substituteType(orig, new Map([...map, [check.name, m]]))
						: orig.distribute ? (m: Type) => substituteType(orig.distribute!(m), map)
						: undefined;
					return arm ? { ...r, distribute: arm } : r;
				}
				return r.type === 'union' || r.type === 'intersection' ? reduceInstantiated(r) : r;
			}),
			// A method's own generic signature (`Array<T>.map<U>`) is a `TypeMember` node, which needs `avoidCapture` too.
			rewriteOnce((m: TS.TypeMember, process: <T extends TS.TypeMember>(x: T) => T) => {
				if (m.type === 'method' || m.type === 'call' || m.type === 'construct') {
					m = { ...m, ...avoidCapture(m, map) };
					const shadowed = substituteShadowed(m, map);
					if (shadowed)
						return shadowed;
				}
				return process(m);
			})
		).type(t) ?? t;
	}
}

// Each type parameter at its constraint (`unconstrained` when it has none). A constraint may name a sibling in either
// direction (`<K extends keyof T, T>`); constraints are acyclic, so n-1 passes settle them.
export function constraintMap(typeParams: readonly TS.TypeParam[], unconstrained: Type = UNKNOWN): Map<string, Type> {
	const map = new Map(typeParams.map(p => [p.name, p.constraint ?? unconstrained] as const));
	for (let i = 1; i < map.size; i++)
		map.forEach((t, name) => map.set(name, substituteType(t, map)));
	return map;
}

// TS's hasCorrectTypeArgumentArity: a generic signature taking `count` explicit type arguments, a defaulted parameter optional.
export function typeArgArityFits(sig: TS.CallSig, count: number): boolean {
	const params = sig.typeParams ?? [];
	return params.length > 0 && count <= params.length && count >= params.filter(p => !p.default).length;
}

// TS's instantiation expression (`typeof C<A>`, getInstantiatedSignatures): only the signatures the type arguments fit, each instantiated.
function instantiateExpression(v: Type, typeArgs: Type[], scope: Scope): Type {
	const inst = <S extends TS.CallSig>(sig: S): S => instantiateSig(sig, new Map(sig.typeParams!.map((p, i) => [p.name, typeArgs[i] ?? p.default!])));
	const r = resolveOwn(v, scope);
	return r.type === 'intersection' ? TS.IntersectionType(r.types.map(p => instantiateExpression(p, typeArgs, scope)))
		: r.type === 'function' || r.type === 'constructor' ? typeArgArityFits(r, typeArgs.length) ? inst(r) : r
		: r.type === 'object' ? TS.ObjectType(r.members.flatMap<TS.TypeMember>(m => m.type !== 'call' && m.type !== 'construct' ? [m] : typeArgArityFits(m, typeArgs.length) ? [inst(m)] : []))
		: r;
}

// `sig` with its own type parameters replaced per `map`, no longer generic.
export function instantiateSig<S extends TS.CallSig>(sig: S, map: Map<string, Type>): S {
	return { ...mapSigTypes(sig, t => substituteType(t, map)), typeParams: undefined };
}

// TS's `getBaseSignature`: `sig`'s own type parameters replaced by their constraints, so none escapes its binder.
export function baseSignature<S extends TS.CallSig>(sig: S, unconstrained: Type = UNKNOWN): S {
	return sig.typeParams?.length ? instantiateSig(sig, constraintMap(sig.typeParams, unconstrained)) : sig;
}

// Whether `t` names any of `names` as a bare type reference.
function mentionsNames(t: Type, names: ReadonlyMap<string, unknown>): boolean {
	return walkerB(undefined, undefined, searchOnce((x: Type, process: (x: Type) => boolean) => (x.type === 'ref' && !x.typeArgs && names.has(x.name)) || process(x))).type(t);
}

// Whether a node of `kind` occurs anywhere in `t`.
export function containsKind(t: Type, kind: Type['type']): boolean {
	return walkerB(undefined, undefined, searchOnce((x: Type, process: (x: Type) => boolean) => x.type === kind || process(x))).type(t);
}

// The names an `extends` clause binds with `infer`, which its true branch reads.
export function inferNames(t: Type): string[] {
	const names: string[] = [];
	walkerB(undefined, undefined, searchOnce((x: Type, process: (x: Type) => boolean) => (x.type === 'infer' && names.push(x.name), process(x)))).type(t);
	return names;
}

// Replaces a `this` type node with `thisType`, the concrete class ref codegen needs up front. A walk rebuilds every node, so a type
// with no `this` is returned as the same object, keeping every identity-keyed cache downstream (`resolve`, `lookupMember`) warm.
export function substituteThisType(t: Type, thisType: Type): Type {
	return containsKind(t, 'this') ? walker(undefined, undefined, rewriteOnce((x: Type, process: <T extends Type>(x: T) => T) =>
		x.type === 'this' ? thisType : process(x)
	)).type(t) ?? t : t;
}

// Whether `name` occurs where `inferTypeArgs` descends, telling "no argument could determine it" from a real gap. Mirrors its recursion shape.
const mentionsCache = new WeakMap<Type, Map<string, boolean>>();
export function mentionsTypeParam(t: Type, name: string): boolean {
	let byName = mentionsCache.get(t);
	if (!byName)
		mentionsCache.set(t, byName = new Map());
	let r = byName.get(name);
	if (r === undefined)
		byName.set(name, r = mentions(t, name));
	return r;
}
function mentions(t: Type, name: string): boolean {
	return walkerB(undefined, undefined, searchOnce((t: Type, process: (x: Type) => boolean, recurse: WalkerB) => {
		switch (t.type) {
			case 'ref':				return t.typeArgs ? process(t) : t.name === name;
			case 'function':
			case 'constructor':		return t.params.some(p => recurse.type(p.typeAnnotation)) || recurse.type(t.returnType);
			case 'object':			return t.members.some(m =>
				m.type === 'property' ? recurse.type(m.typeAnnotation)
				: m.type === 'method' ? recurse.type(m.returnType)
				: false
			);
			case 'conditional':		return recurse.type(t.trueType) || recurse.type(t.falseType);
			case 'array': case 'tuple': case 'intersection': case 'union': case 'predicate':
				return process(t);
			// `keyof`/`indexed_access`/`mapped`/`typeof`/`this`/`template_literal`/`infer`: not positions `inferTypeArgs` inverts.
			default:				return false;
		}
	})).type(t);
}

// A declared type's body with `typeArgs` substituted for its parameters (their defaults where missing).
function instantiateEntry(entry: TypeEntry, typeArgs: readonly Type[] | undefined): Type {
	return entry.typeParams?.length ? substituteType(entry.type, typeArgMap(entry.typeParams, typeArgs)) : entry.type;
}

// Expands a `ref` one level into its declared body, type args substituted; refs nested inside stay names.
export function expandRefOnce(scope: Scope, t: Type): Type {
	if (t.type !== 'ref')
		return t;
	const entry = ownScope(t, scope).lookupType(t.name);
	return entry ? instantiateEntry(entry, t.typeArgs) : t;
}

// `expandRefOnce` looped: a ref's declared body, stopping at a type parameter, which is opaque.
function peelAliases(t: Type, scope: Scope, depth: number): Type {
	for (let i = 0; i < depth && t.type === 'ref' && !INTRINSIC_TYPES.has(t.name) && !scope.type(t.name)?.isTypeParam; i++)
		t = expandRefOnce(scope, t);
	return t;
}

// ===================================================================
//  Resolution
// ===================================================================

// Does this ref name a real `class`? `resolve` keeps such a ref nominal (its `case 'ref'`).
export function isClassRef(t: Type, scope: Scope): boolean {
	if (t.type !== 'ref' || INTRINSIC_TYPES.has(t.name))
		return false;
	const [ns, name] = declScopeOf(t, scope).qualified(t.name);
	return !!ns?.classDecl(name);
}

// Whether `t` derives from a genuinely uninstantiated type parameter (none registered in `scope`); `indexed_access` asks its inner positions.
function isAbstract(t: Type, scope: Scope): boolean {
	switch (t.type) {
		// Not a CLASS ref, concrete though `resolve` keeps it unexpanded, nor a DOTTED name, which a type parameter never is (`scope.type` does not
		// split on '.'). Looked up in the ref's own `declScope`, where `resolve` looks: a stamped member of an imported union is unknown to the ambient scope.
		case 'ref': {
			const home = declScopeOf(t, scope);
			return !t.typeArgs && !t.name.includes('.') && !INTRINSIC_TYPES.has(t.name) && !isClassRef(t, home) && (!home.type(t.name) || !!home.type(t.name)?.isTypeParam);
		}
		case 'indexed_access':	return isAbstract(t.object, scope) || isAbstract(t.index, scope);
		case 'keyof':			return isAbstract(t.argument, scope);
		default:				return false;
	}
}

// A type parameter's constraint (`unknown` when it declares none); undefined for any other type.
export function typeParamConstraint(t: Type, scope: Scope): Type | undefined {
	if (t.type !== 'ref' || t.typeArgs)
		return undefined;
	const [ns, name] = declScopeOf(t, scope).qualified(t.name);
	const entry = ns?.type(name);
	return entry?.isTypeParam ? entry.type : undefined;
}

// TS's apparent type of a homomorphic mapped type over a type parameter constrained to an array or tuple: the mapping of that constraint
// (`{[K in keyof T]: E<T[K]>}` with `T extends unknown[]` is `E<unknown>[]`).
export function mappedApparentType(t: Type, scope: Scope): Type | undefined {
	const arg		= t.type === 'mapped' && !t.nameType && t.constraint.type === 'keyof' ? t.constraint.argument : undefined;
	const bound		= arg?.type === 'ref' ? typeParamConstraint(arg, scope) : undefined;
	const shape		= bound && resolve(scope, bound).type;
	return arg?.type === 'ref' && (shape === 'array' || shape === 'tuple') ? substituteType(t, new Map([[arg.name, bound!]])) : undefined;
}

// TS's `NonNullable` of a type parameter whose constraint may be nullish (`T & {}`, which relates through that constraint); else undefined.
export function nonNullableParam(t: Type, scope: Scope): Type | undefined {
	const bound = typeParamConstraint(t, scope);
	return bound && (isRef(bound, 'unknown') || unionMembers(bound, scope).some(m => isNullish(m, scope))) ? TS.IntersectionType([t, TS.ObjectType([])]) : undefined;
}

// A deferred conditional is one of its branches, the true one reading its check type as also its extends type (TS's
// substitution types): `X extends T ? X : never` is an `X & T`.
export function deferredBranches(t: Extract<Type, { type: 'conditional' }>): Type {
	const check = typeId(t.checkType), narrowed = TS.IntersectionType([t.checkType, t.extendsType]);
	const trueType = walker(undefined, undefined, (x: Type, process: <T extends Type>(x: T) => T) => typeId(x) === check ? narrowed : process(x)).type(t.trueType) ?? t.trueType;
	return combineTypes([trueType, t.falseType]);
}

// A conditional over an unbound type parameter waits for its instantiation, as TS's does: kept as a conditional, related through
// `deferredBranches`. Unless DEFINITELY true (with parameters opaque), or TS's simplification: `T extends U ? T : never` is
// `never`, and `T extends U ? never : T` is `T`, where no `T` is a `U`.
function deferred(t: Extract<Type, { type: 'conditional' }>, scope: Scope): Type {
	if (isAssignable(t.checkType, t.extendsType, scope, scope, true))
		return resolve(scope, t.trueType);
	const same		= (x: Type) => typeId(x) === typeId(t.checkType);
	const disjoint	= () => isRef(resolve(scope, TS.IntersectionType([t.checkType, t.extendsType])), 'never');
	if (isRef(t.falseType, 'never') && same(t.trueType))
		return disjoint() ? NEVER : t;
	if (isRef(t.trueType, 'never') && same(t.falseType))
		return disjoint() ? resolve(scope, t.falseType) : t;
	return t;
}

// A mapped type's value at one key: `T[K]` with both known IS that property's type (`Tbl["0"]` is `"v128.load"`), never a node repeating all of `T`
// per member, which nested grew past any string a key can hold.
function valueAtKey(t: Extract<Type, { type: 'mapped' }>, key: Type, scope: Scope): Type {
	const sub = substituteType(t.valueType, new Map([[t.keyName, key]]));
	return walker(undefined, undefined, rewriteOnce((x: Type, process: <T extends Type>(x: T) => T) =>
		!refNames(x).has(INDEXED) ? x : x.type === 'indexed_access' && !mentionsAbstract(x, scope) ? resolve(scope, x, undefined, true) : process(x))).type(sub) ?? sub;
}

// TS's permissive instantiation: every unbound type parameter in `t` read as `any`.
function permissive(t: Type, scope: Scope): Type {
	return walker(undefined, undefined, (x: Type, process: <T extends Type>(x: T) => T) => x.type === 'ref' && isAbstract(x, scope) ? ANY : process(x)).type(t) ?? t;
}

// Does `t` mention an unbound type parameter anywhere (an object member, a type argument), not just as a bare ref (`isAbstract`)? `instantiate`
// uses it to tell a real inference result from one carrying an OUTER call's unsolved parameters.
// Memoized per scope and node, by the names bound around it: a chained builder's type (`TreeBuilder<T & X>` per step) is a DAG whose tree is exponential.
const abstractCache = new WeakMap<Scope, WeakMap<Type, Map<string, boolean>>>();
export function mentionsAbstract(t: Type, scope: Scope, bound: ReadonlySet<string> = new Set()): boolean {
	const byType	= abstractCache.get(scope) ?? abstractCache.set(scope, new WeakMap()).get(scope)!;
	const byBound	= byType.get(t) ?? byType.set(t, new Map()).get(t)!;
	const key		= bound.size ? [...bound].sort().join(',') : '';
	let r = byBound.get(key);
	if (r === undefined)
		byBound.set(key, r = mentionsAbstractUncached(t, scope, bound));
	return r;
}
function mentionsAbstractUncached(t: Type, scope: Scope, bound: ReadonlySet<string>): boolean {
	const within	= (x: Type, names: readonly string[]) => mentionsAbstract(x, scope, names.length ? new Set([...bound, ...names]) : bound);
	const any		= (xs: (Type | undefined)[], names: readonly string[] = []) => xs.some(x => !!x && within(x, names));
	const sig		= (s: TS.CallSig) => any([...s.params.map(p => p.typeAnnotation), s.rest?.typeAnnotation, s.returnType], s.typeParams?.map(p => p.name) ?? []);
	switch (t.type) {
		case 'ref':				return !t.typeArgs && bound.has(t.name) ? false : isAbstract(t, scope) || any(t.typeArgs ?? []);
		case 'union':
		case 'intersection':	return any(t.types);
		case 'array':			return any([t.element]);
		case 'tuple':			return any(t.elements.map(e => e.type === 'spread' ? e.argument : tupleElementType(e)));
		case 'indexed_access':	return any([t.object, t.index]);
		case 'keyof':			return any([t.argument]);
		case 'mapped':			return any([t.constraint]) || any([t.nameType, t.valueType], [t.keyName]);
		case 'conditional':		return any([t.checkType, t.extendsType]) || any([t.trueType, t.falseType], inferNames(t.extendsType));
		case 'function':
		case 'constructor':		return sig(t);
		case 'object':			return t.members.some(m => m.type === 'property' || m.type === 'index' ? within(m.typeAnnotation, []) : sig(m));
		default:				return false;
	}
}

// `X[i]` reduced ONE step to the element it names when `X` is a tuple or array, the element left as written (a named ref stays a ref).
function oneStepIndexed(t: Type, scope: Scope): Type {
	if (t.type !== 'indexed_access')
		return t;
	const obj = resolveOwn(t.object, scope);
	const idx = resolveOwn(t.index, scope);
	if (obj.type === 'tuple' && idx.type === 'literal' && typeof idx.value === 'number')
		return (obj.elements[idx.value] && tupleElementType(obj.elements[idx.value])) || t;
	if (obj.type === 'array' && isNumberLike(idx, scope))
		return obj.element;
	// A named property: `Record1['move']` is its declared `[number, 'left' | 'right']`.
	return idx.type === 'literal' && typeof idx.value === 'string' ? lookupMember(obj, idx.value, scope) ?? t : t;
}

// TS's getModifiersTypeFromMappedType: `{[P in K]: ...}` over a type parameter `K extends keyof T` keeps `T`'s property modifiers after `K` is
// instantiated, as `[P in keyof T]` does. Mutates `t`'s mapped types.
export function markModifiersTypes(t: Type, typeParams: TS.TypeParam[] | undefined): Type {
	if (typeParams?.length)
		walkerB(undefined, undefined, (x, process) => {
			if (x.type === 'mapped' && x.constraint.type === 'ref' && !x.constraint.typeArgs) {
				const name	= x.constraint.name;
				const c		= typeParams.find(p => p.name === name)?.constraint;
				if (c?.type === 'keyof')
					x.modifiersType = c.argument;
			}
			return process(x);
		}).type(t);
	return t;
}

// A homomorphic mapped type's `readonly`/`-readonly`/`optional`/`-optional` override the source member's; others pass through.
function mapMemberModifiers(sourceMods: string[] | undefined, mapMods: string[] | undefined): string[] | undefined {
	const result = new Set(sourceMods);
	for (const tag of ['readonly', 'optional']) {
		if (mapMods?.includes(tag))
			result.add(tag);
		else if (mapMods?.includes('-' + tag))
			result.delete(tag);
	}
	return result.size ? [...result] : undefined;
}

// The text each member of a template interpolation contributes, or undefined when some member isn't a finite literal.
function templateTexts(t: Type, scope: Scope): string[] | undefined {
	const out: string[] = [];
	for (const m of unionMembers(t, scope).map(m => resolve(scope, m))) {
		if (m.type === 'literal' && !Array.isArray(m.value))
			out.push(String(m.value));
		else if (m.type === 'range' && m.min !== undefined && m.min === m.max)
			out.push(String(m.min));
		else if (isRef(m, 'boolean'))
			out.push('false', 'true');
		else if (isRef(m, 'null') || isRef(m, 'undefined'))
			out.push(isRef(m, 'null') ? 'null' : 'undefined');
		else
			return undefined;
	}
	return out;
}

// A template literal type with all-finite interpolations is the union of its cross product (real keys for a mapped type over `${E}${E}`).
// tsc refuses past 100,000 members; such a type stays unexpanded.
function expandTemplate(parts: JS.TemplatePart<Type>[], scope: Scope): Type | undefined {
	let acc = [''];
	for (const p of parts) {
		const texts = p.exp ? templateTexts(p.exp, scope) : [''];
		if (!texts || acc.length * texts.length > 100000)
			return undefined;
		acc = acc.flatMap(a => texts.map(x => a + p.str + x));
	}
	return combineTypes(acc.map(x => Literal(x)));
}

// The text each placeholder of a template literal type takes in `src`, as TS's inferFromLiteralPartsToTemplateLiteral: up to the next part's
// text (one character before another placeholder), the last the rest. Each part is text then a placeholder; a final text part may be absent.
function templateSlices(written: readonly JS.TemplatePart<Type>[], src: string): string[] | undefined {
	const parts	= written[written.length - 1].exp ? [...written, { str: '' }] : written;
	const n		= parts.length - 1, end = src.length - parts[n].str.length;
	let pos = parts[0].str.length;
	if (!src.startsWith(parts[0].str) || !src.endsWith(parts[n].str) || end < pos)
		return undefined;
	const slices: string[] = [];
	for (let i = 0; i < n; i++) {
		const delim	= parts[i + 1].str;
		const stop	= i === n - 1 ? end : delim ? src.indexOf(delim, pos) : pos + 1;
		if (stop < pos || stop > end)
			return undefined;
		slices.push(src.slice(pos, stop));
		pos = stop + delim.length;
	}
	return slices;
}

// A regex matching every string an unexpanded template literal type denotes; an interpolation it can't pin down matches anything.
function templatePattern(parts: JS.TemplatePart<Type>[], scope: Scope): string {
	const esc = (x: string) => x.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
	const part = (t: Type): string => {
		const texts = templateTexts(t, scope);
		if (texts)
			return `(?:${texts.map(esc).join('|')})`;
		const r = resolve(scope, t);
		return isRef(r, 'number') ? '(?:[-+]?(?:\\d+\\.?\\d*|\\.\\d+)(?:e[-+]?\\d+)?|NaN|-?Infinity)'
			: isRef(r, 'bigint') ? '-?\\d+'
			: r.type === 'literal' && Array.isArray(r.value) ? `(?:${templatePattern(r.value, scope)})`
			: '[\\s\\S]*';
	};
	return parts.map(p => esc(p.str) + (p.exp ? part(p.exp) : '')).join('');
}

// The disjoint domain of a resolved intersection member (TS's DisjointDomains, `void` counted as `undefined`), 'structural'
// for an object type, undefined when unknown (a type parameter, an unresolved name).
type Domain = PRIMITIVES | 'structural' | undefined;
function domainOf(r: Type, scope: Scope): Domain {
	switch (r.type) {
		case 'literal':	return literalType(r) as Domain;
		case 'range':	return r.base;
		case 'object': case 'array': case 'tuple': case 'function': case 'constructor':
			return 'structural';
		case 'ref':		return r.name === 'void' ? 'undefined' : PRIMITIVES.has(r.name) ? r.name : isClassRef(r, scope) ? 'structural' : undefined;
		default:		return undefined;
	}
}

// No value of `t` is an object: every member is of a primitive domain, so `instanceof` is false of it.
export function isPrimitiveOnly(t: Type, scope: Scope): boolean {
	return unionMembers(t, scope).every(m => {
		const d = domainOf(resolve(scope, m), scope);
		return d !== undefined && d !== 'structural' && d !== 'object';
	});
}

type Unit = string | number | bigint | boolean;
const unitOf = (r: Type): Unit | undefined => r.type === 'literal' && !Array.isArray(r.value) && r.value !== null ? r.value
	: r.type === 'range' && r.min !== undefined && r.min === r.max ? r.min : undefined;

// TS's intersection normalization: distributes over a union member; `unknown`, `{}` beside an object, a primitive beside its unit drop out; disjoint
// domains or units, nullish beside an object, or clashing discriminants are `never`. Undefined if nothing reduces; a type-param part stays opaque.
function reduceIntersection(t: TS.IntersectionType, scope: Scope, depth: number): Type | undefined {
	const raw: Type[] = [], res: Type[] = [];
	// `d`: depth left at each nesting level; once spent a member stays as written, never meeting `resolve`'s bail to `any`.
	const add = (p: Type, d: number) => {
		const r = d < 0 || isAbstract(p, scope) ? p : resolve(scope, p, d);
		if (r.type === 'intersection') {
			r.types.forEach(q => add(q, d - 1));
		} else {
			raw.push(p);
			res.push(r);
		}
	};
	t.types.forEach(p => add(p, depth - 1));
	// `any` must be the part AS WRITTEN: `resolve` answers `any`/`unknown` when it gives up, which is no reduction.
	if (res.some((r, i) => isRef(r, 'any') && isRef(raw[i], 'any')))
		return ANY;
	if (res.some(r => isRef(r, 'never')))
		return NEVER;

	const u = res.findIndex(r => r.type === 'union');
	if (u >= 0) {
		const lists = res.map((r, i) => r.type !== 'union' ? [raw[i]] : r === raw[i] ? r.types : unionMembers(raw[i], scope));
		if (lists.reduce((n, l) => n * l.length, 1) > 100000)
			return undefined;	// tsc refuses such a type as too complex to represent
		return combineTypes(lists[u].map(m => {
			const each = TS.IntersectionType(raw.map((p, i) => i === u ? m : p));
			return reduceIntersection(each, scope, depth - 1) ?? each;
		}));
	}

	const doms	= res.map(r => domainOf(r, scope));
	const prims	= new Set(doms.filter(d => d && d !== 'structural'));
	if (prims.size > 1 || ((prims.has('undefined') || prims.has('null')) && doms.includes('structural') && scope.strictNullChecks()))
		return NEVER;
	const units		= res.map(unitOf);
	const values	= new Set(units.filter(v => v !== undefined));
	if (values.size > 1)
		return NEVER;

	// A literal discriminant two object parts both declare, read as written: resolving property types would expand recursive types and force lazy fields.
	const objects = res.filter((r): r is TS.ObjectType => r.type === 'object');
	if (objects.length > 1) {
		const declared = new Map<string, number>();
		for (const o of objects)
			for (const m of o.members)
				if (m.type === 'property' && typeof m.key !== 'object')
					declared.set(String(m.key), (declared.get(String(m.key)) ?? 0) + 1);
		const written = (a: Type): Unit[] | undefined => {
			const vals: Unit[] = [];
			for (const m of a.type === 'union' ? a.types : [a]) {
				const v = unitOf(m);
				if (v === undefined)
					return undefined;
				vals.push(v);
			}
			return vals;
		};
		const shared = new Map<string, Unit[]>();
		for (const o of objects) {
			for (const m of o.members) {
				const key = m.type === 'property' ? JS.keyName(m.key) : undefined;
				if (m.type !== 'property' || key === undefined || declared.get(key)! < 2 || m.modifiers?.includes('optional'))
					continue;
				const vals = written(m.typeAnnotation);
				if (!vals)
					continue;
				const prev	= shared.get(key);
				const both	= prev ? prev.filter(v => vals.includes(v)) : vals;
				if (!both.length)
					return NEVER;
				shared.set(key, both);
			}
		}
	}

	const isEmpty		= (r: Type) => r.type === 'object' && !r.members.length;
	const hasObject		= res.some((r, i) => doms[i] === 'structural' && !isEmpty(r));
	const unitDomain	= values.size ? domainOf(res[units.findIndex(v => v !== undefined)], scope) : undefined;
	// A part that repeats adds nothing: `'function' & ('function' | 'arrow')` narrows to `'function' & 'function'`, which IS `'function'`.
	const seen			= new Set<string>();
	// `unknown` as RESOLVED too (`X & <conditional evaluating to unknown>` is `X`), unless the part names an unbound type parameter: a deferred
	// conditional collapses to `unknown` while still waiting on the instantiation.
	const kept			= raw.filter((_, i) => !((isRef(res[i], 'unknown') && !mentionsAbstract(raw[i], scope)) || (hasObject && isEmpty(res[i])) || (unitDomain && units[i] === undefined && res[i].type === 'ref' && doms[i] === unitDomain))
		&& !seen.has(typeId(res[i])) && (seen.add(typeId(res[i])), true));

	return kept.length === raw.length ? undefined : !kept.length ? UNKNOWN : kept.length === 1 ? kept[0] : TS.IntersectionType(kept);
}

// How many times `resolve` has run out of depth: a result produced while one did depends on the caller's depth, not on the type.
let depthBails = 0;

// A named alias's body resolves with a fresh `depth` budget, so a chain of structural steps (`Omit` -> mapped -> `Exclude` -> `keyof`) is not
// starved. Re-entering one with the same arguments is a cycle.
const expanding = new WeakMap<object, Set<string>>();
let aliasNesting = 0;
const ALIAS_NESTING_LIMIT = 40;
function resolveAliasBody(scope: Scope, alias: object, args: readonly Type[], body: () => Type, stopAtRef: boolean, ref: Type): Type {
	const key	= args.map(a => typeId(a)).join(',');
	const open	= expanding.get(alias) ?? expanding.set(alias, new Set()).get(alias)!;
	if (open.has(key)) {
		scope.hitDepthLimit('Scope.resolve(circular alias)');
		depthBails++;
		return ref;
	}
	if (aliasNesting >= ALIAS_NESTING_LIMIT) {
		scope.hitDepthLimit('Scope.resolve(alias nesting)');
		depthBails++;
		return ANY;
	}
	open.add(key);
	aliasNesting++;
	try {
		return resolve(scope, body(), undefined, stopAtRef);
	} finally {
		aliasNesting--;
		open.delete(key);
	}
}

const STRUCTURALLY_CACHED = new Set<Type['type']>(['intersection', 'conditional', 'mapped']);
export function resolve(scope: Scope, t: Type, depth = 10, stopAtRef = false): Type {
	const idx = stopAtRef ? 1 : 0;
	const slot = scope.resolveCache?.get(t);
	if (slot?.[idx] !== undefined)
		return slot[idx];
	// An expensive kind is also cached by STRUCTURE: substitution rebuilds equal types as new objects, which the identity cache misses.
	const sid = STRUCTURALLY_CACHED.has(t.type) ? typeId(t, true) : undefined;
	const byId = sid !== undefined ? scope.resolveCacheById?.get(sid)?.[idx]?.deref() : undefined;
	if (byId !== undefined)
		return byId;

	if (scope.resolving?.has(t)) {
		scope.hitDepthLimit('Scope.resolve(circular)');
		// Opaque rather than `ANY` (the depth bail's): `ANY` would pass every check on a circular type instead of reporting the gap.
		return t;
	}

	if (depth < 0) {
		scope.hitDepthLimit('Scope.resolve');
		depthBails++;
		return ANY;
	}

	(scope.resolving ??= new Set).add(t);
	const bails		= depthBails;
	const result	= uncached();
	scope.resolving.delete(t);
	if (depthBails !== bails)
		return result;

	const entry = (scope.resolveCache ??= new WeakMap).get(t) ?? [undefined, undefined];
	entry[idx]	= result;
	scope.resolveCache.set(t, entry);
	if (sid !== undefined) {
		const byIdEntry = (scope.resolveCacheById ??= new Map).get(sid) ?? [undefined, undefined];
		byIdEntry[idx] = new WeakRef(result);
		scope.resolveCacheById.set(sid, byIdEntry);
	}
	return result;

	function uncached(): Type {
		switch (t.type) {
			// A polymorphic `this` that knows its class resolves as that class; a declared `: this` has no class and stays opaque.
			case 'this':
				return t.of ? resolve(scope, t.of, depth - 1, stopAtRef) : t;

			case 'literal':
				return Array.isArray(t.value) ? expandTemplate(t.value, scope) ?? t : t;

			// A spread of a tuple contributes its elements (`[...Split<'add'>]` is `['add']`), as TS normalizes a tuple it instantiates.
			case 'tuple': {
				const elements = t.elements.some(e => e.type === 'spread') ? flatTupleElements(t, scope) : t.elements;
				return elements.length === t.elements.length && elements.every((e, i) => e === t.elements[i]) ? t : { ...t, elements };
			}
			// An array's element resolves too: a `Record<string, number>['string']` element otherwise stayed opaque inside a `V[]`.
			case 'array': {
				// A machine-type element (`i8[]`) stays unresolved: resolved it is plain `number`, and the element kind it forces is lost.
				if (machineOf(t.element, scope))
					return t;
				// Always `stopAtRef`: a named element (`Animal[]`) stays a ref, since a class dispatches by NAME (`animals[0].sound()`); only composition
				// (indexed access, mapped, keyof) needs a concrete shape.
				const element = resolve(scope, t.element, depth - 1, true);
				return element === t.element ? t : TS.ArrayType(element, t.readonly);
			}
			case 'mapped': {
				// Members are knowable only once the key constraint resolves to literals; of `keyof T & U`, the part that does is the key set (other parts
				// are not checked to exclude more). Each key resolved as it descends: a union member may be an alias to a further union.
				// A numeric key (`{69: 'i32.eqz'}`'s) stays a number, as TS's `K` does; its property is named by its string form.
				const literalKeys = (x: Type) => {
					const parts = unionMembers(x, scope).map(m => resolve(scope, m)).map(m => isLiteral(m, 'string') && !Array.isArray(m.value) ? m.value
						: isLiteral(m, 'number') ? m.value : m.type === 'range' && m.base === 'number' && m.min !== undefined && m.min === m.max ? m.min : undefined);
					return parts.every((p): p is string | number => p !== undefined) ? parts : undefined;
				};
				// Homomorphic (`[P in keyof T]`): each property starts from that key's own modifiers on `T`.
				const constraintParts	= t.constraint.type === 'intersection' ? t.constraint.types : [t.constraint];
				const keyofArg			= constraintParts.find(m => m.type === 'keyof')?.argument ?? t.modifiersType;
				const modifiersFor		= (key: string | number) => {
					const source = keyofArg && resolveObjectType(keyofArg, scope);
					return source ? mapMemberModifiers(findTypeMember(source.members, String(key))?.modifiers, t.modifiers) : t.modifiers;
				};
				const property = (key: string | number) => TS.TypeProperty(String(key), valueAtKey(t, Literal(key), scope), modifiersFor(key));
				// A HOMOMORPHIC mapped type over an ARRAY or TUPLE maps its ELEMENTS and stays an array/tuple, as TS does: `{[K in keyof T]: F<T[K]>}` with
				// `T = string[]` is `F<string>[]`, never an object keyed by indices.
				if (!t.nameType && t.constraint.type === 'keyof') {
					const src = resolve(scope, t.constraint.argument, depth - 1);
					// `T[K]` reads the INDEX: `K` is `number` for an array, each position's literal for a tuple.
					const atKey = (k: Type) => resolve(scope, valueAtKey(t, k, scope), depth - 1, stopAtRef);
					if (src.type === 'array')
						return TS.ArrayType(atKey(NUMBER), src.readonly);
					if (src.type === 'tuple')
						return { type: 'tuple', elements: src.elements.map((el, i) => tupleElementType(el) ? atKey(Literal(i)) : el) };
					// Over an object TS maps its MEMBERS, not `keyof`'s union, where a string index absorbs every literal key.
					const shape = resolveObjectType(src, scope);
					if (shape?.members.every(m => m.type !== 'property' && m.type !== 'method' || typeof m.key !== 'object'))
						return resolve(scope, TS.ObjectType(shape.members.flatMap(m => m.type === 'index'
							? [TS.TypeIndex(m.paramName, m.paramType, substituteType(t.valueType, new Map([[t.keyName, m.paramType]])), mapMemberModifiers(m.modifiers, t.modifiers))]
							: (m.type === 'property' || m.type === 'method') && typeof m.key !== 'object' && isPublicMember(m) ? [property(String(m.key))] : [])), depth - 1, stopAtRef);
				}
				const resolvedParts	= constraintParts.map(m => resolve(scope, m, depth - 1));
				const constraint	= resolvedParts.find(m => literalKeys(m)) ?? resolvedParts[0];
				const keys			= literalKeys(constraint);
				if (keys) {
					if (t.nameType) {
						// An `as` clause, as TS's resolveMappedTypeMembers: each key's OUTPUT name is `nameType` with that key substituted. A literal name is a
						// property, a `string`/`number`/`symbol` one an index signature, `never` none; values meeting at one name union. Any other name: opaque.
						const props = new Map<string, { values: Type[]; key: string | number }>(), indexes = new Map<string, { param: Type; values: Type[] }>();
						for (const key of keys) {
							const value = valueAtKey(t, Literal(key), scope);
							for (const named of unionMembers(resolve(scope, substituteType(t.nameType, new Map([[t.keyName, Literal(key)]])), depth - 1), scope)) {
								if (named.type === 'ref' && named.name === 'never')
									continue;
								if (isLiteral(named, 'string') || isLiteral(named, 'number')) {
									const at = props.get(String(named.value)) ?? props.set(String(named.value), { values: [], key }).get(String(named.value))!;
									at.values.push(value);
								} else if (isKeyable(named)) {
									const at = indexes.get(typeId(named)) ?? indexes.set(typeId(named), { param: named, values: [] }).get(typeId(named))!;
									at.values.push(value);
								} else {
									return t;
								}
							}
						}
						return resolve(scope, TS.ObjectType([
							...[...props].map(([name, p]) => TS.TypeProperty(name, combineTypes(p.values), modifiersFor(p.key))),
							...[...indexes.values()].map(i => TS.TypeIndex('key', i.param, combineTypes(i.values), t.modifiers)),
						]), depth - 1, stopAtRef);
					}

					return resolve(scope, TS.ObjectType(keys.map(property)), depth - 1, stopAtRef);
				}
				// Non-literal keys (`Record<string,T>`, `keyof {p: X, [k: string]: X}`) are an index signature beside a property per literal key;
				// a homomorphic `valueType` referencing its own key substitutes the index type in. An `as` clause cannot remap such a key: opaque.
				if (!t.nameType) {
					const parts		= unionMembers(constraint, scope).map(m => resolve(scope, m));
					const indexed	= parts.filter(isKeyable);
					const named		= literalKeys(combineTypes(parts.filter(m => !isKeyable(m))));
					if (indexed.length && named) {
						const index = combineTypes(indexed);
						return resolve(scope, TS.ObjectType([
							...named.map(property),
							TS.TypeIndex('key', index, substituteType(t.valueType, new Map([[t.keyName, index]])), t.modifiers),
						]), depth - 1, stopAtRef);
					}
				}
				break;
			}

			case 'indexed_access': {
				// `T[K]`: resolvable when the index resolves to literals (each member looked up), or is the `number` TYPE (`typeof LIB_DECLS[number]`).
				const index = resolve(scope, t.index);
				// `T[number]` is every position: an array's element, a tuple's elements unioned. A numeric literal into a tuple (`FlatArray`) reads one position.
				if (isRef(index, 'number') || isLiteral(index, 'number')) {
					const object	= resolve(scope, t.object);
					const read		= object.type === 'array' ? object.element
						: object.type !== 'tuple' ? undefined
						: isLiteral(index, 'number') ? tupleReadType(object, index.value, scope) ?? ANY
						: combineTypes(elementTypes(object, scope));
					if (read)
						return resolve(scope, read, undefined, stopAtRef);
				}
				// A mapped type's value for ANY index: `{[K in C]: V}[X]` is `V` with `K := X`, so `Partial<T>` composes over another mapped type. Peeling
				// aliases, not a full `resolve`, which would already have reduced a `Record<string,T>`-shaped mapped type to an index object.
				const peeled = peelAliases(t.object, scope, depth);

				// A concrete union index instantiates the value once per key, as TS does: `{[T in K]: S<T, E[T]>}[K]` keeps each `T` with its `E[T]`.
				if (peeled.type === 'mapped') {
					const mapped = peeled, keys = mentionsAbstract(t.index, scope) ? [t.index] : unionMembers(t.index, scope);
					return resolve(scope, combineTypes(keys.map(k => substituteType(mapped.valueType, new Map([[mapped.keyName, k]])))), depth - 1, stopAtRef);
				}

				const object	= resolve(scope, t.object, depth - 1);
				const indexKeys	= (index.type === 'union' ? index.types : [index]).map(literalKey);
				const keys		= indexKeys.every(k => k !== undefined) ? indexKeys as string[] : undefined;
				if (keys) {
					// An OPTIONAL property's `T['k']` includes `undefined`, as TS gives it; `lookupMember` answers the declared type alone.
					const parts = keys.map(key => {
						const m = lookupMember(object, key, scope);
						return m && optional(m, memberOptional(object, key, scope));
					});
					if (parts.every(p => !!p))
						return resolve(scope, combineTypes(parts), depth - 1, stopAtRef);
				}
				// A union's `T[K]` is each member's, as TS distributes it: `(TSEnum | Record<string, V>)[string]`.
				if (object.type === 'union') {
					const parts = object.types.map(m => resolve(scope, { type: 'indexed_access', object: m, index: t.index }, depth - 1, stopAtRef));
					if (parts.every(p => p.type !== 'indexed_access'))
						return combineTypes(parts);
				}
				// A non-literal key reads the index signature covering it (`Record<string,V>[string]`), each key of a union its own, a number key a string
				// one too (`Foo[keyof Foo]` with `keyof Foo = string | number`).
				const indexes = object.type === 'object' ? indexMembers(object.members) : [];
				if (indexes.length) {
					const parts		= unionMembers(index, scope).map(k => (indexes.find(m => isAssignable(k, m.paramType, scope))
						?? (isNumberLike(k, scope) ? indexes.find(m => isRef(m.paramType, 'string')) : undefined))?.typeAnnotation);
					if (parts.length && parts.every(p => !!p))
						return resolve(scope, combineTypes(parts), depth - 1, stopAtRef);
				}
				break;
			}
			case 'keyof': {
				// `keyof any` is every legal key type, tested on the raw argument: `resolve` also answers `ANY` when it gives up.
				if (isAny(t.argument))
					return TS.UnionType([TS.RefType('string'), TS.RefType('number'), TS.RefType('symbol')]);
				// A computed key's type is its expression's: `[G.H]` is `typeof G.H`, the enum member.
				const keyType = (key: JS.Key<Type>): Type | undefined => {
					if (typeof key !== 'object')
						return Literal(key);
					const e = key.computed, path = e.type === 'identifier' || e.type === 'member' ? pathKey(e) : undefined;
					return e.type === 'literal' && (typeof e.value === 'string' || typeof e.value === 'number') ? Literal(e.value) : path ? { type: 'typeof', name: path } : undefined;
				};
				// TS's key sets: a mapped type's is its constraint (`keyof Record<string, T>` is `string`); an object's, its property keys and index key types
				// (a string index admitting numbers); a union's, the keys ALL members have, an intersection's ANY part's. Aliases are peeled, not resolved.
				const keysOf = (raw: Type, depth: number): Type | undefined => {
					if (depth < 0)
						return undefined;
					const peeled	= peelAliases(raw, scope, depth);
					const t			= peeled.type === 'mapped' || peeled.type === 'union' || peeled.type === 'intersection' ? peeled : resolve(scope, peeled, depth - 1);
					// A remapped key (`as N`) is `N` at each key, as TS: over `keyof T` each of `T`'s own member keys and index key types (`'str'` beside a
					// string index), else each member of the constraint; a `never` drops it. Over an unbound constraint it stays deferred (`isAssignable`
					// relates a key as the constraint's). A symbol-valued key is kept as itself: without `unique symbol` `Record<typeof sym, X>` misreads.
					if (t.type === 'mapped' && t.nameType) {
						const at		= (k: Type) => resolve(scope, substituteType(t.nameType!, new Map([[t.keyName, k]])), depth - 1);
						const arg		= t.constraint.type === 'keyof' ? resolve(scope, t.constraint.argument, depth - 1) : undefined;
						const keySet	= arg ?? resolve(scope, t.constraint, depth - 1);
						if (mentionsAbstract(keySet, scope))
							return undefined;
						const source	= arg && resolveObjectType(arg, scope);
						const keys		= source ? source.members.flatMap(m => m.type === 'property' || m.type === 'method' ? isPublicMember(m) && keyType(m.key) || []
							: m.type === 'index' ? [m.paramType] : []) : unionMembers(arg ? resolve(scope, t.constraint, depth - 1) : keySet, scope);
						return combineTypes(keys.map(k => k.type === 'typeof' ? k : at(k)));
					}
					if (t.type === 'mapped')
						return t.constraint;
					if (t.type === 'object')
						return combineTypes(t.members.flatMap(m => m.type === 'property' || m.type === 'method' ? isPublicMember(m) && keyType(m.key) || []
							: m.type === 'index' ? isRef(m.paramType, 'string') ? [m.paramType, NUMBER] : [m.paramType] : []));
					if (t.type === 'intersection' || t.type === 'union') {
						// A union's `never` member (one only its resolution shows) adds no value, so it constrains no key.
						const parts = (t.type === 'union' ? t.types.filter(p => !isRef(resolveOwn(p, scope), 'never')) : t.types).map(p => keysOf(p, depth - 1));
						if (parts.every(p => !!p))
							return t.type === 'intersection' ? combineTypes(parts) : intersectTypes(parts);
					}
					return undefined;
				};
				const keys = keysOf(t.argument, depth - 1);
				if (keys)
					return resolve(scope, keys, depth - 1, stopAtRef);
				break;
			}
			case 'conditional': {
				// Only once `checkType` is concrete, as TS defers a conditional until its naked check type is instantiated.
				const check = resolve(scope, t.checkType, depth - 1);
				// Distributed only once concrete: over an unbound parameter TS defers, and deciding per member against an abstract
				// `extends` (`Extract<INode, {type: T}>`) would match everything.
				if (t.distribute && !isAny(check) && !isAbstract(check, scope) && !(containsKind(t.extendsType, 'infer') && mentionsAbstract(t.checkType, scope))) {
					const members = unionMembers(check, scope);
					if (members.length !== 1)
						return members.length ? combineTypes(members.map(m => resolve(scope, t.distribute!(m), depth - 1, stopAtRef))) : NEVER;
				}
				// An INDEXED ACCESS has no identity worth keeping raw, and raw it matches nothing (`ElemValue<[Box<number>, ':'][0]>` must see `Box<number>`).
				const checkType = oneStepIndexed(t.checkType, scope);
				if (!isAny(check) && !isAbstract(check, scope)) {
					if (containsKind(t.extendsType, 'infer')) {
						// As TS: each `infer X` is a type parameter inferred from the check type (unresolved: keeps a named type's identity) as a
						// call infers; the pattern, instantiated (uninferred at its constraint, else `unknown`), is what the check type must extend.
						const params	= new Map<string, TS.TypeParam>();
						const pattern	= walker(undefined, undefined, rewriteOnce((x: Type, process: <T extends Type>(x: T) => T) => x.type === 'infer'
							? (params.set(x.name, { ...TS.TypeParam(x.name, x.constraint), const: true }), TS.RefType(x.name)) : process(x))).type(t.extendsType) ?? t.extendsType;
						// As TS's getTypeFromInference: covariant candidates union, contravariant ones intersect (`UnionToIntersection`).
						const inference	= new Inference([...params.values()], scope, scope);
						inferTypeArgs(pattern, checkType, params, inference, scope);
						const bindings	= new Map([...params].map(([name, p]) => [name, inference.union(name) ?? p.constraint ?? UNKNOWN] as const));
						const fits		= [...params].every(([name, p]) => !p.constraint || isAssignable(bindings.get(name)!, p.constraint, scope))
							&& isAssignable(checkType, substituteType(pattern, bindings), scope);
						// A taken branch IS the result, spending no depth: a long `A ? X : B ? Y : ...` chain bailed to `any`, leaving every enclosing resolution uncached.
						return resolve(scope, fits ? substituteType(t.trueType, bindings) : t.falseType, depth, stopAtRef);
					} else {
						// Stricter than `isAssignable`: in TS's `extends` a bare `number` does NOT extend a literal union. Undefined from `isLiteralOnly` stays opaque.
						const extendsType = resolve(scope, t.extendsType, depth - 1);
						const lit = isPrimitive(check) ? isLiteralOnly(extendsType, scope) : false;
						// `t.checkType` unresolved keeps the ref identity `isAssignable`'s same-name fast path needs. Over unbound parameters, as TS: true only if it
						// holds with them opaque, false only if it fails with them `any`, else it waits on the instantiation, both branches meanwhile.
						if (lit !== undefined) {
							if (!lit && isAssignable(checkType, extendsType, scope))
								return resolve(scope, t.trueType, depth, stopAtRef);
							const open = mentionsAbstract(checkType, scope) || mentionsAbstract(extendsType, scope);
							if (!lit && open && isAssignable(permissive(checkType, scope), permissive(extendsType, scope), scope))
								return deferred(t, scope);
							return resolve(scope, t.falseType, depth, stopAtRef);
						}
					}
				} else if (!containsKind(t.extendsType, 'infer')) {
					// An `any` check type takes both branches, as TS's does; an unbound one waits.
					return isAny(check) ? resolve(scope, deferredBranches(t), depth - 1, stopAtRef) : deferred(t, scope);
				}
				break;
			}
			case 'typeof': {
				// The query's own `declScope` wins, as for a `ref`: the name is a VALUE in its declaring module.
				const qScope = declScopeOf(t, scope);
				const parts = t.name.split('.');
				let v		= qScope.value(parts[0]);
				for (let i = 1; v && i < parts.length; i++)
					v = lookupMember(v, parts[i], qScope);
				// A queried `undefined`/`null` widens to `any` without `strictNullChecks`, as TS's widening nullish types do (`typeof undefined`).
				const q = v && resolve(qScope, t.typeArgs ? instantiateExpression(v, t.typeArgs, qScope) : v, depth - 1, stopAtRef);
				return !q || (isNullOrUndefined(q) && !scope.strictNullChecks()) ? ANY : q;
			}
			case 'intersection': {
				const reduced = reduceIntersection(t, scope, depth);
				return reduced ? resolve(scope, reduced, depth - 1, stopAtRef) : t;
			}

			case 'ref':
				if (stopAtRef)
					return t;
				if (!INTRINSIC_TYPES.has(t.name)) {
					// The ref's own `declScope` wins for lookup, kept local: `uncached` shares `scope` with `resolve`'s resolving-set bookkeeping.
					const refScope		= declScopeOf(t, scope);
					const [ns, name]	= refScope.qualified(t.name);
					if (!ns)
						return t;

					// A ref naming a real CLASS keeps its nominal identity: classes are dispatched by NAME. A consumer wanting the MEMBERS asks `resolveMembers`.
					if (isClassRef(t, refScope))
						return t;
					const entry = ns.type(name);
					// A type parameter is opaque, as TS's: its constraint bounds what it IS (`resolveMembers` reads members through it), never what it resolves to.
					if (entry?.isTypeParam)
						return t;
					if (entry) {
						const tparams = entry.typeParams;
						if (!tparams?.length)
							return resolveAliasBody(ns, entry, [], () => entry.type, stopAtRef, t);
						if (!t.typeArgs)
							return resolveAliasBody(ns, entry, [], () => entry.defaultSubstitution ??= substituteType(entry.type, typeArgMap(tparams, undefined)), stopAtRef, t);
						const args = [...typeArgMap(tparams, t.typeArgs).values()];
						// TS's `intrinsic` aliases mean what their NAME says: `NoInfer<T>` is `T` (only inference skips it).
						if (entry.type.type === 'ref' && entry.type.name === 'intrinsic' && name === 'NoInfer')
							return resolve(scope, args[0], depth, stopAtRef);
						return resolveAliasBody(ns, entry, args, () => substituteType(entry.type, new Map(tparams.map((p, i) => [p.name, args[i]]))), stopAtRef, t);
					}
				}
				break;

		}
		return t;
	}
}

export function resolveOwn(t: Type, scope: Scope): Type {
	return resolve(ownScope(t, scope), t);
}

// The one direction `resolve` will not go: a named class into its structural member list. Opt-in, where the MEMBERS are wanted (`lookupMember`);
// one level only, the members keeping their own nominal refs.
export function resolveMembers(t: Type, scope: Scope, depth = 10): Type {
	const r = resolveOwn(t, scope);
	if (r.type !== 'ref' || INTRINSIC_TYPES.has(r.name))
		return r;
	const [ns, name]	= declScopeOf(r, scope).qualified(r.name);
	const entry			= ns?.type(name);
	if (!ns || !entry)
		return r;
	// A class adding no members reduces to its base's nominal ref (`{} & A` is `A`), whose members are then the class's.
	const members = resolve(ns, instantiateEntry(entry, r.typeArgs), depth - 1);
	return members.type === 'ref' && members !== r && depth > 0 ? resolveMembers(members, ns, depth - 1) : members;
}

// Every member a union could BE: `resolve` leaves a union's MEMBERS alone, and one may resolve to a further union (`AB | C`); `never` is dropped,
// as nothing inhabits it. Use this instead of walking `.types`; a non-union is itself.
export function unionMembers(t: Type, scope: Scope, depth = 8): Type[] {
	const r = resolve(scope, t);
	if (r.type === 'union' && depth > 0)
		return r.types.flatMap(m => unionMembers(m, scope, depth - 1));
	// The RAW `t`: resolving only DISCOVERS nesting, and a consumer matching on nominal identity (a class's name and type args) needs the reference.
	return isRef(r, 'never') ? [] : [t];
}

export function flattenIntersection(t: Type, scope: Scope): Type[] {
	const r = resolveOwn(t, scope);
	return r.type === 'intersection' ? r.types.flatMap(t => flattenIntersection(t, scope)) : [r];
}

// Any `Type` down to one flat `ObjectType`, an intersection's parts (possibly unresolved refs) merged, so every caller agrees on the shape.
export function resolveObjectType(t: Type, scope: Scope): TS.ObjectType | undefined {
	const w = resolve(scope, t);
	if (w.type === 'object')
		return w;
	if (w.type === 'intersection') {
		const merged = mergeIntersection(TS.IntersectionType(flattenIntersection(w, scope)));
		return merged.type === 'object' ? merged : undefined;
	}
	return undefined;
}

// Every object shape a union expands to, beside its RAW member: an owner lookup resolves a named interface by NAME to the class the dispatch
// side builds, where the name-stripped shape would build a structural twin.
export function objectShapes(t: Type, scope: Scope): { raw: Type; objT: TS.ObjectType }[] {
	return unionMembers(t, scope).flatMap(raw => {
		const objT = resolveObjectType(raw, scope);
		return objT ? [{ raw, objT }] : [];
	});
}

// The object shape two types share field-wise, each field widened to their union.
export function unionShapes(a: Type, b: Type, scope: Scope): TS.ObjectType | undefined {
	const ra = resolveObjectType(a, scope), rb = resolveObjectType(b, scope);
	if (!ra || !rb)
		return undefined;
	const other = new Map(rb.members.flatMap(m => m.type === 'property' && JS.keyName(m.key) !== undefined ? [[JS.keyName(m.key)!, m.typeAnnotation] as const] : []));
	return TS.ObjectType(ra.members.map(m => m.type === 'property' && other.has(JS.keyName(m.key)!)
		? { ...m, typeAnnotation: combineTypes([m.typeAnnotation, other.get(JS.keyName(m.key)!)!]) }
		: m));
}

// LEVEL-ORDER, as TS orders inherited call signatures by depth (resolution is first-fit): depth-first buries a derived signature behind a
// sibling base's catch-all.
export function collectMembers(t: Type, scope: Scope): TS.TypeMember[] {
	const out: TS.TypeMember[] = [];
	const seen = new Set<Type>();
	for (let level = [t]; level.length; ) {
		const next: Type[] = [];
		for (const p of level) {
			if (seen.has(p))
				continue;
			seen.add(p);
			const r = resolveMembers(p, scope);
			if (r.type === 'object')
				out.push(...r.members);
			else if (r.type === 'intersection')
				next.push(...[...r.types].reverse());
		}
		level = next;
	}
	return out;
}

// ===================================================================
//  Arrays, tuples and rest parameters
// ===================================================================

// `T[]` really is `Array<T>` (`readonly`: `ReadonlyArray<T>`), compared as the named ref instead of bridging two forms at every site.
function normalizeArray(t: Type): Type {
	return t.type === 'array' ? TS.RefType(t.readonly ? 'ReadonlyArray' : 'Array', [t.element]) : t;
}
// The element type of an array: a `T[]` node, or an `Array<T>`/`ReadonlyArray<T>` ref (what `normalizeArray` makes of one).
export function arrayLikeElement(t: Type): Type | undefined {
	return t.type === 'array' ? t.element
		: t.type === 'ref' && (t.name === 'Array' || t.name === 'ReadonlyArray') && t.typeArgs?.length ? t.typeArgs[0]
		: undefined;
}

// A spread contributes no single element; an optional element `T?` contributes `T`. `te` is undefined past a tuple's end (`[1, 2, 3]` against
// `[number, number]`): no contextual type there.
export function tupleElementType(te: TS.TupleElement | undefined): Type | undefined {
	return !te || te.type === 'spread' ? undefined : te.type === 'optional' || te.type === 'labeled' ? te.element : te;
}

// A READ of position `i` (TS's getIndexedAccessType): an optional element may be absent, so it reads `T | undefined`; a position a
// rest spread covers reads the spread's element or any fixed one after it; no type at all past a fixed-length tuple's end.
export function tupleReadType(t: Extract<Type, { type: 'tuple' }>, i: number, scope: Scope): Type | undefined {
	const spreadAt = t.elements.findIndex(e => e.type === 'spread');
	if (spreadAt >= 0 && i >= spreadAt)
		return combineTypes(elementTypes({ ...t, elements: t.elements.slice(spreadAt) }, scope));
	const el = t.elements[i];
	if (!el)
		return undefined;
	const v = tupleElementType(el)!;
	return el.type === 'optional' || (el.type === 'labeled' && el.optional) ? combineTypes([v, UNDEFINED]) : v;
}

// A tuple's elements with each spread of a tuple spliced in (TS normalizes `[...[A, B], C]` to `[A, B, C]`); a spread of an array stays.
export function flatTupleElements(t: Extract<Type, { type: 'tuple' }>, scope: Scope, depth = 4): TS.TupleElement[] {
	return t.elements.flatMap(e => {
		const r = e.type === 'spread' && depth > 0 ? resolveOwn(e.argument, scope) : undefined;
		return r?.type === 'tuple' ? flatTupleElements(r, scope, depth - 1) : [e];
	});
}

// The declared type at REST position `k`: the rest's element, a TUPLE rest's own position; every arm of a union of those shapes answers
// (`[(self) => R<T>] | R<T>[]` names a callback in one), and `resolveFnMember` picks the function out.
export function restArgType(rest: Type, k: number, scope: Scope, depth = 4): Type | undefined {
	const r = resolveOwn(rest, scope);
	const element = arrayLikeElement(r);
	if (element)
		return element;
	if (r.type === 'tuple') {
		const el = r.elements[k];
		return !el ? undefined
			: el.type === 'labeled' || el.type === 'optional' ? el.element
			: el.type === 'spread' ? restArgType(el.argument, 0, scope, depth - 1)
			: el;
	}
	if (r.type === 'union' && depth > 0) {
		const parts = r.types.map(t => restArgType(t, k, scope, depth - 1)).filter((t): t is Type => !!t);
		return parts.length ? combineTypes(parts) : undefined;
	}
	return undefined;
}

// Every value an array, a tuple (a spread contributing what it spreads) or a union of them can hold.
// A rest parameter is physically always one array, whose element these combine into.
export function elementTypes(t: Type, scope: Scope, depth = 4): Type[] {
	const r			= resolveOwn(t, scope);
	const element	= arrayLikeElement(r);
	return element ? [element]
		: r.type === 'tuple' ? r.elements.flatMap(e => e.type === 'spread' ? elementTypes(e.argument, scope, depth - 1) : tupleElementType(e) ?? [])
		: r.type === 'union' && depth > 0 ? r.types.flatMap(m => elementTypes(m, scope, depth - 1))
		: [];
}

// A union of arrays/tuples as ONE array of the combined element, what TS (5.2+) calls a method on when the signatures do not merge (`(Ty[] | Lit[]).map`).
export function arrayUnionAsArray(t: Type, scope: Scope): TS.ArrayType | undefined {
	const r = resolve(scope, t);
	if (r.type !== 'union')
		return undefined;
	const members = r.types.map(m => resolve(scope, m));
	return members.every(m => m.type === 'array' || m.type === 'tuple')
		? TS.ArrayType(combineTypes(members.flatMap(m => elementTypes(m, scope))), members.some(m => !!m.readonly))
		: undefined;
}

// ===================================================================
//  Member lookup
// ===================================================================

// The `property`/`method` member (the only kinds carrying `modifiers`) named `key` in `members`, if any.
function findTypeMember(members: TS.TypeMember[], key: string): TS.TypeMember & { modifiers?: string[] } | undefined {
	return members.find(m => (m.type === 'property' || m.type === 'method') && memberKey(m.key) === key);
}

// What `keyof` sees: neither a `private`/`protected` member nor a `#name`.
function isPublicMember(m: { modifiers?: string[]; key: unknown }) {
	return !m.modifiers?.some(x => x === 'private' || x === 'protected') && !(typeof m.key === 'string' && m.key.startsWith('#'));
}

type IndexMember = Extract<TS.TypeMember, { type: 'index' }>;
function indexMembers(members: TS.TypeMember[]): IndexMember[] {
	return members.filter((m): m is IndexMember => m.type === 'index');
}

// The shape an `interface` declares (checker's hoist): unlike an object literal TYPE it has no implicit index signature.
export const declaredShapes = new WeakSet<Type>();
// Whether a value written as `t` has TS's implicit index signature: an object literal type (or an alias to one) does; an interface or class does not.
export function hasImplicitIndex(t: Type, scope: Scope): boolean {
	if (t.type === 'intersection')
		return t.types.every(p => hasImplicitIndex(p, scope));
	if (t.type !== 'ref')
		return !declaredShapes.has(t);
	// `object` and the primitives (through their boxed interfaces) have no implicit index signature either.
	if (INTRINSIC_TYPES.has(t.name))
		return false;
	if (isClassRef(t, scope))
		return false;
	const entry = declScopeOf(t, scope).lookupType(t.name)?.type;
	return !entry || (entry !== t && hasImplicitIndex(entry, scope));
}

// A property name that is an array index (`'0'`, `'12'`), as a numeric index signature or a tuple position covers.
function isIndexKey(prop: string): boolean {
	return /^(0|[1-9]\d*)$/.test(prop);
}

// The value type of a numeric index signature reachable from `t`, through every intersection part (declaration merging, `lib/typedarray.ts`):
// `resolve` never flattens them. For `lookupMember`'s intersection fallback and the checker's computed `case 'index'`.
export function indexSignatureOf(t: Type, scope: Scope, depth = 6): Type | undefined {
	if (depth < 0)
		return undefined;
	const numeric	= (members: TS.TypeMember[]) => indexMembers(members).find(m => isNumberLike(m.paramType, scope))?.typeAnnotation;
	const r			= resolveOwn(t, scope);
	// A primitive is indexed through its boxed lib interface (`string`'s `String`, `readonly [index: number]: string`), as `lookupMember` reads it.
	const primitive	= r.type === 'ref' ? r.name : r.type === 'range' ? r.base : r.type === 'literal' ? (Array.isArray(r.value) ? 'string' : typeof r.value) : undefined;
	const boxed		= primitive && scope.semantics.boxed(primitive);
	if (boxed)
		return indexSignatureOf(TS.RefType(boxed), scope, depth - 1);
	if (r.type === 'object') {
		const own = numeric(r.members);
		if (own)
			return own;
	}
	if (r.type === 'intersection') {
		// Last part first: every producer of an intersection puts the more concrete declaration last (`NodeListOf<T>` beats its inherited `NodeList`).
		for (const part of [...r.types].reverse()) {
			const found = indexSignatureOf(part, scope, depth - 1);
			if (found)
				return found;
		}
	}
	// A class INHERITS its base's index signature (`class Buffer extends TypedArray<u8>`), surfaced by `collectMembers`; last, so a closer declaration wins.
	return numeric(collectMembers(t, scope));
}

// The index signature among `members` that covers key `prop`: a numeric one only a numeric-looking key (it is the more
// specific, as TS requires), a string one every key. A numeric signature must not answer `'push'` for `String`'s `[i: number]`.
function indexSignatureFor(members: TS.TypeMember[], prop: string, scope: Scope): Type | undefined {
	const indexes = indexMembers(members);
	// A well-known symbol key (`memberKey`'s `[Symbol.iterator]`) is covered only by a `symbol` index signature, never a string one.
	if (prop.startsWith('[Symbol.'))
		return indexes.find(m => unionMembers(m.paramType, scope).some(p => isRef(resolveOwn(p, scope), 'symbol')))?.typeAnnotation;
	return ((isIndexKey(prop) && indexes.find(m => isNumberLike(m.paramType, scope))) || indexes.find(m => !isNumberLike(m.paramType, scope)))?.typeAnnotation;
}

// Cached on (t, prop) alone: every real call starts at the default depth. `skipObjectFallback`: an intersection part must not answer from
// `Object.prototype`, or the first-match search stops before a later part's real declaration. `write`: what an assignment to `prop` accepts.
export function lookupMember(t: Type, prop: string, scope: Scope, depth = 10, skipObjectFallback = false, write = false): Type | undefined {
	const key	= (skipObjectFallback ? prop + '\0skip' : prop) + (write ? '\0write' : '');
	let keyMap	= scope.lookupMemberCache?.get(t);
	if (!keyMap)
		(scope.lookupMemberCache ??= new WeakMap).set(t, keyMap = new Map());
	if (keyMap.has(key))
		return keyMap.get(key);

	const result = uncached();

	keyMap.set(key, result);
	return result;

	function uncached(): Type | undefined {
		if (depth < 0) {
			scope.hitDepthLimit('lookupMember');
			return ANY;
		}
		// A bare `ref` stamped with its own `declScope` resolves there instead of in `scope` -- the caller's chain may shadow it (e.g. DOM's `Element`).
		t = resolveMembers(t, scope, depth);
		// A LITERAL type, or a numeric range, has the members of its primitive (`'a,b'.split(/,/)`, `(255).toString(16)`).
		if (t.type === 'literal' || t.type === 'range')
			t = widenLiterals(t);
		const refined = !write && scope.semantics.refinedMember(t, prop, scope, depth);
		if (refined)
			return refined;

		switch (t.type) {
			// An array's members are its lib's `Array<T>`'s.
			case 'array':
				return lookupMember(TS.RefType('Array', [t.element]), prop, scope, depth - 1, false, write);

			case 'tuple': {
				// A tuple's positions are real properties (`'0'`, `'1'`, ...), which is what lets a union of tuples be indexed and discriminated.
				const at = isIndexKey(prop) && !t.elements.slice(0, +prop).some(el => el.type === 'spread') ? tupleElementType(t.elements[+prop]) : undefined;
				return at ?? lookupMember(TS.RefType('Array', [combineTypes(elementTypes(t, scope))]), prop, scope, depth - 1, false, write);
			}

			case 'object': {
				const ms = t.members.filter(m => (m.type === 'property' || m.type === 'method') && memberKey(m.key) === prop);
				if (ms.length > 1) {
					// Real overloads (all same-named `method`s) group into one multi-signature callable, as `hoist` builds for function overloads.
					return ms.every(m => m.type === 'method')
						? TS.ObjectType(ms.map((m): TS.TypeMember => TS.TypeCall(withScope(TS.CallSig({ params: m.params, rest: m.rest, returnType: m.returnType ?? ANY, typeParams: m.typeParams, origin: m.origin }), m.declScope as Scope))))
						: ANY;
				}
				const m = ms[0];
				if (m?.type === 'property')
					return write && m.writeType || m.typeAnnotation;
				if (m?.type === 'method')
					// `declScope` carried: a method consulted from another module resolves its types in its own.
					return withScope(TS.FunctionType({ ...methodSignature(m), origin: m.origin }), m.declScope as Scope);
				// Both fallbacks run only when no member is named `prop`; skipped per intersection part, so one part's index signature cannot shadow another's member.
				if (skipObjectFallback)
					return undefined;
				// The apparent members (`Object.prototype`'s) before an index signature, as TS's getPropertyOfType: `r.hasOwnProperty` on a `Record<string, V>`
				// is the method. A NUMERIC index signature covers only a numeric-looking key (`'byteLength'` is no element of `[i: number]: u8`), and wins over a string one.
				return scope.semantics.apparentMember(prop, t.members.some(m => m.type === 'call' || m.type === 'construct'), scope)
					?? indexSignatureFor(t.members, prop, scope);
			}
			case 'function':
			case 'constructor':
				return scope.semantics.apparentMember(prop, true, scope);
			case 'intersection': {
				const matches: Type[] = [];
				for (const part of t.types) {
					const m = lookupMember(part, prop, scope, depth - 1, true, write);
					if (m)
						matches.push(m);
				}
				// No part declares `prop` as a member: `Object.prototype`'s, then an index signature on any part covers the key, as in TS.
				if (!matches.length) {
					if (skipObjectFallback)
						return undefined;
					const apparent = scope.semantics.apparentMember(prop, false, scope);
					if (apparent)
						return apparent;
					for (const part of [...t.types].reverse()) {
						const r = resolveOwn(part, scope);
						const idx = r.type === 'object' ? indexSignatureFor(r.members, prop, scope) : undefined;
						if (idx)
							return idx;
					}
					return undefined;
				}
				// A class's own declaration overrides its base's (`declare superClass?: Sub` re-narrowing an inherited field).
				if (matches.length === 1 || t.derived)
					return matches[0];
				// Declaration merging usually declares `prop` identically in several parts: deduped first. A machine type keys as `number` (an ambient interface
				// says `number`, its implementing class `i32`; the class, hoisted later, survives), WITH declaring scopes (two modules' `ClassInfo`s differ).
				const dedupKey = (m: Type) => typeId(machineOf(m, scope) ? NUMBER : m, true);
				const distinct = [...new Map(matches.map(m => [dedupKey(m), m])).values()];
				if (distinct.length === 1)
					return distinct[0];
				// Different same-named methods across parts are TS's cross-file overload merge: one multi-signature set, reversed so the concrete class's
				// signature is tried before an ambient interface stub's (overload resolution is first-fit).
				const sigs: TS.CallSig[] = [];
				let allSigs = true;
				for (const m of [...distinct].reverse()) {
					if (m.type === 'function') {
						sigs.push(m);
					} else if (m.type === 'object' && m.members.length && m.members.every(mem => mem.type === 'call')) {
						sigs.push(...m.members);
					} else {
						allSigs = false;
						break;
					}
				}
				if (allSigs)
					return TS.ObjectType(sigs.map((s): TS.TypeMember => ({ type: 'call', params: s.params, rest: s.rest, returnType: s.returnType, typeParams: s.typeParams, origin: s.origin })));
				// A property narrowed by several parts (`SomeUnion & {kind: 'x'}`) takes every constraint together (`&` has no override order); a part of unit
				// types (`kind: Kind` under `kind: Kind.A`) reduces it to the units every part admits, as TS does.
				const units = distinct.map(m => unionMembers(m, scope)).find(ms => ms.every(u => resolveOwn(u, scope).type === 'literal'));
				return units ? combineTypes(units.filter(u => distinct.every(p => isAssignable(u, p, scope)))) : TS.IntersectionType(distinct);
			}
			case 'union': {
				// A `never` member adds nothing to a union (TS absorbs it), so it constrains no member.
				const live	= t.types.filter(p => !isRef(resolveOwn(p, scope), 'never'));
				const parts	= live.map(p => lookupMember(p, prop, scope, depth - 1, false, write));
				return parts.every(p => !!p) ? (parts.length ? combineTypes(parts as Type[]) : NEVER) : undefined;
			}
			// A primitive auto-boxes for member access (`"x".toUpperCase()`): its boxed lib interface's members.
			case 'ref': {
				const boxed = scope.semantics.boxed(t.name);
				return boxed ? lookupMember(TS.RefType(boxed), prop, scope, depth - 1, false, write) : undefined;
			}
			default:
				return undefined;
		}
	}
}

// A member of the global type `name` as the lib declares it.
function globalTypeMember(name: string, prop: string, scope: Scope): Type | undefined {
	const root = scope.root();
	return root.type(name) ? lookupMember(TS.RefType(name), prop, root, 4, true) : undefined;
}

// The shared vocabulary's apparent members, for a language's `apparentMember`: every value's are the global `Object`'s,
// and anything callable has `Function`'s (`apply`/`call`/`bind`, or Python's `__call__`) first.
export function objectMember(prop: string, callable: boolean, scope: Scope): Type | undefined {
	return (callable ? globalTypeMember('Function', prop, scope) : undefined) ?? globalTypeMember('Object', prop, scope);
}

export function memberOptional(t: Type, prop: string, scope: Scope, depth = 6): boolean {
	return memberOptionalState(t, prop, scope, depth) === 'optional';
}

// `undefined`: this part does not declare `prop`, so (within an intersection) it neither requires it nor makes it optional.
function memberOptionalState(t: Type, prop: string, scope: Scope, depth: number): 'optional' | 'required' | undefined {
	t = resolveMembers(t, scope, depth);
	if (t.type === 'object') {
		const m = findTypeMember(t.members, prop);
		return m ? (hasMod(m, 'optional') ? 'optional' : 'required') : undefined;
	}
	if (t.type !== 'intersection' && t.type !== 'union')
		return undefined;
	if (depth <= 0) {
		scope.hitDepthLimit('memberOptional');
		return undefined;
	}
	// A union's read is each member's read, so one member marking `prop` optional makes the whole read possibly undefined.
	if (t.type === 'union') {
		const states = t.types.map(p => memberOptionalState(p, prop, scope, depth - 1));
		return states.includes('optional') ? 'optional' : states.every(s => s === 'required') ? 'required' : undefined;
	}
	// Optional in `A & B` only if every part declaring it says so, as `lookupMember`'s intersection case.
	let anyOptional = false;
	for (const p of t.types) {
		const s = memberOptionalState(p, prop, scope, depth - 1);
		if (s === 'required')
			return 'required';
		anyOptional ||= s === 'optional';
	}
	return anyOptional ? 'optional' : undefined;
}

// A member keyed by a symbol held in a VALUE (`[observable]`, a `unique symbol`, unmodelled) has no path to compare with: a type declaring one
// may have the member a computed key names, so its absence proves nothing.
function valueKeyed(t: Type, scope: Scope): boolean {
	return collectMembers(t, scope).some(p => (p.type === 'property' || p.type === 'method') && typeof p.key === 'object' && !memberKey(p.key)?.startsWith('[Symbol.'));
}

export function sealed(t: Type, scope: Scope, depth = 6, functions = false): boolean {
	if (depth < 0) {
		scope.hitDepthLimit('sealed');
		return false;
	}
	t = resolveMembers(t, scope);
	// A primitive has exactly its boxed interface's members (`'abc'.foo` is TS2339).
	const w		= widenLiterals(t);
	const boxed	= w.type === 'ref' ? scope.semantics.boxed(w.name) : undefined;
	if (boxed)
		return sealed(TS.RefType(boxed), scope, depth - 1, functions);
	return t.type === 'object' || (functions && t.type === 'function') || (t.type === 'intersection' && t.types.every(p => sealed(p, scope, depth - 1, functions)));
}

// ===================================================================
//  Signatures
// ===================================================================

// TS's getMinArgumentCount: through the last parameter a call must pass -- not optional (or defaulted), not accepting `void`, nor `omittable`.
export function minArgumentCount(sig: TS.Params, scope: Scope, omittable = (_i: number) => false): number {
	const own = sig.params;
	let n = own.length;
	while (n > 0 && (omittable(n - 1) || hasMod(own[n - 1], 'optional') || (own[n - 1].typeAnnotation && unionMembers(resolveOwn(own[n - 1].typeAnnotation!, scope), scope).some(m => m.type === 'ref' && m.name === 'void'))))
		n--;
	return n;
}

// The declared type of argument `i`: its own parameter's, or past them the rest parameter's at that position.
export function paramTypeAt(sig: TS.Params, i: number, scope: Scope): Type | undefined {
	return i < sig.params.length ? sig.params[i].typeAnnotation
		: sig.rest?.typeAnnotation && restArgType(sig.rest.typeAnnotation, i - sig.params.length, scope);
}

// Does `argTs` fit `sig` (arity, then each argument assignable)? `hasSpread`: a spread's count is unknown, so an upper arity mismatch is waived.
export function argsFit(sig: TS.CallSig, argTs: (Type | undefined)[], scope: Scope, hasSpread = false): boolean {
	if (argTs.length < sig.params.filter(p => !hasMod(p, 'optional')).length || (!sig.rest && !hasSpread && argTs.length > sig.params.length))
		return false;
	// `sig.declScope`: parameter types resolve in their declaring module.
	const dstScope = declScopeOf(sig, scope);
	// The arguments past the fixed parameters fill the rest as one tuple, as the call's own check reads them: `concat(0)` fits
	// `(...items: (T | ConcatArray<T>)[])`, not the `ConcatArray<T>[]` overload before it. A spread's elements are not known here.
	const rest = argTs.slice(sig.params.length).filter((t): t is Type => !!t);
	return argTs.every((t, i) => {
		const p = sig.params[i];
		return !t || !p?.typeAnnotation || isAssignable(t, hasMod(p, 'optional') ? TS.UnionType([p.typeAnnotation, UNDEFINED]) : p.typeAnnotation, scope, dstScope);
	}) && (hasSpread || !sig.rest?.typeAnnotation || !rest.length || isAssignable({ type: 'tuple', elements: rest }, sig.rest.typeAnnotation, scope, dstScope));
}

// The signatures of `kind` a value of type `t` is invoked through: a function/constructor type, or an object's (and an
// intersection's) call/construct members.
export function signaturesOf(t: Type, kind: 'call' | 'construct', scope: Scope): TS.CallSig[] {
	const r			= resolveOwn(t, scope);
	const fnKind	= kind === 'call' ? 'function' : 'constructor';
	const parts		= r.type === 'intersection' ? r.types.map(p => resolveOwn(p, scope)) : [r];
	return [
		...parts.flatMap(p => p.type === fnKind ? [p as TS.CallSig] : []),
		...collectMembers(r, scope).flatMap(m => m.type === kind ? [m] : []),
	];
}

// A callee's construct signatures as TS resolves them on an intersection (resolveIntersectionTypeMembers): a MIXIN part -- one
// construct signature taking only `...args: any[]` -- adds none of its own, and its instance type joins every other part's result.
export function constructSignatures(t: Type, scope: Scope): TS.CallSig[] {
	const parts: TS.CallSig[][] = [];
	const collect = (x: Type, depth: number): void => {
		const r = resolveOwn(x, scope);
		if (r.type === 'intersection' && depth > 0)
			r.types.forEach(p => collect(p, depth - 1));
		else if (r.type === 'constructor')
			parts.push([r]);
		else if (r.type === 'object' && r.members.some(m => m.type === 'construct'))
			parts.push(r.members.filter((m): m is TS.TypeMember & TS.CallSig => m.type === 'construct'));
	};
	collect(t, 8);
	const isMixin = (sigs: TS.CallSig[]) => {
		const rest = sigs.length === 1 && !sigs[0].params.length && sigs[0].rest?.typeAnnotation;
		const r = rest && resolveOwn(rest, scope);
		// TS's isMixinConstructorType: the rest is `any[]`, or `any` itself.
		return !!r && (isAny(r) || (r.type === 'array' && isAny(r.element)));
	};
	const mixin = parts.map(isMixin);
	if (mixin.length && mixin.every(m => m))
		mixin[0] = false;
	const mixed = parts.flatMap((sigs, i) => mixin[i] ? [sigs[0].returnType ?? ANY] : []);
	return parts.flatMap((sigs, i) => mixin[i] ? [] : mixed.length ? sigs.map(s => ({ ...s, returnType: TS.IntersectionType([s.returnType ?? ANY, ...mixed]) })) : sigs);
}

// TS's resolveUnionSignature: invoking a union invokes whichever member the value is, so an argument must suit every
// member and the result is any of their returns. For members with one signature each, none generic; TS stops at about
// the same. The parameters combine pairwise as TS's combineUnionParameters does.
export function unionSignature(t: Type, kind: 'call' | 'construct', scope: Scope): TS.CallSig | undefined {
	const r = resolveOwn(t, scope);
	if (r.type !== 'union')
		return undefined;
	const sigs = r.types.map(m => signaturesOf(m, kind, scope));
	if (sigs.some(s => s.length !== 1))
		return undefined;
	// As TS's getUnionSignatures, generic members combine only over IDENTICAL type parameter lists, renamed to the first's.
	const tps	= sigs[0][0].typeParams ?? [];
	const each	= sigs.map(([s]) => {
		const own = s.typeParams ?? [];
		if (own.length !== tps.length)
			return undefined;
		const rename = new Map(own.map((p, i) => [p.name, TS.RefType(tps[i].name) as Type]));
		const renamed = own.length ? substituteType({ ...s, type: 'function', typeParams: undefined } as Type, rename) as TS.CallSig : s;
		return own.every((p, i) => typeId(p.constraint ? substituteType(p.constraint, rename) : UNKNOWN) === typeId(tps[i].constraint ?? UNKNOWN)) ? renamed : undefined;
	});
	if (each.some(s => !s))
		return undefined;
	const combined = each.slice(1).reduce((a, b) => combineUnionParameters(a!, b!, scope), each[0])!;
	return { typeParams: tps.length ? tps : undefined, params: combined.params, rest: combined.rest, returnType: combineTypes(each.map(s => s!.returnType ?? ANY)) };
}

// Each position takes the intersection of both signatures' types there (a missing one constrains nothing), and is optional
// only where both allow no argument. The longer one's rest stays a rest; a rest only the shorter has becomes an extra one.
function combineUnionParameters(left: TS.CallSig, right: TS.CallSig, scope: Scope): TS.CallSig {
	const count		= (s: TS.CallSig) => s.params.length + (s.rest ? 1 : 0);
	const required	= (s: TS.CallSig) => s.params.reduce((n, p, i) => hasMod(p, 'optional') ? n : i + 1, 0);
	const typeAt	= (s: TS.CallSig, i: number) => paramTypeAt(s, i, scope);
	const both		= (a: Type | undefined, b: Type | undefined) => !a ? b ?? ANY : !b ? a : intersectTypes([a, b]);
	const [longest, shorter] = count(left) >= count(right) ? [left, right] : [right, left];
	const n			= count(longest);
	const params: TS.Param[] = [];
	let rest: TS.CallSig['rest'];
	for (let i = 0; i < n; i++) {
		const type = both(typeAt(longest, i), typeAt(shorter, i));
		if (longest.rest && i === n - 1)
			rest = JS.Rest(longest.rest.key, TS.ArrayType(type));
		else
			params.push(JS.Param((longest.params[i] ?? shorter.params[i]).key, type, i >= required(longest) && i >= required(shorter) ? ['optional'] : []));
	}
	if (!longest.rest && !!shorter.rest)
		rest = JS.Rest(shorter.rest!.key, TS.ArrayType(typeAt(shorter, n) ?? ANY));
	return { params, rest };
}

// A union of signatures identical up to their own type-parameter names is ONE signature (real TS's
// `getUnionSignatures`). `(readonly T[] | T[]).map` is that shape: each part minted its own fresh `U`.
export function mergeIdenticalSignatures(t: Type): Type {
	if (t.type !== 'union')
		return t;
	const [first, ...rest] = t.types;
	if (first.type !== 'function')
		return t;
	// By `typeId`, which tells two modules' same-spelled classes apart (binary's sync and async `_stream`), where a printed key does not.
	const names	= first.typeParams?.map(p => p.name) ?? [];
	const key	= typeId(first);
	const same	= (f: Type) => {
		if (f.type !== 'function' || (f.typeParams?.length ?? 0) !== names.length)
			return false;
		const renamed = names.length ? substituteType(f, new Map(f.typeParams!.map((p, i) => [p.name, TS.RefType(names[i])] as const))) as TS.FunctionType : f;
		return typeId({ ...renamed, typeParams: renamed.typeParams?.map((p, i) => ({ ...p, name: names[i] })) }) === key;
	};
	return rest.every(same) ? first : t;
}

// A callable candidate through any nesting of unions, intersections and overload objects (`Promise<T>.then` merged across lib files).
export function findFunctionType(t: Type, scope: Scope): TS.CallSig | undefined {
	const r = resolveOwn(t, scope);
	if (r.type === 'function')
		return r;
	if (r.type === 'object')
		return r.members.find(m => m.type === 'call');
	if (r.type === 'union' || r.type === 'intersection') {
		for (const m of r.types) {
			const f = findFunctionType(m, scope);
			if (f)
				return f;
		}
	}
	return undefined;
}

// ===================================================================
//  Type facts: nullishness, numeric and string kinds
// ===================================================================

export function isNullish(t: Type, scope: Scope): boolean {
	const r = resolveOwn(t, scope);
	return	r.type === 'literal'	? r.value === null
		:	r.type === 'ref'		? r.name === 'undefined' || r.name === 'null' || r.name === 'void'
		:	r.type === 'union'		? r.types.every(t => isNullish(t, scope))
		:	false;
}

// The non-nullish remainder of `t`: its nullish union members dropped (not when all are). `?.`/`??` care only about that part, and
// `lookupMember`'s union case needs every member to have the property. `strip = false` keeps `t` whole, unless `strictNullChecks` is off.
export function nonNullable(t: Type, scope: Scope, strip = true): Type {
	if (!strip && scope.strictNullChecks())
		return t;
	const r = resolveOwn(t, scope);
	if (r.type !== 'union')
		return t;
	// Each member as written unless it hides a nullish itself (`Maybe<X> | undefined`): expanding every member would no longer match `Type` itself.
	const kept = r.types.flatMap(m => isNullish(m, scope) ? [] : [nonNullable(m, scope)]);
	return kept.length === 0 || (kept.length === r.types.length && kept.every((k, i) => k === r.types[i])) ? t : combineTypes(kept);
}

// An inferred declaration or return type, as TS widens one without `strictNullChecks`: `null`/`undefined` leave a union and
// alone become `any`. Identity when strict.
export function widenNullish(t: Type, scope: Scope): Type {
	if (scope.strictNullChecks())
		return t;
	const members	= unionMembers(t, scope);
	const kept		= members.filter(m => !isNullOrUndefined(resolveOwn(m, scope)));
	return !kept.length ? ANY : kept.length === members.length ? t : combineTypes(kept);
}

export function isBigint(t: Type, scope: Scope): boolean {
	const r = resolveOwn(t, scope);
	return r.type === 'ref'		? r.name === 'bigint'
		: r.type === 'literal'	? typeof r.value === 'bigint'
		: r.type === 'range'	? r.base === 'bigint'
		: r.type === 'union'	? r.types.every(m => isBigint(m, scope))
		: false;
}

// Inferred unions over-approximate, so only no possibly numeric member counts as not.
export function isNumberLike(t: Type, scope: Scope): boolean {
	const r = resolveOwn(t, scope);
	return r.type === 'union' ? r.types.some(m => isAssignable(m, NUMERIC, scope)) : isAssignable(r, NUMERIC, scope);
}

export function isStringLike(t: Type, scope: Scope): boolean {
	const r = resolveOwn(t, scope);
	return isString(r)
		|| isLiteral(r, 'string')
		|| (r.type === 'union' && r.types.some(t => isStringLike(t, scope)));
}

// Three-valued: `undefined` is "could not resolve" (an alias not reachable here), never a confirmed `false`.
function isLiteralOnly(t: Type, scope: Scope, depth = 6): boolean | undefined {
	switch (t.type) {
		case 'literal':	return true;
		// A CLASS is definitely no literal union (`string extends RegExp` decides); `undefined` means a name not found.
		case 'ref':		return INTRINSIC_TYPES.has(t.name) || isClassRef(t, scope) ? false : undefined;
		case 'union':
			if (depth >= 0) {
				const parts = t.types.map(m => isLiteralOnly(resolveOwn(m, scope), scope, depth - 1));
				return parts.some(p => p === false) ? false : parts.every(p => p === true) ? true : undefined;
			}
			scope.hitDepthLimit('isLiteralOnly');
			return undefined;
		default:
			return false;
	}
}

// ===================================================================
//  Assignability
// ===================================================================

// An intersection of type parameters, at their constraints and normalized. Undefined when no part is abstract (nothing to gain)
// or the bound came back unchanged, which would make `isAssignable` ask the same question again.
function intersectionConstraint(t: TS.IntersectionType, scope: Scope): Type | undefined {
	if (!t.types.some(p => isAbstract(p, scope)))
		return undefined;
	const bound = resolve(scope, TS.IntersectionType(t.types.map(p => typeParamConstraint(p, scope) ?? p)));
	return bound.type === 'intersection' && bound.types.length === t.types.length && bound.types.every((b, i) => b === t.types[i]) ? undefined : bound;
}

// `t`'s union constituents, resolved, with `boolean` as `true | false`.
function constituents(t: Type, scope: Scope): Type[] {
	return unionMembers(t, scope).flatMap(m => {
		const r = resolveOwn(m, scope);
		return isRef(r, 'boolean') ? [Literal(true), Literal(false)] : [r];
	});
}
const isUnit = (t: Type) => t.type === 'literal' || isRef(t, 'undefined') || isRef(t, 'null');
// TS's discriminant property of a union: one some member types as a unit type (or a union of them).
export function isDiscriminant(union: TS.UnionType, key: string, scope: Scope): boolean {
	return union.types.some(t => { const p = lookupMember(t, key, scope); return !!p && constituents(p, scope).every(isUnit); });
}

// `src` once per combination of its discriminant properties' constituents (a property `dst`'s members discriminate on by a
// unit type), as TS relates an object to a discriminated union; undefined when nothing splits or past TS's 25 combinations.
function splitDiscriminants(src: TS.ObjectType | Extract<Type, { type: 'tuple' }>, dst: TS.UnionType, scope: Scope): Type[] | undefined {
	// A tuple's positions are its properties (`["a" | "b", 1]` against `["a", number] | ["b", number]`).
	const slots: [key: string, t: Type | undefined][] = src.type === 'tuple'
		? src.elements.map((el, i) => [String(i), el.type === 'spread' ? undefined : tupleElementType(el)])
		: src.members.map(m => [m.type === 'property' ? JS.keyName(m.key) ?? '' : '', m.type === 'property' ? m.typeAnnotation : undefined]);
	const splits: { i: number; units: Type[] }[] = [];
	slots.forEach(([key, t], i) => {
		const units = t && key && isDiscriminant(dst, key, scope) ? constituents(t, scope) : [];
		if (units.length > 1)
			splits.push({ i, units });
	});
	if (!splits.length || splits.reduce((n, s) => n * s.units.length, 1) > 25)
		return undefined;
	const variants = splits.reduce<Type[][]>((vs, { i, units }) => vs.flatMap(v => units.map(u => v.map((x, j) => j === i ? u : x))), [slots.map(([, t]) => t ?? ANY)]);
	return variants.map(v => src.type === 'tuple'
		? { ...src, elements: src.elements.map((el, j) => el.type === 'spread' ? el : v[j]) }
		: TS.ObjectType(src.members.map((m, j) => m.type === 'property' ? TS.TypeProperty(m.key, v[j], m.modifiers) : m)));
}

// A generic signature at the type arguments the target's parameters imply, the rest at their constraints (`unknown` where none); the source's
// parameters renamed first (a target's own `T` is another type). `fromReturn`: outside a call's inference, the returns infer what is left.
export function instantiateInContextOf(generic: TS.CallSig, genericParams: TS.TypeParam[], dst: TS.CallSig, scope: Scope, dstScope: Scope, fromReturn = false): TS.CallSig {
	const rename	= new Map(genericParams.map(p => [p.name, TS.RefType(`${p.name}'`)]));
	const src		= instantiateSig({ ...generic, typeParams: undefined }, rename);
	const typeParams = genericParams.map(p => ({ ...p, name: `${p.name}'`, constraint: p.constraint && substituteType(p.constraint, rename) }));
	const tparams	= new Map(typeParams.map(p => [p.name, p] as const));
	const map		= new Map<string, Type>();
	// The target's type at position `i`: a fixed parameter's, else its rest's element there.
	const dstAt = (i: number): Type | undefined => {
		const fixed = dst.params;
		if (i < fixed.length)
			return fixed[i].typeAnnotation;
		const rest = dst.rest?.typeAnnotation && resolve(dstScope, dst.rest.typeAnnotation);
		return rest?.type === 'tuple' ? tupleElementType(flatTupleElements(rest, dstScope)[i - fixed.length]) : rest && arrayLikeElement(rest);
	};
	src.params.forEach((p, i) => {
		const d = dstAt(i);
		if (p.typeAnnotation && d)
			inferTypeArgs(p.typeAnnotation, d, tparams, map, dstScope, scope);
	});
	if (fromReturn && src.returnType && dst.returnType) {
		const ret = new Map<string, Type>();
		inferTypeArgs(src.returnType, dst.returnType, tparams, ret, dstScope, scope);
		ret.forEach((t, name) => map.has(name) || map.set(name, t));
	}
	typeParams.forEach(p => map.has(p.name) || map.set(p.name, p.constraint ?? UNKNOWN));
	const sub = (t: Type | undefined) => t && substituteType(t, map);
	return { ...src, typeParams: undefined, params: src.params.map(p => ({ ...p, typeAnnotation: sub(p.typeAnnotation) })),
		rest: src.rest && { ...src.rest, typeAnnotation: sub(src.rest.typeAnnotation) }, returnType: sub(src.returnType) };
}


// Two parameter types that are both a callback -- one non-generic call signature with no type predicate -- and equally nullable:
// their signatures, which relate by TS's callback rule instead of the parameter's bivariance.
function callbackPair(s: Type, d: Type, scope: Scope, dstScope: Scope): [TS.FunctionType, TS.FunctionType] | undefined {
	const callback = (t: Type, sc: Scope) => {
		const f = resolve(sc, nonNullable(t, sc));
		return f.type === 'function' && !f.typeParams?.length && f.returnType?.type !== 'predicate' ? f : undefined;
	};
	const nullable = (t: Type, sc: Scope) => nonNullable(t, sc) !== t;
	const sf = callback(s, scope), df = callback(d, dstScope);
	return sf && df && nullable(s, scope) === nullable(d, dstScope) ? [sf, df] : undefined;
}

// `dstScope` resolves `dst`'s own names (another module's signature). `precise`: TS's subtype relation, for inference's common supertype and a guard's
// narrowing, without the widened-source leniency (`string` is not below `"def"`), and `any` below nothing but itself.
export function isAssignable(src: Type, dst: Type, scope: Scope, dstScope: Scope = scope, strict = false, depth = 10, precise = false, inProgress = new Set<string>()): boolean {
	// As TS's variadic tuple relation: the target's fixed elements before and after its rest match the source's from each end,
	// and every source position between them (a source rest included) matches the rest's element.
	function tupleRelated(src: Extract<Type, { type: 'tuple' }>, dst: Extract<Type, { type: 'tuple' }>, depth: number): boolean {
		const s = flatTupleElements(src, scope), d = flatTupleElements(dst, dstScope);
		const isRest	= (e: TS.TupleElement) => e.type === 'spread';
		const required	= (e: TS.TupleElement) => !(e.type === 'optional' || e.type === 'spread' || (e.type === 'labeled' && e.optional));
		// An optional element also holds `undefined` (TS without `exactOptionalPropertyTypes`).
		const typeAt	= (e: TS.TupleElement, sc: Scope) => e.type === 'spread' ? arrayLikeElement(resolve(sc, e.argument)) ?? ANY
			: required(e) ? tupleElementType(e)! : TS.UnionType([tupleElementType(e)!, UNDEFINED]);
		const sRest = s.findIndex(isRest), dRest = d.findIndex(isRest);
		if (dRest < 0)
			return sRest < 0 && s.length <= d.length && s.length >= d.filter(required).length && s.every((e, i) => recurse(typeAt(e, scope), typeAt(d[i], dstScope), depth - 1));
		const lead = dRest, trail = d.length - dRest - 1;
		if (sRest < 0 ? s.length < d.filter(required).length : sRest < lead || s.length - sRest - 1 < trail)
			return false;
		return s.every((e, i) => recurse(typeAt(e, scope), typeAt(i < lead ? d[i] : i >= s.length - trail ? d[d.length - (s.length - i)] : d[dRest], dstScope), depth - 1));
	}
	// Coinductive, as TS's maybe-related stack: a named pair already being related further up (up to the renaming of a generic
	// signature's parameters) is assumed to hold, so `Promise<T>` to `PromiseLike<T>` through `then` terminates.
	const recurse = (src: Type, dst: Type, depth: number): boolean => {
		const key = src.type === 'ref' && dst.type === 'ref' ? `${relationKey(src)} -> ${relationKey(dst)}` : undefined;
		if (!key)
			return related(src, dst, depth);
		if (inProgress.has(key))
			return true;
		inProgress.add(key);
		const r = related(src, dst, depth);
		inProgress.delete(key);
		return r;
	};
	// TS's callback mode: a source parameter's callback `s` accepts the target's `d` if each of `s`'s parameters is one of `d`'s
	// (one way, not bivariantly) and `d` returns what `s` does.
	const callbackRelated = (s: TS.FunctionType, d: TS.FunctionType, depth: number): boolean => {
		const dp = d.params;
		return s.params.every((p, i) => !p.typeAnnotation || !dp[i]?.typeAnnotation || recurse(p.typeAnnotation, dp[i].typeAnnotation!, depth - 1))
			&& (!s.returnType || !d.returnType || isRef(s.returnType, 'void') || recurse(d.returnType, s.returnType, depth - 1));
	};
	// A target's call or construct signature (`{ new (s: any): R }`): some signature of that kind on the source fits it, as TS's signaturesRelatedTo.
	// Coinductive like `recurse`: a pair already being related further up (`EventListener` through `Event.target`'s listeners) is assumed to hold.
	const signatureFits = (src: Type, m: TS.CallSig & { type: 'call' | 'construct' }, depth: number): boolean => {
		const asType = (s: TS.CallSig, sc: Scope) => withScope({ ...TS.FunctionType(JS.Params(s.params, s.rest), s.returnType ?? ANY, s.typeParams), type: m.type === 'call' ? 'function' as const : 'constructor' as const }, sc);
		const want = asType(m, dstScope);
		return signaturesOf(src, m.type, scope).some(s => {
			const got = asType(s, declScopeOf(s, scope)), key = `sig ${typeId(got, true)} -> ${typeId(want, true)}`;
			if (inProgress.has(key))
				return true;
			inProgress.add(key);
			const r = recurse(got, want, depth - 1);
			inProgress.delete(key);
			return r;
		});
	};
	const related = (src: Type, dst: Type, depth: number): boolean => {
		if (depth < 0) {
			scope.hitDepthLimit('isAssignable');
			return true;
		}
		src = normalizeArray(src);
		dst = normalizeArray(dst);

		// `Array<T>`/`ReadonlyArray<T>` by name (`Array` to `ReadonlyArray` is the one-directional variance), before the same-name path, which cannot see `T`.
		if (src.type === 'ref' && dst.type === 'ref' && (src.name === 'Array' || src.name === 'ReadonlyArray') && (dst.name === 'Array' || dst.name === 'ReadonlyArray')) {
			if (src.name === 'ReadonlyArray' && dst.name === 'Array')
				return false;
			const sa = src.typeArgs ?? [], da = dst.typeArgs ?? [];
			return sa.length !== da.length || sa.every((a, i) => recurse(a, da[i], depth - 1));
		}

		if (src.type === 'ref' && dst.type === 'ref' && src.name === dst.name) {
			const sa = src.typeArgs ?? [], da = dst.typeArgs ?? [];
			if (sa.length === da.length && sa.every((a, i) => recurse(a, da[i], depth - 1)))
				return true;	// same named type, pairwise-compatible arguments: skip the structural comparison
		}

		// A tuple against an array-like ref compares its elements with the ref's type argument.
		if (src.type === 'tuple') {
			const el = arrayLikeElement(dst);
			// A readonly tuple fits only a ReadonlyArray, as a readonly array does.
			if (el)
				return !(src.readonly && isRef(dst, 'Array')) && elementTypes(src, scope).every(t => recurse(t, el, depth - 1));
		}
		if (dst.type === 'tuple') {
			// An inferred array literal has lost its positions: compared loosely, either way.
			const el = arrayLikeElement(src);
			if (el)
				return dst.elements.every(e => { const t = tupleElementType(e); return !t || recurse(el, t, depth - 1) || recurse(t, el, depth - 1); });
		}

		// Every function value satisfies the lib's `Function`, whose `Function.prototype` members its `'function'` node does not carry.
		if (dst.type === 'ref' && dst.name === 'Function' && (src.type === 'function' || src.type === 'constructor'))
			return true;

		// Before `resolve` drops `src`'s ref identity: each member of a `dst` union against `src` as written, so a same-name path can fire.
		if (dst.type === 'union' && dst.types.some(t => t === src || recurse(src, t, depth - 1)))
			return true;

		// A fresh `resolve` budget, as in `lookupMember`. An intersection `src` is checked part by part, never as the combined shape (a known gap).
		// What recurses below meets the other side AS WRITTEN, keeping the identity the by-name paths need.
		const srcWritten = src, dstWritten = dst;
		src = resolve(scope, src);
		dst = resolve(dstScope, dst);
		// An alias that resolves to an array shape (`type Rules<T> = Rule<T>[]`) goes back through the Array-ref comparisons above.
		if (src.type === 'array' || dst.type === 'array')
			return recurse(src.type === 'array' ? src : srcWritten, dst.type === 'array' ? dst : dstWritten, depth - 1);

		// `unknown` is a top type only as a target: as a source it fits nothing but a top type.
		if (src === dst || isAny(dst))
			return true;
		// `keyof` a remapped mapped type over an unbound constraint stays deferred (`resolve`'s `keyof`): a key relates as its constraint's, as TS's.
		const remapped = dst.type === 'keyof' ? resolve(dstScope, dst.argument) : undefined;
		if (remapped?.type === 'mapped' && remapped.nameType)
			return recurse(src, remapped.constraint, depth - 1);
		if (isRef(src, 'unknown'))
			return false;
		// Under the subtype relation (`precise`) `any` is below nothing but itself: structurally it would fit every object target.
		if (isRef(src, 'any'))
			return !precise;
		if (isNullOrUndefined(src) && !scope.strictNullChecks())
			return true;

		if (isRef(src, 'never'))
			return true;
		// TS's homomorphic mapped source `{[P in K]: X[P]}` adding no `?`: it is an `X` wherever the target's keys are all among `K`.
		if (src.type === 'mapped' && !src.nameType && !src.modifiers?.includes('optional') && src.valueType.type === 'indexed_access' && isRef(src.valueType.index, src.keyName)
			&& recurse({ type: 'keyof', argument: dst }, src.constraint, depth - 1) && recurse(src.valueType.object, dst, depth - 1))
			return true;
		// A type parameter is itself, else related through its constraint as a source; as a target only itself fits. Unconstrained it relates as `{}`
		// without `strictNullChecks`, as in TS; with a union constraint it is also the union of `T & c` (`T extends 1 | 2` is `(1 & T) | (2 & T)`).
		const apparent = mappedApparentType(src, scope);
		if (apparent && recurse(apparent, dst, depth - 1))
			return true;
		const srcBound = typeParamConstraint(src, scope);
		if (srcBound) {
			const bound		= isRef(srcBound, 'unknown') && !scope.strictNullChecks() ? TS.ObjectType([]) : srcBound;
			const members	= dst.type === 'union' ? unionMembers(bound, scope) : [];
			if (isRef(dst, src.type === 'ref' ? src.name : '') && !dst.typeArgs || recurse(bound, dst, depth - 1))
				return true;
			// Each `c & T` meets the intersection rule, which asks `T` against `dst` again: the question in progress here, so it adds nothing.
			const key = `bound:${typeId(src)}:${typeId(dst)}`;
			if (members.length < 2 || inProgress.has(key))
				return false;
			inProgress.add(key);
			const each = members.every(c => recurse(TS.IntersectionType([c, src]), dst, depth - 1));
			inProgress.delete(key);
			return each;
		}
		// A deferred conditional, as TS relates one: the same conditional; as a source, through its branches; as a target, whatever
		// fits both branches (no `infer`, whose bindings only an instantiation supplies).
		if (src.type === 'conditional' && dst.type === 'conditional' && typeId(src.checkType) === typeId(dst.checkType) && typeId(src.extendsType) === typeId(dst.extendsType)
			&& recurse(src.trueType, dst.trueType, depth - 1) && recurse(src.falseType, dst.falseType, depth - 1))
			return true;
		if (src.type === 'conditional' && !containsKind(src.extendsType, 'infer'))
			return recurse(deferredBranches(src), dst, depth - 1);
		if (dst.type === 'conditional' && !containsKind(dst.extendsType, 'infer'))
			return src.type === 'union' ? src.types.every(m => recurse(m, dst, depth - 1))
				: src.type === 'intersection' && src.types.some(m => recurse(m, dst, depth - 1)) || recurse(src, dst.trueType, depth - 1) && recurse(src, dst.falseType, depth - 1);
		if (typeParamConstraint(dst, dstScope) && src.type !== 'union' && src.type !== 'intersection')
			return false;
		// A class ref `resolve` keeps nominal is compared by its members on either side; only an undeclared name stays unverifiable. Not while `dst` is a
		// union or intersection, which decompose below: expanding first would lose the identity the by-name `Array` and same-name paths need.
		if (src.type === 'ref' && !INTRINSIC_TYPES.has(src.name) && dst.type !== 'union' && dst.type !== 'intersection') {
			const members = resolveMembers(src, scope);
			return members.type === 'ref' || recurse(members, dst, depth - 1);
		}
		// A primitive source keeps to the primitive rules below, and a type parameter target is opaque (its constraint bounds what IT is).
		if (dst.type === 'ref' && !INTRINSIC_TYPES.has(dst.name) && dst.name !== 'Array' && dst.name !== 'ReadonlyArray'
			&& !(src.type === 'ref' && INTRINSIC_TYPES.has(src.name)) && !dstScope.type(dst.name)?.isTypeParam) {
			const members = resolveMembers(dst, dstScope);
			if (members.type !== 'ref')
				return recurse(src, members, depth - 1);
		}

		// TS's deferred relations: `keyof S` is a `keyof T` when `T` is an `S` (key sets go the other way); `X[K]` is an `X[J]` when `K` is a `J`.
		if (src.type === 'keyof' && dst.type === 'keyof')
			return recurse(dst.argument, src.argument, depth - 1);
		if (src.type === 'indexed_access' && dst.type === 'indexed_access' && typeId(src.object) === typeId(dst.object))
			return recurse(src.index, dst.index, depth - 1);
		if (OPAQUE.has(src.type) || OPAQUE.has(dst.type))
			return !strict || (!OPAQUE_GAP.has(src.type) && !OPAQUE_GAP.has(dst.type));

		if (src.type === 'union')
			return src.types.every(t => recurse(t, dstWritten, depth - 1));
		// `{}` holds every value but `null`/`undefined` (`void`, `unknown` may be either), primitives and `object` included.
		if (dst.type === 'object' && !dst.members.length && !isNullOrUndefined(src) && !isRef(src, 'void') && !isRef(src, 'unknown'))
			return true;
		if (dst.type === 'union') {
			// The identity test makes a narrowed union (members the alias's own nodes) assignable back to it.
			if (dst.types.some(t => t === src || recurse(src, t, depth - 1)))
				return true;
			// A union inside `src` behind an intersection (`(A|B) & C`): each of `src`'s parts against the whole `dst` union.
			if (src.type === 'intersection' && src.types.some(t => recurse(t, dst, depth - 1)))
				return true;
			// TS's discriminated assignability: `{ kind: A | B, ... }` fits `{ kind: A, ... } | { kind: B, ... }` when each
			// discriminant value, taken alone, fits some member.
			const split = src.type === 'object' || src.type === 'tuple' ? splitDiscriminants(src, dst, scope) : undefined;
			return !!split && split.every(s => dst.types.some(t => recurse(s, t, depth - 1)));
		}

		if (dst.type === 'intersection')
			return dst.types.every(t => recurse(src, t, depth - 1));
		if (src.type === 'intersection' && dst.type !== 'object') {
			if (src.types.some(t => recurse(t, dst, depth - 1)))
				return true;
			// TS's `getBaseConstraintOfType` for an intersection: every part at its own constraint, intersected and normalized
			// (`T & U` with `T extends 1|2` and `U extends 2|3` is `2`). No part-wise match can see a bound only the combination implies.
			const bound = intersectionConstraint(src, scope);
			return !!bound && recurse(bound, dst, depth - 1);
		}

		// A `range` on either side is a narrowed `number`/`bigint`: against a number-shaped `dst` (a range or the plain ref), precise -- does the span
		// fit, integer-ness included? Otherwise it widens to its base and is judged below as a plain `number`/`bigint` would be.
		if (src.type === 'range' || dst.type === 'range') {
			const sr = toRange(src), dr = toRange(dst);
			if (dr) {
				return !!sr && sr.base === dr.base
					&& (dr.min === undefined || (sr.min !== undefined && sr.min >= dr.min))
					&& (dr.max === undefined || (sr.max !== undefined && sr.max <= dr.max))
					&& (!dr.integer || sr.integer);
			}
			if (sr)
				src = sr.base === 'bigint' ? BIGINT : NUMBER;
		}

		// A template literal type still here didn't expand (see `expandTemplate`): as a target it's a pattern, as a source a `string`.
		if (dst.type === 'literal' && Array.isArray(dst.value)) {
			if (isLiteral(src, 'string') && !Array.isArray(src.value))
				return new RegExp(`^${templatePattern(dst.value, dstScope)}$`).test(src.value);
			return !precise && (isLiteral(src, 'string') || isRef(src, 'string'));	// widened source: lenient (inventory C1)
		}
		if (src.type === 'literal' && Array.isArray(src.value))
			return recurse(STRING, dst, depth - 1);
		if (dst.type === 'literal')
			return src.type === 'literal'
				? src.value === dst.value
				: !precise && src.type === 'ref' && dst.value !== null && src.name === typeof dst.value;	// widened source: lenient (inventory C1)
		// A literal is never an array, and a type parameter is opaque; any other name still here could not be expanded, so stays unverifiable.
		// Against a structural target it boxes as its primitive does: `"def"` satisfies `Object` exactly as `string` does.
		if (src.type === 'literal')
			return dst.type === 'ref' ? (INTRINSIC_TYPES.has(dst.name) ? dst.name === (src.value === null ? 'null' : typeof src.value)
				: dst.name !== 'Array' && dst.name !== 'ReadonlyArray' && !dstScope.type(dst.name)?.isTypeParam)
				: src.value !== null && recurse(TS.RefType(typeof src.value), dst, depth - 1);

		// `normalizeArray` and `resolve` above have expanded every array; only tuple against tuple is structural here.
		if (dst.type === 'tuple')
			return src.type === 'tuple' && tupleRelated(src, dst, depth);

		if (dst.type === 'function' || dst.type === 'constructor') {
			if (src.type !== dst.type)
				return src.type === 'object' && src.members.some(m => m.type === (dst.type === 'constructor' ? 'construct' : 'call'));
			// A generic target's own type parameters are real (opaque) types while it is related, as a function body's are -- on both
			// sides, since the source is instantiated in terms of them.
			if (dst.typeParams?.length) {
				const bind = (sc: Scope) => {
					const inner = new Scope(sc);
					dst.typeParams!.forEach(p => inner.addTypeParam(p.name, p.constraint ?? UNKNOWN));
					return inner;
				};
				return isAssignable(src, { ...dst, typeParams: undefined }, bind(scope), bind(dstScope), strict, depth, precise, inProgress);
			}
			// TS's arity rule (compareSignaturesRelated): a source needing more arguments than the target ever passes is not one.
			if (!dst.rest && minArgumentCount(src, scope) > dst.params.length)
				return false;
			// A GENERIC source is instantiated in the target's context first (TS's instantiateSignatureInContextOf): its type parameters
			// inferred from the target's parameters, the rest at their constraints -- `<T>(x: T) => number` is a `(x: number) => void`.
			const fn = src.typeParams?.length ? instantiateInContextOf(src, src.typeParams, dst, scope, dstScope, true) : src;
			// Parameters are BIVARIANT (TS's method-parameter rule), each pair relating one way; a CALLBACK pair relates one way only, the target's callback
			// to the source's (TS's strict callback rule), which makes `then(onfulfilled: (value: T) => ...)` covariant in `T`.
			const srcParams = fn.params, dstParams = dst.params;
			if (srcParams.some((p, i) => {
				const s = p.typeAnnotation, d = dstParams[i]?.typeAnnotation;
				const callbacks = s && d && callbackPair(s, d, scope, dstScope);
				return s && d && (callbacks ? !callbackRelated(...callbacks, depth - 1) : !recurse(s, d, depth - 1) && !recurse(d, s, depth - 1));
			}))
				return false;
			if (!dst.returnType || !fn.returnType)
				return true;	// missing return type (e.g. an unmodeled class method): lenient
			// Returns covariant; a `void` target absorbs anything.
			return dst.returnType.type === 'ref' && dst.returnType.name === 'void'
				|| recurse(fn.returnType, dst.returnType, depth - 1);
		}

		if (dst.type === 'object') {
			if (src.type === 'ref') {
				// A primitive auto-boxes for structural checks too (`Array.from(str)`: a `string` satisfies `Iterable<T>`).
				const boxed = scope.semantics.boxed(src.name);
				return boxed ? recurse(TS.RefType(boxed), dst, depth - 1) : !INTRINSIC_TYPES.has(src.name);	// unresolved nominal: lenient
			}
			if (src.type === 'function' || src.type === 'constructor')
				// A function's apparent type is `Function`, then `Object` (both through `lookupMember`).
				return dst.members.every(m => {
					if (m.type === 'call' || m.type === 'construct')
						return signatureFits(src, m, depth);
					if ((m.type !== 'property' && m.type !== 'method') || hasMod(m, 'optional') || typeof m.key === 'object')
						return true;
					const got = lookupMember(src, String(m.key), scope);
					return !!got && (m.type === 'method' || recurse(got, m.typeAnnotation, depth - 1));
				});
			if (src.type === 'object' || src.type === 'intersection' || src.type === 'tuple')
				return dst.members.every(m => {
					// A computed key names its member by path (`[Symbol.iterator]`), as `lookupMember` finds it.
					if (m.type === 'call' || m.type === 'construct')
						return signatureFits(src, m, depth);
					if (m.type === 'index' && src.type !== 'tuple' && (isRef(m.paramType, 'string') || isRef(m.paramType, 'number'))) {
						// As TS: the source's own index signature covering the key (a string one covers numbers too), else an object literal type's
						// implicit one (each of its properties, numeric-named only for a number index); an interface or class has none.
						const numeric	= isRef(m.paramType, 'number');
						// TS's indexSignaturesRelatedTo: a target string index of type `any` (`Record<string, any>`) takes any non-primitive source.
						if (!numeric && isRef(m.typeAnnotation, 'any'))
							return true;
						const members	= collectMembers(src, scope);
						const indexes	= indexMembers(members);
						const own		= (numeric ? indexes.find(i => isRef(i.paramType, 'number')) : undefined) ?? indexes.find(i => isRef(i.paramType, 'string'));
						if (own)
							return recurse(own.typeAnnotation, m.typeAnnotation, depth - 1);
						if (!hasImplicitIndex(srcWritten, scope))
							return false;
						return members.every(p => {
							const key = (p.type === 'property' || p.type === 'method') ? memberKey(p.key) : undefined;
							const got = key !== undefined && (!numeric || isIndexKey(key)) ? lookupMember(src, key, scope) : undefined;
							return !got || recurse(got, m.typeAnnotation, depth - 1);
						});
					}
					if (m.type !== 'property' && m.type !== 'method')
						return true;		// a symbol or template-literal index: unchecked
					const key = memberKey(m.key);
					if (key === undefined)
						return true;
					// `lookupMember` gets its own fresh budget.
					const got = lookupMember(src, key, scope);
					// A method is its function type, each overload in turn (TS's method bivariance is the function rule's).
					const want = m.type === 'property' ? m.typeAnnotation : withScope(TS.FunctionType(JS.Params(m.params, m.rest), m.returnType ?? ANY, m.typeParams), dstScope);
					// An optional property also accepts undefined. A missing required one is an error even when its type admits
					// `undefined` (TS: "Property is missing") -- absence only counts against a sealed source.
					return got ? recurse(got, hasMod(m, 'optional') ? TS.UnionType([want, UNDEFINED]) : want, depth - 1)
						// A function part is sealed here, as the function rule above holds it; member access keeps it open for expandos, which go unmodelled.
						: hasMod(m, 'optional') || !sealed(src, scope, 6, true) || (typeof m.key === 'object' && valueKeyed(src, scope));
				});
			return false;
		}

		if (dst.type === 'ref') {
			if (dst.name === 'object')
				return !(src.type === 'ref' && INTRINSIC_TYPES.has(src.name)) || src.name === 'object' || src.name === 'null';
			if (dst.name === 'void')
				return src.type === 'ref' && (src.name === 'void' || src.name === 'undefined');
			if (src.type === 'ref') {
				if (src.name === dst.name)
					return !dst.typeArgs || !src.typeArgs || src.typeArgs.length !== dst.typeArgs.length || src.typeArgs.every((a, i) => recurse(a, dst.typeArgs![i], depth - 1));
				if (src.name === 'void' && dst.name === 'undefined')
					return true;	// this checker's own bare-`return` inference produces `void`
				// A PRIMITIVE never satisfies a real CLASS (`string` is no `RegExp`, nor an `Array<T>`), except its boxed wrapper; the leniency below is for a name
				// not found at all.
				const boxedSrc = scope.semantics.boxed(src.name);
				if (boxedSrc && (isClassRef(dst, dstScope) || dst.name === 'Array' || dst.name === 'ReadonlyArray'))
					return boxedSrc === dst.name;
				// Under strict null checks (else answered above) `undefined`/`null` are assignable to no class: `undefined extends T[]` is false.
				if (isNullOrUndefined(src))
					return false;
				return !(INTRINSIC_TYPES.has(src.name) && INTRINSIC_TYPES.has(dst.name));	// distinct primitives: no; unresolved names: lenient
			}
			// `Array`/`ReadonlyArray` are known shapes: a plain object or function (every array-like source was handled above) never satisfies one.
			if (dst.name === 'Array' || dst.name === 'ReadonlyArray')
				return false;
			return !INTRINSIC_TYPES.has(dst.name);	// structural value into unresolved named type: lenient
		}

		if (src.type === 'ref')
			return !INTRINSIC_TYPES.has(src.name);

		return src.type === dst.type;
	};
	return recurse(src, dst, depth);
}

// ===================================================================
//  Inference
// ===================================================================

// TS's hasPrimitiveConstraint: a type parameter bounded by a primitive (`T extends string`, a literal union) infers the
// literal itself, unwidened -- `f<T extends string>(x: T): T` called with 'a' is 'a'.
function primitiveConstraint(c: Type | undefined, scope: Scope): boolean {
	return !!c && unionMembers(c, scope).some(m => PRIMITIVE_DOMAINS.has(domainOf(resolveOwn(m, scope), scope) ?? ''));
}

// An inferred type argument is a TS type: a machine type forces its slot only where written, so a candidate's is `number`. Identity-preserving
// where nothing changes: inference recognises its literal candidates by identity.
function unforced(t: Type, scope: Scope): Type {
	if (t.type === 'union') {
		const ms = t.types.map(m => unforced(m, scope));
		return ms.some((m, i) => m !== t.types[i]) ? combineTypes(ms) : t;
	}
	if (t.type === 'array') {
		const e = unforced(t.element, scope);
		return e !== t.element ? TS.ArrayType(e, t.readonly) : t;
	}
	return machineOf(t, scope) ? NUMBER : t;
}

// TS's choice among candidates: covariant ones if any (object/array literals pooled into one union, then literals of one primitive UNIONED, else the
// leftmost one every later one is a supertype of, `getSupertypeOrUnion`); else the contravariant ones' common subtype.
export function chooseInference(co: Type[], contra: Type[], scope: Scope, fromLiteral: (t: Type) => boolean = () => false): Type | undefined {
	const literals = co.filter(fromLiteral);
	if (literals.length > 1)
		co = [...co.filter(t => !fromLiteral(t)), combineTypes(literals)];
	if (co.length) {
		const members	= co.flatMap(t => unionMembers(t, scope).map(m => resolveOwn(m, scope)));
		const base		= (m: Type) => m.type === 'literal' ? literalType(m) : undefined;
		if (members.every(m => base(m) !== undefined && base(m) === base(members[0])))
			return combineTypes(co);
		// TS's getCommonSupertype: with strictNullChecks, `null`/`undefined` stand aside while the supertype is chosen, then join it.
		const nullish	= scope.strictNullChecks() ? members.filter(m => isNullish(m, scope)) : [];
		const primary	= nullish.length ? co.map(t => combineTypes(unionMembers(t, scope).filter(m => !isNullish(m, scope)))).filter(t => !isRef(t, 'never')) : co;
		const supertype	= primary.length ? primary.reduce((s, t) => s !== t && isAssignable(s, t, scope, scope, false, 10, true) ? t : s) : NEVER;
		return nullish.length ? combineTypes([supertype, ...nullish]) : supertype;
	}
	return contra.length ? contra.reduce((s, t) => s !== t && isAssignable(t, s, scope, scope, false, 10, true) ? t : s) : undefined;
}

// The parameter types of every signature `t` offers a callback (a function, a call member, each member of a union).
function callbackParamTypes(t: Type, scope: Scope, depth = 4): Type[] {
	const r = resolveOwn(t, scope);
	const sigParams = (sig: TS.CallSig) => [...sig.params.flatMap(p => p.typeAnnotation ? [p.typeAnnotation] : []), ...sig.rest?.typeAnnotation ? [sig.rest.typeAnnotation] : []];
	return r.type === 'function' || r.type === 'constructor' ? sigParams(r)
		: r.type === 'object' ? r.members.flatMap(m => m.type === 'call' ? sigParams(m) : [])
		: r.type === 'union' && depth > 0 ? r.types.flatMap(m => callbackParamTypes(m, scope, depth - 1))
		: [];
}

// TS's inference context for one generic call: each type parameter's candidates, covariant and contravariant apart; what the destination implies
// (lowest priority); and the parameters FIXED (read to give a callback its context), whose later candidates are ignored.
export class Inference {
	readonly names:				ReadonlyMap<string, TS.TypeParam>;
	private readonly co			= new Map<string, Type[]>();
	private readonly contra		= new Map<string, Type[]>();
	private readonly reversed	= new Map<string, Type[]>();	// TS's HomomorphicMappedType priority: used only where nothing else speaks
	private readonly fixed		= new Map<string, Type>();
	private readonly fromReturn	= new Map<string, Type>();
	private readonly defaulted	= new Set<string>();
	private readonly literal	= new Set<Type>();		// candidates inferred from an object/array literal argument
	private readonly stored		= new Set<Type>();		// candidates an existing array's element type gives: its storage, kept as is
	private feedingLiteral		= false;

	constructor(typeParams: readonly TS.TypeParam[], readonly scope: Scope, readonly declScope: Scope) {
		this.names = new Map(typeParams.map(p => [p.name, p]));
	}
	// `inferTypeArgs` skips a name this reports: only a fixed one takes no more candidates.
	has(name: string): boolean	{ return this.fixed.has(name); }
	// Every candidate comes from the CALLER's side but is substituted into the callee's types and resolved there, so it carries the caller's scope.
	add(name: string, t: Type, contra: boolean, reversed = false, stored = false) {
		// A fresh copy: the set is by identity, and the same type object may also arrive as an ordinary candidate.
		if (stored && !this.feedingLiteral)
			this.stored.add(t = { ...t });
		stampScope(t, this.scope);
		if (reversed) {
			this.reversed.set(name, [...this.reversed.get(name) ?? [], t]);
			return;
		}
		// Only a candidate that is itself an object/array literal's type pools (TS's isObjectOrArrayLiteralType), not a primitive inside one.
		if (this.feedingLiteral && (t.type === 'object' || t.type === 'array' || t.type === 'tuple'))
			this.literal.add(t);
		const pool = contra ? this.contra : this.co;
		pool.set(name, [...pool.get(name) ?? [], t]);
	}
	// A callback's return is matched on a fresh depth budget: queued on `deferred` when the caller orders them, else replayed now, one level deep,
	// since each level multiplies through overload sets (`Promise.then`).
	infer(paramT: Type, argT: Type, deferred?: Deferred[], contra = false, replays = 1) {
		const own: Deferred[] = [];
		inferTypeArgs(paramT, argT, this.names, this, this.scope, this.declScope, deferred ?? (replays > 0 ? own : undefined), contra);
		for (const d of own)
			this.infer(d.paramT, d.argT, undefined, d.contra, replays - 1);
	}
	// An argument written as an object/array literal: what it gives is a literal candidate, pooled into one union when chosen.
	inferFromLiteral(paramT: Type, argT: Type) {
		this.feedingLiteral = true;
		this.infer(paramT, argT);
		this.feedingLiteral = false;
	}
	// What the call's result must be (`expected` against the signature's return type): used only where nothing else speaks.
	inferReturn(returnType: Type, expected: Type) {
		const m = new Map<string, Type>();
		inferTypeArgs(returnType, expected, this.names, m, this.scope, this.declScope);
		m.forEach((t, name) => this.fromReturn.has(name) || this.fromReturn.set(name, stampScope(t, this.scope)));
	}
	fromCandidates(name: string): Type | undefined {
		const fixed = this.fixed.get(name);
		if (fixed)
			return fixed;
		const reversed = this.reversed.get(name);
		if (reversed && !this.co.has(name) && !this.contra.has(name))
			return chooseInference(reversed, [], this.scope);
		const co		= (this.co.get(name) ?? []).map(t => this.stored.has(t) ? t : unforced(t, this.scope)), contra = this.contra.get(name) ?? [];
		const covariant	= co.length ? chooseInference(co, [], this.scope, t => this.literal.has(t)) : undefined;
		if (!covariant || !contra.length)
			return covariant ?? chooseInference([], contra, this.scope);
		// TS's preferCovariantType: a covariant inference that is no conflicting pick, fits some contravariant one, and holds every candidate of a
		// parameter constrained by this one (`every<T, U extends T>(arr, isC)`: `T` is `isC`'s `A`).
		const fits		= (t: Type, u: Type) => isAssignable(t, u, this.scope);
		const bounded	= [...this.names.values()].filter(p => p.constraint?.type === 'ref' && p.constraint.name === name && !p.constraint.typeArgs);
		const prefer	= !isRef(covariant, 'never') && !isAny(covariant) && co.every(t => fits(t, covariant)) && contra.some(t => fits(covariant, t))
			&& bounded.every(p => (this.co.get(p.name) ?? []).every(t => fits(t, covariant)));
		return prefer ? covariant : chooseInference([], contra, this.scope);
	}
	inferred(name: string): Type | undefined	{ return this.fromCandidates(name) ?? this.fromReturn.get(name); }
	// TS's getTypeFromInference: every candidate at once, as a reverse mapping reads a property's.
	union(name: string): Type | undefined {
		const co = this.co.get(name), contra = this.contra.get(name);
		return co ? combineTypes(co) : contra && intersectTypes(contra);
	}
	current(): Map<string, Type> {
		const map = new Map<string, Type>();
		for (const name of this.names.keys()) {
			const t = this.inferred(name);
			if (t)
				map.set(name, t);
		}
		return map;
	}
	// Fixed with nothing inferred: the parameter's default, else its constraint, else `unknown` (TS's getInferredType).
	wasDefaulted(name: string): boolean	{ return this.defaulted.has(name); }
	// `declared` as a callback's context: every parameter its own parameter types mention is FIXED at its current inference.
	contextFor(declared: Type): Type {
		const params = callbackParamTypes(declared, this.declScope);
		for (const [name, tp] of this.names) {
			if (this.fixed.has(name) || !params.some(p => mentionsTypeParam(p, name)))
				continue;
			const t = this.inferred(name);
			if (!t)
				this.defaulted.add(name);
			this.fixed.set(name, t ?? tp.default ?? tp.constraint ?? UNKNOWN);
		}
		const map = this.current();
		return map.size ? substituteType(declared, map) : declared;
	}
}

// A callback-shaped param's RETURN inference (from the argument's own inferred return, an anonymous shape) queued for `instantiate` to replay
// after the call's contextual `expected` has had first say; every other position infers at once, first binding wins.
export interface Deferred { paramT: Type; argT: Type; contra?: boolean }
// Infers a generic call's type args by matching each param's declared type against the argument's. `declScope` resolves `paramT`'s names, `scope` `argT`'s.
export function inferTypeArgs(paramT: Type, argT: Type, tparams: ReadonlyMap<string, TS.TypeParam>, out: Map<string, Type> | Inference, scope: Scope, declScope: Scope = scope, deferred?: Deferred[], contraStart = false, startDepth = 6): void {
	let pooled: Map<string, Type[]> | undefined;
	// Flipped at each callback parameter position: what a type parameter learns there is a contravariant candidate.
	let contra = contraStart;
	// Bindings made so far: whether an alternative drew an inference from the argument (see the union case).
	let inferences = 0;
	// Inside an argument array's element type: what binds there is that array's storage (`Inference.stored`).
	let inElement = 0;
	return recurse(paramT, argT, startDepth);

	function found(name: string, t: Type, reversed = false) {
		inferences++;
		if (pooled)
			pooled.set(name, [...pooled.get(name) ?? [], t]);
		else if (out instanceof Inference)
			out.add(name, t, contra, reversed, inElement > 0);
		else if (!reversed || !out.has(name))
			out.set(name, t);
	}
	function flipped(inner: () => void) {
		contra = !contra;
		inner();
		contra = !contra;
	}

	// TS's inferToMappedType: `{[K in keyof T]: X}` infers T by reversing X over the argument's properties (createReverseMappedType); `{[K in C]: X}`
	// infers C from the argument's keys and X from its property types.
	function inferToMapped(m: TS.MappedType, a: Type, depth: number, c = m.constraint): void {
		if (c.type === 'intersection')
			return c.types.forEach(t => inferToMapped(m, a, depth, t));
		const bare		= (t: Type): t is TS.RefType => t.type === 'ref' && !t.typeArgs && tparams.has(t.name);
		const all		= a.type === 'object' || a.type === 'ref' ? collectMembers(a, scope) : [];
		const props		= all.filter((p): p is Extract<TS.TypeMember, { type: 'property' | 'method' }> => p.type === 'property' || p.type === 'method');
		const indexes	= all.filter((p): p is IndexMember => p.type === 'index');
		const propType	= (p: typeof props[number]) => p.type === 'property' ? p.typeAnnotation : TS.FunctionType(methodSignature(p));
		if (c.type === 'keyof' && bare(c.argument)) {
			const target	= c.argument.name;
			const slot		= `${target}[${m.keyName}]`;
			const template	= walker(undefined, undefined, rewriteOnce((x: Type, process: <T extends Type>(x: T) => T) =>
				x.type === 'indexed_access' && isRef(x.object, target) && isRef(x.index, m.keyName) ? TS.RefType(slot) : process(x)
			)).type(m.valueType) ?? m.valueType;
			const reverse	= (t: Type) => {
				const out = new Inference([TS.TypeParam(slot)], scope, declScope);
				inferTypeArgs(template, t, out.names, out, scope, declScope, undefined, false, depth - 1);
				return out.union(slot) ?? UNKNOWN;
			};
			const elem		= arrayLikeElement(a);
			if (elem)
				found(target, TS.ArrayType(reverse(elem), a.type === 'array' && a.readonly), true);
			else if (all.length || a.type === 'object')
				found(target, TS.ObjectType([...props.map(p => TS.TypeProperty(p.key, reverse(propType(p)), p.modifiers)), ...indexes.map(i => TS.TypeIndex(i.paramName, i.paramType, reverse(i.typeAnnotation), i.modifiers))]), true);
		} else if (bare(c) && props.length) {
			found(c.name, resolve(scope, { type: 'keyof', argument: a }), true);
			recurse(m.valueType, combineTypes(props.map(propType)), depth - 1);
		}
	}

	function recurse(paramT: Type, argT: Type, depth: number) {
		if (depth < 0)
			return;
		if (paramT.type === 'ref' && !paramT.typeArgs && tparams.has(paramT.name)) {
			// A callee's own type parameter that is none at the call site leaked in through context (`[]` typed against the unsolved `U[]`): as in TS,
			// a parameter never infers from itself.
			const leaked	= (m: Type) => m.type === 'ref' && !m.typeArgs && tparams.has(m.name) && !scope.type(m.name)?.isTypeParam;
			const members	= argT.type === 'union' ? argT.types : [argT];
			const own		= members.filter(m => !leaked(m));
			if (!own.length)
				return;
			const src		= own.length === members.length ? argT : combineTypes(own);
			if (!out.has(paramT.name)) {
				const tp = tparams.get(paramT.name)!;
				// A literal argument widens, unless the constraint is itself a union of literals (`K extends 'string' | 'number'`), which the widened form falls outside.
				found(paramT.name, tp.const || tp.constraint?.type === 'keyof' || primitiveConstraint(tp.constraint, scope) ? src : widenLiterals(src));
			}
			return;
		}
		// As TS's inferFromTypes: an `any` argument is an `any` candidate for every type parameter its target mentions (`new Map(anyValue)`).
		if (isRef(argT, 'any')) {
			tparams.forEach((_, name) => mentionsTypeParam(paramT, name) && found(name, ANY));
			return;
		}
		// TS's getApparentType: a type-parameter argument infers through its constraint (`A extends readonly T[]` gives `readonly E[]`
		// its `E = T`), but a union, intersection or conditional target pairs its parts with the parameter itself first.
		const bound = paramT.type !== 'union' && paramT.type !== 'intersection' && paramT.type !== 'conditional' ? typeParamConstraint(argT, scope) ?? mappedApparentType(argT, scope) : undefined;
		if (bound)
			return recurse(paramT, bound, depth - 1);
		const a = resolveOwn(argT, scope);
		// A string literal against a template literal type binds each placeholder to its stretch of the text (`${infer Head}.${infer Rest}`).
		if (paramT.type === 'literal' && Array.isArray(paramT.value)) {
			const parts: readonly JS.TemplatePart<Type>[] = paramT.value;
			const slices = isLiteral(a, 'string') && !Array.isArray(a.value) ? templateSlices(parts, a.value) : undefined;
			slices?.forEach((text, i) => recurse(parts[i].exp!, Literal(text), depth - 1));
			return;
		}
		if (paramT.type === 'array') {
			if (a.type === 'array') {
				inElement++;
				recurse(paramT.element, a.element, depth - 1);
				inElement--;
			} else if (a.type === 'tuple') {
				// Every element is a candidate, unioned (`readonly T[]` from `['a', 'b'] as const` is `'a' | 'b'`). More precise than tsc, which keeps the common
				// supertype: codegen lays structs out by these keys.
				const outer = pooled;
				pooled = new Map();
				elementTypes(a, scope).forEach(t => recurse(paramT.element, t, depth - 1));
				const got = pooled;
				pooled = outer;
				got.forEach((ts, name) => found(name, combineTypes(ts)));
			// A union argument (`number[] | number[]` from `x ?? y`) distributes; the first member to match wins (`out`'s guard).
			} else if (a.type === 'union') {
				a.types.forEach(m => recurse(paramT, m, depth - 1));
			} else {
				// An array-like spelled by name (`ReadonlyArray<A>`), which resolves to its interface's members.
				const el = arrayLikeElement(argT);
				if (el) {
					inElement++;
					recurse(paramT.element, el, depth - 1);
					inElement--;
				}
			}
		} else if (paramT.type === 'ref' && paramT.typeArgs) {
			// A generic alias unfolded one level (`paramT.name` is declared in `declScope`, not `scope`; `sync.TypeT` through its namespace).
			const entry		= (([ns, n]) => ns?.type(n))(declScopeOf(paramT, declScope).qualified(paramT.name));
			const unfold	= () => instantiateEntry(entry!, paramT.typeArgs);
			// The same declaration however spelled (`Bus<T>` inside its namespace, `Bacon.Bus<number>` outside it), or reached (an import or re-export
			// holds its own entry for it, over the one declared body).
			const sameDecl	= (t: Type): t is TS.RefType => t.type === 'ref' && (t.name === paramT.name
				|| !!entry && (([ns, n]) => ns?.type(n)?.type === entry.type)(declScopeOf(t, scope).qualified(t.name)));
			const sameName	= sameDecl(argT);
			// Array-like to array-like is element to element, covariantly, as TS infers it: through the methods, callback parameters would add CONTRAVARIANT
			// candidates (`ReadonlyArray<T>` from a `(string | number)[]`).
			const el = (paramT.name === 'Array' || paramT.name === 'ReadonlyArray') && paramT.typeArgs.length === 1
				? arrayLikeElement(a) ?? (a.type === 'tuple' ? combineTypes(elementTypes(a, scope)) : undefined) : undefined;
			// Iterating is the language's protocol: what the argument iterates as is what its iteration interface's arguments are (`Iterable<T>` from a string).
			const iteration	= !el && !sameName ? scope.semantics.iterationOf(paramT, argT, scope) : undefined;
			if (el) {
				const stored = a.type !== 'tuple' ? 1 : 0;
				inElement += stored;
				recurse(paramT.typeArgs[0], el, depth - 1);
				inElement -= stored;
			} else if (iteration) {
				recurse(iteration.target.yield, iteration.source.yield, depth - 1);
				recurse(iteration.target.return, iteration.source.return, depth - 1);
				flipped(() => recurse(iteration.target.next, iteration.source.next, depth - 1));
			} else if (paramT.name === 'PromiseLike' && paramT.typeArgs.length === 1 && (argT.type === 'union' ? argT.types : [argT]).some(m => asPromiseRef(m, scope))) {
				// `.then`'s callback may return a union only some of whose members are Promises: `awaitType` unwraps those. On `argT`, not the resolved `a`,
				// which would have lost the `Promise<X>` ref identity.
				recurse(paramT.typeArgs[0], awaitType(argT, scope), depth - 1);
			} else if (!sameName && entry?.typeParams?.length && entry.type.type === 'union') {
				// An alias is transparent, as in TS: `MaybePromise<D>` IS `D | Promise<D>`, so a union argument meets a union target and a
				// bare `D` takes what the other members don't account for, whole -- not one candidate per argument member.
				recurse(unfold(), argT, depth - 1);
			} else if (a.type === 'union' && !sameName) {
				// `Rule<T>` against `Rule2<CallSig> = Rule<CallSig> | Rules<CallSig> | ...`: each member is a candidate, as in TS.
				a.types.forEach(m => recurse(paramT, m, depth - 1));
			} else {
				// The argument's own named type, unresolved: `resolve()` substitutes a generic ref into its body, losing the `Polynomial<number>` identity to match.
				const named = sameDecl(argT) && argT.typeArgs ? argT : sameDecl(a) && a.typeArgs ? a : undefined;
				if (named) {
					paramT.typeArgs.forEach((p, i) => {
						const t = named.typeArgs![i];
						if (t)
							recurse(p, t, depth - 1);
					});
				} else {
					// A generic alias wrapping `T` (`Testable<T> = T extends primitive ? T : T & Equal<T>`): unfolded one level, so the case containing `T` matches.
					if (entry?.typeParams?.length)
						recurse(unfold(), argT, depth - 1);
				}
			}
		} else if (paramT.type === 'tuple') {
			// A tuple parameter infers per position (`Map`/`Set`'s `[K, V][]`); a trailing spread (`[H, ...R]`) takes the remaining elements as a tuple.
			const last = paramT.elements.at(-1), lead = last?.type === 'spread' ? paramT.elements.slice(0, -1) : paramT.elements;
			if (a.type === 'tuple') {
				lead.forEach((el, i) => {
					const p = tupleElementType(el), q = tupleElementType(a.elements[i]);
					if (p && q)
						recurse(p, q, depth - 1);
				});
				if (last?.type === 'spread')
					recurse(last.argument, TS.Tuple(a.elements.slice(lead.length)), depth - 1);
			} else if (a.type === 'union') {
				a.types.forEach(m => recurse(paramT, m, depth - 1));
			}

		} else if (paramT.type === 'intersection') {
			// Same reasoning as `union` below: `T` may be embedded in just one part -- trying every part is safe, only the matching one infers anything.
			for (const p of paramT.types)
				recurse(p, argT, depth - 1);

		} else if (paramT.type === 'conditional') {
			// A deferred conditional argument (or a part of a union or intersection) pairs with it part by part, as TS's inferToConditionalType.
			const parts = (x: Type): Type[] => x.type === 'union' || x.type === 'intersection' ? x.types.flatMap(p => parts(resolveOwn(p, scope))) : [x];
			const conds = parts(a).filter(p => p.type === 'conditional');
			for (const c of conds) {
				recurse(paramT.checkType, c.checkType, depth - 1);
				recurse(paramT.extendsType, c.extendsType, depth - 1);
				recurse(paramT.trueType, c.trueType, depth - 1);
				recurse(paramT.falseType, c.falseType, depth - 1);
			}
			// Else which branch `T` is in depends on `checkType extends extendsType`, not knowable here since `T` may itself be `checkType` -- try both.
			if (!conds.length) {
				recurse(paramT.trueType, argT, depth - 1);
				recurse(paramT.falseType, argT, depth - 1);
			}

		} else if (paramT.type === 'function' || paramT.type === 'constructor') {
			// The argument's signatures of that kind, its last as TS infers from (a function type, an intersection's callable part as
			// `Object.assign(fn, {...})` builds, or an object's call member: `arr.map(Number)`); construct ones as `new` resolves them (mixins).
			const callable = (paramT.type === 'function' ? signaturesOf(a, 'call', scope) : constructSignatures(a, scope)).at(-1);
			if (callable) {
				// A generic argument is instantiated in the context of a parameter that says what it takes (TS's higher-order inference); against one still
				// naming this call's parameters, at its constraints.
				const informative = !paramT.typeParams?.length && !paramT.params.some(p => p.typeAnnotation && mentionsNames(p.typeAnnotation, tparams));
				const fn = callable.typeParams?.length && informative ? instantiateInContextOf(callable, callable.typeParams, paramT, scope, declScope) : baseSignature(callable);
				// The argument's parameters as positions, as a call writes them: a rest of a tuple type is its elements.
				const restT		= fn.rest?.typeAnnotation && resolveOwn(fn.rest.typeAnnotation, scope);
				const positions	= [...fn.params.map((q): TS.TupleElement => hasMod(q, 'optional') ? { type: 'optional', element: q.typeAnnotation ?? ANY } : q.typeAnnotation ?? ANY),
					...restT?.type === 'tuple' ? restT.elements : fn.rest?.typeAnnotation ? [{ type: 'spread' as const, argument: fn.rest.typeAnnotation }] : []];
				flipped(() => {
					paramT.params.forEach((p, i) => {
						const q = tupleElementType(positions[i]);
						if (p.typeAnnotation && q)
							recurse(p.typeAnnotation, q, depth - 1);
					});
					// A rest parameter takes the remaining positions, as a tuple (`Parameters<T>`).
					if (paramT.rest?.typeAnnotation)
						recurse(paramT.rest.typeAnnotation, TS.Tuple(positions.slice(paramT.params.length)), depth - 1);
				});
				// `deferred`'s one case: `fn.returnType` is the argument's own inferred return, an anonymous shape. Queued, so the call's contextual
				// `expected` binds the parameter first when it can; `out`'s first-wins guard makes the replay a no-op then.
				if (paramT.returnType && fn.returnType) {
					if (deferred)
						deferred.push({ paramT: paramT.returnType, argT: fn.returnType, contra });
					else
						recurse(paramT.returnType, fn.returnType, depth - 1);
				}
			} else if (a.type === 'union') {
				// As TS's inferFromTypes, a union infers from each member: `(() => R<any>) | string` gives the callable one's.
				a.types.forEach(m => recurse(paramT, m, depth - 1));
			}
		} else if (paramT.type === 'object') {
			const fromSignature = (target: TS.CallSig, source: TS.CallSig) => {
				flipped(() => target.params.forEach((p, i) => {
					const q = source.params[i];
					if (p.typeAnnotation && q?.typeAnnotation)
						recurse(p.typeAnnotation, q.typeAnnotation, depth - 1);
				}));
				if (target.returnType) {
					if (deferred)
						deferred.push({ paramT: target.returnType, argT: source.returnType ?? ANY, contra });
					else
						recurse(target.returnType, source.returnType ?? ANY, depth - 1);
				}
			};
			for (const m of paramT.members) {
				// An index signature binds through the argument's OWN index signature of that key kind. A NUMBER one also takes an array's or tuple's elements;
				// a primitive argument uses its boxed interface. As TS's `isObjectTypeWithInferableIndex`, only a type WRITTEN as an object (a literal's, a type
				// literal) infers it from its properties (a class instance would match `Object.values`' generic overload); an optional one's without `undefined`.
				if (m.type === 'index') {
					const sameKey	= (x: Type) => typeId(resolveOwn(x, scope)) === typeId(resolveOwn(m.paramType, scope));
					const base		= resolveOwn(widenLiterals(a), scope);
					const boxed		= base.type === 'ref' ? scope.semantics.boxed(base.name) : undefined;
					const idx		= collectMembers(boxed ? TS.RefType(boxed) : base, scope).find((p): p is IndexMember => p.type === 'index' && sameKey(p.paramType));
					const elements	= !idx && sameKey(NUMBER) ? arrayLikeElement(a) ?? (a.type === 'tuple' ? combineTypes(elementTypes(a, scope)) : undefined) : undefined;
					const props		= !idx && !elements && argT.type === 'object' ? argT.members.filter((p): p is Extract<TS.TypeMember, { type: 'property' }> =>
						p.type === 'property' && (!sameKey(NUMBER) || (k => k !== undefined && String(+k) === k)(memberKey(p.key)))) : [];
					const from		= idx?.typeAnnotation ?? elements ?? (props.length ? combineTypes(props.map(p => p.typeAnnotation)) : undefined);
					if (from)
						recurse(m.typeAnnotation, from, depth - 1);
					continue;
				}
				// A call or construct signature member: as TS's inferFromSignatures, the target's and the argument's signatures of that kind pair up from the last.
				if (m.type === 'call' || m.type === 'construct') {
					const targets = paramT.members.filter(x => x.type === m.type), sources = signaturesOf(a, m.type, scope);
					const own = sources[sources.length - targets.length + targets.indexOf(m)];
					if (own)
						fromSignature(m, own);
					continue;
				}
				const key = (m.type === 'property' || m.type === 'method') ? memberKey(m.key) : undefined;
				if (key === undefined)
					continue;
				if (m.type === 'property') {
					const t = lookupMember(a, key, scope);
					if (t)
						recurse(m.typeAnnotation, t, depth - 1);
				} else if (m.type === 'method') {
					// Same shape as `function`/`constructor` above -- `adapter0<T,D>`-style interfaces often carry `T`/`D` only in a method's own signature.
					// An overloaded one (a lib class's method merged with its interface's) pairs from its last signature.
					const member	= lookupMember(a, key, scope);
					const own		= member && signaturesOf(member, 'call', scope).at(-1);
					if (own)
						fromSignature(m, baseSignature(own));
				}
			}
		} else if (paramT.type === 'mapped' && !paramT.nameType) {
			inferToMapped(paramT, a, depth);
		} else if (paramT.type === 'predicate') {
			// Only an argument that is itself a predicate (`.filter`'s `(v) => v is S`) gives an asserted type; a plain `boolean` callback leaves `S` uninferred.
			if (a.type === 'predicate' && paramT.assertedType && a.assertedType)
				recurse(paramT.assertedType, a.assertedType, depth - 1);

		} else if (paramT.type === 'union') {
			// Non-bare alternatives first (`TypeT<K>` drills into K's position); a bare `T` only fills in what is still unbound.
			const isBare	= (t: Type) => t.type === 'ref' && !t.typeArgs && tparams.has(t.name);
			const concrete	= paramT.types.filter(t => !isBare(t));
			const bare		= paramT.types.filter(isBare);
			// TS's inferToMultipleTypes: each argument member infers to the concrete alternatives, and one that drew an inference there is not the bare one's
			// too (`Promise<void>` against `TResult1 | PromiseLike<TResult1>` is `TResult1 = void`).
			const members	= a.type === 'union' ? unionMembers(a, scope) : [argT];
			const drew		= members.map(m => {
				const before = inferences;
				for (const t of concrete)
					recurse(t, m, depth - 1);
				return inferences !== before;
			});
			if (bare.length) {
				// As TS's `inferFromMatchingTypes`, a bare alternative stands for what the concrete ones do not already account for,
				// identically or by a literal's base: `T | Primitive` against `NC | 13 | '12'` infers `T = NC`.
				const keys		= new Set(concrete.flatMap(c => unionMembers(c, scope)).map(c => typeKey(resolveOwn(c, scope))));
				const matched	= (m: Type) => keys.has(typeKey(resolveOwn(m, scope))) || keys.has(typeKey(resolveOwn(widenLiterals(m, false, true, true), scope)));
				const rest		= members.filter((m, i) => !drew[i] && !matched(m));
				const narrowed	= rest.length === members.length ? argT : rest.length === 1 ? rest[0] : TS.UnionType(rest);
				if (rest.length)
					for (const t of bare)
						recurse(t, narrowed, depth - 1);
			}
		}
	}
}

// ===================================================================
//  Promises and async functions
// ===================================================================

// Peels ref aliases one substitution at a time for a literal `Promise<X>` ref: `resolve` would expand it and lose the identity.
export function asPromiseRef(t: Type, scope: Scope, depth = 6): TS.RefType | undefined {
	if (depth < 0) {
		scope.hitDepthLimit('asPromiseRef');
		return undefined;
	}
	if (t.type !== 'ref')
		return undefined;
	if (t.name === 'Promise')
		return t.typeArgs?.length ? t : undefined;
	const body = expandRefOnce(scope, t);
	return body !== t ? asPromiseRef(body, scope, depth - 1) : undefined;
}

// `Awaited<T>` distributes over a union (`string | Promise<string>`), each member awaited on its own.
export function awaitType(t: Type, scope: Scope): Type {
	const r = resolveOwn(t, scope);
	if (r.type === 'union')
		return combineTypes(r.types.map(x => awaitType(x, scope)));
	const p = asPromiseRef(t, scope);
	if (p)
		return p.typeArgs![0];
	// `Promise<T>`'s interface is split across lib files (`.then`/`.catch` in es5, `.finally` in es2018), so a Promise value resolves to an
	// intersection of them: `T` is read off `.then`'s `onfulfilled` parameter, present in every split.
	if (r.type === 'object' || r.type === 'intersection') {
		const onfulfilled = findFunctionType(lookupMember(r, 'then', scope) ?? ANY, scope)?.params[0]?.typeAnnotation;
		const value = onfulfilled && findFunctionType(onfulfilled, scope)?.params[0]?.typeAnnotation;
		if (value)
			return value;
	}
	return r;
}

export function wrapReturnIfAsync(t: Type, scope: Scope, async: boolean|undefined): Type {
	return !async || asPromiseRef(t, scope) ? t : TS.RefType('Promise', [t]);
}

export function unwrapIfAsync(t: Type, scope: Scope, async: boolean|undefined): Type {
	return async ? awaitType(t, scope) : t;
}

// TS's contextual type for what an `await` takes, or an async function returns: the value, or a promise of it.
export function awaitContext(t: Type): Type {
	return TS.UnionType([t, TS.RefType('PromiseLike', [t])]);
}

export function wrapType(t: Type, names: Set<string>, name: string) {
	return t.type === 'ref' && names.has(t.name) ? t : TS.RefType(name, [t]);
}

// ===================================================================
//  Scopes, and the language semantics a root scope carries
// ===================================================================

// `isTypeParam`: registered by `Scope.addTypeParam`, its `type` only the constraint, an upper bound: `isAbstract` treats the entry as still abstract
// (a conditional over it stays deferred), while `keyof` and member access still resolve something useful.
export interface TypeEntry	{ typeParams?: TS.TypeParam[]; type: Type; defaultSubstitution?: Type; isTypeParam?: boolean }

// What a source language's runtime adds to this shared type model: the members its values have beyond what their lib
// declares. Carried by a root `Scope`, so two languages can be checked side by side.
export interface Semantics {
	// The interface a primitive's members come from when it is used as an object (`string` -> `String`).
	boxed(primitive: string): string | undefined;
	// A member every object has without declaring it; `callable`: every function, whose own come first.
	apparentMember(prop: string, callable: boolean, scope: Scope): Type | undefined;
	// A member of `t` (already resolved) the language types more precisely than its lib declares; undefined defers to the lib.
	refinedMember(t: Type, prop: string, scope: Scope, depth: number): Type | undefined;
	// `target` one of the language's iteration interfaces (`Iterable<T>`): its iteration types, and what `source` iterates as.
	iterationOf(target: Type, source: Type, scope: Scope): { target: IterationTypes; source: IterationTypes } | undefined;
}

// `erased`: the iterated value is held as `any`, so it is iterated through `__towasm_iterate` (an array by position, whatever its element storage).
export interface IterationTypes { yield: Type; return: Type; next: Type; erased?: boolean }

// Where `break`/`continue` deliver their flow: a loop, a `switch`, or a labeled statement.
export interface FlowTarget { labels: string[]; loop: boolean; breaks: Scope[]; continues: Scope[] }

export type Declarator = JS.Var<Type> | JS.Param<Type>;

export class Scope {
	private values		= new Map<string, Type>();
	private lazyValues?:	Map<string, () => Type>;
	private types		= new Map<string, TypeEntry>();
	private narrowings?:	Map<string, Type | null>;	// control-flow refinements, consulted before declarations; `null`: a path an assignment invalidated
	private aliases?:		Map<string, Expr>;	// const initializers -- narrowing a const also narrows through its initializer (TS 4.4 aliased conditions)
	private sources?:		Map<string, Expr>;	// a const destructured from a union (`const {kind, a} = x`) IS `x.kind`: narrowed and read through it (TS 4.6)
	private namespaces?:	Map<string, Scope>;	// nested namespace/module scopes, keyed by their bound name -- consulted by `resolve` for a dotted type ref (`NS.Foo`)
	// The `function_decl`/`class_decl` statement a name resolves to: a consumer COMPILING a declaration reaches its source through the scope chain,
	// as types resolve, rather than a separate name-mangling scheme.
	private decls?:			Map<string, TS.Stmt>;
	// A numeric `let`/`var`'s declarator, which records the hull of every type the binding takes (`flowType`).
	private bindings?:		Map<string, JS.Var<Type>>;
	// The node declaring each value named by an identifier (a declarator or a parameter): a slot's identity, where its type is not.
	private declarators?:	Map<string, Declarator>;

	// Caches.
	resolving?:				Set<Type>;
	resolveCache?: 			WeakMap<Type, [Type | undefined, Type | undefined]>;
	// Held weakly: keyed by structure, it would otherwise keep every type it ever resolved alive for the scope's lifetime.
	resolveCacheById?:		Map<string, [WeakRef<Type> | undefined, WeakRef<Type> | undefined]>;
	lookupMemberCache?:		WeakMap<Type, Map<string, Type | undefined>>;

	// This scope IS the global declaration space, a SCRIPT's top level (no import/export): an `interface` there augments a same-named global one,
	// as in TS. A module's top level, and any block, is its own space.
	globalSpace = false;

	// Set by `recordTypes` while a caller wants this scope's own type entries restorable.
	private recorded?: Map<string, TypeEntry | undefined>;

	// Set on a function body's own scope: whether it is `async` (an async generator's `yield`/`yield*` await and iterate asynchronously), and for
	// a generator with a declared type what its `yield` must produce and evaluates to.
	functionKind?: { async: boolean; yield?: Type; next?: Type };
	// A statement's stamped flow (`stampedScope`): its narrowings copied, the scope it froze consulted only for declarations.
	snapshot?:	boolean;

	// `false` on a program's scope: `strictNullChecks` off, so `null`/`undefined` belong to every type. Unset inherits; the root is strict.
	nullChecks?: boolean;
	implicitAnyChecks?: boolean;
	// `true` reports a name that names nothing (TS2304), value or type. Off by default: a file checked without its imports loaded
	// names things it cannot see. Unset inherits.
	unknownNames?: boolean;

	// Where TS's control-flow container stops (a function declaration, a class declaration's members): the enclosing flow's narrowings don't reach in.
	flowBoundary = false;

	// A loop head's speculative walk: nothing under it stamps or reports, only its flow is read.
	quiet = false;
	// Where a `var` binds: a body's own scope (a function's, a program's, a static block's), never a nested block's.
	varBoundary = false;
	flowTarget?: FlowTarget;

	readonly parent?:	Scope;
	readonly semantics:	Semantics;

	// A root scope is made from its language's `Semantics`; every other inherits its parent's.
	constructor(outer: Scope | Semantics, private genericTemplate?: boolean) {
		this.parent		= outer instanceof Scope ? outer : undefined;
		this.semantics	= outer instanceof Scope ? outer.semantics : outer;
	}

	enclosingFunction(): Scope['functionKind']		{ return this.functionKind ?? this.parent?.enclosingFunction(); }
	varScope(): Scope								{ return this.varBoundary || !this.parent ? this : this.parent.varScope(); }
	strictNullChecks(): boolean						{ return this.nullChecks ?? this.parent?.strictNullChecks() ?? true; }
	noImplicitAny(): boolean						{ return this.implicitAnyChecks ?? this.parent?.noImplicitAny() ?? true; }
	reportsUnknownNames(): boolean					{ return this.unknownNames ?? this.parent?.reportsUnknownNames() ?? false; }

	hitDepthLimit(fn: string): void					{ this.parent?.hitDepthLimit(fn); }
	isQuiet(): boolean								{ return this.quiet || !!this.parent?.isQuiet(); }

	findTarget(label: string | undefined, isContinue: boolean): FlowTarget | undefined {
		const t = this.flowTarget;
		return t && (label ? t.labels.includes(label) && (!isContinue || t.loop) : !isContinue || t.loop) ? t
			: this.flowBoundary ? undefined : this.parent?.findTarget(label, isContinue);
	}

	// Every name narrowed between this scope and `base` (exclusive) that is bound at or above `base`: what a merge back into `base` reconciles.
	outerNarrowings(base: Scope): Set<string> {
		const keys = new Set<string>(), local = new Set<string>();
		for (let s: Scope | undefined = this; s && s !== base; s = s.parent) {
			s.narrowings?.forEach((_, k) => keys.add(k));
			s.values.forEach((_, k) => local.add(k));
		}
		return new Set([...keys].filter(k => !local.has(k.split(/[.[]/)[0])));
	}

	isGenericTemplate(): boolean					{ return !!this.genericTemplate || !!this.parent?.isGenericTemplate(); }

	value(name: string): Type | undefined {
		const n = this.narrowings?.get(name);
		// A snapshot holds every narrowing as of its statement: a name narrowed later in the scope it copied is no business of that statement.
		return n === null ? undefined : n ?? this.own(name) ?? (this.flowBoundary || this.snapshot ? this.parent?.declared(name) : this.parent?.value(name));
	}
	type(name: string): TypeEntry | undefined		{ return this.types.get(name) ?? this.parent?.type(name); }
	typeDeclaredIn(name: string): Scope | undefined	{ return this.types.has(name) ? this : this.parent?.typeDeclaredIn(name); }
	declared(name: string): Type | undefined		{ return this.own(name) ?? this.parent?.declared(name); }
	alias(name: string): Expr | undefined			{ return this.aliases?.get(name) ?? (this.values.has(name) ? undefined : this.parent?.alias(name)); }
	source(name: string): Expr | undefined			{ return this.sources?.get(name) ?? (this.values.has(name) ? undefined : this.parent?.source(name)); }
	hasSources(): boolean							{ return !!this.sources || !!this.parent?.hasSources(); }
	namespace(name: string): Scope | undefined		{ return this.namespaces?.get(name) ?? this.parent?.namespace(name); }
	decl(name: string): TS.Stmt | undefined	{ return this.decls?.get(name) ?? this.parent?.decl(name); }
	// The declaration that comes with the name's nearest binding, never one further out that binding hides (an interface over a lib class).
	boundDecl(name: string): TS.Stmt | undefined		{ return this.decls?.get(name) ?? (this.values.has(name) || this.types.has(name) ? undefined : this.parent?.boundDecl(name)); }
	// The class `name` names as a TYPE here: a nearer scope's type of that name that is no class (an imported interface) shadows a class further out.
	classDecl(name: string): TS.Class | undefined {
		const d = this.decls?.get(name);
		return d?.type === 'class_decl' ? d : this.types.has(name) ? undefined : this.parent?.classDecl(name);
	}
	declaring(name: string): Scope | undefined	{ return this.values.has(name) || this.lazyValues?.has(name) || this.namespaces?.has(name) ? this : this.parent?.declaring(name); }
	typeDeclaring(name: string): Scope | undefined	{ return this.types.has(name) ? this : this.parent?.typeDeclaring(name); }

	// A resolved structural type that is EXACTLY some declared type's registered shape (`infer R` bound to a class's instance type with no name
	// attached), matched by reference up the chain of each scope's own type map.
	findDeclaredName(target: Type): { name: string; scope: Scope } | undefined {
		for (let s: Scope | undefined = this; s; s = s.parent) {
			for (const [name, entry] of s.types)
				if (entry.type === target)
					return { name, scope: s };
		}
		return undefined;
	}

	// BFS through namespace imports for one whose `.type(leaf)` is the SAME object as `target`: name-only matching would hit unrelated re-exports.
	findQualifiedPath(leaf: string, target: Type): string[] | undefined {
		const seen = new Set<Scope>([this]);
		let frontier: { scope: Scope; path: string[] }[] = [{ scope: this, path: [] }];
		while (frontier.length) {
			const next: typeof frontier = [];
			for (const { scope, path } of frontier) {
				if (scope.namespaces) {
					for (const [name, ns] of scope.namespaces) {
						if (!seen.has(ns)) {
							seen.add(ns);
							const here = [...path, name];
							if (ns.type(leaf)?.type === target)
								return here;
							next.push({ scope: ns, path: here });
						}
					}
				}
			}
			frontier = next;
		}
		return undefined;
	}

	addValue(name: string, type: Type)				{ this.values.set(name, type); }
	// A closure may run after a later declaration in its block, so it sees that name, typed from the declaration when first read.
	addLazyValue(name: string, type: () => Type)	{ (this.lazyValues ??= new Map()).set(name, type); }
	private own(name: string): Type | undefined {
		const lazy = !this.values.has(name) && this.lazyValues?.get(name);
		if (lazy) {
			// Its own initializer reads it as though not yet declared.
			this.lazyValues!.delete(name);
			const t = lazy();
			if (!this.values.has(name))
				this.values.set(name, t);
		}
		return this.values.get(name);
	}
	// `mergeType`'s value counterpart, against THIS scope's binding only (a user's class never merges with a lib class): for the primitive wrappers,
	// declared twice as TS does (`class BigInt` for `new`, `declare var BigInt` for the call returning `bigint`).
	mergeValue(name: string, type: Type) {
		const prev = this.values.get(name);
		// An `any` is a PLACEHOLDER (what `hoist`'s `case 'import'` writes for an imported name not yet a value), and intersecting with one is `any`:
		// merging never loses a real declaration to one, whichever side carries it.
		this.values.set(name, !prev || isAny(prev) ? type : isAny(type) ? prev : TS.IntersectionType([type, prev]));
	}
	addType(name: string, type: Type, typeParams?: TS.TypeParam[])	{ this.types.set(name, {type, typeParams}); }
	// `constraint` is only an upper bound, not a resolvable alias (`TypeEntry.isTypeParam`).
	addTypeParam(name: string, constraint: Type)	{ this.types.set(name, {type: constraint, isTypeParam: true}); }
	addNarrowing(name: string, t: Type)				{ (this.narrowings ??= new Map()).set(name, t); }
	forget(path: string)							{ (this.narrowings ??= new Map()).set(path, null); }
	addAlias(d: JS.Var<any>)						{ (this.aliases ??= new Map()).set(d.name, d.init); }
	addSource(name: string, e: Expr)				{ (this.sources ??= new Map()).set(name, e); }
	addNamespace(name: string, s: Scope)			{ (this.namespaces ??= new Map()).set(name, s); }
	ownNamespace(name: string): Scope | undefined	{ return this.namespaces?.get(name); }
	ownValue(name: string): Type | undefined		{ return this.values.get(name); }
	addDecl(name: string, stmt: TS.Stmt)			{ (this.decls ??= new Map()).set(name, stmt); }
	addBinding(name: string, d: JS.Var<Type>)		{ (this.bindings ??= new Map()).set(name, d); }
	// Through function boundaries (a closure's write is the binding's too); a nearer declaration of the name shadows it.
	binding(name: string): JS.Var<Type> | undefined	{ return this.bindings?.get(name) ?? (this.values.has(name) ? undefined : this.parent?.binding(name)); }
	addDeclarator(name: string, d: Declarator)		{ (this.declarators ??= new Map()).set(name, d); }
	declarator(name: string): Declarator | undefined	{ return this.declarators?.get(name) ?? (this.values.has(name) ? undefined : this.parent?.declarator(name)); }

	mergeType(name: string, type: Type, typeParams: TS.TypeParam[] | undefined, augment = false) {
		// An `interface` in the GLOBAL declaration space augments a same-named one further out (`interface Array<T> { slice(): this }`), merged into the scope
		// DECLARING it, inherited part first; a local interface shadows instead. `recordTypes` undoes it between a harness's files.
		const owner = augment && this.globalSpace && !this.types.has(name) ? this.ownerOfType(name) : undefined;
		if (owner)
			owner.mergeTypeEntry(name, {type, typeParams});
		else
			this.mergeTypeEntry(name, {type, typeParams});
	}

	// The same entry again is no merge -- `export interface X` beside `export function X` copies it twice -- and a joined copy
	// would lose the entry's identity, which says which module declared it.
	private mergeTypeEntry(name: string, te: TypeEntry) {
		const prev = this.types.get(name);
		this.noteType(name);
		this.types.set(name, prev && prev !== te ? { typeParams: prev.typeParams ?? te.typeParams, type: joinTypes([prev.type, te.type]) } : te);
	}

	private ownerOfType(name: string): Scope | undefined {
		return this.types.has(name) ? this : this.parent?.ownerOfType(name);
	}

	// What a SCRIPT augments here, undone: a harness that checks many files against one global scope (the corpus, test-checker)
	// must not carry one file's global `interface Array<T> { ... }` into the next. Returns the undo.
	recordTypes(): () => void {
		const before = this.recorded = new Map<string, TypeEntry | undefined>();
		return () => {
			this.recorded = undefined;
			before.forEach((te, name) => te ? this.types.set(name, te) : this.types.delete(name));
			// Both caches are keyed by type OBJECT, which the augmentation left untouched: what they hold of it is now wrong.
			this.resolveCache		= undefined;
			this.resolveCacheById	= undefined;
			this.lookupMemberCache	= undefined;
		};
	}

	private noteType(name: string) {
		if (this.recorded && !this.recorded.has(name))
			this.recorded.set(name, this.types.get(name));
	}

	lookupScope(parts: string[]): Scope | undefined {
		let ns: Scope | undefined = this;
		for (const p of parts) {
			ns = ns.namespace(p);
			if (!ns)
				return undefined;
		}
		return ns;
	}

	// A dotted name's namespace scope, beside its last part.
	qualified(name: string): [Scope | undefined, string] {
		const parts	= name.split('.');
		const last	= parts.pop()!;
		return [this.lookupScope(parts), last];
	}

	lookupType(name: string): TypeEntry | undefined {
		const [ns, last] = this.qualified(name);
		return ns?.type(last);
	}

	lookupValue(name: string): TS.Type | undefined {
		const [ns, last] = this.qualified(name);
		return ns?.value(last);
	}

	root(): Scope {
		return this.parent?.root() ?? this;
	}
	

	// Every name narrowed anywhere between this scope and `base` (exclusive); used to combine two independently-narrowed branches of a `||`/`&&` test.
	narrowedNames(base?: Scope): Set<string> {
		const names = new Set<string>();
		for (let s: Scope | undefined = this; s && s !== base; s = s.parent)
			for (const name of s.narrowings?.keys() ?? [])
				names.add(name);
		return names;
	}

	copy(from: Scope, local: string, pub: string, typeOnly = false) {
		if (!typeOnly) {
			const v = from.value(local);
			if (v)
				this.values.set(pub, v);
			const ns = from.namespace(local);
			if (ns)
				this.addNamespace(pub, ns);
			const d = from.boundDecl(local);
			if (d)
				this.addDecl(pub, d);
			const dr = from.declarator(local);
			if (dr)
				this.addDeclarator(pub, dr);
		}
		const te = from.type(local);
		if (te)
			this.mergeTypeEntry(pub, te);
	}
	copyAll(from: Scope, typeOnly = false) {
		for (const name of new Set([...from.values.keys(), ...from.types.keys()]))
			this.copy(from, name, name, typeOnly);
	}

	toObject() {
		const members: TS.TypeMember[] = [];
		for (const [name, typeAnnotation] of this.values)
			members.push({ type: 'property', key: name, typeAnnotation });
		return TS.ObjectType(members);
	}
}
