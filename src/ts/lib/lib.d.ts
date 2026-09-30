/* eslint-disable @typescript-eslint/no-empty-object-type */
/* eslint-disable no-shadow-restricted-names */
/* eslint-disable no-var */
// Ambient declarations shared by every `lib/*.ts` file -- read and parsed alongside them (see backend.ts's
// own `LIB_AST`), never `import`ed as a normal module, so none of this needs an `export`.


declare module 'wasi_snapshot_preview1' {
	export function fd_write(fd: i32, iovsPtr: i32, iovsLen: i32, nwrittenPtr: i32): i32;
	export function fd_read(fd: i32, iovsPtr: i32, iovsLen: i32, nreadPtr: i32): i32;
	export function fd_close(fd: i32): i32;
	export function fd_filestat_get(fd: i32, bufPtr: i32): i32;
	export function fd_prestat_get(fd: i32, prestatPtr: i32): i32;
	export function fd_prestat_dir_name(fd: i32, pathPtr: i32, pathLen: i32): i32;
	export function path_open(fd: i32, dirflags: i32, pathPtr: i32, pathLen: i32, oflags: i32, fsRightsBase: i64, fsRightsInheriting: i64, fdflags: i32, openedFdPtr: i32): i32;
	export function fd_readdir(fd: i32, bufPtr: i32, bufLen: i32, cookie: i64, bufusedPtr: i32): i32;
	export function path_filestat_get(fd: i32, flags: i32, pathPtr: i32, pathLen: i32, bufPtr: i32): i32;
	export function path_create_directory(fd: i32, pathPtr: i32, pathLen: i32): i32;
	export function proc_exit(code: i32): void;
	export function args_get(argvPtr: i32, argvBufPtr: i32): i32;
	export function args_sizes_get(argcPtr: i32, argvBufSizePtr: i32): i32;
	export function environ_get(environPtr: i32, environBufPtr: i32): i32;
	export function environ_sizes_get(environCountPtr: i32, environBufSizePtr: i32): i32;
}
// Declaring standard modern WASI resource management functions
declare module 'wasi:io/resource-error' {
	// Standard WASI function to drop a host resource handle
	export function drop(resourceHandle: i32): void;
}

// `__asm(asmText)` is how a lib file embeds real wasm assembly -- backend.ts's own `isAsm`/`makeAsmBuiltin`
// recognize a call to this exact name and compile `asmText` as real instructions (see `WAT.parseAsmBody`),
// so `Math.floor = __asm<[number], number>('(switch $T (($f32 $f64) $T.floor))')` really does emit an
// `f64.floor`/`f32.floor` at every call site, per whichever type the switch's own arm declares. This
// `declare` itself is only the *signature* half of that: a bodyless ambient function
// has no real implementation to fall back to, but nothing ever calls it as a plain function either -- the
// general checker and the editor just need *some* type for `__asm<...>(...)` to type-check the field/const
// it's assigned to, and this is what supplies it.
declare function __asm<P extends any[], R>(asm: string): (...args: P) => R;

// `console.ts`'s bump allocator, declared here as a global rather than imported: `lib/node/*` is loaded
// ON DEMAND as a real module, and an `import` of `./console` would compile a SECOND copy of it -- a second
// `heap` over the same linear memory, which is silent corruption, not duplication.
declare function __alloc(size: i32, align: i32): i32;
// Mark/release around `__alloc`'s bump offset -- the only reclamation it has. Release only once every
// value that must outlive the scratch (a GC string/array/object) has been built; a raw pointer does not
// survive a release.
declare function __allocMark(): i32;
declare function __allocRelease(mark: i32): void;

// Same shape as `StringParser` below: the real one is `export`ed from `bigint.ts`, which makes it a
// MODULE to tsc and so invisible to a sibling lib file -- towasm sees one flat scope. Named here rather
// than imported, for the reason `lib/node/*` must never import a static lib file.
declare function bigToNumber(a: bigint): number;

declare function pure(target: any, propertyKey: string, descriptor: PropertyDescriptor): void;

// Machine types: a value that fits, and forces, the wasm slot named -- `Int<Bits, Signed>` a machine integer, `Float<Bits>` a float.
// Built in, found through these declarations (never by a type's own name); a value is converted into its slot. To tsc, which
// checks this lib too, each is just the JS type its value has: a `bigint` above 53 bits, which a `number` cannot hold exactly.
declare type Int<Bits extends 8 | 16 | 32 | 64, Signed extends boolean> = Bits extends 64 ? bigint : number;
declare type Float<Bits extends 32 | 64> = number;
declare type i8 = Int<8, true>;
declare type u8 = Int<8, false>;
declare type i16 = Int<16, true>;
declare type u16 = Int<16, false>;
declare type i32 = Int<32, true>;
declare type u32 = Int<32, false>;
declare type i64 = Int<64, true>;
declare type u64 = Int<64, false>;
declare type f32 = Float<32>;
declare type f64 = Float<64>;

declare var NaN: number;
declare var Infinity: number;

interface Function {
	apply(this: Function, thisArg: any, argArray?: any): any;
	call(this: Function, thisArg: any, ...argArray: any[]): any;
	bind(this: Function, thisArg: any, ...argArray: any[]): any;
	toString(): string;
	readonly length: number;
	readonly name: string;
}
interface CallableFunction {}
interface NewableFunction {}
interface IArguments {}
interface Boolean {}
declare var Boolean: {
	(value?: any): boolean;
};

//-----------------------------------------------------------------------------
//	Object
//-----------------------------------------------------------------------------

interface Symbol {
	readonly description: string | undefined;
	toString(): string;
	valueOf(): symbol;
}

// `Symbol` as a VALUE, as far as the lib uses one: the well-known key `[Symbol.iterator]`. A `unique symbol`, so a
// computed key made from it is a symbol key, never checked against a numeric index signature.
interface SymbolConstructor {
	(description?: string | number): symbol;
	readonly iterator: unique symbol;
	readonly hasInstance: unique symbol;
	readonly isConcatSpreadable: unique symbol;
	readonly match: unique symbol;
	readonly replace: unique symbol;
	readonly search: unique symbol;
	readonly species: unique symbol;
	readonly split: unique symbol;
	readonly toPrimitive: unique symbol;
	readonly toStringTag: unique symbol;
	readonly unscopables: unique symbol;
	readonly asyncIterator: unique symbol;
	readonly matchAll: unique symbol;
	readonly dispose: unique symbol;
	readonly asyncDispose: unique symbol;
}
declare var Symbol: SymbolConstructor;

// The iteration protocol as the lib uses it. The implementations are lib/generator.ts's classes; that file is a module,
// so tsc cannot see them from here, while tison flattens the lib into one scope and merges these with them.
interface IteratorResult<Y, R> {
	value: Y | R;
	done: boolean;
}
interface Generator<Y, R, N> {
	next(v: N): IteratorResult<Y, R>;
	[Symbol.iterator](): Generator<Y, R, N>;
}
interface Iterator<T, R = any, N = any> {
	next(v?: N): IteratorResult<T, R>;
}
interface Iterable<T, R = any, N = any> {
	[Symbol.iterator](): Iterator<T, R, N>;
}
interface IterableIterator<T, R = any, N = any> extends Iterator<T, R, N> {
	[Symbol.iterator](): IterableIterator<T, R, N>;
}
declare function __towasm_indexed<T>(size: () => number, at: (i: number) => T): Generator<T, void, unknown>;
interface PromiseLike<T> {
	then<TResult1 = T, TResult2 = never>(onfulfilled?: ((value: T) => TResult1 | PromiseLike<TResult1>) | null, onrejected?: ((reason: any) => TResult2 | PromiseLike<TResult2>) | null): PromiseLike<TResult1 | TResult2>;
}

declare type PropertyKey = string | number | symbol;

interface PropertyDescriptor {
	configurable?: boolean;
	enumerable?: boolean;
	value?: any;
	writable?: boolean;
	get?(): any;
	set?(v: any): void;
}

interface PropertyDescriptorMap {
	[key: PropertyKey]: PropertyDescriptor;
}

// A compiler intrinsic, not real TS source: what fields exist depends on the argument's own concrete
// type at each call site, which only the compiler itself can see. `entries`/`values`/`keys` currently
// support a `Map`-backed dynamic object (forward to its own real methods) and a *sealed* (never-
// subclassed) struct-backed class/object-shape; an extended class isn't supported yet (would need the
// receiver's real runtime type, not just its static one). `defineProperty` only supports a plain value
// descriptor (`{value: ...}`, real `enumerable`/`configurable`/`writable` flags accepted but with no
// observable effect) and a literal string `key` -- see `emitObjectDefineProperty` in backend.ts.
interface Object {
	constructor: Function;
	toString(): string;
	toLocaleString(): string;
	valueOf(): Object;
	hasOwnProperty(v: PropertyKey): boolean;
	isPrototypeOf(v: Object): boolean;
	propertyIsEnumerable(v: PropertyKey): boolean;
}
declare var Object: {
	// TS's own overloads (lib.es2017.object): the generic one preserves the value type, which needs
	// inference through an index signature (`inferTypeArgs`' own `index` case).
	entries<T>(o: { [s: string]: T } | ArrayLike<T>): [string, T][];
	entries(o: {}): [string, any][];
	values<T>(o: { [s: string]: T } | ArrayLike<T>): T[];
	values(o: {}): any[];
	keys<T>(x: T): string[];
	// TS's own overloads (lib.es2019.object).
	fromEntries<T = any>(entries: Iterable<readonly [PropertyKey, T]>): { [k: string]: T };
	fromEntries(entries: Iterable<readonly any[]>): any;
	is<A, B>(a: A, b: B): boolean;
	// TS's own overloads (lib.es2015.core): the result carries every source's members.
	assign<T extends {}, U>(target: T, source: U): T & U;
	assign<T extends {}, U, V>(target: T, source1: U, source2: V): T & U & V;
	assign<T extends {}, U, V, W>(target: T, source1: U, source2: V, source3: W): T & U & V & W;
	assign(target: object, ...sources: any[]): any;
	defineProperty<T>(target: T, key: PropertyKey, descriptor: PropertyDescriptor): T;
};

//-----------------------------------------------------------------------------
//	Number
//-----------------------------------------------------------------------------

interface Number {
	// `lib/number.ts` implements far more than this; declared here because the lib's own sources call it
	// (`Array._indexKeys`), and `lib/tsconfig.json` is the only thing that type-checks them.
	toString(radix?: number): string;
}
declare var Number: {
	new (value?: any): Number;
	(value?: any): number;
};

//-----------------------------------------------------------------------------
//	BigInt
//-----------------------------------------------------------------------------
interface BigInt {
	// Declared because the lib's own sources call them (`toString` recurses on the magnitude, `pow`
	// squares); `lib/bigint.ts` implements far more, and `lib/tsconfig.json` is the only thing that
	// type-checks those sources at all.
	toString(radix?: number): string;
	mul(b: bigint): bigint;
	add(b: bigint): bigint;
}
// The CALL side, as TypeScript's own `BigIntConstructor`: `BigInt(5)` is a `bigint`, and there is no `new BigInt()` (it throws).
declare var BigInt: {
	(value: bigint | boolean | number | string): bigint;
	asIntN(bits: number, int: bigint): bigint;
	asUintN(bits: number, int: bigint): bigint;
};


//-----------------------------------------------------------------------------
//	String
//-----------------------------------------------------------------------------

interface String {
	readonly length: u32;

	toString(): string;
	charAt(pos: number): string;
	charCodeAt(index: number): number;
	//concat(...strings: string[]): string;
	concat(b: string): string;
	indexOf(searchString: string, position?: number): number;
	lastIndexOf(searchString: string, position?: number): number;
//	localeCompare(that: string): number;
	match(regexp: string | RegExp): RegExpMatchArray | null;
	replace(searchValue: string | RegExp, replaceValue: string): string;
	replace(searchValue: string | RegExp, replacer: (substring: string, ...args: any[]) => string): string;
	search(regexp: string | RegExp): number;
	slice(start?: number, end?: number): string;
	split(separator: string | RegExp, limit?: number): string[];
	substring(start: number, end?: number): string;
	toLowerCase(): string;
	toLocaleLowerCase(): string;
	toUpperCase(): string;
	toLocaleUpperCase(): string;
	trim(): string;

	valueOf(): string;

	readonly [index: number]: string;
}

declare var String: {
	(value?: any): string;
//	fromCharCode(...codes: number[]): string;
	fromCharCode(code: number): string;
	fromCodePoint(...codePoints: number[]): string;
	// One byte per char code, read straight out of linear memory -- the single-alloc counterpart to
	// building a string one `fromCharCode` at a time, for `lib/node/*`'s own WASI buffers.
	fromCharCodesAt(ptr: i32, len: i32): string;
};

//-----------------------------------------------------------------------------
//	RegExp
//-----------------------------------------------------------------------------

interface RegExpMatchArray extends Array<string> {
	index?: number;
	input?: string;
	0: string;
}

interface RegExpExecArray extends Array<string> {
	index: number;
	input: string;
	0: string;
}

//-----------------------------------------------------------------------------
//	Tagged templates
//-----------------------------------------------------------------------------

// The array a tag function's first parameter really is -- `case 'tagged_template'` synthesizes a plain
// `string[]` of the cooked text for it. `raw` is declared so the checker reports its real type rather
// than "no such property", but has no physical slot: reading it is an honest `unknown field 'raw'`.
interface TemplateStringsArray extends Array<string> {
	raw: string[];
}

interface RegExp {
	exec(string: string): RegExpExecArray | null;
	test(string: string): boolean;
	readonly source: string;
	readonly global: boolean;
	readonly ignoreCase: boolean;
	readonly multiline: boolean;

	lastIndex: number;

	// Non-standard extensions
}

// As TS's `RegExpConstructor`: callable without `new` (`RegExp(src, flags)`), same as `ArrayConstructor` above.
interface RegExpConstructor {
	new (source: string, flags?: string): RegExp;
	(source: string, flags?: string): RegExp;
}
declare var RegExp: RegExpConstructor;

//-----------------------------------------------------------------------------
//	Array
//-----------------------------------------------------------------------------

// The raw fixed-length wasm array (see lib/array.ts). Opaque: everything that touches one goes through
// `RawArray`'s own methods.
declare class RawArray<T> {
	constructor(n: number);
	readonly length: u32;
	[i: number]: T;
	copyFrom(dstStart: number, src: RawArray<T>, srcStart: number, len: number): void;
	fillWith(start: number, val: T, len: number): void;
}

interface Array<T> {
	[i: number]: T;
	get length(): u32; set length(n: number);

	grow(n: i32): i32;
	toString(): string;
	toLocaleString(): string;
	pop(): T | undefined;
	//push(...items: T[]): number;
	//concat(...items: ConcatArray<T>[]): T[];
	//concat(...items: (T | ConcatArray<T>)[]): T[];
	//unshift(...items: T[]): number;
	push(item: T): number;
	concat(item: T[]): T[];
	unshift(item: T): number;
	join(separator?: string): string;
	reverse(): T[];
	shift(): T | undefined;
	slice(start?: number, end?: number): T[];
	sort(compareFn?: (a: T, b: T) => number): this;
	splice(start: number, deleteCount?: number): T[];
	splice(start: number, deleteCount: number, ...items: T[]): T[];
	indexOf(searchElement: T, fromIndex?: number): number;
	lastIndexOf(searchElement: T, fromIndex?: number): number;
	every<S extends T>(predicate: (value: T, index: number, array: T[]) => value is S, thisArg?: any): this is S[];
	every(predicate: (value: T, index: number, array: T[]) => unknown, thisArg?: any): boolean;
	some(predicate: (value: T, index: number, array: T[]) => unknown, thisArg?: any): boolean;
	forEach(callbackfn: (value: T, index: number, array: T[]) => void, thisArg?: any): void;
	map<U>(callbackfn: (value: T, index: number, array: T[]) => U, thisArg?: any): U[];
	filter<S extends T>(predicate: (value: T, index: number, array: T[]) => value is S, thisArg?: any): S[];
	filter(predicate: (value: T, index: number, array: T[]) => unknown, thisArg?: any): T[];
	find<S extends T>(predicate: (value: T, index: number, obj: T[]) => value is S, thisArg?: any): S | undefined;
	find(predicate: (value: T, index: number, obj: T[]) => unknown, thisArg?: any): T | undefined;
	findIndex(predicate: (value: T, index: number, obj: T[]) => unknown, thisArg?: any): number;
	reduce(callbackfn: (previousValue: T, currentValue: T, currentIndex: number, array: T[]) => T): T;
	reduce(callbackfn: (previousValue: T, currentValue: T, currentIndex: number, array: T[]) => T, initialValue: T): T;
	reduce<U>(callbackfn: (previousValue: U, currentValue: T, currentIndex: number, array: T[]) => U, initialValue: U): U;
	reduceRight(callbackfn: (previousValue: T, currentValue: T, currentIndex: number, array: T[]) => T): T;
	reduceRight(callbackfn: (previousValue: T, currentValue: T, currentIndex: number, array: T[]) => T, initialValue: T): T;
	reduceRight<U>(callbackfn: (previousValue: U, currentValue: T, currentIndex: number, array: T[]) => U, initialValue: U): U;
	[Symbol.iterator](): Generator<T, void, unknown>;
}

// As TS's `ArrayConstructor`: `Array` is callable WITHOUT `new` as well (`Array(n).fill(x)`, the standard
// fixed-size idiom), which a `declare class` alone cannot say -- its value has only a construct signature.
// The statics stay on the class in `lib/array.ts`.
interface ArrayConstructor {
	new <T>(n?: number): T[];
	<T>(n?: number): T[];
}
declare var Array: ArrayConstructor;

interface ArrayLike<T> {
	readonly length: u32;
	readonly [n: number]: T;
}

interface ConcatArray<T> {
	readonly length: u32;
	readonly [n: number]: T;
	join(separator?: string): string;
	slice(start?: number, end?: number): T[];
}

// As TS's: the non-mutating part of `Array`. Physically every readonly array IS an `Array` (`READONLY_ALIAS`);
// without this declaration a `readonly T[]` was an unknown name, assignable to anything (`undefined` included).
interface ReadonlyArray<T> {
	readonly length: u32;
	readonly [n: number]: T;
	toString(): string;
	toLocaleString(): string;
	concat(item: T[]): T[];
	join(separator?: string): string;
	slice(start?: number, end?: number): T[];
	indexOf(searchElement: T, fromIndex?: number): number;
	lastIndexOf(searchElement: T, fromIndex?: number): number;
	at(index: number): T | undefined;
	includes(searchElement: T): boolean;
	every<S extends T>(predicate: (value: T, index: number, array: readonly T[]) => value is S, thisArg?: any): this is readonly S[];
	every(predicate: (value: T, index: number, array: readonly T[]) => unknown, thisArg?: any): boolean;
	some(predicate: (value: T, index: number, array: readonly T[]) => unknown, thisArg?: any): boolean;
	forEach(callbackfn: (value: T, index: number, array: readonly T[]) => void, thisArg?: any): void;
	map<U>(callbackfn: (value: T, index: number, array: readonly T[]) => U, thisArg?: any): U[];
	flatMap<U>(callback: (value: T, index: number, array: readonly T[]) => U[], thisArg?: any): U[];
	filter<S extends T>(predicate: (value: T, index: number, array: readonly T[]) => value is S, thisArg?: any): S[];
	filter(predicate: (value: T, index: number, array: readonly T[]) => unknown, thisArg?: any): T[];
	find<S extends T>(predicate: (value: T, index: number, obj: readonly T[]) => value is S, thisArg?: any): S | undefined;
	find(predicate: (value: T, index: number, obj: readonly T[]) => unknown, thisArg?: any): T | undefined;
	findIndex(predicate: (value: T, index: number, obj: readonly T[]) => unknown, thisArg?: any): number;
	reduce(callbackfn: (previousValue: T, currentValue: T, currentIndex: number, array: readonly T[]) => T): T;
	reduce(callbackfn: (previousValue: T, currentValue: T, currentIndex: number, array: readonly T[]) => T, initialValue: T): T;
	reduce<U>(callbackfn: (previousValue: U, currentValue: T, currentIndex: number, array: readonly T[]) => U, initialValue: U): U;
	reduceRight(callbackfn: (previousValue: T, currentValue: T, currentIndex: number, array: readonly T[]) => T): T;
	reduceRight(callbackfn: (previousValue: T, currentValue: T, currentIndex: number, array: readonly T[]) => T, initialValue: T): T;
	reduceRight<U>(callbackfn: (previousValue: U, currentValue: T, currentIndex: number, array: readonly T[]) => U, initialValue: U): U;
	[Symbol.iterator](): Generator<T, void, unknown>;
}

// Likewise the non-mutating part of `Map`/`Set` (lib/map.ts): physically each IS one (`READONLY_ALIAS`).
interface ReadonlyMap<K, V> {
	readonly size: number;
	get(key: K): V | undefined;
	has(key: K): boolean;
	keys(): K[];
	values(): V[];
	entries(): [K, V][];
	[Symbol.iterator](): Generator<[K, V], void, unknown>;
	forEach(callbackfn: (value: V, key: K, map: ReadonlyMap<K, V>) => void, thisArg?: any): void;
}
interface ReadonlySet<T> {
	readonly size: number;
	has(value: T): boolean;
	keys(): T[];
	values(): T[];
	entries(): [T, T][];
	[Symbol.iterator](): Generator<T, void, unknown>;
	forEach(callbackfn: (value: T, value2: T, set: ReadonlySet<T>) => void, thisArg?: any): void;
}


// `import.meta`: TS's own is empty; these are Node's, as `__dirname`/`__filename` are.
interface ImportMeta {
	url:		string;
	dirname:	string;
	filename:	string;
}

//-----------------------------------------------------------------------------
//	TypedArray
//-----------------------------------------------------------------------------
interface ArrayBuffer {
//	byteLength: number;
}
// TS's is `ArrayBuffer | SharedArrayBuffer`; this lib has no SharedArrayBuffer.
declare type ArrayBufferLike = ArrayBuffer;

interface TypedArray<T extends number | bigint> {
	readonly BYTES_PER_ELEMENT: number;
	/*readonly*/ buffer: ArrayBuffer;
	readonly byteOffset: u32;
	readonly byteLength: u32;
	readonly length: u32;
	[index: number]: T;

	copyWithin(target: number, start: number, end?: number): this;
	every(predicate: (value: T, index: number, array: this) => unknown, thisArg?: any): boolean;
	fill(value: T, start?: number, end?: number): this;
	filter(predicate: (value: T, index: number, array: this) => any, thisArg?: any): TypedArray<T>;
	find(predicate: (value: T, index: number, obj: this) => boolean, thisArg?: any): T | undefined;
	findIndex(predicate: (value: T, index: number, obj: this) => boolean, thisArg?: any): number;
	forEach(callbackfn: (value: T, index: number, array: this) => void, thisArg?: any): void;
	indexOf(searchElement: T, fromIndex?: number): number;
	join(separator?: string): string;
	lastIndexOf(searchElement: T, fromIndex?: number): number;
	map(callbackfn: (value: T, index: number, array: this) => T, thisArg?: any): TypedArray<T>;
	reduce(callbackfn: (previousValue: T, currentValue: T, currentIndex: number, array: this) => T): T;
	reduce(callbackfn: (previousValue: T, currentValue: T, currentIndex: number, array: this) => T, initialValue: T): T;
	reduce<U>(callbackfn: (previousValue: U, currentValue: T, currentIndex: number, array: this) => U, initialValue: U): U;
	reduceRight(callbackfn: (previousValue: T, currentValue: T, currentIndex: number, array: this) => T): T;
	reduceRight(callbackfn: (previousValue: T, currentValue: T, currentIndex: number, array: this) => T, initialValue: T): T;
	reduceRight<U>(callbackfn: (previousValue: U, currentValue: T, currentIndex: number, array: this) => U, initialValue: U): U;
	reverse(): this;
	// Iterable, as TS's own typed arrays are; `lib/typedarray.ts` implements it as an indexed generator.
	[Symbol.iterator](): Generator<T, void, unknown>;
	set(array: ArrayLike<T>, offset?: number): void;
	slice(start?: number, end?: number): TypedArray<T>;
	some(predicate: (value: T, index: number, array: this) => unknown, thisArg?: any): boolean;
	sort(compareFn?: (a: T, b: T) => number): this;
	subarray(begin?: number, end?: number): TypedArray<T>;
	toLocaleString(): string;
	toString(): string;
	valueOf(): this;
}
declare type Int8Array = TypedArray<i8>;
declare type Uint8Array = TypedArray<u8>;
declare type Uint8ClampedArray = TypedArray<u8>;
declare type Int16Array = TypedArray<i16>;
declare type Uint16Array = TypedArray<u16>;
declare type Int32Array = TypedArray<i32>;
declare type Uint32Array = TypedArray<u32>;
declare type Float32Array = TypedArray<f32>;
declare type Float64Array = TypedArray<f64>;
declare type BigInt64Array = TypedArray<i64>;
declare type BigUint64Array = TypedArray<u64>;

// node's `Buffer`, implemented for real by `lib/buffer.ts` -- the same class-merges-with-its-own-ambient-
// interface pairing `TypedArray` uses, so `lib/node/*.ts` (which sees only what is declared here) can name it.
interface Buffer extends TypedArray<u8> {
	// Spelled here because the ambient `TypedArray` deliberately leaves its own commented out; a `Buffer`
	// really is indexed by number, and `lib/buffer.ts` inherits the class's real `[i: i32]: number`.
	[i: number]: number;
	toString(encoding?: string, start?: number, end?: number): string;
}
declare var Buffer: {
	new (length: number): Buffer;
	from(array: number[]): Buffer;
};


//declare var TypedArray: {
//	new (length: number): TypedArray<any>;
//	new (buffer: ArrayBuffer, byteOffset?: number, length?: number): TypedArray<any>;
//	new (array: ArrayBuffer): TypedArray<any>;
//	new <T>(array: ArrayLike<T>): TypedArray<any>;
//	readonly BYTES_PER_ELEMENT: number;
//	of<T>(...items: T[]): TypedArray<T>;
//	from<T>(arrayLike: ArrayLike<T>): TypedArray<T>;
//	from<T, U>(arrayLike: ArrayLike<T>, mapfn: (v: T, k: number) => U, thisArg?: any): TypedArray<U>;
//}

//-----------------------------------------------------------------------------
//	Math
//-----------------------------------------------------------------------------

declare var Math: {
	readonly E: number;
	readonly LN10: number;
	readonly LN2: number;
	readonly LOG2E: number;
	readonly LOG10E: number;
	readonly PI: number;
	readonly SQRT1_2: number;
	readonly SQRT2: number;
	abs(x: number): number;
	acos(x: number): number;
	asin(x: number): number;
	atan(x: number): number;
	atan2(y: number, x: number): number;
	ceil(x: number): number;
	cos(x: number): number;
	exp(x: number): number;
	floor(x: number): number;
	log(x: number): number;
//	max(...values: number[]): number;
//	min(...values: number[]): number;
	max(a: number, b: number): number;
	min(a: number, b: number): number;
	pow(x: number, y: number): number;
	random(): number;
	round(x: number): number;
	sin(x: number): number;
	sqrt(x: number): number;
	tan(x: number): number;
};

//-----------------------------------------------------------------------------
//
//-----------------------------------------------------------------------------
//-----------------------------------------------------------------------------
//
//-----------------------------------------------------------------------------
declare class StringParser {
	str: string;
	pos: number;
	n: number;
	constructor(str: string, pos?: number);

	remaining(): number;
	remainder(): string;
	processed(): string;

	code(): number;
	skipCode(c: number): boolean;
	skipWhitespace(): void;
}
declare function UnsignedToString(n: number, radix?: number, digits?: number): string;
declare function strIsSpace(code: number): boolean;
declare function __towasm_alloc(size: i32, align: i32): i32;

//-----------------------------------------------------------------------------
//	Utility types
//-----------------------------------------------------------------------------

type Partial<T> = { [P in keyof T]?: T[P]; };
type Record<K extends keyof any, T> = { [P in K]: T; };
type Exclude<T, U> = T extends U ? never : T;
type Extract<T, U> = T extends U ? T : never;
type NonNullable<T> = T & {};
type Pick<T, K extends keyof T> = { [P in K]: T[P]; };
type Omit<T, K extends keyof any> = Pick<T, Exclude<keyof T, K>>;
type Readonly<T> = { readonly [P in keyof T]: T[P]; };
type Parameters<T extends (...args: any) => any> = T extends (...args: infer P) => any ? P : never;
type ReturnType<T extends (...args: any) => any> = T extends (...args: any) => infer R ? R : any;

