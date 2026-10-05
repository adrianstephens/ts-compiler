// Checker precision and soundness cases, against lib.esnext.full as the corpus uses. Each case lists the ERRORs it
// must produce (a substring each, in order) -- `[]` means it must be clean. A deliberately wrong annotation is how a
// case proves the checker computed the precise type rather than `any`, which would pass silently.
import * as path from 'path';
import * as TS from '../dist/ts/ts-parser';
import * as T from '../dist/ts/type-utils';
import { checkBlock, SEVERITY } from '../dist/ts/checker';
import { TStypeCheckAsync } from '../dist/ts/transform';
import { ModuleLoader } from '../dist/ts/module-loader';

const NOT_ASSIGNABLE = (from: string, to: string) => `Type '${from}' is not assignable to type '${to}'`;

// `nonStrict`: checked with `strictNullChecks` off (tsc's default; the corpus's unless a test says `@strict`).
const cases: [name: string, code: string, errors: string[], nonStrict?: true][] = [
	// iteration protocol: every consumer reads `[Symbol.iterator]().next()`
	['for-of over Map.keys()',		'for (const x of new Map([[1, "a"]]).keys()) { const q: string = x; }',					[NOT_ASSIGNABLE('number', 'string')]],
	['for-of destructures entries',	'for (const [k, v] of new Map([[1, "a"]])) { const q: boolean = k; }',					[NOT_ASSIGNABLE('number', 'boolean')]],
	['for-of over a string',		'for (const c of "abc") { const q: number = c; }',										[NOT_ASSIGNABLE('string', 'number')]],
	['spread of a Set',				'const s = [...new Set([1, 2])]; const q: string = s[0];',								[NOT_ASSIGNABLE('number', 'string')]],
	['destructuring a Set',			'const [a] = new Set([1, 2]); const q: string = a;',									[NOT_ASSIGNABLE('number', 'string')]],
	['Map inference via Iterable',	'const m = new Map([["a", 1]]); const q: boolean = m.get("a");',						[NOT_ASSIGNABLE('number | undefined', 'boolean')]],
	['overload trial, final context', 'declare function mk<K, V>(entries: readonly (readonly [K, V])[]): Map<K, V>; declare function mk<K, V>(other: Map<K, V>): Map<K, V>; const m = mk([1, 2].map(x => [String(x), x])); const q: boolean = m.get("1");', [NOT_ASSIGNABLE('number | undefined', 'boolean')]],
	['yield* delegates',			'function* g() { yield* new Set([1]); } for (const x of g()) { const q: string = x; }',	[NOT_ASSIGNABLE('number', 'string')]],
	['yield* evaluates to TReturn',	'function* g(): Generator<number, string> { return "x"; } function* h() { const r = yield* g(); const q: number = r; }', [NOT_ASSIGNABLE('string', 'number')]],
	['for await over async gen',	'async function* ag() { yield 1; } async function f() { for await (const x of ag()) { const q: string = x; } }', [NOT_ASSIGNABLE('number', 'string')]],
	['yield* in an async generator', 'async function* a(): AsyncGenerator<number> { yield* b(); } async function* b() { yield 1; }', []],
	['user-defined iterator class',	'class It { next() { return { value: 1, done: false }; } [Symbol.iterator]() { return this; } } for (const v of new It) { const q: string = v; }', [NOT_ASSIGNABLE('number', 'string')]],
	['mixin constructor intersection', 'declare class M { constructor(...args: any[]); p: number } declare class C { constructor(s: string); a: number } declare const X: typeof M & typeof C; const x = new X("a"); const q: string = x.p; const r: string = x.a;', [NOT_ASSIGNABLE('number', 'string'), NOT_ASSIGNABLE('number', 'string')]],
	['construct signature merged onto a class', 'interface D { x: number } class C { m() {} } interface C { new (): D } declare const y: C; const z = new y(); const q: string = z.x;', [NOT_ASSIGNABLE('number', 'string')]],
	['template literal key',			'const o = { ab: 1 }; const q: string = o[`ab`];',												[NOT_ASSIGNABLE('number', 'string')]],
	['literal-union key',				'interface O { a: number[]; b: string[]; c: boolean } declare const o: O; declare const k: boolean; const q: string = o[k ? "a" : "b"].length; o[k ? "a" : "d"]; o["d"];',	[NOT_ASSIGNABLE('number', 'string'), `Property 'd' does not exist on type 'O'`]],
	['a named index narrows until assigned', 'declare const xs: (string | undefined)[]; function f(i: number, c: boolean) { if (xs[i]) { const a: string = xs[i]; if (c) i++; const b: string = xs[i]; } }', [NOT_ASSIGNABLE('string | undefined', 'string')]],
	['a non-null assertion is the same path', 'interface S { r?: string } declare function take(s: string): void; function f(s0: S | undefined) { let s = s0; const g = () => { if (s!.r) take(s!.r); const n: number = s!.r; }; s = undefined; }', [NOT_ASSIGNABLE('string | undefined', 'number')]],
	['assigning a base forgets its paths', 'declare let o: { a?: string } | { a?: number }; function f() { if (typeof o.a === "string") { o = { a: 1 }; const s: string = o.a; } }', [NOT_ASSIGNABLE('number', 'string')]],
	['infer in a template literal type', 'type Split<S extends string> = S extends `${infer H}.${infer R}` ? [H, ...Split<R>] : [S]; declare function z(x: ["a", "b", "c"]): void; declare const s: Split<"a.b.c">; z(s); declare const t: Split<"a.b">; z(t);', [`Argument of type '["a", "b"]' is not assignable to parameter 'x: ["a", "b", "c"]'`]],
	['contravariant infer candidates intersect', 'type U2I<U> = (U extends any ? (k: U) => void : never) extends (k: infer R) => void ? R : never; declare const u: U2I<{ a: 1 } | { b: 2 }>; declare function one(x: 1): void; one(u.a); one(u.b);', [`Argument of type '2' is not assignable to parameter 'x: 1'`]],
	['a tuple spread of a tuple is its elements', 'type Split<S extends string> = S extends `${infer H}.${infer R}` ? [H, ...Split<R>] : [S]; type Nest<P extends readonly string[], F> = P extends readonly [infer O extends string] ? { [K in O]: F } : P extends readonly [infer H extends string, ...infer R extends string[]] ? { [K in H]: Nest<R, F> } : never; declare const t: Nest<Split<"f.add">, 1> & Nest<Split<"f.sub">, 2>; declare function one(x: 1): void; one(t.f.add); one(t.f.sub);', [`Argument of type '2' is not assignable to parameter 'x: 1'`]],
	['keyof a remapped mapped type', 'type Invert<T> = { [K in keyof T as T[K] & PropertyKey]: K }; type I = Invert<{ 69: "eqz"; 70: "eq" }>; declare function z(x: "eqz" | "eq"): void; declare const k: keyof I; z(k); declare function n(x: 70): void; n(({} as I).eqz);', [`Argument of type '69' is not assignable to parameter 'x: 70'`]],
	['a remapped key over keyof T keeps literal keys beside an index', 'type O = { [k: string]: any, str: any }; type R = { [K in keyof O as {} extends Record<K, any> ? never : K]: any }; declare let x: keyof R; x = "str"; x = "other";', [NOT_ASSIGNABLE('"other"', '"str"')]],
	['a remapped keyof over a generic stays deferred', 'type Inv<T> = { [K in keyof T as T[K] & PropertyKey]: K }; function keysOf<Tbl>(t: Tbl) { const inv = t as unknown as Inv<Tbl>; return Object.keys(inv) as (keyof typeof inv)[]; } declare function z(x: "a"[]): void; z(keysOf({ 1: "a" } as const)); function f<T>() { type R = { [K in keyof ({ s: 1 } & T) as {} extends Record<K, any> ? never : K]: any }; let x: keyof R = "s"; }', []],
	['an optional tuple element accepts undefined', 'declare const g: (...args: [a?: { o: number }]) => void; function h(a?: { o: number }) { g(a); g(); }', []],
	['a cast naming a local is its type in an inferred return', 'declare function keysOf<T>(o: T): (keyof T)[]; function f<T extends object>(t: T) { const inv = t; return Object.keys(inv) as (keyof typeof inv)[]; } const k: "a"[] = f({ a: 1 }); const j: "b"[] = f({ a: 1 });', [`is not assignable to type '"b"[]'`]],
	['a function returning itself', 'interface I { (i: I): I } function f(p: I) { return f; } declare const i: I; f(i); f(f(i));', []],
	['a construct signature must be matched', 'interface T { new (x: number): void } interface S2 { (x: string): void } declare const s2: S2; declare let t: T; t = s2; type N<X> = X extends { new (s: any): infer R } ? R : "no"; declare function z(x: "Z"): void; declare const n: N<{ a: 1 }>; z(n);', [NOT_ASSIGNABLE('S2', 'T'), `Argument of type '"no"' is not assignable to parameter 'x: "Z"'`]],
	['overloaded signatures infer pairwise from the last', 'function foo5<T>(cb: { new(x: T): string; new(x: number): T }) { return cb; } declare const a: { new (x: boolean): string; new (x: number): boolean }; const r = foo5(a);', []],
	['a unary of a maybe-bigint is either', 'declare const x: number | bigint; const q: string = -x;', [NOT_ASSIGNABLE('number | bigint', 'string')]],
	['template literal type',			'const t = `ab`; const q: "ab" = t; function f(r: "ac") {} f(`ab`);',								[`Argument of type '"ab"' is not assignable to parameter 'r: "ac"'`]],
	['template literal `in`',			'declare const o: { test: string } | {}; if (`test` in o) { const q: number = o.test; }',		[NOT_ASSIGNABLE('string', 'number')]],
	['iterator through this["entries"]', 'class M { *entries(): Generator<[string, number], void> { yield ["a", 1]; } declare [Symbol.iterator]: this["entries"]; } for (const [k, v] of new M) { const q: string = v; }', [NOT_ASSIGNABLE('number', 'string')]],
	['computed method in a literal','function* g(): IterableIterator<(x: string) => number> { yield* { *[Symbol.iterator]() { yield (x: string) => x.length; } }; }', []],

	['a declared generator types yield',	'function* g(): Generator<number, string, boolean> { const v = yield 1; const w: number = v; yield "x"; return 1; }', [NOT_ASSIGNABLE('boolean', 'number'), `Type '"x"' is not assignable to the yielded type 'number'`, "Type '1' is not assignable to declared return type 'string'"]],
	['a declared return is never replaced', 'function f(): any { return 1; } const q: string = f();',								[]],

	// unannotated class members infer their return types at every use
	['method and getter returns',	'class B { m() { return 1; } get g() { return "s"; } } const x: string = new B().m(); const y: number = new B().g;', [NOT_ASSIGNABLE('number', 'string'), NOT_ASSIGNABLE('string', 'number')]],
	// a get/set pair is one property whose write type may be wider than its read type (TS 5.1)
	['an interface get/set pair reads its getter', 'interface I { get x(): string; set x(v: string); } declare const i: I; const q: number = i.x;', [NOT_ASSIGNABLE('string', 'number')]],
	['an interface setter accepts its own type', 'interface I { get x(): string; set x(v: string | number); } declare const i: I; i.x = 5; i.x = true;', ["Type 'true' is not assignable to type 'string | number'"]],
	['a class setter accepts wider, the getter still reads', 'class C { get x(): string { return ""; } set x(v: string | number) {} } const c = new C(); c.x = 5; const q: number = c.x;', [NOT_ASSIGNABLE('string', 'number')]],
	['an object literal accessor pair', 'const o = { get x(): string { return ""; }, set x(v: string | number) {} }; o.x = 5; const q: number = o.x;', [NOT_ASSIGNABLE('string', 'number')]],
	['a write narrows only within the getter type', 'declare const t: { get bar(): string | number; set bar(s: string | number | boolean) }; t.bar = 42; const n: number = t.bar; t.bar = false; const o: number = t.bar;', [NOT_ASSIGNABLE('string | number', 'number')]],
	['a literal key writes through the setter', 'interface Foo { get k(): Set<string>; set k(v: Iterable<string>); } declare const foo: Foo; foo["k"] = ["foo"];', []],
	['an object literal lone setter', 'const o = { set x(v: number) {} }; o.x = "s";', ["is not assignable to type 'number'"]],
	['static accessors see the constructor', 'class A { static #n: number; static get g(): string { return this.#n; } static set s(v: number) { const q: string = this.#n; } }', ["is not assignable to declared return type 'string'", NOT_ASSIGNABLE('number', 'string')]],
	['fluent this',					'class A { foo() { return this; } } class B extends A { bar() { return this; } } declare const b: B; const q: number = b.foo().bar();', ["Type 'B' is not assignable to type 'number'"]],
	['a guard drops a nullish member', 'class A { a = 1 } class B { b = 2 } declare const x: A | B | undefined; if (x instanceof A) { const q: number = x; }', [NOT_ASSIGNABLE('A', 'number')]],
	['a guard keeps a narrower type', 'class A { a = 1; } class C extends A { c = ""; } declare function isA(x: any): x is A; declare const s: C; if (isA(s)) { const q: number = s.c; }', [NOT_ASSIGNABLE('string', 'number')]],
	['a guard narrows unknown', 'declare const u: unknown; if (Array.isArray(u)) { const q: string = u; }', [NOT_ASSIGNABLE('any[]', 'string')]],
	['a guard narrows any, except to Function', 'declare const a: any; declare function isF(x: any): x is Function; if (Array.isArray(a)) { const q: string = a; } if (isF(a)) { const r: string = a; }', [NOT_ASSIGNABLE('any[]', 'string')]],
	['instanceof a shadowing any value names no class', 'function f(t: any, Promise: any) { if (t instanceof Promise) t.__then(); }', []],
	['a guard keeps narrower members', 'class A { a = 1; } class B { b = 1; } class C extends A { c = ""; } declare function isA(x: any): x is A; declare const u: C | B; if (isA(u)) { const q: number = u.c; }', [NOT_ASSIGNABLE('string', 'number')]],
	['a nested function has its own this', 'class Foo { x: number; bar() { function inner() { const q: string = this.x; } const g = function () { const r: string = this.x; }; } }', []],
	['an annotated sibling parameter infers', 'class C { test: string } class D extends C { test2: number } declare function test<T extends C>(a: (t: T, t1: T) => void): T; test((t1: D, t2) => { const q: string = t2.test2; });', [NOT_ASSIGNABLE('number', 'string')]],
	['super reaches a generic base', 'declare class A<T> { constructor(x: T); m(): T; } class B extends A<string> { constructor() { super("s"); } n() { const q: number = super.m(); } }', [NOT_ASSIGNABLE('string', 'number')]],
	['super() fixes the base type args', 'class A<T> { constructor(x: T) {} } class B extends A<string> { constructor() { super(1); } }', ["Argument of type '1' is not assignable to parameter 'x: string'"]],
	['super reaches the base method', 'class A { m(): string { return ""; } } class B extends A { m(): number { return 1; } n() { const q: number = super.m(); } }', [NOT_ASSIGNABLE('string', 'number')]],
	['super.m() has the derived this', 'class A { self(): this { return this; } } class B extends A { b = 1; n() { const q: number = super.self(); } }', [NOT_ASSIGNABLE('this', 'number')]],
	['super() checks its arguments', 'class A { constructor(x: number) {} } class B extends A { constructor() { super("x"); } }', ["Argument of type '\"x\"' is not assignable to parameter 'x: number'"]],
	['super() accepts the base arguments', 'class A { constructor(x: number) {} } class B extends A { constructor() { super(1); } }', []],
	['static super reaches the base', 'class A { static s(): string { return ""; } } class B extends A { static t() { const q: number = super.s(); } }', [NOT_ASSIGNABLE('string', 'number')]],
	['static member returns its class', 'class A { static self = A; static make() { return A; } static me() { return this; } } const q: number = A.make();', [NOT_ASSIGNABLE('typeof A', 'number')]],

	// strictNullChecks off: null/undefined belong to every type, and inferred null/undefined widen to `any`
	['non-strict null is in every type', 'let x = null; x = 5; function f() { return null; } const s: string = f(); declare const o: { a?: number } | undefined; const n: number = o.a;', [], true],
	['non-strict: missing property still errs', 'type A = { a: string }; const x: A = 42;', ["Type 'number' is not assignable to type 'A'"], true],
	['a missing required property errs',	'const z: { a: string | undefined } = {};',												["Type '{}' is not assignable to type '{"]],

	// generic inference: candidates by polarity, TS's common supertype, parameters fixed as callbacks are typed
	['common supertype of candidates',	'function f<T>(y: T, x: T): T { return y; } interface A { a: number } interface B extends A { b: number } declare const a: A, b: B; const r: string = f(b, a);', [NOT_ASSIGNABLE('A', 'string')]],
	['literal candidates union',		'enum E { A, B, C } interface I<T extends E> { type: T } declare function foo<T extends E>(x: I<T>): T; declare const x: I<E.A | E.B> | I<E.C>; const r: string = foo(x);', ["is not assignable to type 'string'"]],
	['contravariant candidates',		'declare function f1<T>(a: (x: T) => void, b: (x: T) => void): T; declare function fo(x: Object): void; declare function fs(x: string): void; const r: number = f1(fo, fs);', [NOT_ASSIGNABLE('string', 'number')]],
	['instantiation expression rest',	'declare function g<T>(...args: ((x: T) => void)[]): T; const h = g<number>; h(x => { const s: string = x; });', [NOT_ASSIGNABLE('number', 'string')]],
	['callback context fixes',			'declare function f<T, U>(t: T, u: U, a: (u: U) => T, b: (t: T) => U): [T, U]; interface A { a: A } interface B extends A { b: any } declare const a: A, b: B; const d = f(a, b, u => u.b, t => t);', []],

	['superclass type arguments',		'declare class Base<P> { readonly props: Readonly<P>; } interface CP { ref?: () => void; } class X extends Base<CP> { m() { const a: number = this.props.ref; } }', ["is not assignable to type 'number'"]],
	['numeric index answers numbers only', 'declare const s: String; const p = s.push;',												["Property 'push' does not exist"]],

	// class references compare by their members; shadowing, tuple contexts and readonly are respected
	['unrelated classes',				'class A { a = 1; } class B { b = ""; } const x: A = new B();',							["Type 'B' is not assignable to type 'A'"]],
	['an array is not a number',		'const n: number = [1];',																["is not assignable to type 'number'"]],
	['a method type parameter shadows', 'class G<T> { foo<T>(t: T): T { return t; } } declare const g: G<string>; const r: number = g.foo(1);', []],
	['a union of tuples is a tuple context', "type TA = ['a', number]; type TB = ['b', string]; declare function f(c: TA | TB): void; f(['a', 5]); f(['b', 'x']);", []],
	['as const under a mutable context', 'const a = [1, 2] as const satisfies unknown[];',										[]],
	['readonly tuple into a mutable array', 'declare const r: readonly [number]; const m: number[] = r;',						["is not assignable to type 'number[]'"]],

	['a quoted type argument is opaque', "declare function g<A, B>(a: string): number; declare function h(x: number): void; h(g<number, '<'>('<')); const r: string = g<number, `>${'<'}`>('');", [NOT_ASSIGNABLE('number', 'string')]],
	['a tagged template is a call',	'declare function tag(s: TemplateStringsArray): number; declare function tag(s: TemplateStringsArray, n: number): string; const r: boolean = tag`x${1}`;', [NOT_ASSIGNABLE('string', 'boolean')]],
	['object literal candidates union', 'declare function f<T>(a: T, b: T): T; const r = f({ x: 1, z: 2 }, { x: 1, y: "" });',		[]],
	['primitive candidates do not',	'declare function f<T>(x: { bar: T; baz: T }): T; f({ bar: 1, baz: "" });',						["is not assignable to parameter"]],
	// A type parameter is opaque, as TS's: its constraint bounds what it IS; unconstrained it is `unknown` (`{}` without strictNullChecks).
	['a type parameter is opaque',		'function g<V>(v: V, vs: V[]): V { const a: string = v; const b: V = vs[0]; const c: unknown = v; return 1; } class B<V> { items: V[] = []; f(): void { const q: string = this.items; } }', [NOT_ASSIGNABLE('V', 'string'), "declared return type 'V'", NOT_ASSIGNABLE('V[]', 'string')]],
	['unknown is a top type only as a target', 'declare const u: unknown; const n: number = u; const o: object = u; const k: unknown = 5;', [NOT_ASSIGNABLE('unknown', 'number'), NOT_ASSIGNABLE('unknown', 'object')]],
	['typeof narrows unknown and type parameters', 'function f(v: unknown) { if (typeof v === "string") { const a: number = v; } if (v) { const b: number = v; } } function g<T extends string | undefined>(t: T) { const s: string = t!; if (typeof t !== "undefined") { const r: string = t; } }', [NOT_ASSIGNABLE('string', 'number'), NOT_ASSIGNABLE('{}', 'number')]],
	['trivial conditionals over a parameter simplify', 'function f<T>(x: Extract<T, T>, y: Exclude<T, never>): T { const a: T = x; x = a; return y; } function g<T extends 1 | 2>(a: T): (1 | 2) & T { return a; } const h = <P>(p: Pick<P, keyof P>): P => p; const k = <P>(p: Partial<P>): P => p;', ["declared return type 'P'"]],
	['generic signatures relate by instantiation', 'function f<T>(x: T): T { return x; } let r = <T>(x: T) => x; r = f; declare function h<R>(func: (x: number) => R): R; const z: string = h(f); declare function ta<A, B>(a?: A, b?: B): B; declare function ctx(...s: string[]): string; const sig: typeof ctx = ta;', [NOT_ASSIGNABLE('number', 'string')]],
	['a mixin class is also its base parameter', 'type Ctor = new (...args: any[]) => {}; function M<T extends Ctor>(base: T): T { return class extends base { m() {} }; }', []],
	['a bare union alternative takes only unmatched members', 'declare function one<U>(value: U | readonly U[]): U; function g<T>(value: readonly T[] | T) { const r: number = one(value); }', [NOT_ASSIGNABLE('T', 'number')]],
	['{} holds every non-nullish value', 'declare const o: object; const a: {} = o; const b: {} = 5; declare const u: unknown; const c: {} = u;', [NOT_ASSIGNABLE('unknown', '{}')]],
	['a computed key is checked by path', 'const it: Iterable<number> = [1]; const bad: Iterable<number> = { length: 1 };', ["not assignable to type 'Iterable<number>'"]],
	['typeof undefined is any without strictNullChecks', 'var x: typeof undefined; x = 1;', [], true],
	['a logical assignment is its binary', 'declare let r: any; const n = r.a ??= {}; n.b = 5; declare let s: string | undefined; const q: number = (s ??= "a");', [NOT_ASSIGNABLE('string', 'number')]],

	// equality narrows by any unit-typed operand, and enum members are types
	['enum member discriminant',		'enum Kind { A, B } interface Base { kind: Kind } interface A extends Base { kind: Kind.A; yar: number } interface B extends Base { kind: Kind.B; gar: number } declare const foo: A | B; switch (foo.kind) { case Kind.A: const myA: A = foo; break; case Kind.B: const myB: B = foo; }', []],
	['const-named unit narrows',		'declare const x: "a" | "b"; const k = "a"; if (x === k) { const q: "a" = x; }',		[]],
	['compared path narrows itself',	'enum E { A = 1, B = 2 } declare function never(v: never): never; function f(v: Partial<{ t: E.A } | { t: E.B }>) { if (v.t !== undefined) switch (v.t) { case E.A: break; case E.B: break; default: never(v.t); } }', []],
	// every merge point joins the flows reaching it: after a loop, a try, a switch, a labeled break (tsc agrees on each)
	['a loop body sees its own back edge', 'declare const c: boolean; let x: string | undefined; x = "a"; while (c) { const q: string = x; x = undefined; }', [NOT_ASSIGNABLE('string | undefined', 'string')]],
	['after a loop, its assignments hold', 'declare const c: boolean; let x: string | undefined; x = "a"; while (c) { x = undefined; } const q: string = x;', [NOT_ASSIGNABLE('string | undefined', 'string')]],
	['a do-while body runs at least once', 'declare const c: boolean; let x: string | undefined; x = "a"; do { x = undefined; } while (c); const q: string = x;', ['is not assignable']],
	['a for-of body may run', 'declare const xs: number[]; let s: string | undefined; s = "b"; for (const x of xs) { if (x) s = undefined; } const q: string = s;', ['is not assignable']],
	['a continue is a back edge', 'declare const c: boolean; let x: string | undefined; x = "a"; while (c) { if (c) continue; x = undefined; } const q: string = x;', ['is not assignable']],
	['a labeled break leaves both loops', 'declare const c: boolean; let x: string | undefined; x = "a"; out: while (c) { while (c) { x = undefined; break out; } } const q: string = x;', ['is not assignable']],
	['a break carries its flow out', 'declare const c: boolean; let n: string | undefined; for (;;) { n = "a"; if (c) break; } const q: string = n;', []],
	['a try body may be cut short', 'declare const c: boolean; let x: string | undefined; x = "a"; try { x = undefined; } catch {} const q: string = x;', ['is not assignable']],
	['a switch clause falls out', 'declare const c: number; let x: string | undefined; x = "a"; switch (c) { case 1: x = undefined; } const q: string = x;', ['is not assignable']],
	// a numeric `let`'s flow carries a range: a loop head widens to a machine limit, then its test bounds it again
	['a loop exit knows its counter', 'let i = 0; for (; i < 3; i++) {} let q = ""; q = i;', ["Type '3' is not assignable to type 'string'"]],
	['a countdown ends in range', 'let m = 10; while (m > 0) m -= 2; let q = ""; q = m;', ["Type 'number[-1..0] (int)' is not assignable"]],
	['++ never overflows its i32 (the user\'s rule)', 'declare const c: boolean; let k = 0; while (c) k++; let q = ""; q = k;', ["Type 'number[0..2147483647] (int)' is not assignable"]],
	['an alias chain deeper than one resolve budget', 'type A0 = { x: number }; type A1 = A0; type A2 = A1; type A3 = A2; type A4 = A3; type A5 = A4; type A6 = A5; type A7 = A6; type A8 = A7; type A9 = A8; type A10 = A9; type A11 = A10; type A12 = A11; declare const v: A12; const q: string = v.x;', [NOT_ASSIGNABLE('number', 'string')]],
	['a function\'s own arguments',	'function f() { const q: string = arguments; }',										[NOT_ASSIGNABLE('IArguments', 'string')]],
	// `var` is function-scoped: it binds in its body's scope, from any nested block, and a namespace body is its own
	['var after its loop',			'function f() { for (var i = 0; i < 3; i++) {} const q: string = i; }',					[NOT_ASSIGNABLE('number', 'string')]],
	['var for-in binding',			'function f(o: {a: number}) { for (var k in o) {} const q: number = k; }',				[NOT_ASSIGNABLE('string', 'number')]],
	['closure in the var\'s block',	'function f() { if (true) { var j = 0; const g = () => j; const q: string = g; } }',		[NOT_ASSIGNABLE('() => number', 'string')]],
	['var redeclared keeps its type', 'function f() { var r = 1; var r = r + 1; const q: string = r; }',					[NOT_ASSIGNABLE('number', 'string')]],
	['a namespace var stays inside', 'var x: string = ""; namespace M { export var x = 1; } const q: number = x;',			[NOT_ASSIGNABLE('string', 'number')]],
	// an i32 cannot hold -0, so a result that may be -0 is not an int: `-k` or `k * -2` with k possibly 0
	['-0 is not an int: negation',	'declare const c: boolean; let k = 0; while (c) k++; let q = ""; q = -k;',		["Type 'number[-2147483647..0]' is not assignable"]],
	['a nonzero negation is an int', 'declare const c: boolean; let k = 1; while (c) k++; let q = ""; q = -k;',	["Type 'number[-2147483647..-1] (int)' is not assignable"]],
	['-0 is not an int: product',	'declare const c: boolean; let k = 0; while (c) k++; let q = ""; q = k * -2;',	["Type 'number[-4294967294..0]' is not assignable"]],
	['a compound assignment narrows to its result', 'let x = 2; x *= 3; let q = ""; q = x;', ["Type '6' is not assignable"]],
	['++ on a string path is still an error', 'declare let e: { h: string }; e.h = "a"; e.h += 1; e.h++;', ["Operand of '++' must be numeric, got 'string'"]],
	['an assignment is judged by the declaration, not an undeclared name\'s flow', 'for (var i = 0; i < 10; i++) {} for (i = 0; i < 10; i++) {} i = 0;', []],
	['exhaustive switch narrows after',	'declare function assertNever(x: never): never; function f(x: 1 | 2) { switch (x) { case 1: return "a"; case 2: return "b"; } return assertNever(x); }', []],
	['switch that breaks does not',		'declare function assertNever(x: never): never; function f(x: 1 | 2) { switch (x) { case 1: break; case 2: return "b"; } return assertNever(x); }', ["Argument of type '1' is not assignable to parameter 'x: never'"]],
	['string enum members are strings', 'enum C { Y = "yes", N = "no" } function f(a: C.Y, b: C.Y | C.N) { const s: string = a + b; }', []],
	['const reads its initializer',		'declare enum E { ONE, TWO, THREE = "x" } const e: E = E.ONE; const x: E.ONE = e;',		[]],
	['typeof narrows object and aliases', 'type Basic = number | object | Function; declare function n(x: number): void; declare function fn(x: Function): void; function f(x: Basic) { switch (typeof x) { case "number": n(x); return; case "function": fn(x); return; } }', []],
	['typeof exclusions apply together', 'declare function assertNever(x: never): never; function f(x: number | object) { switch (typeof x) { case "number": return; case `function`: return; case "object": return; } assertNever(x); }', []],
	['a repeated case is unreachable',	'declare function assertNever(x: never): never; function f(x: string | number) { switch (typeof x) { case "string": return 1; case "number": return 2; case "number": return assertNever(x); } }', []],
	['discriminant values split',		'enum K { A = 1, B = 2 } type T = { kind: K.A, id?: number } | ({ kind: K.B } & ({ id?: undefined } | { id: number })); declare function take(t: T): void; function f(kind: K, id?: number) { take({ kind, id }); }', []],

	// an implementation signature is invisible to callers when overloads exist
	['overloads hide the implementation', 'class C { m(x: string): number; m(x: any) { return x; } } const r: string[] = ["a"].map(new C().m);', [NOT_ASSIGNABLE('number[]', 'string[]')]],
	['a truthy optional chain narrows its roots', 'declare const f: (() => boolean) | undefined, x: string[] | undefined; if (f?.()) { const g: () => boolean = f; } if (x?.[0]) { const n: string[] = x; }', []],
	['an exiting branch does not merge',	'declare const c: boolean; function f() { let y; if (c) y = "s"; else return; const q: number = y; }', [NOT_ASSIGNABLE('string', 'number')]],
	// overloads: a context-sensitive callback is untyped until a candidate fits, then fixed by it; the next is tried with it fixed
	['a callback fixed by the first fit',	'declare function foo(arg: (x: string) => string): string; declare function foo(arg: (x: string) => number): number; const r: boolean = foo(x => 1);', [NOT_ASSIGNABLE('number', 'boolean')]],
	['an alias is transparent to inference', 'type MP<T> = T | Promise<T>; declare function f<D>(m: (x: number) => MP<D>): D; const r = f(u => u as number | string); const q: boolean = r;', [NOT_ASSIGNABLE('number | string', 'boolean')]],
	['shared subtrees are walked once',		`declare function d<T>(x: T): { a: T; b: T }; declare function id<U>(u: U, f?: <V>(v: V) => V): U; const x = id(${'d('.repeat(40)}1${')'.repeat(40)}); const q: number = x.a.b;`, ["is not assignable to type 'number'"]],
	['an IIFE parameter with no argument is optional', '((a) => a)(); (({ x = 1 }) => x)(); (function (a, b: number) {})();', ['Expected 2 arguments, but got 0']],
	['any absorbs a union, unknown the rest', 'declare const a: unknown, b: string, c: any; const u = Math.random() > 0.5 ? a : b; const v = Math.random() > 0.5 ? b : c; const q: number = [u]; const p: number = [v];', ["Type 'unknown[]' is not assignable to type 'number'", "Type 'any[]' is not assignable to type 'number'"]],
	['a union of signatures is callable',	'declare const f: ((x: number) => string) | ((x: number) => number); const r: boolean = f(1); declare const g: ((a?: {x: number}, ...b: {x: number}[]) => void) | ((a?: {y: number}) => void); g({x: 0, y: 0}, {x: 0});', [NOT_ASSIGNABLE('string | number', 'boolean')]],
	['an any callee still checks its arguments', 'declare const k: any; const r = new k(); const q: number = r; k(() => { const s: string = 1; });', [NOT_ASSIGNABLE('number', 'string')]],
	['an assignment narrows as its target',	'declare function next(): string | null; let s; while ((s = next()) !== null) { const n: string = s; } let t: string | null; if (typeof (t = next()) === "string") { const w: string = t; }', []],
	['names never reach Object.prototype',	'declare const v: constructor; const n = v.solutionRead; declare const w: toString | number; const m = w.valueOf;', []],
	['a function type inside call type arguments', 'declare function g<T>(x?: T): T; const r: number = g<() => string>();', [NOT_ASSIGNABLE('() => string', 'number')]],
	['null stands aside for the supertype',	'declare function g<T>(a: T, b: T): T; const s: boolean = g(1, null); declare function f<U>(x: U[]): U; declare const b: boolean; const r = f(b ? [1] : [undefined]); const q: boolean = r;', [NOT_ASSIGNABLE('number | null', 'boolean'), NOT_ASSIGNABLE('number | undefined', 'boolean')]],
	['a compared path narrows from its precise type', 'declare const m: { type: "method" | "get" | "set" }; declare function acc(k: "get" | "set"): void; if (m.type === "get") acc(m.type); if (m.type === "get" || m.type === "set") acc(m.type);', []],
	['as const reaches every property',		'const b = { type: "v", a: [1, "x"] } as const; const q: { type: "w"; a: readonly [1, "x"] } = b; declare const d: { name: string }; const c = [d].map(x => ({ type: "v", ...x } as const)); const r: "v" = c[0].type;', ["Type '{\n  type: \"v\";"]],
	['a const is bound inside its own initializer', 'declare function pure(a: any, b: string, c: number): void; function f() { const pure = (x: number): boolean => x > 0 && pure(x - 1); const s: (n: number) => string = n => n ? s(n - 1) : ""; const q: number = s(2); }', [NOT_ASSIGNABLE('string', 'number')]],
	['as const takes mutability from its context', 'declare function fg<T>(more?: Partial<{ m: string[]; t: T }>): void; fg({ m: ["a"] } as const); const m: { args: number[] } = { args: [] } as const; declare const c: boolean; const o = { e: c ? [1] : [2] } as const; const e: number[] = o.e; declare function R<const T extends readonly unknown[]>(x: T): T; const s: boolean = R([1, "a"]);', [NOT_ASSIGNABLE('readonly [1, "a"]', 'boolean')]],
	['an overload trial types an argument in its candidate\'s context', 'type Rl<T> = { t: T }; declare function Rule<T, const R extends readonly unknown[]>(rhs: R, action: (v: R) => T): Rl<T>; type K = { key: string; modifiers?: string[] }; interface L<T> { push(item: T): number; push(...items: T[]): number } declare const list: L<Rl<K>>; list.push(Rule(["a"] as const, $ => ({ key: "x", modifiers: ["optional"] } as const)));', []],
	['a literal excludes what it cannot be',	'type V = "i32" | "f64" | "ref"; interface P { tp: string } declare const l: { type: V | P }; declare function temp(w: "i32" | "f64"): void; if (l.type === "i32" || l.type === "f64") temp(l.type);', []],
	['a union of tuples destructures by member', 'declare const u: readonly ["a", number] | readonly ["b", string]; const [k, v] = u; declare function ab(x: "a" | "b"): void; ab(k); declare function onlyA(x: "a"): void; onlyA(k); const r: boolean = v; for (const [a] of [["f64", 1], ["ref", "x"]] as const) { const z: boolean = a; }', ["Argument of type '\"a\" | \"b\"' is not assignable", NOT_ASSIGNABLE('number | string', 'boolean'), NOT_ASSIGNABLE('"f64" | "ref"', 'boolean')]],
	['a thrown end adds no undefined',		'const f = (b: boolean) => { if (b) return 1; throw new Error(); }; const q: string = f(true); function h(b: boolean) { if (b) return 1; } const t: string = h(true);', [NOT_ASSIGNABLE('number', 'string'), NOT_ASSIGNABLE('number | undefined', 'string')]],
	['an instantiated intersection reduces',	'declare function f<T, U>(a: T, b: U): { v: T & U }; const s = f<unknown, string>(1, ""); const q: boolean = s.v; const t = f<any, string>(1, ""); const r: boolean = t.v;', [NOT_ASSIGNABLE('string', 'boolean')]],
	['a class instance is never falsy',		'class Sc { a = 1 } declare const s: Sc | undefined; const m = s && "x"; const q: boolean = m;', [NOT_ASSIGNABLE('undefined | string', 'boolean')]],
	['an optional chain equal to a value narrows its roots', 'interface D { type: string } interface N { decl(k: string): D | undefined } declare const h: N | undefined; if (h?.decl("a")?.type === "c") { const n: N = h; } if (h?.decl("a")?.type !== "c") { const m: N = h; }', [NOT_ASSIGNABLE('N | undefined', 'N')]],
	['a literal index path narrows its reads',	'declare const args: [{ a: 1 }] | [number[]]; if (Array.isArray(args[0])) { const q: number[] = args[0]; }', []],
	['null is not an array',					'const c: number[] = null;', [NOT_ASSIGNABLE('null', 'number[]')]],
	["an array guard's false branch keeps null",	'declare const v: number | null | RegExp | string[]; if (!Array.isArray(v) && typeof v === "object") { const q: RegExp = v; }', [NOT_ASSIGNABLE('null | RegExp', 'RegExp')]],
	['a spread of an interface that extends another keeps its shape',	'interface B { b: number } interface D extends B { d: number } declare const d: D; const o = { ...d, e: 1 }; const q: string = o.b;', [NOT_ASSIGNABLE('number', 'string')]],
	['an assignment target is its declared type', 'let x: { o: boolean } = { o: false }; if (x["o"] === false) { x["o"] = true; } const y: [number, number] = [0, 0]; if (y[0] === 0) { y[0] = -1; }', []],
	// literal freshness: only a literal written as an expression widens (TS's fresh vs regular literal types)
	['a declared literal stays literal',	'declare const c: "this"; const a = [c]; const q: boolean = a; declare const k: { kind: "a" | "b" }; let s = k.kind; s = "c";', [NOT_ASSIGNABLE('"this"[]', 'boolean'), "Type '\"c\"' is not assignable to type '\"a\" | \"b\"'"]],
	['a fresh literal widens in either union order', 'declare function t(): "void" | "x" | undefined; let r1 = Math.random() ? t() : "void"; const q1: boolean = r1; let r2 = Math.random() ? "void" : t(); const q2: boolean = r2; const e = ""; let z = e; z = "other";', [NOT_ASSIGNABLE('string | undefined', 'boolean'), NOT_ASSIGNABLE('string | undefined', 'boolean')]],
	['a disjunction infers a type predicate', 'type U = { type: "this" } | { type: "fn"; x: 1 } | { type: "ctor"; x: 2 }; declare function take(s: { x: 1 | 2 }): void; declare const xs: U[]; const f = xs.find(p => p.type === "fn" || p.type === "ctor"); if (f) take(f); const g = xs.filter(p => p.type === "fn" || p.type === "ctor"); take(g[0]);', []],
	['inference picks a supertype by the real relation', 'declare function f3<T>(obj: T, f2: (f: (x: T) => void) => void): T; declare function fx(f: (x: "def") => void): void; const x3 = f3("abc", fx); const q: boolean = x3;', [NOT_ASSIGNABLE('string', 'boolean')]],
	// TS's control-flow containers: a function declaration or class declaration member sees declared types; closures and class expressions carry narrowings
	['a function declaration starts from declared types', 'interface R { ref: string } type W = "a" | R; const C: W = { ref: "x" }; function fd() { const a: R = C; } const fe = function () { const b: R = C; }; const ar = () => { const c: R = C; };', [NOT_ASSIGNABLE('"a" | R', 'R')]],
	['a class declaration\'s members start from declared types', 'interface R { ref: string } type W = "a" | R; const C: W = { ref: "x" }; class CD { p = (() => { const a: R = C; })(); } const CE = class { m() { const b: R = C; } };', [NOT_ASSIGNABLE('"a" | R', 'R')]],
	['a narrowed parameter does not reach a nested function declaration', 'function outer(q: string | undefined) { if (q) { function f7() { const s: string = q; } const a6 = () => { const t: string = q; }; } }', [NOT_ASSIGNABLE('string | undefined', 'string')]],
	// TS's intersection normalization (getIntersectionType) -- see `reduceIntersection`
	['NonNullable of a union narrows like the union', 'type G = { type: "a"; x: 1 } | { type: "b"; y: 2 }; declare function takeA(a: { x: 1 }): void; declare function takeB(b: { y: 2 }): void; declare const n: NonNullable<G | undefined>; if (n.type === "a") takeA(n); else takeB(n); const g: G = n;', []],
	['an intersection of type parameters relates by its constraint', 'type A = 1 | 2; type B = 2 | 3; function f2<T extends A, U extends B>(ab: T & U): (A | B) & T & U { return ab; }', []],
	['a function satisfies an interface extending Function', 'interface IResultCallback extends Function {} declare function fn(cb: IResultCallback): void; fn((a: number, b: number) => true);', []],
	['a phantom parameter infers nothing from its intersection with never', 'type AT<P> = string & { hack?: P & never }; type H<S, P> = P extends void ? (s: S) => S : (s: S, p: P) => S; declare function h<S, P>(a: AT<P>, handler: H<S, P>): void; declare const act: AT<number>; h<{ d: string }, number>(act, (state, _p) => state);', []],
	['a deferred conditional part is not dropped as unknown', 'type Foo<K> = K extends unknown ? { a: number } : unknown; const mk = <K,>(x: K): Foo<K> & { x: K } => { return { a: 1, x: x }; };', []],
	['an optional property\'s indexed access includes undefined', 'interface K { a: boolean } class S { kind?: K; parent?: S; enclosing(): S["kind"] { return this.kind ?? this.parent?.enclosing(); } } declare const s: S["kind"]; const q: boolean = s;', [NOT_ASSIGNABLE('K | undefined', 'boolean')]],
	['a construct-only value is not callable without new', 'class C { x = 1 } C(); interface CtorOnly { new (): C } declare const co: CtorOnly; co(); declare function f(): void; new f();', ["is not callable without 'new'", "is not callable without 'new'"]],
	['reduce with and without a seed',		'const r: string = [1, 2].reduce((a, v) => a + v, ""); const s: boolean = [1, 2].reduce((a, v) => a + v);', [NOT_ASSIGNABLE('number', 'boolean')]],
	['functions have Function members',		'function f(a: number) {} f.call(null, 1); const n: string = f.length;',					[NOT_ASSIGNABLE('number', 'string')]],
	['an expando assignment declares, not narrows', 'const E = function () {}; E.prop = { x: 2 }; E.prop = { y: "" }; const n = E.prop.x || 0;', []],
	// TS narrows a discriminant compared with a value typed as a union of literals, on the matching branch only.
	['a discriminant compared with a literal-union value narrows', 'type A = { type: "a"; x: 1 } | { type: "b"; y: 2 } | { type: "c"; z: 3 }; function f(m: A, k: "a" | "b") { if (m.type === k) { const n: { type: "a"; x: 1 } | { type: "b"; y: 2 } = m; } }', []],
	['a literal-union comparand does not narrow the other branch', 'type A = { type: "a"; x: 1 } | { type: "b"; y: 2 } | { type: "c"; z: 3 }; function f(m: A, k: "a" | "b") { if (m.type !== k) { const o: { type: "c"; z: 3 } = m; } }', ['is not assignable']],
	// A guard's false branch drops only members ASSIGNABLE to the guarded type: `R` (its `T` defaulted to `string`) is not an
	// `R<'never'>`, so it stays. Dropping it narrowed `src.type === 'ref'` to `never` (type-utils.ts `isAssignable`'s `recurse`).
	['a guard with a narrower type argument keeps a defaulted member', 'interface R<T extends string = string> { type: "ref"; name: T } interface L { type: "lit" } type Ty = R | L; declare function isRef<T extends string>(t: Ty, name: T): t is R<T>; function f(src: Ty) { if (isRef(src, "never")) return; const l: L = src; }', ['is not assignable']],
	['a primitive-constrained type parameter infers the literal', 'declare function lit<T extends string>(x: T): T; const a: "a" = lit("a");', []],
	// TS 5.5 infers a type predicate only when the function is true exactly when the parameter has that type. `isTop` is false for
	// most `R`s, so its false branch must not exclude `R` (type-utils.ts `isAny`, which left `src.type === 'ref'` as `never`).
	['an inferred predicate needs its false branch to be exact', 'interface R { type: "ref"; name: string } interface L { type: "lit" } type Ty = R | L; function isTop(t: Ty) { return t.type === "ref" && t.name === "any"; } function f(src: Ty) { if (isTop(src)) return; const l: L = src; }', ['is not assignable']],
	// TS's arity rule: a source needing more arguments than the target passes is not assignable (towasm's `staticGuard` folded
	// `has0args(f2)` to true on it). Optional, defaulted and trailing `void` parameters, and a rest target, are not needed.
	['a function needing more arguments than the target passes is not assignable', 'const f2 = (a: number, b: number) => a + b; const g: () => number = f2;', ['is not assignable']],
	['optional, defaulted, void and rest parameters are not needed arguments', 'const f = (a: number, b?: number, c = 1) => a; const g: (a: number) => number = f; const h: (...xs: number[]) => number = (a: number, b: number) => a; declare const r: (v: void) => void; const p: () => void = r;', []],
	// TS's read of a tuple position: an optional element, or a union member too short for it, reads `undefined` too (towasm's
	// bounds-checked read relies on it); a position a rest spread covers reads the spread's element, with no error.
	['a union of tuples read past a shorter member is possibly undefined', 'function f(...args: [number] | [number, number]) { const q: number = args[1]; }', ['is not assignable']],
	['an overload implementation\'s own type parameters are its body\'s', 'function q<T extends object>(s: number, spec: T): number; function q<T extends object>(s: string, spec: T): string; function q<T extends object>(s: any, spec: T): any { const n: string = Object.entries(spec); return 0; }', ["'[string, any][]' is not assignable"]],
	['a literal in a primitive-constrained type parameter\'s array context stays literal', 'declare function s1<K extends string>(keys: K[]): K; function f2(x: number) {} f2(s1(["image"]));', ['\'"image"\' is not assignable']],
	['an interface has no implicit index signature', 'interface Rd { get(): number } declare const r: Rd; const x: { [s: string]: unknown } = r;', ['is not assignable']],
	['a type literal has an implicit index signature, and any non-primitive fits a string index of any', 'interface Rd { get(): number } type L = { get(): number }; declare const r: Rd; declare const l: L; const y: { [s: string]: unknown } = l; const z: Record<string, any> = r;', []],
	['an asserted function\'s parameters are typed through local aliases expanded', 'function f<T>(v: T) { type R = T[]; return ((x) => x.length) as (x: R) => number; } const g = f(1); function h(s: string) {} h(g);', ['is not assignable']],
	['a union of generic methods with identical type parameters is callable', 'class A { view<V>(t: V, n: number): number { return n; } } class B { view<V>(t: V, n: number): string { return ""; } } function h(s: A | B) { const r: boolean = s.view(1, 2); }', ['is not assignable']],
	['Awaited unwraps nested promises', 'declare const p: Promise<Promise<number>>; function f(s: string) {} f(0 as any as Awaited<typeof p>);', ['is not assignable']],
	['undefined is assignable to no class under strict null checks', 'function f(a: number[]) {} f(undefined); type C = undefined extends number[] ? 1 : 2; const c: 2 = 1 as C;', ['is not assignable']],
	['a local type alias in an asserted result takes the caller\'s type arguments', 'function opt<T>(v: T) { type R = T | undefined; return ((x: number) => v) as (x: number) => R; } const f = opt(1); const n: string = f(0);', ['is not assignable']],
	['a remapped key that is no literal is an index signature', 'type Invert<T> = { [K in keyof T as T[K] & PropertyKey]: K }; declare const I: Invert<{ a: number; b: number }>; const z: number = I[1];', ['is not assignable']],
	['a signed number is a literal in a const context', 'const S = { i8: -8 } as const; function f(a: -9) {} f(S.i8);', ['is not assignable']],
	['several call signatures contextually type a parameter as their union', 'class A { a = 1 } class B { b = 2 } type G = ((s: A) => number) & ((s: B) => string); const g: G = s => { const t: number = s; return 1 as any; };', ['is not assignable']],
	['a callable interface contextually types a parameter', 'class A { a = 1 } interface C { (s: A): number } const k: C = s => { const t: number = s; return 1; };', ['is not assignable']],
	['an asserted function takes the assertion as its context', 'class A { a = 1 } const h = (s => { const t: number = s; return 1; }) as (s: A) => number;', ['is not assignable']],
	['a string indexed by a number reads its index signature', 'function g(t: string, n: number) { const a: number = t[n]; let i = 0; i++; const b: number = t[i]; }', ['is not assignable', 'is not assignable']],
	['a type predicate returns a boolean', 'function f(x: any): x is string { return 1; } function g(x: any): x is string { return x.length; }', ['is not assignable']],
	['a function type part seals its intersection: a member neither part declares is missing', 'declare const f: ((n: number) => void) & { load: number }; const i: { eq: string } = f;', ['is not assignable']],
	['an optional tuple element reads as possibly undefined', 'function g(t: [number, string?]) { const r: string = t[1]; }', ['is not assignable']],
	['a rest tuple position reads its element type', 'function h(t: [number, ...string[]]) { const s: string = t[3]; const n: number = t[0]; }', []],
	// TS's `T[number]`: a computed index reads any position, an optional one contributing `undefined` too.
	['a tuple indexed by a computed number reads any position', 'declare const i: number; const t = [1, "a"] as const; const q: boolean = t[i];', ['is not assignable']],
	['a tuple indexed by a computed number includes an optional position', 'declare function f(t: [number, string?], i: number): void; const g = (t: [number, string?], i: number) => { const q: number = t[i]; };', ['is not assignable']],
	// TS narrows at an assignment wherever it sits, so a branch that assigns inside a call argument still settles the type after it.
	['an assignment nested in a call argument narrows after the branch', 'interface B { v: number } declare const m: Map<string, B>; function f(k: string): B { let b = m.get(k); if (!b) { m.set(k, b = { v: 1 }); } return b; }', []],
	// TS instantiates a type parameter's default with the arguments already chosen, so one naming an earlier parameter resolves.
	['a type parameter default naming an earlier one is instantiated with it', 'interface C<E, A = E> { c: E; args: A[] } declare const x: C<number>; const q: boolean = x.args;', ['number[]']],
	// A generic argument infers through its base signature (TS's `getBaseSignature`), or its own bound `T` escapes into the result.
	// Arguments are typed in order, each against its parameter under what the arguments before it inferred -- or the explicit
	// type arguments -- so an inner generic call can infer from that context (walker.ts's `mapObject(t, { ps: mapArray(p => ...) })`).
	['an argument is typed against what the earlier arguments inferred', 'declare function mapArray<T>(map: (x: T) => T | undefined): (x: readonly T[]) => T[] | undefined; interface Pn { n: number } interface Q { ps: Pn[] } declare const q: Q; declare function withPlain<N>(node: N, fields: {[K in keyof N]?: (x: N[K]) => N[K] | undefined}): N; const b = withPlain(q, { ps: mapArray(p => p.nope) });', ["Property 'nope' does not exist"]],
	['an argument is typed against the explicit type arguments', 'declare function mapArray<T>(map: (x: T) => T | undefined): (x: readonly T[]) => T[] | undefined; interface Pn { n: number } interface Q { ps: Pn[] } declare const q: Q; declare function withPlain<N>(node: N, fields: {[K in keyof N]?: (x: N[K]) => N[K] | undefined}): N; const b = withPlain<Q>(q, { ps: mapArray(p => p.nope) });', ["Property 'nope' does not exist"]],
	// A guard narrows a union by TS's subtype relation, where `any` is below nothing but itself: `x is any[]` keeps `string[]`.
	['a guard to any[] keeps the union member that is an array', 'declare const v: number | string[]; if (Array.isArray(v)) { const q: number = v; }', [NOT_ASSIGNABLE('string[]', 'number')]],
	// ...and the same relation picks inference's common supertype: an `any` candidate makes it `any`, not the other candidate.
	['an any candidate makes the inferred type any', 'declare function f<T>(a: T, b: T): T; declare const x: any; const q: string = f(x, 1);', []],
	// Callback parameters are bivariant, TS's weakest rule: a pair unrelated in both directions is still no fit.
	['callback parameters unrelated both ways do not fit', 'interface A { a: number } interface B { b: number } declare function srt(f: (x: A) => number): void; declare function byB(x: B): number; srt(byB);', ["Argument of type '(x: B) => number'"]],
	// A literal against a structural target boxes as its primitive does, so a literal-typed value is an `Object` as `string` is.
	['a literal-typed value satisfies Object', 'declare const s: "def"; const o: Object = s; declare function fo(x: Object): void; const d: (x: "def") => void = fo;', []],
	// TS's isAritySmaller: an overload whose callback takes fewer parameters than the literal requires gives it no context.
	['a too-short overload does not type a callback', 'interface O { (h1: (a: string) => void): void; (h2: (a: number, b: number) => void): void; } declare const use: O; use((req, res) => { const q: string = req; });', [NOT_ASSIGNABLE('number', 'string')]],
	// A written `undefined`, or a discriminant the literal leaves out, discriminates a union context as TS does.
	['an undefined or omitted discriminant picks the optional member', 'type DT = { disc: true; cb: (x: string) => void }; type DF = { disc?: false; cb: (x: number) => void }; declare function f(o: DT | DF): void; f({ disc: undefined, cb: n => { const q: string = n; } }); f({ cb: n => { const q: string = n; } });', [NOT_ASSIGNABLE('number', 'string'), NOT_ASSIGNABLE('number', 'string')]],
	// A property's truthiness narrows the union holding it (TS's discriminant rule): past `if (c.errors) return`, only the member
	// whose `errors` can be falsy is left, so `coerced` is no longer possibly undefined.
	['a property truthiness test narrows the union holding it', "interface E { e: number } type C = { errors: ReadonlyArray<E>; coerced?: never } | { coerced: { [v: string]: unknown }; errors?: never }; declare const c: C; function g(): { vv: { [v: string]: unknown } } | undefined { if (c.errors) return undefined; const k: number = c.coerced; return { vv: c.coerced }; }", ["unknown\n}' is not assignable to type 'number'"]],
	// A read off a union is each member's read: one member's optional property makes it possibly undefined.
	['an optional property read through a union includes undefined', "interface C { n: number; s?: string } interface D { m: string; s?: string } declare const u: C | D; const q: string = u.s;", [NOT_ASSIGNABLE('string | undefined', 'string')]],
	// A spread of a union distributes, as TS's getSpreadType does: the literal is one shape per member, not an unknowable `any`.
	['a spread of a union is the union of each spread', "interface A { type: 'a'; x: number } interface B { type: 'b'; y: string } declare const u: A | B; const r = { ...u, z: 1 }; const s: number = r;", ['z: number\n} | {']],
	// A mapped type's key binds only inside it: `Partial`'s own `[P in keyof T]` must not capture a caller's type named `P`.
	['a mapped type key does not capture a same-named type substituted into it', 'interface P { n: number } declare const a: Partial<{ ps: P[] }>; const q: string = a.ps;', [NOT_ASSIGNABLE('P[] | undefined', 'string')]],
	// An uncontextual `[]` is `never[]`, which a union drops; an auto-typed declaration or assignment still evolves (`any[]`).
	['an empty array arm of a conditional takes the other arm', 'declare const c: boolean; declare const xs: { n: number }[]; const r = c ? xs : []; const q: string = r.map(x => x.n);', [NOT_ASSIGNABLE('number[]', 'string')]],
	['an empty array declaration or assignment evolves', 'let a = []; a.push(1); let b; (b = [], b).push(5);', []],
	// `in`'s false branch drops only a member declaring the key as required: an index signature or an optional member may lack it.
	['a false `in` keeps an index signature or optional member', "const r: { [x: string]: number } = {}; declare const o: { k?: string }; if (!('k' in r) && !('k' in o)) { const q: string = r.k; const p: number = o.k; }",
		[NOT_ASSIGNABLE('number', 'string'), NOT_ASSIGNABLE('string | undefined', 'number')]],
	// `new Promise(executor)` infers `T` only from where it is going, as TS does: the executor's `resolve` calls do not pin it.
	['an uncontextual new Promise is Promise<unknown>', "const p = new Promise(r => r(5)); const q: Promise<number> = p; const c: Promise<number> = new Promise(r => r(5)); const s: Promise<string> = new Promise<number>(r => r(5));",
		[NOT_ASSIGNABLE('Promise<unknown>', 'Promise<number>'), NOT_ASSIGNABLE('Promise<number>', 'Promise<string>')]],
	// `instanceof` narrows to the class's prototype type: a generic one's arguments are `any`.
	['instanceof a generic class narrows to its prototype type', 'declare const x: unknown; if (x instanceof Map) { const q: string = x; }', [NOT_ASSIGNABLE('Map<any, any>', 'string')]],
	// `unknown` is a top type only as a target.
	['unknown is assignable only to a top type', 'class C { x = 1; } declare const u: unknown; const p: C = u; const r: unknown = u; const s: any = u;', [NOT_ASSIGNABLE('unknown', 'C')]],
	// An async function's returned value, and an `await` operand, are typed against the value or a promise of it (TS's contextual type).
	['an async return or await operand is contextually a value or a promise of it', "async function f(): Promise<number> { return new Promise(r => r(1)); } async function g(): Promise<number> { const n: number = await new Promise(r => r(2)); return new Promise(r => r('a')); }",
		["Argument of type '\"a\"' is not assignable"]],
	// TS's getMinArgumentCount: a trailing parameter accepting `void` may be omitted.
	['a trailing void parameter may be omitted', 'declare function f(x: void | PromiseLike<void>): void; f(); const p = new Promise<void>(r => r()); declare function h(x: number): void; h();', ['Expected 1 arguments, but got 0']],
	// A type parameter's value narrowed by a guard it does not relate to directly is both (`T & C`), as TS narrows it.
	['instanceof narrows a type-parameter value to an intersection', "class C { prop = ''; } function f<T>(x: T) { if (x instanceof C) { const v1: T = x; const v2: C = x; const n: number = x.prop; } }", [NOT_ASSIGNABLE('string', 'number')]],
	// `yield*`'s operand is contextually a generator of the function's Y and N, returning what the `yield*` is expected to evaluate to.
	['yield* gives its operand a generator context', 'declare const g: <T, U, V>() => Generator<T, U, V>; function* f(): Generator<string, void, unknown> { const x1 = yield* g(); const x2: number = yield* g(); }', []],
	// `NoInfer<T>` is `T`, except that inference skips it.
	['NoInfer is its argument, skipped by inference', "declare function f<T>(a: T, b: NoInfer<T>): T; f(1, 'x'); function g<A>(x: NoInfer<A>): A { return x; } declare const n: NoInfer<number>; const s: string = n;",
		["Argument of type '\"x\"' is not assignable", NOT_ASSIGNABLE('number', 'string')]],
	// The result's context infers through an array-like spelled by name, and through a declaration however its name is spelled.
	['a result context infers through ReadonlyArray', 'declare function from<T>(): T[]; const c: ReadonlyArray<number> = from(); const s: string = c[0];', [NOT_ASSIGNABLE('number', 'string')]],
	// As TS's isObjectTypeWithInferableIndex: a type written as an object infers an index signature from its properties.
	['an object type infers an index signature from its properties', 'declare function ents<T>(o: { [s: string]: T }): T[]; declare const b: { p: string; q?: string }; const r: number = ents(b)[0];', [NOT_ASSIGNABLE('string', 'number')]],
	// The result's context is heard before the arguments: a generic call argument infers from it (`compose(filter(x => ...))`).
	['a nested generic call infers from the outer result context', 'declare class SetOf<A> { _a: A; transform<B>(t: (a: SetOf<A>) => SetOf<B>): SetOf<B>; } declare function compose<A, B, C>(f: (x: A) => B, g: (y: B) => C): (x: A) => C; declare function map<A, B>(fn: (a: A) => B): (s: SetOf<A>) => SetOf<B>; declare function filter<A>(p: (a: A) => boolean): (s: SetOf<A>) => SetOf<A>; declare const s: SetOf<number>; s.transform(compose(filter(x => x % 1 === 0), map(x => x + x))); const r: string = s.transform(map(x => x));',
		[NOT_ASSIGNABLE('SetOf<number>', 'string')]],
	// As TS's inferFromTypes: an `any` argument is an `any` candidate; a union infers from each member; a const context still types a call element.
	['inference from any, from a union, and in a const context', "interface R<T> { x: T } declare function Fw<T>(r: () => any): () => R<T>; declare const a: any; const m: Map<string, number> = new Map(a); const z: (() => R<number>) | string = Fw(() => 1); const q: string = z; declare function Ru<const A extends readonly ((() => R<number>) | string)[]>(rhs: A): A; const w: [string] = Ru([Fw(() => 1)]);",
		[NOT_ASSIGNABLE('() => R<number>', 'string'), NOT_ASSIGNABLE('readonly [() => R<number>]', '[string]')]],
	// Under strict null checks `undefined` is below no class, so `o => !!o` infers `o is Sc` (TS 5.5) and `filter` narrows.
	['an inferred predicate excludes undefined from a class union', 'class Sc { x = 1; } declare const outs: (Sc | undefined)[]; const live = outs.filter(o => !!o); const n: string = live;', [NOT_ASSIGNABLE('Sc[]', 'string')]],
	['a destructuring default adds its own type', "let [x = 'a' in {}] = []; x = !x; const { y = 1 } = {} as { y?: string }; const q: boolean = y;", [NOT_ASSIGNABLE('string | number', 'boolean')]],
	// Stripping `undefined` keeps an aliased union by name, as TS does: expanded, it no longer matched the alias itself.
	['?? and ! keep an aliased union by name', "type U = { a: 1 } | { b: 2 }; declare const p: { c?: U }; declare function d(): U; const q: string = p.c ?? d(); declare const n: U | undefined; const r: string = n!;", [NOT_ASSIGNABLE('U', 'string'), NOT_ASSIGNABLE('U', 'string')]],
	// The rest parameter takes every argument past the fixed ones as ONE tuple, a spread as a spread element; neither was checked.
	['rest and spread arguments are checked', "function f(a: number, ...xs: number[]): number { return a; } declare const ys: string[]; f(1, 'x', 2); f(1, ...ys);", ["Arguments of type '[\"x\", 2]' are not assignable to rest parameter", "Arguments of type '[...string[]]' are not assignable to rest parameter"]],
	['fitting rest and spread arguments are clean', 'function f(a: number, ...xs: number[]): number { return a; } declare const ns: number[]; declare const t: [number, number]; f(1); f(1, 2, 3); f(1, ...ns); f(1, 2, ...t); const q: number[] = []; q.push(...ns, 4);', []],
	['an overload is chosen by its rest arguments too', 'declare const fa: number[]; const r: string = fa.concat(0);', [NOT_ASSIGNABLE('number[]', 'string')]],
	// `oneStepIndexed` stepped into tuples and arrays but not a named property, so `T[K] extends any[]` took the false branch (TS's genericRestParameters1).
	['a rest type conditional over an indexed access decides', "type Rec = { move: [number, 'left' | 'right']; stop: string; done: [] }; type Ev<T> = { emit<K extends keyof T = keyof T>(e: K, ...payload: T[K] extends any[] ? T[K] : [T[K]]): void }; declare var events: Ev<Rec>; events.emit('move', 10, 'left'); events.emit('stop', 'Bye!'); events.emit('done');", []],
	// Every block of a namespace is checked in the MERGED scope: re-hoisting a block into a fresh one hid what a later block adds.
	['a namespace block sees what later blocks merge in', 'declare namespace N { interface I { a: number } const make: { new(): I } } declare namespace N { interface I { b: string } } const x = new N.make(); const s: string = x.b; const n: string = x.a;', [NOT_ASSIGNABLE('number', 'string')]],
	['a namespace merged onto a function keeps its call', 'function f(): number { return 1; } namespace f { export const hello: number = 1; } const r: number = f(); const s: string = f.hello;', [NOT_ASSIGNABLE('number', 'string')]],
	// An annotation-only declaration keeps its ref, so an interface augmented after it is read whole (lib.es2020.intl's constructors).
	['a declaration typed by an interface sees its later augmentation', 'declare namespace N { interface C { new(a: string): number } const K: C } declare namespace N { interface C { new(a: number): string } } const r: boolean = new N.K(1);', [NOT_ASSIGNABLE('string', 'boolean')]],
	// TS's preferCovariantType: `U extends T` is inferred `C`, which the covariant `B` does not hold, so `T` is the callback's `A` (coAndContraVariantInferences2).
	['a covariant inference yields where a bounded parameter would not fit it', 'interface A { a: string } interface B extends A { b: string } interface C extends A { c: string } declare function isC(x: A): x is C; declare function pick<T, U extends T>(arr: readonly T[], f: (x: T) => x is U): T; declare const arr: readonly B[] | readonly C[]; const r: string = pick(arr, isC);', [NOT_ASSIGNABLE('A', 'string')]],
	// A generic source is instantiated in the target's context: `T` is `number` here (assignmentCompatWithCallSignatures2).
	['a generic function fits a target that instantiates it', 'const f: (x: number) => void = <T>(x: T) => 1; const g: (x: number) => string = <T>(x: T) => x;', [NOT_ASSIGNABLE('<T>(x: T) => T', '(x: number) => string')]],
	// TS's getTypeFromBindingPattern: with a default anywhere in the pattern the parameter is what the PATTERN implies, not what it
	// is defaulted to (`= []` would make it `never[]`); with no default the initializer says more (destructuringWithLiteralInitializers).
	['a destructuring parameter takes its type from its pattern', 'function g1([x = 0, y = 0] = []) {} const bad1: (a?: [string?]) => void = g1; function g3({ a, b } = { a: 1, b: "x" }) {} const bad3: (o?: { a: string }) => void = g3; g1(); g1([1, 1]);', ["is not assignable to type '(a?: [string?]) => void'", "is not assignable to type '(o?: {"]],
	// A SCRIPT's `interface` augments the GLOBAL one, so the lib's own `RangeErrorConstructor extends ErrorConstructor` has it too
	// (errorConstructorSubtypes); the augmentation is undone between cases, as the corpus harness undoes it between files.
	['a script augments the global interface every declaration sees', 'interface ErrorConstructor { capture(o: object): void } let x: ErrorConstructor; x = RangeError; const s: string = RangeError.capture;', ["is not assignable to type 'string'"]],
	['a script augmentation does not reach the next file', 'const s: string = RangeError.capture;', ["Property 'capture' does not exist"]],
	// `tag<T>`...`` is a tagged template, not `(tag < T) > `...`` -- the type-argument terminal reads a backtick after `>` too.
	['a tagged template takes type arguments', 'declare function tag<T>(s: TemplateStringsArray): T; const s: string = tag<number>`x`;', [NOT_ASSIGNABLE('number', 'string')]],
	// The lazily inferred return was checked against the FIXED signature, whose `FixParams` flattened every pattern to `_`, so
	// nothing the pattern binds existed and the body read `any`. Checked against the declaration now, its parameters refreshed after.
	['a function with a destructuring parameter infers its return', 'function g([x = 0, y = 0] = []) { return x + y; } function h({ a = 0 } = {}) { return a; } const n: string = g(); const m: string = h();', [NOT_ASSIGNABLE('number', 'string'), NOT_ASSIGNABLE('number', 'string')]],
	// `reduceIntersection` narrowed the union but kept both parts: `('a' | 'b') & ('b' | 'c')` stayed `"b" & "b"`.
	['an intersection drops a part that repeats', "declare const i: ('a' | 'b') & ('b' | 'c'); const n: number = i;", [NOT_ASSIGNABLE('"b"', 'number')]],
	// Rest arguments are inferred from as one tuple: against `[(self) => R<T>[]] | R<T>[]` (core.ts's `Rules`), the array member infers `T`.
	['a rest parameter of tuple-or-array type infers from its arguments', 'interface R<T> { a?: (x: number) => T } declare function rule<T>(action: (x: number) => T): R<T>; declare function rules<T>(...alts: [(self: () => R<T>[]) => R<T>[]] | R<T>[]): R<T>[]; const q: string = rules(rule(x => ({ p: 1 })), rule(x => ({ p: 2 })));', [NOT_ASSIGNABLE('R<{\n  p: number\n}>[]', 'string')]],
	// A resolution cut short by the depth limit answers `any` for THAT call; cached, every alias it passed through stayed `any`.
	['a type resolved past the depth limit is not cached as any', 'type A0 = A1; type A1 = A2; type A2 = A3; type A3 = A4; type A4 = A5; type A5 = A6; type A6 = A7; type A7 = A8; type A8 = A9; type A9 = A10; type A10 = A11; type A11 = A12; type A12 = { x: number }; const b: A0 = { x: 1 }; const q: A9 = { x: "s" };', ["is not assignable to type 'A9'"]],
	// A NUMBER index signature infers from an array's elements and a primitive's boxed interface (`String`), as tsc does: `Array.from(xs, f)` was `any[]`.
	['a number index signature infers from an array or a string', 'interface AL<T> { readonly length: number; readonly [n: number]: T } declare function g<T, U>(a: AL<T>, m: (v: T) => U): U[]; const p: boolean = g([1, 2], x => x * 2); const q: boolean = g("abc", c => c);', [NOT_ASSIGNABLE('number[]', 'boolean'), NOT_ASSIGNABLE('string[]', 'boolean')]],
	['a generic function argument to a call returning a function keeps its type parameters (tsc: `<T extends string>(x: T) => T`)','declare function total<T>(map: (x: T) => T | undefined): (x: T) => T; declare function id<T extends string>(t?: T): T | undefined; const q: boolean = total(id);', ['extends string>(x: T']],
	['an assignment to a narrowed name is typed against its declaration', 'interface Ty { k: number } declare function trial<R>(f: () => R): R; declare function get(): Ty; declare const m: Map<number, Ty>; function g(i: number): Ty { let t = m.get(i); if (!t) m.set(i, t = trial(() => get())); return t; }', []],
	['typing a later const early leaves no parameter fixed', 'declare function G<T>(f: () => unknown): T; declare function R<T, U>(xs: T[], f: (x: T) => U): U; const a = G<string[]>(() => b); const b: number = R(a, x => x.toUpperCase());', [NOT_ASSIGNABLE('string', 'number')]],
	// TS's inference priority: a callback's own return outranks the destination, which only fills what nothing else spoke for.
	// `Promise<T>` is covariant (measured, as TS does), and `then`'s callback parameter relates one way (TS's strict callback rule).
	['instantiations of one generic relate by its variance', 'declare const c: Promise<string | number>; const d: Promise<string> = c; declare const a: Promise<number>; const e: Promise<string | number> = a; declare const p: Promise<{ answer: number }>; const t: Promise<string> = p.then(m => m.answer);', ["in declaration of 'd'", "in declaration of 't'"]],
	['a promise a callback returns infers what it resolves to', 'let chain: Promise<void> = Promise.resolve(); declare function step(): Promise<void>; chain = chain.then(() => step());', []],
	['a callback return outranks the destination', 'declare function wrap<T>(f: () => T): { get(): T }; const w: { get(): string } = wrap(() => 1);', ["in declaration of 'w'"]],
	['a closure reads a const declared after it', 'declare function mapA<T>(m: (x: T) => T): T; function outer() { const use = () => { const s: string = mapA(later); const n: string = twice(1); }; const later = (m: number) => m; const twice = (x: number) => x * 2; return use; }', [NOT_ASSIGNABLE('number', 'string'), NOT_ASSIGNABLE('number', 'string')]],
	['a spread of a type parameter or a nullable object keeps its members', 'function f<T>(t: T) { return { ...t, a: 1 }; } const n: number = f({ b: "s" }).b; declare const u: { a: number } | undefined; const m: number = { ...u }.a;', [NOT_ASSIGNABLE('string', 'number'), NOT_ASSIGNABLE('number | undefined', 'number')]],
	['infer against a primitive reads its boxed members', "type L<T> = T extends { length: infer N } ? N : 'no'; type X = L<'ab'>; declare const x: X; const q: string = x; type H<T> = T extends { then(): infer R } ? R : 'no'; type Y = H<{ a: 1 }>; const y: Y = 1;", [NOT_ASSIGNABLE('X', 'string'), "is not assignable to type 'Y'"]],
	['a non-null assertion passes its context on', "declare function q<E extends object = {}>(s: string): E | null; const r: { a: number } = q('x')!;", []],
	['a bare alternative infers only what the others do not match', "type P = number | string; declare function g<T extends { valueOf(): number }>(a: Array<T | P>): T; class N { valueOf() { return 1; } } const z: string = g([new N(), 13, 'x']);", [NOT_ASSIGNABLE('N', 'string')]],
	['a tuple with a rest matches from both ends', "const v: [...string[], 'a' | 'b'] = ['x', 'y', 'a']; const w: [number, ...string[]] = [1, 2]; const t3 = ['x', 'y'] as const; const u: [string, string, 'a'] = [...t3, 'a']; const c = [...t3, 'a'] as const; const n: number = c;", [NOT_ASSIGNABLE('[number, number]', '[number, ...string[]]'), NOT_ASSIGNABLE('readonly ["x", "y", "a"]', 'number')]],
	['a homomorphic mapped parameter infers by reversing it', "declare function s<T>(i: { [K in keyof T]: () => T[K] }): T; const r: string = s({ c: () => 1 }); declare function k<C extends string>(i: { [K in C]: number }): C; const q: number = k({ c: 1, d: 2 }); declare function f<T>(o: T, p: Partial<T>): T; const o = { a: 5, b: 7 }; const w: string = f(o, { b: 9 });", ["is not assignable to type 'string'", NOT_ASSIGNABLE('"c" | "d"', 'number'), "is not assignable to type 'string'"]],
	['a type-parameter parameter gives its constraint as context', "interface AF<A> { o?: A } declare function mk<A extends string>(): AF<A>; declare function cm<const C extends { e?: AF<'k'> }>(c: C): C; cm({ e: mk() }); declare function cn<C extends { e?: AF<'k'> }>(c: C): C; cn({ e: mk() });", []],
	['an inference its constraint does not admit fails the argument', 'declare function g<T extends { a: string }>(t: T): T; g({ a: 1 });', ["Argument of type '{"]],
	['a long conditional chain resolves past the depth budget', "type D<T> = T extends 0 ? 'a' : T extends 1 ? 'b' : T extends 2 ? 'c' : T extends 3 ? 'd' : T extends 4 ? 'e' : T extends 5 ? 'f' : T extends 6 ? 'g' : T extends 7 ? 'h' : T extends 8 ? 'i' : T extends 9 ? 'j' : T extends 10 ? 'k' : T extends 11 ? 'l' : never; declare const x: D<11>; const y: 1 = x; const z: 'l' = x;", [NOT_ASSIGNABLE('"l"', '1')]],
	['a return hint its constraint rejects leaves a predicate to infer', "interface Sig { params: number[] } type M = ({ type: 'call' } & Sig) | { type: 'prop'; key: string }; declare const ms: M[]; const c: Sig[] = ms.filter((m): m is Extract<M, { type: 'call' }> => m.type === 'call'); const f: Sig | undefined = ms.find((m): m is Extract<M, { type: 'call' }> => m.type === 'call');", []],
	['keyof includes a computed enum key', "enum G { A = 0, H = 10 } interface P { [G.H]: { b: 1 }; x: 2 } declare const k: keyof P; const x: 'x' = k; const y: G.H | 'x' = k;", ["is not assignable to type '\"x\"'"]],
	['keyof a union is the keys every member has; a string index admits numbers', "interface E { [k: string]: string | number; [v: number]: string } declare const a: keyof (E | { a: 1 }); const a1: 'a' = a; declare const b: keyof (E | Record<string, bigint>); const b1: string = b; declare const c: keyof { [k: string]: 1 }; const c1: string | number = c; const c2: string = c;", [NOT_ASSIGNABLE('string | number', 'string')]],
	['keyof a class is its public members', "class C { x = 1; private y = 2; protected z = 3; m() { return 1; } } declare const k: keyof C; const k1: 'x' | 'm' = k;", []],
	['an indexed access distributes over a union object', "type E = { [k: string]: string | number } | Record<string, number | bigint>; declare const v: E[string]; const v1: string | number | bigint = v; type V = Extract<E[keyof E], number | bigint>; declare const w: V; const w1: number | bigint = w; const w2: number = w;", ["is not assignable to type 'number'"]],
	['a homomorphic mapped type keeps a string index beside its properties', "type Foo = { prop: number, [x: string]: number }; function f(x: Partial<Foo>, y: { [P in keyof Foo]: Foo[P] }) { const a: number | undefined = x.prop; const b: number = y['other']; const c: string = y.prop; }", [NOT_ASSIGNABLE('number', 'string')]],
	['a mapped type over an intersection keeps its members\' modifiers; an empty key set is {}', "type Om<T, K extends keyof T> = Pick<T, Exclude<keyof T, K>>; const h: Partial<Pick<{ p: 1 }, 'p'>> & Om<{ p: 1 }, 'p'> = {}; const e: { [K in never]: 1 } = {};", []],
	['a conditional over keyof a type parameter defers', "const f = <P>(p: Pick<P, Exclude<keyof P, never>>): P => p; function g<T extends { a: string, b: string }>(o: Pick<T, Exclude<keyof T, 'a'>>) { return o.b; } function h<T>(x: Exclude<T, never>, y: Extract<T, never>) { const a: T = x; x = a; const b: never = y; }", []],
	['a deferred conditional relates through its branches', "function f<T>(x: T extends string ? 1 : 2, y: T extends string ? 'a' : 'b') { const a: 1 | 2 = x; const b: 1 = x; y = 'a'; }", ["is not assignable to type '1'", "is not assignable to type"]],
	['a generic target signature binds its own type parameters', "declare let a: <T>() => (T extends true ? true : false) & boolean; declare let b: <T>() => (T extends true ? true : false) & boolean; a = b; declare let c: <T>() => T extends true ? 1 : 2; declare let d: <T>() => T extends true ? 1 : 3; c = d; const f: <A>(x: A) => A[] = x => [x]; const g: <A>(x: A) => A[] = x => [1];", ["is not assignable to type '<T>() => T extends true ? 1 : 2'", "is not assignable to type '<A>(x: A) => A[]'"]],
	['higher-order inference lifts a generic argument\'s type parameters into the result', "type Box<T> = { value: T }; declare function wrap<A, B>(f: (a: A) => B): (a: A) => B; declare function compose<A, B, C>(f: (a: A) => B, g: (b: B) => C): (a: A) => C; declare function list<T>(a: T): T[]; declare function box<V>(x: V): Box<V>; const f02: <A>(x: A) => A[] = wrap(list); const f03: <A>(x: A) => A[] = wrap(x => [x]); const f11: <T>(x: T) => Box<T[]> = compose(list, box); declare function af<T>(f: (x: T) => boolean): (a: T[]) => T[]; const k: <T extends { v: 1 }>(a: T[]) => T[] = af(x => x.nope);", ["Property 'nope' does not exist"]],
	['keyof keeps a numeric property name a number, a quoted one a string', "type O = { 0: () => void; '1': () => void; 0x10: () => void }; const n: Extract<keyof O, number> = 16; declare const s: Extract<keyof O, string>; const x: 5 = s; declare function f<T>(x: T): Extract<keyof T, number>; const t: 0 | 1 = f({ 0: 'a', 1: 'b' });", [NOT_ASSIGNABLE('\"1\"', '5')]],
	['a mapped type indexed by a union of keys instantiates per key', "interface EV { MC: { a: 1 }; MU: { a: 2 } } interface S<T, D> { d: D; t?: T } type U = { [T in keyof EV]: S<T, EV[T]> }[keyof EV]; declare const g: U; if (g.t === 'MC') { const d: { a: 1 } = g.d; }", []],
	['an inline conditional over a type parameter distributes', "interface B<T> { g(): T extends string ? 's' : 'n'; } declare const b: B<string | number>; const f: 's' | 'n' = b.g(); const g: 's' = b.g();", ["is not assignable to type '\"s\"'"]],
	// A recursive alias over an abstract parameter must stay deferred: taken as concrete, it unrolled until memory ran out.
	['a recursive conditional over an abstract parameter stays deferred', `
		type UnionToIntersection<U> = (U extends any ? (x: U) => void : never) extends (x: infer I) => void ? I : never;
		type Invert<T> = { [K in keyof T as T[K] & PropertyKey]: K };
		type OPTABLE = { [k: string]: string | OPTABLE };
		type FlattenOps<T> = T[keyof T] extends string ? Invert<T> : UnionToIntersection<{ [K in keyof T]: FlattenOps<T[K]> }[keyof T]>;
		class TableBuilder<T extends object> {
			constructor(private root: T) {}
			flatten<S extends OPTABLE>(page: number, obj: S): TableBuilder<T & FlattenOps<S>> {
				for (const [byte, mnemonic] of Object.entries(obj)) {
					if (typeof mnemonic !== 'string')
						this.flatten(page, mnemonic);
					else
						(this.root as any)[mnemonic] = (page << 8) + Number(byte);
				}
				return this as never;
			}
			build(): T { return this.root; }
		}
		const OP = new TableBuilder({}).flatten(0x00, { NONE: { '0x00': 'unreachable', '0x01': 'nop' }, MEM: { '0x28': 'i32.load' } }).build();`, []],
	['a numeric key names the property its value prints as', `
		const t = { 0x20: 'a', 1_0: 'b', 0b11: 'c' } as const;
		const a: 'a' = t[32], b: 'b' = t[10], c: 'c' = t[3];
		interface I { 0x10: number }
		declare const i: I;
		const d: number = i[16];
		const h: 0x10 = 16;
		const wrong: 'b' = t[0x20];`, ["not assignable to type '\"b\"'"]],
	['an exact bigint context keeps a bigint literal', `
		declare function take(o: { a: 10n }): void;
		take({ a: 10n });
		take({ a: 11n });`, ["not assignable to parameter"]],
	['two instantiations of one generic function type are distinct', `
		declare function make<T extends string>(op: T): { op: T };
		type Table<T extends Record<number, string>> = { [K in keyof T]: ReturnType<typeof make<T[K] & string>> };
		declare const v: Table<{ 1: 'a'; 2: 'b' }>[1 | 2];
		const w: { op: 'a' } | { op: 'b' } = v;
		const u: { op: 'a' } = v;`, ["not assignable to type"]],
	['an immediately invoked function types its parameters by its arguments, widened', `
		const r = (d => d.y)({ x: 1 });
		const ok: number = (d => d.x)({ x: 1 });
		const n: string = ((a, b) => a + b)(1, 2);
		const s: string = (function (v) { return v; })('k');`, ["Property 'y' does not exist", "not assignable to type 'string'"]],
	['a declared this parameter is inferred from the receiver and is no argument', `
		interface WithGet { get<X extends abstract new (...args: any) => any>(this: X, s: number): InstanceType<X>; }
		declare const C: (new (s: number) => { n: number }) & WithGet;
		const ok: number = C.get(1).n;
		const bad: string = C.get(1).n;
		interface Y { foo<T>(this: T, arg: keyof T): void; a: number }
		declare const y: Y | undefined;
		y?.foo('a');
		y?.foo('z');
		interface Box { m(this: Box, v: string): number }
		declare const b: Box;
		b.m('a');
		b.m();
		const cp: ConstructorParameters<new (a: string) => void> = [1];
		const r: Required<{ a?: number }> = {};`, ["not assignable to type 'string'", "not assignable to parameter", "Expected 1 arguments", "not assignable to type", "not assignable to type"]],
	['a method binds its own type parameters and declared this; a type-parameter argument infers through its constraint', `
		class C<T> {
			m<A extends readonly T[]>(a: A): void { const z: number = a; }
			k<A extends string>(this: A): void { const s: string = this; const n: number = this; }
		}
		declare function g<E>(a: readonly E[]): E;
		function f<T, A extends readonly T[]>(a: A): T { const y: number = g(a); return g(a); }`,
		["Type 'A' is not assignable to type 'number'", "Type 'A' is not assignable to type 'number'", "Type 'T' is not assignable to type 'number'"]],
	['a class adding no members has the members of its base', `
		class A { tell() { return 1; } }
		class B extends A { constructor(x: number) { super(); } }
		class C extends A {}
		const b: string = new B(1).tell(), c: string = new C().tell();`,
		["Type 'number' is not assignable to type 'string'", "Type 'number' is not assignable to type 'string'"]],
	['a homomorphic mapped type over an array-constrained type parameter is apparently that array mapped', `
		interface Expr<T> { t: T }
		declare function fold(...args: Expr<any>[]): number;
		function struct<T extends readonly unknown[]>(...fields: { [K in keyof T]: Expr<T[K]> }) {
			const v = Object.values(fields), w: string = v;
			return fold(...v);
		}`,
		["is not assignable to type 'string'"]],
];

(async () => {
	const global	= T.makeGlobal();
	const lib		= await new ModuleLoader(path.join(__dirname, '../test'), {}).get('typescript/lib/lib.esnext.full', '.');
	checkBlock(lib!.program.body, global);
	const parser	= TS.make();
	let failures = 0;
	for (const [name, code, expected, nonStrict] of cases) {
		global.nullChecks = !nonStrict;
		// Each case is a SCRIPT: what it augments in the global scope is undone before the next one.
		const undo		= global.recordTypes();
		const diags		= await TStypeCheckAsync(parser.parse(code), new ModuleLoader(__dirname, {}), global);
		undo();
		const errors	= diags.filter(d => d.severity === SEVERITY.ERROR).map(d => String(d.message));
		const ok		= errors.length === expected.length && expected.every((e, i) => errors[i].includes(e));
		if (!ok) {
			++failures;
			console.error(`FAIL - ${name}\n  expected: ${JSON.stringify(expected)}\n  got:      ${JSON.stringify(errors)}`);
		} else {
			console.log(`ok - ${name}`);
		}
	}
	console.log(failures ? `${failures} checker test(s) failed` : 'all checker tests passed');
	process.exitCode = failures ? 1 : 0;
})();
