import * as TS from './ts-parser';
import * as JS from './js-parser';
import { Literal, hasMod } from '@isopodlabs/tison/ast';
import { Expr } from './js-parser';
import { Type } from './ts-parser';
import {
	ANY, BIGINT, BOOLEAN, INTRINSIC_TYPES, IterationTypes, NEVER, NUMBER, REGEXP, SIMPLE_TYPES, STRING, Scope, Semantics, UNDEFINED, UNKNOWN,
	arrayLikeElement, awaitType, combineTypes, elementTypes, findFunctionType, freshTypeParamName, objectMember, isAny, isBoolean, isLiteral, isNullish,
	isRef, isString, lookupMember, ownScope, paramTypeAt, rangeIncludesZero, resolve, resolveMembers, resolveOwn, substituteThisType,
	typeArgMap, unionMembers, widenLiterals,
} from './type-core';

// TypeScript's view of the shared type model: `type-core` plus the rules JavaScript's runtime adds to it -- truthiness,
// `typeof`, literal typing, the iteration protocol, and the members every value gets without declaring them.
export * from './type-core';

// ===================================================================
//  JavaScript primitives and literals
// ===================================================================

// A Map, not an object: it is indexed by names from source, and `constructor`/`toString` must not find `Object.prototype`'s.
const BOXED_PRIMITIVE = new Map([['string', 'String'], ['number', 'Number'], ['boolean', 'Boolean'], ['bigint', 'BigInt'], ['symbol', 'Symbol']]);

export function isNullLiteral(e: Expr): boolean {
	return nullLiteralKind(e) !== undefined;
}

// Which nullish literal `e` is, if either: they share one physical form (`ref.null`), so only a STRICT comparison tells them apart, statically.
export function nullLiteralKind(e: Expr): 'null' | 'undefined' | undefined {
	return	e.type === 'literal' && e.value === null			? 'null'
		:	e.type === 'identifier' && e.name === 'undefined'	? 'undefined'
		:	undefined;
}

export function literalTypeOf(e: Expr | undefined): Type | undefined {
	if (e?.type === 'literal') {;
		switch (typeof e.value) {
			case 'string':	return STRING;
			case 'boolean':	return BOOLEAN;
			case 'number':	
				return	e.value !== (e.value | 0)						? NUMBER
					:	e.value >= -0x80000000 && e.value <= 0x7fffffff ? TS.RefType('i32')
					:	e.value >= 0 && e.value <= 0xffffffff			? TS.RefType('u32')
					:	NUMBER;
			case 'bigint':
				return	e.value >= -0x8000000000000000n && e.value <= 0x7fffffffffffffffn	? TS.RefType('i64')
					:	e.value >= 0n && e.value <= 0xffffffffffffffffn						? TS.RefType('u64')
					:	BIGINT;
			case 'object':	return e.value === null ? Literal(e.value) : Array.isArray(e.value) ? STRING : REGEXP;
		}
	}
}

// ===================================================================
//  Members JavaScript adds: TS_SEMANTICS, and the global scope
// ===================================================================

// Built-in array members precise enough that element types survive (`pop()!`).
function arrayMethod(elem: Type, prop: string): Type | undefined {
	// `map`'s result follows the callback's return, so it needs a real generic signature. Its type param is named fresh per call: built by hand,
	// not through `substituteType`, a fixed `U` would be captured by an ambient `U` in `elem` (`.map()` on `U[][]` inside a method of `<U>`).
	if (prop === 'map') {
		const U = TS.RefType(freshTypeParamName('U'));
		return TS.FunctionType([
				JS.Param('callback', TS.FunctionType([
					JS.Param('v', elem),
					JS.Param('i', NUMBER),
					JS.Param('arr', TS.ArrayType(elem))
				], U)),
				JS.Param('thisArg', ANY, ['optional']),
			],
			TS.ArrayType(U),
			[{ name: U.name }]
		);
	}

	// TS's three overloads: no seed (the accumulator is the element type), a seed of the element type, a seed of `U` (fresh, as `map`'s).
	if (prop === 'reduce' || prop === 'reduceRight') {
		const U		= TS.RefType(freshTypeParamName('U'));
		const cb	= (acc: Type) => JS.Param('callback', TS.FunctionType([JS.Param('acc', acc), JS.Param('v', elem), JS.Param('i', NUMBER), JS.Param('arr', TS.ArrayType(elem))], acc));
		return TS.ObjectType([
			TS.TypeCall(TS.CallSig({ params: [cb(elem)] }, elem)),
			TS.TypeCall(TS.CallSig({ params: [cb(elem), JS.Param('initialValue', elem)] }, elem)),
			TS.TypeCall(TS.CallSig({ params: [cb(U), JS.Param('initialValue', U)] }, U, [{ name: U.name }])),
		]);
	}

	// One rest-based signature: the overload picker fails whenever an argument is a spread (`arr.splice(i, n, ...items)`).
	if (prop === 'splice')
		return TS.FunctionType(
			{ params: [JS.Param('start', NUMBER), JS.Param('deleteCount', NUMBER, ['optional'])], rest: JS.Rest('items', TS.ArrayType(elem)) },
			TS.ArrayType(elem)
		);

	// Fresh, as `map`'s `U`.
	if (prop === 'every' || prop === 'filter' || prop === 'find' || prop === 'findLast') {
		const S = TS.RefType(freshTypeParamName('S'));
		return TS.FunctionType(
			[
				JS.Param('predicate', TS.FunctionType(
					[JS.Param('v', elem), JS.Param('i', NUMBER), JS.Param('arr', TS.ArrayType(elem))],
					TS.Predicate('v', S)
				)),
				JS.Param('thisArg', ANY, ['optional']),
			],
			prop === 'every' ? TS.Predicate('this', TS.ArrayType(S)) : prop === 'filter' ? TS.ArrayType(S) : combineTypes([S, UNDEFINED]),
			[{ name: S.name, constraint: elem, default: elem }],
		);
	}
	return undefined;
}

// Everything else `interface Array<T>` declares: only the RETURN type is refined, over the declaration's own parameters, so an unannotated
// callback (`a.some(x => x > 0)`) is still contextually typed.
function arrayMethodReturn(elem: Type, prop: string): Type | undefined {
	return	prop === 'pop' || prop === 'shift' ? combineTypes([elem, UNDEFINED])
			// Bounded, not bare `number`, so a loop comparing against it stays `i32`; `0x7fffffff`, so it is `i32`, not `u32`.
			:	prop === 'push' || prop === 'unshift' ? TS.RangeType('number', 0, 0x7fffffff, true)
			:	prop === 'indexOf' || prop === 'lastIndexOf' || prop === 'findIndex' ? TS.RangeType('number', -1, 0x7fffffff, true)
			:	prop === 'includes' || prop === 'some' ? BOOLEAN
			:	prop === 'join' ? STRING
			:	prop === 'slice' || prop === 'concat' || prop === 'reverse' ? { type: 'array', element: elem } as Type
			:	undefined;
}

// `arrayMethodReturn`'s refinement onto whatever shape the declaration has: a lone `function`, or an overload set's multi-signature `object`.
function withReturnType(t: Type | undefined, ret: Type): Type | undefined {
	if (t?.type === 'function')
		return { ...t, returnType: ret };
	if (t?.type === 'object' && t.members.every(m => m.type === 'call'))
		return TS.ObjectType(t.members.map(m => ({ ...m, returnType: ret })));
	return undefined;
}

// The members of an array or tuple this checker models more precisely than `interface Array<T>` declares.
function refinedMember(t: Type, prop: string, scope: Scope, depth: number): Type | undefined {
	if (t.type !== 'array' && t.type !== 'tuple')
		return undefined;
	const elem	= t.type === 'array' ? t.element : combineTypes(elementTypes(t, scope));
	const ret	= arrayMethodReturn(elem, prop);
	// The synthetic fallback only for a member `lib.d.ts` does not declare: each such name is a gap in `interface Array<T>`.
	return arrayMethod(elem, prop) ?? (ret && (withReturnType(lookupMember(TS.RefType('Array', [elem]), prop, scope, depth - 1), ret)
		?? TS.FunctionType({ params: [], rest: JS.Rest('args', TS.ArrayType(ANY)) }, ret)));
}

export const TS_SEMANTICS: Semantics = {
	boxed:			name => BOXED_PRIMITIVE.get(name),
	apparentMember:	objectMember,
	refinedMember,
	iterationOf,
};

export function makeGlobal() {
	const global = new Scope(TS_SEMANTICS);
	for (const [r, n] of BOXED_PRIMITIVE)
		global.addValue(n, TS.FunctionType([JS.Param('value', ANY, ['optional'])], TS.RefType(r)));

	global.addValue('undefined',	UNDEFINED);
	global.addValue('NaN',			NUMBER);
	global.addValue('Infinity',		NUMBER);

	const TT = TS.RefType('T');
	const TP = [TS.TypeParam('T')];
	global.addValue('Array', TS.ObjectType([
		TS.TypeCall(TS.CallSig([JS.Param('arrayLength', NUMBER, ['optional'])], TS.ArrayType(TT), TP)),
		TS.TypeProperty('prototype', ANY),
		TS.TypeMethod('from', 		TS.CallSig(
			[
				JS.Param('arrayLike',	ANY),
				JS.Param('mapfn',		TS.FunctionType([JS.Param('v', ANY), JS.Param('k', NUMBER)], TT), ['optional']),
				JS.Param('thisArg', 	ANY, ['optional']),
			],
			TS.ArrayType(TT),
			TP
		)),
		TS.TypeMethod('isArray',	TS.CallSig([JS.Param('a', ANY)], TS.Predicate('a', TS.ArrayType(ANY)))),
		TS.TypeMethod('of',			TS.CallSig({ params: [], rest: JS.Rest('items', TT) }, TS.ArrayType(TT), TP)),
	]));

	return global;
}

// ===================================================================
//  Signatures of JavaScript functions
// ===================================================================

// An unannotated parameter's type from its default, widened (`f(scale = 10)` declares `number`), as codegen's `resolveParam` infers it:
// the two must agree, or a function TYPE built from a declaration lowers to another physical signature.
function widenedDefaultType(d: JS.Expr<any> | undefined): Type | undefined {
	const t = d && literalTypeOf(d);
	// A numeric literal's is its value's type: `literalTypeOf` gives it the storage it fits (`i32`), which a signature does not declare.
	return !t ? undefined : d.type === 'literal' && typeof d.value === 'number' ? NUMBER : d.type === 'literal' && typeof d.value === 'bigint' ? BIGINT : widenLiterals(t);
}

// TS's getTypeFromBindingPattern: what a pattern implies about what it destructures, the parameter's own type where it has a DEFAULT anywhere
// (`[x = 0, y = 0] = []`); without one the initializer says more (`{a, b} = {a: 1, b: 'x'}`).
export function patternDefaults(target: JS.BindingTarget): boolean {
	return typeof target !== 'string' && (target.type === 'array_pattern'
		? target.elements.some(el => !!el && (!!el.default || patternDefaults(el.target)))
		: target.properties.some(p => !!p.default || patternDefaults(p.value)));
}

// A default makes its slot optional and its type nullable, as TS writes it; a nested pattern says what it implies.
export function patternType(target: JS.BindingTarget): Type {
	const implied = (t: JS.BindingTarget, def?: JS.Expr<any>): Type => {
		const base = typeof t !== 'string' ? patternType(t) : widenedDefaultType(def) ?? ANY;
		return def ? combineTypes([base, UNDEFINED]) : base;
	};
	if (typeof target === 'string')
		return ANY;
	return target.type === 'array_pattern'
		? { type: 'tuple', elements: target.elements.map(el => el?.default ? { type: 'optional', element: implied(el.target, el.default) } : el ? implied(el.target) : ANY) }
		: TS.ObjectType(target.properties.flatMap(p => typeof p.key !== 'object' ? [TS.TypeProperty(p.key, implied(p.value, p.default), p.default ? ['optional'] : undefined)] : []));
}

// JS params as TS params; a defaulted parameter counts as optional.
export function FixParams(params: JS.Params<any>): TS.Params {
	return {
		params: params.params.map((p): TS.Param => ({
			key:			typeof p.key === 'string' ? p.key : '_',
			modifiers:		hasMod(p, 'optional') || !!p.default ? ['optional'] : [],
			typeAnnotation: p.typeAnnotation as Type ?? (typeof p.key !== 'string' && patternDefaults(p.key) ? patternType(p.key) : widenedDefaultType(p.default)),
			default:		p.default
		})),
		rest:		params.rest as JS.Rest<Type>,
		thisType:	params.thisType
	};
}
// `declaredReturnType`: the function's own annotation, captured before `checkFunctionBody` overwrites `returnType` with what its body infers.
export function FixSig(params: JS.CallSig<any>, defaultRet?: Type, declaredReturnType?: Type): TS.CallSig {
	return { ...FixParams(params),
		returnType: declaredReturnType ?? params.returnType as Type ?? defaultRet,
		typeParams: params.typeParams as TS.TypeParam[]
	};
}

// ===================================================================
//  typeof and truthiness
// ===================================================================

// A constructor parameter with an accessibility or `readonly` modifier also declares the property of that name.
export const isParamProperty = <P extends { modifiers?: string[] }>(p: P): p is P & { modifiers: string[] } => !!p.modifiers?.some(m => m !== 'optional');

// What `typeof` reports for this type, or undefined when not known statically (`'object'`/`'function'` have no single physical form to test).
// `scope`: resolve each union member first; omitted, the type is answered as given (the checker's narrowing, per split member).
export function typeofName(t: Type, scope?: Scope): string | undefined {
	const r = scope ? resolve(scope, t) : t;
	switch (r.type) {
		case 'literal':				return Array.isArray(r.value) ? 'string' : typeof r.value;
		case 'range':				return r.base;
		case 'function':
		case 'constructor':			return 'function';
		case 'array':
		case 'tuple':				return 'object';
		// `{}` holds any value but `null`/`undefined`, primitives too: it has no one `typeof`.
		case 'object':				return r.members.length ? 'object' : undefined;
		case 'intersection': {
			// A part that makes the value a PRIMITIVE wins: a branded `string & {brand}` is a string to `typeof`.
			const parts = r.types.map(p => typeofName(p, scope));
			return parts.find(n => n && SIMPLE_TYPES.has(n))
				?? (parts.includes('function') ? 'function' : 'object');
		}
		case 'union': {
			// Every inhabitant must agree (`unionMembers` resolves, flattens, drops `never`); without a `scope`, a shallow answer.
			const members	= scope ? unionMembers(r, scope) : r.types.filter(m => !isRef(m, 'never'));
			const names		= new Set(members.map(m => typeofName(m, scope)));
			return names.size === 1 && !names.has(undefined) ? [...names][0] : undefined;
		}
		case 'ref': {
			if (SIMPLE_TYPES.has(r.name))
				return r.name;
			if (r.name === 'unique symbol')
				return 'symbol';
			if (r.name === 'void' || r.name === 'null')
				return r.name === 'void' ? 'undefined' : 'object';
			// A ref left by `resolve` names a real class: `typeof` asks about STRUCTURE, so its members are asked for, guarded so an unexpandable ref
			// does not recurse on itself.
			const m = scope && resolveMembers(r, scope);
			return m && m.type !== 'ref' ? typeofName(m, scope) : undefined;
		}
		default:					return undefined;
	}
}

export function isFalsy(t: Type, scope: Scope): boolean {
	const r = resolveOwn(t, scope);
	return	r.type === 'literal'	? !r.value
		:	r.type === 'ref'		? r.name === 'undefined' || r.name === 'null' || r.name === 'void'
		:	r.type === 'range'		? r.min !== undefined && r.min === r.max && rangeIncludesZero(r)	// the single point 0
		:	r.type === 'union'		? r.types.every(t => isFalsy(t, scope))
		:	false;
}

export function isTruthy(t: Type, scope: Scope): boolean {
	const r = resolveOwn(t, scope);
	return	r.type === 'literal'		? !!r.value
		:	r.type === 'range'			? !rangeIncludesZero(r)
		:	r.type === 'union'			? r.types.every(m => isTruthy(m, scope))
		:	r.type === 'intersection'	? r.types.some(m => isTruthy(m, scope))
		:	r.type === 'ref'			? isObjectRef(r, scope)
		:	['object', 'array', 'tuple', 'function', 'constructor'].includes(r.type);
}

// True when a value of this type is truthy whenever non-null (an object, array, tuple, function); never a string, number, boolean, literal or a
// dynamic `any`/type parameter. From the CHECKER's type, which still knows a boxed `any` slot holds `Stmt | undefined`.
export function alwaysTruthy(t: Type, scope: Scope): boolean {
	const r = resolve(scope, t);
	switch (r.type) {
		case 'object': case 'array': case 'tuple':	case 'function': case 'constructor':
			return true;
		case 'union':
			// An all-nullish union is `true` here, still correct: the null test answers `false` for it.
			return unionMembers(r, scope).every(m => isNullish(m, scope) || alwaysTruthy(m, scope));
		case 'intersection':
			// One object-ish part of an intersection makes it an object, unless another makes it a PRIMITIVE (`string & {brand}`); an interface that
			// `extends` another resolves to exactly this.
			return r.types.some(m => alwaysTruthy(m, scope))
				&& !r.types.some(m => ['ref', 'literal'].includes(resolve(scope, m).type));
		case 'ref':
			// `never` is uninhabited: vacuously true. Any other `ref` left by `resolve` is a primitive or an unresolved name, undecidable here.
			return r.name === 'never';
		default:
			// A literal, `keyof`, a conditional, a type parameter: not decidable here either.
			return false;
	}
}

// A class or interface instance is an object, never falsy; not an empty shape (`{}`, `Object`), which a primitive satisfies.
function isObjectRef(r: TS.RefType, scope: Scope): boolean {
	if (INTRINSIC_TYPES.has(r.name))
		return false;
	const m = resolveMembers(r, scope);
	return m.type === 'object' ? m.members.length > 0 : m.type === 'intersection' && m.types.some(p => p.type === 'object' && p.members.length > 0);
}

export function makeNullish(type: Type) {
	if (type.type === 'ref') {
		switch (type.name) {
			case 'bigint':
			case 'number':	return Literal(0);
			case 'boolean':	return Literal(false);
			case 'string':	return Literal('');
		}
	}
	if (type.type === 'range') {
		// A range provably excluding 0 can never take its "one falsy value" -- that branch is unreachable for it.
		if (!rangeIncludesZero(type))
			return NEVER;
		return type.base === 'number' ? Literal(0) : TS.RangeType('bigint', 0n, 0n);
	}
	return type;
}

export function isOther(op: string) {
	return op === '?' ? isNullish : op === '|' ? isFalsy : isTruthy;
}

// What `a && b` / `a || b` / `a ?? b` yields from `a` when it short-circuits: a boolean survives `||` only as true, `&&` only as false, and
// `&&` narrows a string/number to its one falsy literal.
export function logicalLeftPart(t: Type, op: string, scope: Scope): Type {
	const other	= isOther(op[0]);
	// A member union nothing is dropped from stays as written: `p.constraint ?? x` is `Type`, not `Type`'s members.
	const part	= (m: Type): Type[] => {
		const p = resolveOwn(m, scope);
		if (p.type === 'union') {
			const kept = p.types.flatMap(part);
			return kept.length === p.types.length && kept.every((k, i) => k === p.types[i]) ? [m] : kept;
		}
		if (other(p, scope))
			return [];
		if (op !== '??' && isBoolean(p))
			return [Literal(op === '||')];
		return [op === '&&' ? makeNullish(p) : m];
	};
	return combineTypes(part(t));
}

// ===================================================================
//  The iteration protocol
// ===================================================================


// The global iteration types whose type arguments ARE their iteration types (TS's getIterationTypesOfIterableFast): a bundled lib may not
// declare them through the protocol (codegen's `Generator` has only `next`). A bare Iterator is never iterated.
const ITERABLES		= new Set(['Iterable', 'IterableIterator', 'IteratorObject', 'Generator']);
const ASYNC_ITERABLES	= new Set(['AsyncIterable', 'AsyncIterableIterator', 'AsyncIteratorObject', 'AsyncGenerator']);
function globalIterationTypes(t: Type, scope: Scope, async: boolean, generatorReturn: boolean): IterationTypes | undefined {
	if (t.type !== 'ref' || !((async ? ASYNC_ITERABLES : ITERABLES).has(t.name) || (generatorReturn && t.name === (async ? 'AsyncIterator' : 'Iterator'))))
		return undefined;
	const entry = ownScope(t, scope).lookupType(t.name);
	if (!entry?.typeParams || entry !== scope.root().type(t.name))
		return undefined;
	const [y, r, n] = [...typeArgMap(entry.typeParams, t.typeArgs, UNKNOWN).values()];
	return { yield: y ?? UNKNOWN, return: r ?? ANY, next: n ?? ANY };
}

function iterationOf(target: Type, source: Type, scope: Scope) {
	const async	= target.type === 'ref' && ASYNC_ITERABLES.has(target.name);
	const own	= globalIterationTypes(target, scope, async, false);
	const it	= own && iterationTypes(source, scope, async);
	return it && { target: own, source: it };
}

export function iterationTypes(t: Type, scope: Scope, async = false, depth = 6, generatorReturn = false): IterationTypes | undefined {
	const fast = globalIterationTypes(t, scope, async, generatorReturn);
	if (fast)
		return fast;
	const r = resolveOwn(t, scope);
	if (isAny(r))
		return { yield: ANY, return: ANY, next: ANY };
	if (r.type === 'union' && depth > 0) {
		const parts = r.types.map(m => iterationTypes(m, scope, async, depth - 1));
		return parts.every(p => !!p) ? { yield: combineTypes(parts.map(p => p!.yield)), return: combineTypes(parts.map(p => p!.return)), next: combineTypes(parts.map(p => p!.next)) } : undefined;
	}
	// TS's getIterationTypesOfIterable: a method, iterator or `next` typed `any` iterates as `any`. Read through the receiver's `this`, so
	// `declare [Symbol.iterator]: this["entries"]` reaches its `entries`.
	const anyIteration	= { yield: ANY, return: ANY, next: ANY };
	const isAnyType		= (x: Type | undefined) => !!x && isAny(resolveOwn(x, scope));
	const protocol = (key: string): IterationTypes | undefined => {
		const method	= lookupMember(t, key, scope);
		if (isAnyType(method))
			return anyIteration;
		const iterator	= findFunctionType(substituteThisType(method ?? NEVER, t), scope)?.returnType;
		if (isAnyType(iterator))
			return anyIteration;
		// An iterator that is itself a global Iterator/Generator reference reads its type arguments (getIterationTypesOfIteratorFast): `next()`'s
		// bundled IteratorResult cannot split `value` by `done`.
		const fastIterator	= iterator && globalIterationTypes(substituteThisType(iterator, t), scope, key === '[Symbol.asyncIterator]', true);
		if (fastIterator)
			return fastIterator;
		const nextMember	= iterator && lookupMember(substituteThisType(iterator, t), 'next', scope);
		if (isAnyType(nextMember))
			return anyIteration;
		const nextSig	= nextMember && findFunctionType(nextMember, scope);
		const next		= nextSig?.returnType;
		if (!next)
			return undefined;

		const yields: Type[] = [], returns: Type[] = [];
		for (const m of unionMembers(key === '[Symbol.asyncIterator]' ? awaitType(next, scope) : next, scope)) {
			const done = lookupMember(m, 'done', scope);
			const d = done && resolveOwn(done, scope);
			(d && isLiteral(d, 'boolean') && d.value === true ? returns : yields).push(lookupMember(m, 'value', scope) ?? UNDEFINED);
		}
		// `next`: what `next(v)` accepts, which a generator's `yield` evaluates to -- `next(...[value]: [] | [TNext])` spells it as a rest.
		return { yield: combineTypes(yields), return: combineTypes(returns),
			next: paramTypeAt(nextSig, 0, scope) ?? UNDEFINED };
	};
	if (async) {
		const own = protocol('[Symbol.asyncIterator]');
		if (own)
			return own;
		const sync = iterationTypes(t, scope, false, depth);
		return sync && { ...sync, yield: awaitType(sync.yield, scope) };
	}
	const found = protocol('[Symbol.iterator]');
	if (found)
		return found;
	const direct = arrayLikeElement(r) ?? (r.type === 'tuple' ? combineTypes(elementTypes(r, scope)) : isString(r) || isLiteral(r, 'string') ? STRING : undefined);
	return direct && { yield: direct, return: UNDEFINED, next: UNDEFINED };
}
