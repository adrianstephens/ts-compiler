/* eslint-disable @typescript-eslint/no-unused-expressions */
import * as TS from './ts-parser';
import * as JS from './js-parser';
import { Literal, Binary, hasMod, Location, getPos } from '@isopodlabs/tison/ast';
import { isTsDeclaration, walker, walkerB } from './walker';
import * as T from './type-utils';
import { type Closure, paramNames } from './free-names';

export const SEVERITY = {
	GAP:		0,	// known missing functionality (see the header's own gap list) -- not a judgment call, just a reminder
	WARNING:	1,
	ERROR:		2,
} as const;
export type SEVERITY = (typeof SEVERITY)[keyof typeof SEVERITY];
export type Err = (sev: SEVERITY, pos: Location) => (strings: TemplateStringsArray, ...values: (string | number | undefined)[]) => void;
// A fresh printer per interpolated value: `typeBudget` is spent per `Output` instance, never reset.
const show = T.show;

type Type		= TS.Type;
type Expr		= TS.Expr;
type Stmt		= TS.Stmt;
type Scope		= T.Scope;
const Scope		= T.Scope;

// ===================================================================
//  TStypeCheck -- structural type checking of a parsed TS AST
// ===================================================================
// Partial. An unmodeled case reports `SEVERITY.GAP`; the old silent-`any` leniency is being removed (memory/tison_workaround_inventory.md), never extended.


const COMPARISON_OPS 	= new Set(['==', '!=', '===', '!==', '<', '>', '<=', '>=', 'in', 'instanceof']);
const LOGICAL_OPS		= new Set(['&&', '||', '??']);

// ===================================================================
//  statement utils
// ===================================================================

// Every plain-identifier local a generator/async body declares (with its statement, for its stamped scope), stopping at a nested closure:
// wasm-backend.ts keeps each in the resumable frame, with no liveness analysis. A destructured declarator is skipped. `varsOnly`: just the `var`s.
export function collectHoistedLocals(body: Stmt[], varsOnly = false): Map<string, { stmt: Stmt; decl: JS.Var<Type> }> {
	const decls = new Map<string, { stmt: Stmt; decl: JS.Var<Type> }>();
	walkerB(
		(s, process) => {
			if (s.type === 'function_decl' || s.type === 'class_decl')
				return false;
			if (s.type === 'var_decl' && (!varsOnly || s.kind === 'var')) {
				for (const d of s.declarations) {
					if (typeof d.name === 'string' && !decls.has(d.name))
						decls.set(d.name, { stmt: s, decl: d });
				}
			}
			return process(s);
		},
		(e, process) => (e.type === 'arrow' || e.type === 'function' || e.type === 'class') ? false : process(e)
	).statements(body);
	return decls;
}

// An identifier, `this`, or a non-optional member/index chain of one: reading it again has no side effect and
// names the same storage both times. A literal is pure only as an INDEX -- a literal BASE (`/re/.lastIndex`) can be a fresh object each read.
export function isPurePath(e: Expr): boolean {
	switch (e.type) {
		case 'identifier':
		case 'this':	return true;
		case 'member':	return !e.optional && isPurePath(e.object);
		// `typeof value !== 'object'` keeps out a regex (fresh each read) and a template's arbitrary sub-expressions.
		case 'index':	return !e.optional && isPurePath(e.object) && (isPurePath(e.index) || (e.index.type === 'literal' && typeof e.index.value !== 'object'));
		default:		return false;
	}
}

// Whether `body` assigns to `this`, which TS never allows: here it means "this method replaces its receiver's physical value"
// (a wasm-GC array or struct cannot resize in place).
export function assignsToThis(body: Stmt[]): boolean {
	return walkerB(undefined, (e, process) => e.type === 'assign' && !e.operator && e.target.type === 'this' ? true : process(e)).statements(body);
}

// A body with zero `return`s normally infers `void` -- but if every path ends in `throw`, real TS infers `never`
// instead, which (unlike `void`) is assignable to any declared return type. Not a full CFG.
function alwaysThrows(stmt: Stmt | undefined): boolean {
	if (!stmt)
		return false;
	switch (stmt.type) {
		case 'throw':	return true;
		case 'block':	return stmt.body.length > 0 && alwaysThrows(stmt.body[stmt.body.length - 1]);
		case 'if':		return !!stmt.alternate && alwaysThrows(stmt.consequent) && alwaysThrows(stmt.alternate);
		case 'try':		return stmt.handlers.every(h => alwaysThrows(h.body[h.body.length - 1])) && alwaysThrows(stmt.body[stmt.body.length - 1]);
		default:		return false;
	}
}

// The test under which no case of `stmt` matched: every case test negated, ANDed; undefined without cases.
function noCaseMatched(stmt: Stmt & { type: 'switch' }): Expr | undefined {
	return stmt.cases.flatMap(c => c.test ? [{ type: 'unary', operator: '!', operand: { type: 'binary', operator: '===', left: stmt.discriminant, right: c.test } } as Expr] : [])
		.reduce<Expr | undefined>((acc, t) => acc ? { type: 'binary', operator: '&&', left: acc, right: t } : t, undefined);
}

// TS's higher-order inference: a generic function argument to a generic call returning a plain function keeps its type parameters, renamed fresh,
// bound in `liftScope` so they resolve with their constraints anywhere; those the result mentions become its own (`wrap(list)` is `<T>(a: T) => T[]`).
function liftGeneric(t: Type, scope: Scope, lifted: TS.TypeParam[], liftScope: Scope): Type {
	const f = T.resolveOwn(t, scope);
	if (f.type !== 'function' || !f.typeParams?.length)
		return t;
	const refs = new Map(f.typeParams.map(p => [p.name, T.withScope(TS.RefType(T.freshTypeParamName(p.name)), liftScope)] as const));
	for (const p of f.typeParams) {
		const param = { ...p, name: refs.get(p.name)!.name, constraint: p.constraint && T.substituteType(p.constraint, refs) };
		liftScope.addTypeParam(param.name, param.constraint ?? T.UNKNOWN);
		lifted.push(param);
	}
	return T.substituteType({ ...f, typeParams: undefined }, refs);
}
const isGenericFunction = (t: Type, scope: Scope) => {
	const f = T.resolveOwn(t, scope);
	return f.type === 'function' && !!f.typeParams?.length;
};
function withLifted(t: Type | undefined, lifted: TS.TypeParam[], scope: Scope): Type | undefined {
	const f		= lifted.length && t ? T.resolveOwn(t, scope) : undefined;
	const used	= f?.type === 'function' ? lifted.filter(p => T.mentionsTypeParam(f, p.name)) : [];
	return used.length ? { ...f as TS.FunctionType, typeParams: used } : t;
}

// A declared callback param is routinely a union (lib.d.ts's `((value: T) => R) | undefined | null` style for nullable
// callbacks, e.g. `Promise.then`) -- dig through it to find the function/constructor alternative.
function resolveFnMember(t: Type, scope: Scope): TS.CallSig | undefined {
	const r = T.resolveOwn(t, scope);
	if (r.type === 'function' || r.type === 'constructor')
		return r;
	if (r.type === 'union') {
		for (const m of r.types) {
			const f = resolveFnMember(m, scope);
			if (f)
				return f;
		}
		return undefined;
	}
	// TS's getIntersectedSignatures (under noImplicitAny): several call signatures (`F & G`, overloads) contextually type as one, each
	// parameter the union of theirs and the result their intersection; a generic or rest one gives no context.
	const sigs = T.signaturesOf(r, 'call', scope);
	if (sigs.length === 1)
		return sigs[0];
	if (sigs.length < 2 || !scope.noImplicitAny() || sigs.some(sig => sig.typeParams?.length || sig.rest))
		return undefined;
	return sigs.reduce((a, b) => {
		const [long, short] = a.params.length >= b.params.length ? [a, b] : [b, a];
		const params = long.params.map((p, i) => ({ ...p, typeAnnotation: T.combineTypes([p.typeAnnotation ?? T.ANY, short.params[i]?.typeAnnotation ?? T.UNKNOWN]) }));
		return T.withScope(TS.FunctionType(JS.Params(params), TS.IntersectionType([a.returnType ?? T.VOID, b.returnType ?? T.VOID])), scope);
	});
}

// TS's const context, standing in for the contextual type `inner`: a literal keeps its literal type, and an array literal is a tuple, readonly
// unless `inner` asks for a mutable array. It travels as the expected type, so `recurseCache` (keyed on node and expected) stays sound.
const constContext = (inner?: Type): TS.RefType => TS.RefType('const', inner ? [inner] : undefined);
export const isConstContext = (t: Type | undefined): t is TS.RefType => t?.type === 'ref' && t.name === 'const' && (t.typeArgs?.length ?? 0) <= 1;
// The context a const context gives an element or property value: its own part of `inner` where TS's isConstContext reaches the
// value (a literal, array or object literal), none past anything else -- a conditional's branches, a call's result are ordinary.
// Inside a const context a literal part stays one; anything else is contextually typed as usual (`Forward(...)` among a `const R`'s elements).
// A literal as TS counts one: a signed number or bigint (`-8`) too.
const isLiteralExpr = (e: Expr): boolean => e.type === 'literal'
	|| (e.type === 'unary' && (e.operator === '-' || e.operator === '+') && e.operand.type === 'literal' && (typeof e.operand.value === 'number' || typeof e.operand.value === 'bigint'));
const constContextOf = (e: Expr, inner: Type | undefined): Type | undefined => isLiteralExpr(e) || e.type === 'array' || e.type === 'object' ? constContext(inner) : inner;
const hasMutableArrayLike = (t: Type, scope: Scope) => T.unionMembers(t, scope).some(m => {
	const r = T.resolveOwn(m, scope);
	return (r.type === 'array' || r.type === 'tuple') && !r.readonly || T.isRef(r, 'Array');
});
// What a contextual tuple gives an element at position `i` (unknown past a variadic spread) or `fromEnd` from the literal's end:
// its fixed element there, else what its rest spreads.
function tupleContextAt(t: Extract<Type, { type: 'tuple' }>, i: number | undefined, fromEnd: number, scope: Scope): Type | undefined {
	const flat = T.flatTupleElements(t, scope), rest = flat.findIndex(e => e.type === 'spread');
	const at = i !== undefined && (rest < 0 || i < rest) ? flat[i] : rest >= 0 && fromEnd < flat.length - rest ? flat[flat.length - fromEnd] : flat[rest];
	return at?.type === 'spread' ? T.arrayLikeElement(T.resolve(scope, at.argument)) : at && T.tupleElementType(at);
}
// What an array-like contextual type gives position `i`: a tuple's element there, an array's element type.
const positionContext = (t: Type, i: number, scope: Scope): Type | undefined => {
	const parts = T.unionMembers(t, scope).flatMap(m => {
		const r = T.resolveOwn(m, scope);
		const el = r.type === 'tuple' ? T.tupleElementType(r.elements[i]) : r.type === 'array' ? r.element
			: r.type === 'ref' && (r.name === 'Array' || r.name === 'ReadonlyArray') ? r.typeArgs?.[0] : undefined;
		return el ? [el] : [];
	});
	return parts.length ? T.combineTypes(parts) : undefined;
};


// An async function's context from a contextual return type: what its PROMISE members promise (TS's `getAwaitedTypeOfPromise`; a
// `StateMachine<T>` beside `Promise<T>` contributes nothing), or a promise of that.
function promisedContext(t: Type, scope: Scope): Type | undefined {
	const promised = T.unionMembers(t, scope).flatMap(m => (p => p ? [p.typeArgs![0]] : [])(T.asPromiseRef(m, scope)));
	return promised.length ? T.awaitContext(T.combineTypes(promised)) : undefined;
}

// A contextual return type is worth handing to a body only when it carries STRUCTURE (an array literal against a tuple becomes a tuple).
// A bare `ref` carries none: an unsolved type parameter of the call being inferred, or a name the body resolves on its own.
function shapedHint(t: Type | undefined, scope: Scope): Type | undefined {
	return t && T.resolveOwn(t, scope).type !== 'ref' ? t : undefined;
}

// TS's getReferenceCandidate: an assignment narrows as what it assigns to (`(x = next()) !== null`), a comma as its last operand.
function referenceOf(e: Expr): Expr {
	return	e.type === 'assign' && (!e.operator || e.operator === '??' || e.operator === '&&' || e.operator === '||') ? referenceOf(e.target)
		:	e.type === 'sequence' ? referenceOf(e.expressions[e.expressions.length - 1])
		:	e;
}

// The member and index reads that are assignment targets, read as declared rather than narrowed: an assignment is judged
// against the declaration (`x['o'] = true` after `x['o'] === false`), also through a destructuring target's leaves.
const assignmentTargets = new WeakSet<Expr>();
function markAssignmentTargets(e: Expr | undefined) {
	if (!e)
		return;
	if (e.type === 'member' || e.type === 'index')
		assignmentTargets.add(e);
	else if (e.type === 'array')
		e.elements.forEach(el => markAssignmentTargets(el?.type === 'spread' ? el.operand : el));
	else if (e.type === 'object')
		e.properties.forEach(p => markAssignmentTargets(p.type === 'spread' ? p.operand : p.type === 'field' ? p.value : undefined));
	else if (e.type === 'assign')
		markAssignmentTargets(e.target);
}

// A callback with an unannotated parameter takes its parameter types from its context (TS's `isContextSensitive`).
function isContextSensitive(a: Expr): a is Expr & { type: 'function' | 'arrow' } {
	return (a.type === 'function' || a.type === 'arrow') && a.params.some(p => !p.typeAnnotation);
}
// What a context-sensitive callback fits as before its context is chosen: any function (TS's `anyFunctionType`).
const ANY_FUNCTION = TS.FunctionType({ params: [], rest: JS.Rest('args', TS.ArrayType(T.ANY)) }, T.ANY);

// A parameter type that is, or through a union may be, an array of TUPLES (Map's `entries?: readonly (readonly [K, V])[] | null`).
function tupleShaped(t: Type, scope: Scope): boolean {
	return T.unionMembers(t, scope).some(m => {
		const r = T.resolveOwn(m, scope);
		const el = r.type === 'tuple' ? r : r.type === 'array' ? r.element : !T.isAny(r) && T.iterationTypes(m, scope)?.yield;
		return !!el && T.resolveOwn(el, scope).type === 'tuple';
	});
}

// The context a non-callback argument is typed in against `sig`'s parameter `declared`: ONE rule for the overload trial and the
// final pass, since a callback nested in the argument keeps the first context it is typed in (`new Map(xs.map(x => [a, b]))`).
function argContext(a: Expr, declared: Type | undefined, sig: TS.CallSig, scope: Scope): Type | undefined {
	if (!declared)
		return undefined;
	// A `const` type parameter (TS 5.0) infers from its argument AS IF it were written `as const`.
	// Its constraint is the contextual type the const context stands in for: `const R extends readonly X[]` is readonly.
	const constParam = declared.type === 'ref' && !declared.typeArgs ? sig.typeParams?.find(p => p.name === declared.name && p.const) : undefined;
	if (constParam)
		return constContext(constParam.constraint);
	// As TS's `getApparentTypeOfContextualType`, a bare type parameter's context is its constraint.
	const bare = declared.type === 'ref' && !declared.typeArgs ? sig.typeParams?.find(p => p.name === declared.name) : undefined;
	if (bare)
		return bare.constraint && argContext(a, bare.constraint, sig, scope);
	// A GENERIC parameter still gives its tuple SHAPE to an array literal or a call (its type params land only as inert per-position
	// hints, so `[[k, v]]` and `xs.map(x => [a, b])` become tuples), and itself to an `as const` argument, which reads only mutability.
	const generic	= !!sig.typeParams?.some(p => T.mentionsTypeParam(declared, p.name));
	const constArg	= a.type === 'as' && isConstContext(a.typeAnnotation);
	// An array literal against `K[]`: its elements' context is the bare type parameter, so a primitive-constrained one keeps their literals
	// (TS's isLiteralOfContextualType: `keys: K[]` with `K extends string` infers `"image"` from `["image"]`).
	const element	= declared.type === 'array' ? declared.element : declared.type === 'ref' && (declared.name === 'Array' || declared.name === 'ReadonlyArray') ? declared.typeArgs?.[0] : undefined;
	if (a.type === 'array' && element?.type === 'ref' && !element.typeArgs && sig.typeParams?.some(p => p.name === element.name))
		return declared;
	if (!generic || constArg || ((a.type === 'array' || a.type === 'call') && tupleShaped(declared, scope)))
		return declared;
	// A generic call's result is inferred from the rest, as TS's non-fixing mapper instantiates it: the parameters still unsolved stand for nothing yet.
	return a.type === 'call' ? T.substituteType(declared, new Map(sig.typeParams!.map(p => [p.name, T.UNKNOWN]))) : undefined;
}

// Whether `args` fit candidate `c` as TS's overload resolution asks (checkExpressionWithContextualType): each argument typed
// against the candidate's OWN parameter, since a literal's type depends on it (`new Map([['', true]])` fits only as tuples).
function candidateFits(c: TS.CallSig, args: Expr[], scope: Scope, typeArgs?: Type[], typedIn = args.map(() => new Map<Type | undefined, Type>()), yieldCollector?: Type[], pos: Location = { line: 0, col: 0 }): boolean {
	const paramAt = (i: number) => T.paramTypeAt(c, i, scope);
	// TS's hasCorrectArity: a spread of unknown length (no tuple) starts past the required parameters, and lands in a rest or optional one (TS2556).
	const spreadAt = args.findIndex(a => a.type === 'spread' && T.resolveOwn(trial(() => typeOf(a.operand, scope, false)), scope).type !== 'tuple');
	if (spreadAt >= 0 && (spreadAt < T.minArgumentCount(c, scope) || (!c.rest && spreadAt >= c.params.length)))
		return false;
	// A callback fits as any function (the chosen candidate fixes its parameters later); every other argument gets the final pass's
	// own context (`argContext`). Muted and unwidened, typed once per distinct context (`typedIn`).
	const ts = args.map((a, i) => {
		if (a.type === 'spread' || isContextSensitive(a))
			return undefined;
		const ctx	= argContext(a, paramAt(i), c, scope);
		let t = typedIn[i].get(ctx);
		if (!t)
			typedIn[i].set(ctx, t = trial(() => typeOf(a, scope, false, ctx, yieldCollector, undefined)));
		return t;
	});
	return T.argsFit(instantiate(c, ts, typeArgs, scope, pos), args.map((a, i) => isContextSensitive(a) ? ANY_FUNCTION : ts[i]), scope, args.some(a => a.type === 'spread'));
}

// Contextual parameter typing: fills an unannotated callback's params from `expected`'s, mutating the AST before its body is checked.
// Returns the contextual signature, whose RETURN type the body needs too (`xs.map(x => [a, b])` against `[K, V][]`).
// What `applyContextualParams` wrote is its context's, not source: an instance of a generic body (codegen's `substituteTypeParams`) drops it and re-derives.
export type Contextual = { contextual?: true };

function applyContextualParams(fn: { params: JS.Param<Type>[]; typeParams?: TS.TypeParam[] }, expected: Type | undefined, scope: Scope) {
	const params	= fn.params;
	// TS's isAritySmaller: a signature with fewer parameters than the callback REQUIRES gives it no context at all -- an overload
	// trial with `(req1: string) => void` must not type `(req, res) => ...`, which only the two-parameter overload fits.
	const required	= params.findIndex(p => !!p.default || hasMod(p, 'optional'));
	const found		= expected && resolveFnMember(expected, scope);
	const sig		= found && (found.rest || found.params.length >= (required < 0 ? params.length : required)) ? found : undefined;
	if (sig) {
		// Past the fixed parameters the REST's ELEMENT is the context (`(_, a, b) => ...` against `(s: string, ...args: any[])`). Written shape first:
		// resolving `Array<T>` expands it to the class's object shape and loses the element.
		const restAnn	= sig.rest?.typeAnnotation;
		const asArray	= (t: Type | undefined) => t && t.type === 'array' ? t.element
			: t && t.type === 'ref' && t.name === 'Array' && t.typeArgs?.length === 1 ? t.typeArgs[0] : undefined;
		const restElem	= asArray(restAnn) ?? asArray(restAnn && T.resolveOwn(restAnn, scope));
		// An omittable contextual parameter (`x?: T`, or one with a default) is `T | undefined` to the callback, as in TS.
		const contextual = (c: JS.Param<Type> | undefined) => c?.typeAnnotation && (hasMod(c, 'optional') || c.default)
			? T.combineTypes([c.typeAnnotation, T.UNDEFINED]) : c?.typeAnnotation;
		// A generic context makes the function generic too (TS's contextual signature instantiation): its parameters name the context's.
		const adopt = !!sig.typeParams?.length && !fn.typeParams?.length && params.some(p => !p.typeAnnotation);
		if (adopt) {
			written(fn, 'typeParams');
			written(fn as Contextual, 'contextual');
			fn.typeParams = sig.typeParams;
			(fn as Contextual).contextual = true;
		}
		// Stamped where it is written: a name the context spells unqualified (`put<TypedArray>`) is this module's, wherever the type is read later.
		params.forEach((p, j) => {
			if (!p.typeAnnotation) {
				written(p, 'typeAnnotation');
				written(p as Contextual, 'contextual');
				p.typeAnnotation = (t => t && T.stampScope(t, scope))(contextual(sig.params[j]) ?? restElem);
				(p as Contextual).contextual = true;
			}
		});
	}
	return sig || undefined;
}

// Whether `e` is a link in an ACTIVE optional chain: itself a `?.` step, or continuing one through its receiver (`a?.b.c`), as TS short-circuits
// a contiguous chain. Shared with wasm-backend.ts's codegen, so the two agree on what is still the same chain.
export function isOptionalChainLink(e: Expr): boolean {
	if (e.type === 'member' || e.type === 'index')
		return !!e.optional || isOptionalChainLink(e.object);
	if (e.type === 'call')
		return !!e.optional || isOptionalChainLink(e.callee);
	return false;
}



function narrowMath(func: string, params: TS.Param[], scope: Scope): Type | undefined {
	const rangeOf = (p?: TS.Param) => p?.typeAnnotation && numericSlot(p.typeAnnotation, scope);
	switch (func) {
		case 'random':
			return T.rangeToType({ base: 'number', min: 0, max: 1, integer: false });
		case 'max': {
			const all = params.map(rangeOf);
			return all.every(i => !!i) ? T.rangeToType(T.rangeMax(all)) : undefined;
		}
		case 'min': {
			const all = params.map(rangeOf);
			return all.every(i => !!i) ? T.rangeToType(T.rangeMin(all)) : undefined;
		}
	}

	const mr = rangeOf(params[0]);
	if (mr) {
		switch (func) {
			case 'abs':
			case 'sqrt':	//> 0
			case 'exp':		return T.rangeToType({ ...mr, min: 0 });

			case 'ceil':
			case 'floor':
			case 'round':	return T.rangeToType({ ...mr, integer: true });

			case 'acos':	return T.rangeToType({ ...mr, min: 0, max: Math.PI });
			case 'asin':
			case 'atan':	return T.rangeToType({ ...mr, min: -Math.PI / 2, max: Math.PI / 2 });
			case 'atan2':	return T.rangeToType({ ...mr, min: -Math.PI, max: Math.PI });

			case 'cos':
			case 'sin':		return T.rangeToType({ ...mr, min: -1, max: 1 });

		}
	}
}


// A body check infers what a parameter's default or pattern says, writing it onto the DECLARATION after the signature was copied:
// `FixParams` reads the declaration again.
function refreshParams(sig: TS.CallSig, decl: JS.CallSig<any>) {
	T.FixParams(decl).params.forEach((p, i) => {
		if (sig.params[i] && !sig.params[i].typeAnnotation) {
			written(sig.params[i], 'typeAnnotation');
			sig.params[i].typeAnnotation = p.typeAnnotation;
		}
	});
}

// An unannotated body's `sig.returnType` as a self-memoizing accessor: the first read infers it (muted) and replaces itself, recorded on `decl` too.
// While inferring it reads as absent; a recursive call's reader falls back to `any`, as TS types such a recursion.
function lazyReturnType(sig: TS.CallSig, decl: { returnType?: Type }, scope: Scope, infer: () => void, fold = (t: Type) => t) {
	let resolving = false;
	(selfUndoing.get(sig) ?? selfUndoing.set(sig, new Set()).get(sig)!).add('returnType');
	Object.defineProperty(sig, 'returnType', {
		configurable: true,
		enumerable: true,
		get(): Type | undefined {
			if (resolving)
				return undefined;
			resolving = true;
			infer();
			resolving = false;
			return sig.returnType ?? T.ANY;
		},
		// Stamped here, not at the read site, so it happens exactly once whoever triggers inference.
		set(value: Type | undefined) {
			if (value)
				T.stampScope(value = fold(value), scope);
			// Undone by reinstalling the accessor: an inference a speculative walk made must not outlive it.
			selfUndoing.get(sig)!.delete('returnType');
			aheadLog?.push(() => lazyReturnType(sig, decl, scope, infer, fold));
			written(decl, 'returnType');
			Object.defineProperty(sig, 'returnType', { value, writable: true, configurable: true, enumerable: true });
			decl.returnType = value;
		},
	});
}

// The scopes a class's member bodies are checked in: instance members see `this` as the instance and the class's type params, static ones the constructor.
function classBodyScopes(c: TS.Class, scope: Scope, instance: Type, value: Type, superType?: Type): { inst: Scope; stat: Scope } {
	// A generic class's instance scope is flagged (`Scope.isGenericTemplate`): its method bodies are one template shared by every instantiation.
	// A generic class's instantiation (`instanceOfClass`) has its type arguments substituted already: `this` is that instance, and no parameter is left to bind.
	const instanceOf	= instanceOfClass(c);
	const typeParams	= instanceOf ? [] : c.typeParams ?? [];
	const inst			= new Scope(scope, !!typeParams.length);
	// The polymorphic `this` type, so `return this` infers `this` and each call substitutes its receiver (TS's fluent `this`).
	// Its class prefers the named entry: declaration merging can extend it beyond this declaration's shape.
	inst.addValue('this', { type: 'this', of: instanceOf ?? (c.name && scope.type(c.name) ? TS.RefType(c.name, c.typeParams?.map(p => TS.RefType(p.name))) : instance) });
	// `addTypeParam`, as `checkFunctionBody` registers its own: an unregistered `K` stays opaque to every member read through it.
	for (const p of typeParams)
		inst.addTypeParam(p.name, p.constraint ?? T.UNKNOWN);
	// `typeof C` when named, as TS types it: the structural value holds this very member, so a static `return this` would make a cyclic type.
	const stat = new Scope(scope);
	stat.addValue('this', c.name && scope.value(c.name) ? { type: 'typeof', name: c.name } : value);
	// `super`: the base's instance side in an instance member, its static side in a static one. `super(...)` invokes the base
	// CONSTRUCTOR instead, so the static side is bound for it too, under a key no identifier can spell.
	if (superType) {
		const staticSide: Type = superType.type === 'ref' && scope.value(superType.name) ? { type: 'typeof', name: superType.name } : T.ANY;
		inst.addValue('super', superType);
		inst.addValue('super()', staticSide);
		stat.addValue('super', staticSide);
	}
	inst.flowBoundary = stat.flowBoundary = isClassDecl(c);
	return { inst, stat };
}

const isClassDecl = (c: TS.Class) => 'type' in c && c.type === 'class_decl';

function flowContainer(scope: Scope): Scope {
	const s = new Scope(scope);
	s.flowBoundary = true;
	return s;
}

// A non-arrow function's body: its own `this`, which TS types `any` absent a `this:` parameter (`checkFunctionBody` binds one), never the
// enclosing method's. An arrow keeps the enclosing `this`, so it does not come through here.
function ownThis(scope: Scope): Scope {
	scope.addValue('this', T.ANY);
	return scope;
}

// `instance` is `new C(...)`/`this`'s type; `value` the class binding's (construct signature and statics); `superType` the base's instance side.
function classShapes(c: TS.Class, scope: Scope): { instance: Type; value: Type; superType?: Type } {
	const members:			TS.TypeMember[] = [];
	const staticMembers:	TS.TypeMember[] = [];
	const ctorMembers:		TS.ClassMethod[] = [];

	// A field's lazy-inference getter is installed only after this function's `stampScope` walk, or that walk would be its first read, inferring
	// mid-`hoist`, before later declarations are hoisted.
	const pendingFieldInit: { prop: TS.TypeMember; init: Expr | Expr[]; inner?: Scope }[] = [];
	// A field with neither annotation nor initializer is typed by the constructor's `this.x = ...`, which may come later in `c.body`.
	const pendingCtorInit: { prop: TS.TypeMember; key: string }[] = [];
	// Unannotated method/getter bodies: their return types are inferred lazily, like a hoisted function's (`lazyReturnType`).
	const pendingReturns: { sig: TS.CallSig; decl: TS.ClassMethod }[] = [];

	// A member with overload signatures (bodyless) hides its implementation's own signature, as TS does: only the overloads are callable.
	const overloaded = new Set(c.body.flatMap(m => m.type === 'method' && !m.body ? [T.memberKey(m.key)] : []));
	for (const m of c.body) {
		if (m.type === 'index_signature') {
			members.push(TS.TypeIndex(m.paramName, m.paramType, m.typeAnnotation));
			continue;
		}
		if (m.type === 'method' && m.body && m.key !== 'constructor' && overloaded.has(T.memberKey(m.key)))
			continue;
		const key = 'key' in m && T.memberKey(m.key);
		if (key === undefined || key === false)
			continue;

		const list = hasMod(m, 'static') ? staticMembers : members;
		switch (m.type) {
			case 'field': {
				// No annotation: a literal initializer's widened type, as TS infers a field; anything else is queued in `pendingFieldInit`.
				const lit = m.typeAnnotation ? undefined : T.literalTypeOf(m.value);
				if (!m.typeAnnotation && !m.value && !hasMod(m, 'static')) {
					// `x;` -- real TS infers such a field from the assignments its own constructor makes to it.
					const prop = TS.TypeProperty(m.key, T.ANY, m.modifiers);
					pendingCtorInit.push({ prop, key });
					list.push(prop);
				} else if (m.typeAnnotation || lit || !m.value) {
					list.push(TS.TypeProperty(m.key, m.typeAnnotation ?? (lit && T.widenLiterals(lit)) ?? T.ANY, m.modifiers));
				} else {
					const prop = TS.TypeProperty(m.key, T.ANY, m.modifiers);
					pendingFieldInit.push({ prop, init: m.value });
					list.push(prop);
				}
				break;
			}
			case 'method':
				if (m.key === 'constructor') {
					// An overloaded constructor's implementation still declares its parameter properties, but not a signature.
					if (!(m.body && overloaded.has('constructor')))
						ctorMembers.push(m);
					for (const p of m.params)
						if (T.isParamProperty(p) && typeof p.key === 'string')
							// The PARAMETER's modifiers: `public b?: P` declares an optional property, unless a default always assigns it.
							members.push(TS.TypeProperty(p.key, p.typeAnnotation ?? T.literalTypeOf(p.default) ?? T.ANY, p.default ? p.modifiers.filter(x => x !== 'optional') : p.modifiers));
				} else {
					const member = TS.TypeMethod(m.key, T.withScope({ ...T.FixSig(m, T.ANY), origin: m }, scope), m.modifiers);
					list.push(member);
					if (!m.returnType && m.body)
						pendingReturns.push({ sig: member, decl: m });
				}
				break;
			case 'get': {
				const prop = TS.TypeProperty(m.key, m.returnType ?? T.ANY);
				list.push(prop);
				if (!m.returnType && m.body) {
					const sig = T.FixSig(m, T.ANY);
					pendingReturns.push({ sig, decl: m });
					Object.defineProperty(prop, 'typeAnnotation', { get: () => sig.returnType, configurable: true, enumerable: true });
				}
				break;
			}
			case 'set':
				list.push(TS.TypeSetter(m.key, m.params[0]?.typeAnnotation ?? T.ANY));
				break;
		}
	}
	TS.mergeAccessors(members);
	TS.mergeAccessors(staticMembers);
	// Every `this.<key> = <expr>` at the top level of the constructor body; not a nested closure's, which runs who knows when.
	for (const { prop, key } of pendingCtorInit) {
		for (const ctor of c.body.filter((m): m is TS.ClassMethod => m.type === 'method' && m.key === 'constructor' && !!m.body)) {
			const inits = (ctor.body ?? []).flatMap(st =>
				st.type === 'expression' && st.expression.type === 'assign' && !st.expression.operator
				&& st.expression.target.type === 'member' && st.expression.target.object.type === 'this' && st.expression.target.property === key
					? [st.expression.value] : []);
			if (!inits.length)
				continue;
			// `this.p = o` names the CONSTRUCTOR's parameter, unknown to the class scope.
			const inner = new Scope(scope);
			inner.flowBoundary = isClassDecl(c);
			for (const p of T.FixParams(ctor).params)
				if (typeof p.key === 'string')
					inner.addValue(p.key, p.typeAnnotation ?? T.ANY);
			pendingFieldInit.push({ prop, init: inits, inner });
		}
	}

	const obj = TS.ObjectType(members);
	// A base the checker can't name (a mixin call) leaves the instance unsealed; likewise an inherited constructor accepts any arguments.
	// Own members come first: lookupMember's first match implements override precedence
	// A base naming no type is a VALUE (a lifted heritage call, `liftClassHeritage`): its construct signature's instance, typed when first needed.
	const superRef	= superClassRef(c.superClass);
	const superType: Type | undefined = superRef && !superRef.typeArgs && !superRef.name.includes('.') && !scope.type(superRef.name)
		? T.stampScope(TS.RefType('InstanceType', [{ type: 'typeof', name: superRef.name }]), scope)
		: superRef ?? (c.superClass && T.ANY);
	const instance		= superType ? { ...TS.IntersectionType([obj, superType]), derived: true } : obj;
	// The named ref carries its own type params as type arguments (`new(...): Box<T>`), or `new Box<number>(...)` has none.
	const ctorReturn	= c.name ? TS.RefType(c.name, c.typeParams?.map(p => TS.RefType(p.name))) : instance;
	const makeCtorSig	= (params: TS.Params) => T.withScope(TS.CallSig(params, ctorReturn, c.typeParams), scope);
	// Several constructor bodies are an overload set, the same multi-signature shape `lookupMember` builds for methods.
	const ctor: Type = ctorMembers.length > 1
		? TS.ObjectType(ctorMembers.map(m => TS.TypeConstruct({ ...makeCtorSig(T.FixParams(m)), origin: m })))
		: { type: 'constructor', ...makeCtorSig(ctorMembers.length ? T.FixParams(ctorMembers[0]) : {params: [], rest: c.superClass ? JS.Rest('args', TS.ArrayType(T.ANY)) : undefined}) };
	// TS's mixin rule: a class extending a value typed by a type parameter (`base: T`) is also a `T`.
	const baseValue	= c.superClass?.type === 'identifier' ? scope.value(c.superClass.name) : undefined;
	const mixin		= baseValue && T.typeParamConstraint(baseValue, scope) ? [baseValue] : [];
	const own		= staticMembers.length ? [ctor, TS.ObjectType(staticMembers)] : [ctor];
	const value		= own.length + mixin.length > 1 ? TS.IntersectionType([...own, ...mixin]) : ctor;
	T.stampScope(instance, scope);
	T.stampScope(value, scope);

	// A member's inferred type naming its own class's shape (`static make() { return A; }`) names it as TS does (`typeof A`, `A`):
	// the shape holds that very member, so embedding the shape itself would make the type cyclic.
	const selfRefs = (t: Type): Type => {
		const name = c.name;
		if (!name || !walkerB(undefined, undefined, (x, process) => x === value || x === instance || process(x)).type(t))
			return t;
		return walker(undefined, undefined, (x, process) => x === value ? { type: 'typeof', name } : x === instance ? ctorReturn : process(x)).type(t) ?? t;
	};

	// Installed only now, after the walks above.
	for (const { prop, init, inner } of pendingFieldInit) {
		const initScope = inner ?? (isClassDecl(c) ? flowContainer(scope) : scope);
		let resolving = false;
		Object.defineProperty(prop, 'typeAnnotation', {
			configurable:	true,
			enumerable:		true,
			get(): Type {
				if (resolving)
					return T.ANY;
				resolving = true;
				const raw = Array.isArray(init)
					? T.combineTypes(init.map(e => typeOf(e, initScope) ?? T.ANY))
					: typeOf(init, initScope) ?? T.ANY;
				const t = T.stampScope(T.widenNullish(T.widenLiterals(selfRefs(raw)), scope), scope);
				Object.defineProperty(prop, 'typeAnnotation', { value: t, writable: true, enumerable: true, configurable: true });
				return t;
			},
		});
	}
	let bodyScopes: { inst: Scope; stat: Scope } | undefined;
	for (const { sig, decl } of pendingReturns) {
		lazyReturnType(sig, decl, scope, () => {
			bodyScopes ??= classBodyScopes(c, scope, instance, value, superType);
			const generator = hasMod(decl, 'generator');
			// The DECLARATION, not `sig`: `FixParams` flattens a destructuring parameter to `_`, which would leave the names it binds unbound.
			checkFunctionBody(decl, decl.body, hasMod(decl, 'static') ? bodyScopes.stat : bodyScopes.inst, hasMod(decl, 'async'), generator, generator);
			refreshParams(sig, decl);
			sig.returnType = decl.returnType;
		}, selfRefs);
	}
	return { instance, value, superType };
}

// ---- control-flow narrowing -----------------------------------------------------------------



// Depth of the `narrow()` calls on the stack. `narrow` types a test's operands, and its disjunctive case passes the UNnarrowed scope on, so a
// stamp taken inside it would freeze a speculative answer (`??=` first-wins).
let narrowing = 0;
// An overload TRIAL is speculative the same way: a nested call typed against a candidate that loses must not stamp its resolution.
let trying = 0;
function trial<R>(f: () => R): R {
	++trying;
	try {
		return f();
	} finally {
		--trying;
	}
}
// A declaration typed ahead of its statement is walked while earlier ones are still placeholders, so nothing that walk writes onto the
// AST may stay: each write's prior property is restored after it.
let aheadLog: (() => void)[] | undefined;
// Keys held by an accessor that records its own undo (`lazyReturnType`): `written` leaves them to it, since reading one would run it.
const selfUndoing = new WeakMap<object, Set<string>>();
function written<O extends object>(o: O, key: keyof O & string) {
	if (!aheadLog || selfUndoing.get(o)?.has(key))
		return;
	// What the key held, or that it held nothing: the node's own data properties are all a speculative walk writes.
	const had = key in o, prior = o[key];
	aheadLog.push(() => {
		if (had)
			o[key] = prior;
		else
			delete o[key];
	});
}
function ahead<R>(f: () => R): R {
	const outer = aheadLog;
	aheadLog = [];
	try {
		return trial(f);
	} finally {
		aheadLog.reverse().forEach(undo => undo());
		aheadLog = outer;
	}
}

// A ternary's or `&&`/`||`'s branch scope, stamped on the BRANCH node, where no statement boundary exists. Not in a generic class's method
// (`isGenericTemplate`): one template serves every instantiation, and a first-wins stamp would block the per-instantiation scope.
function stampBranch(branch: Expr, branchScope: Scope, scope: Scope) {
	if (!narrowing && !trying && branchScope !== scope && !scope.isGenericTemplate() && !scope.isQuiet())
		(branch as any).scope ??= branchScope;
}

// Whether any of `names` is written anywhere in `body`: an assignment, or `++`/`--` on either side.
function writesAny(body: JS.Stmt<any>[] | Expr, names: Set<string>): boolean {
	let found = false;
	walkerB(undefined, (x: any, process: (x: any) => boolean) => {
		if ((x.type === 'assign' && x.target.type === 'identifier' && names.has(x.target.name))
			|| ((x.type === 'unary' || x.type === 'unary_post') && (x.operator === '++' || x.operator === '--') && x.operand.type === 'identifier' && names.has(x.operand.name)))
			found = true;
		return found || process(x);
	}).body(body);
	return found;
}


// A statement's stamp is its scope's state at the START: an assignment narrowing (its own, or a later statement's on the same live scope) would
// otherwise read back as the later type (`asm.some(...)` before `asm = asm.map(...).join('')`). So the narrowings are copied whenever there are any.
function stampedScope(s: Stmt, scope: Scope): Scope {
	const frozen = new Scope(scope);
	frozen.snapshot = true;
	for (const name of scope.narrowedNames()) {
		const t = scope.value(name);
		if (t)
			frozen.addNarrowing(name, t);
	}
	return frozen;
}
// A name destructured from a union narrows as its source path (`kind` as `x.kind`), so the rest of `x` narrows with it.
function throughSources(e: Expr, scope: Scope): Expr {
	if (e.type === 'identifier')
		return scope.source(e.name) ?? e;
	const out: any = { ...e };
	for (const k of ['left', 'right', 'operand', 'object', 'expression'])
		if (out[k] && typeof out[k] === 'object' && 'type' in out[k])
			out[k] = throughSources(out[k], scope);
	if (Array.isArray(out.arguments))
		out.arguments = out.arguments.map((a: any) => a && a.type !== 'spread' ? throughSources(a, scope) : a);
	return out;
}

// A string literal's value, or a template literal's with no substitutions (`` `number` ``).
function staticText(e: Expr): string | undefined {
	return e.type !== 'literal' ? undefined
		: typeof e.value === 'string' ? e.value
		: Array.isArray(e.value) && e.value.every(p => !p.exp) ? e.value.map(p => p.str).join('')
		: undefined;
}

// `e` (holding when `sense`) as "`typeof operand` is not `kind`", or undefined.
function typeofExclusion(e: Expr, sense: boolean): { operand: Expr; kind: string } | undefined {
	if (e.type !== 'binary' || !['===', '==', '!==', '!='].includes(e.operator))
		return undefined;
	const [t, k] = e.left.type === 'unary' && e.left.operator === 'typeof' ? [e.left, e.right] : [e.right, e.left];
	const kind = staticText(k);
	return (e.operator === '===' || e.operator === '==') !== sense && t.type === 'unary' && t.operator === 'typeof' && kind !== undefined ? { operand: t.operand, kind } : undefined;
}

// TS's subtype reduction of an inferred return, where two object-like returns relate both ways (`{v: any}` and `{v: unknown}`): the first stands for both.
function equivalentsOnce(types: Type[], scope: Scope): Type[] {
	const objectLike = (t: Type) => ['object', 'intersection', 'array', 'tuple', 'function'].includes(T.resolveOwn(t, scope).type);
	return types.filter((t, i) => !objectLike(t) || !types.slice(0, i).some(u => objectLike(u) && T.isAssignable(t, u, scope) && T.isAssignable(u, t, scope)));
}

// The type `typeof x === kind` proves: `object` includes `null` unless the value is known non-nullish.
function kindType(kind: string, nullable: boolean): Type {
	return kind === 'object' ? (nullable ? T.combineTypes([TS.RefType('object'), Literal(null)]) : TS.RefType('object')) : kind === 'function' ? TS.RefType('Function') : TS.RefType(kind);
}

// Every result `typeof` can give for a value of `m`: a non-primitive `object` may be a function. Undefined when unknown.
function typeofNames(m: Type, scope: Scope): string[] | undefined {
	const name = T.typeofName(m, scope);
	return name ? [name] : T.isRef(T.resolveOwn(m, scope), 'object') ? ['object', 'function'] : undefined;
}

// What survives of `m` once `typeof` is among `kinds` (`inside`) or not: kept, dropped, or refined (`object` to its `Function` part,
// `unknown`/`{}` to the kind's type). A type parameter follows its constraint where that decides, else is `T & kind`, as in TS.
function narrowByTypeof(m: Type, kinds: Set<string>, inside: boolean, scope: Scope): boolean | Type {
	const [kind]	= kinds;
	const bound		= T.typeParamConstraint(m, scope);
	if (bound) {
		const members	= T.unionMembers(bound, scope);
		const cs		= members.map(b => narrowByTypeof(b, kinds, inside, scope));
		return cs.every(c => c === false) ? false
			: !inside ? (kinds.has('undefined') && T.nonNullableParam(m, scope)) || true
			: cs.every((c, i) => c === true && typeofNames(members[i], scope)) ? true
			: T.combineTypes(T.unionMembers(kindType(kind, true), scope).map(k => TS.IntersectionType([m, k])));
	}
	const r = T.resolveOwn(m, scope);
	const empty = r.type === 'object' && !r.members.length;
	if (inside && kinds.size === 1 && (empty || T.isRef(r, 'unknown')))
		return empty && kind === 'undefined' ? false : kindType(kind, !empty);
	const names = typeofNames(m, scope);
	const left = names?.filter(n => kinds.has(n) === inside);
	return !names || left!.length === names.length ? true : !left!.length ? false : left!.includes('function') ? TS.RefType('Function') : true;
}

// A scope refined by `test` holding (`sense`) or failing: truthiness, `!`, `&&`/`||`, typeof, nullish comparisons, discriminants, instanceof, `in`,
// type predicates. Pure: an unstamped branch (`stampBranch`) re-derives the same scope.
export function narrow(test: Expr, scope: Scope, sense: boolean): Scope {
	const aliasing = new Set<string>();
	++narrowing;
	try {
		return recurse(scope.hasSources() ? throughSources(test, scope) : test, scope, sense);
	} finally {
		--narrowing;
	}

	// Refines `name`'s binding (maybe a dotted path key) to the members `keep` accepts: `true` keeps, `false` excludes, a `Type` replaces
	// (splitting a compound member, `narrowByDiscriminant`).
	function narrowValue(scope: Scope, name: string, keep: (m: Type) => boolean | Type, t = scope.value(name)): Scope {
		const r = t && T.resolveOwn(t, scope);
		if (!r || T.isRef(r, 'any'))
			return scope;
		if (r.type !== 'union') {
			const k = keep(r);
			if (k !== true) {
				const s = new Scope(scope);
				s.addNarrowing(name, k === false ? TS.RefType('never') : k);
				return s;
			}
			return scope;
		}
		// A member may resolve to further nested unions, several aliases deep: flattened, so a discriminant filters at the right granularity.
		// Each keeps its ORIGINAL form beside the resolved one: a kept member stays its clean ref, which later generic inference needs.
		const flatten = (m: Type): { resolved: Type; orig: Type }[] => {
			const resolved = T.resolveOwn(m, scope);
			return resolved.type === 'union' ? resolved.types.flatMap(flatten) : [{ resolved, orig: m }];
		};
		const candidates = r.types.flatMap(flatten);
		const parts: Type[] = [];
		let changed = false;
		for (const { resolved, orig } of candidates) {
			const k = keep(resolved);
			if (k !== false)
				parts.push(k === true ? orig : k);
			if (k !== true)
				changed = true;
		}
		if (changed) {
			// No member left narrows to `never`, so disjunctive narrowing can tell "excludes everything" from "didn't narrow".
			const s = new Scope(scope);
			s.addNarrowing(name, parts.length ? T.combineTypes(parts) : TS.RefType('never'));
			return s;
		}
		return scope;
	}


	// Narrows `name` to `target`: union members are filtered by assignability; a non-union binding (or any binding, for an opaque `any` target)
	// is replaced outright when the guard holds. `name` may be a dotted path key.
	function narrowTo(scope: Scope, name: string, target: Type, sense: boolean, t = scope.value(name)): Scope {
		const r = t && T.resolveOwn(t, scope);
		// A guard narrows `unknown`, and `any` too unless it names `Object`/`Function`; an `any` target says nothing to narrow to.
		if (!r || (T.isAny(r) && (!sense || T.isAny(target) || (T.isRef(r, 'any') && (T.isRef(target, 'Object') || T.isRef(target, 'Function'))))))
			return scope;
		// Already strictly narrower than the guard (`C extends A` under `x is A`): kept, as TS's getNarrowedType does. A NULLISH member never is:
		// under non-strict rules `undefined` is assignable to everything, and the true branch says the value is not nullish.
		const narrower = (m: Type) => !T.isAny(target) && !T.isNullish(m, scope) && T.isAssignable(m, target, scope) && !T.isAssignable(target, m, scope, scope, false, 10, true);
		// A matching member narrows to `target` itself, which says more than its declared type (`Literal<TypeOfMap[K]>` pinning `.value`);
		// a member WIDER than the target (`Lit<string | number>` under `Lit<string>`) narrows to it too, as in TS.
		const direct = (m: Type) => narrower(m) ? m : T.isAssignable(m, target, scope) || T.isAssignable(target, m, scope) ? target : false;
		// Where no member relates to the target directly, a type parameter's value is both, as TS narrows it (`T & C`): it keeps `T`'s identity.
		const generic = (m: Type) => !T.isAny(target) && !!T.typeParamConstraint(m, scope) && TS.IntersectionType([m, target]);
		if (r.type === 'union' && !T.isAny(target))
			// Excluding a member (the false branch) takes the EXACT relation: the lenient widened-source rule would count a `string` as a `"never"`.
			return narrowValue(scope, name, !sense ? m => !T.isAssignable(m, target, scope, scope, false, 10, true)
				: T.unionMembers(r, scope).some(m => direct(m) !== false) ? direct : generic, t);
		if (!sense || narrower(r))
			return scope;
		const s = new Scope(scope);
		s.addNarrowing(name, direct(r) === false && generic(t) || target);
		return s;
	}


	function nonNullChainRoots(e: Expr, scope: Scope): Scope {
		for (let x: Expr = e; x.type === 'member' || x.type === 'index' || x.type === 'call'; x = x.type === 'call' ? x.callee : x.object) {
			const root = x.optional ? (x.type === 'call' ? x.callee : x.object) : undefined;
			const key = root && T.pathKey(root);
			if (key)
				scope = narrowValue(scope, key, m => !T.isNullish(m, scope), scope.value(key) ?? typeOf(root!, scope, false));
		}
		return scope;
	}

	function recurse(test: Expr, scope: Scope, sense: boolean): Scope {
		// A truthy optional chain (`a?.b.c(x)`) has every object before a `?.` non-nullish (a nullish one short-circuits to `undefined`); only the
		// truthy branch knows it.
		if (sense && (test.type === 'member' || test.type === 'index' || test.type === 'call'))
			scope = nonNullChainRoots(test, scope);
		// A truthy `unknown` is `{}`, as TS narrows it: anything but `null`/`undefined`.
		const truthy: (m: Type) => boolean | Type = sense ? m => T.isRef(m, 'unknown') ? TS.ObjectType([]) : T.nonNullableParam(m, scope) ?? !T.isFalsy(m, scope) : m => !T.isTruthy(m, scope);
		const narrowKey = (target: Expr, keep: (m: Type) => boolean | Type, base = scope) => {
			const key = T.pathKey(referenceOf(target));
			return key ? narrowValue(base, key, keep, base.value(key) ?? typeOf(target, base, false)) : undefined;
		};

		switch (test.type) {
			case 'unary':
				return test.operator === '!' ? recurse(test.operand, scope, !sense) : scope;
			case 'unary_post'://only for '!'?
				return recurse(test.operand, scope, sense);
			case 'identifier': {
				const s		= narrowValue(scope, test.name, truthy);
				const alias = aliasing.has(test.name) ? undefined : scope.alias(test.name);
				if (!alias)
					return s;
				aliasing.add(test.name);
				try {
					return recurse(alias, s, sense);
				} finally {
					aliasing.delete(test.name);
				}
			}
			// Truthiness narrows a dotted property path (`if (icon.color)`), keyed by the whole path.
			case 'member': {
				const key		= T.pathKey(test);
				const narrowed	= key ? narrowValue(scope, key, truthy, scope.value(key) ?? typeOf(test, scope, false)) : scope;
				// ...and the union holding it, by TS's discriminant rule: a member whose property can never pass the test goes
				// (`if (c.errors) return;` drops `{errors: E[]}` and keeps `{errors?: never}`).
				const objKey	= T.pathKey(referenceOf(test.object));
				const objT		= objKey && (narrowed.value(objKey) ?? typeOf(test.object, narrowed, false));
				if (!objT || T.resolveOwn(objT, narrowed).type !== 'union')
					return narrowed;
				return narrowValue(narrowed, objKey, m => {
					const p = T.lookupMember(m, test.property, narrowed);
					return !p || T.unionMembers(T.optional(p, T.memberOptional(m, test.property, narrowed)), narrowed).some(truthy);
				}, objT);
			}
			// `if ((x = e))` narrows `x` by truthiness, as `if (a[i])` does its element.
			case 'index':
			case 'assign':
			case 'sequence':
				return narrowKey(test, truthy) ?? scope;

			case 'binary': {
				// `a && b`'s true branch / `a || b`'s false branch: both conjuncts hold (or fail), each narrowing on top of the other.
				if ((test.operator === '&&' && sense) || (test.operator === '||' && !sense)) {
					// A conjunction's `typeof` exclusions on one reference apply TOGETHER, as TS narrows `switch (typeof x)`: `object` goes only once both
					// 'object' and 'function' are excluded.
					const parts: [Expr, boolean][] = [];
					const flatten = (e: Expr, s: boolean): void => {
						if (e.type === 'binary' && ((e.operator === '&&' && s) || (e.operator === '||' && !s))) {
							flatten(e.left, s);
							flatten(e.right, s);
						} else if (e.type === 'unary' && e.operator === '!') {
							flatten(e.operand, !s);
						} else {
							parts.push([e, s]);
						}
					};
					flatten(test, sense);
					const excluded = new Map<string, { operand: Expr; kinds: Set<string> }>();
					const unrelated = parts.filter(([e, s]) => {
						const x = typeofExclusion(e, s);
						const key = x && T.pathKey(referenceOf(x.operand));
						if (!x || !key)
							return true;
						const group = excluded.get(key) ?? { operand: x.operand, kinds: new Set<string>() };
						group.kinds.add(x.kind);
						excluded.set(key, group);
						return false;
					});
					let narrowed = scope;
					for (const { operand, kinds } of excluded.values())
						narrowed = narrowKey(operand, m => narrowByTypeof(m, kinds, false, scope), narrowed) ?? narrowed;
					for (const [e, s] of unrelated)
						narrowed = recurse(e, narrowed, s);
					return narrowed;
				}
				// `a || b`'s true branch: one disjunct holds, so a variable BOTH sides narrow (`typeof icon === 'string' || icon instanceof Uri`) narrows to the
				// union of the two.
				if ((test.operator === '||' && sense) || (test.operator === '&&' && !sense)) {
					const left = recurse(test.left, scope, sense), right = recurse(test.right, scope, sense);
					// Only when NEITHER side narrows: `left === scope` alone cannot tell "vacuously true" from "unreachable".
					if (left === scope && right === scope)
						return scope;
					const names = left.narrowedNames(scope);
					for (const name of right.narrowedNames(scope))
						names.add(name);
					let s = scope;
					for (const name of names) {
						const lt = left.value(name), rt = right.value(name);
						if (lt && rt) {
							s = new Scope(s);
							s.addNarrowing(name, T.combineTypes([lt, rt]));
						}
					}
					return s;
				}
				const eq = test.operator === '===' || test.operator === '==';
				if (eq || test.operator === '!==' || test.operator === '!=') {
					const keepMatch	= eq === sense;		// keep the members that match the compared value
					const loose		= test.operator === '==' || test.operator === '!=';
					// The compared value when it is one unit type: a literal, or a name typed as one (`Kind.A`, a `const k = 'a'`) -- TS narrows by either.
					const unitOf = (x: Expr): { value: string | number | bigint | boolean } | undefined => {
						const text = staticText(x);
						const t = x.type === 'literal' ? x : T.pathKey(x) !== undefined ? T.resolveOwn(typeOf(x, scope, false), scope) : undefined;
						return text !== undefined ? { value: text }
							: t?.type === 'literal' && t.value !== null && !Array.isArray(t.value) ? { value: t.value as string | number | bigint | boolean } : undefined;
					};
					// A comparand typed as a union of unit literals (`kind: 'call' | 'construct'`) matches any of them, narrowing only the matching branch:
					// the other holds for every member but the one value it turned out to be.
					const literalUnionOf = (x: Expr): Set<unknown> | undefined => {
						const t = T.pathKey(x) !== undefined ? T.resolveOwn(typeOf(x, scope, false), scope) : undefined;
						const parts = t?.type === 'union' ? t.types.map(u => T.resolveOwn(u, scope)) : undefined;
						return parts?.every(u => u.type === 'literal' && u.value !== null && !Array.isArray(u.value)) ? new Set(parts.map(u => (u as { value: unknown }).value)) : undefined;
					};
					for (const [l, r] of [[test.left, test.right], [test.right, test.left]] as const) {
						const unit = unitOf(r);
						const units = unit ? new Set<unknown>([unit.value]) : keepMatch ? literalUnionOf(r) : undefined;
						// An optional chain equal to a non-nullish value did not short-circuit, so every object before a `?.` is non-nullish (matching branch only).
						if (units && keepMatch && (l.type === 'member' || l.type === 'index' || l.type === 'call'))
							scope = nonNullChainRoots(l, scope);
						// `typeof x === 'kind'`, `x` maybe a dotted path.
						const text = staticText(r);
						if (l.type === 'unary' && l.operator === 'typeof' && text !== undefined) {
							const kinds = new Set([text]);
							const s = narrowKey(l.operand, m => narrowByTypeof(m, kinds, keepMatch, scope));
							if (s)
								return s;
						}
						// `x === null / undefined` (loose `==` matches both), `x` maybe a dotted path.
						if (T.isLiteral(r, 'null') || r.type === 'identifier' && r.name === 'undefined') {
							const matches: (m: Type) => boolean
								= loose					? m => T.isNullish(m, scope)
								: r.type === 'literal'	? m => T.isLiteral(m, 'null')
								: m => m.type === 'ref' && (m.name === 'undefined' || m.name === 'void');
							const s = narrowKey(l, m => matches(m) === keepMatch);
							if (s)
								return s;
						}
						// Which members of the compared reference's type survive: literal members must match; non-literal members might.
						const unitKeep = unit && ((raw: Type): boolean | Type => {
							const m = T.resolveOwn(raw, scope);
								if (m.type === 'literal')
									return (m.value === unit.value) === keepMatch;
								// `unknown`/`{}` equal to a unit IS that unit, as TS narrows a supertype by equality.
								if (keepMatch && (T.isRef(m, 'unknown') || (m.type === 'object' && !m.members.length))) {
									const v = unit.value;
									return typeof v === 'bigint' ? T.rangeToType({ base: 'bigint', min: v, max: v, integer: true }) : Literal(v);
								}
								// `boolean` is `true | false`, so `x === false` narrows the other branch to `true`.
								if (m.type === 'ref' && m.name === 'boolean' && typeof unit.value === 'boolean')
									return Literal(keepMatch ? unit.value : !unit.value);
								// A number/bigint pins to exactly the value on the matching branch, intersected with what is known (`x > 10` then `x === 3` is `never`).
								// The excluding branch can only special-case "was already pinned to this value".
								const v = unit.value;
								if (typeof v === 'number' || typeof v === 'bigint') {
									const mr = T.toRange(m);
									if (mr && mr.base === typeof v) {
										if (keepMatch) {
											const merged = T.rangeIntersect(mr, { base: mr.base, min: v, max: v, integer: typeof v === 'bigint' || T.isIntValue(v) });
											return merged ? T.rangeToType(merged) : false;
										}
										return mr.min !== undefined && mr.min === mr.max && mr.min === v ? false : true;
									}
								}
								// TS's areTypesComparable: on the matching branch, a member the value is comparable with neither way (an object against a string) cannot be it.
								// A numeric unit is a one-value range here, as a numeric literal types.
								const lit: Type = typeof v === 'number' ? TS.RangeType('number', v, v, T.isIntValue(v)) : typeof v === 'bigint' ? TS.RangeType('bigint', v, v) : Literal(v);
								return !keepMatch || T.isAssignable(lit, m, scope) || T.isAssignable(m, lit, scope);
							});
						if (l.type === 'identifier' && unitKeep)
							return narrowValue(scope, l.name, unitKeep);
						// `x.prop === literal` (a discriminated union): `narrowByDiscriminant` splits a compound member to its matching variants; `x[0] === literal`
						// discriminates too (a tuple position, a numeric key).
						const discKey = l.type === 'member' ? l.property
							: l.type === 'index' ? (T.isLiteral(l.index, 'number') ? String(l.index.value) : T.literalString(l.index))
							: undefined;
						if ((l.type === 'member' || l.type === 'index') && discKey !== undefined && units) {
							// `x?.prop === literal` holding implies `x` is non-nullish (a nullish `x` gives `undefined`); not on the excluding branch, which a nullish `x` satisfies.

							const prop = discKey;
							const targets = units;

							// Narrows `m` by a discriminant equality, recursing into its structure to split a compound member down to its matching variants.
							function narrowByDiscriminant(m: Type, depth = 6): boolean | Type {
								if (depth < 0) {
									scope.hitDepthLimit('narrowByDiscriminant');
									return true;	// can't determine within budget: lenient, same as an unresolvable discriminant below
								}
								const r = T.resolveOwn(m, scope);
								if (r.type === 'union') {
									const parts: Type[] = [];
									let changed = false;
									for (const x of r.types) {
										const k = narrowByDiscriminant(x, depth - 1);
										if (k !== false)
											parts.push(k === true ? x : k);
										if (k !== true)
											changed = true;
									}
									return !changed ? true : parts.length ? T.combineTypes(parts) : false;
								}
								// A nullish member has no discriminant to equal a value: what `x?.k === 'a'` holds for short-circuited past it.
								if (T.isNullish(r, scope))
									return !keepMatch;
								const pt = T.lookupMember(r, prop, scope);
								const rp = pt && T.resolve(scope, pt);
								if (!rp)
									return true;	// unresolvable discriminant: lenient, matching `lookupMember`'s/`resolve`'s own established leniency
								if (rp.type === 'literal')
									return targets.has(rp.value) === keepMatch;
								// A discriminant declared as a union of literals on one interface: whether all of it can be excluded or kept without ambiguity.
								return rp.type !== 'union' || !rp.types.every(x => x.type === 'literal')
									|| (keepMatch ? rp.types.some(x => targets.has(x.value)) : rp.types.some(x => !targets.has(x.value)));
							}

							const s = narrowKey(l.object, narrowByDiscriminant, keepMatch && l.optional ? narrowKey(l.object, m => !T.isNullish(m, scope)) : scope);
							// The compared path is itself a reference TS narrows too (`value.type` over a `Partial<...>` no discriminant can split).
							const key = T.pathKey(l);
							if (key && unitKeep) {
								const base = s ?? scope;
								return narrowValue(base, key, unitKeep, base.value(key) ?? typeOf(l, base, false));
							}
							if (s)
								return s;
						}
					}

				} else if (test.operator === '<' || test.operator === '<=' || test.operator === '>' || test.operator === '>=') {
					// Normalized to `A < B` / `A <= B` by swapping for `>`/`>=`; the false branch asserts the negation (`!(A<B)` is `A>=B`), so which side gets
					// the upper bound depends only on `sense`, and its strictness on the operator and `sense` together.
					const swap			= test.operator === '>' || test.operator === '>=';
					const A				= swap ? test.right : test.left;
					const B				= swap ? test.left : test.right;
					const strict		= (swap ? test.operator === '>' : test.operator === '<') === sense;
					const upperOnA		= sense;

					const applyBound = (base: Scope, target: Expr, other: T.NumRange | undefined, isUpper: boolean): Scope => {
						const key = T.pathKey(target);
						if (!key || !other)
							return base;
						const bound = isUpper ? other.max : other.min;
						if (bound === undefined)
							return base;

						return narrowValue(base, key, m => {
							const mr = T.toRange(m);
							if (!mr || mr.base !== other.base)
								return true;
							const merged = T.rangeClamp(mr, bound, isUpper, strict);
							return !merged ? false : T.rangeToType(merged);
						}, asRange(base.value(key) ?? typeOf(target, base, false), base));
					};

					return applyBound(
						applyBound(scope, A, numericSlot(typeOf(B, scope, false), scope), upperOnA),
						B, numericSlot(typeOf(A, scope, false), scope), !upperOnA
					);

				} else if (test.operator === 'instanceof') {
					const key = T.pathKey(test.left);
					if (key) {
						const cur = scope.value(key) ?? typeOf(test.left, scope, false);
						const shadow	= test.right.type === 'identifier' && scope.value(test.right.name);
						const entry		= test.right.type === 'identifier' ? scope.type(test.right.name) : undefined;
						// The class's prototype type, as TS takes it: a generic one's arguments are all `any` (`Promise<any>`).
						return test.right.type === 'identifier' && entry && !(shadow && T.isAny(shadow))
							? narrowTo(scope, key, TS.RefType(test.right.name, entry.typeParams?.map(() => T.ANY)), sense, cur)
							// An unknown class: trust the guard, stop tracking the binding.
							: sense ? narrowTo(scope, key, T.ANY, sense, cur) : scope;
					}

				} else if (test.operator === 'in' && T.literalString(test.left) !== undefined && test.right.type === 'identifier') {
					const prop = T.literalString(test.left)!, key = test.right.name;
					const t = scope.value(key);
					const r = t && T.resolveOwn(t, scope);
					// TS's unlisted-property narrowing: `'length' in a` on a sealed type lacking it gives the truthy branch `length: unknown`.
					if (sense && r && T.sealed(r, scope) && !T.lookupMember(r, prop, scope)) {
						const s = new Scope(scope);
						s.addNarrowing(key, TS.IntersectionType([r, TS.ObjectType([TS.TypeProperty(prop, T.UNKNOWN)])]));
						return s;
					}
					// The false branch drops only a member DECLARING the property as required: an index signature or an optional one may lack it.
					const required = (m: Type) => !T.memberOptional(m, prop, scope)
						&& T.collectMembers(m, scope).some(d => (d.type === 'property' || d.type === 'method') && T.memberKey(d.key) === prop);
					return narrowValue(scope, key, m => !T.sealed(m, scope) || (sense ? !!T.lookupMember(m, prop, scope) : !required(m)), t);
				}
				return scope;
			}
			case 'call': {
				// `Number.isInteger(x)`/`Number.isSafeInteger(x)`: no guard signature models them, but range narrowing needs them, so they are decided here.
				if (test.callee.type === 'member' && test.callee.object.type === 'identifier' && test.callee.object.name === 'Number'
					&& (test.callee.property === 'isInteger' || test.callee.property === 'isSafeInteger') && test.arguments.length === 1
				) {
					const key = T.pathKey(test.arguments[0]);
					if (key) {
						return narrowValue(scope, key, m => {
							const mr = T.toRange(m);
							if (!mr || mr.base !== 'number')
								return true;
							// The false branch can only exclude "known integer": a non-integer range may still hold integers.
							return sense ? T.rangeToType({ ...mr, integer: true }) : mr.integer ? false : true;
						}, scope.value(key) ?? typeOf(test.arguments[0], scope, false));
					}
				}
				// User-defined type guards: `f(x)` with `x is T` narrows `x`; `o.m()` with `this is T` narrows `o`.
				const calleeT = T.resolve(scope, typeOf(test.callee, scope));
				if (T.isAny(calleeT)) {
					// An unknown callee (an imported helper) could be a type guard: the bindings it was given stop being tracked.
					let s = scope;
					for (const a of test.arguments) {
						if (a.type === 'identifier' && s.value(a.name)) {
							s = new Scope(s);
							s.addNarrowing(a.name, T.ANY);
						}
					}
					return s;
				}
				// A bare `function` callee wins; else an overload set's `call` members, or (a union receiver's `lookupMember`) each member's
				// signatures -- the first predicate one the arguments fit, trailing optional parameters omitted (`every(p, thisArg?)`).
				const callSigs = (t: Type): TS.CallSig[] => {
					const r = T.resolveOwn(t, scope);
					return r.type === 'function' ? [r] : r.type === 'object' ? r.members.filter((m): m is Extract<TS.TypeMember, { type: 'call' }> => m.type === 'call') : [];
				};
				const parts = T.flattenIntersection(calleeT, scope);
				const sig	= parts.find((p): p is Extract<Type, { type: 'function' }> => p.type === 'function')
						?? parts.flatMap(p => p.type === 'union' ? p.types.flatMap(callSigs) : callSigs(p))
						.find(m => m.returnType?.type === 'predicate' && (m.rest || m.params.length >= test.arguments.length)
							&& m.params.slice(test.arguments.length).every(p => hasMod(p, 'optional') || p.default));
				const ret	= sig?.returnType;
				if (ret && ret.type === 'predicate' && ret.assertedType && !ret.asserts) {
					const arg = ret.paramName === 'this'
						? (test.callee.type === 'member' ? test.callee.object : undefined)
						: test.arguments[sig.params.findIndex(p => p.key === ret.paramName)];
					const key = arg && T.pathKey(arg);
					if (key) {
						let target = ret.assertedType;
						if (sig.typeParams?.length) {
							const map	= new Map<string, Type>();
							const names = new Map(sig.typeParams.map(p => [p.name, p] as const));
							test.arguments.forEach((a, i) => {
								const p = sig.params[i];
								// Unwidened, as a call's own arguments are: `isLiteral(t, 'string')`'s `K` is the literal `'string'`.
								if (a.type !== 'spread' && p?.typeAnnotation)
									T.inferTypeArgs(p.typeAnnotation, typeOf(a, scope, false), names, map, scope);
							});
							// An uninferred type param must not leave a dangling ref in `target`, which every assignability check would treat as unrelated.
							sig.typeParams.forEach(p => { if (!map.has(p.name)) map.set(p.name, p.constraint ?? p.default ?? T.ANY); });
							target = T.substituteType(target, map);
						}
						return narrowTo(scope, key, target, sense, scope.value(key) ?? typeOf(arg, scope, false));
					}
				}
				return scope;
			}
			default:
				return scope;
		}
	}
}

// Every place a value is accepted INTO a slot (a declaration, assignment, argument, return, yield, field) is a FLOW, stamped on the value's node:
// codegen's open-shape pass stores a slot receiving another layout as `any`. `element`: an array element's slot (a rest argument).
export interface FlowSlot { type: Type; element?: boolean }

export const flowSlotOf = (e: Expr): FlowSlot | undefined => (e as { flowSlot?: FlowSlot }).flowSlot;
// The type the check pass gave `e`, precise (unwidened) and narrowed where it stands; `??=`, so the first real check wins.
export const checkedTypeOf = (e: Expr): Type | undefined => (e as { checkedType?: Type }).checkedType;
// The contextual type the check pass typed `e` against (its slot, parameter, element or member), taken with `checkedType`.
export const expectedTypeOf = (e: Expr): Type | undefined => (e as { expectedType?: Type }).expectedType;
// The signature a call or `new` resolved to -- the chosen overload as declared -- and the type arguments it was instantiated with.
// `lifted`: the parameters higher-order inference made the result's own (`liftGeneric`), which `typeArgs` may name.
export interface CheckedCall { sig: TS.CallSig; typeArgs?: Map<string, Type>; lifted?: TS.TypeParam[] }
// A class declaration codegen copied for one instantiation of a generic class is stamped with that instance's type.
export const instanceOfClass = (c: TS.Class): Type | undefined => (c as { instanceOf?: Type }).instanceOf;
export const checkedCallOf = (e: Expr): CheckedCall | undefined => (e as { checkedCall?: CheckedCall }).checkedCall;

// `??=`: the first real (unmuted) check wins. The slot's scope is stamped onto its refs that carry none: the reader has only the VALUE's scope.
function stampFlow(value: Expr | undefined, type: Type | undefined, scope: Scope, element?: boolean) {
	if (!value || !type)
		return;
	if (!trying && !flowSlotOf(value))
		restampFlow(value, type, scope, element);
}

// `value` as built for `type`, its literal parts too. Codegen re-stamps a call's arguments where it instantiates a generic otherwise.
export function restampFlow(value: Expr, type: Type, scope: Scope, element?: boolean) {
	// An object literal's real slot is the union member it discriminates to -- the one it is BUILT as, here and in codegen.
	const slot = value.type === 'object' ? discriminateContext(type, value, scope) : type;
	(value as { flowSlot?: FlowSlot }).flowSlot = { type: T.stampScope(slot, scope), element };
	stampParts(value, slot, scope);
}

// What a literal's elements and properties are built for: their part of the slot it flows into, INSTANTIATED, where the check's own
// context may still name a generic callee's unsolved parameters (`[K, V]`). Parts past a spread have no known position.
function stampParts(value: Expr, slot: Type, scope: Scope) {
	if (value.type === 'array') {
		const spread = value.elements.findIndex(el => el?.type === 'spread');
		value.elements.slice(0, spread < 0 ? undefined : spread).forEach((el, i) => el && stampContext(el, positionContext(slot, i, scope), scope));
	} else if (value.type === 'object') {
		for (const p of value.properties) {
			const key = p.type === 'field' && p.value ? T.memberKey(p.key) : undefined;
			if (key !== undefined)
				stampContext((p as JS.Field<Type>).value!, contextualMember(slot, key, scope), scope);
		}
	} else if (value.type === 'conditional') {
		stampContext(value.consequent, slot, scope);
		stampContext(value.alternate, slot, scope);
	} else if (value.type === 'binary' && (value.operator === '&&' || value.operator === '||' || value.operator === '??')) {
		// Each operand that may BE the result lands in the slot.
		if (value.operator !== '&&')
			stampContext(value.left, slot, scope);
		stampContext(value.right, slot, scope);
	} else if (value.type === 'sequence') {
		stampContext(value.expressions[value.expressions.length - 1], slot, scope);
	} else if ((value.type === 'arrow' || value.type === 'function') && value.inferredReturn) {
		// A function whose return was only inferred returns what the slot's signature does, as its caller reads the value.
		const ret = T.findFunctionType(slot, scope)?.returnType;
		if (ret)
			returnedValues(value.body).forEach(r => stampContext(r, T.unwrapIfAsync(ret, scope, hasMod(value, 'async')), scope));
	}
}
// The values a body returns: an expression body, or each `return`'s argument outside a nested function.
function returnedValues(body: JS.Stmt<any>[] | Expr | undefined): Expr[] {
	if (!body)
		return [];
	if (!Array.isArray(body))
		return [body];
	const out: Expr[] = [];
	walkerB((s, process) => (s.type === 'return' && s.argument && out.push(s.argument), s.type !== 'function_decl' && s.type !== 'class_decl' && process(s)),
		(e, process) => e.type !== 'arrow' && e.type !== 'function' && e.type !== 'class' && process(e)).statements(body);
	return out;
}
function stampContext(e: Expr, t: Type | undefined, scope: Scope) {
	if (!t)
		return;
	(e as { expectedType?: Type }).expectedType = t;
	stampParts(e, e.type === 'object' ? discriminateContext(t, e, scope) : t, scope);
}

// A numeric `let`/`var`'s representation must hold everything its binding is given or read as: the hull of those stamps,
// recorded on its declarator (`flowType`) as the check stamps them. A non-numeric one takes the whole base.
function foldFlow(scope: Scope, name: string, t: Type) {
	const d = scope.binding(name);
	if (!d)
		return;
	const r = numericSlot(t, scope), prev = d.flowType && T.toRange(d.flowType);
	const hull = r && prev ? T.rangeUnion(prev, r) : r ?? prev;
	d.flowType = T.rangeToType(hull ?? { base: 'number', integer: false });
}

// A write: the flow holds `t` from here, and a stamping check records it in the binding's hull (a value never read still lands in the slot).
function assignFlow(scope: Scope, key: string, t: Type, stamp: boolean) {
	forgetPathsThrough(scope, key);
	scope.addNarrowing(key, t);
	if (stamp)
		foldFlow(scope, key, t);
}

// A numeric unary's result, as TS's: a bigint stays one, an operand that MAY be one (`number | bigint`) gives either.
function numericOf(t: Type, scope: Scope): Type {
	return T.isBigint(t, scope) ? T.BIGINT : T.unionMembers(t, scope).some(m => T.isBigint(m, scope)) ? T.combineTypes([T.NUMBER, T.BIGINT]) : T.NUMBER;
}

// A pseudo-type as the range it is, before splitting into union members resolves it to plain `number`.
const asRange = (t: Type, scope: Scope) => {
	const m = T.machineOf(t, scope);
	return m ? T.rangeToType(T.machineRange(m)) : t;
};

// A non-logical, non-comparison binary operator's result: `+` concatenates a string; interval arithmetic keeps a bounded
// result bounded (`x + 1` for a range-narrowed `x`); else the operands' `number`/`bigint`.
function arithmetic(op: JS.binaryOps, lt: Type, rt: Type, scope: Scope): Type {
	if (op === '+' && (T.isStringLike(lt, scope) || T.isStringLike(rt, scope)))
		return T.STRING;
	if (T.isAny(T.resolveOwn(lt, scope)) || T.isAny(T.resolveOwn(rt, scope)))
		return T.ANY;
	const lr = T.toRange(T.resolveOwn(lt, scope)), rr = T.toRange(T.resolveOwn(rt, scope));
	const nr = lr && rr && T.rangeBinOp(op, lr, rr);
	return nr ? T.rangeToType(nr) : T.isBigint(lt, scope) || T.isBigint(rt, scope) ? T.BIGINT : T.NUMBER;
}

// A `number`/`bigint` slot's range (a pseudo-type's before it resolves away to `number`).
const numericSlot = (t: Type, scope: Scope) => {
	const m = T.machineOf(t, scope);
	return m ? T.machineRange(m) : T.toRange(t) ?? T.toRange(T.resolveOwn(t, scope));
};

// What a numeric slot holds after a value in range `range()`: that, or the slot's own range where it leaves it (a forced `u32` wraps). Lazy:
// ranging a value resolves it, which only a numeric slot may ask.
function numericFlow(declared: Type, range: () => T.NumRange | undefined, scope: Scope): Type | undefined {
	const slot	= numericSlot(declared, scope);
	const r		= slot && range();
	if (!slot || !r || r.base !== slot.base)
		return undefined;
	const inside = (!slot.integer || r.integer) && (slot.min === undefined || (r.min !== undefined && r.min >= slot.min)) && (slot.max === undefined || (r.max !== undefined && r.max <= slot.max));
	return T.rangeToType(inside ? r : slot);
}

// `before` stepped by `by` (`+=`, `-=`, `++`, `x = x + a`), which by the user's rule never overflows its machine int.
function steppedRange(before: Type, op: '+' | '-', by: T.NumRange | undefined, scope: Scope): T.NumRange | undefined {
	const old = numericSlot(before, scope);
	return old && by && T.rangeStep(old, op === '-' ? T.rangeUnOp('-', by)! : by);
}
const unitRange = (base: T.NumRange['base']): T.NumRange => ({ base, min: base === 'bigint' ? 1n : 1, max: base === 'bigint' ? 1n : 1, integer: true });

// `checkAssignable` for a real flow: the value's node carries the slot it flows into.
function checkFlow(value: Expr | undefined, src: Type, dst: Type, scope: Scope, pos: Location, dstScope: Scope, err: Err): boolean {
	stampFlow(value, dst, dstScope);
	return checkAssignable(src, dst, scope, pos, dstScope, err);
}

// Tries `T.isAssignable` strict then lax; a GAP means strict failed only due to an opaque type (keyof/conditional/infer/mapped).
// Every real assignability check should go through this, not `T.isAssignable` directly. `dstScope` resolves `dst`'s own structure.
function checkAssignable(src: Type, dst: Type, scope: Scope, pos: Location, dstScope: Scope, err: Err): boolean {
	if (T.isAssignable(src, dst, scope, dstScope, true))
		return true;
	const lax = T.isAssignable(src, dst, scope, dstScope, false);
	// The same type, written the same way, is assignable to itself however opaque it is (`Record<K, M[K]>`).
	if (lax && (src === dst || T.typeId(src) === T.typeId(dst)))
		return true;
	if (lax)
		err(SEVERITY.GAP, pos)`Assignability of '${show().type(src)}' to '${show().type(dst)}' could not be fully verified ('keyof'/conditional/'infer'/mapped types aren't evaluated)`;
	return lax;
};

// A fresh object literal assigned to a fully-known object type may not introduce unknown keys
function checkExcessProps(lit: Expr, target: Type, pos: Location, targetScope: Scope, err: Err) {
	if (lit.type !== 'object')
		return;

	const r			= T.resolveOwn(target, targetScope);
	const targets	= (r.type === 'intersection' ? r.types.map(t => T.resolveOwn(t, targetScope)) : [r]).filter(t => t.type === 'object');
	if (targets.length !== (r.type === 'intersection' ? r.types.length : 1) || targets.some(t => t.members.some(m => m.type === 'index')))
		return;		// partially-unknown target or index signature: anything goes

	if (lit.properties.some(p => p.type === 'spread' || typeof p.key === 'object'))
		return;		// spread/computed keys: shape is open

	for (const p of lit.properties)
		if (p.type !== 'spread' && typeof p.key !== 'object' && !targets.some(t => t.members.some(m => (m.type === 'property' || m.type === 'method') && JS.keyName(m.key) === JS.keyName(p.key))))
			err(SEVERITY.ERROR, pos)` Object literal may only specify known properties, and '${show().memberKey(p.key)}' does not exist in type '${show().type(target)}'`;
}

// ---- declaration hoisting / namespace resolution ------------------------------------------

// `globalThis` of a global declaration space: the outer space's, plus this one's `var`s (at any block depth outside a function),
// functions and namespaces, each a `typeof` query resolved when read. Any other key is `any`: TS7017 needs noImplicitAny, untracked here.
function globalObject(stmts: Stmt[], scope: Scope): Type {
	const names = new Set(['globalThis']);
	walkerB(
		(st, process) => {
			if (st.type === 'var_decl' && st.kind === 'var')
				st.declarations.forEach(d => T.bindingNames(d.name).forEach(n => names.add(n)));
			else if (st.type === 'function_decl' || st.type === 'namespace_decl')
				names.add(st.name);
			return st.type === 'var_decl' || st.type === 'function_decl' || st.type === 'namespace_decl' || st.type === 'class_decl' ? false : process(st);
		},
		() => false,
	).statements(stmts);
	const own	= TS.ObjectType([...[...names].map(name => TS.TypeProperty(name, T.stampScope({ type: 'typeof', name }, scope))), TS.TypeIndex('key', T.STRING, T.ANY)]);
	const outer	= scope.parent?.value('globalThis');
	return outer ? TS.IntersectionType([outer, own]) : own;
}

// A declaration's type parameters' defaults and constraints name types of its own module: a default filled in where the type is used
// (`Cls<string>` for `Cls<T, M = CM<T>>`) must still resolve there. Its own parameters stay unstamped, bound per use.
function stampTypeParams(tps: TS.TypeParam[] | undefined, scope: Scope) {
	const own = new Set(tps?.map(p => p.name));
	for (const p of tps ?? []) {
		if (p.default)
			T.stampScope(p.default, scope, own);
		if (p.constraint)
			T.stampScope(p.constraint, scope, own);
	}
}

// A block's `interface`/`type` declarations into `scope`. Codegen binds a body's own too, so what it asks the checker resolves them.
export function hoistTypes(stmts: readonly Stmt[], scope: Scope) {
	for (let stmt of stmts) {
		if (stmt.type === 'export_decl')
			stmt = stmt.declaration;
		if (stmt.type === 'type_alias_decl') {
			stampTypeParams(stmt.typeParams as TS.TypeParam[], scope);
			scope.addType(stmt.name, T.stampScope(T.markModifiersTypes(stmt.value, stmt.typeParams as TS.TypeParam[]), scope), stmt.typeParams);
		} else if (stmt.type === 'interface_decl') {
			stampTypeParams(stmt.typeParams as TS.TypeParam[], scope);
			const obj = T.stampScope(TS.ObjectType(stmt.body), scope);
			T.declaredShapes.add(obj);
			// Inherited parts FIRST, own members LAST: the order `mergeType` uses, which `lookupMember`'s reversal turns into override precedence.
			scope.mergeType(stmt.name, stmt.extendsClause?.length ? T.intersectTypes([...stmt.extendsClause.map(e => T.stampScope(e, scope)), obj]) : obj, stmt.typeParams, true);
		}
	}
}

function hoist(block: Stmt[], scope: Scope) {
	const fnGroups = new Map<string, JS.FunctionDecl<any>[]>();
	// `declare global` in a block that is already global (the lib's root, a script) declares here; a module's is not merged yet.
	const inGlobal	= !scope.parent || scope.globalSpace;
	const stmts		= block.flatMap(s => inGlobal && s.type === 'module_decl' && s.name === 'global' ? (s.body as Stmt[]).map(d => d.type === 'var_decl' ? { ...d, ambient: true } : d) : [s]);
	if (inGlobal)
		scope.addLazyValue('globalThis', () => globalObject(stmts, scope));

	// `interface`/`type` declarations first: a `declare var X: Y` resolves `Y` eagerly, so every augmentation of `Y` across lib files must be merged.
	hoistTypes(stmts, scope);
	for (let stmt of stmts) {
		if (stmt.type === 'export_decl')
			stmt = stmt.declaration;
		switch (stmt.type) {
			case 'function_decl':
				fnGroups.set(stmt.name, [...(fnGroups.get(stmt.name) ?? []), stmt]);
				break;

			case 'class_decl': {
				// `stmt` was reassigned twice above, beyond this checker's narrowing.
				stampTypeParams(stmt.typeParams as TS.TypeParam[], scope);
				const { instance, value } = classShapes(stmt as TS.Class, scope);
				scope.mergeType(stmt.name, instance, stmt.typeParams as TS.TypeParam[]);
				// `mergeValue`, as `mergeType` above: a primitive wrapper is declared twice on purpose, and overwriting would lose its ambient call signature.
				scope.mergeValue(stmt.name, value);
				scope.addDecl(stmt.name, stmt);
				break;
			}
			case 'enum_decl': {
				let next = 0;
				const memberTypes = stmt.members.map((m): Type => !m.init ? Literal(next++)
					: T.isLiteral(m.init, 'number') ? Literal((next = m.init.value + 1, m.init.value))
					: T.literalString(m.init) !== undefined ? { ...Literal(T.literalString(m.init)!), fresh: true }
					: T.isLiteral(m.init, 'string') ? T.STRING
					: T.NUMBER
				);
				scope.addType(stmt.name, T.combineTypes(memberTypes));
				scope.addValue(stmt.name, TS.ObjectType(stmt.members.map((m, i) => TS.TypeProperty(m.name, memberTypes[i]))));
				// Each member is a type too (`kind: Kind.A`), reached as a dotted name through the enum's own namespace; merged declarations share it.
				const members = scope.ownNamespace(stmt.name) ?? new Scope(scope);
				stmt.members.forEach((m, i) => members.addType(m.name, memberTypes[i]));
				scope.addNamespace(stmt.name, members);
				break;
			}
			case 'namespace_decl': {
				// Same-named blocks MERGE (lib.es5's `namespace Intl`, added to by later files): a later block sees the earlier's names and merges into it.
				const prior = scope.ownNamespace(stmt.name);
				const { scope: block, inner, alias } = exportScope(stmt.body, prior ?? scope, undefined, prior && namespaceInner.get(prior));
				if (prior)
					prior.copyAll(block);
				const ns	= prior ?? block;
				// A namespace merged onto an enum's has an inner scope of its own; every later block merges into it.
				if (!namespaceInner.has(ns))
					namespaceInner.set(ns, inner);
				// Merged onto a function or class, the namespace is both: its value keeps that one's call/construct signatures.
				if (!prior)
					namespaceBase.set(ns, scope.ownValue(stmt.name));
				const members	= alias ?? ns.toObject();
				const base		= namespaceBase.get(ns);
				const value		= base ? TS.IntersectionType([base, members]) : members;
				// A type-only namespace merged onto a same-named const or class would clobber its value with a sealed empty object before the `var_decl` walk.
				if (!(value.type === 'object' && value.members.length === 0))
					scope.addValue(stmt.name, value);
				scope.addNamespace(stmt.name, ns);
				break;
			}
			case 'import':
				// Resolved into `scope`'s PARENT (`TStypeCheckAsync`): an own entry here serves an own-map reader, and carries the
				// declarator, which an own value would otherwise hide (a cross-module const's identity).
				[stmt.default, stmt.namespace, ...stmt.specifiers?.map(s => s.local) ?? []].forEach(name => {
					if (name) {
						const d = scope.declarator(name);
						scope.addValue(name, scope.value(name) ?? T.ANY);
						if (d)
							scope.addDeclarator(name, d);
					}
				});
				break;

			case 'var_decl':
				// Only a `declare const/let/var` is hoisted: a plain one observes a temporal dead zone (`checkStmt`'s sequential walk); an ambient one has no order.
				if (stmt.ambient)
					stmt.declarations.forEach(d => hoistVar(scope, d, stmt.kind !== 'const'));
				else if (stmt.kind !== 'var')
					for (const d of stmt.declarations) {
						let bound: Scope | undefined;
						const declared = () => bound ??= ahead(() => {
							const s = new Scope(scope);
							hoistVar(s, d, stmt.kind !== 'const');
							return s;
						});
						T.bindingNames(d.name).forEach(n => scope.addLazyValue(n, () => declared().ownValue(n)!));
					}
				break;
		}
	}

	// Same-named declarations are overloads: bodyless signatures are the public face, an object type with one call member each; a single one stays a function.
	for (const [name, decls] of fnGroups) {
		const sigs		= decls.filter(d => !d.body);
		const chosen	= sigs.length ? sigs : decls;
		if (chosen.length > 1) {
			// Each overload's types resolve in THIS module (`declScope`/`stampSig`). Merged, not overwritten: a same-named namespace is part of the value.
			scope.mergeValue(name, TS.ObjectType(chosen.map(d => TS.TypeCall(T.stampSig(T.withScope({ ...T.FixSig(d, T.ANY), origin: d }, scope), scope)))));
			// The bodied implementation an overload group always has.
			const impl = decls.find(d => d.body);
			if (impl) {
				// The IMPLEMENTATION's own annotations resolve in this module too, for a consumer reading the decl (codegen's `resolveParams`), except
				// its own type parameters, which its body binds.
				const own = new Set(impl.typeParams?.map(tp => tp.name));
				impl.params.forEach(p => p.typeAnnotation && T.stampScope(p.typeAnnotation, scope, own));
				if (impl.returnType)
					T.stampScope(impl.returnType, scope, own);
				scope.addDecl(name, impl);
			}
		} else {
			const d = chosen[0];
			const t = TS.FunctionType(T.stampSig(T.withScope({ ...T.FixSig(d, T.ANY), origin: d }, scope), scope));
			if (!d.returnType && d.body)
				// `d`, not `t`: a destructuring parameter's pattern is `_` in the fixed signature.
				lazyReturnType(t, d, scope, () => {
					checkFunctionBody(d, d.body, ownThis(flowContainer(scope)), hasMod(d, 'async'), hasMod(d, 'generator'), hasMod(d, 'generator'));
					refreshParams(t, d);
					t.returnType = d.returnType as Type | undefined;
				});
			scope.mergeValue(name, t);
			scope.addDecl(name, d);
		}
	}
}

// A class's `extends` operand as the type it names: `Base`, a namespace-qualified `NS.Base`, either with type arguments.
export function superClassRef(e: Expr | undefined): TS.RefType | undefined {
	const dotted = (x: Expr): string | undefined => x.type === 'identifier' ? x.name
		: x.type === 'member' ? (o => o && `${o}.${x.property}`)(dotted(x.object)) : undefined;
	const target	= e?.type === 'instantiation' ? e.expression : e;
	const name		= target && dotted(target);
	return name ? TS.RefType(name, e?.type === 'instantiation' ? e.typeArgs : undefined) : undefined;
}

// TS's auto-typed array: `let x = []` (or `x = []` into an untyped `let x`) evolves by its writes, which `any[]` approximates.
const AUTO_ARRAY			= TS.ArrayType(T.ANY);
const isEmptyArrayLiteral	= (e?: Expr) => e?.type === 'array' && !e.elements.length;

// `home` is where the name binds (a `var`'s is its body's scope); `scope` is the flow the initializer is typed and narrows in.
function hoistVar(scope: Scope, d: JS.Var<Type>, widen: boolean, typeAnnotation = d.typeAnnotation, err?: Err, stamp = false, home = scope) {
	if (typeof d.name === 'string') {
		// A machine-type annotation stays unresolved: resolved, it is plain `number`, and the slot it forces would be lost for every later read.
		const forcesSlot = !!typeAnnotation && !!T.machineOf(typeAnnotation, scope);
		// A bare ref stays that ref for an annotation-only declaration, stamped where written: resolving it now would bake in the interface as declared
		// so far, before a later lib block merges into it. Otherwise it resolves now, in its own `declScope`.
		const bareRef = typeAnnotation?.type === 'ref' && !typeAnnotation.typeArgs;
		// An annotated initializer is already checked (`checkStmt`'s `var_decl`): typed again only for its range, reporting nothing.
		const precise = d.init && !isEmptyArrayLiteral(d.init) && (!typeAnnotation || T.toRange(typeAnnotation) || forcesSlot)
			? typeOf(d.init, scope, false, typeAnnotation, undefined, typeAnnotation ? undefined : err, stamp && !typeAnnotation) : undefined;
		home.addValue(d.name, bareRef && !d.init && !forcesSlot ? T.stampScope(typeAnnotation, scope)
			: bareRef && typeAnnotation.declScope ? T.resolve(typeAnnotation.declScope as Scope, typeAnnotation, undefined, forcesSlot)
			// Stamped before resolving: `resolve` is shallow, so a ref NESTED in the annotation (`Type[]`, `Box<Type>`) survives and would otherwise
			// re-resolve in whatever scope reads the value, binding to a same-named type in an importing module.
			: typeAnnotation ? T.resolve(scope, T.stampScope(typeAnnotation, scope), undefined, forcesSlot)
			: isEmptyArrayLiteral(d.init) ? AUTO_ARRAY
			: d.init ? T.widenNullish(widen ? T.widenLiterals(precise!) : precise!, scope) : T.ANY);
		home.addDeclarator(d.name, d);
		// The declared type's own shape: resolving it here would bake in an interface before a later lib block merges into it.
		if (widen && (T.toRange(scope.declared(d.name)) || forcesSlot))
			home.addBinding(d.name, d);
		// A numeric `let`'s flow starts at its initializer's range: its declared type stays the widened `number`.
		const flow = widen && precise && (err || stamp || scope.isQuiet()) && numericFlow(scope.declared(d.name)!, () => numericSlot(precise, scope), scope);
		if (flow)
			assignFlow(scope, d.name, flow, stamp);
		// TS 4.4 aliased conditions: a `const`'s initializer stays true for its lifetime, so narrowing the const narrows through what its initializer narrows.
		if (!widen && d.init)
			scope.addAlias(d);
		// ...and an unannotated `const op = x.op` of a union's DISCRIMINANT IS `x.op`, as a destructured `const {op} = x` is (`bindPattern`).
		if (!widen && !typeAnnotation && d.init && aliasedDiscriminant(d.init, scope))
			home.addSource(d.name, d.init);
		// TS's assignment narrowing: a union-typed `const` reads as the members its initializer can be (`const e: E = E.ONE` is `E.ONE`). Not a `let`,
		// whose narrowings reassignment never invalidates.
		if (!widen && d.init && typeAnnotation) {
			const declared = T.unionMembers(typeAnnotation, scope);
			const init = declared.length > 1 ? T.unionMembers(typeOf(d.init, scope, false, typeAnnotation), scope) : [];
			const kept = declared.filter(m => init.some(i => T.isAssignable(i, m, scope)));
			if (kept.length && kept.length < declared.length)
				scope.addNarrowing(d.name, T.combineTypes(kept));
		}
	} else {
		// TS's getTypeFromBindingPattern as the initializer's context: an array pattern makes an array literal a tuple (`const [a] = [s, n]`).
		const context	= d.name.type === 'array_pattern' ? T.patternType(d.name) : undefined;
		const t			= typeAnnotation ?? (d.init && T.widenNullish(typeOf(d.init, scope, widen, context, undefined, err, stamp), scope));
		if (t)
			bindPattern(home, d.name, t, d.init, !widen, err);
		else
			T.bindingNames(d.name).forEach(n => home.addValue(n, T.ANY));
	}
}

// TS's aliased discriminant (getCandidateDiscriminantPropertyAccess): a plain access of a discriminant property of a union-typed path.
function aliasedDiscriminant(init: Expr, scope: Scope): boolean {
	if ((init.type !== 'member' && init.type !== 'index') || !isPurePath(init))
		return false;
	const key	= init.type === 'member' ? init.property : init.index.type === 'literal' ? String(init.index.value) : undefined;
	const objT	= T.resolve(scope, typeOf(init.object, scope, false));
	return key !== undefined && objT.type === 'union' && T.isDiscriminant(objT, key, scope);
}

// What iterating `t` yields and returns. A non-iterable is TS 2488 and then `any`, as in TS; a GAP rather than an error while `t` isn't fully known.
function iterationOrReport(t: Type, scope: Scope, pos: Location, err?: Err, async = false): T.IterationTypes {
	const it = T.iterationTypes(t, scope, async);
	if (!it && err)
		err(T.sealed(t, scope) ? SEVERITY.ERROR : SEVERITY.GAP, pos)`Type '${show().type(t)}' must have a '[Symbol.iterator]()' method that returns an iterator`;
	return it ?? { yield: T.ANY, return: T.ANY, next: T.ANY };
}

// A union context narrowed to the members an object literal's literal-valued properties can match (TS's discriminateContextualType);
// the whole union when none or all survive.
function discriminateContext(t: Type, lit: Expr & { type: 'object' }, scope: Scope): Type {
	const members = T.unionMembers(t, scope);
	if (members.length < 2)
		return t;
	// TS's discriminateContextualTypeByObjectMembers: a written unit (a literal, or `undefined`), and an omitted discriminant reading as `undefined`,
	// so `{cb}` against `{disc: true; ...} | {disc?: false; ...}` is the second member's.
	const UNDEFINED = Symbol('undefined');
	const written = new Map<string, unknown>(lit.properties.flatMap((p): [string, unknown][] => p.type !== 'field' || typeof p.key === 'object' ? []
		: p.value?.type === 'literal' && !Array.isArray(p.value.value) ? [[String(p.key), p.value.value]]
		: p.value?.type === 'identifier' && p.value.name === 'undefined' ? [[String(p.key), UNDEFINED]] : []));
	const present = new Set(lit.properties.flatMap(p => p.type !== 'spread' ? JS.keyName(p.key) ?? [] : []));
	// A key's unit values in `m`, or undefined when it is no discriminant there (some non-unit type, or absent).
	const unitsOf = (m: Type, key: string) => {
		const pt = T.lookupMember(m, key, scope);
		const units = pt && T.unionMembers(pt, scope).map(u => T.resolveOwn(u, scope));
		return units && units.every(u => u.type === 'literal' || T.isRef(u, 'undefined'))
			? [...units.map(u => u.type === 'literal' ? u.value : UNDEFINED), ...T.memberOptional(m, key, scope) ? [UNDEFINED] : []] : undefined;
	};
	const omitted = [...new Set(members.flatMap(m => { const r = T.resolveMembers(m, scope); return r.type === 'object' ? r.members : []; })
		.flatMap(m => { const k = m.type === 'property' && hasMod(m, 'optional') ? JS.keyName(m.key) : undefined; return k !== undefined && !present.has(k) ? [k] : []; }))];
	const tests = [...written, ...omitted.map(k => [k, UNDEFINED] as const)];
	const kept = members.filter(m => tests.every(([key, value]) => { const units = unitsOf(m, key); return !units || units.some(u => u === value); }));
	return kept.length && kept.length < members.length ? T.combineTypes(kept) : t;
}

// A property's contextual type: its type in each member of the context that has it (TS: a union context maps over its members).
function contextualMember(t: Type, key: string, scope: Scope): Type | undefined {
	const parts = T.unionMembers(t, scope).flatMap(m => { const p = T.lookupMember(m, key, scope); return p ? [p] : []; });
	return parts.length ? T.combineTypes(parts) : undefined;
}

// Whether a contextual type asks for literals: one of its members is a literal (an enum member, a literal union), so a fresh
// literal checked against it keeps its literal type instead of widening.
function contextKeepsLiteral(t: Type, scope: Scope): boolean {
	return T.unionMembers(t, scope).some(m => {
		// TS's isLiteralOfContextualType: a type parameter constrained to a primitive (`K extends string`) keeps the literal too.
		const bound = T.typeParamConstraint(m, scope);
		if (bound)
			return T.unionMembers(bound, scope).some(c => (r => T.isRef(r, 'string') || T.isRef(r, 'number') || T.isRef(r, 'bigint') || T.isRef(r, 'boolean') || r.type === 'literal')(T.resolveOwn(c, scope)));
		const r = T.resolveOwn(m, scope);
		return r.type === 'literal' || (r.type === 'range' && r.min !== undefined && r.min === r.max);
	});
}

// A fresh value's type widened as TS widens one: fully with no context; with one, its parts were already typed against their own
// contexts, so only a top-level literal the context does not ask for widens (an inferred return, an object literal's property).
function widenForContext(t: Type, context: Type | undefined, scope: Scope): Type {
	return !context ? T.widenLiterals(t) : contextKeepsLiteral(context, scope) ? t : T.widenLiterals(t, false, false, true);
}

// The element context an iterable contextual type gives an array literal: what its iterable members yield (`any` gives none).
function iteratedContext(t: Type, scope: Scope): Type | undefined {
	const yields = T.unionMembers(t, scope).flatMap(m => {
		const it = !T.isAny(T.resolveOwn(m, scope)) && T.iterationTypes(m, scope);
		return it ? [it.yield] : [];
	});
	return yields.length ? T.combineTypes(yields) : undefined;
}

// Each name a pattern binds gets its part of `t` (a tuple position, an array element, a member), narrowed where the source path is. A `const`
// destructured from a UNION at a stable path is recorded as that path (`scope.addSource`), so narrowing one name narrows the others (TS 4.6).
function bindPattern(scope: Scope, target: JS.BindingTarget, t: Type, source?: Expr, constant = false, err?: Err) {
	if (typeof target === 'string') {
		scope.addValue(target, t);
		return;
	}
	const r			= T.resolve(scope, t);
	const narrowed	= (e: Expr | undefined) => { const k = e && T.pathKey(e); return k ? scope.value(k) : undefined; };
	const correlate	= constant && r.type === 'union' && !!source && T.pathKey(source) !== undefined;
	// A default replaces only `undefined`, so the binding is the source's non-nullable part or the default's own type.
	const withDefault = (t: Type, def?: Expr) => def ? T.combineTypes([T.nonNullable(t, scope), typeOf(def, scope, !constant, T.nonNullable(t, scope))]) : t;
	if (target.type === 'array_pattern') {
		// Each union member answers for itself, as TS destructures one: a tuple's position, else its iterated element (iterated once per member).
		const members	= T.unionMembers(r, scope).map(m => T.resolveOwn(m, scope));
		const elems		= members.map(m => m.type === 'tuple' ? undefined : iterationOrReport(m, scope, getPos(target)!, err).yield);
		const at		= (i: number) => T.combineTypes(members.map((m, j) => m.type === 'tuple' ? T.tupleElementType(m.elements[i]) ?? T.ANY : elems[j]!));
		const restOf	= (m: Type, j: number) => m.type === 'tuple' ? T.combineTypes(m.elements.slice(target.elements.length).map(el => T.tupleElementType(el) ?? T.ANY)) : elems[j]!;
		target.elements.forEach((el, i) => {
			const sub	= el && source ? { type: 'index', object: source, index: { type: 'literal', value: i } } as Expr : undefined;
			const et	= el && (narrowed(sub) ?? at(i));
			if (el)
				bindPattern(scope, el.target, withDefault(et!, el.default), sub, constant, err);
		});
		if (target.rest)
			bindPattern(scope, target.rest, TS.ArrayType(T.combineTypes(members.map(restOf))), undefined, false, err);
	} else {
		for (const p of target.properties) {
			const key	= JS.keyName(p.key);
			const sub	= key !== undefined && source ? { type: 'member', object: source, property: key } as Expr : undefined;
			const m		= narrowed(sub)
				?? (key !== undefined ? T.optional(T.lookupMember(r, key, scope) ?? T.ANY, T.memberOptional(r, key, scope)) : T.ANY);
			bindPattern(scope, p.value, withDefault(m, p.default), sub, constant, err);
			if (correlate && sub && typeof p.value === 'string' && !p.default)
				scope.addSource(p.value, sub);
		}
		if (target.rest)
			scope.addValue(target.rest, T.ANY);
	}
}

// CommonJS's `__filename`/`__dirname` are per module (the module wrapper's parameters), so they bind into the module's own scope, never the lib's.
// `require`/`module`/`exports` stay unbound.
export function bindModuleNames(filename: string | undefined, scope: Scope) {
	if (filename) {
		scope.addValue('__filename', T.STRING);
		scope.addValue('__dirname', T.STRING);
	}
}

// A namespace's export view -> the scope its blocks hoist into, so a later same-named block merges into the first.
const namespaceInner = new WeakMap<Scope, Scope>();
const namespaceBase = new WeakMap<Scope, Type | undefined>();

export function exportScope(body: Stmt[], parent: Scope, filename?: string, into?: Scope): { scope: Scope; inner: Scope; alias?: Type } {
	// `hoist` + `hoistVars`, not a full `checkBlock`: only the exposed declaration types are needed. `into`: an earlier same-named namespace's scope.
	const inner = into ?? new Scope(parent);
	hoist(body, inner);
	// `inner` is RETURNED for the caller to put on the module record: codegen resolves names declared inside the module. `scope` is the export VIEW.
	bindModuleNames(filename, inner);

	// Infers the top-level declarations' types MUTED: this resolves what a module exposes; its own real check is when it is the entry.
	for (let stmt of body) {
		if (stmt.type === 'export_decl')
			stmt = stmt.declaration;
		if (stmt.type === 'var_decl') {
			const varStmt = stmt;
			stmt.declarations.forEach(d => {
				hoistVar(inner, d, varStmt.kind !== 'const');
				// The real initializer reachable through `Scope.decl`, as a function's or class's is (codegen initializes a cross-module const lazily).
				if (typeof d.name === 'string')
					inner.addDecl(d.name, varStmt);
			});
		}
	}

	const assign = body.find(s => s.type === 'export_assignment');
	if (assign) {
		return {
			inner,
			scope: inner.namespace(assign.expr) ?? new Scope(inner.semantics),
			alias: inner.value(assign.expr) ?? T.ANY,
		};
	}

	const scope = new Scope(inner.semantics);
	// Parent-chain-aware (`inner.value`): an imported name may have resolved into `inner`'s parent.

	if (body.some(s => s.type === 'export_decl' || s.type === 'export')) {
		for (const stmt of body) {
			if (stmt.type === 'export_decl') {
				const decl = stmt.declaration;
				if (decl.type === 'var_decl') {
					for (const d of decl.declarations) {
						if (typeof d.name === 'string')
							scope.copy(inner, d.name, d.name);
					}
				} else if ('name' in decl) {
					scope.copy(inner, decl.name, decl.name);
				}
			} else if (stmt.type === 'export' && !stmt.source && stmt.specifiers) {
				for (const spec of stmt.specifiers)
					scope.copy(inner, spec.local, spec.exported);
				
			} else if (stmt.type === 'export' && stmt.default) {
				const d = stmt.default;
				// A declaration default export is already hoisted under its own name -- just alias 'default' to it.
				if (isTsDeclaration(d)) {
					if ('name' in d)
						scope.copy(inner, d.name, 'default');
				} else if (d.type === 'identifier') {
					// `export default someIdentifier` may carry a same-named type too (`export type rational = ...; export default rational;`): `scope.copy` takes both.
					scope.copy(inner, d.name, 'default');
				} else {
					// Any other default expression has no name of its own: typed here.
					const v = typeOf(d, inner);
					if (v)
						scope.addValue('default', v);
				}
			}
		}
	} else {
		// Ambient `.d.ts` convention: a body with no `export` keyword anywhere implicitly exports every top-level declaration.
		scope.copyAll(inner);
	}
	return { scope, inner };
}

// ---- lazy return-type inference -------------------------------------------------------------

// The type arguments a generic call instantiates with: explicit ones, else TS's inference over the arguments (`inference`, the call site's own, fed
// in TS's order; a bare trial infers here), the contextual result settling what they left open. `restArgs`: what fills the rest param, as tuple elements.
export function inferTypeArgMap(sig: TS.CallSig, argTs: (Type | undefined)[], typeArgs: Type[] | undefined, scope: Scope, restArgs?: TS.TupleElement[], expected?: Type, inference?: T.Inference, err?: Err, pos?: Location): Map<string, Type> {
	const map = new Map<string, Type>();
	if (!sig.typeParams?.length)
		return map;
	// An explicit argument names things in the CALLER's scope, as an inferred one does (`T.Inference` stamps those), but is
	// substituted into the callee's structure and resolved there. Defaults and constraints are the callee's own.
	if (typeArgs) {
		sig.typeParams.forEach((p, i) => map.set(p.name, typeArgs[i] ? T.stampScope(typeArgs[i], scope) : p.default ?? T.ANY));
		return map;
	}
	// A callback's own return, when the callback wasn't typed in order by the call site: heard only after the destination.
	const deferred: T.Deferred[] = [];
	if (!inference) {
		inference = new T.Inference(sig.typeParams, scope, T.declScopeOf(sig, scope));
		argTs.forEach((t, i) => {
			const p = sig.params[i];
			if (t && p?.typeAnnotation)
				inference!.infer(p.typeAnnotation, t, deferred);
		});
		if (expected && sig.returnType)
			inference.inferReturn(sig.returnType, expected);
	}
	// The rest arguments infer as one tuple, as TS synthesizes it: against an array its elements are ONE candidate (`new Array(false, 1, 'x')`),
	// against a union each member.
	if (sig.rest?.typeAnnotation && restArgs?.length)
		inference.infer(sig.rest.typeAnnotation, { type: 'tuple', elements: restArgs }, deferred);
	for (const { paramT, argT, contra } of deferred)
		inference.infer(paramT, argT, undefined, contra);
	const inferred = inference.current();
	sig.typeParams.forEach(p => {
		const t = inferred.get(p.name);
		if (t && !inference!.wasDefaulted(p.name)) {
			// As TS's `getInferredType`: an inference its constraint does not admit gives way to the constraint, and the argument then fails against it.
			const constraint = p.constraint && T.substituteType(p.constraint, inferred);
			map.set(p.name, constraint && !T.isAssignable(t, constraint, scope) ? constraint : t);
			return;
		}
		const assumed = t ?? p.default ?? p.constraint ?? T.UNKNOWN;
		map.set(p.name, assumed);
		// A default is a silent fallback, as in TS; flagged only when a supplied argument mentions `p.name` and still could not pin it. Not one fixed with
		// nothing inferred to type a callback's parameters (`new Promise(resolve => ...)`): TS has no candidate there either.
		if (err && pos && !p.default && !inference!.wasDefaulted(p.name) && sig.params.some((prm, i) => argTs[i] && prm.typeAnnotation && T.mentionsTypeParam(prm.typeAnnotation, p.name)))
			err(SEVERITY.GAP, pos)`Type parameter '${p.name}' could not be inferred from the arguments; assumed '${show().type(assumed)}'`;
	});
	return map;
}

// Instantiates `sig` against `argTs`, substituting type params through params/return type. Pure -- doesn't validate (see `argsFit`).
function instantiate(sig: TS.CallSig, argTs: (Type | undefined)[], typeArgs: Type[] | undefined, scope: Scope, pos: Location, restArgs?: TS.TupleElement[], expected?: Type, err?: Err, inference?: T.Inference): TS.CallSig & { typeArgs?: Map<string, Type> } {
	// `declScope` travels with the result -- e.g. into `argsFit`, which only ever sees this instantiated object, never `sig` itself.
	const { params, rest, declScope } = sig, returnType = sig.returnType ?? T.ANY;
	if (!sig.typeParams?.length)
		return { params, rest, returnType, declScope };
	const map = inferTypeArgMap(sig, argTs, typeArgs, scope, restArgs, expected, inference, err, pos);
	return {
		params:		params.map(p => p.typeAnnotation ? { ...p, typeAnnotation: T.substituteType(p.typeAnnotation, map) } : p),
		rest:		rest?.typeAnnotation ? { ...rest, typeAnnotation: T.substituteType(rest.typeAnnotation, map) } : rest,
		returnType:	T.substituteType(returnType, map),
		declScope,
		typeArgs:	map,
	};
}

// ---- expressions ----------------------------------------------------------------------------

// `widen: false` gives an expression's precise type -- what an assignability check compares, as TS checks a fresh literal.
type typeOf = (e: Expr, scope: Scope, expected?: Type, widen?: boolean)=>Type;
export function typeOf1(err?: Err, stamp = true): typeOf {
	return (e, scope, expected, widen = true) => {
		const quiet = scope.isQuiet();
		return typeOf(e, scope, widen, expected, undefined, quiet ? undefined : err, stamp && !quiet);
	};
}

// `expected`: the contextual type, which lets a generic call infer what its arguments leave open from where the result goes. `stamp`: this is the
// check pass, so each node it types records that type (`checkedTypeOf`). `overStamps`: a later query reads stamped nodes' types.
export function typeOf(e: Expr, scope: Scope, widen = true, expected?: Type, yieldCollector?: Type[], err?: Err, stamp = false, overStamps = false): Type {
	// `recurse` computes the PRECISE type; widening is applied once, to the result.

	// Memoized per (node, expected) for this one call: a chained call's receiver is re-derived through several paths, which compounds to 2^N
	// evaluations over a chain of N calls. A second visit's side effects (diagnostics, yields) are exact duplicates.
	const recurseCache = new Map<Expr, Map<Type | undefined, Type>>();

	// Widened once, here: a bare literal never widens itself, so `as const` can see the precise type deeper; a frozen leaf stays at any depth.
	const result = recurse(e, expected);
	// A freshly inferred function type may carry an unstamped ref in a param annotation (a nested closure that never gets an unmuted check);
	// `scope` is where it was written, and stamping skips what is tagged.
	T.stampScope(result, scope);
	return widen ? T.widenLiterals(result) : result;

	// `++`/`--` leave the operand stepped (never overflowing its machine int, by the user's rule), and the flow keeps that range.
	function stepOperand(operand: Expr, argT: Type, op: '++' | '--'): Type | undefined {
		const old	= numericSlot(argT, scope);
		const unit	= old && unitRange(old.base);
		const next	= old && unit && T.rangeStep(old, op === '++' ? unit : T.rangeUnOp('-', unit)!);
		const key	= T.pathKey(operand);
		if (key && (err || stamp || scope.isQuiet()))
			assignFlow(scope, key, next ? T.rangeToType(next) : T.widenLiterals(argT), stamp);
		return next && T.rangeToType(next);
	}

	// A step's value (`x + a` in `x = x + a`) is the stepped range, which never overflows its machine int.
	function stampStep(value: Expr, r: T.NumRange | undefined): T.NumRange | undefined {
		if (r && stamp && !narrowing)
			(value as { checkedType?: Type }).checkedType = T.rangeToType(r);
		return r;
	}

	function recurse(e: Expr, expected?: Type): Type {
		const stamped = overStamps ? checkedTypeOf(e) : undefined;
		if (stamped)
			return stamped;
		let byExpected = recurseCache.get(e);
		const cached = byExpected?.get(expected);
		if (cached !== undefined)
			return cached;
		const result = recurseUncached(e, expected);
		// Unlike a scope stamp, a type stamp is taken in a generic template too: an instance is a substituted COPY, re-checked, so it never inherits one.
		if (stamp && !narrowing) {
			const node = e as { checkedType?: Type; expectedType?: Type };
			node.checkedType	??= result;
			node.expectedType	??= expected;
			if (e.type === 'identifier')
				foldFlow(scope, e.name, result);
		}
		if (!byExpected)
			recurseCache.set(e, byExpected = new Map());
		byExpected.set(expected, result);
		return result;
	}
	function recurseUncached(e: Expr, expected?: Type): Type {
		const pos = (e as any).pos;
		switch (e.type) {
			case 'literal':
				if (Array.isArray(e.value)) {
					e.value.forEach(p => p.exp && recurse(p.exp));
					const text = T.literalString(e);
					return text === undefined ? T.STRING : { ...Literal(text), fresh: true };
				}
				switch (typeof e.value) {
					case 'string':
					case 'boolean':	return { ...Literal(e.value), fresh: true };
					case 'number':	return TS.RangeType('number', e.value, e.value, e.value === (e.value | 0));
					case 'bigint':	return TS.RangeType('bigint', e.value, e.value);
					case 'object':	return e.value === null ? Literal(e.value) : T.REGEXP;
				}
				break;

			case 'this':		return scope.value('this') ?? T.ANY;
			case 'super':		return scope.value('super') ?? T.ANY;
			case 'identifier':	{
				// A name destructured from a union is its source path, read in the CURRENT (narrowed) scope.
				const src = scope.source(e.name);
				if (src)
					return recurse(src);
				const t = scope.value(e.name);
				if (!t && err && scope.reportsUnknownNames())
					err(SEVERITY.ERROR, pos)`Cannot find name '${e.name}'`;
				return t ?? T.ANY;
			}

			case 'array': {
				// A tuple-typed context threads each position's context into its element and makes the literal a tuple (`[1, 2]` alone is `number[]`).
				// A spread of a tuple splices; another spread is a variadic `...T[]`. `i` is the position (unknown past one), `fromEnd` counts from the end.
				const tupleElements = (context: (el: Expr, i: number | undefined, fromEnd: number) => Type | undefined, each = (t: Type) => t,
					element = (el: Expr, c: Type | undefined) => recurse(el, c)) => {
					const out: TS.TupleElement[] = [];
					let i: number | undefined = 0;
					e.elements.forEach((el, k) => {
						if (el?.type === 'spread') {
							const t = recurse(el.operand), r = T.resolveOwn(t, scope);
							const spliced = r.type === 'tuple' ? T.flatTupleElements(r, scope) : [{ type: 'spread', argument: TS.ArrayType(iterationOrReport(t, scope, pos, err).yield) } as const];
							out.push(...spliced.map(x => x.type === 'spread' ? x : x.type === 'optional' || x.type === 'labeled' ? { ...x, element: each(x.element) } : each(x)));
							i = i !== undefined && !spliced.some(x => x.type === 'spread') ? i + spliced.length : undefined;
						} else {
							out.push(el ? each(element(el, context(el, i, e.elements.length - k))) : T.UNDEFINED);
							i = i !== undefined ? i + 1 : undefined;
						}
					});
					return out;
				};
				// CONST CONTEXT: a READONLY TUPLE whose elements keep their literals and pass the context down. As a plain
				// array, `Rule<T, const R ...>`'s `ValuesOf<R>` has no positions and every `$[i]` is the union of all of them.
				if (isConstContext(expected)) {
					const inner = expected.typeArgs?.[0];
					return { type: 'tuple', readonly: !(inner && hasMutableArrayLike(inner, scope)), elements: tupleElements((el, i) => constContextOf(el, inner && i !== undefined ? positionContext(inner, i, scope) : undefined), T.freeze) };
				}
				// A union context contributes its one array-like member (Map's `readonly (readonly [K, V])[] | null`).
				const contextual		= expected && T.resolveOwn(expected, scope);
				const arrayLike			= contextual?.type === 'union' ? T.unionMembers(contextual, scope).map(m => T.resolveOwn(m, scope)).filter(m => m.type === 'tuple' || m.type === 'array') : [];
				const resolvedExpected	= arrayLike.length === 1 ? arrayLike[0] : contextual;
				// A context with ANY tuple member makes the literal a tuple, as TS (`TA | TB` both tuples); each position's context
				// is that position across them.
				const tuples			= resolvedExpected?.type === 'tuple' ? [resolvedExpected] : arrayLike.filter((m): m is Type & { type: 'tuple' } => m.type === 'tuple');
				if (tuples.length)
					return { type: 'tuple', elements: tupleElements((_, i, fromEnd) => T.combineTypes(tuples.flatMap(t => { const c = tupleContextAt(t, i, fromEnd, scope); return c ? [c] : []; })),
						undefined, (el, c) => widenForContext(recurse(el, c), c, scope)) };
				// Otherwise an element's context is what the context iterates to (TS): an `Iterable<T>`'s `T` as much as an array's element.
				const elemExpected		= resolvedExpected?.type === 'array' ? resolvedExpected.element : contextual && iteratedContext(contextual, scope);
				const elems				= e.elements.flatMap(el => !el ? [] : el.type === 'spread' ? [iterationOrReport(recurse(el.operand), scope, pos, err).yield] : [recurse(el, elemExpected)]);
				// An EMPTY literal is its context, else TS's `never[]`, which a union (`c ? xs : []`) drops; against several array types it is `never[]` too.
				if (!elems.length)
					return resolvedExpected?.type === 'array' ? resolvedExpected : TS.ArrayType(arrayLike.length > 1 ? T.NEVER : elemExpected ?? T.NEVER);
				// LITERAL WIDENING as TS does it: `[1, 2, 3]` is mutable, so `number[]`, not `(1|2|3)[]`. Not where a contextual array type supplied the
				// element, a deliberate choice; a `frozen` leaf (`as const`) stays.
				const elem = T.combineTypes(elems);
				return TS.ArrayType(elemExpected ? elem : T.widenLiterals(elem));
			}

			case 'object': {
				// A union context is first narrowed by this literal's own discriminant values, as TS does (`type: 'inter'` picks Inter).
				// Inside a const context the contextual type is what it stands in for: a call there is ordinary (`{ entry: assign(...) }`).
				const inner		= isConstContext(expected) ? expected.typeArgs?.[0] : expected;
				const context	= inner && discriminateContext(inner, e, scope);
				// A later property overrides an earlier same-named one, as in JS, spreads included; a spread of a union distributes, one shape per alternative.
				// `parts`: what precedes `members` -- object parts and spreads of a type with no enumerable members (a type parameter), intersected.
				const shape = (members: TS.TypeMember[] = [], byKey = new Map<string, number>(), parts: Type[] = []) => ({ members, byKey, parts,
					push(m: TS.TypeMember) {
						const key = 'key' in m ? T.memberKey(m.key) : undefined;
						if (key !== undefined) {
							const i = byKey.get(key);
							if (i !== undefined) {
								// A later OPTIONAL property does not erase an earlier one: absent at run time, it leaves the earlier value (`{...defaults, ...opts}`), so the
								// result is either type, optional only if both were. An explicit `key: value` or a required spread member overrides outright.
								const prev = members[i];
								// Resolved before combining: a mapped type's member (`Partial<typeof D>['k']`) is an indexed access that would not collapse into the earlier
								// `string`. Its `| undefined` is dropped: the absent case is what the earlier member covers.
								members[i] = m.type === 'property' && prev.type === 'property' && hasMod(m, 'optional')
									? TS.TypeProperty(key, T.combineTypes([prev.typeAnnotation, T.nonNullable(T.resolveOwn(m.typeAnnotation, scope), scope)]), hasMod(prev, 'optional') ? ['optional'] : undefined)
									: m;
								return;
							}
							byKey.set(key, members.length);
						}
						members.push(m);
					},
				});
				let shapes	= [shape()];
				const push	= (m: TS.TypeMember) => shapes.forEach(s => s.push(m));
				// An interface that EXTENDS another resolves to an INTERSECTION: each part contributes its members, a later part winning. Undefined where
				// they are not determinable.
				const intersectionMembers = (t: Type, depth = 4): TS.TypeMember[] | undefined => {
					if (!depth)
						return undefined;
					const parts = T.flattenIntersection(t, scope).map(x => {
						const r = T.resolveMembers(x, scope);
						return r.type === 'object' ? r.members : r.type === 'intersection' ? intersectionMembers(r, depth - 1) : undefined;
					});
					return parts.every(m => !!m) ? parts.flat() as TS.TypeMember[] : undefined;
				};
				// A get/set pair is one property, and a lone setter is one too.
				const accessorOf = (kind: 'get' | 'set', key: string | undefined) => e.properties.find((q): q is JS.Method<Type> => q.type === kind && T.memberKey(q.key) === key);
				for (const p of e.properties) {
					if (p.type === 'spread') {
						const spreadMembers = (x: Type) => {
							const t = T.resolveOwn(x, scope);
							return t.type === 'object' ? t.members : t.type === 'intersection' ? intersectionMembers(t) : undefined;
						};
						// As TS's `getSpreadType`: `any` spreads to `any`, and a type with no enumerable members (a type parameter) is intersected in.
						// A nullish or primitive alternative adds nothing, so the others' members become optional -- one shape, not one per alternative.
						const operand	= recurse(p.operand);
						// A type parameter is not its constraint: what it holds may have more members, so it stays whole.
						const typeParam	= operand.type === 'ref' && !operand.typeArgs && !!scope.type(operand.name)?.isTypeParam;
						if (!typeParam && T.isAny(T.resolveOwn(operand, scope)))
							return T.ANY;
						const members	= typeParam ? [operand] : T.unionMembers(operand, scope);
						const adds		= members.filter(x => typeParam || !(T.isNullish(x, scope) || T.isPrimitive(T.resolveOwn(x, scope)) || ['literal', 'range'].includes(T.resolveOwn(x, scope).type)));
						const optional	= (m: TS.TypeMember): TS.TypeMember => adds.length < members.length && m.type === 'property' && !hasMod(m, 'optional') ? { ...m, modifiers: [...m.modifiers ?? [], 'optional'] } : m;
						const alternatives = adds.map(x => spreadMembers(x)?.map(optional) ?? x);
						shapes = shapes.flatMap(s => alternatives.map(a => {
							if (!Array.isArray(a))
								return shape([], new Map(), [...s.parts, ...s.members.length ? [TS.ObjectType(s.members)] : [], a]);
							const next = shape([...s.members], new Map(s.byKey), s.parts);
							a.forEach(m => next.push(m));
							return next;
						}));
					} else {
						// An `expected` type propagates member by member, so an unannotated arrow or method value gets its params' types.
						const key				= T.memberKey(p.key);
						const expectedMember	= context && key !== undefined ? contextualMember(context, key, scope) : undefined;
						switch (p.type) {
							case 'method':
								applyContextualParams(p, expectedMember, scope);
								checkFunctionBody(p, p.body, scope, hasMod(p, 'async'), hasMod(p, 'generator'), hasMod(p, 'generator'), err, undefined, stamp);
								if (key !== undefined)
									push(TS.TypeMethod(p.key, T.FixSig(p, T.ANY)));
								break;
							case 'get':
								checkFunctionBody(p, p.body, scope, false, false, false, err, undefined, stamp);
								push(TS.TypeProperty(p.key, p.returnType ?? T.ANY, undefined, accessorOf('set', key)?.params[0]?.typeAnnotation));
								break;
							case 'set':
								checkFunctionBody(p, p.body, scope, false, false, false, err, undefined, stamp);
								if (!accessorOf('get', key))
									push(TS.TypeSetter(p.key, p.params[0]?.typeAnnotation ?? T.ANY));
								break;
							case 'field': {
								// A literal stays literal where its context expects one (TS's isLiteralOfContextualType): `{ kind: "mod" }` as a `Mod`.
								// A value `as const` reaches is itself in the const context, and does not widen.
								const valueConst = isConstContext(expected) ? constContextOf(p.value!, expectedMember) : undefined;
								const _t = isConstContext(expected) && valueConst ? typeOf(p.value!, scope, false, valueConst, yieldCollector, err, stamp, overStamps)
									: widenForContext(typeOf(p.value!, scope, false, expectedMember, yieldCollector, err, stamp, overStamps), expectedMember, scope);
								if (key !== undefined)
									push(TS.TypeProperty(p.key, _t));
								break;
							}
						}
					}
				}
				return T.combineTypes(shapes.map(s => {
					const all = [...s.parts, ...s.members.length || !s.parts.length ? [TS.ObjectType(s.members)] : []];
					return all.length === 1 ? all[0] : TS.IntersectionType(all);
				}));
			}

			case 'function': {
				const csig	= applyContextualParams(e, expected, scope);
				const self	= () => TS.FunctionType({ ...T.FixSig(e, T.ANY, e.returnType), origin: e });
				const inner	= ownThis(new Scope(scope));
				// Lazy: a recursive read while the return is still being inferred sees it as `any`, as TS does.
				if (e.name)
					inner.addLazyValue(e.name, self);
				checkFunctionBody(e, e.body, inner, hasMod(e, 'async'), hasMod(e, 'generator'), hasMod(e, 'generator'), err, shapedHint(csig?.returnType, scope), stamp);
				return self();
			}
			case 'arrow': {
				const csig = applyContextualParams(e, expected, scope);
				checkFunctionBody(e, e.body, scope, hasMod(e, 'async'), false, false, err, shapedHint(csig?.returnType, scope), stamp);
				return TS.FunctionType({ ...T.FixSig(e, T.ANY, e.returnType), origin: e });
			}

			case 'member': {
				const key		= assignmentTargets.has(e) ? undefined : T.pathKey(e);
				const refined	= key && scope.value(key);	// dotted keys live only in narrowings
				if (refined) {
					// The narrowed path answers without the receiver, which the check pass still types, so it carries a stamp too.
					if (stamp)
						recurse(e.object);
					return refined;
				}
				const objT	= recurse(e.object);
				// `chained`: `a?.b.c`'s `.c` continues a `?.` chain, so it short-circuits when `a` is nullish; looked up on the non-nullish part of `objT`.
				const chained		= isOptionalChainLink(e);
				if (T.isRef(T.resolve(scope, T.nonNullable(objT, scope, chained)), 'ArrayBuffer') && e.property === 'byteLength')
					return TS.RangeType('number', 0, 0x7fffffff, true);

				// Only a `?.` (direct or chained) looks the property up on `objT`'s non-nullish part (`lookupMember` needs every union member to have it).
				// A plain access keeps the nullish members, so `x.y` on a possibly-null `x` is still reported.
				const t		= T.lookupMember(T.nonNullable(objT, scope, chained), e.property, scope);
				if (!t) {
					if (err && !e.optional && T.sealed(objT, scope))
						err(SEVERITY.ERROR, pos)`Property '${e.property}' does not exist on type '${show().type(objT)}'`;
					return T.ANY;
				}
				// `lookupMember` gives an optional property's declared type; a read sees its `| undefined`, as a chained access does.
				return T.optional(t, chained || T.memberOptional(objT, e.property, scope));
			}
			case 'index': {
				// A literal index is a path (`args[0]`) that narrowing refines, exactly as a member's is.
				const indexKey	= assignmentTargets.has(e) ? undefined : T.pathKey(e);
				const refined	= indexKey && scope.value(indexKey);
				if (refined)
					return refined;
				const rawObjT = recurse(e.object);
				// `chained`: a chain continuation short-circuits too (`case 'member'`).
				const chained = isOptionalChainLink(e);
				// A read the program tests for absence answers `T | undefined`, as an optional chain does (`markAbsenceTests`).
				const absent = chained || !!(e as { testedForAbsence?: boolean }).testedForAbsence;
				// Only the non-nullish part of `objT` is indexed, or no branch below matches a union. `resolveMembers`: each branch reads a STRUCTURE (an element,
				// a tuple, an index signature, a key), so a named class gives up its nominal identity here.
				const declaredT	= T.nonNullable(rawObjT, scope, absent);
				const objT		= T.resolveMembers(declaredT, scope);
				const indexT	= recurse(e.index);
				// A key typed as string literals (`o[k ? 'a' : 'b']`, a `const` key) reads each property it names, as TS's `T[K]`.
				const named	= T.unionMembers(indexT, scope).map(m => T.literalString(m));
				const keys	= named.length && named.every((k): k is string => k !== undefined) ? named : undefined;
				// A symbol key reads the member a computed key of its path declares (`array[Symbol.iterator]`), never an element: a `unique symbol`'s
				// identity is not modeled, so the path names it, as `memberKey` keys the declaration. Declared members only; a `symbol` index signature below.
				const symbolKey		= T.typeofName(indexT, scope) === 'symbol' ? T.memberKey({ computed: e.index }) : undefined;
				const symbolMember	= symbolKey && T.lookupMember(objT, symbolKey, scope, 10, true);
				if (symbolMember)
					return T.optional(symbolMember, absent);
				if (objT.type === 'array')
					return T.optional(objT.element, absent);
				// A union of tuples and arrays reads each member's position (TS's getIndexedAccessType); a member too short or optional there reads `undefined`.
				if (objT.type === 'union' && T.isLiteral(e.index, 'number')) {
					const i			= e.index.value;
					const members	= T.unionMembers(objT, scope).map(m => T.resolveOwn(m, scope));
					if (members.every(m => m.type === 'tuple' || m.type === 'array'))
						return T.optional(T.combineTypes(members.map(m => m.type === 'array' ? m.element : T.tupleReadType(m, i, scope) ?? T.UNDEFINED)), absent);
				}
				// A literal index reads that property of each member: a tuple's position, an interface's `0:` key.
				const atKey = objT.type !== 'tuple' && T.isLiteral(e.index, 'number') && T.lookupMember(objT, String(e.index.value), scope);
				if (atKey)
					return T.optional(atKey, absent);
				const arrayUnion = !keys && T.arrayUnionAsArray(objT, scope);
				if (arrayUnion)
					return T.optional(arrayUnion.element, absent);
				// A tuple indexed by a COMPUTED number reads any of its positions, as TS's `T[number]`.
				if (objT.type === 'tuple' && !T.isLiteral(e.index, 'number') && T.isNumberLike(indexT, scope))
					return T.optional(T.combineTypes(objT.elements.map((_, i) => T.tupleReadType(objT, i, scope) ?? T.UNDEFINED)), absent);
				if (objT.type === 'tuple' && T.isLiteral(e.index, 'number')) {
					const t = T.tupleReadType(objT, e.index.value, scope);
					if (err && !t)
						err(SEVERITY.ERROR, pos)`Tuple type '${show().type(objT)}' has no element at index ${e.index.value}`;
					return t ? T.optional(t, absent) : T.ANY;
				}
				// A declared `[i: number]: T` index signature (`Record<number, T>`, typed arrays), searched through every intersection part (`indexSignatureOf`):
				// for a computed key no named property applies.
				// A computed key reads the signature its type selects, as TS's getIndexedAccessType: a number key a number signature, else (and any
				// other key) a string one.
				if (!keys) {
					const idxT = (T.isNumberLike(indexT, scope) ? T.indexSignatureOf(objT, scope) : undefined) ?? T.stringIndexSignatureOf(objT, scope);
					return idxT ? T.optional(idxT, absent) : T.ANY;
				}
				const found = keys.map(k => T.lookupMember(objT, k, scope));
				// Only a WRITTEN key is reported: one typed as literals reads `any`, as TS's implicit any does without `noImplicitAny`.
				if (err && T.literalString(e.index) !== undefined && !found[0] && T.sealed(objT, scope))
					err(SEVERITY.ERROR, pos)`Property '${keys[0]}' does not exist on type '${show().type(declaredT)}'`;
				return found.every((t): t is Type => !!t)
					? T.optional(T.combineTypes(found), absent || keys.some(k => T.memberOptional(objT, k, scope)))
					: T.ANY;
			}

			case 'call':
			case 'new': {
				// `super(...)` invokes the base CONSTRUCTOR, resolved as `new` is, against the one `classBodyScopes` bound. The receiver is typed once,
				// as typing it twice duplicated diagnostics.
				const construct = e.type === 'new' || e.callee.type === 'super';
				let calleeObjT: Type | undefined;
				if (e.type === 'call' && e.callee.type === 'member') {
					calleeObjT = recurse(e.callee.object);
					// `super.m()`'s receiver is the DERIVED one: a base method returning `this` yields the current `this`, not the base instance.
					if (e.callee.object.type === 'super')
						calleeObjT = scope.value('this') ?? calleeObjT;
				}
				// `obj?.method(...)` (or a continued chain) and `f?.()`: the call resolves against the callee's non-nullish signature, and its
				// short-circuit `undefined` is reattached to the result.
				const calleeOptional = (e.callee.type === 'member' && isOptionalChainLink(e.callee)) || !!(e as { optional?: boolean }).optional;
				// An immediately invoked function or arrow: TS types each unannotated parameter by its argument, widened. A quiet query,
				// as an overload trial types an argument, so the argument's own check below reports once.
				const iife		= e.type === 'call' && (e.callee.type === 'arrow' || e.callee.type === 'function') && !e.arguments.some(a => a.type === 'spread')
					? TS.FunctionType({ params: e.arguments.map((a, i) => ({ key: `$${i}`, typeAnnotation: trial(() => typeOf(a, scope, true, undefined, yieldCollector, undefined)) })), returnType: T.ANY })
					: undefined;
				let calleeT		= T.mergeIdenticalSignatures(T.resolveOwn(T.nonNullable(e.callee.type === 'super' ? scope.value('super()') ?? T.ANY : recurse(e.callee, iife), scope, calleeOptional), scope));
				if (calleeT.type === 'union' && calleeObjT && e.callee.type === 'member') {
					const arr		= T.arrayUnionAsArray(T.nonNullable(calleeObjT, scope, calleeOptional), scope);
					const method	= arr && T.lookupMember(arr, e.callee.property, scope);
					if (method)
						calleeT = T.resolveOwn(method, scope);
				}
				// Explicit call-site type args are raw AST: stamped, or a ref substituted into the callee's body would resolve in the callee's scope.
				let typeArgs	= e.typeArgs?.map(t => T.stampScope(t, scope));
				// `super(...)` against a generic base takes the `extends` clause's type arguments (`extends A<string>`): the base's `T` is fixed.
				if (!typeArgs && e.callee.type === 'super') {
					const base = scope.value('super');
					typeArgs = base?.type === 'ref' ? base.typeArgs : undefined;
				}
				// An `any` callee is called (or constructed) as TS does: the result is `any`, and every argument is still checked.
				if (T.isRef(T.resolveOwn(calleeT, scope), 'any')) {
					for (const a of e.arguments)
						recurse(a.type === 'spread' ? a.operand : a);
					return T.ANY;
				}
				let overloads: TS.CallSig[] | undefined;
				const parts = calleeT.type === 'intersection' ? calleeT.types.map(p => T.resolveOwn(p, scope)) : [calleeT];
				// A bare `constructor` part is not taken for a plain call, or it pre-empts the member scan's call-vs-construct preference: `BigInt(5)` is `bigint`,
				// by `declare var BigInt`'s call signature beside the class's constructor. `new` on an intersection follows TS's mixin rule (`T.constructSignatures`).
				const mixedCtors = construct && calleeT.type === 'intersection' ? T.constructSignatures(calleeT, scope) : [];
				if (mixedCtors.length > 1)
					overloads = mixedCtors;
				let sig: TS.CallSig|undefined = mixedCtors.length === 1 ? mixedCtors[0] : mixedCtors.length ? undefined
					: construct ? parts.find(p => p.type === 'constructor') ?? parts.find(p => p.type === 'function')
					: parts.find(p => p.type === 'function');
				sig ??= overloads ? undefined : T.unionSignature(calleeT, construct ? 'construct' : 'call', scope);
				if (!sig && !overloads) {
					// Each kind takes only its OWN signatures: a plain call on a construct-only value is TS2348, `new` on a call-only one TS7009.
					const members 		= T.collectMembers(calleeT, scope);
					const constructs	= members.filter(m => m.type === 'construct');
					const callSigs		= members.filter(m => m.type === 'call');
					const own			= construct ? constructs : callSigs;
					// `new` still falls back to a call signature: TS7009 is implicit-any, reported only under `noImplicitAny` (untracked here), and still `any`.
					// TS2348 is unconditional, so a plain call on a construct-only value is rejected.
					const calls			= own.length || !construct ? own : callSigs;
					if (calls.length === 1) {
						sig = calls[0];
					} else if (calls.length > 1) {
						// Resolved below, once argument types are known; explicit type arguments first rule out the arities they do not fit.
						overloads = typeArgs ? calls.filter(c => T.typeArgArityFits(c, typeArgs.length)) : calls;
					} else if (!construct && (constructs.length > 0 || parts.some(p => p.type === 'constructor'))) {
						if (err)
							err(SEVERITY.ERROR, pos)`Type '${show().type(calleeT)}' is not callable without 'new' in '${show().expression(e)}'`;
						return T.ANY;
					} else if (T.sealed(calleeT, scope)) {
						if (err)
							err(SEVERITY.ERROR, pos)`Type '${show().type(calleeT)}' is not callable in '${show().expression(e)}'`;
						return T.ANY;
					}
				}

				// Contextual parameter typing (`arr.map(x => x.foo)`) from the declared (pre-substitution) param, mutating the AST before `argTs` checks each
				// argument's body. A `trial` reports nothing, but still FIXES a callback's parameters, as TS does.
				const settle = (sig: TS.CallSig, trial: boolean) => {
					const arg		= (a: Expr, exp?: Type) => trial ? typeOf(a, scope, false, exp, yieldCollector, undefined) : recurse(a, exp);
					const declScope	= T.declScopeOf(sig, scope);

					// Each non-callback argument is typed against its declared parameter as `expected` (`heap.push([1, ...])` against a tuple parameter), and
					// feeds inference before any callback. Past the fixed parameters the REST names the argument, a tuple rest by position.
					const declaredArg = (i: number) => T.paramTypeAt(sig!, i, scope);
					// TS's two passes: every non-callback argument feeds inference first, then each callback in order, its context FIXING the type parameters its
					// own parameters read, its return feeding only those still open. Explicit type arguments leave nothing to infer.
					const explicit	= typeArgs && sig.typeParams?.length ? new Map(sig.typeParams.map((p, i) => [p.name, typeArgs![i] ?? p.default ?? T.ANY] as const)) : undefined;
					const inference	= !explicit && sig.typeParams?.length ? new T.Inference(sig.typeParams, scope, declScope) : undefined;
					// A declared `this` is inferred from the receiver before any argument (`get<X>(this: X, s)` binds `X` to `base`), its non-nullish part for `?.`.
					if (inference && sig.thisType && calleeObjT)
						inference.infer(sig.thisType, T.nonNullable(calleeObjT, scope, calleeOptional));
					// In order, as TS does: each argument's context is its parameter under what the arguments before it inferred
					// (`mapObject(q, { ps: mapArray(p => ...) })` knows `N` from `q`, so the inner call can infer its `T`). What the result's context
					// inferred reaches only a generic call's (`compose(filter(x => ...))`): a `const T` argument keeps its bare `T`.
					const soFar = (declared: Type | undefined, viaResult = false) => declared && (explicit ? T.substituteType(declared, explicit)
						: inference ? T.substituteType(declared, new Map(sig!.typeParams!.flatMap(p => {
							const t = viaResult ? inference.inferred(p.name) : inference.fromCandidates(p.name);
							return t ? [[p.name, t] as const] : [];
						})))
						: declared);
					const returned	= sig.returnType && T.resolveOwn(sig.returnType, declScope);
					const lifting	= !explicit && !!sig.typeParams?.length && returned?.type === 'function' && !returned.typeParams?.length;
					const lifted: TS.TypeParam[] = [];
					// Lifted only where the context leaves them open (a parameter type still naming this call's own parameters); else
					// instantiated in that context as it now stands (`compose(list, box)`: `box`'s `V` is `list`'s `T[]`).
					const liftOrInstantiate = (t: Type, declared: Type | undefined): Type => {
						const f			= T.resolveOwn(t, scope);
						const declSig	= declared && T.findFunctionType(declared, declScope);
						const want		= declared && T.findFunctionType(soFar(declared)!, declScope);
						if (f.type !== 'function' || !f.typeParams?.length)
							return t;
						const open = !declSig || !want || declSig.params.some(p => p.typeAnnotation && sig!.typeParams!.some(q => T.mentionsTypeParam(p.typeAnnotation!, q.name) && !inference?.fromCandidates(q.name)));
						return open ? liftGeneric(f, scope, lifted, liftScope) : TS.FunctionType(T.instantiateInContextOf(f, f.typeParams, want, scope, declScope));
					};
					const liftScope = new Scope(scope);
					// A param no argument pins down may come from where the call's result is going (`new Promise<T>((resolve) => ...)`). Heard first, as TS
					// does, at the lowest priority: an argument's own context then sees it (`compose(filter(x => ...))`). A GENERIC context is heard after
					// the arguments, as its lifted parameters must meet those the generic function arguments lift (`compose(unbox, unlist)`).
					const resultFirst	= !lifting || !isGenericFunction(expected ?? T.ANY, scope);
					const inferFromResult = () => {
						if (inference && expected && sig!.returnType)
							inference.inferReturn(sig!.returnType, lifting ? liftGeneric(expected, scope, lifted, liftScope) : expected);
					};
					if (resultFirst)
						inferFromResult();
					const preArgTs = e.arguments.map((a, i) => {
						if (a.type === 'function' || a.type === 'arrow' || a.type === 'spread')
							return undefined;
						// The inner call of `new Map(xs.map(x => [a, b]))` reverse-matches its own `U` from the tuple shape (`instantiate`'s `fromExpected`).
						const t = arg(a, argContext(a, soFar(declaredArg(i), a.type === 'call'), sig!, scope));
						// A generic function argument waits until every other argument (and the result's context) has spoken, as TS's does.
						if (lifting && t && isGenericFunction(t, scope))
							return t;
						const p = sig!.params[i];
						if (inference && t && p?.typeAnnotation)
							(a.type === 'object' || a.type === 'array' ? inference.inferFromLiteral : inference.infer).call(inference, p.typeAnnotation, t);
						return t;
					});
					if (!resultFirst)
						inferFromResult();
					if (lifting)
						preArgTs.forEach((t, i) => {
							const p = sig!.params[i];
							if (!t || !isGenericFunction(t, scope))
								return;
							preArgTs[i] = liftOrInstantiate(t, declaredArg(i));
							if (inference && p?.typeAnnotation)
								inference.infer(p.typeAnnotation, preArgTs[i]!);
						});

					const contextOf = (a: Expr, declared: Type | undefined) => declared && (explicit ? T.substituteType(declared, explicit)
						: !inference ? declared : isContextSensitive(a) ? inference.contextFor(declared) : T.substituteType(declared, inference.current()));
					const typeCallback = (a: Expr & { type: 'function' | 'arrow' }, i: number) => {
						const declared		= declaredArg(i);
						// TS's inferFromAnnotatedParameters: `(t1: D, t2) => ...` against `(t: T, t1: T) => void` fixes `T = D` from `t1` first, so `t2` sees `D`.
						// A callback's own `...rest` annotation is not a source yet.
						const declaredSig	= inference && declared && T.findFunctionType(declared, scope);
						if (declaredSig)
							a.params.forEach((p, k) => {
								const target = T.paramTypeAt(declaredSig, k, scope);
								if (p.typeAnnotation && target)
									inference!.infer(target, p.typeAnnotation);
							});
						const contextual	= contextOf(a, declared);
						applyContextualParams(a, contextual, scope);
						// For codegen, which compiles an overload's IMPLEMENTATION and never sees this; only once fully determined, since the same call is also typed
						// without context.
						const defaults	= new Map(sig!.typeParams?.filter(p => p.default && !inference?.inferred(p.name)).map(p => [p.name, p.default!] as const));
						const settled	= contextual && defaults.size ? T.substituteType(contextual, defaults) : contextual;
						if (!trial && !trying && settled && !sig.typeParams?.some(p => T.mentionsTypeParam(settled, p.name)))
							(a as any).contextualType ??= T.stampScope(settled, scope);
						// The contextual signature is the body's too: `xs.map(x => [a, b])` against `[K, V][]` produces a TUPLE only if its return is contextually typed.
						const t = arg(a, contextual);
						if (inference && declared)
							inference.infer(declared, t);
						return t;
					};
					const annotated = new Map(e.arguments.flatMap((a, i) => (a.type === 'function' || a.type === 'arrow') && !isContextSensitive(a) ? [[i, typeCallback(a, i)] as const] : []));

					const spreads: TS.TupleElement[][] = [];
					const argTs = e.arguments.map((a, i) => {
						if (a.type === 'function' || a.type === 'arrow')
							return annotated.get(i) ?? typeCallback(a, i);
						if (a.type !== 'spread')
							return preArgTs[i];
						const t		= T.resolveOwn(arg(a.operand), scope);
						if (t.type === 'array' || t.type === 'tuple')
							spreads[i] = t.type === 'array' ? [{ type: 'spread', argument: t }] : t.elements;
						return undefined;
					});
					// A spread and the plain arguments past `sig.params.length` fill the rest parameter, in order. `restKnown`: every spread's elements are.
					const restArgs	= e.arguments.flatMap((a, i) => a.type === 'spread' ? spreads[i] ?? [] : i >= sig!.params.length && argTs[i] ? [argTs[i]] : []);
					const restKnown	= e.arguments.every((a, i) => a.type !== 'spread' || !!spreads[i]);

					const inst = instantiate(sig, argTs, typeArgs, scope, pos, restArgs, expected, trial ? undefined : err, inference);
					return { ...inst, returnType: withLifted(inst.returnType, lifted, scope) ?? inst.returnType, lifted, declScope, argTs, restArgs, restKnown };
				};

				// Overload resolution, TS's two passes: each candidate is tried with its context-sensitive callbacks untyped (fitting as any function); one that fits
				// types them, FIXING their parameters, and must still fit, or the next is tried. No fit at all stays a warning.
				if (overloads) {
					const hasSpread = e.arguments.some(a => a.type === 'spread');
					// A nested call's type depends on its context too: its callback's return is fixed by the first context it is typed in.
					const typedIn		= e.arguments.map(() => new Map<Type | undefined, Type>());
					const fits			= (c: TS.CallSig) => candidateFits(c, e.arguments, scope, typeArgs, typedIn, yieldCollector, pos);
					sig = overloads.find((c, k) => {
						if (!fits(c))
							return false;
						// The last candidate that can fit needs no second pass: resolution settles on it either way.
						if (!e.arguments.some(isContextSensitive) || !overloads!.slice(k + 1).some(fits))
							return true;
						// Undone after: the contextual parameter types this candidate writes onto the callbacks must not become annotations for the final pass.
						const typed = ahead(() => settle(c, true));
						return T.argsFit(typed, typed.argTs, scope, hasSpread);
					});
				}
				if (overloads && !sig && err)
					err(SEVERITY.WARNING, pos)`No overload of '${show().expression(e.callee)}' matches this call; arguments left unchecked`;

				if (sig) {
					const { declScope, argTs, params, rest, returnType, restArgs, restKnown, typeArgs: inferred, lifted } = settle(sig, false);
					// Not gated on `stamp`: a resolution changes no scope, the real check reaches a source call first (`??=`), and a codegen query resolves a call
					// codegen synthesized. A loop head's quiet walk sees types still widening.
					if (!narrowing && !trying && !scope.isQuiet())
						(e as { checkedCall?: CheckedCall }).checkedCall ??= { sig, typeArgs: inferred, lifted: lifted.length ? lifted : undefined };
					const firstSpread = e.arguments.findIndex(a => a.type === 'spread');

					// TBD: check if callee if pure

					if (err && firstSpread < 0) {
						// In an IIFE an unannotated parameter no argument reaches is optional.
						const iife		= e.type === 'call' && (e.callee.type === 'function' || e.callee.type === 'arrow') ? e.callee : undefined;
						const required	= T.minArgumentCount({ params }, scope, i => !!iife && i >= argTs.length && !iife.params[i]?.typeAnnotation);
						const max		= sig.rest ? Infinity : params.length;
						if (argTs.length < required || argTs.length > max)
							err(SEVERITY.ERROR, pos)`Expected ${required === max ? required : required + '-' + (max === Infinity ? 'more' : max)} arguments, but got ${argTs.length} in '${show().expression(e)}'`;
					}
					// Checkable while no spread lands on a fixed parameter: the rest takes every argument past them as ONE tuple, a spread of unknown length as a spread
					// element, as TS checks it. Not gated on `err`: the flow STAMP is codegen data, and an imported module is only checked muted.
					if (firstSpread < 0 || firstSpread >= params.length) {
						// An argument typed in a context still naming the callee's own unsolved parameters (`[]` against `U[]`) carries them:
						// read at their solutions, as TS instantiates a contextual type. A name the call site binds itself is its own.
						const leaked = inferred && new Map([...inferred].filter(([name]) => !scope.type(name)));
						argTs.forEach((arg, i) => {
							const t = arg && leaked?.size ? T.substituteType(arg, leaked) : arg;
							const p = params[i];
							if (t && p && p.typeAnnotation) {
								if (!scope.isQuiet())
									stampFlow(e.arguments[i], p.typeAnnotation, declScope);
								// An optional parameter also accepts `undefined`.
								if (err && !checkAssignable(t, hasMod(p, 'optional') ? TS.UnionType([p.typeAnnotation, T.UNDEFINED]) : p.typeAnnotation, scope, pos, declScope, err))
									err(SEVERITY.ERROR, pos)`Argument of type '${show().type(t)}' is not assignable to parameter '${show().bindingTarget(p.key)}: ${show().type(p.typeAnnotation)}' in '${show().expression(e)}'`;
								else if (err)
									checkExcessProps(e.arguments[i], p.typeAnnotation, pos, declScope, err);
							}
						});
						// Each plain argument past the fixed parameters fills an ELEMENT of the rest array.
						const restEl = rest?.typeAnnotation && T.arrayLikeElement(T.resolveOwn(rest.typeAnnotation, declScope));
						if (restEl)
							e.arguments.forEach((a, i) => i >= params.length && a.type !== 'spread' && !scope.isQuiet() && stampFlow(a, restEl, declScope, true));
						const restT: Type = { type: 'tuple', elements: restArgs };
						if (err && rest?.typeAnnotation && restArgs.length && restKnown && !checkAssignable(restT, rest.typeAnnotation, scope, pos, declScope, err))
							err(SEVERITY.ERROR, pos)`Arguments of type '${show().type(restT)}' are not assignable to rest parameter '...${show().bindingTarget(rest.key)}: ${show().type(rest.typeAnnotation)}' in '${show().expression(e)}'`;
					}

					if (e.callee.type === 'member' && e.callee.object.type === 'identifier' && e.callee.object.name === 'Math')
						return narrowMath(e.callee.property, params, scope) ?? returnType!;

					// A predicate return as a plain value is `boolean` (or `void` asserting); only `narrow()`'s `case 'call'` reads the predicate.
					const result = returnType && returnType.type === 'predicate' ? (returnType.asserts ? T.VOID : T.BOOLEAN) : returnType!;
					// A `this`-typed return (`sort(): this`) is the receiver's type, substituted here (`this` as a type is never resolved eagerly).
					if (e.callee.type === 'super')
						return T.VOID;
					return T.optional(e.callee.type === 'member' ? T.substituteThisType(result, calleeObjT ?? recurse(e.callee.object)) : result, calleeOptional);
				}
				return T.ANY;
			}

			// `expr<T,U>` (TS 4.7+) pins a generic's type params without calling it; an overloaded callee keeps every arity-compatible signature, instantiated.
			case 'instantiation': {
				const calleeT	= T.resolveOwn(recurse(e.expression), scope);
				// Raw AST type args, stamped as for a call.
				const typeArgs	= e.typeArgs.map(t => T.stampScope(t, scope));
				const fnPart	= (calleeT.type === 'intersection' ? calleeT.types.map(p => T.resolveOwn(p, scope)) : [calleeT]).find(p => p.type === 'function' || p.type === 'constructor');
				if (fnPart)
					return { type: fnPart.type, ...instantiate(fnPart, [], typeArgs, scope, pos, undefined, undefined, err) };
				if (calleeT.type === 'object') {
					// Only the signatures the type arguments fit (TS's getInstantiatedSignatures).
					const calls = calleeT.members.filter(m => m.type === 'call' || m.type === 'construct').filter(m => T.typeArgArityFits(m, typeArgs.length));
					if (calls.length)
						return TS.ObjectType(calls.map(m => TS.TypeMember(m.type, instantiate(m, [], typeArgs, scope, pos, undefined, undefined, err))));
				}
				return T.ANY;
			}

			case 'await':	return T.awaitType(recurse(e.operand, expected && T.awaitContext(expected)), scope);

			case 'unary': {
				const argT = recurse(e.operand);
				switch (e.operator) {
					case '!':		return T.BOOLEAN;
					case 'typeof':	return T.STRING;
					case 'void':	return T.UNDEFINED;
					case 'delete':	return T.BOOLEAN;
				}
				const stepped = (e.operator === '++' || e.operator === '--') && stepOperand(e.operand, argT, e.operator);
				if (stepped)
					return stepped;
				const r = T.resolveOwn(argT, scope);
				if (T.isAny(r))
					return T.ANY;
				const nr = numericSlot(argT, scope);
				if (nr)
					return T.rangeToType(T.rangeUnOp(e.operator, nr)!);
				switch (e.operator) {
					case '++':
					case '--':
						if (err && !T.isNumberLike(r, scope))
							err(SEVERITY.ERROR, pos)`Operand of '${e.operator}' must be numeric, got '${show().type(argT)}' in '${show().expression(e)}'`;
						return numericOf(r, scope);
					default:
						return numericOf(r, scope);
				}
			}
			case 'unary_post': {
				// As TS's `getContextualType`, a non-null assertion hands its own contextual type to its operand.
				const argT = recurse(e.operand, e.operator === '!' ? expected : undefined);
				if (e.operator === '!') {
					const t = T.resolveOwn(argT, scope);
					if (t.type === 'union') {
						const parts = t.types.filter(x => !T.isNullish(x, scope)).map(x => T.nonNullableParam(x, scope) ?? x);
						return parts.length ? T.combineTypes(parts) : t;
					}
					return T.nonNullableParam(t, scope) ?? (T.isNullish(t, scope) ? T.NEVER : t);
				}
				if (err && !T.isNumberLike(argT, scope))
					err(SEVERITY.ERROR, pos)`Operand of '${e.operator}' must be numeric, got '${show().type(argT)}' in '${show().expression(e)}'`;
				// The value is the operand's OLD one.
				if ((e.operator === '++' || e.operator === '--') && stepOperand(e.operand, argT, e.operator))
					return argT;
				return T.isAny(T.resolveOwn(argT, scope)) ? T.ANY : numericOf(argT, scope);
			}

			// `x = y` is a MUTATION, not a binary: `operator` absent is a plain `=`, present the compound form's BASE operator.
			case 'assign': {
				markAssignmentTargets(e.target);
				let lt = recurse(e.target);
				// What the slot held: its flow value (a target reads as its declared type, which a path's narrowing is not).
				const path		= T.pathKey(e.target);
				const before	= (path && scope.value(path)) || lt;
				// The target's DECLARED type, as written, contextually types the value (a bare `new C` has nothing else to go on): an assignment is never narrowed,
				// and resolved, `Promise<void>` would be a shape whose generic `then` inference reads. Nullish members are stripped below; the check uses all of `lt`.
				const target = e.target.type === 'identifier' ? scope.declarator(e.target.name)?.typeAnnotation ?? scope.declared(e.target.name) ?? lt : lt;
				const rt = recurse(e.value, e.target.type === 'array' || e.target.type === 'object' ? undefined : T.nonNullable(target, scope));
				const compound = e.operator && !LOGICAL_OPS.has(e.operator) ? arithmetic(e.operator, before, rt, scope) : undefined;
				// A compound assignment's value is what its slot then holds: a step's range for `+=`/`-=`, as `x = x + a`'s.
				let holds: Type | undefined;
				// Judged against the declaration-site type, not a narrowing: a dotted target goes through `lookupMember`. A destructuring target has no
				// pattern checker yet: `lt` is no real declared type there, as in `hoistVar` (widens to `any`, unchecked).

				if (e.target.type === 'member' || e.target.type === 'index') {
					// TBD: mark unpure if assigning to part of a parameter?

				}

				// Narrowing is flow, which every check needs (reporting, stamping, or a quiet loop-head walk); a query must not mutate its scope.
				if ((err || stamp || scope.isQuiet()) && (e.target.type === 'identifier' || e.target.type === 'member' || e.target.type === 'index')) {
					let expando = false;
					// An accessor pair's setter judges the value; a later read still goes through the getter (`getter`, where they differ).
					let written: Type | undefined, getter: Type | undefined;
					const accessor = (objT: Type, prop: string) => {
						const read = T.lookupMember(objT, prop, scope);
						written	= T.lookupMember(objT, prop, scope, undefined, undefined, true);
						getter	= written !== read ? read : undefined;
					};
					if (e.target.type === 'identifier') {
						// Never the flow's narrowing: a name with no declaration in view (a `for`'s `var`, not yet hoisted) is `any`.
						lt = scope.declared(e.target.name) ?? T.ANY;
					} else if (e.target.type === 'member') {
						const objT = recurse(e.target.object);
						// A property assigned to a function declaration, or a `const` holding a function expression, is DECLARED by it (TS's expando, `foo.meta = 1`).
						const holder = e.target.object.type === 'identifier' ? e.target.object.name : undefined;
						const init = holder !== undefined ? scope.alias(holder) : undefined;
						expando = holder !== undefined && (scope.decl(holder)?.type === 'function_decl' || init?.type === 'function' || init?.type === 'arrow');
						accessor(objT, e.target.property);
						lt = expando ? rt : T.optional(written || lt, T.memberOptional(objT, e.target.property, scope));
					} else if (e.target.type === 'index') {
						const objT = recurse(e.target.object);
						const k = recurse(e.target.index);
						if (k.type === 'literal' && (typeof k.value === 'string' || typeof k.value === 'number'))
							accessor(objT, String(k.value));
						lt = written ?? lt;
					}

					if (!e.operator) {
						if (err && !checkFlow(e.value, rt, lt, scope, pos, scope, err)) {
							err(SEVERITY.ERROR, pos)`Type '${show().type(rt)}' is not assignable to type '${show().type(lt)}' in '${show().expression(e.target)} = ...'`;
						} else {
							if (err)
								checkExcessProps(e.value, lt, pos, scope, err);
							// Later statements see the assigned type, not the declared one; a dotted target narrows as a bare name does. Not an expando, whose type is the
							// union of all its assignments.
							const key = T.pathKey(e.target);
							if (key && !expando)
								// Widened (`x = "a"` narrows `x` to `string`), except a numeric slot's range, which the flow keeps precise (`steppedRange`).
								assignFlow(scope, key, getter && !T.isAssignable(rt, getter, scope) ? getter : T.isAny(lt) && isEmptyArrayLiteral(e.value) ? AUTO_ARRAY
									: numericFlow(lt, () => e.value.type === 'binary' && (e.value.operator === '+' || e.value.operator === '-') && T.pathKey(e.value.left) === key
										? stampStep(e.value, steppedRange(before, e.value.operator, numericSlot(recurse(e.value.right), scope), scope)) : numericSlot(rt, scope), scope) ?? T.widenLiterals(rt), stamp);
						}
					} else if (e.operator !== '??' && e.operator !== '||' && e.operator !== '&&') {
						// A compound operator leaves the slot holding its result: a step's range for `+=`/`-=`, else the operator's.
						const key = T.pathKey(e.target);
						if (key && !expando) {
							const op = e.operator;
							holds = numericFlow(lt, () => {
								const old = numericSlot(before, scope), by = numericSlot(rt, scope);
								return op === '+' || op === '-' ? steppedRange(before, op, by, scope) : old && by && T.rangeBinOp(op, old, by);
							}, scope) ?? T.widenLiterals(compound!);
							assignFlow(scope, key, holds, stamp);
						}
					} else {
						const key = T.pathKey(e.target);
						if (key) {
							// `x ??= y` leaves `x` holding its non-nullish members or `y` (likewise `||=`/`&&=`).
							const other = T.isOther(e.operator[0]);
							forgetPathsThrough(scope, key);

							scope.addNarrowing(key, T.combineTypes([
								...T.unionMembers(lt, scope).filter(m => !other(T.resolveOwn(m, scope), scope)),
								T.widenLiterals(rt),
							]));
						}
					}
				}
				return holds ?? compound ?? (e.operator ? T.combineTypes([T.logicalLeftPart(before, e.operator, scope), rt]) : rt);
			}

			case 'binary': {
				const lt = recurse(e.left);

				if (LOGICAL_OPS.has(e.operator)) {
					// Precise throughout: a fresh literal decides `other`/`makeNullish` exactly (`5 && b` drops the falsy branch). `??`'s right is contextually typed
					// by the LEFT's non-nullish type, what the expression yields: `specs ?? []` is `Spec[]`, as tsc gives. `&&`/`||` yield either side.
					const rightExpected = e.operator === '??' ? T.nonNullable(lt, scope) : undefined;
					const rightScope	= e.operator === '&&' ? narrow(e.left, scope, true) : e.operator === '||' ? narrow(e.left, scope, false) : scope;
					stampBranch(e.right, rightScope, scope);
					const rt	= typeOf(e.right, rightScope, false, rightExpected, yieldCollector, err, stamp, overStamps);
					return T.combineTypes([T.logicalLeftPart(lt, e.operator, scope), rt]);
				}
				const rt = recurse(e.right);
				if (COMPARISON_OPS.has(e.operator))
					return T.BOOLEAN;
				const result = arithmetic(e.operator, lt, rt, scope);
				// A `+` that may concatenate takes any operand.
				if (err && !(e.operator === '+' && (result === T.STRING || result === T.ANY))) {
					if (!T.isNumberLike(lt, scope))
						err(SEVERITY.ERROR, pos)`Operand of '${e.operator}' must be numeric, got '${show().type(lt)}' in '${show().expression(e.left)}'`;
					if (!T.isNumberLike(rt, scope))
						err(SEVERITY.ERROR, pos)`Operand of '${e.operator}' must be numeric, got '${show().type(rt)}' in '${show().expression(e.right)}'`;
				}
				return result;
			}

			case 'conditional': {
				recurse(e.test);
				const thenScope = narrow(e.test, scope, true), elseScope = narrow(e.test, scope, false);
				stampBranch(e.consequent, thenScope, scope);
				stampBranch(e.alternate, elseScope, scope);
				// Precise per branch; the final wrap widens the result once.
				return T.combineTypes([
					typeOf(e.consequent, thenScope, false, expected, yieldCollector, err, stamp, overStamps),
					typeOf(e.alternate, elseScope, false, expected, yieldCollector, err, stamp, overStamps)
				]);
			}

			case 'sequence':
				return e.expressions.map(x => recurse(x)).pop() ?? T.ANY;

			case 'spread':
				return recurse(e.operand);

			// TS types a tagged template as the call `tag(strings, ...substitutions)`: overloads, inference and argument checks alike.
			case 'tagged_template': {
				const at = <N extends object>(n: N) => Object.defineProperty(n, 'pos', { value: pos, enumerable: false });
				const strings = at({ type: 'as', expression: at({ type: 'array', elements: [] }), typeAnnotation: TS.RefType('TemplateStringsArray') } as Expr);
				return recurse(at({ type: 'call', callee: e.tag, arguments: [strings, ...e.quasi.flatMap(p => p.exp ? [p.exp] : [])] } as Expr), expected);
			}
			case 'import_call': {
				// A specifier that is not a string literal is `Promise<any>`, as in TS.
				e.arguments.forEach(a => recurse(a));
				const spec = literalSpecifier(e);
				if (err && e.arguments.some(a => a.type === 'spread'))
					err(SEVERITY.ERROR, pos)`Argument of dynamic import cannot be spread element.`;
				else if (err && (e.arguments.length < 1 || e.arguments.length > 2))
					err(SEVERITY.ERROR, pos)`Dynamic imports can only accept a module specifier and an optional set of attributes as arguments`;
				else if (!e.module && err && scope.reportsUnknownNames() && spec !== undefined)
					err(SEVERITY.ERROR, pos)`Cannot find module '${spec}'`;
				return TS.RefType('Promise', [e.module ?? T.ANY]);
			}
			case 'import_meta':
				return TS.RefType('ImportMeta');
			case 'yield': {
				// A declared generator's Y is a plain `yield`'s context, and what is yielded must fit it.
				const fnKind	= scope.enclosingFunction();
				const async		= !!fnKind?.async;
				// `yield* x`'s `x` is a generator of Y and N, returning what the `yield*` is expected to evaluate to.
				const delegateContext = fnKind?.yield && TS.RefType(async ? 'AsyncGenerator' : 'Generator', [fnKind.yield, expected ?? T.UNKNOWN, fnKind.next ?? T.UNKNOWN]);
				const argT		= e.operand ? recurse(e.operand, e.delegate ? delegateContext : fnKind?.yield) : T.UNDEFINED;
				// `yield* x` yields what `x` iterates to and evaluates to what its iterator returns.
				const delegated	= e.delegate ? iterationOrReport(argT, scope, pos, err, async) : undefined;
				const yielded	= delegated ? delegated.yield : T.unwrapIfAsync(argT, scope, async);
				if (err && fnKind?.yield && !checkFlow(e.delegate ? undefined : e.operand, yielded, fnKind.yield, scope, pos, scope, err))
					err(SEVERITY.ERROR, pos)`Type '${show().type(yielded)}' is not assignable to the yielded type '${show().type(fnKind.yield)}'`;
				yieldCollector?.push(delegated ? yielded : T.widenLiterals(yielded));
				// `yield x` evaluates to what `next(v)` is given: the declared N, else `any` (as TS, which flags it under noImplicitAny).
				return delegated ? delegated.return : fnKind?.next ?? T.ANY;
			}

			case 'class':
				return checkClass(e as TS.Class, scope, err, stamp);

			case 'as': {
				const anno = e.typeAnnotation;
				// `T.freeze`: an assertion's result never widens, `as const` or a plain `as T`, even embedded in a later-widened container (`[1, x as const]`).
				if (isConstContext(anno))
					return T.freeze(recurse(e.expression, constContext(expected)));
				// The check pass types the operand so it carries a stamp (`(m as any).kind` reads `m`). Not against `anno`, which would drive a generic call's
				// inference from the assertion (`xs.flatMap(...) as C[]`).
				// A function or literal operand takes `anno` as its context, as in TS (`(s => ...) as get<R>`, `{ get: s => t } as TypeT<T>`): no inference rides on it.
				if (isContextSensitive(e.expression) || e.expression.type === 'object' || e.expression.type === 'array') {
					// Local aliases expanded as the result's are: a parameter typed from them must resolve outside the body too.
					recurse(e.expression, T.expandLocalQueries(anno, scope));
				} else if (stamp) {
					recurse(e.expression);
					// What the operand is BUILT as, though not typed against: `{ type: 'array', ... } as Expr` names the union member.
					stampContext(e.expression, anno, scope);
				}
				return T.freeze(T.expandLocalQueries(anno, scope));
			}
			case 'satisfies': {
				const anno = e.typeAnnotation;
				const t = recurse(e.expression, anno);
				if (err) {
					if (!checkAssignable(t, anno, scope, pos, scope, err))
						err(SEVERITY.ERROR, pos)`Type '${show().type(t)}' does not satisfy the expected type '${show().type(anno)}'`;
					else
						checkExcessProps(e.expression, anno, pos, scope, err);
				}
				return t;
			}
			default:
				return T.ANY;
		}
	}
}

// ---- functions / classes / statements -------------------------------------------------------

// `contextualReturn`: what the CALL SITE wants returned where the function declares no return type, an inference hint that shapes the body's
// types and never yields a diagnostic; `expected`, the DECLARED return type, is checked.
function checkFunctionBody(fn: TS.CallSig, body: JS.Stmt<any>[] | Expr | undefined, scope: Scope, async: boolean, skipReturn?: boolean, generator?: boolean, err?: Err, contextualReturn?: Type, stampTypes = false) {
	if (!body)
		return;

	// A declared return type is never replaced by inference, even one (`any`, a generator's) that checks nothing.
	const declaredReturn = fn.returnType;
	// A declared generator's body is checked against what it iterates: `return x` against its TReturn, `yield`s against Y and N.
	const generatorTypes = generator && declaredReturn ? T.iterationTypes(declaredReturn, scope, async, undefined, true) : undefined;
	let expected = generator ? generatorTypes?.return : declaredReturn;
	if (expected && async && !generator) {
		const p = T.asPromiseRef(expected, scope);
		expected = p ? p.typeArgs![0] : expected;
	}
	// A declared type predicate (`x is T`) is neither checked against the body's boolean return nor inferred over.
	const predicate = expected?.type === 'predicate' ? expected : undefined, isPredicate = !!predicate;
	// A type predicate returns a `boolean` (an `asserts` one, nothing): its returns are checked, and typed, against that.
	if ((skipReturn && !generator) || (expected && T.isAny(expected)) || predicate?.asserts)
		expected = undefined;
	else if (predicate)
		expected = T.BOOLEAN;
	// What a returned value is typed against: in an async function, the value or a promise of it.
	const returnContext = expected && async ? T.awaitContext(expected) : expected;

	// A muted re-walk of a function with a declared return type is skipped once its BODY carries a stamp: `narrow`'s speculative re-walks reach a node
	// only after the real pass. A lib method's one muted check still walks it, so its callbacks get contextual params.
	if (expected && !err && fn.scope && (!Array.isArray(body) || !body.length || (body[0] as any).scope || scope.isGenericTemplate()))
		return;

	// A function expression's parameter annotations name the scope it is written in, stamped before the body runs: a parameter's type flows from
	// there into callees' instantiations, whose own stamps would claim it. Not a class member's, which each instance's scope must resolve, nor in a
	// generic class's template or a speculative walk, which never stamp (`noStamp`).
	if ('type' in fn && (fn.type === 'arrow' || fn.type === 'function') && !trying && !scope.isGenericTemplate()) {
		const ownTypeParams = fn.typeParams?.length ? new Set(fn.typeParams.map(p => p.name)) : undefined;
		for (const p of [...fn.params, ...fn.rest ? [fn.rest] : []])
			if (p.typeAnnotation)
				T.stampScope(p.typeAnnotation, scope, ownTypeParams);
	}
	const inner = new Scope(scope);
	inner.functionKind = { async, yield: generatorTypes?.yield, next: generatorTypes?.next };
	// Every non-arrow function has its own `arguments`; an arrow reads its enclosing one's.
	if (!('type' in fn && fn.type === 'arrow'))
		inner.addValue('arguments', TS.RefType('IArguments'));
	// Only where nothing is declared: a declared return type is the better answer, and `expected` keeps driving the diagnostics.
	const inferHint = expected || !contextualReturn ? undefined : async && !generator ? promisedContext(contextualReturn, scope) : contextualReturn;
	// A speculative walk, or a generic class's method template shared by every instantiation, must not stamp: `??=` would freeze an
	// answer the real walk or the instance needs. Consumers fall back to an instantiation-correct scope when unset.
	const noStamp = trying > 0 || (!!expected && !err && scope.isGenericTemplate());
	if (!noStamp)
		fn.scope ??= inner;

	// `??=`: the first real check wins; a speculative re-walk reaches a statement only after the real pass has.
	const stamp: (s: Stmt, scope: Scope) => void = noStamp ? _ => {} : (s, scope) => {(s as any).scope ??= stampedScope(s, scope);};

	// Each type param is registered in the body's scope (`addTypeParam`), at its constraint (`any` unconstrained): an unregistered name stays opaque
	// to every reference in the body.
	for (const p of fn.typeParams ?? [])
		inner.addTypeParam(p.name, p.constraint ?? T.UNKNOWN);
	if (fn.thisType)
		inner.addValue('this', fn.thisType);

	for (const p of fn.params) {
		const anno = p.typeAnnotation;
		// Typed against `anno`, as TS checks a default against the declared parameter type, so an unannotated arrow default gets typed params.
		// Checked precise; an unannotated parameter's own type is the widened one, as TS infers it.
		const precise	= p.default && typeOf(p.default, inner, false, anno, undefined, err, stampTypes);
		const dt		= precise && T.widenLiterals(precise);
		if (err && precise && anno && !checkFlow(p.default, precise, anno, inner, (p as any).pos, inner, err))
			err(SEVERITY.ERROR, (p as any).pos)`Default value of type '${show().type(precise)}' is not assignable to parameter type '${show().type(anno)}'`;
		// Written back, as `applyContextualParams` does, since the function's type (`FixParams`) has no scope to type a non-literal default in. What the
		// PATTERN implies outranks its default, as in `FixParams` (`{ a = 0 } = {}` binds `a`, which `{}` lacks).
		const implied	= !anno && typeof p.key !== 'string' && T.patternDefaults(p.key) ? T.patternType(p.key) : undefined;
		const declared	= implied ?? dt;
		// An IMPLIED type is never written back: `FixParams` derives it again, and an unannotated parameter is what makes an IIFE's optional.
		if (!anno && !implied && dt) {
			written(p, 'typeAnnotation');
			p.typeAnnotation = typeof p.key === 'string' ? T.widenNullish(dt, inner) : dt;
		}
		if (typeof p.key === 'string') {
			inner.addValue(p.key, anno ? T.optional(anno, hasMod(p, 'optional') && !p.default) : dt ? T.widenNullish(dt, inner) : T.ANY);
			inner.addDeclarator(p.key, p);
		} else {
			// The whole argument, under a name no source can spell, is the pattern's source -- so a destructured
			// discriminated union correlates as a `const` one does, unless the body reassigns one of its names.
			const hidden = `#param${fn.params.indexOf(p)}`;
			inner.addValue(hidden, anno ?? declared ?? T.ANY);
			bindPattern(inner, p.key, anno ?? declared ?? T.ANY, { type: 'identifier', name: hidden } as Expr, !writesAny(body, new Set(T.bindingNames(p.key))));
		}
	}
	
	if (fn.rest) {
		if (typeof fn.rest.key === 'string')
			inner.addValue(fn.rest.key, fn.rest.typeAnnotation ?? T.ANY);
		else
			bindPattern(inner, fn.rest.key, fn.rest.typeAnnotation ?? T.ANY);
	}

	// TS 5.5 inferred type predicates: a function whose single return is a type guard (`x => x != null`) gets `x is T`, from what `narrow()` makes of it.
	function inferredPredicate(test: Expr|undefined, result: Type): Type {
		if (test && T.isBoolean(result) && typeof fn.params[0]?.key === 'string') {
			const key		= fn.params[0].key;
			const paramT	= fn.params[0].typeAnnotation ?? T.ANY;
			const inner		= new Scope(scope);
			inner.addValue(key, paramT);
			const narrowed	= narrow(test, inner, true).value(key);
			// Only when the function is false exactly when `x` is no `T`: the false branch must narrow the parameter to its declared type less `T`.
			const keys		= (t: Type) => new Set(T.unionMembers(t, inner).map(m => T.typeKey(m)));
			const falseT	= keys(narrow(test, inner, false).value(key) ?? paramT);
			const restT		= narrowed && keys(TS.UnionType(T.unionMembers(paramT, inner).filter(m => !T.isAssignable(m, narrowed, inner, inner, false, 10, true))));
			if (narrowed && narrowed !== paramT && restT && falseT.size === restT.size && [...restT].every(k => falseT.has(k)))
				return TS.Predicate(key, narrowed);
		}
		return result;
	}


	if (Array.isArray(body)) {
		if (expected) {
			checkBlock(body, inner, typeOf1(err, stampTypes), (s, scope, typeOf1, checkStmt1) => {
				const quiet = scope.isQuiet();
				if (!quiet)
					stamp(s, scope);
				const out = checkStmt(s, scope, typeOf1, checkStmt1, err);
				if (s.type === 'return' && s.argument) {
					const argument = s.argument;
					const t = typeOf(argument, scope, false, returnContext, undefined, quiet ? undefined : err, stampTypes && !quiet);
					if (err && !quiet) {
						if (!checkFlow(argument, T.unwrapIfAsync(t, scope, async), expected, scope, (argument as any).pos, scope, err))
							err(SEVERITY.ERROR, (argument as any).pos)`Type '${show().type(t)}' is not assignable to declared return type '${show().type(expected)}'`;
						else
							checkExcessProps(argument, expected, (argument as any).pos, scope, err);
					}
				}
				return out;
			});

		} else if (isPredicate) {
			checkBlock(body, inner, typeOf1(err, stampTypes), (s, scope, typeOf1, checkStmt1) => {
				if (!scope.isQuiet())
					stamp(s, scope);
				return checkStmt(s, scope, typeOf1, checkStmt1, err);
			});
			

		} else {
			// Keyed by statement: a loop's quiet head walks type a `return` too (inference is typing), and the last walk is the real one.
			const	returns		= new Map<Stmt, Type | undefined>();
			const	yields		= generator ? [] as Type[] : undefined;
			const	fallsOut	= checkBlock(body, inner,
				(e: Expr, scope: Scope, expected?: Type, widen = true) => {
					const quiet = scope.isQuiet();
					return typeOf(e, scope, widen, expected, yields, quiet ? undefined : err, stampTypes && !quiet);
				},
				(s, scope, typeOf1, checkStmt1) => {
					const quiet = scope.isQuiet();
					if (!quiet)
						stamp(s, scope);
					const out = checkStmt(s, scope, typeOf1, checkStmt1, err);
					if (s.type === 'return')
						returns.set(s, s.argument && widenForContext(typeOf(s.argument, scope, false, inferHint, undefined, quiet ? undefined : err, stampTypes && !quiet), inferHint, scope));
					return out;
				}
			);

			const retDef		= [...returns.values()].filter(r => !!r);

			if (retDef.length && (retDef.length < returns.size || fallsOut)) {
				retDef.push(T.UNDEFINED);
			}
			const returnType = retDef.length ? T.widenNullish(T.combineTypes(equivalentsOnce(retDef, inner)), inner) : alwaysThrows(body[body.length - 1]) ? T.NEVER : T.VOID;

			if (!declaredReturn) {
				written(fn, 'inferredReturn');
				written(fn, 'returnType');
				fn.inferredReturn = true;
				fn.returnType = generator
					? TS.RefType(async ? 'AsyncGenerator' : 'Generator', [yields!.length ? T.combineTypes(yields!) : T.NEVER, returnType, T.ANY])
					: T.wrapReturnIfAsync(inferredPredicate(body.length === 1 && body[0].type === 'return' ? body[0].argument : undefined, returnType), inner, async);
			}
		}
	} else {
		// Precise: `expected` may be a narrow declared return type, so the check sees the body's exact type; only inference widens.
		// Stamped like a block body's statements, so codegen's closure sees what this saw.
		if (!noStamp && !narrowing)
			(body as any).scope ??= inner;
		const t = typeOf(body, inner, false, returnContext ?? inferHint, undefined, err, stampTypes);
		if (expected) {
			if (err && !checkFlow(body as Expr, T.unwrapIfAsync(t, inner, async), expected, inner, (body as any).pos, inner, err))
				err(SEVERITY.ERROR, (body as any).pos)`Type '${show().type(t)}' is not assignable to declared return type '${show().type(expected)}'`;
		} else if (!isPredicate && !declaredReturn) {
			written(fn, 'inferredReturn');
			written(fn, 'returnType');
			fn.inferredReturn = true;
			fn.returnType = T.wrapReturnIfAsync(inferredPredicate(body, T.widenNullish(widenForContext(t, inferHint, inner), inner)), inner, async);
		}
	}
}
function checkClass(c: TS.Class, scope: Scope, err?: Err, stamp = false) {
	// A named class EXPRESSION binds its name only within itself, as its type and its value, which its constructor's result names.
	if (!isClassDecl(c) && c.name)
		scope = new Scope(scope);
	const { instance, value, superType } = classShapes(c, scope);
	if (!isClassDecl(c) && c.name) {
		scope.mergeType(c.name, instance, c.typeParams as TS.TypeParam[]);
		scope.mergeValue(c.name, value);
	}
	const scopes = classBodyScopes(c, scope, instance, value, superType);
	for (const m of c.body)
		checkMember(m, scopes, err, stamp);
	return value;
}

// A generic method's instance (its own type parameters substituted, its body a fresh unstamped copy): checked and stamped as its
// class checks the template, in the class's body scope.
export function checkMethodInstance(c: TS.Class, m: TS.ClassMember, scope: Scope): void {
	const { instance, value, superType } = classShapes(c, scope);
	checkMember(m, classBodyScopes(c, scope, instance, value, superType), MUTED, true);
}

function checkMember(m: TS.ClassMember, { inst: instScope, stat: statScope }: { inst: Scope; stat: Scope }, err?: Err, stamp = false) {
	switch (m.type) {
		case 'field':
			if (m.value) {
				const inner = hasMod(m, 'static') ? statScope : instScope;
				const t		= typeOf(m.value, inner, false, m.typeAnnotation, undefined, err, stamp);
				if (m.typeAnnotation && err) {
					if (!checkFlow(m.value, t, m.typeAnnotation, inner, (m as any).pos, inner, err))
						err(SEVERITY.ERROR, (m as any).pos)`Type '${show().type(t)}' is not assignable to type '${show().type(m.typeAnnotation)}'`;
					else
						checkExcessProps(m.value, m.typeAnnotation, (m as any).pos, inner, err);
				}
			}
			break;
		case 'method':
			checkFunctionBody(m, m.body, hasMod(m, 'static') ? statScope : instScope, hasMod(m, 'async'), m.key === 'constructor' || hasMod(m, 'generator'), hasMod(m, 'generator'), err, undefined, stamp);
			break;
		case 'get':
			checkFunctionBody(m, m.body, hasMod(m, 'static') ? statScope : instScope, false, false, false, err, undefined, stamp);
			break;
		case 'set':
			checkFunctionBody(m, m.body, hasMod(m, 'static') ? statScope : instScope, false, true, false, err, undefined, stamp);
			break;
		case 'static_block':
			checkBlock(m.body, new Scope(statScope), typeOf1(err), checkStmt1(err));
	}
}

// The ordinary walk: stamp the scope, then check. A caller wanting more (a return hook) or no stamping writes its own and calls `checkStmt`;
// the wrapper re-supplies `err` on every entry, so `err` is no part of `checkStmt`'s own type.
export const checkStmt1 = (err?: Err): checkStmt => (s, scope, typeOf, self) => {
	if (!scope.isQuiet() && !trying)
		(s as any).scope ??= stampedScope(s, scope);
	return checkStmt(s, scope, typeOf, self, err);
};

// A muted, stamping check of statements already HOISTED into `scope`: a generic instance's re-check, which must leave its
// template methods unstamped (`noStamp`) as an entry file's instances are.
export function checkHoisted(stmts: Stmt[], scope: Scope, err?: Err) {
	const check = checkStmt1(err);
	for (const s of stmts)
		check(s, scope, typeOf1(err), check);
}
// An imported module, which `exportScope` only hoists, is checked as an entry file is with its reports discarded: unlike a QUERY (no `err`),
// such a check still narrows and stamps what codegen reads (flows, assignment narrowings).
export const MUTED: Err = () => () => {};
export const checkImported = (stmts: Stmt[], scope: Scope) => checkHoisted(stmts, scope, MUTED);

// What a lowering builds out of checked code (`transform.ts`): its NEW statements and expressions checked and stamped into `scope`
// (the caller's child of the original's), each over its parts' stamps. A statement already checked (stamped: user code) is not walked again.
export function checkSynthesized(stmts: Stmt[], scope: Scope): void {
	const type = (e: Expr, scope: Scope) => typeOf(e, scope, true, undefined, undefined, MUTED, true, true);
	for (const s of stmts.filter(s => !(s as { scope?: Scope }).scope)) {
		(s as { scope?: Scope }).scope = scope;
		switch (s.type) {
			case 'var_decl':
				for (const d of s.declarations) {
					bindPattern(scope, d.name, d.typeAnnotation ?? (d.init ? type(d.init, scope) : T.ANY), d.init, s.kind === 'const', MUTED);
					if (typeof d.name === 'string')
						scope.addDeclarator(d.name, d);
				}
				break;
			case 'expression':
				type(s.expression, scope);
				break;
			case 'block':
				checkSynthesized(s.body, new T.Scope(scope));
				break;
			case 'for': {
				const loop = new T.Scope(scope);
				if (s.kind !== 'normal') {
					// `for (const k of xs)` / `in`: the declared name takes the element (a key), as `checkLoop`'s head does.
					const elemT = s.kind === 'in' ? (type(s.right, loop), T.STRING) : T.iterationTypes(type(s.right, loop), loop, s.kind === 'of await')?.yield ?? T.ANY;
					if (s.init.type !== 'var_decl')
						throw `internal: a synthesized 'for...${s.kind}' needs a declared loop variable`;
					for (const d of s.init.declarations)
						bindPattern(loop, d.name, elemT, undefined, s.init.kind === 'const', MUTED);
					(s.init as { scope?: Scope }).scope = loop;
					checkSynthesized([s.body], new T.Scope(loop));
					break;
				}
				if (s.init)
					checkSynthesized([s.init.type === 'var_decl' ? s.init : JS.ExprStmt(s.init)], loop);
				[s.test, s.update].forEach(e => e && type(e, loop));
				checkSynthesized([s.body], new T.Scope(loop));
				break;
			}
			default:
				throw `internal: a synthesized '${s.type}' is not checked`;
		}
	}
}

// A lowered expression (`lowerExpr`), checked and stamped over its parts' stamps.
export const checkSynthesizedExpr = (e: Expr, scope: Scope) => typeOf(e, scope, true, undefined, undefined, MUTED, true, true);

// An index read is possibly absent exactly when the program TESTS it (TS types `a[i]` as `T`; JS reads `undefined` past the end): a marked read is
// `T | undefined`, a BOUNDED read. A tested name is matched to its BINDING: its own closure's declarations, else its nearest enclosing closure's.
export function markAbsenceTests(stmts: Stmt[]): void {
	type Reads = (name: string) => TS.Expr[] | undefined;
	const scan = (body: Stmt[] | Expr, outer: Reads, params: string[]) => {
		// A closure's blocks are not told apart: a tested name marks each same-named read in it, at the cost of a needless bounds check.
		const own		= new Map<string, TS.Expr[]>(params.map(p => [p, []]));
		const reads: Reads = n => own.get(n) ?? outer(n);
		const tested	= new Set<string>();
		// Scanned once this closure's own declarations are all known, as a nested function sees every one of them.
		const nested: Closure[] = [];
		const declare	= (target: JS.BindingTarget, read?: TS.Expr) => T.bindingNames(target).forEach(n => own.set(n, [...own.get(n) ?? [], ...read ? [read] : []]));
		const w = walkerB(
			(st, process) => {
				if (st.type === 'function_decl')
					return (nested.push(st), false);
				if (st.type === 'var_decl')
					st.declarations.forEach(d => declare(d.name, typeof d.name === 'string' && d.init?.type === 'index' ? d.init : undefined));
				if (st.type === 'try')
					st.handlers.forEach(h => h.param && declare(h.param));
				return process(st);
			},
			(e, process) => {
				if (e.type === 'arrow' || e.type === 'function')
					return (nested.push(e), false);
				if (e.type === 'object') {
					e.properties.forEach(p => p.type === 'spread' ? w.expression(p.operand)
						: p.type === 'field' ? (typeof p.key === 'object' && w.expression(p.key.computed), p.value && w.expression(p.value))
						: nested.push(p));
					return false;
				}
				if (e.type === 'binary' && (e.operator === '===' || e.operator === '!==' || e.operator === '==' || e.operator === '!=')) {
					for (const [a, b] of [[e.left, e.right], [e.right, e.left]] as const) {
						if (T.isNullLiteral(b)) {
							if (a.type === 'index')
								(a as { testedForAbsence?: boolean }).testedForAbsence = true;
							else if (a.type === 'identifier')
								tested.add(a.name);
						}
					}
				}
				return process(e);
			},
			undefined,
			// A class member's code is a closure of its own: a method's parameters, a field's or static block's own locals.
			m => {
				if (m.type === 'method' || m.type === 'get' || m.type === 'set')
					nested.push(m);
				else if (m.type === 'field' && m.value)
					nested.push({ params: [], body: m.value });
				else if (m.type === 'static_block')
					nested.push({ params: [], body: m.body });
				return false;
			}
		);
		w.body(body);
		nested.forEach(fn => fn.body && scan(fn.body, reads, paramNames(fn.params, fn.rest)));
		for (const name of tested)
			reads(name)?.forEach(read => (read as { testedForAbsence?: boolean }).testedForAbsence = true);
	};
	scan(stmts, () => undefined, []);
}

// TS2304 for a type: a ref naming nothing in the scope it was written in. Collected BEFORE checking, which writes contextual
// types onto the AST; judged after, once every scope is complete. Names a type binds itself are in no scope.
export function unknownTypeNames(stmts: Stmt[]): (err: Err) => void {
	const refs: { ref: TS.RefType; at: Location }[] = [];
	let bound	= new Set<string>();
	let at:		Location | undefined;
	const binding = <N extends object>(x: N, names: string[], process: (x: N) => boolean) => {
		const outer = bound, outerAt = at;
		bound	= names.length ? new Set([...bound, ...names]) : bound;
		at		= getPos(x) ?? at;
		const r	= process(x);
		bound	= outer;
		at		= outerAt;
		return r;
	};
	const typeParams = (x: object) => (x as { typeParams?: TS.TypeParam[] }).typeParams?.map(p => p.name) ?? [];
	walkerB(
		(st, process) => binding(st, typeParams(st), process),
		(e, process) => binding(e, typeParams(e), process),
		(t, process) => {
			if (t.type === 'ref' && !bound.has(t.name.split('.')[0]))
				refs.push({ ref: t, at: getPos(t) ?? at! });
			return binding(t, [...typeParams(t), ...t.type === 'mapped' ? [t.keyName] : t.type === 'conditional' ? T.inferNames(t.extendsType) : []], process);
		},
		(m, process) => binding(m, typeParams(m), process),
	).statements(stmts);
	// A ref the checker never stamped (unreachable, or never read) has no scope to ask.
	return err => {
		for (const { ref, at } of refs)
			if (ref.declScope instanceof T.Scope && !ref.declScope.lookupType(ref.name))
				err(SEVERITY.ERROR, at)`Cannot find name '${ref.name}'`;
	};
}

// A dynamic import's specifier when it is a string literal: the only form resolved before checking.
export function literalSpecifier(e: JS.ImportCall): string | undefined {
	const s = e.arguments[0];
	return s?.type === 'literal' && typeof s.value === 'string' ? s.value : undefined;
}

// A body: its scope is where its `var`s bind.
export function checkBlock(stmts: Stmt[], scope: Scope, typeOf = typeOf1(MUTED), checkStmt: checkStmt = checkStmt1(MUTED)): Scope | undefined {
	scope.varBoundary = true;
	return checkNestedBlock(stmts, scope, typeOf, checkStmt);
}

// A block statement's body: a `var` in it binds further out.
function checkNestedBlock(stmts: Stmt[], scope: Scope, typeOf: typeOf, checkStmt: checkStmt): Scope | undefined {
	hoist(stmts, scope);
	return checkStatements(stmts, scope, typeOf, checkStmt);
}

// The sequential walk of statements already hoisted into `scope`: the flow out of the last, `undefined` where control never gets
// there. Unreachable statements are still checked, in the last flow that reached anything.
function checkStatements(stmts: Stmt[], scope: Scope, typeOf: typeOf, checkStmt: checkStmt): Scope | undefined {
	let flow = scope, reached = true;
	for (const s of stmts) {
		const out = checkStmt(s, flow, typeOf, checkStmt);
		reached &&= !!out;
		flow = out ?? flow;
	}
	return reached ? flow : undefined;
}

type checkStmt = (s: Stmt, scope: Scope, typeOf: typeOf, checkStmt: checkStmt)=>Scope | undefined;

// The flow after `stmt`: the scope its successor sees, `undefined` where control never falls out of it.
export function checkStmt(stmt: Stmt, scope: Scope, typeOf: typeOf, checkStmt: checkStmt, err?: Err): Scope | undefined {
	const quiet = scope.isQuiet();
	if (quiet)
		err = undefined;

	switch (stmt.type) {
		case 'var_decl': {
			// `hoistVar` registers the name even in a muted pass; only the diagnostics are skipped. An ambient declaration is skipped here: `hoist` registered
			// it in order, and re-registering at this position would clobber a later same-named real class (`declare var String` beside `class String`).
			const pos	= (stmt as any).pos;
			const home	= stmt.kind === 'var' ? scope.varScope() : scope;
			for (const d of stmt.declarations) {
				// Like a signature's: a module-private type named by a local (`let c: CacheFile`) must resolve where it was written.
				if (d.typeAnnotation)
					T.stampScope(d.typeAnnotation, scope);
				// A block-scoped name is bound for its whole block, so a closure in its own initializer (`const f = (n): R => f(n - 1)`) reaches it: as its
				// annotation, else a function expression's signature, else `any`, as TS types it there. A `var` already declared keeps that binding.
				if (typeof d.name === 'string' && d.init && !stmt.ambient && !(stmt.kind === 'var' && home.ownValue(d.name)))
					home.addValue(d.name, d.typeAnnotation ? T.resolve(scope, d.typeAnnotation)
						: d.init.type === 'function' || d.init.type === 'arrow' ? { type: 'function', ...T.FixSig(d.init, T.ANY), origin: d.init } : T.ANY);
				if (d.typeAnnotation && d.init) {
					const anno = d.typeAnnotation;
					// Walked even muted: a callback in the initializer takes its contextual params from this walk (an imported module is only ever checked muted).
					// Widened until `let` assignment narrowing exists: a precise `let` union read later is only its declared type.
					const init = typeOf(d.init, scope, anno);
					if (err) {
						if (!init)
							checkExcessProps(d.init, anno, pos, scope, err);
						else if (!checkFlow(d.init, init, anno, scope, pos, scope, err))
							err(SEVERITY.ERROR, pos)`Type '${show().type(init)}' is not assignable to type '${show().type(anno)}' in declaration of '${show().bindingTarget(d.name)}'`;
					}
				}
				if (!stmt.ambient)
					hoistVar(scope, d, stmt.kind !== 'const', undefined, err, !quiet, home);
			}
			break;
		}
		case 'expression':
			typeOf(stmt.expression, scope);
			return scope;

		case 'block':
			return joinFlow(scope, [checkNestedBlock(stmt.body, new Scope(scope), typeOf, checkStmt)]);

		case 'if': {
			typeOf(stmt.test, scope);
			const then = checkStmt(stmt.consequent, new Scope(narrow(stmt.test, scope, true)), typeOf, checkStmt);
			const other = stmt.alternate ? checkStmt(stmt.alternate, new Scope(narrow(stmt.test, scope, false)), typeOf, checkStmt) : narrow(stmt.test, scope, false);
			return joinFlow(scope, [then, other]);
		}

		case 'while':
		case 'do_while':
		case 'for':
			return checkLoop(stmt, scope, [], typeOf, checkStmt, err);

		case 'switch': {
			typeOf(stmt.discriminant, scope);
			// A `case` with no body falls through: each clause narrows as `if` does, by its test (OR-ed with fallthrough tests); `default` by the negation
			// of every test.
			const caseTest	= (test: Expr): Expr => ({ type: 'binary', operator: '===', left: stmt.discriminant, right: test });
			const any		= (tests: Expr[]) => tests.reduce<Expr | undefined>((acc, t) => acc ? { type: 'binary', operator: '||', left: acc, right: t } : t, undefined);
			const none		= noCaseMatched(stmt);
			const earlier: Expr[] = [];		// every earlier clause's test, negated
			const inner		= new Scope(scope);
			const target: T.FlowTarget = inner.flowTarget = { labels: [], loop: false, breaks: [], continues: [] };
			let pending: Expr[] = [];
			let fall: Scope | undefined;	// the previous clause's flow, falling through into this one
			for (const c of stmt.cases) {
				if (c.test) {
					typeOf(c.test, scope);
					// A clause is entered when its value matches and no EARLIER clause's did: a repeated `case 'number':` is unreachable.
					pending.push(earlier.reduce<Expr>((acc, t) => ({ type: 'binary', operator: '&&', left: acc, right: t }), caseTest(c.test)));
					earlier.push({ type: 'unary', operator: '!', operand: caseTest(c.test) });
				} else if (none) {
					pending.push(none);
				}
				if (c.consequent.length) {
					const test = any(pending);
					fall = checkNestedBlock(c.consequent, new Scope(joinFlow(inner, [test ? narrow(test, inner, true) : inner, fall])!), typeOf, checkStmt);
					pending = [];
				}
			}
			// Trailing empty clauses match and do nothing; with no `default`, no clause matching at all leaves too.
			const unmatched	= stmt.cases.some(c => !c.test) ? undefined : none ? narrow(none, scope, true) : scope;
			const trailing	= any(pending);
			return joinFlow(scope, [fall, ...target.breaks, unmatched, trailing && narrow(trailing, scope, true)]);
		}
		case 'throw':
			typeOf(stmt.argument, scope);
			return undefined;

		case 'with':
			typeOf(stmt.argument, scope);
			return checkStmt(stmt.body, scope, typeOf, checkStmt);

		case 'return':
			return undefined;

		case 'break':
		case 'continue': {
			const target = scope.findTarget(stmt.label, stmt.type === 'continue');
			target?.[stmt.type === 'break' ? 'breaks' : 'continues'].push(scope);
			return undefined;
		}

		case 'try': {
			const body = checkNestedBlock(stmt.body, new Scope(scope), typeOf, checkStmt);
			// Any statement of the body may throw, so a handler starts from the entry with whatever the body assigns reset.
			const handlers = stmt.handlers.map(h => {
				const inner = havoc(scope, assignedNames(stmt.body));
				if (h.param) {
					if (typeof h.param === 'string')
						inner.addValue(h.param, T.ANY);
					else
						T.bindingNames(h.param).forEach(n => inner.addValue(n, T.ANY));
				}
				return checkNestedBlock(h.body, inner, typeOf, checkStmt);
			});
			const normal = joinFlow(scope, [body, ...handlers]);
			if (!stmt.finalizer)
				return normal;
			// The finalizer runs after any of those, completed or not; its own assignments then hold.
			const done = checkNestedBlock(stmt.finalizer, havoc(scope, assignedNames([...stmt.body, ...stmt.handlers.flatMap(h => h.body)])), typeOf, checkStmt);
			return done && normal && havoc(normal, assignedNames(stmt.finalizer));
		}

		case 'labeled': {
			const labels = [stmt.label];
			let body = stmt.body;
			for (; body.type === 'labeled'; body = body.body)
				labels.push(body.label);
			if (body.type === 'while' || body.type === 'do_while' || body.type === 'for')
				return checkLoop(body, scope, labels, typeOf, checkStmt, err);
			const inner = new Scope(scope);
			const target: T.FlowTarget = inner.flowTarget = { labels, loop: false, breaks: [], continues: [] };
			return joinFlow(scope, [checkStmt(body, inner, typeOf, checkStmt), ...target.breaks]);
		}

		case 'function_decl':
			if (stmt.body) {
				checkFunctionBody(stmt, stmt.body, ownThis(flowContainer(scope)), hasMod(stmt, 'async'), hasMod(stmt, 'generator'), hasMod(stmt, 'generator'), err, undefined, !quiet);
				// The hoisted signature typed only literal defaults: the body's check wrote back the rest (`c = m.constraint`).
				const hoisted = scope.value(stmt.name);
				if (hoisted?.type === 'function' && hoisted.origin === stmt)
					refreshParams(hoisted, stmt);
			}
			return scope;

		case 'class_decl':
			checkClass(stmt, scope, err, !quiet);
			return scope;

		case 'export_decl':
			return checkStmt(stmt.declaration, scope, typeOf, checkStmt);

		case 'export':
			if (stmt.default) {
				if (isTsDeclaration(stmt.default))
					checkStmt(stmt.default, scope, typeOf, checkStmt);
				else
					typeOf(stmt.default, scope);
			}
			return scope;

		// In the namespace's MERGED scope, where every same-named block hoisted: a fresh scope would shadow augmentations from other lib files.
		case 'namespace_decl': {
			const body = new Scope(namespaceInner.get(scope.namespace(stmt.name)!)!);
			body.varBoundary = true;
			checkStatements(stmt.body, body, typeOf, checkStmt);
			return scope;
		}

		// type_alias_decl / interface_decl / enum_decl / import / empty / debugger: declaration-only or nothing to check (hoist saw them)
	}
	return scope;
}

// Where control merges back into `base` from each of `outs` (its descendants; `undefined` where control does not arrive): every
// outer name any of them narrowed holds what any of them may hold. `undefined` when none arrives.
function joinFlow(base: Scope, outs: (Scope | undefined)[]): Scope | undefined {
	const live = outs.filter(o => !!o);
	if (!live.length)
		return undefined;
	const names = new Set(live.flatMap(o => o === base ? [] : [...o.outerNarrowings(base)]));
	if (!names.size)
		return base;
	const joined = new Scope(base);
	for (const name of names) {
		const ts = live.map(o => o.value(name));
		if (ts.every(t => !!t))
			joined.addNarrowing(name, joinTypes(base.declared(name), ts, base));
		else if (/[.[]/.test(name))
			joined.forget(name);
	}
	return joined;
}

// Values meeting at a merge. A numeric slot's ranges merge into one range: a union of literals would grow with every iteration.
function joinTypes(declared: Type | undefined, ts: Type[], scope: Scope): Type {
	const slot	= declared && numericSlot(declared, scope);
	const rs	= slot ? ts.map(t => numericSlot(t, scope)) : [];
	return slot && rs.every(r => r?.base === slot.base) ? T.rangeToType(rs.reduce((a, b) => a && b && T.rangeUnion(a, b))!) : T.combineTypes(ts);
}

// `next` with each numeric range still moving since `prev` widened to the next machine limit (`rangeWiden`), so a head settles.
function widenFlow(base: Scope, prev: Scope, next: Scope): Scope {
	const out = new Scope(base);
	for (const n of next.outerNarrowings(base)) {
		const a = T.toRange(prev.value(n)), b = T.toRange(next.value(n)), v = next.value(n);
		if (!v)
			out.forget(n);
		else
			out.addNarrowing(n, a && b && a.base === b.base ? T.rangeToType(T.rangeWiden(a, b)) : v);
	}
	return out;
}

// Whether two flows descended from `base` hold the same type for every name either narrowed.
function sameFlow(base: Scope, a: Scope, b: Scope): boolean {
	const names = new Set([...a.outerNarrowings(base), ...b.outerNarrowings(base)]);
	return [...names].every(n => {
		const x = a.value(n), y = b.value(n);
		return x === y || (!!x && !!y && T.typeId(x) === T.typeId(y));
	});
}

// `base` with each of `names` reset to its declared type: where they may hold any value an assignment gave them.
function havoc(base: Scope, names: Set<string>): Scope {
	const s = new Scope(base);
	for (const n of names) {
		const t = base.declared(n);
		if (t)
			s.addNarrowing(n, t);
		forgetPathsThrough(s, n);
	}
	return s;
}

// An assignment to `key` invalidates every narrowed path through it: `o.a` when `o` is assigned, `xs[i]` when `i` is.
function forgetPathsThrough(scope: Scope, key: string) {
	for (const k of scope.narrowedNames())
		if (k.startsWith(key + '.') || k.startsWith(key + '[') || k.includes(`[${key}]`))
			scope.forget(k);
}

// Every name `stmts` assign: `=`, a compound assignment, `++`/`--`, a destructuring target, a `for-in/of` target. Not a closure's.
function assignedNames(stmts: Stmt[]): Set<string> {
	const names = new Set<string>();
	const targets = (e: Expr) => walkerB(undefined, (x, process) => x.type === 'identifier' ? (names.add(x.name), false) : process(x)).expression(e);
	walkerB(
		(s, process) => {
			if (s.type === 'for' && s.kind !== 'normal' && s.init.type !== 'var_decl')
				targets(s.init);
			return process(s);
		},
		(e, process) => {
			if (e.type === 'arrow' || e.type === 'function')
				return false;
			if (e.type === 'assign')
				targets(e.target);
			else if ((e.type === 'unary' || e.type === 'unary_post') && (e.operator === '++' || e.operator === '--') && e.operand.type === 'identifier')
				names.add(e.operand.name);
			return process(e);
		}
	).statements(stmts);
	return names;
}

type LoopStmt = Extract<Stmt, { type: 'while' | 'do_while' | 'for' }>;
const LOOP_ITERATIONS = 8;

// A loop head merges the entry with every back edge: walked QUIETLY from the entry until the head stops changing, then once for real.
// A head that will not settle takes every name the loop assigns at its declared type, which is always sound.
function checkLoop(stmt: LoopStmt, scope: Scope, labels: string[], typeOf: typeOf, checkStmt: checkStmt, err?: Err): Scope | undefined {
	// What runs once, before the head: a `for`'s initializer, in the scope its bindings live in; a `for-in/of`'s iterable.
	const entry = new Scope(scope);
	let elemT: Type | undefined;
	if (stmt.type === 'for' && stmt.kind === 'normal') {
		if (stmt.init?.type === 'var_decl')
			checkStmt(stmt.init, entry, typeOf, checkStmt);
		else if (stmt.init)
			typeOf(stmt.init, entry);
	} else if (stmt.type === 'for') {
		elemT = stmt.kind === 'in' ? (typeOf(stmt.right, entry), T.STRING) : iterationOrReport(typeOf(stmt.right, entry), entry, getPos(stmt.right)!, err, stmt.kind === 'of await').yield;
	}

	const walk = (head: Scope, quiet: boolean) => {
		const h = new Scope(head);
		h.quiet = quiet;
		const target: T.FlowTarget = h.flowTarget = { labels, loop: true, breaks: [], continues: [] };
		const report = quiet ? undefined : err;
		switch (stmt.type) {
			case 'while': {
				typeOf(stmt.test, h);
				const end = checkStmt(stmt.body, new Scope(narrow(stmt.test, h, true)), typeOf, checkStmt);
				return { back: [end, ...target.continues], exits: [narrow(stmt.test, h, false), ...target.breaks] };
			}
			case 'do_while': {
				const end = joinFlow(h, [checkStmt(stmt.body, new Scope(h), typeOf, checkStmt), ...target.continues]);
				if (end)
					typeOf(stmt.test, end);
				return { back: [end && narrow(stmt.test, end, true)], exits: [end && narrow(stmt.test, end, false), ...target.breaks] };
			}
		}
		if (stmt.kind === 'normal') {
			if (stmt.test)
				typeOf(stmt.test, h);
			const end = checkStmt(stmt.body, new Scope(stmt.test ? narrow(stmt.test, h, true) : h), typeOf, checkStmt);
			// The update runs after the body (or a `continue`), the test holding; its narrowing is the next iteration's.
			const next = joinFlow(h, [end, ...target.continues]);
			const after = next && new Scope(next);
			if (after && stmt.update)
				typeOf(stmt.update, after);
			return { back: [after], exits: [stmt.test ? narrow(stmt.test, h, false) : undefined, ...target.breaks] };
		}
		const inner = new Scope(h);
		if (stmt.init.type === 'var_decl') {
			const home = stmt.init.kind === 'var' ? inner.varScope() : inner;
			for (const d of stmt.init.declarations)
				hoistVar(inner, d, true, d.typeAnnotation ?? elemT, report, !quiet, home);
		} else {
			typeOf(stmt.init, inner);
		}
		return { back: [checkStmt(stmt.body, inner, typeOf, checkStmt), ...target.continues], exits: [h, ...target.breaks] };
	};

	// Only a name narrowed on entry can change at the head: an assignment's value is checked against the declared type, so a back
	// edge never widens a name the entry already holds at its declared type.
	const assigned = assignedNames([stmt]);
	if (![...assigned].some(n => entry.value(n) !== entry.declared(n)))
		return joinFlow(scope, walk(entry, scope.isQuiet()).exits);
	let head = entry;
	let last = walk(head, true);
	let widened = false;
	for (let i = 0; ; i++) {
		const joined	= joinFlow(entry, [entry, ...last.back])!;
		const next		= widenFlow(entry, head, joined);
		if (sameFlow(entry, next, head))
			break;
		if (i === LOOP_ITERATIONS) {
			head = havoc(entry, assigned);
			last = walk(head, true);
			break;
		}
		widened ||= !sameFlow(entry, next, joined);
		head = next;
		last = walk(head, true);
	}
	// Widening overshoots. Stepping down from a settled head (each step still covers every back edge) recovers the bound a test
	// gives: `i < a.length` caps `i` at the length's range, not at the machine limit widening jumped to.
	for (let i = 0; widened && i < 2; i++) {
		const next = joinFlow(entry, [entry, ...last.back])!;
		if (sameFlow(entry, next, head))
			break;
		head = next;
		last = walk(head, true);
	}
	return joinFlow(scope, (scope.isQuiet() ? last : walk(head, false)).exits);
}

export function inferReturn(fnj: JS.CallSig<any>, body: JS.Stmt<any>[], outer: Scope): Type {
	if (fnj.returnType)
		return fnj.returnType;
	const sig = { ...fnj } as TS.CallSig;
	checkFunctionBody(sig, body, outer, false);
	return sig.returnType ?? T.VOID;
}

// The `Scope` holding every lib declaration, passed both to the checker (as an ancestor of the user's `global`) and to `TStoWasm`.
// Checked muted, but every lib method body is walked, so callbacks get contextual params; a generic class's method skips only its stamps.
export function makeLibScope(libAst: Stmt[]): Scope {
	const libScope = new Scope(T.TS_SEMANTICS);
	// `undefined` is a language built-in, which no `.d.ts` may declare (`T.makeGlobal` binds it on the checker-only path).
	libScope.addValue('undefined', T.UNDEFINED);
	checkBlock(libAst, libScope);
	return libScope;
}
