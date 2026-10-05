import * as TS from './ts-parser';
import * as JS from './js-parser';
import * as T from './type-utils';
import { Module, Location, Identifier, Literal, Binary, Conditional, Assign, Await, Member, ExprStmt, hasMod, dropMod, If, While } from '@isopodlabs/tison/ast';
import { walker, walkerB, constantFolder } from './walker';
import { SEVERITY, Err, isPurePath, checkBlock, checkStmt1, exportScope, markAbsenceTests, literalSpecifier, unknownTypeNames, typeOf, typeOf1, inferReturn } from './checker';
import { LoadedModule, ModuleLoader } from './module-loader';

type Expr			= JS.Expr;
type Stmt			= TS.Stmt;
type BindingTarget	= JS.BindingTarget;
type Type			= TS.Type;
type Scope			= T.Scope;
const Scope			= T.Scope;

//-----------------------------------------------------------------------------
// Constant folding
//-----------------------------------------------------------------------------

export function foldConstants<T extends Expr>(e: T) {
	return walker(
		undefined,
		(expr, process) => {
			expr = process(expr);
			switch (expr.type) {
				case 'literal': {
					if (Array.isArray(expr.value)) {
						const parts: JS.TemplatePart<Expr>[] = [];
						let current = '';
						for (const i of expr.value) {
							current += i.str;
							if (i.exp?.type === 'literal') {
								current += i.exp.value?.toString();
							} else {
								parts.push({str: current, exp: i.exp});
								current = '';
							}
						}
						if (parts.length === 0)
							return Literal(current);
						parts.push({str: current});
						return Literal(parts);
					}
					break;
				}
				case 'binary': {
					if (expr.left.type === 'literal' && expr.right.type === 'literal' && expr) {
						const r = constantFolder.fold(expr, [expr.left.value, expr.right.value]);
						if (r)
							return r;
					}
					break;
				}
				case 'unary':
					if (expr.operand.type === 'literal') {
						const r = constantFolder.fold(expr, [expr.operand.value]);
						if (r !== undefined)
							return r;
					}
					break;

				case 'call':
					if (expr.arguments.every(a => a.type === 'literal')) {
						const r = constantFolder.fold(expr, expr.arguments.map(a => (a as Literal<any>).value));
						if (r !== undefined)
							return r;
					}
					break;
					
				case 'conditional':
					if (expr.test.type === 'literal')
						return expr.test.value ? expr.consequent : expr.alternate;
					break;
			}
			return expr;
		},
		undefined
	).expression(e);
}

//-----------------------------------------------------------------------------
// State-machine flattening (generators/async functions)
//-----------------------------------------------------------------------------

// A suspend point in statement position, the only supported shape; a `yield`/`await` inside a larger expression is rejected by `containsSuspend`.
export interface SuspendBoundary {
	kind: 'yield' | 'await';
	operand?:	Expr;
	delegate?:	boolean;	// 'yield*' -- recognized here so it isn't caught by the generic "nested" rejection below; wasm-backend.ts's own consumer currently still rejects delegation itself (a separate, later gap).
	resultVar?:	string;		// set when the source binds the resumed/settled value directly: 'const v = yield x;' / 'const v = await p;'
}

// Every transition out of a segment: 'goto'/'branch' are jumps (a RESUMED call has no structured nesting left), 'complete' the one shared
// "done" landing, reached by falling off the end and by every later call.
export type SegmentNext =
	| { type: 'goto';		target: number }
	| { type: 'branch';		test: Expr; then: number; else: number }
	| { type: 'suspend';	resumeId: number } & SuspendBoundary
	| { type: 'complete' };

export interface StateMachineSegment {
	id:			number;
	stmts:		Stmt[];
	next:		SegmentNext;
}

export interface StateMachine {
	segments:	StateMachineSegment[];
	entryId:	number;
	completeId:	number;
}

// Splits a generator/async body into an id-addressable graph of segments, which codegen turns into one resumable step (a dispatch, one block
// per segment, in a loop so a transition redispatches). Pure AST in and out; `containsSuspend`/`isFlattenable` reject what cannot be expressed.

export function BuildStateMachine(stmts: Stmt[]) {
	const segments = [] as (StateMachineSegment | undefined)[];

	function reserve(): number {
		return segments.push(undefined) - 1;
	}
	function define(id: number, stmts: Stmt[], next: SegmentNext) {
		segments[id] = { id, stmts, next };
	}

	function suspendExpr(e: Expr): SuspendBoundary | undefined {
		return e.type === 'yield' ? { kind: 'yield', operand: e.operand, delegate: e.delegate }
			: e.type === 'await' ? { kind: 'await', operand: e.operand }
			: undefined;
	}

	// The statement shapes recognised as a suspend boundary: a bare `yield x;`/`await p;`, `return await p;`, a single `const v = yield x;`/`= await p;`.
	function suspendBoundary(stmt: Stmt): SuspendBoundary | undefined {
		if (stmt.type === 'expression')
			return suspendExpr(stmt.expression);
		if (stmt.type === 'return' && stmt.argument) {
			// `return (yield x)` is not recognised (only `return await p;`): rare, deferred.
			const b = suspendExpr(stmt.argument);
			return b?.kind === 'await' ? b : undefined;
		}
		if (stmt.type === 'var_decl' && stmt.declarations.length === 1) {
			const d = stmt.declarations[0];
			if (typeof d.name === 'string' && d.init) {
				const b = suspendExpr(d.init);
				if (b)
					return { ...b, resultVar: d.name };
			}
		}
		return undefined;
	}

	// Stops at a nested closure: a yield/await inside it is that function's.
	function containsSuspend(stmt: Stmt): boolean {
		return walkerB(
			undefined,
			(e, process) => suspendExpr(e as Expr) ? true : (e.type === 'arrow' || e.type === 'function') ? false : process(e)
		).statement(stmt);
	}

	// An unlabeled break/continue targeting the loop or switch holding `body` directly, not a nested one (which has its own targets).
	function containsOwnBreakOrContinue(body: Stmt): boolean {
		return walkerB(
			(s, process) => {
				if (s.type === 'break' || s.type === 'continue')
					return true;
				if (s.type === 'while' || s.type === 'do_while' || s.type === 'for' || s.type === 'switch')
					return false;
				return process(s);
			},
			(e, process) => (e.type === 'arrow' || e.type === 'function') ? false : process(e)
		).statement(body);
	}

	function bodyStmtsOf(stmt: Stmt): Stmt[] {
		return stmt.type === 'block' ? stmt.body : [stmt];
	}

	// Flattens `stmts`, returning its entry segment's id. `contId`: where control goes after `stmts`, always a known id, since statements are
	// processed backward and everything after one is already built.
	function recurse(stmts: Stmt[], contId: number): number {
		let cont = contId;
		let trailing: Stmt[] = [];	// ordinary statements seen so far, nearest-to-`cont` first
		const flush = (): number => {
			if (trailing.length === 0)
				return cont;
			const id = reserve();
			define(id, trailing.reverse(), { type: 'goto', target: cont });
			trailing = [];
			cont = id;
			return id;
		};
		for (let i = stmts.length - 1; i >= 0; i--) {
			const stmt = stmts[i];
			const boundary = suspendBoundary(stmt);
			if (boundary) {
				const id = reserve();
				define(id, [], { ...boundary, type: 'suspend', resumeId: flush() });
				cont = id;

			} else if (containsSuspend(stmt)) {
				switch (stmt.type) {
					case 'block':
						cont = recurse(stmt.body, flush());
						break;

					case 'if': {
						const cont0 = flush();
						cont = reserve();
						define(cont, [], {
							type: 'branch', test: stmt.test,
							then: recurse(bodyStmtsOf(stmt.consequent), cont0),
							else: stmt.alternate ? recurse(bodyStmtsOf(stmt.alternate), cont0) : cont0,
						});
						break;
					}
					case 'while': {
						if (containsOwnBreakOrContinue(stmt.body))
							throw new Error("'break'/'continue' inside a yield-containing loop is not yet supported");
						const cont0 = flush();
						cont = reserve();
						define(cont, [], { type: 'branch', test: stmt.test, then: recurse(bodyStmtsOf(stmt.body), cont), else: cont0 });
						break;
					}
					case 'do_while': {
						if (containsOwnBreakOrContinue(stmt.body))
							throw new Error("'break'/'continue' inside a yield-containing loop is not yet supported");
						const cont0		= flush();
						const testId	= reserve();
						cont = recurse(bodyStmtsOf(stmt.body), testId);
						define(testId, [], { type: 'branch', test: stmt.test, then: cont, else: cont0 });
						break;
					}
					case 'for': {
						if (containsOwnBreakOrContinue(stmt.body))
							throw new Error("'break'/'continue' inside a yield-containing loop is not yet supported");
						const cont0		= flush();
						cont = reserve();
						const updateId	= reserve();
						const bodyEntry = recurse(bodyStmtsOf(stmt.body), updateId);
						switch (stmt.kind) {
							case 'normal':
								define(updateId, stmt.update ? [{ type: 'expression', expression: stmt.update } as Stmt] : [], { type: 'goto', target: cont });
								define(cont, [], stmt.test ? { type: 'branch', test: stmt.test, then: bodyEntry, else: cont0 } : { type: 'goto', target: bodyEntry });
								break;
						}
						if (stmt.init) {
							const cont2 = reserve();
							define(cont2, [stmt.init.type === 'var_decl' ? stmt.init : { type: 'expression', expression: stmt.init } as Stmt], { type: 'goto', target: cont });
							cont = cont2;
						}
						break;
					}
					default:
						throw new Error("a yield/await here is not yet supported (only a bare 'yield x;'/'await x;' statement, 'return await x;', 'const v = yield x;', or one of those nested in a plain 'if'/'while'/'do..while'/'for' -- not embedded in a larger expression, and not inside a 'switch'/'try')");
				}

			} else {
				trailing.push(stmt);
			}
		}
		return flush();
	}
	const completeId	= reserve();
	const entryId		= recurse(stmts, completeId);
	define(completeId, [], { type: 'complete' });

	return {
		entryId, completeId,
		segments: segments.map((s, id) => {
			if (!s)
				throw new Error(`internal: state-machine segment ${id} was reserved but never defined`);
			return s;
		}),
	};
}


// Debug only: a `StateMachine` as a printable `while (true) { switch (state) { ... } }` loop, a suspend rendered as `state = resumeId;
// return yield/await x;`. Codegen lowers the same graph straight to wasm.
export function StateMachineToAST(machine: StateMachine) {
	type S = Stmt;
	const state		= Identifier('state');
	const setState	= (v: number): S => ExprStmt(Assign<Expr, JS.assignableOps>(state, Literal(v)));
	const cont: S	= {type: 'continue'};

	// A suspend's `resultVar` (`const v = yield x;`) is bound only once control resumes: re-materialized as a `let` atop the segment it resumes into.
	const resultVars = new Map<number, string>();
	for (const seg of machine.segments)
		if (seg.next.type === 'suspend' && seg.next.resultVar)
			resultVars.set(seg.next.resumeId, seg.next.resultVar);
	const resumeValue = Identifier('$resume');

	return JS.Block<S>(
		JS.VarDecl<Type>('let', JS.Var<Type>('state', Literal(machine.entryId))),
		While(Literal(true), JS.Block<S>(JS.Switch<S>(state, ...machine.segments.map((seg, k) => {
			const stmts: S[] = [];
			const resultVar = resultVars.get(k);
			if (resultVar)
				stmts.push(JS.VarDecl<Type>('let', JS.Var<Type>(resultVar, resumeValue)));
			stmts.push(...seg.stmts);

			const next = seg.next;
			switch (next.type) {
				case 'goto':
					stmts.push(
						setState(next.target),
						cont
					);
					break;

				case 'branch':
					stmts.push(
						If(next.test,
							JS.Block<S>(setState(next.then)),
							JS.Block<S>(setState(next.else))
						),
						cont
					);
					break;

				case 'suspend': {
					if (next.delegate)
						throw new Error("'yield*' delegation is not supported");
					stmts.push(setState(next.resumeId));
					stmts.push(JS.Return(next.kind === 'yield'
						? { type: 'yield', operand: next.operand, delegate: next.delegate }
						: Await(next.operand!)
					));
					break;
				}

				case 'complete':
					stmts.push(JS.Return());
					break;
			}
			return JS.SwitchCase(Literal(k), ...stmts);
		}))))
	);
}


// A destructuring as plain declarations, for VSDG (before the check: the value's path is re-read and indexed) -- `lowerPattern`'s.
export function patternBindings(kind: JS.DeclarationKind, target: BindingTarget, valueExpr: TS.Expr): Stmt[] {
	const out: Stmt[] = [];
	lowerPattern(kind, target, valueExpr, undefined, {}, s => out.push(s));
	return out;
}

//-----------------------------------------------------------------------------
// Lowering for codegen -- after the check; the result is checked with `checkSynthesized`
//-----------------------------------------------------------------------------

type ForOf = Extract<Stmt, { type: 'for'; right: unknown }>;

// `iterator.next()`: JS sends `undefined` to a `next` that takes a value (a generator's).
// As `for...of` calls it, with no argument; `undefined` only where the iterator's `next` declares a parameter it takes (an `any` iterator declares none).
export function nextCall(iterator: TS.Expr, it: T.IterationTypes, scope: Scope): TS.Expr {
	return JS.Call(JS.Member(iterator, 'next'), T.isNullish(it.next, scope) || T.isAny(it.next) ? [] : [Identifier('undefined')]);
}

// An expression codegen compiles as a plainer one, its parts reused (`typeOf` answers a part's checked type); `undefined`: as it is.
// A `string | number` operand of `+` is decided at run time, which this cannot model, so only all-string members concatenate.
export function lowerExpr(e: TS.Expr, typeOf: (e: TS.Expr) => Type, scope: Scope): TS.Expr | undefined {
	// The call a tagged template makes (an untagged one's tag is the lib's `stringTemplate`). One ending in `${...}` has no trailing
	// text part, yet the strings array has one more entry than the values.
	const template = (tag: TS.Expr, quasi: readonly JS.TemplatePart<TS.Expr>[]) => JS.Call(tag, [
		JS.ArrayLit([...quasi.map(p => Literal(p.str)), ...quasi[quasi.length - 1].exp ? [Literal('')] : []]),
		...quasi.flatMap(p => p.exp ? [p.exp] : [])]);
	const isString = (x: TS.Expr) => (ms => ms.length > 0 && ms.every(m => T.isStringLike(m, scope)))(T.unionMembers(T.resolve(scope, typeOf(x)), scope));
	switch (e.type) {
		case 'literal':
			return e.value instanceof RegExp ? { type: 'new', callee: Identifier('RegExp'), arguments: [Literal(e.value.source), Literal(e.value.flags)] }
				: Array.isArray(e.value) ? (e.value.some(p => p.exp) ? template(Identifier('stringTemplate'), e.value) : Literal(e.value.map(p => p.str).join('')))
				: undefined;
		case 'unary':
			return e.operator === '+' && T.typeofName(typeOf(e.operand), scope) === 'string' ? JS.Call(Identifier('Number'), [e.operand]) : undefined;
		case 'binary':
			// `**` has no instruction: a number's is `Math.pow`, a bigint's its own `pow`. `+` with one string side is the template `${a}${b}`.
			return e.operator === '**' && !T.isBigint(typeOf(e.left), scope) ? JS.Call(JS.Member(Identifier('Math'), 'pow'), [e.left, e.right])
				: e.operator === '+' && isString(e.left) !== isString(e.right) ? Literal([{ str: '', exp: e.left }, { str: '', exp: e.right }])
				: undefined;
		case 'tagged_template':
			return template(e.tag, e.quasi);
		default:
			return undefined;
	}
}

// `t op= v` as `t = t op v`, `t`'s object and index held first unless re-reading them is pure, so each is evaluated once.
export function lowerCompound(e: Extract<TS.Expr, { type: 'assign' }>, op: JS.assignableOps, temp: (role: string) => string, emit: (s: Stmt) => void): TS.Expr {
	const hold = (x: TS.Expr): (() => TS.Expr) => {
		if (isPurePath(x) || x.type === 'literal')
			return () => x;
		const name = temp('compound');
		emit(JS.VarDecl('const', JS.Var(name, x)));
		return () => Identifier(name);
	};
	const t = e.target;
	const place: () => TS.Expr = t.type === 'member' ? (o => () => JS.Member(o(), t.property))(hold(t.object))
		: t.type === 'index' ? ((o, i) => () => JS.Index(o(), i()))(hold(t.object), hold(t.index))
		: () => t;
	return Assign<TS.Expr, never>(place(), Binary(op, place(), e.value));
}

// `Object.assign(target, {k: v}, ...)` whose sources write their keys out: the target held, then an ordinary `t.k = v` per key.
export function lowerObjectAssign(target: TS.Expr, writes: { key: string; value: TS.Expr }[], temp: (role: string) => string, emit: (s: Stmt) => void): TS.Expr {
	const t = temp('assign');
	emit(JS.VarDecl('const', JS.Var(t, target)));
	writes.forEach(w => emit(ExprStmt(Assign<TS.Expr, never>(JS.Member(Identifier(t), w.key), w.value))));
	return Identifier(t);
}

// `{...a, ...(c ? {k: v} : {}), ...}` is the literal either arm makes, `c ? {...a, k: v, ...} : {...a, ...}`: what precedes the conditional
// is held first, so each value is still read once and in order. `undefined` when no spread is such a conditional.
export function lowerConditionalSpread(e: Extract<TS.Expr, { type: 'object' }>, temp: (role: string) => string, emit: (s: Stmt) => void): TS.Expr | undefined {
	const bare	= (x: TS.Expr): TS.Expr => x.type === 'as' ? bare(x.expression) : x;
	const picks	= (p: typeof e.properties[number]) => {
		const c = p.type === 'spread' ? bare(p.operand) : undefined;
		const a = c?.type === 'conditional' ? bare(c.consequent) : undefined, b = c?.type === 'conditional' ? bare(c.alternate) : undefined;
		return c?.type === 'conditional' && a?.type === 'object' && b?.type === 'object' ? { test: c.test, arms: [a.properties, b.properties] } : undefined;
	};
	const at = e.properties.findIndex(p => picks(p));
	if (at < 0)
		return undefined;
	const { test, arms } = picks(e.properties[at])!;
	// Each held value read through a fresh node per arm: a checked node holds one type.
	const hold = (value: TS.Expr) => {
		const name = temp('cspread');
		emit(JS.VarDecl('const', JS.Var(name, value)));
		return () => Identifier(name);
	};
	const before = e.properties.slice(0, at).map(p => {
		if (p.type === 'spread')
			return (v => () => ({ ...p, operand: v() }))(hold(p.operand));
		if (p.type !== 'field' || !p.value)
			return () => p;
		const key = typeof p.key === 'object' ? hold(p.key.computed) : undefined, value = hold(p.value);
		return () => ({ ...p, key: key ? { computed: key() } : p.key, value: value() });
	});
	const [yes, no] = arms.map(props => ({ ...e, properties: [...before.map(b => b()), ...props, ...e.properties.slice(at + 1)] }));
	return Conditional<TS.Expr>(test, yes, no);
}

// How a destructuring is lowered for its consumer. Codegen names each level (`temp`), so each value is read once, and asks the
// checked types how a level iterates (`iterates`: by the protocol, else by position) and whether a position may hold `undefined`.
export interface PatternLowering {
	temp?:		(role: string) => string;
	iterates?:	(value: TS.Expr) => T.IterationTypes | undefined;
	absent?:	(element: TS.Expr) => boolean;
	scope?:		Scope;
}

// A destructuring as plain declarations, each handed to `emit` in order: a later level's questions are about what an earlier one
// declared. A default replaces `undefined` only, never `null`; a position past the end is `undefined` (a length test: wasm traps there).
export function lowerPattern(kind: JS.DeclarationKind, target: BindingTarget, value: TS.Expr, annotation: Type | undefined, how: PatternLowering, emit: (s: Stmt) => void): void {
	if (typeof target === 'string')
		return emit(JS.VarDecl(kind, JS.Var(target, value, annotation)));
	// A level held in a temp is read through a fresh node per use: each is typed where it stands, and a node holds one type.
	const hold = (init: TS.Expr, role: string, t?: Type): (() => TS.Expr) => {
		if (!how.temp)
			return () => init;
		const name = how.temp(role);
		emit(JS.VarDecl('const', JS.Var(name, init, t)));
		return () => Identifier(name);
	};
	const sub	= (t: BindingTarget, e: TS.Expr, ann?: Type) => lowerPattern(kind, t, e, ann, how, emit);
	const v		= hold(value, 'destructure', annotation);
	if (target.type === 'array_pattern') {
		const it = how.iterates?.(v());
		if (it && how.temp && how.scope) {
			const iter = hold(JS.Call(JS.Member(v(), '[Symbol.iterator]'), []), 'iterator');
			for (const el of target.elements) {
				const r = hold(nextCall(iter(), it, how.scope), 'result');	// a hole still advances
				if (el)
					sub(el.target, el.default ? Conditional<TS.Expr>(JS.Member(r(), 'done'), el.default, Binary('??', JS.Member(r(), 'value'), el.default)) : JS.Member(r(), 'value'), el.default ? undefined : it.yield);
			}
			if (target.rest)
				sub(target.rest, drainIterator(iter(), it, how.scope, how.temp, emit));
			return;
		}
		target.elements.forEach((el, i) => {
			const elem = () => JS.Index(v(), Literal(i));
			if (el)
				sub(el.target, !el.default ? elem() : Conditional<TS.Expr>(Binary<TS.Expr, '<'>('<', Literal(i), JS.Member(v(), 'length')),
					how.absent?.(elem()) === false ? elem() : Conditional<TS.Expr>(Binary<TS.Expr, '==='>('===', elem(), Identifier('undefined')), el.default, elem()), el.default));
		});
		if (target.rest)
			sub(target.rest, JS.Call(JS.Member(v(), 'slice'), [Literal(target.elements.length)]));
		return;
	}
	if (target.rest)
		throw "a rest property ('...') in an object destructuring pattern is not supported -- it needs a new object type holding 'all fields but these'";
	for (const prop of target.properties) {
		const key = JS.keyName(prop.key);
		if (key === undefined)
			throw "a computed key ('[expr]') in an object destructuring pattern is not supported";
		const propExpr = JS.Member(v(), key);
		sub(prop.value, prop.default ? Binary('??', propExpr, prop.default) : propExpr);
	}
}

// Every remaining value of an iterator, into a new array: what `...` does with an iterable, and a rest element.
export function drainIterator(iterator: TS.Expr, it: T.IterationTypes, scope: Scope, temp: (role: string) => string, emit: (s: Stmt) => void): TS.Expr {
	const arr = temp('drained'), r = temp('result');
	emit(JS.VarDecl('const', JS.Var(arr, JS.ArrayLit([]), TS.ArrayType(it.yield))));
	emit(JS.For(JS.VarDecl('let', JS.Var(r, nextCall(iterator, it, scope))), JS.JSUnary('!', JS.Member(Identifier(r), 'done')), Assign<TS.Expr, never>(Identifier(r), nextCall(iterator, it, scope)),
		ExprStmt(JS.Call(JS.Member(Identifier(arr), 'push'), [JS.Member(Identifier(r), 'value')]))));
	return Identifier(arr);
}

// `for (v of xs) body` as plain loops: by the iteration protocol where codegen iterates by it (`it`: what iterating yields), else by
// position, a string's (`byCodePoint`) a code point at a time as its iterator yields. `temp` names a fresh hidden binding.
export function lowerForOf(s: ForOf, it: T.IterationTypes | undefined, scope: Scope, temp: (role: string) => string, byCodePoint = false): Stmt {
	if (s.init.type !== 'var_decl' || s.init.declarations.length !== 1)
		throw "'for...of' loop variable must be a single declaration";
	const v		= s.init.declarations[0], kind = s.init.kind;
	const bind	= (value: TS.Expr, t?: Type) => JS.Block<Stmt>(JS.VarDecl(kind, JS.Var(v.name, value, v.typeAnnotation ?? t)), s.body);
	// A fresh node per use: each is typed where it stands (`r` narrowed by `!r.done`), and a node holds one type.
	const use = (name: string) => () => Identifier(name);
	if (it) {
		const iter = use(temp('it')), r = use(temp('r'));
		return JS.Block<Stmt>(
			JS.VarDecl('const', JS.Var(iter().name, JS.Call(JS.Member(s.right, '[Symbol.iterator]'), []))),
			JS.For(JS.VarDecl('let', JS.Var(r().name, nextCall(iter(), it, scope))), JS.JSUnary('!', JS.Member(r(), 'done')), Assign<TS.Expr, never>(r(), nextCall(iter(), it, scope)), bind(JS.Member(r(), 'value'), it.yield)),
		);
	}
	const arr = use(temp('arr')), i = use(temp('i'));
	const step = byCodePoint ? Assign<TS.Expr, never>(i(), JS.JSBinary('+', i(), JS.Call(JS.Member(arr(), '_codePointLength'), [i()]))) : JS.JSUnary('++', i());
	return JS.Block<Stmt>(
		JS.VarDecl('const', JS.Var(arr().name, s.right)),
		JS.For(JS.VarDecl('let', JS.Var(i().name, Literal(0))), JS.JSBinary('<', i(), JS.Member(arr(), 'length')), step,
			bind(byCodePoint ? JS.Call(JS.Member(arr(), '_codePointString'), [i()]) : JS.Index(arr(), i()))),
	);
}

//-----------------------------------------------------------------------------
// TS to JS
//-----------------------------------------------------------------------------

const dropOptional = (p: JS.Param<any>) => dropMod(p, 'optional');

export function TStoJS(ast: Module<Stmt>) {
	return walker(
		(stmt, process) => {
			switch (stmt.type) {
				case 'type_alias_decl':
				case 'interface_decl':
				case 'namespace_decl':
					return undefined;

				case 'export_decl':
					stmt = process(stmt);
					return stmt.declaration ? stmt : undefined;

				case 'function_decl':
					if (!stmt.body)
						return undefined;
					stmt = process(stmt);
					stmt.params.forEach(dropOptional);
					return stmt;

				case 'enum_decl': {
					stmt = process(stmt);
					let next = 0;
					return JS.VarDecl('const', {
						name: stmt.name,
						init: JS.ObjectExpr(stmt.members.map(m => {
							let value: Expr;
							if (m.init) {
								value = m.init;
								next = T.isLiteral(m.init, 'number') ? m.init.value + 1 : NaN;
							} else {
								value = Literal(next++);
							}
							return JS.Field(m.name, value);
						})),
					});
				}
				
				case 'var_decl':
					return stmt.ambient ? undefined : process(stmt);

				case 'class_decl':
					if (stmt.ambient)
						return undefined;
					stmt = process(stmt);
					stmt.body.forEach(m => {
						if (m.type === 'field') {
							delete m.modifiers;

						} else if (m.type === 'method') {
							if (m.key === 'constructor') {
								// A parameter-property modifier is anything but `'optional'`, which `modifiers` may also hold.
								const prelude: JS.Stmt<any>[] = m.params
									.filter((p) => p.modifiers?.some(x => x !== 'optional'))
									.map(p => ({
										type: 'expression',
										expression: Assign<Expr, JS.assignableOps>(
											Member<Expr>({ type: 'this' }, p.key as string),
											Identifier(p.key as string),
										),
									})
								);
								if (prelude.length)
									m.body = [...prelude, ...m.body!];
							}

							for (const p of m.params)
								delete p.modifiers;
							delete m.modifiers;
						}
					});
					delete stmt.typeParams;
					delete stmt.implements;
					delete stmt.abstract;
					return stmt;

				default:
					return process(stmt);
			}

		},
		(expr, process, recurse) => {
			switch (expr.type) {

				case 'function':
					expr = process(expr)!;
					expr.params.forEach(dropOptional);
					return expr;

				case 'arrow':
					expr = process(expr)!;
					expr.params.forEach(dropOptional);
					return expr;

				case 'class':
					return {...process(expr)!, typeParams: undefined, implements: undefined, abstract: undefined};

				case 'as':
				case 'satisfies':
				case 'instantiation':
					return recurse.expression(expr.expression);

				case 'unary_post':
					return expr.operator === '!' ? recurse.expression(expr.operand) : process(expr);

				default:
					return process(expr);
			}
		},
		(_type, _process) => undefined
	).module(ast);
}

// ===================================================================
//  TStypeCheck
// ===================================================================

export interface Diagnostic {
	severity:	SEVERITY;
	pos:		Location;
	message:	string;
}

function makeDiagnostic(func: (d: Diagnostic) => void): Err {
	const clip		= (s: string, max = 60)	=> s.length > max ? s.slice(0, max - 3) + '...' : s;
	const toString	= (v: string | number | undefined) => v === undefined ? '' : String(v);

	return (severity: SEVERITY, pos: Location) => (strings: TemplateStringsArray, ...values: (string | number | undefined)[]) => func({
		severity,
		message: ['GAP', 'WRN', 'ERR'][severity] + ': ' + strings.map((s, i) => s + clip(toString(values[i]))).join(''),
		pos
	});
}

// Folds any depth-budget hits from type-utils.ts's structural recursion into one summary GAP diagnostic, not one per occurrence.
function pushDepthExhaustionGap(depthHits: Map<string, number>, diagnostics: Diagnostic[]) {
	if (depthHits.size) {
		diagnostics.push({
			severity: SEVERITY.GAP,
			pos: { line: 1, col: 1 },
			message: 'GAP: recursion depth limit reached during structural type resolution ('
				+ [...depthHits].map(([fn, n]) => `${fn}×${n}`).join(', ')
				+ ') -- some assignability/member checks may be incomplete',
		});
	}
}

// `global`: the scope the program is checked under, a lib scope (`makeLibScope`) as its ancestor when a later consumer (`TStoWasm`) needs
// the lib in view from the program's own scopes.
export function TStypeCheck(ast: Module<Stmt>, global: Scope): Diagnostic[] {
	const diagnostics: Diagnostic[] = [];
	checkEntry(ast, global, global, diagnostics);
	return diagnostics;
}

function checkEntry(ast: Module<Stmt>, scope: Scope, global: Scope, diagnostics: Diagnostic[]) {
	// A SCRIPT (no top-level import/export) declares into the global space -- see `Scope.globalSpace`.
	scope.globalSpace = !ast.body.some(s => s.type === 'import' || s.type === 'export' || s.type === 'export_decl' || s.type === 'export_assignment');
	const depthExhaustion = new Map<string, number>();
	global.hitDepthLimit = fn => depthExhaustion.set(fn, (depthExhaustion.get(fn) ?? 0) + 1);
	// The expressions a statement holds report through the same `err` as the statement itself, top level included.
	const err = makeDiagnostic(d => diagnostics.push(d));
	markAbsenceTests(ast.body);
	const unknownNames = scope.reportsUnknownNames() ? unknownTypeNames(ast.body) : undefined;
	checkBlock(ast.body, scope, typeOf1(err), checkStmt1(err));
	unknownNames?.(err);
	pushDepthExhaustionGap(depthExhaustion, diagnostics);
	ast.scope = scope;
}

// `tainted`: this build (or one it awaited) had to skip something to avoid deadlocking on a genuine import cycle -- real and usable, just incomplete.
interface ModuleShape { scope: Scope; value: Type; tainted: boolean }

// The checker's memos for one module, stamped on its record: keyed by identity, a memo is reusable exactly while its module is, and
// process-wide tables kept every past compile's scopes alive.
interface ModuleMemo {
	// A genuine cycle (Node's `fs`<->`fs/promises` `.d.ts` graph) truncates whichever side asks second; `tainted` marks that, so it is cleared later.
	shape?:		Promise<ModuleShape>;
	// Own declarations, recorded before re-export merging (the part that can cycle): a plain `import`'s deadlock fallback resolves from here.
	own?:		{ scope: Scope; alias?: Type };
	// What this module is currently waiting on, for `wouldDeadlock`.
	waiting?:	Set<LoadedModule>;
}
const memoOf = (m: LoadedModule): ModuleMemo => ((m as { memo?: ModuleMemo }).memo ??= {});

function wouldDeadlock(waiter: LoadedModule, target: LoadedModule): boolean {
	const seen = new Set<LoadedModule>([target]);
	const stack = [target];
	while (stack.length) {
		const cur = stack.pop()!;
		if (cur === waiter)
			return true;
		for (const next of memoOf(cur).waiting ?? []) {
			if (!seen.has(next)) {
				seen.add(next);
				stack.push(next);
			}
		}
	}
	return false;
}

async function safely<T>(waiter: LoadedModule, target: LoadedModule, func: () => Promise<T>): Promise<T | undefined> {
	if (wouldDeadlock(waiter, target))
		return undefined;

	const waits = memoOf(waiter).waiting ??= new Set();
	waits.add(target);
	try {
		return await func();
	} finally {
		waits.delete(target);
	}
}

export async function loadLib(loader: ModuleLoader, libs: string[]): Promise<T.Scope> {
	const global	= T.makeGlobal();
	for (const spec of libs!) {
		const lib = await loader.get(spec, '.');
		if (lib) {
			markAbsenceTests(lib.program.body);
			checkBlock(lib.program.body, global);
		}
	}
	return global;
}

// As `TStypeCheck`, with `global` chained on top of whatever `options.lib` loads.
export async function TStypeCheckAsync(program: Module<Stmt>, loader: ModuleLoader, global: Scope) {
	const diagnostics: Diagnostic[] = [];

	// A module's shape; on a genuine cycle, its own declarations so far (tainted), if it has any yet.
	const shapeOf = async (waiter: LoadedModule, src: LoadedModule): Promise<ModuleShape | undefined> => {
		const resolved	= await safely(waiter, src, () => makeScope(src));
		const own		= resolved ? undefined : memoOf(src).own;
		return resolved ?? (own && { scope: own.scope, value: own.alias ?? own.scope.toObject(), tainted: true });
	};

	// A literal `import('...')` resolves as a static import does, onto the call, which the checker types `Promise<namespace>`.
	const resolveDynamicImports = async (waiter: LoadedModule, body: readonly Stmt[], from: string) => {
		const calls: JS.ImportCall[] = [];
		walkerB(undefined, (e, process) => (e.type === 'import_call' && calls.push(e), process(e))).statements(body);
		for (const call of calls) {
			const spec	= literalSpecifier(call);
			const src	= spec === undefined ? undefined : await loader.get(spec, from);
			call.module	= src && (await shapeOf(waiter, src))?.value;
		}
	};

	// Resolves one `import` into `importScope`; false is a cycle truncation, feeding `makeScope`'s `tainted`.
	const resolveImport = async (waiter: LoadedModule, importScope: Scope, imp: JS.Import, from: string): Promise<boolean> => {
		const impSrc = await loader.get(imp.source, from);
		if (!impSrc) {
			diagnostics.push({ severity: 1, pos: (imp as any).pos, message: `Could not resolve import '${imp.source}'` });
			return true;	// unresolvable specifier, not a cycle -- nothing for `makeScope` to retry later
		}
		const resolved = await shapeOf(waiter, impSrc);
		if (!resolved)
			return false;	// genuine import cycle -- contribute nothing further rather than deadlock

		const { scope: impScope, value } = resolved;

		// A default import (`import X from 'mod'`), which may combine with the other forms; `exportScope` registers a default export as `'default'`.
		if (imp.default)
			importScope.copy(impScope, 'default', imp.default, imp.typeOnly);

		if (imp.namespace) {
			importScope.addValue(imp.namespace, value);
			importScope.addNamespace(imp.namespace, impScope);
		} else {
			for (const spec of imp.specifiers ?? [])
				importScope.copy(impScope, spec.imported, spec.local, spec.typeOnly || imp.typeOnly);
		}
		return !resolved.tainted;
	};

	// One at a time, in source order: concurrently, WHICH edge of an import cycle got cut depended on I/O timing.
	const resolveImports = async (waiter: LoadedModule, importScope: Scope, body: readonly Stmt[], from: string) => {
		const clean: boolean[] = [];
		for (const s of body)
			if (s.type === 'import')
				clean.push(await resolveImport(waiter, importScope, s, from));
		return clean;
	};

	// `src`'s exported symbols as one `Scope`, `export ... from` re-exports resolved here, where the loader is.
	async function makeScope(src: LoadedModule): Promise<ModuleShape> {
		const existing = memoOf(src).shape;
		if (existing)
			return existing;

		const importScope = new Scope(global);
		const cached = resolveImports(src, importScope, src.program.body, src.canonical).then(async imports => {
			let tainted = imports.some(clean => !clean);
			await resolveDynamicImports(src, src.program.body, src.canonical);
			markAbsenceTests(src.program.body);
			const { scope, inner, alias } = exportScope(src.program.body, importScope, src.program.filename);
			// The module RECORD carries its full internal scope: codegen resolves names declared inside the module through it.
			src.program.scope ??= inner;
			// Recorded before the (possibly cyclic) re-export loop awaits anything -- see `ModuleMemo.own` for why placement matters.
			memoOf(src).own = { scope, alias };
			for (const stmt of src.program.body) {
				if (stmt.type !== 'export' || !stmt.source)
					continue;
				const target = await loader.get(stmt.source, src.canonical);
				if (!target)
					continue;
				const targetShape = await safely(src, target, () => makeScope(target));
				if (!targetShape) {
					tainted = true;
					continue;	// genuine circular re-export chain -- contribute nothing further rather than deadlock/recurse forever
				}
				tainted ||= targetShape.tainted;

				if (stmt.namespace) {
					// `export * as name from './x'`: one property holding the target's whole shape.
					scope.addValue(stmt.namespace, targetShape.value);
					scope.addNamespace(stmt.namespace, targetShape.scope);

				} else if (stmt.specifiers) {
					for (const spec of stmt.specifiers)
						scope.copy(targetShape.scope, spec.local, spec.exported, stmt.typeOnly || spec.typeOnly);
				} else {
					// bare `export * from './x'`: everything, as-is
					scope.copyAll(targetShape.scope, stmt.typeOnly);
				}
			}
			// `toObject()` after the re-export loop, so the value type includes what `export ... from` merged in.
			return { scope, value: alias ?? scope.toObject(), tainted };
		});
		memoOf(src).shape = cached;
		// Only clean builds are cached; a tainted one serves concurrent awaiters, then is evicted (identity-checked), so the next caller retries.
		cached.then(result => {
			if (result.tainted && memoOf(src).shape === cached)
				memoOf(src).shape = undefined;
		});
		return cached;
	}

	// The entry program never goes through `makeScope`: just its own identity for `wouldDeadlock`.
	const entryScope = new Scope(global);
	const entry = { program, canonical: '.' };
	await resolveImports(entry, entryScope, program.body, '.');
	await resolveDynamicImports(entry, program.body, '.');

	checkEntry(program, entryScope, global, diagnostics);
	return diagnostics;
}

// ===================================================================
//  TStoDecl -- TypeScript AST to a .d.ts-shaped AST
// ===================================================================

export const OutputOptionsDefault = {
	declaration:							false,
	declarationDir:							undefined,
	declarationMap:							undefined,
	downlevelIteration:						undefined,
	emitBOM:								undefined,
	emitDeclarationOnly:					undefined,
	importHelpers:							undefined,
	inlineSourceMap:						undefined,
	inlineSources:							undefined,
	mapRoot:								undefined,
	newLine:								'\n',
	noEmit:									undefined,
	noEmitHelpers:							undefined,
	noEmitOnError:							undefined,
	outDir:									undefined,
	outFile:								undefined,
	preserveConstEnums:						undefined,
	removeComments:							undefined,
	sourceMap:								undefined,
	sourceRoot:								undefined,
	stripInternal:							undefined,
};

// The type kinds `T.resolve` can simplify: constructs with no printable name (a `ref` stays a name).
const RESOLVABLE = new Set(['mapped', 'conditional', 'indexed_access', 'keyof', 'typeof']);

// One `onType` pass doing two things: a `ref` to another module's scope is requalified through a namespace import that reaches it (or inlined),
// and an unprintable construct (`mapped`/`conditional`/`keyof`/...) is resolved to its structure. Named refs stay names, as declaration emit does.

function resolveTypes(entryScope: Scope, importScope: Scope | undefined) {
	// (alias, first type argument) pairs on the inline stack: re-entering with the SAME argument is a cycle (`ReadType<T>` recursing with a different
	// `T` is not). Keyed by `T.typeKey`, since each substitution builds a fresh object even when a type recurs.
	const inlining = new Map<Type, Set<string | undefined>>();
	let depth = 0;	// nesting depth across *all* active inlines, not per-alias -- distinct from the per-(alias,argument) cycle check just above: bounds legitimately deep but finite recursion (real generic helper libraries chain many distinct instantiations), which the cycle check alone wouldn't catch since each level's argument genuinely differs.
	let scope = entryScope;	// ambient scope for scope-less constructs (`typeof`, `mapped`'s `keyof` &c) -- tracks whichever module's body we're currently inlining through

	// Thrown when a computed-type unwrap's cycle guard or depth cap fires, caught by the top-level call that started the chain, which prints the
	// original ref rather than a partial expansion.
	class ComputedCycle {}

	const MAX_DEPTH = 40;

	return (type: Type, process: (t: Type, recall?: boolean) => Type | undefined): Type | undefined => {
		if (type.type === 'ref' && type.declScope) {
			const declScope	= type.declScope as Scope;
			const entry		= declScope.lookupType(type.name);
			if (entry) {
				// Requalifies a ref through a namespace import that reaches it (`ReadType` -> `bin.ReadType`), or to its bare leaf where that already reaches it
				// (a `pe.PE` printed from inside `pe`'s own module); used whenever the ref is not unwrapped in place, or the unwrap bailed.
				const requalify = (): Type | undefined => {
					if (!importScope)
						return undefined;
					const leaf = type.name.split('.').pop()!;
					// Reference-identity match, same as `findQualifiedPath` -- the normal case.
					if (importScope.type(leaf)?.type === entry.type)
						return leaf === type.name ? process(type) : process(TS.RefType(leaf, type.typeArgs));
					const path = importScope.findQualifiedPath(leaf, entry.type);
					if (path)
						return process(TS.RefType([...path, leaf].join('.'), type.typeArgs));
					// No identity match: across an import cycle, a type declared in this module can come back as another object. The same leaf in this module's
					// top-level scope is the best signal short of structural equality: printed bare.
					return importScope.type(leaf) ? process(TS.RefType(leaf, type.typeArgs)) : undefined;
				};

				// A ref whose body is a nameless computed construct (a type-level function like `bin.ReadType<T>`) is unwrapped one level rather than printed
				// as a name hiding the computation. The try/catch covers both branches: a `ComputedCycle` from a foreign inline must unwind to here.
				const topLevel = inlining.size === 0;
				try {
					const resolvable = RESOLVABLE.has(entry.type.type);
					if (!resolvable) {
						const r = requalify();
						if (r !== undefined)
							return r;
					}

					// Substitutes `typeArgs` into `entry`'s body and recurses, cycle-guarded. `bail`: throw `ComputedCycle` rather than stop, for the `RESOLVABLE`
					// chain, which has nothing to fall back to mid-expansion.

					const argKey	= type.typeArgs?.[0] && T.typeKey(type.typeArgs[0]);
					const active	= inlining.get(entry.type);
					if (active?.has(argKey) || depth >= MAX_DEPTH) {
						if (resolvable)
							throw new ComputedCycle;
					} else {
						const set = active ?? new Set<string | undefined>();
						if (!active)
							inlining.set(entry.type, set);
						set.add(argKey);
						++depth;
						const savedScope = scope;
						scope = declScope;
						try {
							return process(entry.typeParams?.length
								? T.substituteType(entry.type, new Map(entry.typeParams.map((p, i) => [p.name, type.typeArgs?.[i] ?? p.default ?? T.ANY])))
								: entry.type
								, true);
						} finally {
							scope = savedScope;
							--depth;
							set.delete(argKey);
							if (!set.size)
								inlining.delete(entry.type);
						}
					}
				} catch (e) {
					if (!topLevel || !(e instanceof ComputedCycle))
						throw e;
					// The unwrap bailed: still worth requalifying before giving up to the original ref.
					const r = requalify();
					if (r !== undefined)
						return r;
				}
			}
			return process(type);
		}

		if (RESOLVABLE.has(type.type)) {
			// `stopAtRef`: once resolution reaches a named type, that name prints.
			const resolved = T.resolve(scope, type, undefined, true);
			if (resolved !== type) {
				const found = scope.findDeclaredName(resolved);
				return process(found ? T.withScope(TS.RefType(found.name), found.scope) : resolved, true);	// recall
			}
		}
		return process(type);
	};
}

export function TStoDecl(program: Module<Stmt>, opts?: Partial<typeof OutputOptionsDefault>): Module<Stmt> {
	const options		= {...OutputOptionsDefault, ...opts};
	const importScope	= program.scope as Scope | undefined;

	// ---- Gathering every top-level declaration, and seeding `reachable` with the explicit exports ----

	type Owner = TS.Stmt | JS.Var<any>;
	class Owners extends Map<string, Owner[]> {
		exported	= false;
		add(name: string, owner: Owner) {
			this.set(name, [...(this.get(name) ?? []), owner]);
			if (this.exported)
				reachable.add(name);
		}
	}

	const owners	= new Owners;
	const reachable = new Set<string>();

	// ---- Shared checking/resolution machinery, needed by the strip helpers below --------------------

	const global	= importScope ? new Scope(importScope) : T.makeGlobal();
	markAbsenceTests(program.body);
	checkBlock(program.body, global);

	// A class whose heritage is a call (`bin.Class(spec)`) cannot keep it in a `declare class`: `declare const <Name>_base: <type>;` is prepended
	// and the class extends that name, as tsc's emitter does. Seeded into `reachable`, as nothing else names it.
	const syntheticBases: TS.Stmt[] = [];

	// Every top-level name, before stripping, so a synthesized base name collides with no real declaration.
	const usedNames = new Set<string>();
	for (let stmt of program.body) {
		if (stmt.type === 'export_decl')
			stmt = stmt.declaration;
		switch (stmt.type) {
			case 'function_decl': case 'class_decl': case 'interface_decl':
			case 'type_alias_decl': case 'enum_decl': case 'namespace_decl':
				usedNames.add(stmt.name);
				break;
			case 'var_decl':
				for (const d of stmt.declarations)
					for (const name of T.bindingNames(d.name))
						usedNames.add(name);
				break;
		}
	}
	const uniqueName = (base: string) => {
		let name = base;
		for (let n = 1; usedNames.has(name); n++)
			name = base + n;
		usedNames.add(name);
		return name;
	};

	// ---- Strip helpers -------------------------------------------------------------------------------

	// `undefined`, not `: any`, keeps an unknowable type implicit.
	const inferType		= (e: Expr, narrow: boolean): Type | undefined => {
		const t = typeOf(e, global, !narrow);
		return t.type === 'ref' && t.name === 'any' ? undefined : t;
	};

	const stripBindingDefaults = (t: BindingTarget): BindingTarget => {
		if (typeof t === 'string')
			return t;
		if (t.type === 'object_pattern')
			return { ...t, properties: t.properties.map(p => ({ ...p, value: stripBindingDefaults(p.value), default: undefined })) };
		return { ...t, elements: t.elements.map(el => el && ({ ...el, target: stripBindingDefaults(el.target), default: undefined })) };
	};
	
	const stripParam = (p: JS.Param<any>): JS.Param<any> => ({ ...p,
		key:			stripBindingDefaults(p.key),
		typeAnnotation: p.typeAnnotation ?? (p.default && inferType(p.default, false)),
		default:		undefined,
		modifiers:		hasMod(p, 'optional') || !!p.default ? ['optional'] : []
	});

	const PROMISE_TYPES		= new Set(['Promise']);
	const GENERATOR_TYPES	= new Set(['Generator', 'IterableIterator', 'Iterator', 'Iterable']);

	const stripFunctionDecl = (stmt: JS.FunctionDecl<any>): JS.Declaration<any> => {
		const returnType: Type = stmt.returnType ? stmt.returnType as Type : stmt.body ? inferReturn(stmt, stmt.body, global) : T.ANY;
		return JS.FunctionDecl(stmt.name, {
			params:		stmt.params.map(stripParam),
			typeParams:	stmt.typeParams,
			returnType: hasMod(stmt, 'async')		? T.wrapType(returnType, PROMISE_TYPES, 'Promise')
					:	hasMod(stmt, 'generator')	? T.wrapType(returnType, GENERATOR_TYPES, 'Generator')
					:	returnType
		}, undefined, {ambient: true});
	};

	// A single type parameter constrained to a literal union, used directly as one parameter's type, expands into one non-generic overload per
	// literal, each return collapsing to its own result instead of exposing the machinery that computed them all.
	function expandConstrainedGeneric(typeParams: TS.TypeParam[] | undefined, params: JS.Param<any>[], returnType: Type | undefined) {
		const tparam = typeParams?.length === 1 ? typeParams[0] : undefined;
		if (!tparam?.constraint)
			return undefined;
		let target: JS.Param<any> | undefined;
		for (const p of params) {
			if (p.typeAnnotation?.type === 'ref' && !p.typeAnnotation.typeArgs && p.typeAnnotation.name === tparam.name) {
				if (target)
					return undefined;	// ambiguous -- more than one param depends directly on T
				target = p;
			}
		}
		if (!target)
			return undefined;

		const constraint	= T.resolve(global, tparam.constraint);
		const members		= constraint.type === 'union' ? constraint.types : [constraint];
		if (!members.every(m => T.isLiteral(m, 'string') || T.isLiteral(m, 'number')))
			return undefined;

		return members.map(m => ({
			params:		params.map(p => p === target ? { ...p, typeAnnotation: m } : p),
			returnType:	returnType && T.expandRefOnce(global, T.substituteType(returnType, new Map([[tparam.name, m]]))),
		}));
	}

	const stripClassDecl = (stmt: JS.ClassDecl<any>): JS.Declaration<any> => {
		const setKeys	= new Set(stmt.body.flatMap(m => m.type === 'set' ? JS.keyName(m.key) ?? [] : []));
		const seen		= new Set<string>();

		// A non-identifier heritage cannot survive into a `.d.ts`: its type becomes a synthesized `declare const _base` to extend instead.
		let superClass = stmt.superClass;
		if (superClass && superClass.type !== 'identifier') {
			const name = uniqueName((stmt.name ?? '_default') + '_base');
			reachable.add(name);
			syntheticBases.push(JS.AmbientVarDecl('const', JS.Var(name, undefined, typeOf(superClass, global))));
			superClass = Identifier(name);
		}

		return {
			...stmt,
			body: (stmt.body as TS.ClassMember[]).flatMap((m): TS.ClassMember[] => {
				switch (m.type) {
					case 'field':
						return [JS.Field(m.key, undefined, m.typeAnnotation ?? (m.value && inferType(m.value, false)) ?? T.ANY)];

					case 'get':
					case 'set': {
						// An accessor pair is one field, read-only without a setter.
						const name = JS.keyName(m.key);
						if (name !== undefined) {
							if (seen.has(name))
								return [];
							seen.add(name);
						}
						return m.type === 'get'
							? [JS.Field(m.key, undefined, m.returnType ?? T.ANY, name !== undefined && !setKeys.has(name) ? ['readonly'] : undefined)]
							: [JS.Field(m.key, undefined, m.params[0]?.typeAnnotation ?? T.ANY)];
					}

					case 'method': {
						if (m.key === 'constructor')
							return [...m.params.filter(T.isParamProperty).map(p => JS.Field<Type>(typeof p.key === 'string' ? p.key : '?', undefined, p.typeAnnotation, p.modifiers)),
								JS.Method('method', m.key, {params: m.params.map(stripParam), rest: m.rest, typeParams: m.typeParams})];
						const params		= m.params.map(stripParam);
						const returnType	= m.returnType ?? (m.body ? inferReturn(m, m.body, global) : undefined);
						const expansions	= expandConstrainedGeneric(m.typeParams, params, returnType);
						if (expansions)
							return expansions.map(o => JS.Method('method', m.key, { params: o.params, rest: m.rest, returnType: o.returnType, typeParams: undefined }, undefined, m.modifiers));

						return [JS.Method('method', m.key, { params, rest: m.rest, returnType, typeParams: m.typeParams }, undefined, m.modifiers)];
					}
				}
				return [];
			}) as JS.ClassMember<any>[],
			superClass,
			ambient: true
		};
	};

	// An ambient declaration has no initializer to destructure: one simple declarator per bound name, typed `any`.
	const stripVarDeclarator = (d: JS.Var<any>, narrow: boolean): JS.Var<any>[] => typeof d.name === 'string'
		? [JS.Var(d.name, undefined, (d.typeAnnotation as Type) ?? (d.init && inferType(d.init, narrow)) ?? T.ANY)]
		: T.bindingNames(d.name).map(name => JS.Var(name, undefined, T.ANY));


	// ---- Strip bodies/initializers down to their essentials in one pass, registering owners as we go --

	const stripped = walker((stmt, process) => {
		switch (stmt.type) {
			case 'import':
				return stmt;

			case 'export':
				if (stmt.default?.type === 'identifier')
					reachable.add(stmt.default.name);
				else if (stmt.specifiers && !stmt.source)
					stmt.specifiers.forEach(s => reachable.add(s.local));
				return process(stmt);

			case 'export_decl':
				try {
					owners.exported = true;
					return process(stmt);
				} finally {
					owners.exported = false;
				}
			case 'function_decl': {
				const s = stripFunctionDecl(stmt);
				owners.add(stmt.name, s);
				return s;
			}
			case 'class_decl': {
				const s = stripClassDecl(stmt);
				owners.add(stmt.name, s);
				return s;
			}
			case 'interface_decl':
			case 'type_alias_decl':
			case 'enum_decl':
			case 'namespace_decl':
			case 'module_decl':
				owners.add(stmt.name, stmt);
				return process(stmt);	// namespace/module bodies can nest further declarations -- recurse so those get stripped too

			case 'export_assignment':
				// `export = Foo;` -- not a declaration itself, just marks whatever it names as always needed.
				reachable.add(stmt.expr.split('.')[0]);
				return stmt;

			case 'var_decl':
				for (const d of stmt.declarations) {
					for (const name of T.bindingNames(d.name))
						owners.add(name, d);
				}
				return stmt;
			default:
				return undefined;
		}
	}).module(program);

	const declRefs = (refs: Set<string>) => walker(
		undefined,
		(e, process) => {
			if (e.type === 'identifier')
				refs.add(e.name.split('.')[0]);
			return process(e);
		},
		(t, process) =>{
			if (t.type === 'ref')
				refs.add(t.name.split('.')[0]);
			return process(t);
		}
	);

	const worklist	= [...reachable];
	while (worklist.length) {
		const refs		= new Set<string>();
		const collect	= declRefs(refs);
		for (const owner of owners.get(worklist.pop()!) ?? []) {
			if ('type' in owner) {
				collect.statement(owner);
			} else {
				collect.expression(owner.init);
				collect.type(owner.typeAnnotation as Type);
			}
		}
		for (const ref of refs) {
			if (!reachable.has(ref)) {
				reachable.add(ref);
				worklist.push(ref);
			}
		}
	}

	// ---- Final rebuild: keep only what's reachable, from the already-stripped tree above -------------

	stripped.body.splice(stripped.body.findLastIndex(i => i.type === 'import') + 1, 0, ...syntheticBases);

	return walker(
		(stmt, process) => {
			switch (stmt.type) {
				case 'import':
					if (stmt.specifiers) {
						const spec = stmt.specifiers!.filter(s => reachable.has(s.local));
						if (!spec.length)
							return undefined;
						return { ...stmt, specifiers: spec};

					} else if (stmt.namespace) {
						if (!reachable.has(stmt.namespace))
							return undefined;
					}
					return stmt;

				case 'export_decl': {
					const r = process(stmt);
					return r.declaration ? r : undefined;
				}

				case 'export':
					if (stmt.default) {
						switch (stmt.default.type) {
							case 'identifier':
								return stmt;
							case 'function_decl':
							case 'class_decl':
								// Already stripped; `process` still runs its types through `onType`.
								return process(stmt);
							case 'function':
								if (stmt.default.name)
									return process({ ...stmt, default: stripFunctionDecl(JS.FunctionDecl(stmt.default.name, stmt.default))});
								//fallthrough
							default:
								// An anonymous default export: ambient declarations cannot have an inline value, so a name is synthesized, as tsc does.
								return { type: 'export', default: Identifier('_default') };
						}
					}
					return stmt;

				case 'function_decl':
				case 'class_decl':
				case 'interface_decl':
				case 'type_alias_decl':
				case 'enum_decl':
				case 'namespace_decl':
				case 'module_decl':
					return reachable.has(stmt.name) ? process(stmt) : undefined;

				case 'export_assignment':
					return stmt;

				case 'var_decl': {
					const declarations = stmt.declarations.filter(d => T.bindingNames(d.name).some(n => reachable.has(n)));
					return declarations.length
						? process({ ...stmt,
							ambient:		true,
							declarations:	declarations.flatMap(d => stripVarDeclarator(d, stmt.kind === 'const'))
						})
						: undefined;
				}

				default:
					return undefined;
			}
		},
		undefined,
		resolveTypes(global, importScope)
	).module(stripped);
}

