import * as TS from './ts-parser';
import * as JS from './js-parser';
import * as T from './type-utils';
import { walkerB } from './walker';

// ===================================================================
//  Free-variable analysis: what a closure, or a module, reads from outside itself
// ===================================================================

type Expr	= TS.Expr;
type Type	= TS.Type;
type Stmt	= TS.Stmt;

export function paramNames(params: JS.Param<Type>[], rest?: JS.Rest<Type>): string[] {
	const names = params.flatMap(p => T.bindingNames(p.key));
	return rest ? [...names, ...T.bindingNames(rest.key)] : names;
}

// Every name body binds directly (own params + var_decls), not descending into nested arrow/function/class bodies.
export function ownBoundNames(names: string[], body: Stmt[] | Expr, selfName?: string): Set<string> {
	const bound = new Set(names);
	if (selfName)
		bound.add(selfName);
	// A `for`'s own `let i` reaches the `var_decl` case too: the walker routes `init` through the statement walk.
	walkerB(
		(s, process) => {
			// A nested function or class binds its own name here, but its body is a closure boundary of its own.
			if (s.type === 'function_decl' || s.type === 'class_decl') {
				bound.add(s.name);
				return false;
			}
			if (s.type === 'var_decl') {
				for (const d of s.declarations)
					T.bindingNames(d.name).forEach(n => bound.add(n));
			}
			if (s.type === 'try') {
				for (const h of s.handlers)
					if (h.param)
						T.bindingNames(h.param).forEach(n => bound.add(n));
			}
			return process(s);
		},
		// An object literal reaches statements only through its methods' bodies, each a closure boundary.
		(e, process) => (e.type === 'arrow' || e.type === 'function' || e.type === 'object' || e.type === 'class') ? false : process(e)
	).body(body);
	return bound;
}

export type Closure = { type?: string; params: JS.Param<Type>[]; rest?: JS.Rest<Type>; body?: Stmt[] | Expr; name?: string };

// The names a statement list binds for itself, as JS scopes them: `let`/`const`, classes and function declarations (`var` is the function's).
function blockNames(stmts: Stmt[]): string[] {
	return stmts.flatMap(s => {
		const d = s.type === 'export_decl' ? s.declaration : s;
		return d.type === 'var_decl' && d.kind !== 'var' ? d.declarations.flatMap(x => T.bindingNames(x.name))
			: (d.type === 'function_decl' || d.type === 'class_decl') && d.name ? [d.name] : [];
	});
}

// Every `var` a body declares at any depth short of a nested closure: function-scoped.
function varNames(body: Stmt[] | Expr): string[] {
	const out: string[] = [];
	walkerB(
		(s, process) => s.type === 'function_decl' || s.type === 'class_decl' ? false
			: (s.type === 'var_decl' && s.kind === 'var' && s.declarations.forEach(d => out.push(...T.bindingNames(d.name))), process(s)),
		(e, process) => e.type === 'arrow' || e.type === 'function' || e.type === 'object' || e.type === 'class' ? false : process(e)
	).body(body);
	return out;
}

// The names `body` reads that `bound` does not cover, `this` included, in first-use order. A nested closure contributes what it reads from
// outside itself; an object literal's method reads its own `this`. Scoped as JS is: a block, a `for`'s own `let`, a catch parameter and a
// `switch`'s cases bind their names over their own extent only.
export function freeIn(body: Stmt[] | Expr, bound: ReadonlySet<string> = new Set()): Set<string> {
	const free		= new Set<string>();
	const entered	= new WeakSet<Stmt>();
	const scan = (x: Stmt[] | Expr, outer: ReadonlySet<string>): void => {
		const inner	= Array.isArray(x) ? new Set([...outer, ...blockNames(x)]) : outer;
		const with_	= (names: string[]) => new Set([...inner, ...names]);
		const add	= (names: Iterable<string>) => {
			for (const n of names)
				if (!inner.has(n))
					free.add(n);
		};
		const w = walkerB(
			(s, process) => {
				switch (s.type) {
					case 'function_decl':	return add(closureFree(s)), false;
					case 'class_decl':		return add(classFree(s)), false;
					case 'block':			return scan(s.body, inner), false;
					case 'try':
						scan(s.body, inner);
						s.handlers.forEach(h => scan(h.body, with_(h.param ? T.bindingNames(h.param) : [])));
						if (s.finalizer)
							scan(s.finalizer, inner);
						return false;
					case 'switch': {
						const cases = with_(blockNames(s.cases.flatMap(c => c.consequent)));
						scan(s.discriminant, inner);
						s.cases.forEach(c => (c.test && scan(c.test, cases), scan(c.consequent, cases)));
						return false;
					}
					case 'for': {
						// Its own `let`/`const` covers the whole loop; walked once more under it.
						const names = s.init?.type === 'var_decl' && s.init.kind !== 'var' ? s.init.declarations.flatMap(d => T.bindingNames(d.name)) : [];
						if (!names.length || entered.has(s))
							return process(s);
						entered.add(s);
						return scan([s], with_(names)), false;
					}
				}
				return process(s);
			},
			(e, process) => {
				if (e.type === 'identifier' || e.type === 'this')
					add([e.type === 'this' ? 'this' : e.name]);
				else if (e.type === 'arrow' || e.type === 'function')
					add(closureFree(e));
				else if (e.type === 'class')
					add(classFree(e));
				else if (e.type !== 'object')
					return process(e);
				else
					for (const p of e.properties)
						add(p.type === 'spread' ? freeIn(p.operand)
							: p.type !== 'field' ? [...closureFree(p)].filter(n => n !== 'this')
							: [...typeof p.key === 'object' ? freeIn(p.key.computed) : [], ...p.value ? freeIn(p.value) : []]);
				return false;
			}
		);
		if (Array.isArray(x))
			w.statements(x);
		else
			w.expression(x);
	};
	scan(body, bound);
	return free;
}

// Whether a closure nested in `body` (an arrow, a function, a method) reads `name` from outside itself.
function nestedReads(body: Stmt[] | Expr, name: string): boolean {
	let found = false;
	walkerB(
		(s, process) => s.type === 'function_decl' ? (found ||= closureFree(s).has(name), false) : process(s),
		(e, process) => {
			if (e.type === 'arrow' || e.type === 'function')
				return (found ||= closureFree(e).has(name), false);
			if (e.type === 'object')
				for (const p of e.properties)
					if (p.type !== 'spread' && p.type !== 'field')
						found ||= closureFree(p).has(name);
			return process(e);
		}
	).body(body);
	return found;
}

// What a closure reads from outside itself: its body's free names and its parameter defaults' (a default runs in the callee).
const closureFrees = new WeakMap<Closure, Set<string>>();
export function closureFree(fn: Closure): Set<string> {
	let free = closureFrees.get(fn);
	if (!free) {
		const body	= fn.body ?? [];
		const bound	= new Set([...paramNames(fn.params, fn.rest), ...varNames(body), ...fn.name ? [fn.name] : []]);
		free		= new Set([body, ...fn.params.flatMap(p => p.default ? [p.default] : [])].flatMap(b => [...freeIn(b, bound)]));
		closureFrees.set(fn, free);
		// A function declaration read from a closure nested in it (not a direct self-call, which `selfCall` makes) is its enclosing scope's binding.
		if (fn.type === 'function_decl' && fn.name && nestedReads(body, fn.name))
			free.add(fn.name);
	}
	return free;
}

// What a class reads from outside itself: its heritage and its members', each method a closure over its own `this`.
function classFree(c: JS.Class<Type, TS.ClassMember>): string[] {
	const own = (m: TS.ClassMember): Iterable<string> =>
		m.type === 'method'			? [...typeof m.key === 'object' ? freeIn(m.key.computed) : [], ...closureFree(m)]
		: m.type === 'field'		? [...typeof m.key === 'object' ? freeIn(m.key.computed) : [], ...m.value ? freeIn(m.value) : []]
		: m.type === 'static_block'	? freeIn(m.body)
		: [];
	return [...c.superClass ? freeIn(c.superClass) : [], ...c.body.flatMap(m => [...own(m)])].filter(n => n !== 'this' && n !== c.name);
}

// The names a module reads that it neither declares nor imports: what only a global (the lib's, or the host's) can supply.
export function moduleFree(body: Stmt[]): Set<string> {
	const bound = new Set(varNames(body));
	for (const s of body) {
		const d = s.type === 'export_decl' ? s.declaration : s;
		if (d.type === 'import')
			[d.default, d.namespace, ...(d.specifiers ?? []).map(x => x.local)].forEach(n => n && bound.add(n));
		else if (d.type === 'class_decl' || d.type === 'enum_decl' || d.type === 'namespace_decl')
			bound.add(d.name);
	}
	return freeIn(body, bound);
}
