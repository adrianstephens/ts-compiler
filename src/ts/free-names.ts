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

// The names `body` reads that `bound` does not cover, `this` included, in first-use order. A nested closure contributes
// what it reads from outside itself; an object literal's method reads its own `this`.
export function freeIn(body: Stmt[] | Expr, bound: ReadonlySet<string> = new Set()): Set<string> {
	const free	= new Set<string>();
	const add	= (names: Iterable<string>) => {
		for (const n of names)
			if (!bound.has(n))
				free.add(n);
	};
	walkerB(
		(s, process) => s.type === 'function_decl' ? (add(closureFree(s)), false) : s.type === 'class_decl' ? (add(classFree(s)), false) : process(s),
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
	).body(body);
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
		const bound	= ownBoundNames(paramNames(fn.params, fn.rest), body, fn.name);
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
	const bound = ownBoundNames([], body);
	for (const s of body) {
		const d = s.type === 'export_decl' ? s.declaration : s;
		if (d.type === 'import')
			[d.default, d.namespace, ...(d.specifiers ?? []).map(x => x.local)].forEach(n => n && bound.add(n));
		else if (d.type === 'class_decl' || d.type === 'enum_decl' || d.type === 'namespace_decl')
			bound.add(d.name);
	}
	return freeIn(body, bound);
}
