// A minimal Python -> wasm back end over the neutral `wasm/codegen.ts`, in the mould of `cpp/wasm-backend.ts`.
// Python is dynamically typed and this is not a checker, so the subset is the statically typed one: every
// parameter and return is annotated with `int`, `float`, `bool` or `None`, and a local takes the type of its
// first assignment and keeps it. Anything outside the subset throws `W.Error` rather than miscompiling.
//
// SCOPE: functions, scalar locals, `= += : =`, `if`/`elif`/`else`, `while`, `for .. in range(..)` (constant
// step), `break`/`continue`/`return`, the arithmetic/bitwise/comparison operators (chained comparisons too),
// value-returning `and`/`or`, `not`, `x if c else y`, direct positional calls, and `int()`/`float()`/`bool()`.
// No strings, containers, classes, closures, exceptions, keyword arguments or `print`.
//
// Where it departs from CPython:
//  * `int` is an i64, so overflow wraps or traps where Python grows a bigint.
//  * A local read on a path that never assigned it reads zero, where Python raises `UnboundLocalError`.
//  * `and`/`or` on mixed types yield the wider one (`1 and True` is the int `1`, not the bool).
//  * Comparing an `int` with a `float` converts the int, which is inexact past 2**53.
//  * `**`, `@`, shifts, and `//` and `%` on floats are refused (float `//` is not `floor(a / b)` in Python).

import * as PY from './py-parser';
import * as W from '../wasm/codegen';
import * as wasm from '@isopodlabs/binary_libs/wasm';

const I = wasm.I;

type Expr	= PY.Expr;
type Stmt	= PY.Stmt;
type FnDef	= Stmt & { type: 'funcdef' };
// 'i64' is `int`, 'f64' is `float`, 'i32' is `bool`, and 'void' is `None`.
type Num	= 'i32' | 'i64' | 'f64';
type Val	= Num | 'void';
interface Var		{ index: number; type: Num }
interface Func		{ funcIndex: number; typeIndex: number; params: Num[]; result: Val }

const NAMES: Record<Val, string> = { i32: 'bool', i64: 'int', f64: 'float', void: 'None' };
const SCALARS = new Map<string, Num>([['int', 'i64'], ['float', 'f64'], ['bool', 'i32']]);

const ARITHMETIC = new Set(['+', '-', '*', '//', '%']);

const OPS: Record<Num, Record<string, wasm.Instr>> = {
	i32: {
		'&': I.i32.and, '|': I.i32.or, '^': I.i32.xor,
		'==': I.i32.eq, '!=': I.i32.ne, '<': I.i32.lt_s, '>': I.i32.gt_s, '<=': I.i32.le_s, '>=': I.i32.ge_s,
	},
	i64: {
		'+': I.i64.add, '-': I.i64.sub, '*': I.i64.mul, '&': I.i64.and, '|': I.i64.or, '^': I.i64.xor,
		'==': I.i64.eq, '!=': I.i64.ne, '<': I.i64.lt_s, '>': I.i64.gt_s, '<=': I.i64.le_s, '>=': I.i64.ge_s,
	},
	f64: {
		'+': I.f64.add, '-': I.f64.sub, '*': I.f64.mul,
		'==': I.f64.eq, '!=': I.f64.ne, '<': I.f64.lt, '>': I.f64.gt, '<=': I.f64.le, '>=': I.f64.ge,
	},
};

const wider		= (...ts: Num[]): Num => ts.includes('f64') ? 'f64' : ts.includes('i64') ? 'i64' : 'i32';
const isNone	= (e: Expr) => e.type === 'literal' && e.value === null;

function annotated(e: Expr): Num {
	const t = e.type === 'identifier' ? SCALARS.get(e.name) : undefined;
	if (!t)
		throw new W.Error("only 'int', 'float' and 'bool' annotations are supported", e);
	return t;
}

// An `int` operand that is a compile-time constant, for a `range` step.
function constantInt(e: Expr): bigint {
	if (e.type === 'literal' && typeof e.value === 'number' && e.raw === undefined)
		return BigInt(e.value);
	if (e.type === 'unary' && e.operator === '-')
		return -constantInt(e.operand);
	throw new W.Error('a range step must be an integer literal', e);
}

export function PYtoWasm(module: { body: Stmt[] }): wasm.WasmModule {
	const out	= new wasm.WasmModule();
	const types	= new W.Types;
	const funcs	= new Map<string, Func>();

	// The one answer only the language has, taken as a parameter by the neutral helpers that need it.
	function toValType(w: W.Type): wasm.ValType {
		if (typeof w !== 'string' || w === 'void')
			throw new W.Error('only scalar values are supported');
		return W.notUnsigned(w);
	}

	// ---- declarations ---------------------------------------------------

	// Every function is declared before any body compiles, so a call can reach one defined later.
	function declare(s: Stmt) {
		if (s.type !== 'funcdef')
			throw new W.Error(`only function definitions are supported at the top level, not '${s.type}'`, s);
		if (s.decorators.length || s.is_async)
			throw new W.Error('decorators and async are not supported', s);
		if (funcs.has(s.name))
			throw new W.Error(`'${s.name}' is defined twice`, s);
		const params = s.params.map(p => {
			if (!p.name || !p.annotation || p.default || (p.kind && p.kind !== 'normal'))
				throw new W.Error(`parameter '${p.name}' must be a plain annotated name`, s);
			return { name: p.name, type: annotated(p.annotation) };
		});
		const result: Val = !s.returns || isNone(s.returns) ? 'void' : annotated(s.returns);
		const wtypes = params.map(p => p.type);
		const { funcIndex, typeIndex } = types.func(wtypes.map(type => ({ type })), result === 'void' ? [] : [result]);
		funcs.set(s.name, { funcIndex, typeIndex, params: wtypes, result });
		return { def: s, params, result };
	}

	// ---- one function ---------------------------------------------------

	function compile(def: FnDef, params: { name: string; type: Num }[], result: Val): wasm.FuncBody {
		const ctx	= new W.FunctionContext(def.name);
		const vars	= new Map<string, Var>();

		const push = (t: Num, ...instr: wasm.Instr[]): Num => (ctx.emit(...instr), t);

		// ---- variables

		// A Python local is function-wide, so nothing here opens a scope: a name assigned in a branch or loop stays visible after it.
		function bind(name: string, type: Num, node?: unknown): Var {
			const v = vars.get(name);
			if (!v) {
				const created = { index: ctx.declareLocal(name, type).index, type };
				vars.set(name, created);
				return created;
			}
			if (v.type !== type)
				throw new W.Error(`'${name}' is ${NAMES[v.type]} here, so it cannot also be ${NAMES[type]}`, node);
			return v;
		}

		const variable = (name: string, node: Expr): Var => vars.get(name) ?? fail(`unknown name '${name}'`, node);

		// Assigns the value on the stack, declaring the local with its type on first assignment.
		function store(name: string, got: Num, node?: unknown): void {
			const v = vars.get(name) ?? bind(name, got, node);
			convert(got, v.type, node);
			ctx.emit(I.local.set(v.index));
		}

		function fail(msg: string, node?: unknown): never {
			throw new W.Error(msg, node);
		}

		// ---- conversions

		// Only the implicit ones Python has: bool -> int -> float. Narrowing needs an explicit `int()`.
		function convert(got: Num, want: Num, node?: unknown): void {
			if (got === want)
				return;
			if (want === 'i64' && got === 'i32')
				ctx.emit(I.i64.extend_i32_u);
			else if (want === 'f64')
				ctx.emit(got === 'i64' ? I.f64.convert_i64_s : I.f64.convert_i32_s);
			else
				fail(`cannot convert ${NAMES[got]} to ${NAMES[want]}`, node);
		}

		function truthy(t: Num): void {
			if (t === 'i64')
				ctx.emit(I.i64.const(0n), I.i64.ne);
			else if (t === 'f64')
				ctx.emit(I.f64.const(0), I.f64.ne);
		}

		// The code `fn` emits, kept apart, so a caller that must know an operand's type before converting the one under it can splice it back in afterwards.
		function capture<T extends Val>(fn: () => T): { type: T; code: wasm.Instr[] } {
			const outer	= ctx.swapOut();
			const type	= fn();
			return { type, code: ctx.swapOut(outer) };
		}

		// ---- expressions

		function value(e: Expr): Num {
			const t = emitExpr(e);
			return t === 'void' ? fail('None has no value here', e) : t;
		}

		// Both operands, converted to their common type: the wider of the two, but at least `floor`.
		function operands(lhs: () => Num, rhs: () => Num, floor: Num): Num {
			const l = capture(lhs), r = capture(rhs);
			const t = wider(l.type, r.type, floor);
			ctx.emit(l.code);
			convert(l.type, t);
			ctx.emit(r.code);
			convert(r.type, t);
			return t;
		}

		function applyOp(op: string, t: Num): void {
			const instr = OPS[t][op];
			if (!instr)
				fail(`the operator '${op}' is not supported on ${NAMES[t]}`);
			ctx.emit(instr);
		}

		// Python's `/` refuses a zero divisor and always gives a float; wasm would give an infinity.
		function trueDivide(lhs: () => Num, rhs: () => Num): Num {
			operands(lhs, rhs, 'f64');
			return ctx.inScope(() => {
				const b = ctx.temp(`$div$${ctx.tempCounter++}`, 'f64');
				ctx.emit(I.local.tee(b), I.f64.const(0), I.f64.eq);
				ctx.emitIf(undefined, () => ctx.emit(I.unreachable));
				return push('f64', I.local.get(b), I.f64.div);
			});
		}

		// `//` rounds toward -inf and `%` takes the divisor's sign; wasm's `div_s`/`rem_s` truncate. Both are one off
		// exactly when the remainder is nonzero and its sign differs from the divisor's.
		function floorDivMod(op: '//' | '%'): void {
			ctx.inScope(() => {
				const n		= ctx.tempCounter++;
				const a		= ctx.temp(`$a$${n}`, 'i64'), b = ctx.temp(`$b$${n}`, 'i64');
				const rem	= () => [I.local.get(a), I.local.get(b), I.i64.rem_s];
				const off	= () => [...rem(), I.i64.const(0n), I.i64.ne, ...rem(), I.local.get(b), I.i64.xor, I.i64.const(0n), I.i64.lt_s, I.i32.and, I.i64.extend_i32_u];
				ctx.emit(I.local.set(b), I.local.set(a));
				if (op === '//')
					ctx.emit(I.local.get(a), I.local.get(b), I.i64.div_s, off(), I.i64.sub);
				else
					ctx.emit(rem(), off(), I.local.get(b), I.i64.mul, I.i64.add);
			});
		}

		function arithmetic(op: string, lhs: () => Num, rhs: () => Num): Num {
			if (op === '/')
				return trueDivide(lhs, rhs);
			// A bool is an int under arithmetic, but `True & False` is still a bool.
			const t = operands(lhs, rhs, ARITHMETIC.has(op) ? 'i64' : 'i32');
			if (t === 'i64' && (op === '//' || op === '%'))
				floorDivMod(op);
			else
				applyOp(op, t);
			return t;
		}

		// `a and b` is `b` when `a` is truthy, else `a` itself -- so the left value is kept, not just its truth.
		function logical(op: '&&' | '||', left: Expr, right: Expr): Num {
			const lt = value(left);
			return ctx.inScope(() => {
				const a = ctx.temp(`$left$${ctx.tempCounter++}`, lt);
				ctx.emit(I.local.tee(a));
				truthy(lt);
				const r			= capture(() => value(right));
				const t			= wider(lt, r.type);
				const keepLeft	= () => (ctx.emit(I.local.get(a)), convert(lt, t));
				const takeRight	= () => (ctx.emit(r.code), convert(r.type, t));
				ctx.emitIf(t, op === '&&' ? takeRight : keepLeft, op === '&&' ? keepLeft : takeRight);
				return t;
			});
		}

		// `a < b < c` is `a < b and b < c` with `b` evaluated once, and nothing after a false link evaluated at all.
		function compare(e: PY.Compare): Num {
			const last = e.ops.length - 1;
			const link = (i: number, lhs: () => Num): void => {
				let next = lhs;
				const rhs = () => {
					const t = value(e.comparators[i]);
					if (i < last) {
						const tmp = ctx.temp(`$cmp$${ctx.tempCounter++}`, t);
						ctx.emit(I.local.tee(tmp));
						next = () => push(t, I.local.get(tmp));
					}
					return t;
				};
				applyOp(e.ops[i], operands(lhs, rhs, 'i32'));
				if (i < last)
					ctx.emitIf('i32', () => link(i + 1, next), () => ctx.emit(I.i32.const(0)));
			};
			ctx.inScope(() => link(0, () => value(e.left)));
			return 'i32';
		}

		function unary(op: PY.unaryOps, operand: Expr): Num {
			const t = value(operand);
			if (op === '!') {
				truthy(t);
				return push('i32', I.i32.eqz);
			}
			if (t === 'f64' && op === '~')
				fail("'~' is not supported on float", operand);
			// A bool is an int under `+`, `-` and `~`.
			const n = wider(t, 'i64');
			convert(t, n);
			switch (op) {
				case '+':	return n;
				case '-':	return n === 'f64' ? push(n, I.f64.neg) : push(n, I.i64.const(-1n), I.i64.mul);
				default:	return push(n, I.i64.const(-1n), I.i64.xor);
			}
		}

		function toInt(t: Num): Num {
			if (t === 'f64')
				ctx.emit(I.i64.trunc_f64_s);
			else
				convert(t, 'i64');
			return 'i64';
		}

		// `int(x)`, `float(x)` and `bool(x)`: the explicit conversions, which are how a float narrows to an int.
		function builtin(name: string, args: Expr[], node: Expr): Num | undefined {
			if (name !== 'int' && name !== 'float' && name !== 'bool')
				return undefined;
			if (args.length !== 1)
				fail(`${name}() takes exactly one argument`, node);
			const t = value(args[0]);
			if (name === 'int')
				return toInt(t);
			if (name === 'float') {
				convert(t, 'f64');
				return 'f64';
			}
			truthy(t);
			return 'i32';
		}

		function call(e: PY.Call): Val {
			if (e.callee.type !== 'identifier')
				fail('only a direct call by name is supported', e);
			const args = e.arguments.map(a => a.kind === 'pos' ? a.value : fail('only positional arguments are supported', e));
			const fn = funcs.get(e.callee.name);
			if (!fn)
				return builtin(e.callee.name, args, e) ?? fail(`unknown function '${e.callee.name}'`, e);
			if (fn.params.length !== args.length)
				fail(`'${e.callee.name}' takes ${fn.params.length} arguments, not ${args.length}`, e);
			args.forEach((a, i) => convert(value(a), fn.params[i], a));
			ctx.emit(I.call(fn.funcIndex));
			return fn.result;
		}

		function conditional(e: PY.Conditional): Num {
			truthy(value(e.test));
			const c = capture(() => value(e.consequent)), a = capture(() => value(e.alternate));
			const t = wider(c.type, a.type);
			ctx.emitIf(t, () => (ctx.emit(c.code), convert(c.type, t)), () => (ctx.emit(a.code), convert(a.type, t)));
			return t;
		}

		function literal(e: Extract<Expr, { type: 'literal' }>): Val {
			const v = e.value;
			if (typeof v === 'boolean')
				return push('i32', I.i32.const(+v));
			// The parser records a float's spelling in `raw`, since `1.0` and `1` share a value.
			if (typeof v === 'number' && e.raw !== undefined)
				return push('f64', I.f64.const(v));
			if (typeof v === 'number' || typeof v === 'bigint') {
				const n = BigInt(v);
				return n === BigInt.asIntN(64, n) ? push('i64', I.i64.const(n)) : fail(`the integer ${n} does not fit in 64 bits`, e);
			}
			return v === null ? 'void' : fail('only numeric and boolean literals are supported', e);
		}

		function emitExpr(e: Expr): Val {
			switch (e.type) {
				case 'literal':		return literal(e);
				case 'identifier':	{ const v = variable(e.name, e); return push(v.type, I.local.get(v.index)); }
				case 'unary':		return unary(e.operator, e.operand);
				case 'compare':		return compare(e);
				case 'conditional':	return conditional(e);
				case 'call':		return call(e);
				case 'binary':
					return e.operator === '&&' || e.operator === '||'
						? logical(e.operator, e.left, e.right)
						: arithmetic(e.operator, () => value(e.left), () => value(e.right));
			}
			return fail(`unsupported expression '${e.type}'`, e);
		}

		// ---- statements

		const emitBody = (body: Stmt[]) => body.forEach(emitStmt);

		// The counter, the limit and the step of `for name in range(..)`; Python evaluates them once, before the first pass.
		function emitFor(s: Stmt & { type: 'for' }): void {
			const n		= ctx.tempCounter++;
			const args	= s.iter.type === 'call' && s.iter.callee.type === 'identifier' && s.iter.callee.name === 'range' && s.iter.arguments.every(a => a.kind === 'pos')
				? s.iter.arguments.map(a => a.value) : [];
			if (s.target.type !== 'identifier' || s.orelse.length || s.is_async || args.length < 1 || args.length > 3)
				fail("only 'for name in range(stop | start, stop [, step])' is supported", s);
			const step	= args[2] ? constantInt(args[2]) : 1n;
			if (step === 0n)
				fail('a range step cannot be zero', args[2]);
			const i		= ctx.temp(`$i$${n}`, 'i64'), stop = ctx.temp(`$stop$${n}`, 'i64');
			const int	= (e: Expr) => convert(value(e), 'i64', e);
			if (args.length > 1)
				int(args[0]);
			else
				ctx.emit(I.i64.const(0n));
			ctx.emit(I.local.set(i));
			int(args[args.length > 1 ? 1 : 0]);
			ctx.emit(I.local.set(stop));
			const name = s.target.name;
			bind(name, 'i64', s.target);
			ctx.emitLoop(() => {
				ctx.emit(I.local.get(i), I.local.get(stop), step > 0n ? I.i64.lt_s : I.i64.gt_s, I.i32.eqz, I.br_if(1), I.local.get(i));
				store(name, 'i64', s.target);
				ctx.emitContinueBlock(() => emitBody(s.body));
				ctx.emit(I.local.get(i), I.i64.const(step), I.i64.add, I.local.set(i), I.br(0));
			});
		}

		function emitStmt(s: Stmt): void {
			switch (s.type) {
				case 'pass':
					return;

				case 'expression':
					if (emitExpr(s.expression) !== 'void')
						ctx.emit(I.drop);
					return;

				case 'assign': {
					const t = value(s.value);
					const names = s.targets.map(x => x.type === 'identifier' ? x.name : fail('only plain names can be assigned to', x));
					if (names.length === 1)
						return store(names[0], t, s);
					// The value is stored more than once, and each target may convert it differently.
					const tmp = ctx.temp(`$assign$${ctx.tempCounter++}`, t);
					ctx.emit(I.local.set(tmp));
					names.forEach(name => (ctx.emit(I.local.get(tmp)), store(name, t, s)));
					return;
				}

				case 'augassign': {
					if (s.target.type !== 'identifier')
						fail('only a plain name can be assigned to', s.target);
					const name	= s.target.name, v = variable(name, s.target);
					const t		= arithmetic(s.op.slice(0, -1), () => push(v.type, I.local.get(v.index)), () => value(s.value));
					return store(name, t, s);
				}

				case 'annassign': {
					if (s.target.type !== 'identifier')
						fail('only a plain name can be annotated', s.target);
					const type = annotated(s.annotation);
					if (!s.value) {
						bind(s.target.name, type, s);
						return;
					}
					const t = value(s.value);
					bind(s.target.name, type, s);
					return store(s.target.name, t, s);
				}

				case 'return': {
					const t = s.argument ? emitExpr(s.argument) : 'void';
					if (result === 'void' && t !== 'void')
						fail(`'${def.name}' is not annotated to return a value`, s);
					if (result !== 'void')
						convert(t === 'void' ? fail(`'${def.name}' must return ${NAMES[result]}`, s) : t, result, s);
					ctx.emit(I.return);
					return;
				}

				case 'if':
					truthy(value(s.test));
					ctx.emitIf(undefined, () => emitBody(s.consequent), () => emitBody(s.alternate ?? []));
					return;

				case 'while':
					if (s.orelse?.length)
						fail("'while ... else' is not supported", s);
					// `emitLoop` owns the block+loop and registers both branch targets: `br_if(1)` leaves it, `br(0)` restarts it.
					ctx.emitLoop(() => {
						truthy(value(s.test));
						ctx.emit(I.i32.eqz, I.br_if(1));
						emitBody(s.body);
						ctx.emit(I.br(0));
					});
					return;

				case 'for':
					return emitFor(s);

				case 'break':
					if (!ctx.breakTargets.length)
						fail("'break' outside of a loop", s);
					return ctx.emitBreak();

				case 'continue':
					if (!ctx.continueTargets.length)
						fail("'continue' outside of a loop", s);
					return ctx.emitContinue();
			}
			fail(`unsupported statement '${s.type}'`, s);
		}

		params.forEach(p => bind(p.name, p.type));
		W.withCatch(() => emitBody(def.body), def.name)();
		// A non-void body need not end in a top-level `return`, and a trailing `unreachable` is dead wherever one already covers every path.
		ctx.emitTrailingUnreachable(result);
		return ctx.toFuncBody(params.length, toValType);
	}

	// ---- drive ----------------------------------------------------------

	const decls = module.body.map(declare);

	out.code			= decls.map(d => compile(d.def, d.params, d.result));
	out.types			= { types, groupSizes: types.groupSizes(new Set()) };
	out.functionTypes	= decls.map(d => funcs.get(d.def.name)!.typeIndex);
	out.exports			= decls.map(d => ({ name: d.def.name, kind: 'func' as const, index: funcs.get(d.def.name)!.funcIndex }));
	return out;
}
