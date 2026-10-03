// ===================================================================
//  The Python half of the language-neutral VSDG.
// ===================================================================
// The same three pieces as ts/vsdg.ts (`PYDialect`, `PYBuilder`, `PYEmitter`, printed by py/printer.ts) and the pipeline entry points.
// Where Python differs: assignment is a STATEMENT (a value only as `(x := v)`); the FIRST assignment to a name is its declaration (`bindTarget`);
//   bodies are statement ARRAYS, passed straight through; no switch, do-while, postfix `++/--`, destructuring, or `try` without `except`.
// Not modelled, printed verbatim: `with`, `del`, `assert`, `global`/`nonlocal`, loop `else:`, several `except`s, `try/else`, class bases past
//   the first, decorators, comprehensions' loop structure, parameter defaults.

import * as PY from './py-parser';
import { printer as PYPrinter } from './printer';
import { Identifier, Literal, Assign, If, Throw } from '@isopodlabs/tison/ast';
import { walkerB, calcUnary, calcBinary, calcCompare } from './walker';
import {
	Dialect, VSDGBuilder, Emitter, Recurse, ParamSlot,
	Node, NodeOf, NodeType, NodeId, ClassInfo, Scope, VSDG, BlockTree,
	connectValue, slotName,
	optimize, optimizeStructuralCSE as structuralCSE
} from '../vsdg';

type Expr	= PY.Expr;
type Stmt	= PY.Stmt;
type N		= Node<Expr, Stmt, Expr>;
type NOf<K extends NodeType> = NodeOf<Expr, Stmt, Expr, K>;

// ===================================================================
//  Dialect
// ===================================================================

let printerInstance: ReturnType<typeof PYPrinter> | undefined;
const pyPrinter = () => (printerInstance ??= PYPrinter());

function MaybeLiteral(v: any): Expr | undefined {
	return v === undefined ? undefined : Literal(v);
}
const pyDialect: Dialect<Expr, Stmt, Expr> = {
	identifierName(e: Expr) {
		return e.type === 'identifier' ? e.name : undefined;
	},
	identifier(name: string) {
		return Identifier(name);
	},
	exprKey(e: Expr) {
		return pyPrinter().expression(e);
	},
	stmtKey(s: Stmt) {
		return pyPrinter().statement(s);
	},
	isCSEUnsafe(node: N): boolean {
		// A `list`/`set`/`dict`/comprehension is a fresh identity per evaluation, a `tuple` at least for `is`; an `index`/`member` read may see a mutation.
		return node.type === 'floating' && ['list', 'set', 'dict', 'tuple', 'index', 'listcomp', 'setcomp', 'dictcomp', 'genexp'].includes(node.expr.type);
	},
	foldable(e) {
		return	e.type === 'binary' ? 2
			:	e.type === 'unary'	? 1
			:	e.type === 'compare' && e.ops.length === 1 ? 2	// A NON-CHAINED comparison (`a == b`) folds like a binary; `a < b < c` doesn't (it can't be spelled as one pair of operands).
			:	0;
	},
	fold(e, ops) {
		return	e.type === 'binary' ? MaybeLiteral(calcBinary(e.operator, ops[0], ops[1]))
			:	e.type === 'unary'	? MaybeLiteral(calcUnary(e.operator, ops[0]))
			:	e.type === 'compare' && e.ops.length === 1 ? MaybeLiteral(calcCompare(e.ops[0], ops[0], ops[1]))
			:	undefined;
	},
	// A plain literal's value is its `value`; an f-string has interpolation holes and is NOT a constant.
	literalValue(e) {
		return	e.type === 'imaginary' ? e.value
			:	e.type === 'literal' && !Array.isArray(e.value) ? e.value
			:	undefined;
	},
	// Python falsiness of a constant: `0`/`''`/`False` coincide with js's, and the kinds that differ are never constants.
	truthy(value) {
		return !!value;
	},
	isCalleeEdge(consumer: N, port: number) {
		const v = consumer.type === 'effect' && consumer.expr;
		return !!v && v.type === 'call' && port === v.arguments.length + 1;
	}
};

// ===================================================================
//  Lowering
// ===================================================================

// This language's parameter list as the core's slots; `/` and a bare `*` are markers, not parameters.
function paramSlots(params: readonly PY.Param[] | undefined): ParamSlot[] | undefined {
	if (!params)
		return undefined;
	const slots: ParamSlot[] = [];
	for (const p of params)
		if (p.name !== undefined && p.kind !== 'slash' && p.kind !== 'stardelim')
			slots.push({ name: p.name });
	return slots;
}

function posCall(callee: string, args: Expr[]): Expr {
	return { type: 'call', callee: Identifier(callee), arguments: args.map(value => ({ kind: 'pos', value })) } as Expr;
}

// An f-string's interpolations, the only nested AST a literal carries: builder and emitter walk them in the same order.
function forEachFStringField(parts: readonly PY.FStringPart[], fn: (e: Expr, port: number) => void): void {
	let port = 0;
	for (const part of parts) {
		if (!part.field)
			continue;
		fn(part.field.expr, port++);
		for (const spec of part.field.spec ?? [])
			if (typeof spec !== 'string')
				fn(spec, port++);
	}
}

function rebuildFString(parts: readonly PY.FStringPart[], resolve: (port: number) => Expr): PY.FStringPart[] {
	let port = 0;
	return parts.map(part => {
		if (!part.field)
			return part;
		const expr	= resolve(port++);
		const spec	= part.field.spec?.map(s => typeof s === 'string' ? s : resolve(port++));
		return { ...part, field: { ...part.field, expr, spec } };
	});
}

export class PYBuilder extends VSDGBuilder<Expr, Stmt, Expr> {
	constructor() { super(pyDialect); }

	build(ast: readonly Stmt[]) {
		walkerB(
			(s, process, recurse) => this.lowerStatement(s, process, recurse),
			(e, process, recurse) => this.lowerExpression(e, process, recurse)
		).statements(ast);
	}

	lowerStatement(s: Stmt, process: (s: Stmt) => boolean, recurse: Recurse<Expr, Stmt>): boolean {
		switch (s.type) {
			case 'funcdef': {
				const fn = this.buildFunctionBody(recurse, paramSlots(s.params), s.body);
				fn.stmt = s;
				this.end = fn;
				return false;
			}
			case 'classdef': {
				const node = this.makeNode({ type: 'class_decl', stmt: s });
				node.classInfo = this.buildClass(recurse, node, s);
				this.connectEnd(node);
				return false;
			}

			case 'return': {
				// As TS's return: the marker carries its value at port 1; `exited` makes an enclosing `if` build a real gamma.
				if (s.argument)
					recurse.expression(s.argument);
				const marker = this.makeMarker('EARLY_RETURN_MARKER');
				this.connectEnd(marker);
				if (s.argument)
					connectValue(this.getExprNode(s.argument), 0, marker, 1);
				this.exited = true;
				return false;
			}
			case 'throw': {
				// A bare `raise` re-raises with no value, and `raise X from Y` has an unmodelled second expression: both verbatim.
				if (!s.argument || s.cause) {
					console.log(`not handling raise with ${!s.argument ? 'no argument' : 'a cause'}`);
					return this.lowerVerbatim(s, process);
				}
				recurse.expression(s.argument);
				const marker = this.makeMarker('THROW_MARKER');
				this.connectEnd(marker);
				connectValue(this.getExprNode(s.argument), 0, marker, 1);
				this.exited = true;
				return false;
			}
			case 'break':
				this.connectEnd(this.makeMarker('BREAK_MARKER'));
				this.exited = true;
				this.brokeOut = true;
				return false;
			case 'continue':
				this.connectEnd(this.makeMarker('CONTINUE_MARKER'));
				this.exited = true;
				return false;

			case 'assign': {
				// `a = b = value` walks the value ONCE and binds every target to it.
				recurse.expression(s.value);
				const value = this.getExprNode(s.value);
				for (const target of s.targets)
					recurse.expression(target);
				for (const target of s.targets)
					this.bindTarget(target, s.value, value, undefined, undefined);
				return false;
			}
			case 'augassign': {
				// `op` arrives as `+=`; the converged Assign stores the BASE operator (`+`).
				recurse.expression(s.target);
				recurse.expression(s.value);
				this.bindTarget(s.target, s.value, this.getExprNode(s.value), s.op.slice(0, -1) as PY.binaryOps, undefined);
				return false;
			}
			case 'annassign': {
				// A bare `x: int` declares a name with no value: nothing to bind or elide, so verbatim.
				if (s.value === undefined || s.target.type !== 'identifier') {
					this.lowerVerbatim(s, process);
					return false;
				}
				recurse.expression(s.value);
				this.bindTarget(s.target, s.value, this.getExprNode(s.value), undefined, s.annotation);
				return false;
			}

			case 'if': {
				recurse.expression(s.test);
				const test		= this.getExprNode(s.test);
				const parent	= this.getState();
				// Each branch gets its own scope (Python has no block scoping): reconcileVariables merges the two branches' BINDINGS.
				const trueState		= this.walkBranch(parent, () => { for (const st of s.consequent) recurse.statement(st); });
				const falseState	= this.walkBranch(parent, () => { for (const st of s.alternate ?? []) recurse.statement(st); });
				this.mergeState(parent, test, trueState, falseState);
				this.reconcileVariables(parent, test, trueState, falseState);
				return false;
			}
			case 'while': {
				// A loop's `else:` runs iff it was not broken out of: an exit path the graph has no anchor for.
				if (s.orelse?.length) {
					console.log(`not handling while-else`);
					return this.lowerVerbatim(s, process);
				}
				this.buildLoop(recurse, s.test, () => { for (const st of s.body) recurse.statement(st); }, false);
				return false;
			}
			case 'for': {
				if (s.is_async || s.orelse?.length) {
					console.log(`not handling ${s.is_async ? 'async ' : ''}for-else`);
					return this.lowerVerbatim(s, process);
				}
				this.lowerFor(recurse, s);
				return false;
			}

			case 'try': {
				// One typed handler and no `else:`, as TS's try/catch plus the matched type; anything more stays verbatim.
				const handler = s.handlers[0];
				if (!handler || s.handlers.length > 1 || handler.star || s.orelse?.length) {
					console.log(`not handling ${s.handlers.length > 1 ? 'multiple except clauses' : 'try with an else clause'}`);
					return this.lowerVerbatim(s, process);
				}
				const parent = this.getState();

				// Each branch gets its own start marker after the shared predecessor, or a branch's first anchor would share `except`'s.
				const startMarker = (pred: N, tag: 'TRY_START' | 'CATCH_START' | 'FINALLY_START') => {
					const marker = this.makeMarker(tag);
					connectValue(pred, 0, marker, 0);
					return marker;
				};

				// Two scopes per branch, as in TS: an outer one the reconciliation reads, an inner one flushed first.
				this.setState(new Scope(parent.scope), startMarker(parent.end, 'TRY_START'));
				this.scope = new Scope(this.scope);
				for (const stmt of s.body)
					recurse.statement(stmt);
				this.scope = this.scope.closeAndFlush()!;
				const tryState = this.getState();

				this.setState(new Scope(parent.scope), startMarker(parent.end, 'CATCH_START'));
				this.scope = new Scope(this.scope);
				if (handler.param !== undefined)
					this.scope.create(handler.param, this.makeNode({type: 'var', name: handler.param}));
				for (const stmt of handler.body)
					recurse.statement(stmt);
				this.scope = this.scope.closeAndFlush()!;
				const catchState = this.getState();

				// Never skipped like an `if`'s gamma: try/except is observable syntax.
				const exc = this.makeNode({ type: 'except' });
				if (handler.param !== undefined)
					exc.catchParam = handler.param;
				if (handler.type) {
					// Threaded so a referenced name keeps a reader; the node is a side channel (`collectProtectedNodeIds`), resolved at print time.
					recurse.expression(handler.type);
					exc.handlerTypeNodeId = this.getExprNode(handler.type).id;
				}
				connectValue(parent.end, 0, exc, 0);
				connectValue(tryState.end, 0, exc, 1);
				connectValue(catchState.end, 0, exc, 2);
				this.end = exc;

				// Per-variable merges as in TS: no binding cleared, each branch force-printing its own `x = ...`, the merge connecting both.
				this.scope = parent.scope;
				const diverged = new Set([...tryState.scope.bindings.keys(), ...catchState.scope.bindings.keys()]);
				for (const name of diverged) {
					const tryVal	= tryState.scope.get(name)!;
					const catchVal	= catchState.scope.get(name)!;
					if (tryVal !== catchVal) {
						if (slotName(tryVal) === name)
							tryVal.forcedPrint = true;
						if (slotName(catchVal) === name)
							catchVal.forcedPrint = true;

						const namedExc = this.makeNode({ type: 'exceptValue', name });
						connectValue(tryVal, 0, namedExc, 0);
						connectValue(catchVal, 0, namedExc, 1);
						this.scope.set(name, namedExc);
					}
				}

				// `finally` runs after the merge, walked as ordinary code and reconstructed as a real `finally` clause.
				let finallyExited = false;
				let finallyBrokeOut = false;
				if (s.finalizer?.length) {
					this.end		= startMarker(exc, 'FINALLY_START');
					this.exited		= false;
					this.brokeOut	= false;
					this.scope		= new Scope(this.scope);
					for (const stmt of s.finalizer)
						recurse.statement(stmt);
					this.scope			= this.scope.closeAndFlush()!;
					finallyExited		= this.exited;
					finallyBrokeOut		= this.brokeOut;
					connectValue(this.end, 0, exc, 3);
					this.end = exc;
				}
				this.exited = finallyExited || (tryState.exited && catchState.exited);
				this.brokeOut = s.finalizer?.length
					? finallyBrokeOut
					: (tryState.exited && catchState.exited && tryState.brokeOut && catchState.brokeOut);
				return false;
			}

			case 'import':
			case 'importfrom': {
				// Each bound name gets a declKind-less 'var' node, anchored after the verbatim import so GCM never reads it earlier.
				process(s);
				this.connectEnd(this.makeNode({type: 'passthru', stmt: s}));
				const names = s.names === '*' ? [] : s.names;
				for (const alias of names) {
					const varNode = this.makeNode({type: 'var', name: alias.asname ?? alias.name});
					this.threadMutation(varNode);
					this.scope.create(alias.asname ?? alias.name, varNode);
				}
				return false;
			}

			case 'expression':
				// A bare literal statement is a docstring (or a directive): verbatim.
				if (s.expression.type === 'literal')
					return this.lowerVerbatim(s, process);
				break;

			default:
				// An unmodelled construct (`with`, `del`, `assert`, `pass`, `global`/`nonlocal`) prints verbatim.
				this.lowerVerbatim(s, process);
				return false;
		}
		return process(s);
	}

	// One assignment target as a binding: Python spells a declaration (`var`) and a rebinding (`mutation`) alike, so whether the name is already
	// bound decides; a first assignment creates a function local.
	private bindTarget(target: Expr, valueExpr: Expr, value: N, operator: PY.binaryOps | undefined, annotation: Expr | undefined) {
		if (target.type === 'identifier' && operator === undefined) {
			const fresh = this.scope.get(target.name) === undefined;
			if (fresh) {
				// A declaration: an annassign's annotation travels to the print site.
				const varNode = this.makeNode({ type: 'var', name: target.name });
				connectValue(value, 0, varNode, 0);
				varNode.declKind		= annotation ? 'annotate' : 'assign';
				varNode.typeAnnotation	= annotation;
				this.bindVar(varNode);
				return;
			}
		}

		// A reassignment, or a member/index target, on the converged Assign shape with its base operator.
		const node = this.makeNode({ type: 'mutation', expr: Assign<Expr, PY.binaryOps>(target, valueExpr, operator) as unknown as Expr });
		node.plainAssign = operator === undefined;
		connectValue(this.getExprNode(target), 0, node, 0);
		connectValue(value, 0, node, 1);
		if (target.type === 'identifier') {
			// Assigning a name captured from an enclosing function escapes it: no same-region consumer count decides (`isLocalToCurrentFunction`).
			if (!this.scope.isLocalToCurrentFunction(target.name))
				node.forcedPrint = true;
			this.rebindVar(target.name, node);
		} else {
			// A member/index target mutates outside this pass's scope tracking: it prints whatever its consumer count.
			node.forcedPrint = true;
			this.threadMutation(node);
		}
	}

	// `for x in it:` has no exit CONDITION (exhaustion raises): TS's explicit-iterator loop with a sentinel, not a try/except (binding the target on one
	// branch only): `__missN = object(); __itN = iter(it); while True: __rN = next(__itN, __missN); if __rN is __missN: break; x = __rN; body`.
	private lowerFor(recurse: Recurse<Expr, Stmt>, s: PY.Stmt & { type: 'for' }) {
		const suffix		= String(this.freshId());
		const missName		= `__miss${suffix}`;
		const iterName		= `__it${suffix}`;
		const resultName	= `__r${suffix}`;
		const missExpr		= Identifier(missName);

		recurse.statement({ type: 'assign', targets: [Identifier(missName)], value: posCall('object', []) } as Stmt);
		recurse.statement({ type: 'assign', targets: [Identifier(iterName)], value: posCall('iter', [s.iter]) } as Stmt);

		const body: Stmt[] = [
			{ type: 'assign', targets: [Identifier(resultName)], value: posCall('next', [Identifier(iterName), missExpr]) } as Stmt,
			If<Expr, Stmt[]>(
				{ type: 'compare', left: Identifier(resultName), ops: ['is'], comparators: [missExpr] } as Expr,
				[{ type: 'break' } as Stmt]
			),
			{ type: 'assign', targets: [s.target], value: Identifier(resultName) } as Stmt,
			...s.body,
		];
		this.buildLoop(recurse, Literal(true), () => { for (const st of body) recurse.statement(st); }, false);
	}

	// Heritage and method bodies resolved through VSDG, each with a REAL edge into `anchor` (classInfo's NodeIds are invisible to consumer counting).
	buildClass(recurse: Recurse<Expr, Stmt>, anchor: N, s: PY.Stmt & { type: 'classdef' }): ClassInfo {
		let port = 1;
		let superClassNodeId: NodeId | undefined;
		for (const base of s.bases) {
			recurse.expression(base.value);
			const node = this.getExprNode(base.value);
			connectValue(node, 0, anchor, port++);
			// Only the first base is spliced back at print time; the edge keeps what the others reference alive.
			superClassNodeId ??= node.id;
		}
		return {
			superClassNodeId,
			members: s.body.map(m => {
				if (m.type !== 'funcdef')
					return {};
				return { entryNodeId: this.buildFunctionBody(recurse, paramSlots(m.params), m.body).id };
			}),
		};
	}

	lowerExpression(e: Expr, process: (e: Expr) => boolean, recurse: Recurse<Expr, Stmt>): boolean {
		switch (e.type) {
			case 'identifier':
				return false;

			case 'literal': {
				process(e);
				const node = this.makeExprNode(e);
				// An f-string is no constant, but its fields are real value inputs, or a binding one reads would be elided.
				if (Array.isArray(e.value))
					forEachFStringField(e.value, (expr, port) => {
						recurse.expression(expr);
						connectValue(this.getExprNode(expr), 0, node, port);
					});
				return false;
			}
			case 'imaginary': {
				this.makeExprNode(e);
				return false;
			}
			case 'ellipsis':
				// `...` is a singleton whose identity matters; a pure opaque value, never a folded one.
				this.makeExprNode(e);
				return false;

			case 'unary': {
				// Python has no `++`/`--`, so a unary is never a mutation.
				process(e);
				const node = this.makeExprNode(e);
				connectValue(this.getExprNode(e.operand), 0, node, 0);
				return false;
			}
			case 'binary': {
				process(e);
				const node = this.makeExprNode(e);
				connectValue(this.getExprNode(e.left), 0, node, 0);
				connectValue(this.getExprNode(e.right), 0, node, 1);
				return false;
			}
			case 'compare': {
				// `a < b < c`: the left operand plus each comparator, in order.
				process(e);
				const node = this.makeExprNode(e);
				connectValue(this.getExprNode(e.left), 0, node, 0);
				e.comparators.forEach((c, i) => connectValue(this.getExprNode(c), 0, node, i + 1));
				return false;
			}
			case 'conditional': {
				process(e);
				const node = this.makeExprNode(e);
				connectValue(this.getExprNode(e.test), 0, node, 0);
				connectValue(this.getExprNode(e.consequent), 0, node, 1);
				connectValue(this.getExprNode(e.alternate), 0, node, 2);
				return false;
			}
			case 'namedexpr': {
				// `(x := v)` assigns AND yields: a mutation valued as its right-hand side, its target a name, with no old-value port.
				process(e);
				const node = this.makeExprNode(e, 'mutation');
				connectValue(this.getExprNode(e.value), 0, node, 1);
				this.rebindVar(e.target, node, this.scope.get(e.target) === undefined);
				return false;
			}
			case 'spread': {
				process(e);
				connectValue(this.getExprNode(e.operand), 0, this.makeExprNode(e), 0);
				return false;
			}
			case 'member': {
				process(e);
				const node = this.makeNode({type: 'member', name: e.property});
				node.freshTarget = true;
				this.expnodes.set(e, node);
				connectValue(this.getExprNode(e.object), 0, node, 0);
				return false;
			}
			case 'index': {
				process(e);
				const node = this.makeExprNode(e);
				node.freshTarget = true;
				connectValue(this.getExprNode(e.object), 0, node, 0);
				connectValue(this.getExprNode(e.index), 0, node, 1);
				return false;
			}
			case 'slice': {
				process(e);
				const node = this.makeExprNode(e);
				if (e.lower)
					connectValue(this.getExprNode(e.lower), 0, node, 0);
				if (e.upper)
					connectValue(this.getExprNode(e.upper), 0, node, 1);
				if (e.step)
					connectValue(this.getExprNode(e.step), 0, node, 2);
				return false;
			}
			case 'call': {
				// As in TS, a callee named `pure...` stands in for purity analysis; every other call is an effect.
				process(e);
				const pure = e.callee.type === 'identifier' && e.callee.name.startsWith('pure');
				const node = pure ? this.makeExprNode(e) : this.makeExprNode(e, 'effect');
				if (!pure)
					this.connectEnd(node);
				e.arguments.forEach((arg, i) => connectValue(this.getExprNode(arg.value), 0, node, i + 1));
				connectValue(this.getExprNode(e.callee), 0, node, e.arguments.length + 1);
				return false;
			}
			case 'await': {
				process(e);
				const node = this.makeExprNode(e, 'effect');
				this.connectEnd(node);
				connectValue(this.getExprNode(e.operand), 0, node, 1);
				return false;
			}
			case 'yield': {
				process(e);
				const node = this.makeExprNode(e, 'effect');
				this.connectEnd(node);
				if (e.operand)
					connectValue(this.getExprNode(e.operand), 0, node, 1);
				if (e.from)
					connectValue(this.getExprNode(e.from), 0, node, 2);
				return false;
			}

			case 'tuple':
			case 'list':
			case 'set': {
				process(e);
				const node = this.makeExprNode(e);
				e.elements.forEach((elem, i) => connectValue(this.getExprNode(elem), 0, node, i));
				return false;
			}
			case 'dict': {
				// One port per key (a `**` entry has none) plus one per value, in source order.
				process(e);
				const node = this.makeExprNode(e);
				let port = 0;
				e.keys.forEach((k, i) => {
					if (k)
						connectValue(this.getExprNode(k), 0, node, port++);
					connectValue(this.getExprNode(e.values[i]), 0, node, port++);
				});
				return false;
			}
			case 'genexp':
			case 'listcomp':
			case 'setcomp': {
				process(e);
				// A clause's TARGET is a binding, so only `iter`/`test` are threaded, which they must be, or a variable they read is elided.
				const node = this.makeExprNode(e);
				let port = 0;
				connectValue(this.getExprNode(e.elt), 0, node, port++);
				this.connectCompClauses(node, e.gens, port);
				return false;
			}
			case 'dictcomp': {
				process(e);
				const node = this.makeExprNode(e);
				let port = 0;
				connectValue(this.getExprNode(e.key), 0, node, port++);
				connectValue(this.getExprNode(e.value), 0, node, port++);
				this.connectCompClauses(node, e.gens, port);
				return false;
			}
			case 'lambda': {
				// A `def`'s 'function' entry with `.expr` set: one expression body, printed verbatim as a value.
				recurse.expression(e.body);
				const entry = this.buildFunctionBody(recurse, paramSlots(e.params), e.body);
				entry.expr = e;
				this.expnodes.set(e, entry);
				this.end = entry;
				return false;
			}

			default:
				// An unmodelled expression form: descended into, but an effect, the only safe assumption about unknown order and purity.
				console.log(`not handling expression ${(e as {type: string}).type}`);
				process(e);
				this.connectEnd(this.makeExprNode(e, 'effect'));
				return false;
		}
	}

	private connectCompClauses(node: N, gens: readonly PY.CompClause[], port: number) {
		for (const clause of gens) {
			if (clause.type === 'for')
				connectValue(this.getExprNode(clause.iter), 0, node, port++);
			else
				connectValue(this.getExprNode(clause.test), 0, node, port++);
		}
	}
}

// ===================================================================
//  Reconstruction
// ===================================================================

export class PYEmitter extends Emitter<Expr, Stmt, Expr> {
	constructor(graph: VSDG, blocks?: BlockTree, blockIds?: Map<NodeId, string>) {
		super(graph, pyDialect, blocks, blockIds);
	}

	// Python's suites ARE statement lists, passed straight in; only an EMPTY one needs spelling (no `{}`).

	makeBlock(body: Stmt[] | undefined): Stmt[] | undefined { return body === undefined ? undefined : body.length ? body : [{ type: 'pass' }]; }

	makeIf(test: Expr, consequent: Stmt[], alternate?: Stmt[]): Stmt {
		// An empty `else:` prints as nothing (the printer's elseChain).
		return { type: 'if', test, consequent: this.makeBlock(consequent), alternate } as Stmt;
	}
	makeSwitch(): Stmt							{ throw new Error('vsdg/py: Python has no switch'); }
	makeTry(body: Stmt[], handler: { param?: string, type?: Expr, body: Stmt[] }, finalizer?: Stmt[]): Stmt {
		return {
			type: 'try',
			body:		this.makeBlock(body),
			handlers:	[{ param: handler.param, type: handler.type, star: false, body: this.makeBlock(handler.body) }],
			orelse:		[],
			finalizer:	finalizer ?? [],
		} as Stmt;
	}
	makeThrow(argument: Expr): Stmt			{ return Throw(argument) as Stmt; }
	makeTempDecl(name: string, value: Expr): Stmt {
		return { type: 'assign', targets: [Identifier(name)], value } as Stmt;
	}

	// ---- whole statements the core anchors on ----

	emitPassthru(node: NOf<'passthru'>): Stmt {
		return node.stmt;
	}
	rebuildClassDecl(node: NOf<'class_decl'>): Stmt {
		const info = node.classInfo!;
		const raw  = node.stmt as PY.Stmt & { type: 'classdef', bases: PY.Arg[], body: Stmt[] };
		return {
			...raw,
			bases: info.superClassNodeId
				? raw.bases.map((b, i) => i === 0 ? { ...b, value: this.resolveNode(info.superClassNodeId!) } : b)
				: raw.bases,
			body: raw.body.map((m, i) => {
				const entryNodeId = info.members[i]?.entryNodeId;
				if (entryNodeId === undefined || m.type !== 'funcdef')
					return m;
				return { ...m, body: this.rebuildFunctionBody(this.graph.getNode(entryNodeId) as NOf<'function'>) };
			}),
		} as Stmt;
	}
	rebuildFunctionDecl(node: NOf<'function'>, body: Stmt[]): Stmt {
		return { ...(node.stmt as Stmt & { type: 'funcdef' }), body } as Stmt;
	}

	// The first assignment IS the declaration in Python: a `var` prints as a plain assignment.
	emitNamedSlot(name: string, node: N): Stmt | undefined {
		this.names.add(name);

		if (node.type === 'var') {
			if (!node.inputs[0])
				return undefined;
			// Nothing reads the name (dead, or its reader recomputes the pure initializer). A forced sibling reads it by name, so it must exist:
			// `name = None` is Python's "declared, no value yet".
			if (!this.graph.hasRealConsumer(node) || (this.isInlinableVarDecl(node) && !this.hasForcedSibling(name, node.id)))
				return this.hasForcedSibling(name, node.id)
					? { type: 'assign', targets: [Identifier(name)], value: Literal(null) } as Stmt
					: undefined;
			const value = this.resolveOperand(node.id, 0);
			return node.declKind === 'annotate' && node.typeAnnotation !== undefined
				? { type: 'annassign', target: Identifier(name), annotation: node.typeAnnotation, value } as Stmt
				: { type: 'assign', targets: [Identifier(name)], value } as Stmt;
		}
		if (node.type === 'mutation')
			return this.rebuildMutationStatement(node);
		return { type: 'assign', targets: [Identifier(name)], value: this.buildExpr(node) } as Stmt;
	}

	// ---- expressions ----

	rebuildPayload(node: N): Expr {
		switch (node.type) {
			case 'floating':
				return this.rebuildFloating(node);
			case 'mutation':
				return this.rebuildMutationValue(node);
			case 'effect':
				return this.rebuildEffect(node);
			case 'member':
				return { type: 'member', object: this.resolveOperand(node.id, 0), property: node.name } as Expr;
		}
		console.log(`not handling value node ${node.type}`);
		return Literal(null);
	}

	private rebuildCompClauses(node: N, gens: readonly PY.CompClause[], start: number): PY.CompClause[] {
		let port = start;
		return gens.map(clause => clause.type === 'for'
			? { ...clause, iter: this.resolveOperand(node.id, port++) }
			: { ...clause, test: this.resolveOperand(node.id, port++) });
	}

	rebuildFloating(node: NOf<'floating'>): Expr {
		const e = node.expr;
		switch (e.type) {
			case 'identifier':
			case 'imaginary':
			case 'ellipsis':
				return e;
			case 'literal':
				// An f-string's interpolated expressions are the one nested AST a literal carries.
				return Array.isArray(e.value)
					? { ...e, value: rebuildFString(e.value, port => this.resolveOperand(node.id, port)) }
					: e;
			case 'unary':
				return { ...e, operand: this.resolveOperand(node.id, 0) };
			case 'binary':
				return { ...e, left: this.resolveOperand(node.id, 0), right: this.resolveOperand(node.id, 1) };
			case 'compare':
				return { ...e, left: this.resolveOperand(node.id, 0), comparators: e.comparators.map((_, i) => this.resolveOperand(node.id, i + 1)) };
			case 'conditional':
				return this.buildConditional(node);
			case 'spread':
				return { ...e, operand: this.resolveOperand(node.id, 0) };
			case 'index':
				return { ...e, object: this.resolveOperand(node.id, 0), index: this.resolveOperand(node.id, 1) };
			case 'slice':
				return {
					...e,
					lower:	e.lower ? this.resolveOperand(node.id, 0) : undefined,
					upper:	e.upper ? this.resolveOperand(node.id, 1) : undefined,
					step:	e.step  ? this.resolveOperand(node.id, 2) : undefined,
				};
			case 'call':
				return { ...e, arguments: e.arguments.map((arg, i) => ({ ...arg, value: this.resolveOperand(node.id, i + 1) })) };
			case 'tuple':
			case 'list':
			case 'set':
				return { ...e, elements: e.elements.map((_, i) => this.resolveOperand(node.id, i)) };
			case 'dict': {
				let port = 0;
				const keys		= e.keys.map(k => k ? this.resolveOperand(node.id, port++) : null);
				const values	= e.values.map((_, _i) => this.resolveOperand(node.id, port++));
				return { ...e, keys, values };
			}
			case 'genexp':
			case 'listcomp':
			case 'setcomp': {
				const gens = this.rebuildCompClauses(node, e.gens, 1);
				return { ...e, elt: this.resolveOperand(node.id, 0), gens };
			}
			case 'dictcomp': {
				const gens = this.rebuildCompClauses(node, e.gens, 2);
				return { ...e, key: this.resolveOperand(node.id, 0), value: this.resolveOperand(node.id, 1), gens };
			}
		}
		console.log(`not handling value node ${(e as {type: string}).type}`);
		return Literal(null);
	}

	// An assignment read as a VALUE: in Python only `(x := v)`.
	rebuildMutationValue(node: NOf<'mutation'>): Expr {
		const e = node.expr;
		if (e.type === 'namedexpr')
			return { ...e, value: this.resolveOperand(node.id, 1) };
		// The converged Assign of a plain `x = v`: as a value, its right-hand side (`x += v` has no value form).
		const assign = e as unknown as { type: 'assign', operator?: PY.binaryOps };
		if (assign.type === 'assign') {
			const right = this.resolveOperand(node.id, 1);
			return assign.operator === undefined
				? right
				: { type: 'binary', operator: assign.operator, left: this.resolveTarget(node.id, 0), right };
		}
		console.log(`not handling mutation value ${(e as {type: string}).type}`);
		return Literal(null);
	}

	rebuildMutationStatement(node: NOf<'mutation'>): Stmt {
		const e = node.expr;
		if (e.type === 'namedexpr') {
			// As a statement `x := v` is `x = v`, and it is not even legal unparenthesized.
			const name = slotName(node) ?? e.target;
			return { type: 'assign', targets: [Identifier(name)], value: this.resolveOperand(node.id, 1) } as Stmt;
		}
		// The converged Assign payload (see the builder's own bindTarget).
		const assign = e as unknown as { type: 'assign', operator?: PY.binaryOps };
		if (assign.type === 'assign')
			return assign.operator === undefined
				? { type: 'assign', targets: [this.resolveTarget(node.id, 0)], value: this.resolveOperand(node.id, 1) } as Stmt
				: {
					type: 'augassign',
					target:	this.resolveTarget(node.id, 0),
					op:		(assign.operator + '=') as string,
					value:	this.resolveOperand(node.id, 1),
				} as Stmt;
		console.log(`not handling mutation statement ${(e as {type: string}).type}`);
		return { type: 'pass' } as Stmt;
	}

	rebuildEffect(node: NOf<'effect'>): Expr {
		const e = node.expr;
		switch (e.type) {
			case 'await':
				return { ...e, operand: this.resolveOperand(node.id, 1) };
			case 'yield':
				return {
					...e,
					operand:	e.operand ? this.resolveOperand(node.id, 1) : undefined,
					from:		e.from    ? this.resolveOperand(node.id, 2) : undefined,
				};
			case 'call': {
				// The callee prints raw, unless it embeds an effect (or was hoisted into a temp), which raw source would run again.
				const calleeEdge	= node.inputs[e.arguments.length + 1];
				const calleeNode	= calleeEdge && this.graph.get(calleeEdge.nodeId);
				const calleeTemp	= calleeNode && this.nodeVariableNames.get(calleeNode.id);
				const callee		= calleeTemp ? Identifier(calleeTemp)
					: calleeNode && !this.graph.isPureSubgraph(calleeNode) ? this.resolveNode(calleeNode.id) : e.callee;
				return { ...e, callee, arguments: e.arguments.map((arg, i) => ({ ...arg, value: this.resolveOperand(node.id, i + 1) })) };
			}
			default:
				return e;	// `lambda`, or an unmodelled construct kept verbatim
		}
	}
}

// ===================================================================
//  The pipeline
// ===================================================================

export function BuildVSDG(ast: readonly Stmt[]): VSDG {
	const builder = new PYBuilder();
	builder.build(ast);
	return builder.finish();
}

export function Optimize(graph: VSDG): void {
	optimize(graph, pyDialect);
}

export function BuildProgram(graph: VSDG, blocks?: BlockTree, blockIds?: Map<NodeId, string>): Stmt[] {
	return new PYEmitter(graph, blocks, blockIds).build();
}

// Kept for callers that drive CSE directly; `Optimize` runs it as its own final round.
export function optimizeStructuralCSE(graph: VSDG, protectedIds: Set<NodeId>): boolean {
	return structuralCSE(graph, pyDialect, protectedIds);
}
