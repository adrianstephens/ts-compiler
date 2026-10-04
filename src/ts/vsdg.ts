// ===================================================================
//  The TypeScript/JavaScript half of the language-neutral VSDG.
// ===================================================================
// The core (`../vsdg.ts`) plus three TypeScript-shaped pieces: `TSDialect` (shape facts the core asks), `TSBuilder` (lowering this AST's tags onto
// graph nodes) and `TSEmitter` (reconstruction onto this AST); at the bottom the pipeline entry points, BuildVSDG -> Optimize -> GCM -> BuildProgram.

import * as JS from './js-parser';
import * as TS from './ts-parser';
import { Identifier, Literal, Binary, Assign, If, ExprStmt, Block } from '@isopodlabs/tison/ast';
import { walkerB, isJsStatement, isTsDeclaration, constantFolder } from './walker';
import { patternBindings as buildPatternBindings } from './transform';
import { tocode } from './type-utils';
import {
	Dialect, VSDGBuilder, Emitter, Recurse, ParamSlot, NodeType, SwitchSyntax,
	Node, NodeOf, NodeId, ClassInfo, ClassMember, Scope, VSDG, BlockTree,
	connectValue, slotName,
	optimize, optimizeStructuralCSE as structuralCSE,
} from '../vsdg';

type Expr	= TS.Expr;
type Stmt	= TS.Stmt;
type Type	= TS.Type;
type N		= Node<Expr, Stmt, Type>;
type NOf<K extends NodeType> = NodeOf<Expr, Stmt, Type, K>;

// ===================================================================
//  Dialect
// ===================================================================

const tsDialect: Dialect<Expr, Stmt, Type> = {
	...constantFolder,
	identifierName(e) {
		return e.type === 'identifier' ? e.name : undefined;
	},
	identifier(name) {
		return Identifier(name);
	},
	// A 'floating' node's discriminator is its expr's type, except these three, whose OPERATOR separates `a + b` from `a - b`.
	exprKey(e) {
		switch (e.type) {
			case 'assign':
			case 'binary':
			case 'unary':	return String((e as {operator?: unknown}).operator);
		}
		return tocode.expression(e);
	},
	stmtKey(s) {
		return tocode.statement(s);
	},
	isCSEUnsafe(node) {
		// 'this'/'super' key alike in every method but are bound per call; 'array'/'object' are a fresh identity per evaluation; 'member'/'index'
		// reads may observe a mutation between two identical-looking occurrences.
		return node.type === 'floating' && ['array', 'object', 'index', 'this', 'super'].includes(node.expr.type);
	},
	isCalleeEdge(consumer, port) {
		const v = consumer.type === 'effect' && consumer.expr;
		if (!v || (v.type !== 'call' && v.type !== 'new'))
			return false;
		return port === v.arguments.length + 1;
	}
};

// ===================================================================
//  Lowering
// ===================================================================

// This language's parameter list as the core's neutral slots: a plain name its own param node, a destructured one a hidden temp plus the
// step binding its names off it (a closure, since finishing a pattern walks statements: lowering, not a Dialect fact).
function paramSlots(params: JS.Params<Type> | undefined, recurse: Recurse<Expr, Stmt>): ParamSlot[] | undefined {
	// Only `key` is read: on a plain parameter and on the rest it is a name or a pattern.
	const slot = (p: { key: string | JS.BindingTarget }): ParamSlot => {
		const key = p.key;
		return typeof key === 'string' ? { name: key }
			: { token: key, desugar: tempName => {
				for (const stmt of patternBindings('let', key, Identifier(tempName)))
					recurse.statement(stmt);
			} };
	};
	if (!params)
		return undefined;
	const slots: ParamSlot[] = params.params.map(slot);
	if (params.rest)
		slots.push(slot(params.rest));
	return slots;
}

export class TSBuilder extends VSDGBuilder<Expr, Stmt, Type> implements SwitchSyntax<Expr, Stmt, Type> {
	constructor() { super(tsDialect); }

	build(ast: readonly Stmt[]) {
		walkerB(
			(s, process, recurse) => this.lowerStatement(s, process, recurse),
			(e, process, recurse) => this.lowerExpression(e, process, recurse)
		).statements(ast);
	}

	// ---- SwitchSyntax: js/ts's own spelling of switch's fixed scaffolding (the walk is the core's) ----

	local(value: Expr, name: string) {
		const node = this.makeNode({ type: 'var', name, declKind: 'let' });
		connectValue(this.getExprNode(value), 0, node, 0);
		return node;
	}
	comparison(discName: string, test: Expr): Expr {
		return { type: 'binary', operator: '===', left: Identifier(discName), right: test } as Expr;
	}
	// `default` matches iff none of the OTHER cases did, wherever it sits.
	condition(hitName: string, matchName: string | undefined, otherMatches: string[]): Expr {
		const hit	= Identifier(hitName);
		const others: Expr = otherMatches.length === 0
			? Literal(true)
			: { type: 'unary', operator: '!', operand: otherMatches.map((n): Expr => Identifier(n)).reduce((a, b) => Binary('||', a, b) as Expr) } as Expr;
		return { type: 'binary', operator: '||', left: hit, right: matchName !== undefined ? Identifier(matchName) : others } as Expr;
	}
	setHit(hitName: string): Expr {
		return Assign<Expr, JS.assignableOps>(Identifier(hitName), Literal(true));
	}

	lowerStatement(s: Stmt, process: (s: Stmt) => boolean, recurse: Recurse<Expr, Stmt>): boolean {
		switch (s.type) {
			case 'function_decl':
				if (s.body) {
					const fn = this.buildFunctionBody(recurse, paramSlots(s, recurse), s.body);
					fn.stmt = s;
					this.end = fn;
				}
				return false;

			case 'return': {
				// The marker carries its value at port 1 (unconnected for a bare `return;`), not through scope, which cannot say "not returned yet";
				// `exited` makes 'if' build a real gamma, so each return prints in place.
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
				// Only an EXPLICIT throw is modelled; a call in `try` that may throw needs no edge, since nothing reorders the try body.
				recurse.expression(s.argument);
				const marker = this.makeMarker('THROW_MARKER');
				this.connectEnd(marker);
				connectValue(this.getExprNode(s.argument), 0, marker, 1);
				this.exited = true;
				return false;
			}
			case 'break': {
				// A labeled break may target an OUTER loop/switch, which no target tracking here supports: flagged rather than mistargeted.
				if (s.label)
					console.log(`not handling labeled break`);
				// Marks `exited` (enclosing `if`s see the branch not falling through) and leaves a marker printing `break;`, which JS routes at run time.
				this.connectEnd(this.makeMarker('BREAK_MARKER'));
				this.exited = true;
				this.brokeOut = true;
				return false;
			}
			case 'continue': {
				if (s.label)
					console.log(`not handling labeled continue`);
				// A `for`'s `update` still runs on `continue`, but this lowers onto the while-shaped graph, where `continue;` would skip it: a FRESH clone
				// of it is walked first (switch pushes nothing on loopUpdateStack, staying transparent to `continue`).
				const forUpdate = this.loopUpdateStack[this.loopUpdateStack.length - 1];
				if (forUpdate)
					recurse.expression(structuredClone(forUpdate));
				this.connectEnd(this.makeMarker('CONTINUE_MARKER'));
				this.exited = true;
				return false;
			}
			case 'var_decl': {
				// Each declarator is walked THEN bound, one at a time, left to right (`let i = off, e = i + len;` needs `i` for `e`).
				for (const v of s.declarations) {
					if (typeof v.name === 'string') {
						if (v.init)
							recurse.expression(v.init);
						// A wrapper node per declared variable, never an alias to the initializer's node, or `let x = 5; let y = 5;` would share one.
						const varNode = this.makeNode({type: 'var', name: v.name});
						if (v.init)
							connectValue(this.getExprNode(v.init), 0, varNode, 0);
						varNode.declKind = s.kind;
						varNode.typeAnnotation = v.typeAnnotation;
						// A declaration is an observable event, as a reassignment is: else GCM could schedule `let a = 1;` after a read of `a`.
						this.bindVar(varNode);
					} else if (v.init) {
						// The initializer bound once to a hidden temp (patternBindings may read it several times), then the pattern desugared off it; a nested
						// pattern re-enters this case.
						const tempName = `__destructure${this.freshId()}`;
						recurse.statement(JS.VarDecl<Type>(s.kind, JS.Var<Type>(tempName, v.init)) as Stmt);
						for (const stmt of patternBindings(s.kind, v.name, Identifier(tempName)))
							recurse.statement(stmt);
					} else {
						console.log(`not handling destructured declarator with no initializer`);
					}
				}
				return false;
			}

			case 'block': {
				this.scope = new Scope(this.scope);
				process(s);
				this.scope = this.scope.closeAndFlush()!;
				return false;
			}
			case 'if': {
				recurse.expression(s.test);
				const test		= this.getExprNode(s.test);
				const parent	= this.getState();
				// `recurse`, not `process`: a bare consequent (`if (x) let y = 1;`) still needs its own dispatch.
				const trueState		= this.walkBranch(parent, () => recurse.statement(s.consequent));
				const falseState	= this.walkBranch(parent, () => { if (s.alternate) recurse.statement(s.alternate!); });
				this.mergeState(parent, test, trueState, falseState);
				this.reconcileVariables(parent, test, trueState, falseState);
				return false;
			}

			case 'while':
				this.buildLoop(recurse, s.test, () => recurse.statement(s.body), false);
				return false;

			case 'do_while':
				// The body runs BEFORE the test (using the mu's INITIAL value on the first pass), unlike `while`
				this.buildLoop(recurse, s.test, () => recurse.statement(s.body), true);
				return false;

			case 'for': {
				// `for await...of` needs the async iterator protocol, unmodelled here, so it stays verbatim rather than run its body once.
				if (s.kind === 'of await') {
					console.log(`not handling for-${s.kind}`);
					return this.lowerVerbatim(s, process);
				}
				if (s.kind !== 'normal') {
					// Desugared to the synchronous iterator protocol over buildLoop: `const __iterN = iterable[Symbol.iterator](); while (true) { const __rN =
					// __iterN.next(); if (__rN.done) break; binding = __rN.value; body }`; `for...in` over `Object.keys(iterable)`. `continue` re-runs the advance.
					const suffix		= String(this.freshId());
					const iterName		= `__iter${suffix}`;
					const resultName	= `__r${suffix}`;
					const iterable		= s.kind === 'in' ? JS.Call<Type>(JS.Member<Type>(Identifier('Object'), 'keys'), [s.right]) : s.right;
					recurse.statement(JS.VarDecl<Type>('const', JS.Var<Type>(iterName,
						JS.Call<Type>(JS.Index<Type>(iterable, JS.Member<Type>(Identifier('Symbol'), 'iterator')), [])
					)));

					const value = JS.Member<Type>(Identifier(resultName), 'value');
					this.buildLoop(recurse, Literal(true), () => recurse.statement(JS.Block<Stmt>(
						JS.VarDecl<Type>('const', JS.Var<Type>(resultName, JS.Call<Type>(JS.Member<Type>(Identifier(iterName), 'next'), []))),
						If(JS.Member<Type>(Identifier(resultName), 'done'), { type: 'break' }),
						(s.init.type === 'var_decl'
							? JS.VarDecl<Type>(s.init.kind, JS.Var<Type>(s.init.declarations[0].name, value))
							: ExprStmt(Assign<Expr, JS.assignableOps>(s.init, value))),
						s.body
					)), false);
					return false;
				}
				// `init` once, then `while (test) { body; update; }`, `update` on the body's normal tail.
				if (s.init) {
					if (s.init.type === 'var_decl')
						recurse.statement(s.init);
					else
						recurse.expression(s.init);
				}
				const test = s.test ?? Literal(true);
				const body = s.update ? JS.Block(s.body, ExprStmt(s.update)) : s.body;
				this.buildLoop(recurse, test, () => recurse.statement(body), false, s.update);
				return false;
			}

			case 'switch': {
				// The cascade is the core's (`buildSwitch`); this is js/ts's scaffolding for it. `continue` in a case reaches the enclosing loop.
				this.buildSwitch(recurse, s.discriminant, s.cases.map(c => ({
					test: c.test,
					body: () => { for (const stmt of c.consequent) recurse.statement(stmt); },
				})), this);
				return false;
			}
			case 'try': {
				// A bare `try { } finally { }` (no catch) is not attempted: nothing diverges there to merge.
				const handler = s.handlers[0];
				if (!handler) {
					console.log(`not handling try without catch`);
					return this.lowerVerbatim(s, process);
				}
				const parent = this.getState();

				// Each branch gets its own start marker after the shared predecessor, or a branch's first gamma/mu/break_scope/except would share `except`'s.
				const startMarker = (pred: N, tag: 'TRY_START' | 'CATCH_START' | 'FINALLY_START') => {
					const marker = this.makeMarker(tag);
					connectValue(pred, 0, marker, 0);
					return marker;
				};

				// Each branch gets TWO scopes: an outer one the reconciliation reads (as if/else), an inner one flushed first so a block-level `let`/`const`
				// does not leak into the outer bindings.
				this.setState(new Scope(parent.scope), startMarker(parent.end, 'TRY_START'));

				this.scope = new Scope(this.scope);
				for (const stmt of s.body)
					recurse.statement(stmt);
				this.scope = this.scope.closeAndFlush()!;
				const tryState		= this.getState();

				this.setState(new Scope(parent.scope), startMarker(parent.end, 'CATCH_START'));
				this.scope = new Scope(this.scope);
				// A destructured catch param prints as its hidden temp in `catch (<here>)`, the pattern desugared after it.
				let catchParamName: string | undefined;
				if (typeof handler.param === 'string') {
					catchParamName = handler.param;
					this.scope.create(catchParamName, this.makeNode({type: 'var', name: catchParamName}));
				} else if (handler.param) {
					catchParamName = `__destructure${this.freshId()}`;
					this.scope.create(catchParamName, this.makeNode({type: 'var', name: catchParamName}));
					for (const stmt of patternBindings('let', handler.param, Identifier(catchParamName)))
						recurse.statement(stmt);
				}
				for (const stmt of handler.body)
					recurse.statement(stmt);
				this.scope = this.scope.closeAndFlush()!;
				const catchState	= this.getState();

				// Never skipped like an `if`'s gamma: try/catch is observable syntax, which needs an anchor to reconstruct from.
				const exc = this.makeNode({ type: 'except' });
				if (catchParamName !== undefined)
					exc.catchParam = catchParamName;
				connectValue(parent.end, 0, exc, 0);
				connectValue(tryState.end, 0, exc, 1);
				connectValue(catchState.end, 0, exc, 2);
				this.end = exc;

				// Per-variable merges as 'if' makes them, except no branch's binding is cleared: with no condition to print, each branch force-prints its own
				// `x = ...;` and the merge connects both.
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

				// `finally` runs after the merge, walked as ordinary code and reconstructed as a real `finally` clause (JS guarantees every exit runs it).
				let finallyExited = false;
				let finallyBrokeOut = false;
				if (s.finalizer) {
					this.end		= startMarker(exc, 'FINALLY_START');
					this.exited		= false;
					this.brokeOut	= false;
					// As try/catch's inner scope: a `let`/`const` in the finalizer stays local; a reassignment propagates.
					this.scope		= new Scope(this.scope);
					for (const stmt of s.finalizer)
						recurse.statement(stmt);
					this.scope			= this.scope.closeAndFlush()!;
					finallyExited		= this.exited;
					finallyBrokeOut		= this.brokeOut;
					// Port 3 = finally's own tail, mirroring a gamma's true/false-tail ports.
					connectValue(this.end, 0, exc, 3);
					this.end = exc;
				}
				// An exit inside `finally` overrides try/catch, so the construct falls through only when finally (if present) does.
				this.exited = finallyExited || (tryState.exited && catchState.exited);
				this.brokeOut = s.finalizer
					? finallyBrokeOut
					: (tryState.exited && catchState.exited && tryState.brokeOut && catchState.brokeOut);
				return false;
			}
			case 'expression':
				// A bare literal statement is a directive (`"use strict"`), not dead arithmetic.
				if (s.expression.type === 'literal')
					return this.lowerVerbatim(s, process);
				break;

			case 'export_decl': {
				// `export class/function/const`: recursing here, rather than the default's generic descent that also walks `s.declaration`, runs its handler
				// exactly once; `exported` is read at that node's print site.
				recurse.statement(s.declaration);
				if (s.declaration.type === 'var_decl') {
					// `end` wraps only the LAST declarator's rebind, so each declared name's node is looked up in scope for the flag.
					for (const v of s.declaration.declarations)
						if (typeof v.name === 'string')
							this.scope.get(v.name)!.exported = 'named';
				} else {
					this.end.exported = 'named';
				}
				return false;
			}

			case 'import': {
				// Each bound name gets a never-declared 'var' node (as `externalNodes`; the import's passthru declares it), anchored after that passthru so
				// GCM never reads it earlier. A type-only import binds nothing.
				this.lowerVerbatim(s, process);
				if (!s.typeOnly) {
					const bindImport = (name: string) => {
						const varNode = this.makeNode({type: 'var', name});
						this.threadMutation(varNode);
						this.scope.create(name, varNode);
					};
					if (s.namespace)
						bindImport(s.namespace);
					if (s.default)
						bindImport(s.default);
					for (const spec of s.specifiers ?? [])
						if (!spec.typeOnly)
							bindImport(spec.local);
				}
				return false;
			}

			case 'export': {
				// `export default class/function`: as export_decl above. A plain-expression default, or a re-export, prints verbatim.
				if (s.default !== undefined && (isJsStatement(s.default) || isTsDeclaration(s.default))) {
					recurse.statement(s.default);
					this.end.exported = 'default';
					return false;
				}
				this.lowerVerbatim(s, process);
				return false;
			}

			case 'class_decl': {
				// Its own tag (not 'passthru') makes "always needs rebuildClass" a property of the node; anchored as a statement, producing no value.
				const node = this.makeNode({type: 'class_decl', stmt: s});
				node.classInfo = this.buildClass(recurse, node, s);
				this.connectEnd(node);
				return false;
			}

			default:
				// Anything this dialect does not model (`labeled`, `with`, `debugger`, an ambient declaration) prints verbatim, anchored.
				this.lowerVerbatim(s, process);
				return false;
		}
		return process(s);
	}

	lowerExpression(s: Expr, process: (e: Expr) => boolean, recurse: Recurse<Expr, Stmt>): boolean {
		switch (s.type) {
			case 'literal': {
				// A literal is a 'floating' node whose expr is this AST's literal form: what `literalValue` reads, and what foldConstants folds into in place.
				this.makeExprNode(s);
				return false;
			}

			case 'import_meta':
				this.makeExprNode(s);
				return false;

			case 'identifier':
				return false;

			case 'super':
			case 'this': {
				// `this`/`super` have no scope lookup, so they get a node here, floored to their function by scopeAnchorId (a materialized this-derived value
				// could otherwise escape it).
				this.makeExprNode(s).scopeAnchorId = this.currentFunctionEntry?.id;
				return false;
			}

			// Not pure: it suspends. Same treatment as 'yield'.
			case 'await': {
				process(s);
				const node = this.makeExprNode(s, 'effect');
				this.connectEnd(node);
				connectValue(this.getExprNode(s.operand), 0, node, 1);
				return false;
			}

			case 'unary': {
				process(s);
				const isMutation = s.operator === '++' || s.operator === '--';
				const node = this.makeExprNode(s, isMutation ? 'mutation' : 'floating');
				connectValue(this.getExprNode(s.operand), 0, node, 0);
				if (isMutation) {
					if (s.operand.type === 'identifier') {
						this.rebindVar(s.operand.name, node);
					} else {
						// A property/index target mutates outside this pass's scope tracking: nothing reads it back through scope, so needsTemp would drop it.
						node.forcedPrint = true;
						this.threadMutation(node);
					}
				}
				return false;
			}
			case 'unary_post': {
				// `expr!` shares `unary_post`'s shape with `++`/`--` but has no runtime effect: aliased straight through.
				if (s.operator === '!') {
					process(s);
					this.expnodes.set(s, this.getExprNode(s.operand));
					return false;
				}
				// `i++` evaluates to the OLD value, so it cannot alias the operand's node, reachable by name after the rebind: a snapshot node, threaded before
				// the rebind, pins its value and schedule.
				process(s);
				const operandNode	= this.getExprNode(s.operand);
				const oldNode		= this.makeExprNode(s, 'unary_post_old' as 'floating');
				connectValue(operandNode, 0, oldNode, 0);
				this.threadMutation(oldNode);

				const node = this.makeNode({ type: 'unary_post', expr: s });
				connectValue(operandNode, 0, node, 0);
				// Scheduling-only (the core's INVARIANT): the snapshot must be READ before the increment, and the marker only floors it; the increment
				// consuming it stops GCM sinking it past (`g(i++)` reading the new `i`).
				connectValue(oldNode, 0, node, 1);
				if (s.operand.type === 'identifier') {
					this.rebindVar(s.operand.name, node);
				} else {
					// A property/index target has no name to rebind: the snapshot materializes if read, and the mutation itself gets a forced anchor.
					node.forcedPrint = true;
					this.threadMutation(node);
				}
				return false;
			}
			// Always a mutation -- no operator set to consult, and none to forget an entry from.
			case 'assign': {
				process(s);
				const node = this.makeExprNode(s, 'mutation');
				// A plain `=` (no compound operator) never reads its own "old value" port.
				node.plainAssign = s.operator === undefined;
				connectValue(this.getExprNode(s.target), 0, node, 0);
				connectValue(this.getExprNode(s.value), 0, node, 1);
				if (s.target.type === 'identifier') {
					// Reassigning a variable CAPTURED from an enclosing function escapes it: its consumer may be a later caller, so no consumer count decides.
					if (!this.scope.isLocalToCurrentFunction(s.target.name))
						node.forcedPrint = true;
					this.rebindVar(s.target.name, node);
				} else {
					// A property/index assignment mutates outside this pass's scope tracking: threadMutation anchors it, forcedPrint keeps it printing.
					node.forcedPrint = true;
					this.threadMutation(node);
				}
				return false;
			}

			// Never a mutation now that assignment has its own tag.
			case 'binary': {
				process(s);
				const node = this.makeExprNode(s, 'floating');
				connectValue(this.getExprNode(s.left), 0, node, 0);
				connectValue(this.getExprNode(s.right), 0, node, 1);
				return false;
			}
			case 'call': {
				process(s);
				// TEMPORARY stand-in for purity analysis: a callee name starting with "pure" is treated as pure, for testing only.
				const pure = s.callee.type === 'identifier' && s.callee.name.startsWith('pure');
				const node = pure ? this.makeExprNode(s) : this.makeExprNode(s, 'effect');
				if (!pure)
					this.connectEnd(node); // Slot 0 = Input State

				s.arguments.forEach((arg, index) => connectValue(this.getExprNode(arg), 0, node, index + 1));

				// The callee prints verbatim, but a bare identifier callee needs a real edge so hasRealConsumer sees it (`const g = makeThing(); g();`).
				connectValue(this.getExprNode(s.callee), 0, node, s.arguments.length + 1);
				return false;
			}

			case 'new': {
				// An effect, like an impure call: a constructor can run arbitrary code.
				process(s);
				const node = this.makeExprNode(s, 'effect');
				this.connectEnd(node);
				s.arguments.forEach((arg, index) => connectValue(this.getExprNode(arg), 0, node, index + 1));
				// See 'call' above for why the callee still needs a real edge despite never being resolved as a value.
				connectValue(this.getExprNode(s.callee), 0, node, s.arguments.length + 1);
				return false;
			}
			case 'yield': {
				// An effect: a yield is never reordered against other effects.
				process(s);
				const node = this.makeExprNode(s, 'effect');
				this.connectEnd(node);
				if (s.operand)
					connectValue(this.getExprNode(s.operand), 0, node, 1);
				return false;
			}
			case 'tagged_template': {
				// Calls `tag` with a strings array and each interpolation, an effect; only the `.exp`s are threaded.
				process(s);
				const node = this.makeExprNode(s, 'effect');
				this.connectEnd(node);
				s.quasi.forEach((part, index) => {
					if (part.exp)
						connectValue(this.getExprNode(part.exp), 0, node, index + 1);
				});
				return false;
			}
			case 'import_call': {
				// Loads a module: an effect, like an impure call.
				process(s);
				const node = this.makeExprNode(s, 'effect');
				this.connectEnd(node);
				s.arguments.forEach((arg, i) => connectValue(this.getExprNode(arg), 0, node, i + 1));
				return false;
			}
			case 'class': {
				// A class expression can run code (a computed key, the heritage clause): always order-anchored, like 'new'.
				const node = this.makeExprNode(s, 'effect');
				node.classInfo = this.buildClass(recurse, node, s);
				this.connectEnd(node);
				return false;
			}
			case 'jsx': {
				// A factory call at run time, an effect; `name` and attribute keys are compile-time metadata.
				process(s);
				const node = this.makeExprNode(s, 'effect');
				this.connectEnd(node);
				let port = 1;
				s.attributes.forEach(attr => {
					if (attr.value)
						connectValue(this.getExprNode(attr.value), 0, node, port++);
				});
				s.children.forEach(child => connectValue(this.getExprNode(child), 0, node, port++));
				return false;
			}
			case 'arrow':
			case 'function': {
				if (!s.body)
					return false;
				// A declaration's 'function' entry with `.expr` set: a printable value (verbatim; GCM never moves bodies), registered for getExprNode.
				const entry = this.buildFunctionBody(recurse, paramSlots(s, recurse), s.body);
				entry.expr = s;
				this.expnodes.set(s, entry);
				this.end = entry;
				return false;
			}
			case 'member': {
				process(s);
				const node = this.makeNode({type: 'member', name: s.property});
				node.optional = s.optional;
				node.freshTarget = true;
				this.expnodes.set(s, node);
				connectValue(this.getExprNode(s.object), 0, node, 0);
				return false;
			}
			case 'index': {
				process(s);
				const node = this.makeExprNode(s);
				node.freshTarget = true;
				connectValue(this.getExprNode(s.object), 0, node, 0);
				connectValue(this.getExprNode(s.index), 0, node, 1);
				return false;
			}
			case 'conditional': {
				process(s);
				const node = this.makeExprNode(s);
				connectValue(this.getExprNode(s.test), 0, node, 0);
				connectValue(this.getExprNode(s.consequent), 0, node, 1);
				connectValue(this.getExprNode(s.alternate), 0, node, 2);
				return false;
			}
			case 'array': {
				process(s);
				const node = this.makeExprNode(s);
				s.elements.forEach((elem, index) => {
					if (elem)
						connectValue(this.getExprNode(elem), 0, node, index);
				});
				return false;
			}
			case 'object': {
				// A field or spread threads a value port, index-matched to `s.properties`; a method/get/set gets its own function subgraph on classInfo,
				// invisible to a generic walk like isPureSubgraph, so a literal with a method is an 'effect', never freely inlined.
				const hasMethod = s.properties.some(p => p.type === 'method' || p.type === 'get' || p.type === 'set');
				const node		= this.makeExprNode(s, hasMethod ? 'effect' : 'floating');
				if (hasMethod)
					this.connectEnd(node);

				const members: ClassMember[] = [];
				s.properties.forEach((prop, index) => {
					switch (prop.type) {
						case 'spread':
							recurse.expression(prop.operand);
							connectValue(this.getExprNode(prop.operand), 0, node, index);
							break;
						case 'method': case 'get': case 'set':
							if (typeof prop.key === 'object')
								console.log(`not handling computed object key`);
							else if (!prop.body)
								console.log(`not handling object property ${prop.type} with no body`);
							else
								members[index] = { entryNodeId: this.buildFunctionBody(recurse, paramSlots(prop, recurse), prop.body).id };
							break;
						case 'field':
							if (typeof prop.key === 'object') {
								console.log(`not handling computed object key`);
							} else {
								recurse.expression(prop.value);
								connectValue(this.getExprNode(prop.value!), 0, node, index);
							}
							break;
					}
				});
				if (hasMethod)
					node.classInfo = { members };
				return false;
			}
			case 'spread':
				// A spread is only reached as an OPERAND (an argument, an element): it needs a node addressable by its consumers, its operand an input.
				process(s);
				connectValue(this.getExprNode(s.operand), 0, this.makeExprNode(s), 0);
				return false;

			case 'as':
			case 'satisfies':
			case 'instantiation':
				// A type-level annotation with no runtime effect: aliased straight through.
				process(s);
				this.expnodes.set(s, this.getExprNode(s.expression));
				return false;

			case 'sequence':
				// `(a, b, c)` evaluates all three in order, its value the last's.
				process(s);
				this.expnodes.set(s, this.getExprNode(s.expressions.at(-1)!));
				return false;
		}
		return false;
	}

	// ---- things only a class/object literal needs ----

	// Heritage and computed keys are expressions that can call out, resolved through VSDG so a referenced outer variable is not orphaned. Each gets
	// a REAL edge into `anchor` (ports 1..; 0 is the state predecessor): classInfo's NodeIds alone are invisible to consumer counting.
	buildClass(recurse: Recurse<Expr, Stmt>, anchor: N, s: { superClass?: JS.Expr<any>; body: JS.ClassMember<any>[] }): ClassInfo {
		let port = 1;
		let superClassNodeId: NodeId | undefined;
		if (s.superClass) {
			recurse.expression(s.superClass);
			const node = this.getExprNode(s.superClass);
			connectValue(node, 0, anchor, port++);
			superClassNodeId = node.id;
		}
		return {
			superClassNodeId,
			// Two ports per member (key, static field value); unused ones go unclaimed.
			members: s.body.map(m => {

				// A computed key resolves through VSDG and is wired into `anchor` at the next port, as above.
				let keyNodeId;
				if ('key' in m && typeof m.key === 'object') {
					const expr = m.key.computed;
					recurse.expression(expr);
					const node = this.getExprNode(expr);
					connectValue(node, 0, anchor, port++);
					keyNodeId = node.id;
				}

				switch (m.type) {
					case 'method':
					case 'get':
					case 'set':
						return m.body ? { keyNodeId, entryNodeId: this.buildFunctionBody(recurse, paramSlots(m, recurse), m.body).id } : { keyNodeId };
					case 'static_block':
						return { entryNodeId: this.buildFunctionBody(recurse, undefined, m.body).id };
					case 'field': {
						if (!m.value)
							return { keyNodeId };
						if (m.modifiers?.includes('static')) {
							// A static field's initializer runs once, at definition time: resolved and wired into `anchor` as heritage and keys are.
							recurse.expression(m.value);
							const valueNode = this.getExprNode(m.value);
							connectValue(valueNode, 0, anchor, port++);
							return { keyNodeId, valueNodeId: valueNode.id };
						}
						// An INSTANCE field's initializer runs once per `new`: its own function subgraph (no params, `m.value` as an expression body), whose resolved
						// value `resolveFieldInitializer` reads off the return node's port 1.
						return { keyNodeId, entryNodeId: this.buildFunctionBody(recurse, undefined, m.value).id };
					}
					default:
						// 'index_signature' has no runtime code at all (a type-only member).
						return { keyNodeId };
				}

			}),
		};
	}
}

// A destructuring desugared into flat var_decls off `valueExpr`, which MUST be a stable reference (a pattern reads it several times). transform.ts's
// version, shared with codegen; it throws on two rare gaps (object rest, computed key), caught here.
function patternBindings(kind: JS.DeclarationKind, target: JS.BindingTarget, valueExpr: Expr): Stmt[] {
	try {
		return buildPatternBindings(kind, target, valueExpr);
	} catch (e) {
		console.log(`not handling destructuring pattern: ${e}`);
		return [];
	}
}

// ===================================================================
//  Reconstruction
// ===================================================================

// Wraps a reconstructed statement in `export `/`export default `, per a node's own `exported` stamp.
function wrapExported(stmt: Stmt, exported: 'named' | 'default' | undefined): Stmt {
	return exported === 'named' ? { type: 'export_decl', declaration: stmt } as Stmt
		: exported === 'default' ? { type: 'export', default: stmt } as Stmt
		: stmt;
}

export class TSEmitter extends Emitter<Expr, Stmt, Type> {
	constructor(graph: VSDG, blocks?: BlockTree, blockIds?: Map<NodeId, string>) {
		super(graph, tsDialect, blocks, blockIds);
	}

	// ---- statement constructors ----

	// `undefined` is no body (an absent `else`); an EMPTY array a genuinely empty one, which a braced block still spells.
	makeBlock(body: Stmt[] | undefined) { return body === undefined ? undefined : Block(...body); }

	// A JS/C body is ONE statement (a `Block` when braced, so the distinction survives): the dialect wraps, not the core.
	makeSwitch(discriminant: Expr, cases: { test?: Expr, consequent: Stmt[] }[]): Stmt {
		return JS.Switch(discriminant, ...cases);
	}
	// js's `catch (e)` binds a name and matches nothing, so the handler's type is always undefined.
	makeTry(body: Stmt[], handler: { param?: string, type?: Expr, body: Stmt[] }, finalizer?: Stmt[]): Stmt {
		return { type: 'try', body, handlers: [{ param: handler.param, body: handler.body }], finalizer } as Stmt;
	}
	makeThrow(argument: Expr): Stmt			{ return { type: 'throw', argument }; }
	makeTempDecl(name: string, value: Expr): Stmt { return JS.VarDecl('var', JS.Var(name, value)); }

	// ---- whole statements the core anchors on ----

	emitPassthru(node: NOf<'passthru'>): Stmt {
		return wrapExported(node.stmt, node.exported);
	}
	rebuildClassDecl(node: NOf<'class_decl'>): Stmt {
		return wrapExported(this.rebuildClass(node.stmt, node.classInfo!) as Stmt, node.exported);
	}
	rebuildFunctionDecl(node: NOf<'function'>, body: Stmt[]): Stmt {
		return wrapExported({ ...this.rebuildParams(node.stmt as JS.FunctionDecl<Type>, node), body } as Stmt, node.exported);
	}
	// A named slot's own printed statement: a declaration, a first assignment, or a reassignment.
	emitNamedSlot(name: string, node: N): Stmt | undefined {
		const first = !this.names.has(name);
		this.names.add(name);

		const slot = (): Stmt | undefined => {
			if (node.type === 'var') {
				const declKind = node.declKind as JS.DeclarationKind;
				if (!node.inputs[0])
					return JS.VarDecl(declKind, JS.Var(name, undefined, node.typeAnnotation));

				const forced = this.hasForcedSibling(name, node.id);
				// The initializer need not print under the name: nothing reads it, or its sole reader recomputes the pure initializer (an effectful dead one
				// still runs, as an effect). A forced sibling reads it by name, so then it keeps its value.
				if (!this.graph.hasRealConsumer(node) || (this.isInlinableVarDecl(node) && !forced)) {
					// A bare `let x;` only when the binding is still needed (an export, a forced sibling); `const x;` is invalid, so `let`.
					return node.exported || forced
						? JS.VarDecl(node.declKind === 'const' ? 'let' : declKind, JS.Var(name, undefined, node.typeAnnotation))
						: undefined;
				}
				// The FIRST emit of a source variable is its declaration, later ones plain reassignments.
				const expr = this.resolveOperand(node.id, 0);
				return first
					? JS.VarDecl(declKind, JS.Var(name, expr, node.typeAnnotation))
					: ExprStmt(Assign<Expr, JS.assignableOps>(Identifier(name), expr));
			}
			if ((node.type === 'mutation' && node.expr.type === 'unary') || node.type === 'unary_post') {
				// A ++/-- already assigns: printed bare (`i++;`), never as `i = i++;`.
				return ExprStmt(this.rebuildPayload(node));
			}
			return ExprStmt(Assign<Expr, JS.assignableOps>(Identifier(name), this.buildExpr(node)));
		};

		const stmt = slot();
		return stmt && wrapExported(stmt, node.exported);
	}

	// ---- expressions ----

	rebuildPayload(node: N): Expr {
		switch (node.type) {
			case 'unary_post':
				return { ...(node.expr as Extract<Expr, {type: 'unary_post'}>), operand: this.resolveTarget(node.id, 0) };
			case 'unary_post_old':
				// resolveOperand, NOT resolveTarget: the snapshot freezes the value BEFORE the increment, sharing the target's read, not reading it again.
				return this.resolveOperand(node.id, 0);
			case 'member':
				return JS.Member(this.resolveOperand(node.id, 0), node.name, node.optional);
			case 'floating':
				return this.rebuildFloating(node, node.expr);
			case 'mutation':
				return this.rebuildMutationValue(node);
			case 'effect':
				return this.rebuildEffect(node);
		}
		console.log(`not handling value node ${node.type}`);
		return Literal(null);
	}

	// A mutation read as a VALUE: only its value, a member/index target rebuilt fresh (resolveTarget).
	rebuildMutationValue(node: NOf<'mutation'>): Expr {
		const expr = node.expr;
		switch (expr.type) {
			case 'unary':
				return { ...expr, operand: this.resolveTarget(node.id, 0) };
			// The base operator is stored on the node now, so no `=` has to be sliced back off.
			case 'assign': {
				const right = this.resolveOperand(node.id, 1);
				return expr.operator
					? Binary(expr.operator, this.resolveTarget(node.id, 0), right)
					: right;
			}
		}
		console.log(`not handling value node ${node.type}`);
		return Literal(null);
	}

	rebuildMutationStatement(node: NOf<'mutation'>): Stmt {
		const expr = node.expr;
		return ExprStmt(node.plainAssign && expr.type === 'assign'
			? { ...expr, target: this.resolveTarget(node.id, 0), value: this.resolveOperand(node.id, 1) }
			: this.rebuildPayload(node));
	}

	// Every pure value-producing expression is 'floating' (`makeExprNode`), so `node.expr`'s type picks the shape.
	rebuildFloating(node: N, expr: Expr): Expr {
		switch (expr.type) {
			case 'literal':
			case 'import_meta':
			case 'this':
			case 'super':		return expr;
			case 'unary':		return { ...expr, operand: this.resolveOperand(node.id, 0) };
			case 'array':		return { ...expr, elements: expr.elements.map((elem, i) => elem ? this.resolveOperand(node.id, i) : elem) };
			case 'object':		return this.buildObjectExpr(node, expr);
			case 'spread':		return { ...expr, operand: this.resolveOperand(node.id, 0) };
			case 'binary':		return { ...expr, left: this.resolveOperand(node.id, 0), right: this.resolveOperand(node.id, 1) };
			case 'conditional':	return this.buildConditional(node);
			case 'index':		return { ...expr, object: this.resolveOperand(node.id, 0), index: this.resolveOperand(node.id, 1) };
			case 'call':		return { ...expr, arguments: expr.arguments.map((_, i) => this.resolveOperand(node.id, i + 1)) };
		}
		console.log(`not handling value node ${expr.type}`);
		return Literal(null);
	}

	// Shared by the floating and effect paths: what matters is whether classInfo has a resolved body for a property.
	buildObjectExpr(node: N, expr: Expr & {type: 'object'}): Expr {
		return {
			...expr,
			properties: expr.properties.map((prop, i) => {
				if (prop.type === 'spread')
					return { ...prop, operand: this.resolveOperand(node.id, i) };
				const mi = node.classInfo?.members[i];
				if (mi?.entryNodeId)
					return { ...prop, body: this.rebuildFunctionBody(this.graph.getNode(mi.entryNodeId) as NOf<'function'>) as JS.Stmt<Type>[] };
				return prop.type === 'field' && typeof prop.key !== 'object' ? { ...prop, value: this.resolveOperand(node.id, i) } : prop;
			}),
		};
	}

	rebuildEffect(node: NOf<'effect'>): Expr {
		const value = node.expr;
		switch (value.type) {
			// `await x` always has an operand, threaded at port 1: the resolved one prints.
			case 'await':
				return { ...value, operand: this.resolveOperand(node.id, 1) };
			// A method-bearing object literal, through the same helper: classInfo needs the graph, not the tag.
			case 'object':
				return this.buildObjectExpr(node, value);
			case 'yield':
				return { ...value, operand: value.operand ? this.resolveOperand(node.id, 1) : undefined };
			case 'tagged_template':
				return { ...value, quasi: value.quasi.map((part, i) => part.exp ? { ...part, exp: this.resolveOperand(node.id, i + 1) } : part) };
			case 'import_call':
				return { ...value, arguments: value.arguments.map((_, i) => this.resolveOperand(node.id, i + 1)) };
			case 'class':
				return node.classInfo ? this.rebuildClass(value, node.classInfo) : value;
			case 'jsx': {
				let port = 1;
				return {
					...value,
					attributes: value.attributes.map(a => a.value ? { ...a, value: this.resolveOperand(node.id, port++) } : a),
					children: value.children.map(() => this.resolveOperand(node.id, port++)),
				};
			}
			case 'call': case 'new': {
				// A call's callee prints raw, wrong only when it embeds an effect (`new Point(3,4).sum()`), which the graph threads as its own node:
				// the counting edge reaches that node instead.
				const calleeEdge = node.inputs[value.arguments.length + 1];
				const calleeNode = calleeEdge && this.graph.get(calleeEdge.nodeId);
				// A pure callee may have materialized as a named temp (hoisted loop-invariant): that temp prints, not the raw source.
				const calleeTemp = calleeNode && this.nodeVariableNames.get(calleeNode.id);
				const callee = calleeTemp ? Identifier(calleeTemp)
					: calleeNode && !this.graph.isPureSubgraph(calleeNode) ? this.resolveNode(calleeNode.id) : value.callee;
				return { ...value, callee, arguments: value.arguments.map((_, i) => this.resolveOperand(node.id, i + 1)) };
			}
			default:
				return value;	// can't get here
		}
	}

	// ---- class / signature reconstruction ----

	// A destructured param prints as its hidden temp in the SIGNATURE too (`destructuredParams`).
	rebuildParams<T extends JS.Params<Type>>(raw: T, entryNode: NOf<'function'>): T {
		if (!entryNode.destructuredParams)
			return raw;
		const rebuildKey = <P extends { key: JS.BindingTarget }>(p: P): P => {
			const tempName = entryNode.destructuredParams!.get(p.key);
			return tempName !== undefined ? { ...p, key: tempName } : p;
		};
		return { ...raw, params: raw.params.map(rebuildKey), rest: raw.rest && rebuildKey(raw.rest) };
	}

	// Splices VSDG's resolution of heritage, keys and method bodies into the otherwise verbatim member list; a class expression and a class_decl
	// both arrive, differing only in fields this never touches.
	rebuildClass(raw: any, info: ClassInfo): any {
		return {
			...raw,
			superClass: info.superClassNodeId ? this.resolveNode(info.superClassNodeId) : raw.superClass,
			body: raw.body.map((m: any, i: number) => {
				const mi = info.members[i];
				if (!mi)
					return m;
				const withKey = mi.keyNodeId ? { ...m, key: { computed: this.resolveNode(mi.keyNodeId) } } : m;
				if (mi.valueNodeId)
					return { ...withKey, value: this.resolveNode(mi.valueNodeId) };
				if (m.type === 'field')
					return mi.entryNodeId
						? { ...withKey, value: this.resolveOperand((this.graph.getNode(mi.entryNodeId) as NOf<'function'>).returnNodeId, 1) }
						: withKey;
				if (!mi.entryNodeId)
					return withKey;
				const entryNode = this.graph.getNode(mi.entryNodeId) as NOf<'function'>;
				return { ...this.rebuildParams(withKey, entryNode), body: this.rebuildFunctionBody(entryNode) };
			}),
		};
	}
}

// ===================================================================
//  The pipeline
// ===================================================================

export function BuildVSDG(ast: readonly Stmt[]): VSDG {
	const builder = new TSBuilder();
	builder.build(ast);
	return builder.finish();
}

export function Optimize(graph: VSDG): void {
	optimize(graph, tsDialect);
}

export function BuildProgram(
	graph:		VSDG,
	blocks?:	BlockTree,
	blockIds?:	Map<NodeId, string>
): Stmt[] {
	return new TSEmitter(graph, blocks, blockIds).build();
}

// Kept for callers that drive CSE directly; `Optimize` runs it as its own final round.
export function optimizeStructuralCSE(graph: VSDG, protectedIds: Set<NodeId>): boolean {
	return structuralCSE(graph, tsDialect, protectedIds);
}
