// ===================================================================
//  The C++ half of the language-neutral VSDG.
// ===================================================================
// The same three pieces as ts/vsdg.ts and py/vsdg.ts (`CPPDialect`, `CPPBuilder`, `CPPEmitter`, printed by cpp/printer.ts) and the pipeline
// entry points. Where C++ differs:
//   * the top level is DEFINITIONS: `S` is `TopLevel = Definition | Stmt`, bridged in `walkerB` (DEFINITION_ONLY);
//   * a declaration carries its TYPE (a `var` node's `T` is its `DeclarationSpec`), which can never be invented, so an assignment to an
//     unmodelled name prints as an assignment, not a declaration;
//   * assignment is an EXPRESSION and `++`/`--` are mutations, never pure values; a body is ONE `Block`, handed over as a one-element list.
// Not modelled, printed verbatim (correct, everything they mention kept read): classes/templates/namespaces/`using`, typedefs, `goto`/labels,
// `throw`/`try`, range-`for`, initializer lists, non-name declarators (`int *p`), and `new`/`delete`/casts/`typeid`/`alignof`. `++`/`--` print
// verbatim too, but the name they rewrite IS re-bound (`lowerUnmodelledMutation`). Constant folding uses C++'s arithmetic type model (walker.ts).

import * as C from './c-parser';
import * as CPP from './cpp-parser';
import * as Common from '@isopodlabs/tison/ast';
import { walkerB, isExpr, isPackParameter, calcBinary, calcUnary, Scalar, scalarFor, spellScalar } from './walker';
import { printer as cppPrinterFactory } from './printer';
import {
	Dialect, VSDGBuilder, Emitter, Recurse, ParamSlot, SwitchSyntax,
	Node, NodeOf, NodeType, NodeId, Scope, VSDG, BlockTree,
	connectValue, slotName,
	optimize, optimizeStructuralCSE as structuralCSE
} from '../vsdg';

type Expr		= CPP.Expr;
type Stmt		= CPP.Stmt;
type Definition	= CPP.Definition;
// What one top-level item is: `BuildVSDG` is handed a module body, `BuildProgram` hands one back.
type TopLevel	= Definition | Stmt;
// The `var` node's own `T`: everything needed to print a declaration's type, storage class included.
type Spec		= CPP.DeclarationSpec;
type FunctionDef = C.FunctionDef<CPP.Declarator, CPP.TypeSpecifierExt, Expr, Stmt>;

type N			= Node<Expr, TopLevel, Spec>;
type NOf<K extends NodeType> = NodeOf<Expr, TopLevel, Spec, K>;

// ===================================================================
//  Which top-level items are definitions
// ===================================================================
// The walker keeps definitions and statements apart; only tags that CANNOT be a statement go to the definition walker (`declaration`,
// `typedef`, `static_assert`, `using` are in both unions, handled alike).
const DEFINITION_ONLY = new Set<string>([
	'function_def', 'namespace', 'linkage', 'template', 'method_def', 'operator_def', 'constructor_def', 'destructor_def', 'static_member_def',
]);

export function isDefinition(s: TopLevel): s is Definition {
	return DEFINITION_ONLY.has(s.type);
}


// ===================================================================
//  Dialect
// ===================================================================

let printerInstance: ReturnType<typeof cppPrinterFactory> | undefined;
const cppPrinter = () => (printerInstance ??= cppPrinterFactory());

function MaybeLiteral(value: unknown) {
	if (value === undefined)
		return undefined;
	// A folded scalar spells itself from its type; the core's own values reach here too (a rotated loop's `literal(true)`, buildExpr's `null`).
	if (typeof value === 'boolean')
		return Common.Literal(value);
	const s = value as Scalar | null;
	return s && typeof s === 'object' && 'kind' in s
		? (s.kind === 'bool' ? Common.Literal(s.value !== 0) : Common.Literal(s.value, spellScalar(s)))
		: Common.Literal(value as number | string);
}


export const cppDialect: Dialect<Expr, TopLevel, Spec> =  {
	identifierName(e) {
		return e.type === 'identifier' ? e.name : undefined;
	},
	identifier(name) {
		return Common.Identifier(name);
	},
	exprKey(e) {
		return cppPrinter().expression(e);
	},
	stmtKey(s) {
		return isDefinition(s)
			? cppPrinter().definition(s)
			: cppPrinter().statement(s);
	},
	isCSEUnsafe(node) {
		// A read an intervening mutation can change while its text stays identical: `a[i]` (a user `operator[]`), `this`, `A::b`. `a.b` never
		// reaches here: CSE skips 'member'.
		return node.type === 'floating'
			&& (['index', 'this', 'qualified'] as Expr['type'][]).includes(node.expr.type);
	},
	foldable(e) {
		// Shape only: which OPERATORS actually fold is `foldValue`'s own answer (see foldBinary).
		return	e.type === 'binary' ? 2
			:	e.type === 'unary' ? 1
			:	0;
	},
	fold(e, ops) {
		// Every operand reached here through `literalValue`, so each one is a `Scalar`.
		return	e.type === 'binary'	? MaybeLiteral(calcBinary(e.operator, ops[0] as Scalar, ops[1] as Scalar))
			:	e.type === 'unary'	? MaybeLiteral(calcUnary(e.operator, ops[0] as Scalar))
			: undefined;
	},
	// A constant: a literal (its spelling is its type; `true`/`false` are `bool`), and `'a'`, an `int` after promotion. A string literal is a
	// pointer, `nullptr` has no value, and `sizeof(T)` needs declarations this AST never resolves.
	literalValue(e) {
		if (e.type === 'char_literal')
			return e.value.length === 1 ? { kind: 'int', value: e.value.charCodeAt(0) & 0xFF } : undefined;
		return	e.type !== 'literal'			? undefined
			:	typeof e.value === 'boolean'	? { kind: 'bool', value: e.value ? 1 : 0 }
			:	typeof e.value === 'number'		? scalarFor(e.value, e.raw)
			:	undefined;
	},
	// C++'s zero is falsy for every scalar kind -- including the `0.0` a float carries, and the 0 a folded `false` does.
	truthy(value) {
		return value !== undefined && (value as Scalar).value !== 0;
	},
	isCalleeEdge(consumer, port) {
		const v = consumer.type === 'effect' && consumer.expr;
		return !!v && v.type === 'call' && port === v.arguments.length + 1;
	}
};


// ===================================================================
//  Lowering
// ===================================================================

// A parameter's name from whatever declarator spelled it (through pointer/array/reference wrappers, `int *p` binds `p`); unnamed binds nothing.
// c-parser's own `declaratorName` is typed against its narrower declarator.
function declaratorName(d: CPP.Declarator): string {
	switch (d.type) {
		case 'identifier':			return d.name;
		case 'pointer':
		case 'reference':
		case 'rvalue_reference':	return declaratorName(d.to);
		case 'array':				return declaratorName(d.element);
		case 'function':			return declaratorName(d.name);
		default:					throw new Error(`vsdg/cpp: no name behind declarator ${(d as {type: string}).type}`);
	}
}

/** The type of switch's hidden helpers: C++ has no keyword-less declaration (`makeTempDecl`), and the source spells none. */
const AUTO: Spec = { type: C.RefType('auto') };

/** C's switch body is a FLAT list (`case 1: g(); break;` is three siblings, the label holding only its first statement): regrouped per case,
*  as transpile.ts's `cppSwitchToTs` does. Undefined for a shape that will not regroup (a statement before the first label), left verbatim. */
function switchCasesOf(s: Stmt & { type: 'switch' }): { test?: Expr, body: Stmt[] }[] | undefined {
	if (s.body.type !== 'block')
		return undefined;
	const cases: { test?: Expr, body: Stmt[] }[] = [];
	let sawDefault = false;
	const add = (item: TopLevel): boolean => {
		if (item.type === 'case' || item.type === 'default') {
			if (item.type === 'default' && sawDefault)
				return false;
			sawDefault ||= item.type === 'default';
			cases.push({ test: item.type === 'case' ? item.test : undefined, body: [] });
			return add(item.body);
		}
		if (cases.length === 0)
			return false;
		cases[cases.length - 1].body.push(item as Stmt);
		return true;
	};
	for (const item of s.body.body)
		if (!add(item))
			return undefined;
	return cases;
}

function paramSlots(declarator: CPP.Declarator): ParamSlot[] | undefined {
	return declarator.type === 'function' ? paramSlotsOf(declarator.params) : undefined;
}

/** The same, for a parameter list no declarator wraps -- a lambda's own. */
function paramSlotsOf(params: readonly CPP.ParamDecl[]): ParamSlot[] {
	const slots: ParamSlot[] = [];
	for (const p of params) {
		if (isPackParameter(p))
			continue;
		if (p.declarator)
			slots.push({ name: declaratorName(p.declarator) });
	}
	return slots;
}

export class CPPBuilder extends VSDGBuilder<Expr, TopLevel, Spec> implements SwitchSyntax<Expr, TopLevel, Spec> {
	constructor() { super(cppDialect); }

	build(ast: readonly Definition[]) {
		const w = walkerB(
			(d, process, recurse) => this.lowerDefinition(d, process, recurse),
			(s, process, recurse) => this.lowerStatement(s, process, recurse),
			(e, process, recurse) => this.lowerExpression(e, process, recurse)
		);
		return ast.some(x => isDefinition(x) ? w.definition(x) : w.statement(x));
	}

	lowerDefinition(d: Definition, process: (d: Definition) => boolean, recurse: Recurse<Expr, TopLevel>): boolean {
		if (d.type === 'function_def' && this.modellable(d)) {
			// The body is one `Block`: as a one-element list it reaches the builder's 'block' case, which gives it its own scope.
			const fn = this.buildFunctionBody(recurse, paramSlots(d.declarator), [d.body]);
			fn.stmt = d;
			this.end = fn;
			return false;
		}
		console.log(`not handling definition ${(d as {type: string}).type}`);
		return this.lowerVerbatim(d, () => process(d));
	}

	// A plain function whose parameters are all bindable names; a parameter DEFAULT appears only in the verbatim signature, so a name it mentions
	// would look unread and be elided.
	private modellable(d: FunctionDef): boolean {
		if (d.declarator.type !== 'function')
			return false;
		for (const p of d.declarator.params)
			if (isPackParameter(p) || p.default)
				return false;
		return true;
	}

	lowerStatement(s: TopLevel, process: (s: Stmt) => boolean, recurse: Recurse<Expr, TopLevel>): boolean {
		// c-parser keeps BOTH readings of an ambiguous construct (`S *p = 0;` as a declaration and a multiplication) as a nested list: ALTERNATIVES,
		// not a sequence. The first is taken, the only one a printer could emit.
		if (Array.isArray(s)) {
			console.log(`ambiguous statement: ${s.length} readings, taking the first`);
			if (s.length)
				recurse.statement(s[0] as TopLevel);
			return false;
		}
		// Everything else IS a statement: `walkerB` routed the definition-only tags to `lowerDefinition`.
		const stmt = s as Stmt;
		switch (stmt.type) {
			case 'declaration':
				if (this.lowerDeclaration(recurse, stmt))
					return false;
				console.log(`not handling declaration`);
				return this.lowerVerbatim(stmt, () => process(stmt));

			case 'block':
				this.scope = new Scope(this.scope);
				process(stmt);
				this.scope = this.scope.closeAndFlush()!;
				return false;

			case 'if': {
				recurse.expression(stmt.test);
				const test		= this.getExprNode(stmt.test);
				const parent	= this.getState();
				const trueState		= this.walkBranch(parent, () => recurse.statement(stmt.consequent));
				const falseState	= this.walkBranch(parent, () => { if (stmt.alternate) recurse.statement(stmt.alternate); });
				this.mergeState(parent, test, trueState, falseState);
				this.reconcileVariables(parent, test, trueState, falseState);
				return false;
			}

			case 'while':
				this.buildLoop(recurse, stmt.test, () => recurse.statement(stmt.body), false);
				return false;

			case 'do_while':
				// The body runs BEFORE the test (the mu's initial value is what it sees first).
				this.buildLoop(recurse, stmt.test, () => recurse.statement(stmt.body), true);
				return false;

			case 'switch': {
				const cases = switchCasesOf(stmt);
				// An empty switch, or one that will not regroup, stays verbatim, without hidden helpers declared for nothing.
				if (!cases?.length) {
					console.log(`not handling switch body`);
					return this.lowerVerbatim(stmt, () => process(stmt));
				}
				this.buildSwitch(recurse, stmt.discriminant, cases.map(c => ({
					test: c.test,
					body: () => { for (const s of c.body) recurse.statement(s); },
				})), this);
				return false;
			}

			case 'for': {
				// `init` once, then `while (test) { body; update; }`, `update` on the body's non-`continue` tail, as TS's lowering does.
				if (stmt.init) {
					if (isExpr(stmt.init))
						recurse.expression(stmt.init);
					else
						recurse.statement(stmt.init);	// a declaration in the init clause
				}
				const test	= stmt.test ?? Common.Literal(1);
				const body: Stmt = stmt.update ? Common.Block<Stmt>(stmt.body, Common.ExprStmt(stmt.update)) : stmt.body;
				this.buildLoop(recurse, test, () => recurse.statement(body), false, stmt.update);
				return false;
			}

			case 'return': {
				// The marker carries its value at port 1 (unconnected for a bare `return;`); `exited` makes an enclosing `if` build a real gamma.
				if (stmt.argument)
					recurse.expression(stmt.argument);
				const marker = this.makeMarker('EARLY_RETURN_MARKER');
				this.connectEnd(marker);
				if (stmt.argument)
					connectValue(this.getExprNode(stmt.argument), 0, marker, 1);
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

			case 'empty':
				return false;

			case 'expression':
				// A call reaches the state chain from `lowerExpression`'s 'call' case; anything with no effect is dead and drops.
				break;

			default:
				// Everything else prints verbatim, what it mentions kept read by the descent.
				console.log(`not handling statement ${(stmt as {type: string}).type}`);
				return this.lowerVerbatim(stmt, () => process(stmt));
		}
		return process(stmt);
	}

	// `int x = 1;`: one binding per declarator, each printing as its own declaration. `int *p = ...` needs a TYPE rewrite the declarator model
	// lacks, and `int x;` has no value to bind yet must print: both stay verbatim.
	private lowerDeclaration(recurse: Recurse<Expr, TopLevel>, s: Stmt & { type: 'declaration' }): boolean {
		const declarators = s.initDeclarators;
		if (!declarators?.length)
			return false;
		for (const d of declarators)
			if (!('declarator' in d) || d.declarator.type !== 'identifier' || !d.initializer || !isExpr(d.initializer))
				return false;

		// Walked THEN bound, one declarator at a time, left to right (`int i = 0, e = i + 1;`).
		for (const d of declarators as { declarator: Common.Identifier, initializer: Expr }[]) {
			recurse.expression(d.initializer);
			const varNode = this.makeNode({ type: 'var', name: d.declarator.name });
			connectValue(this.getExprNode(d.initializer), 0, varNode, 0);
			// The declaration's type, replayed by `emitNamedSlot`. No declKind: `isInlinableVarDecl` would read it as "elidable", making an assignment's
			// TARGET resolve to the initializer (`0 = 1`); `typeAnnotation` and `nameStoredTo` keep the declaration printed.
			varNode.typeAnnotation = s.specifiers;
			this.bindVar(varNode);
		}
		return true;
	}

	// Every assignment, statement or subexpression: a 'mutation', whose target's location decides what else it needs.
	private lowerAssign(recurse: Recurse<Expr, TopLevel>, e: Common.Assign<Expr, C.assignableOps>): boolean {
		recurse.expression(e.target);
		recurse.expression(e.value);
		const node = this.makeExprNode(e, 'mutation');
		node.plainAssign = e.operator === undefined;
		connectValue(this.getExprNode(e.target), 0, node, 0);
		connectValue(this.getExprNode(e.value), 0, node, 1);

		if (e.target.type === 'identifier') {
			const fresh = this.scope.get(e.target.name) === undefined;
			// A name never seen declared (a global, or one a verbatim statement declares) is read by NAME, so a store to it always prints, as a plain
			// assignment: its type is what is unknown.
			if (fresh || !this.scope.isLocalToCurrentFunction(e.target.name))
				node.forcedPrint = true;
			this.rebindVar(e.target.name, node, fresh);
		} else {
			// A member/subscript target mutates outside this pass's scope tracking: it prints whatever its consumer count.
			node.forcedPrint = true;
			this.threadMutation(node);
		}
		return false;
	}

	// A name mentioned only in TEXT the graph never prints (a verbatim statement, a lambda's captures) needs a READER, or its declaration is elided.
	private readOnly(e: Expr) {
		connectValue(this.getExprNode(e), 0, this.makeExprNode(e), 0);
	}

	/**
	* An unmodelled `++`/`--`: an opaque effect printed in place. Rewriting it is unsafe (a user `operator++` is a call whose old value is a COPY),
	* but the name it rewrites is re-bound, so CSE cannot merge a read before it with one after (`g(i * 2); i++; h(i * 2);`).
	*/
	private lowerUnmodelledMutation(e: { type: 'unary' | 'unary_post', operand: Expr } & Expr): false {
		console.log(`not handling expression ${e.type}`);
		const node = this.makeExprNode(e, 'effect');
		this.connectEnd(node);

		const name = this.dialect.identifierName(e.operand);
		if (name !== undefined) {
			// The operand is a real READ of `name` (port 1, never read as the payload prints verbatim): without it a later `i++` would not depend on this one.
			connectValue(this.getExprNode(e.operand), 0, node, 1);
			// A name-only 'var' like an import binding, never `bound`, resolved by name; its threadMutation anchor orders those reads after this increment.
			const alias = this.makeNode({ type: 'var', name });
			this.threadMutation(alias);
			this.scope.set(name, alias);
			// A builtin `++`/`--` only rewrites the name, so with no reader of the binding the core drops it as a dead write. Whether `operator++` is the
			// builtin is a TYPES question: "builtin" is the documented assumption (as `pure<name>` is for calls); a member/index target claims nothing.
			node.mutatesBindingId = alias.id;
		}
		return false;
	}

	// ---- SwitchSyntax: C++'s own spelling of switch's fixed scaffolding (the walk is the core's) ----

	local(value: Expr, name: string) {
		const node = this.makeNode({ type: 'var', name, typeAnnotation: AUTO });
		connectValue(this.getExprNode(value), 0, node, 0);
		return node;
	}
	comparison(discName: string, test: Expr): Expr {
		return Common.Binary<Expr, C.binaryOps>('==', Common.Identifier(discName), test);
	}
	// `default` matches iff none of the OTHER cases did, wherever it sits.
	condition(hitName: string, matchName: string | undefined, otherMatches: string[]): Expr {
		const hit = Common.Identifier(hitName);
		if (matchName !== undefined)
			return Common.Binary<Expr, C.binaryOps>('||', hit, Common.Identifier(matchName));
		return Common.Binary<Expr, C.binaryOps>('||', hit, otherMatches.length === 0
			? Common.Literal(true)
			: Common.Unary<Expr, C.unaryOps>('!', otherMatches.map((n): Expr => Common.Identifier(n))
				.reduce((a, b) => Common.Binary<Expr, C.binaryOps>('||', a, b))));
	}
	setHit(hitName: string): Expr {
		return Common.Assign<Expr, C.assignableOps>(Common.Identifier(hitName), Common.Literal(true));
	}

	lowerExpression(e: Expr, process: (e: Expr) => boolean, recurse: Recurse<Expr, TopLevel>): boolean {
		switch (e.type) {
			case 'identifier':
				// A verbatim statement mentions this name in text: the mention must look like a READ, or a declaration it depends on is elided (`int x = 1;
				// switch (x) {...}`). Created inside a verbatim descent, the reader is `suppressed` and never prints.
				if (this.verbatim)
					this.readOnly(e);
				return false;

			case 'literal': {
				process(e);
				this.makeExprNode(e);
				return false;
			}

			case 'char_literal':
			case 'sizeof_type':
			case 'null_literal':
			case 'this':
			case 'qualified':
				// A leaf: `'a'` IS a constant (`literalValue`), `sizeof(T)`/`nullptr` are not; `this`/`A::b` are CSE-unsafe.
				process(e);
				this.makeExprNode(e);
				return false;

			case 'unary': {
				process(e);
				// `++x`/`--x` mutate, so they must never be mistaken for a pure value.
				if (e.operator === '++' || e.operator === '--')
					return this.lowerUnmodelledMutation(e);
				connectValue(this.getExprNode(e.operand), 0, this.makeExprNode(e), 0);
				return false;
			}

			case 'unary_post':
				// Likewise, and their value is the PRE-mutation one, which C++ gives no safe way to rewrite (`lowerUnmodelledMutation`).
				process(e);
				return this.lowerUnmodelledMutation(e);

			case 'binary': {
				process(e);
				const node = this.makeExprNode(e);
				connectValue(this.getExprNode(e.left), 0, node, 0);
				connectValue(this.getExprNode(e.right), 0, node, 1);
				return false;
			}

			case 'assign':
				return this.lowerAssign(recurse, e);

			case 'lambda': {
				// A definition's 'function' entry with `.expr` set: the lambda's text prints verbatim as a VALUE, its BODY lowered into its own region
				// (descending here would print the body's statements in the enclosing function).
				const entry = this.buildFunctionBody(recurse, paramSlotsOf(e.params), [e.body]);
				entry.expr = e;
				this.expnodes.set(e, entry);
				this.end = entry;
				// A name only the lambda's text mentions (an unread capture, a parameter default) needs a reader, or its declaration is elided.
				for (const c of e.captures) {
					if (c.init)
						recurse.expression(c.init);
					if (c.name)
						this.readOnly(Common.Identifier(c.name));
				}
				for (const p of e.params)
					if (!isPackParameter(p) && p.default)
						recurse.expression(p.default);
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

			case 'index': {
				process(e);
				const node = this.makeExprNode(e);
				node.freshTarget = true;
				connectValue(this.getExprNode(e.object), 0, node, 0);
				connectValue(this.getExprNode(e.index), 0, node, 1);
				return false;
			}

			case 'member':
			case 'pointer_member': {
				// One tag for `.` and `->`, the operator a stamp; the whole expr is not kept, so `pointer_member` is recorded on the node.
				process(e);
				const node = this.makeNode({ type: 'member', name: e.property });
				if (e.type === 'pointer_member')
					node.pointerMember = true;
				node.freshTarget = true;
				this.expnodes.set(e, node);
				connectValue(this.getExprNode(e.object), 0, node, 0);
				return false;
			}

			case 'cast': {
				// `(T)x`: pure, with the cast's own type kept in the payload and the operand threaded.
				process(e);
				connectValue(this.getExprNode(e.expression), 0, this.makeExprNode(e), 0);
				return false;
			}

			case 'call': {
				// As in TS/PY, a callee named `pure...` stands in for purity analysis; every other call is an effect.
				process(e);
				const pure = e.callee.type === 'identifier' && e.callee.name.startsWith('pure');
				const node = pure ? this.makeExprNode(e) : this.makeExprNode(e, 'effect');
				if (!pure)
					this.connectEnd(node);
				e.arguments.forEach((arg, i) => connectValue(this.getExprNode(arg), 0, node, i + 1));
				connectValue(this.getExprNode(e.callee), 0, node, e.arguments.length + 1);
				return false;
			}
		}

		// An unmodelled expression form: an effect, the only safe assumption about unknown evaluation order and purity, which also keeps it verbatim.
		console.log(`not handling expression ${(e as {type: string}).type}`);
		process(e);
		this.connectEnd(this.makeExprNode(e, 'effect'));
		return false;
	}
}

// ===================================================================
//  Reconstruction
// ===================================================================

export class CPPEmitter extends Emitter<Expr, TopLevel, Spec> {
	constructor(graph: VSDG, blocks?: BlockTree, blockIds?: Map<NodeId, string>) {
		super(graph, cppDialect, blocks, blockIds);
	}

	// A C++ body is ONE statement (a `Block` when braced), so the core's arrays are wrapped (py's bodies ARE arrays).

	makeBlock(body: TopLevel[] | undefined): Stmt | undefined {
		// A body slot never holds a definition; the cast is that contract, not a guess.
		return body === undefined ? undefined : Common.Block<Stmt>(...(body as Stmt[]));
	}
	private declaration(name: string, specifiers: Spec, value: Expr): TopLevel {
		return {
			type: 'declaration',
			specifiers,
			initDeclarators: [{ declarator: Common.Identifier(name), initializer: value }],
		} as TopLevel;
	}

	makeSwitch(discriminant: Expr, cases: { test?: Expr, consequent: TopLevel[] }[]): TopLevel {
		const body: TopLevel[] = [];
		// Labels waiting for a body: `case 1: case 2: g();` chains an empty case onto the next instead of printing `case 1: ;`.
		let open: Stmt[] = [];
		const close = (label: Stmt): Stmt => {
			let node: TopLevel = label;
			for (let i = open.length; i-- > 0;)
				node = { ...open[i], body: node } as Stmt;
			open = [];
			return node as Stmt;
		};

		for (const c of cases) {
			const label = (c.test ? { type: 'case', test: c.test } : { type: 'default' }) as unknown as Stmt;
			if (c.consequent.length === 0) {
				open.push(label);
				continue;
			}
			// C++ forbids jumping past an initialisation into its scope (`case 1: int y = 1; break; case 2:`), so such a case gets a block.
			if (c.consequent.some(st => (st as { type?: string }).type === 'declaration')) {
				body.push(close({ ...label, body: Common.Block<TopLevel>(...c.consequent) } as unknown as Stmt));
				continue;
			}
			const [first, ...rest] = c.consequent;
			body.push(close({ ...label, body: first } as unknown as Stmt), ...rest);
		}
		// A trailing empty case has nothing to chain onto; it still needs a statement to print.
		for (const label of open)
			body.push({ ...label, body: { type: 'empty' } } as unknown as Stmt);

		return { type: 'switch', discriminant, body: Common.Block<TopLevel>(...body) } as unknown as TopLevel;
	}
	makeTry(): TopLevel									{ throw new Error('vsdg/cpp: try is printed verbatim'); }
	makeThrow(argument: Expr): TopLevel					{ return { type: 'throw', argument }; }
	// C++ spells a temporary as `auto t0 = value;` -- there is no keyword-less declaration form.
	makeTempDecl(name: string, value: Expr): TopLevel	{ return this.declaration(name, { type: C.RefType('auto') }, value); }

	// ---- whole statements the core anchors on ----

	emitPassthru(node: NOf<'passthru'>): TopLevel {
		return node.stmt;
	}
	rebuildClassDecl(node: NOf<'class_decl'>): TopLevel {
		// A class is never modelled (it stays a passthru): reached only if a future lowering creates class_decl nodes.
		return node.stmt;
	}
	rebuildFunctionDecl(node: NOf<'function'>, body: TopLevel[]): TopLevel {
		return { ...(node.stmt as FunctionDef), body: this.makeBlock(body) } as TopLevel;
	}

	// A declaration when it carries its declared type, else a plain assignment (a binding made by assigning a name declared elsewhere).
	emitNamedSlot(name: string, node: N): TopLevel | undefined {
		this.names.add(name);

		if (node.type === 'var') {
			// An external name has no initializer to print: read by name wherever used.
			if (!node.inputs[0])
				return undefined;
			if (!this.graph.hasRealConsumer(node) && !this.nameStoredTo(name, node.id))
				return undefined;
			const value = this.resolveOperand(node.id, 0);
			return node.typeAnnotation !== undefined
				? this.declaration(name, node.typeAnnotation, value)
				: Common.ExprStmt(Common.Assign(Common.Identifier(name), value));
		}
		if (node.type === 'mutation')
			return this.rebuildMutationStatement(node);
		return Common.ExprStmt(Common.Assign(Common.Identifier(name), this.buildExpr(node)));
	}

	// Whether anything still names this variable as a STORE TARGET: C++ has no implicit declaration, so it must survive when nothing reads its value.
	// Scanned, since folding a constant branch bypasses the merge that held the name. A PARAMETER never matches.
	private nameStoredTo(name: string, excludeId: NodeId): boolean {
		for (const other of this.graph.values()) {
			if (other.id === excludeId)
				continue;
			if (slotName(other) === name)
				return true;
			const target = other.type === 'mutation' ? (other.expr as unknown as { target?: Expr }).target : undefined;
			if (target?.type === 'identifier' && target.name === name)
				return true;
		}
		return false;
	}

	// ---- expressions ----

	rebuildPayload(node: N): Expr {
		switch (node.type) {
			case 'floating':	return this.rebuildFloating(node as NOf<'floating'>);
			case 'mutation':	return this.rebuildMutationValue(node as NOf<'mutation'>);
			case 'effect':		return this.rebuildEffect(node as NOf<'effect'>);
			case 'member': {
				const object = this.resolveOperand(node.id, 0);
				return node.pointerMember
					? { type: 'pointer_member', object, property: node.name } as Expr
					: Common.Member(object, node.name);
			}
		}
		console.log(`not handling value node ${node.type}`);
		return Common.Literal(0);
	}

	private rebuildFloating(node: NOf<'floating'>): Expr {
		const e = node.expr;
		switch (e.type) {
			case 'identifier':
			case 'literal':
			case 'char_literal':
			case 'sizeof_type':
			case 'null_literal':
			case 'this':
			case 'qualified':
				return e;	// leaf: nothing in the graph to put back, the payload prints as-is
			case 'unary':
				return { ...e, operand: this.resolveOperand(node.id, 0) };
			case 'binary':
				return { ...e, left: this.resolveOperand(node.id, 0), right: this.resolveOperand(node.id, 1) };
			case 'conditional':
				return this.buildConditional(node);
			case 'index':
				return { ...e, object: this.resolveOperand(node.id, 0), index: this.resolveOperand(node.id, 1) };
			case 'cast':
				return { ...e, expression: this.resolveOperand(node.id, 0) };
		}
		console.log(`not handling value node ${(e as {type: string}).type}`);
		return Common.Literal(0);
	}

	private rebuildMutationValue(node: NOf<'mutation'>): Expr {
		const e = node.expr as Common.Assign<Expr, C.assignableOps>;
		return Common.Assign(this.resolveTarget(node.id, 0), this.resolveOperand(node.id, 1), e.operator);
	}

	rebuildMutationStatement(node: NOf<'mutation'>): TopLevel {
		return Common.ExprStmt(this.rebuildMutationValue(node));
	}

	private rebuildEffect(node: NOf<'effect'>): Expr {
		const e = node.expr;
		if (e.type === 'call') {
			// The callee prints raw, unless it embeds an effect (or was hoisted into a temp), which raw source would run again.
			const calleeEdge	= node.inputs[e.arguments.length + 1];
			const calleeNode	= calleeEdge && this.graph.get(calleeEdge.nodeId);
			const calleeTemp	= calleeNode && this.nodeVariableNames.get(calleeNode.id);
			const callee		= calleeTemp
				? Common.Identifier(calleeTemp)
				: calleeNode && !this.graph.isPureSubgraph(calleeNode) ? this.resolveNode(calleeNode.id) : e.callee;
			return { ...e, callee, arguments: e.arguments.map((_, i) => this.resolveOperand(node.id, i + 1)) };
		}
		return e;	// `new`/`delete`/a lambda/an unmodelled construct, kept verbatim
	}
}

// ===================================================================
//  The pipeline
// ===================================================================

export function BuildVSDG(ast: readonly Definition[]): VSDG {
	const builder = new CPPBuilder();
	builder.build(ast);
	return builder.finish();
}

export function Optimize(graph: VSDG): void {
	optimize(graph, cppDialect);
}

export function BuildProgram(
	graph:		VSDG,
	blocks?:	BlockTree,
	blockIds?:	Map<NodeId, string>
): TopLevel[] {
	return new CPPEmitter(graph, blocks, blockIds).build();
}

// Kept for callers that drive CSE directly; `Optimize` runs it as its own final round.
export function optimizeStructuralCSE(graph: VSDG, protectedIds: Set<NodeId>): boolean {
	return structuralCSE(graph, cppDialect, protectedIds);
}
