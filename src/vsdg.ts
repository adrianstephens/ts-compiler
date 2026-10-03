/* eslint-disable @typescript-eslint/no-this-alias */

// ===================================================================
//  The language-neutral VSDG middle end.
// ===================================================================
// BuildVSDG -> Optimize -> applyGlobalCodeMotion -> BuildProgram, over any of the converged ASTs (ts/js, py, cpp): pure graph machinery
// (nodes, edges, scopes, mu/theta/gamma, GCM, CSE, folding), or a question asked of a `Dialect`. A language supplies:
//   * `Dialect`  -- stateless FACTS the core asks (spelling a name, literals, which operators fold, what is unsafe to CSE), on `graph.dialect`;
//   * LOWERING   -- its own `walkerB` plus a callback per tag on its `VSDGBuilder` subclass, driving the base's primitives in its own order.
//                   No interface: the core never walks an AST (`Recurse` is all it names), and a builder never points back at its walker;
//   * `Emitter`  -- RECONSTRUCTION of graph nodes onto its AST (its printer makes the source text).
// The few shape facts the core needs are STAMPED on a node by the language when it makes it (`plainAssign`, `freshTarget`, `switchInternal`,
// `scopeAnchorId`, `capturedRead`), keeping `RawNode` language-free; whether an expression is a constant the dialect answers.
// Generics: E = expression, S = statement, T = type annotation.

import { Literal, Unary, Conditional, If, While, DoWhile, Return, ExprStmt, ConstantFolder } from '@isopodlabs/tison/ast';

// ===================================================================
//  Node model
// ===================================================================

export type NodeId = string;

export interface Edge {
	nodeId:	NodeId;
	port:	number; 
}
export interface ClassMember {
	keyNodeId?:		NodeId;
	entryNodeId?:	NodeId;
	valueNodeId?:	NodeId;
}
export interface ClassInfo {
	superClassNodeId?: NodeId;
	members: ClassMember[];
}

// What a node IS: its tag plus that tag's payload, an AST expression (floating/mutation/unary_post/effect/a function EXPRESSION), a raw statement
// (passthru/class_decl/a function DECLARATION) or a slot name. A literal is a 'floating' node; `foldConstants` mutates `.expr` into one in place.
export interface SwitchCase { testNodeId?: NodeId; boundaryId: NodeId; tailId: NodeId }

// Internal bookkeeping / state-chain anchor nodes -- a 'marker' node's whole payload.
export type MarkerName =
	| 'PROGRAM_START' | 'FUNCTION_BODY_START' | 'RETURN_ANCHOR' | 'MUTATION_MARKER'
	| 'EARLY_RETURN_MARKER' | 'THROW_MARKER' | 'BREAK_MARKER' | 'CONTINUE_MARKER'
	| 'TRY_START' | 'CATCH_START' | 'FINALLY_START' | 'BREAK_SCOPE_START';

export type INode<E, S, T> =
	| { type: 'gamma' }
	// `name` is the variable this merge is the value of -- its only identity, and never cleared.
	// neverMaterialize: a broken-out merge whose operand still resolves to its OWN name would print a
	// circular `name = op0 ? name : name;` -- forces it to always resolve lazily instead.
	| { type: 'gammaValue', name: string, neverMaterialize?: boolean }
	// loopKind: a do-while's state mu -- the body runs before the first test, so no loop-rotation.
	| { type: 'mu', loopKind?: 'do' }
	| { type: 'muValue', name: string }
	| { type: 'theta' }
	| { type: 'thetaValue', name: string }
	// declKind + typeAnnotation: a var_decl wrapper node (a param is a declKind-less 'var'); the annotation travels through every reconstruction,
	// so an explicitly typed empty collection keeps its type.
	| { type: 'var', name: string, declKind?: string, typeAnnotation?: T, capturedRead?: boolean }
	// switchDiscriminantId/switchCases: a `break_scope` reconstructing a real `switch` -- the
	// discriminant node, and each case's resolved test + body span (see SwitchCase). A language with
	// no switch construct never creates one.
	| { type: 'break_scope', switchDiscriminantId?: NodeId, switchCases?: SwitchCase[] }
	// catchParam: the catch binding. handlerTypeNodeId: the exception TYPE matched (`except ValueError`), a side channel CSE must not merge away
	// (`collectProtectedNodeIds`).
	| { type: 'except', catchParam?: string, handlerTypeNodeId?: NodeId }
	// A per-variable try/catch value merge, like gammaValue, except no branch's binding is cleared for it: there is no condition to print.
	| { type: 'exceptValue', name: string }
	// One entry/RETURN_ANCHOR-pair subgraph: a declaration (stmt), a method (neither), or a function EXPRESSION (expr, printed inline). `returnNodeId`
	// is the only way to the RETURN_ANCHOR. destructuredParams: a param bound through a hidden temp, so the printed SIGNATURE names the temp (`ParamSlot`).
	| { type: 'function', stmt?: S, expr?: E, returnNodeId: NodeId, destructuredParams?: Map<unknown, string> }
	| { type: 'class_decl', stmt: S }
	| { type: 'passthru', stmt: S }
	| { type: 'marker', name: MarkerName }
	// mutatesBindingId: the expression does NOTHING but rewrite the name bound to that node (C++'s `x++` on a plain name); used only to drop a wholly dead
	// one, a store to a name nobody reads.
	| { type: 'effect', expr: E, mutatesBindingId?: NodeId }
	// optional: a `?.` access (else `a.b?.c` reconstructs as `a.b.c`). pointerMember: C++'s `a->b`. Both are the operator of one member access: stamps, not tags.
	| { type: 'member', name: string, optional?: boolean, pointerMember?: boolean }
	| { type: 'unary_post', expr: E, name?: string }
	| { type: 'unary_post_old', expr: E }
	| { type: 'floating', expr: E }
	// name: set while this assignment is the current binding of that variable (see rebindVar) -- a
	// mutation has no declared name of its own, unlike a var_decl.
	| { type: 'mutation', expr: E, name?: string }
	;

export type NodeType = INode<any, any, any>['type'];
// The graph's value type, `any` payloads deliberately: the core reads variant payloads off nodes it
// fetches (narrowing the tag needs a UNION), and an erased node must fit a `Node<E, S, T>` parameter.
type NodeAny = Node<any, any, any>;

// The edge machinery every node has, plus the optional annotations the passes stamp on that span
// several tags. Tag-local annotations live on the matching INode variant instead.
export class RawNode {
	// Assigned by MakeNode from the INode variant this is Object.assign'd with (there are no
	// subclasses). The tag UNION, not `string`, so a mistyped case label below is still an error.
	type!:			NodeType;
	inputs:			Edge[]		= [];		// inputs[port] = the single source edge feeding this slot
	outputs:		Edge[][]	= [];		// outputs[port] = every downstream edge consuming this channel
	// Set while this node is the current binding of its own variant's `name` (a var_decl/reassignment,
	// or a per-variable merge); CLEARED when a branch's reassignment is superseded by a merge.
	bound?:			boolean;
	forcedPrint?:	boolean;				// Forces a reassignment to print even with no value-consumer: one on an exited branch (break/continue/return) skips the post-branch merge entirely, so needsTemp would see it as dead.
	// Switch's own bookkeeping (`__hit`/`__matchN`), always resolved by name rather than inlined by forcedPrint/needsTemp. On the gamma and the `hit` var/mutation.
	switchInternal?: boolean;
	// A 'this'/'super' node's enclosing function: it has no input edge to float a hoisted read against, so without this it could escape its function.
	scopeAnchorId?: NodeId;
	exported?:		'named' | 'default';	// Stamped on whatever node an export left behind, so its own print site can wrap it in `export `/`export default `.
	classInfo?:		ClassInfo;				// A class anchor's own resolved pieces -- index-aligned with the original `body` array; rebuildClass splices these back in. Set on a class_decl statement AND on the effect node of a class expression.

	// ---- shape stamps, set by the language when it creates the node (see the file header) ----
	plainAssign?:	boolean;				// A 'mutation' from a plain `=` (no compound operator), whose port 0 is the never-read old value
	freshTarget?:	boolean;				// A 'member'/index-shaped lvalue address: must always rebuild, never resolve to a cached temp
	// On every node lowered inside a statement PRINTED VERBATIM (`lowerVerbatim`): they exist only so a name the text mentions keeps a reader;
	// emitting one would run the statement's insides twice.
	suppressed?:	boolean;

	constructor(public id: string) {}
	outDegree() { return this.outputs.reduce((sum, arr) => sum + arr.length, 0); }

	// An edge wired up generically but never read by codegen: no real reader for reuse/dead/inline decisions, and no constraint on GCM.
	isVestigialEdge(port: number): boolean {
		switch (this.type) {
			// A mutation's old-value port (0) is never read for a plain `=`; port 2 is threadMutation's ordering-only marker.
			case 'mutation':	return port === 2 || (!!this.plainAssign && port === 0);
			// A named theta's own condition edge -- resolveNode always resolves a thetaValue through
			// its mu source (port 1) instead.
			case 'thetaValue':	return port === 0;
			// A postfix ++/--'s old-value snapshot (port 1): real for SCHEDULING (read before the increment), never a value either node reads.
			case 'unary_post':	return port === 1;
			// Same ordering-only marker edge as 'mutation', see above.
			case 'var':			return port === 2;
			// A state gamma's tail ports (2/3), walked directly by the emitter; a switchInternal gamma's condition (port 1), which switch's cascade never reads.
			case 'gamma':		return port === 2 || port === 3 || (port === 1 && !!this.switchInternal);
			// A break_scope's tail port (1) -- same reasoning as gamma's.
			case 'break_scope': return port === 1;
			// The state except's try/catch/finally tails (1/2/3), likewise.
			case 'except':		return port === 1 || port === 2 || port === 3;
			default:			return false;
		}
	}
}

// A concrete node: RawNode's edge machinery + annotations, plus one INode variant's own payload.
export type Node<E, S, T, N extends INode<E, S, T> = INode<E, S, T>> = RawNode & N;
// The node for one specific tag, with that variant's own annotations -- what makeNode/MakeNode hand back.
export type NodeOf<E, S, T, K extends NodeType> = Node<E, S, T, Extract<INode<E, S, T>, { type: K }>>;

export function MakeNode<E, S, T, N extends INode<E, S, T>>(id: string, inode: N): NodeOf<E, S, T, N['type']> {
	return Object.assign(new RawNode(id), inode) as unknown as NodeOf<E, S, T, N['type']>;
}

/**
* A node's source-variable name, if this node is CURRENTLY that binding (a direct rebind or a per-variable merge). A free function: the name is tag-local.
*/
export function slotName<E, S, T>(node: Node<E, S, T>): string | undefined {
	switch (node.type) {
		// A merge IS its own name, and is never cleared (see reconcileVariables's own exclusions),
		// so there is no flag to consult.
		case 'gammaValue':
		case 'exceptValue':	return node.name;
		// Every tag a binding can be cleared from (a declaration, a rebind, a postfix ++/--): the same set as rebindVar's guard.
		case 'var':
		case 'mutation':
		case 'unary_post':	return node.bound ? node.name : undefined;
		// muValue/thetaValue carry a name too, but resolveNode's own cases trust them by name where
		// they're read -- neither is ever printed under it.
		default:			return undefined;
	}
}

export function connectValue(
	from:	RawNode, outputPort: number,
	to:		RawNode, inputPort: number
): void {
	to.inputs[inputPort] = { nodeId: from.id, port: outputPort };
	(from.outputs[outputPort] ??= []).push({ nodeId: to.id, port: inputPort });
}

// INVARIANT for a scheduling-only edge (placing `to`, not read by codegen): `from` must be a genuine STRUCTURAL lower bound on `to`'s depth,
// since scheduleEarly treats it as a dependency and an incidental one drags an unconditional statement into a conditional.

// ===================================================================
//  Scopes
// ===================================================================

export class Scope<E, S, T> {
	local		= new Set<string>;
	bindings	= new Map<string, Node<E, S, T>>();
	// Set only on a function's own scope: a reassignment crossing into an enclosing function needs forcedPrint (`isLocalToCurrentFunction`).
	isFunctionBoundary = false;

	constructor(public parent: Scope<E, S, T> | null = null) { }
	closeAndFlush() {
		if (this.parent) {
			for (const [name, node] of this.bindings.entries()) {
				if (!this.local.has(name))
					this.parent.bindings.set(name, node);
			}
		}
		return this.parent;
	}
	create(name: string, node: Node<E, S, T>): void {
		this.local.add(name);
		this.bindings.set(name, node);
	}
	set(name: string, node: Node<E, S, T>): void {
		this.bindings.set(name, node);
	}
	get(name: string): Node<E, S, T> | undefined {
		return this.bindings.get(name) ?? this.parent?.get(name);
	}

	// False when `name` is captured from outside the current function: reassigning it escapes, so no same-region consumer count may inline it.
	isLocalToCurrentFunction(name: string): boolean {
		for (let s: Scope<E, S, T> | null = this; s; s = s.parent) {
			if (s.local.has(name))
				return true;
			if (s.isFunctionBoundary)
				return false;
		}
		return true;
	}

}

export class ScopeMu<E, S, T> extends Scope<E, S, T> {
	muNodes = new Map<string, Node<E, S, T>>();

	// stateAnchor gives a named mu a scheduling dependency on the loop, or GCM would float its dependents out as loop-invariant.
	// currentFunctionEntry is live: a name looked up from a nested function needs THAT function's entry.
	constructor(parent: Scope<E, S, T>, public makeMu: (name: string) => Node<E, S, T>, public stateAnchor: Node<E, S, T>, public currentFunctionEntry: () => Node<E, S, T> | undefined) {
		super(parent);
	}
	public get(name: string): Node<E, S, T> | undefined {
		const node = this.bindings.get(name);
		if (node)
			return node;
		const old = this.parent?.get(name);
		if (old) {
			const mu = this.makeMu(name);
			// A captured read touched inside a loop gets the scopeAnchorId floor this/super get, or a value derived from this mu could be hoisted past the
			// arrow it is inside (a verbatim arrow body is oblivious to GCM).
			mu.scopeAnchorId = this.currentFunctionEntry()?.id;
			this.muNodes.set(name, mu);					//original mu
			this.bindings.set(name, mu);				// current node
			connectValue(old, 0, mu, 0);				// Slot 0 = Initial value from outside
			connectValue(this.stateAnchor, 0, mu, 2);	// Slot 2 = scheduling-only: "at least as deep as the loop"
			return mu;
		}
	}
}

export class VSDG extends Map<NodeId, NodeAny> {
	root: NodeId = '';

	constructor() { super(); }

	getNode(id: NodeId) {
		const node = this.get(id);
		if (!node)
			throw new Error(`missing node ${id}`);
		return node;
	}

	removeInputs(node: RawNode) {
		for (const e of node.inputs) {
			const down = this.getNode(e.nodeId);
			down.outputs[e.port] = down.outputs[e.port].filter(c => c.nodeId !== node.id);
		}
		// Clears the node's OWN inputs too: scheduleEarly walks every node's inputs, and the producer may be removed by a later CSE pass.
		node.inputs = [];
	}
	removeNode(node: RawNode) {
		this.removeInputs(node);
		this.delete(node.id);
	}

	// True if `node`'s value has a real reader beyond vestigial edges; zero means dead (every branch reassigns before any read).
	hasRealConsumer(node: RawNode): boolean {
		return (node.outputs[0] ?? []).some(e => !this.get(e.nodeId)!.isVestigialEdge(e.port));
	}
	// Conservative, single-pass purity check over `node`'s own transitive inputs: true only if NO
	// effect appears anywhere in the subgraph that produces it.
	isPureSubgraph(node: RawNode): boolean {
		const seen		= new Set<NodeId>();
		const recurse	= (node: RawNode): boolean => {
			if (seen.has(node.id))
				return true;
			seen.add(node.id);
			if (node.type === 'effect' || node.type === 'marker')
				return false;
			// A function entry has NO input edges, so an empty `.every(...)` would call it vacuously pure.
			if (node.type === 'function')
				return false;
			// A PARAMETER's value is pure whatever runs before the call: its input is an entry OUTPUT port (>= 1); port 0 is `const f = () => {}` reading itself.
			if (node.type === 'var' && node.inputs[0]?.port !== undefined && node.inputs[0].port >= 1
				&& this.get(node.inputs[0].nodeId)!.type === 'function')
				return true;
			// Skip vestigial edges (e.g. threadMutation's own scheduling-only marker) -- a real graph
			// edge GCM needs, but never part of the actual value computation.
			return node.inputs.every((e, port) => !e || node.isVestigialEdge(port) || recurse(this.get(e.nodeId)!));
		};
		return recurse(node);
	}

}

// ===================================================================
//  The dialect seam
// ===================================================================

// A language's own walker, narrowed to what the core and the lowering handlers need; its `WalkerB` recurse satisfies it structurally.
// The ONLY part of a walk the core names: it DRIVES a subtree, never handles a node. It exists before the first statement is lowered.
export interface Recurse<E, S> {
	statement(s?: S): boolean;
	expression(e?: E): boolean;
	statements(x: readonly S[]): boolean;
}

// One parameter position: a plain name gets a 'var' on the entry's next output port; any other shape (js/ts destructuring) a HIDDEN temp, with the
// step binding it off that temp as a closure (it WALKS, which is lowering, not a Dialect fact). `token` comes back through `destructuredParams`.
export type ParamSlot = { name: string } | { token: unknown, desugar: (tempName: string) => void };

/**
* A language's spelling of `switch`'s fixed scaffolding; the walk, per-case scopes included, is the core's (`buildSwitch`).
*/
export interface SwitchSyntax<E, S, T> {
	/**
	* A hidden local bound to `value`, named by the core (`__disc_<n>`, `__match0_<n>`, `__hit_<n>`, `n` unique per switch).
	*/
	local(value: E, name: string): NodeOf<E, S, T, 'var'>;
	/** `<discName>` tested against a case's own test: `===` in js, `==` in C++, ... */
	comparison(discName: string, test: E): E;
	/** "this case runs": `<hit> || <match>`, or -- for `default` -- "none of the others matched". */
	condition(hitName: string, matchName: string | undefined, otherMatches: string[]): E;
	/** `<hit> = true`, as an expression this language's own assignment lowering walks. */
	setHit(hitName: string): E;
}

// FACTS about a language the core asks, nothing else (no walker, no lowering, no reconstruction). A deeper question would be the core learning
// AST shapes: that is a node stamp instead. The graph carries one, which is how the optimiser passes reach it.
export interface Dialect<E, S, T> extends ConstantFolder<E> {
	/** The name a bare identifier reference binds to, or undefined for any other expression shape. */
	identifierName(e: E): string | undefined;
	// This language's own node for a bare name reference.
	identifier(name: string): E;
	// A structural signature for an opaque expression payload, for structural CSE.
	exprKey(e: E): string;
	// The same, for a raw statement held verbatim by a passthru/class_decl node.
	stmtKey(s: S): string;
	/**
	* True when `node` must never merge with an identical-looking one: its VALUE may differ (a fresh array, a per-call receiver, an lvalue a mutation changes).
	*/
	isCSEUnsafe(node: Node<E, S, T>): boolean;
	// True when `port` of `consumer` reads its producer as a call's own CALLEE.
	isCalleeEdge(consumer: Node<E, S, T>, port: number): boolean;
}

/**
* True when `node` holds this language's literal form; a type predicate, so a guarded caller reads `node.expr` directly.
*/
function isLiteral<E, S, T>(dialect: Dialect<E, S, T>, node: Node<E, S, T>): node is NodeOf<E, S, T, 'floating'> {
	return node.type === 'floating' && dialect.literalValue(node.expr) !== undefined;
}

// ===================================================================
//  BuildVSDG -- the state machine, shared by every language
// ===================================================================

export interface State<E, S, T> { scope: Scope<E, S, T>, end: Node<E, S, T>, exited: boolean, brokeOut: boolean };

// `abstract` is a marker only: a language subclasses this for the run's state and calls its primitives from its lowering handlers.
export abstract class VSDGBuilder<E, S, T> {
	readonly graph: VSDG;
	scope:			Scope<E, S, T>;
	end!:			Node<E, S, T>;
	exited			= false;
	brokeOut		= false;
	/** The innermost function currently being walked (undefined at top level). */
	currentFunctionEntry: Node<E, S, T> | undefined;

	protected nextId	= 0;
	protected expnodes	= new Map<E, Node<E, S, T>>();
	/** Names declared nowhere in this file (globals, built-ins, imports): one shared declKind-less 'var' each, read by name. */
	protected externalNodes = new Map<string, Node<E, S, T>>();
	/**
	* Per enclosing LOOP (switch is transparent to `continue`): a for-loop's `update`, which `continue` re-walks as a fresh clone, or undefined.
	*/
	protected loopUpdateStack: (E | undefined)[] = [];
	/** True only while lowering the inside of a statement that will print verbatim -- see lowerVerbatim. */
	protected verbatim = false;

	constructor(public readonly dialect: Dialect<E, S, T>) {
		this.graph	= new VSDG;
		this.scope	= new Scope(null);	// The global scope
		this.end	= this.makeMarker('PROGRAM_START');
	}

	/** A fresh, graph-unique numeric suffix -- for synthesised names (`__iter0`, `__destructure3`). */
	protected freshId(): number { return this.nextId++; }

	// ---- node construction ----

	makeNode<N extends INode<E, S, T>>(inode: N): NodeOf<E, S, T, N['type']> {
		const id	= inode.type + String(this.nextId++);
		const node	= MakeNode<E, S, T, N>(id, inode);
		node.suppressed = this.verbatim || undefined;
		this.graph.set(id, node as unknown as Node<E, S, T>);
		return node;
	}
	// An internal bookkeeping / state-chain anchor node.
	makeMarker(name: MarkerName): NodeOf<E, S, T, 'marker'> {
		return this.makeNode({ type: 'marker', name });
	}
	/**
	* 'floating' is every pure value-producing expression; an assignment operator or ++/-- is 'mutation', a real effect never pooled, folded or inlined.
	* Registers the expr for getExprNode; the tag is open because a postfix ++/-- snapshots its old value under 'unary_post_old'.
	*/
	makeExprNode<K extends NodeType = 'floating'>(expr: E, type: K = 'floating' as K): NodeOf<E, S, T, K> {
		const node = this.makeNode({ type, expr } as INode<E, S, T>);
		this.expnodes.set(expr, node);
		return node as unknown as NodeOf<E, S, T, K>;
	}
	getExprNode(expr: E): Node<E, S, T> {
		const name = this.dialect.identifierName(expr);
		if (name !== undefined) {
			const found = this.scope.get(name);
			if (found) {
				// A read reaching outside its declaring function is never statically inlined (`capturedRead`): that function may run any number of times.
				if (found.type === 'var' && !this.scope.isLocalToCurrentFunction(name))
					found.capturedRead = true;
				return found;
			}
			let ext = this.externalNodes.get(name);
			if (!ext) {
				ext = this.makeNode({type: 'var', name});
				this.externalNodes.set(name, ext);
			}
			return ext;
		}
		const node = this.expnodes.get(expr);
		if (!node)
			throw new Error(`missing node for ${this.dialect.exprKey(expr)}`);
		return node;
	}

	// ---- state ----

	getState(): State<E, S, T> {
		return { scope: this.scope, end: this.end, exited: this.exited, brokeOut: this.brokeOut };
	}
	setState(_scope: Scope<E, S, T>, _end: Node<E, S, T>, _exited = false, _brokeOut = false) {
		this.scope		= _scope;
		this.end		= _end;
		this.exited		= _exited;
		this.brokeOut	= _brokeOut;
	}

	connectEnd(effect: Node<E, S, T>) {
		connectValue(this.end, 0, effect, 0);
		this.end = effect;
	}

	// Whether the state chain from `tail` back to `boundary` holds a REAL effect (a call), MUTATION_MARKERs ignored: does a branch need a structural gamma.
	hasRealEffect(tail: Node<E, S, T>, boundary: Node<E, S, T>): boolean {
		for (let cur = tail; cur !== boundary; ) {
			if (!(cur.type === 'marker' && cur.name === 'MUTATION_MARKER'))
				return true;
			const pred = cur.inputs[0];
			if (!pred)
				return true; // shouldn't happen; treat conservatively as a real divergence
			cur = this.graph.get(pred.nodeId)!;
		}
		return false;
	}

	// A reassignment is an observable mutation, like a call, but not threaded through the state chain: a marker is, and the node hangs off it by a
	// scheduling-only edge on its unused port 2. A per-prior-effect edge would also constrain DEPTH, pulling an unconditional reassignment into a conditional.
	threadMutation(node: Node<E, S, T>) {
		const marker = this.makeMarker('MUTATION_MARKER');
		connectValue(marker, 0, node, 2);
		this.connectEnd(marker);
	}
	// Binds a node the language ALREADY named as a NEW declaration in the current scope, ordered into the state chain (`rebindVar` without the naming).
	bindVar(node: NodeOf<E, S, T, 'var'>) {
		node.bound = true;
		this.scope.create(node.name, node);
		this.threadMutation(node);
	}
	// The single place a name becomes bound to a node: names it, updates scope, and orders it -- so a
	// call site can't skip one. A declaration whose node already carries its name is `bindVar` instead.
	rebindVar(name: string, node: Node<E, S, T>, isDeclaration = false) {
		// Only these tags hold the name in a field that comes and goes with the binding; a merge carries its own for good. The same set as slotName's cases.
		if (node.type === 'var' || node.type === 'mutation' || node.type === 'unary_post') {
			node.name	= name;
			node.bound	= true;
		}
		if (isDeclaration)
			this.scope.create(name, node);
		else
			this.scope.set(name, node);
		this.threadMutation(node);
	}

	// ---- loops and branches ----

	// Shared by every language's loop lowering: the same mu/theta machinery, the test read before the body (while) or after it (do_while).
	buildLoop(recurse: Recurse<E, S>, test: E, walkBody: () => void, isDoWhile: boolean, forUpdate?: E) {
		const preLoop	= this.getState();
		const muEnd		= this.makeNode({ type: 'mu' });
		const muScope	= new ScopeMu(this.scope, name => this.makeNode({type: 'muValue', name}), muEnd, () => this.currentFunctionEntry);
		this.scope		= muScope;
		this.connectEnd(muEnd);

		this.loopUpdateStack.push(forUpdate);
		let testNode: Node<E, S, T>;
		if (isDoWhile) {
			muEnd.loopKind = 'do';
			this.exited		= false;
			this.brokeOut	= false;
			walkBody();
			recurse.expression(test);
			testNode	= this.getExprNode(test);
		} else {
			recurse.expression(test);
			testNode	= this.getExprNode(test);
			this.exited		= false;
			this.brokeOut	= false;
			walkBody();
		}
		this.loopUpdateStack.pop();

		connectValue(this.end, 0, muEnd, 1); // Slot 1 = Feedback loop

		const stateTheta = this.makeNode({ type: 'theta' });
		connectValue(muEnd, 0, stateTheta, 0);		// Slot 0 = State predecessor (the loop)
		connectValue(testNode, 0, stateTheta, 1);	// Slot 1 = Loop termination condition
		this.end = stateTheta;

		this.scope = preLoop.scope;
		for (const [name, muNode] of muScope.muNodes) {
			connectValue(muScope.bindings.get(name)!, 0, muNode, 1);		// Slot 1 = Feedback loop

			const theta = this.makeNode({type: 'thetaValue', name});
			connectValue(testNode, 0, theta, 0);	// Slot 0 = Condition
			connectValue(muNode, 0, theta, 1);		// Slot 1 = Value to pass out
			connectValue(stateTheta, 0, theta, 2);	// Scheduling-only anchor, see ScopeMu's own
			this.scope.set(name, theta);
		}
		// The loop AS A WHOLE falls through to what follows, whatever break/continue happened inside.
		this.exited = false;
		this.brokeOut = false;
	}

	/**
	* `switch` as the if-cascade every language lowers it into: one binary branch per case ("entered already, or this one matches"), chained forward;
	* `break_scope`'s `switchCases` reconstruct a real `switch` at print time, `switchInternal` keeps the bookkeeping out. `cases` arrive grouped.
	*/
	protected buildSwitch(recurse: Recurse<E, S>, discriminant: E, cases: { test?: E, body: () => void }[], syntax: SwitchSyntax<E, S, T>) {
		// The discriminant is evaluated exactly ONCE, into a wrapper every case test reads.
		recurse.expression(discriminant);
		// The id its local is about to get, borrowed without consuming one: what keeps two switches in one enclosing scope apart.
		const discNode	= syntax.local(discriminant, `__disc_${this.nextId}`);
		this.bindVar(discNode);

		// Each case's test is evaluated once, in source order, into its own flag; walked first, since `syntax.local` finds it through `getExprNode`.
		const caseNodes = cases.map((c, i) => {
			if (!c.test)
				return { matchName: undefined, testNodeId: undefined };
			const comparison	= syntax.comparison(discNode.name, c.test);
			recurse.expression(comparison);
			const matchNode		= syntax.local(comparison, `__match${i}_${this.nextId}`);
			this.bindVar(matchNode);
			return { matchName: matchNode.name, testNodeId: this.getExprNode(c.test).id };
		});
		const matchNames = caseNodes.map(t => t.matchName);

		// A hidden "entered a case yet" flag, reassigned like a variable, so fallthrough falls out of the ordinary merge machinery.
		const falseValue	= Literal(false) as E;
		recurse.expression(falseValue);
		const hitNode		= syntax.local(falseValue, `__hit_${this.nextId}`);
		this.bindVar(hitNode);

		// The anchor is created AFTER the cases: created first, it would be the first case's `parent.end`, stopping emitChain's backward walk there.
		// The start marker keeps the first case's state gamma off break_scope's predecessor.
		const predecessor	= this.end;
		const startMarker	= this.makeMarker('BREAK_SCOPE_START');
		this.connectEnd(startMarker);
		this.exited		= false;
		this.brokeOut	= false;

		const switchCases: { testNodeId?: NodeId, boundaryId: NodeId, tailId: NodeId }[] = [];
		for (const [i, c] of cases.entries()) {
			const testExpr	= syntax.condition(hitNode.name, matchNames[i], matchNames.filter((n): n is string => n !== undefined));
			recurse.expression(testExpr);
			const testNode	= this.getExprNode(testExpr);
			const parent	= this.getState();
			let bodyBoundary: Node<E, S, T> | undefined;
			const trueState = this.walkBranch(parent, () => {
				// switchInternal keeps the hit reassignment resolving by name: its mutation is never printed.
				recurse.expression(syntax.setHit(hitNode.name));
				this.scope.get(hitNode.name)!.switchInternal = true;
				bodyBoundary = this.end;
				// A case body gets its own scope, as a braced block would: a declaration in one case never reaches the branch MERGE, where the other
				// branch would lack the binding.
				this.scope = new Scope(this.scope);
				c.body();
				this.scope = this.scope.closeAndFlush()!;
			});
			const falseState = this.walkBranch(parent, () => {});
			// A state gamma here belongs to switch's own cascade, which print-time reconstruction bypasses: switchInternal excludes its condition edge.
			const stateGamma = this.mergeState(parent, testNode, trueState, falseState);
			if (stateGamma)
				stateGamma.switchInternal = true;
			this.reconcileVariables(parent, testNode, trueState, falseState);
			switchCases.push({ testNodeId: caseNodes[i].testNodeId, boundaryId: bodyBoundary!.id, tailId: trueState.end.id });
		}

		const breakScope = this.makeNode({ type: 'break_scope', switchDiscriminantId: discNode.id, switchCases });
		connectValue(predecessor, 0, breakScope, 0);
		// Port 1 = the scope's tail (like a gamma's tail ports), where emitChain walks back from.
		connectValue(this.end, 0, breakScope, 1);
		this.end		= breakScope;
		this.exited		= false;
		this.brokeOut	= false;
	}

	// Shared by 'if' and 'switch' (each case a binary branch): resets scope/end/exited to `parent`, walks one branch, captures the result.
	walkBranch(parent: State<E, S, T>, walk: () => void): State<E, S, T> {
		this.setState(new Scope(parent.scope), parent.end);
		walk();
		return this.getState();
	}

	// The STATE half of reconciling two branches: whether either needs a structural gamma (a call, an exit), or state continues past a branch that only
	// reassigned variables. Sets `end`/`exited` for what follows.
	mergeState(parent: State<E, S, T>, test: Node<E, S, T>, trueState: State<E, S, T>, falseState: State<E, S, T>): NodeOf<E, S, T, 'gamma'> | undefined {
		if (trueState.exited || falseState.exited || this.hasRealEffect(trueState.end, parent.end) || this.hasRealEffect(falseState.end, parent.end)) {
			const gamma = this.makeNode({ type: 'gamma' });
			connectValue(parent.end, 0, gamma, 0);		// Slot 0 = State predecessor
			connectValue(test, 0, gamma, 1);			// Slot 1 = Condition
			connectValue(trueState.end, 0, gamma, 2);	// Slot 2 = True State
			connectValue(falseState.end, 0, gamma, 3);	// Slot 3 = False State
			this.end = gamma;
			// "Exited" only when BOTH sides did: an implicit empty else always falls through.
			this.exited = trueState.exited && falseState.exited;
			// Likewise brokeOut; mixed exit kinds fall back to false, as nothing downstream is reachable either way.
			this.brokeOut = this.exited && trueState.brokeOut && falseState.brokeOut;
			return gamma;
		}
		// No real effect: the per-variable gammas capture it. `end` still resets, or it dangles off whichever branch's marker chain was walked last.
		this.end		= parent.end;
		this.exited		= trueState.exited && falseState.exited;
		this.brokeOut	= this.exited && trueState.brokeOut && falseState.brokeOut;
		return undefined;
	}

	// True if `name` is loop-carried: the next iteration sees the update only through the real runtime variable. The nearest ScopeMu owns it.
	isLoopCarried(name: string): boolean {
		for (let s: Scope<E, S, T> | null = this.scope; s; s = s.parent) {
			if (s instanceof ScopeMu && s.muNodes.has(name))
				return true;
		}
		return false;
	}

	// The VALUE half: per-variable reconciliation of everything either branch reassigned.
	reconcileVariables(parent: State<E, S, T>, test: Node<E, S, T>, trueState: State<E, S, T>, falseState: State<E, S, T>) {
		this.scope = parent.scope;
		const divergedVariables = new Set([
			...trueState.scope.bindings.keys(),
			...falseState.scope.bindings.keys()
		]);
		for (const name of divergedVariables) {
			const trueVal	= trueState.scope.get(name)!;
			const falseVal	= falseState.scope.get(name)!;

			// Different values: a gamma stitches them.
			if (trueVal !== falseVal) {
				// Exactly one branch exited. continue/return/throw: that branch's forced-printed statement handles it, and merging would corrupt GCM scheduling.
				// break: its target loop or switch DOES read `name` back through the graph, so it merges as usual.
				if (trueState.exited !== falseState.exited && !(trueState.exited ? trueState : falseState).brokeOut) {
					const exitedVal = trueState.exited ? trueVal : falseVal;
					if (slotName(exitedVal) === name)
						exitedVal.forcedPrint = true;
					this.scope.set(name, trueState.exited ? falseVal : trueVal);
					continue;
				}

				// Each branch's plain reassignment was named as the tentative answer; the gamma supersedes it, so it is cleared, except a side that broke out
				// (forcedPrint needs the name) and a var_decl's own wrapper.
				const trueExitedViaBreak	= trueState.exited && !falseState.exited && trueState.brokeOut;
				const falseExitedViaBreak	= falseState.exited && !trueState.exited && falseState.brokeOut;

				// forcedPrint is NECESSARY only for a loop-carried `name` (or switch's `hit = true;`): a one-shot merge is a graph edge. A gammaValue/exceptValue
				// operand keeps its name: a MERGE identity that a further chained merge resolves by name.

				const forcedPrint	= (n: Node<E, S, T>) => slotName(n) === name && (n.switchInternal || this.isLoopCarried(name));
				const clearable		= (n: Node<E, S, T>) => slotName(n) === name && !(n.type === 'var' && n.declKind) && n.type !== 'gammaValue' && n.type !== 'exceptValue';

				if (trueExitedViaBreak && forcedPrint(trueVal))
					trueVal.forcedPrint = true;
				else if (clearable(trueVal))
					trueVal.bound = undefined;

				if (falseExitedViaBreak && forcedPrint(falseVal))
					falseVal.forcedPrint = true;
				else if (clearable(falseVal))
					falseVal.bound = undefined;

				// One side broke out, its operand still named `name`: printing the merge under it would be circular, so neverMaterialize.
				const gamma = this.makeNode({ type: 'gammaValue', name, neverMaterialize: trueExitedViaBreak || falseExitedViaBreak });
				connectValue(test, 0, gamma, 0); 		// Condition
				connectValue(trueVal, 0, gamma, 1);		// True path
				connectValue(falseVal, 0, gamma, 2);	// False path

				// The merge is the binding the code after the branch sees.
				this.scope.set(name, gamma);
			}
		}
	}

	// ---- functions ----

	// A method/get/set/static_block's own function subgraph, with a top-level function's entry/return machinery. The entry joins the outer state chain
	// only so GCM nests it under the right region (the body does not run there, a static block aside).
	buildFunctionBody(recurse: Recurse<E, S>, slots: ParamSlot[] | undefined, body: E | readonly S[]): NodeOf<E, S, T, 'function'> {
		const outer			= this.getState();
		const returnNode	= this.makeMarker('RETURN_ANCHOR');
		const entryNode		= this.makeNode({ type: 'function', returnNodeId: returnNode.id });
		connectValue(outer.end, 0, entryNode, 0);

		// The body's own region root for `regionRootOf` (GCM); the entry's block is not safe for that.
		const bodyStart		= this.makeMarker('FUNCTION_BODY_START');
		connectValue(entryNode, 0, bodyStart, 0);

		const fnScope		= new Scope<E, S, T>(this.scope);
		fnScope.isFunctionBoundary = true;

		// A hidden param's finishing statements can only be walked once the function's state chain is live: run after setState, before the body.
		const pendingParamDesugars: (() => void)[] = [];
		if (slots) {
			// Each param gets its own node on the entry's output ports (port 0 is state, so params start at 1).
			let port = 1;
			for (const slot of slots) {
				if ('name' in slot) {
					const paramNode = this.makeNode({type: 'var', name: slot.name});
					connectValue(entryNode, port++, paramNode, 0);
					fnScope.create(slot.name, paramNode);
				} else {
					const tempName = `__destructure${this.nextId++}`;
					const paramNode = this.makeNode({type: 'var', name: tempName});
					connectValue(entryNode, port++, paramNode, 0);
					fnScope.create(tempName, paramNode);
					(entryNode.destructuredParams ??= new Map()).set(slot.token, tempName);
					pendingParamDesugars.push(() => slot.desugar(tempName));
				}
			}
		}

		this.setState(fnScope, bodyStart);

		// A `this`/`super` inside is stamped with the INNERMOST entry: not exact for a nested arrow, but it keeps a hoisted this-derived value in a function.
		const outerFunctionEntry = this.currentFunctionEntry;
		this.currentFunctionEntry = entryNode;
		for (const desugar of pendingParamDesugars)
			desugar();
		if (Array.isArray(body)) {
			for (const stmt of body as readonly S[])
				recurse.statement(stmt);
			// Unconnected, as EARLY_RETURN_MARKER's bare `return;` is: rebuildFunctionBody then omits the trailing statement.
		} else {
			recurse.expression(body as E);
			connectValue(this.getExprNode(body as E), 0, returnNode, 1);
		}
		this.currentFunctionEntry = outerFunctionEntry;

		connectValue(this.end, 0, returnNode, 0);

		// A captured variable's reassignment propagates back into the caller's bindings, so a later read resolves it by name: forcedPrint and scheduleLate's
		// region boundary keep it printed inside this function.
		fnScope.closeAndFlush();
		this.setState(outer.scope, outer.end, outer.exited, outer.brokeOut);
		return entryNode;
	}

	/**
	* A statement this language does not model, lowered as an opaque verbatim step: `walk` descends into it (so every name its text mentions keeps a reader),
	* everything it creates stamped `suppressed`, and the statement is anchored in the state chain, or it vanishes and its body runs unconditionally.
	*/
	protected lowerVerbatim(s: S, walk: (s: S) => void): false {
		const outer		= this.getState();
		const wasVerbatim = this.verbatim;
		this.verbatim	= true;
		walk(s);
		this.verbatim	= wasVerbatim;
		// The body's effects must not become the state chain: the verbatim statement is one opaque step.
		this.setState(outer.scope, outer.end, outer.exited, outer.brokeOut);
		this.connectEnd(this.makeNode({type: 'passthru', stmt: s}));
		return false;
	}

	/**
	* Closes the run: the state chain's tail becomes the graph's root. Called once, after the language's walk.
	*/
	finish(): VSDG {
		this.graph.root = this.end.id;
		return this.graph;
	}
}

// ===================================================================
//  BuildProgram -- reconstruction, shared by every language
// ===================================================================

// A source name is unique only WITHIN its function: one frame per function body, so two functions' same-named locals both declare; `has` walks
// outward (a captured variable), `add` writes the innermost frame.
export class ScopedNames {
	private stack = [new Set<string>()];
	has(name: string) {
		for (let i = this.stack.length - 1; i >= 0; i--)
			if (this.stack[i].has(name))
				return true;
		return false;
	}
	add(name: string)	{ this.stack[this.stack.length - 1].add(name); }
	push() 				{ this.stack.push(new Set()); }
	pop() 				{ this.stack.pop(); }
}

export type BlockId = string;

type CommonStmt<E> = If<E, unknown> | While<E, unknown> | DoWhile<E, unknown> | Return<E> | ExprStmt<E> | { type: 'break' } | { type: 'continue' };
type CommonExpr<E> = Conditional<E> | Unary<E, unknown>;
function admit<X extends CommonStmt<E>, E, S>(stmt: X): S	{ return stmt as unknown as S; }
function admitExpr<X extends CommonExpr<E>, E>(expr: X): E	{ return expr as unknown as E; }

// `S extends { type: string }` for `isBreakStmt` below: every language's statement union is tagged.
export abstract class Emitter<E, S extends { type: string }, T> {
	protected nodeVariableNames	= new Map<NodeId, string>();
	/** Confirms a name's own statement was ACTUALLY printed somewhere reachable (see ScopedNames). */
	names						= new ScopedNames();
	protected tempVarCounter	= 0;

	// GCM's output (applyGlobalCodeMotion), undefined without a GCM pass; buildProgram/emitChain/needsTemp degrade gracefully without it.
	protected blockNodesCache: Map<BlockId, NodeId[]> | undefined;

	constructor(public readonly graph: VSDG, public readonly dialect: Dialect<E, S, T>, protected blocks?: BlockTree, protected blockIds?: Map<NodeId, BlockId>) {
	}

	// The whole program's statements, walked back from programEndId to PROGRAM_START ('block_entry' in GCM; else found by type and value).
	build(): S[] {
		const programStartId = this.blocks?.getControl('block_entry')
			?? [...this.graph.values()].find(n => n.type === 'marker' && n.name === 'PROGRAM_START')?.id;
		if (!programStartId)
			return [];
		return [...this.emitControlNode(this.graph.getNode(programStartId)), ...this.emitChain(this.graph.root, programStartId)];
	}

	makeTempVar(id: NodeId) {
		const varName = `t${this.tempVarCounter++}`;
		this.nodeVariableNames.set(id, varName);
		return varName;
	}

	// A gammaValue's condition port where both branches resolve to one name (`cond ? x : x` collapses): switchInternal, on switch's `hit`, marks it.
	// Counted as a consumer it would materialize a needless temp.
	isCollapsingGammaValueCondition(edge: Edge): boolean {
		if (edge.port !== 0)
			return false;
		const target = this.graph.get(edge.nodeId)!;
		return target.type === 'gammaValue' && !!(
				(target.inputs[1] && this.graph.get(target.inputs[1].nodeId))?.switchInternal
			||	(target.inputs[2] && this.graph.get(target.inputs[2].nodeId))?.switchInternal
		);
	}

	valueConsumers(node: Node<E, S, T>): Edge[] {
		return (node.outputs[0] ?? []).filter(e => {
			const target = this.graph.get(e.nodeId)!;
			// Port 0 of a control node is its predecessor, never a value read, EXCEPT on the per-variable merges, whose port 0 IS the condition they print;
			// missing that inlined an impure condition and printed its call twice.
			if (CONTROL.has(target.type) && e.port === 0 && target.type !== 'gammaValue' && target.type !== 'exceptValue')
				return false;
			// A mu's feedback port (1) is as much scheduling-only as its predecessor port (0).
			if ((target.type === 'mu' || target.type === 'muValue') && e.port === 1)
				return false;
			if (target.isVestigialEdge(e.port))
				return false;
			if (this.isCollapsingGammaValueCondition(e))
				return false;
			// A dead var_decl prints bare (`let x = f();` becomes `f();`): its value never surfaces.
			if (target.type === 'var' && !this.graph.hasRealConsumer(target))
				return false;
			return true;
		});
	}

	// A pure value needs its own `var tN = ...;` only if REUSED; a single consumer inlines it, recomputing being valid wherever its inputs are.
	// `allowReuse` exempts only that last heuristic (a literal is free to duplicate), never the structural checks above it.
	needsTemp(node: Node<E, S, T>, allowReuse = false): boolean {
		// A named theta's condition edge is never read by codegen: a test feeding two loop-carried thetas would otherwise look reused.
		const consumers = (node.outputs[0] ?? []).filter(e => !this.graph.getNode(e.nodeId).isVestigialEdge(e.port) && !this.isCollapsingGammaValueCondition(e));
		// A member-access callee (`obj.method`) never becomes a temp, which would lose its receiver.
		if (node.type === 'member' && consumers.some(e => this.dialect.isCalleeEdge(this.graph.getNode(e.nodeId), e.port)))
			return false;
		// A mu's initial-value/feedback port or a rebind's old-value port needs the producer by name (`mustNameOwnValue`).
		if (consumers.some(e => mustNameOwnValue(this.graph.getNode(e.nodeId), e.port)))
			return true;
		// A postfix ++/--'s old-value snapshot freezes the value before the increment: inlined later, it reads the mutated value.
		if (node.type === 'unary_post_old')
			return consumers.length > 0;
		// A consumer that is never emitted (suppressed, inside a verbatim statement) cannot recompute it: the verbatim text names the variable.
		if (consumers.some(e => this.graph.getNode(e.nodeId).suppressed))
			return true;
		// A value GCM scheduled SHALLOWER than a consumer is loop-invariant to it: inlined, it would be recomputed every iteration.
		if (this.blockIds && this.blocks) {
			const ownDepth = this.blocks.getLoopDepth(this.blockIds.get(node.id));
			if (consumers.some(e => this.blocks!.getLoopDepth!(this.blockIds!.get(e.nodeId)) > ownDepth))
				return true;
		}
		return !allowReuse && consumers.length > 1;

		// A consumer needing its producer BY NAME whatever the reuse count: a mu's initial-value/feedback port (never read through resolveNode, so
		// `i = i + 1;` would vanish), or a rebind's old-value port (inlining would make the mutation a recompute).
		function mustNameOwnValue(consumer: Node<E, S, T>, port: number): boolean {
			if (consumer.type === 'mu' || consumer.type === 'muValue')
				return true;
			if (port !== 0)
				return false;
			return consumer.type === 'unary_post' || consumer.type === 'mutation';
		}

	}

	// A named slot (a plain reassignment or a merge) its sole consumer resolves lazily, by needsTemp's criteria: a merge printed by name is only
	// correct where something printed `name = ...;`, not guaranteed for a pure value merge.
	isInlinableSlot(node: Node<E, S, T>): boolean {
		return !node.forcedPrint
			&& ((node.type === 'mutation' && !!node.plainAssign) || node.type === 'gammaValue')
			&& ((node.type === 'gammaValue' && !!node.neverMaterialize) || !this.needsTemp(node));
	}

	// Whether this value reaches printed code: an inlinable slot prints nowhere, so its consumers are followed; anything else surfaces where it stands.
	// A chain that only loops back to itself surfaces nothing.
	surfacesValue(node: Node<E, S, T>, visiting = new Set<NodeId>()): boolean {
		if (!this.isInlinableSlot(node))
			return true;
		if (visiting.has(node.id))
			return false;
		visiting.add(node.id);
		const surfaces = this.valueConsumers(node).some(e => this.surfacesValue(this.graph.getNode(e.nodeId), visiting));
		visiting.delete(node.id);
		return surfaces;
	}

	// A function subgraph's body, its own region (entry/RETURN_ANCHOR pair, scope); `returnNodeId` is the only way to the RETURN_ANCHOR.
	rebuildFunctionBody(entryNode: NodeOf<E, S, T, 'function'>): S[] {
		const returnNode		= this.graph.getNode(entryNode.returnNodeId);
		// A fresh `names` frame per function body.
		this.names.push();
		const bodyStatements	= this.emitChain(returnNode.inputs[0].nodeId, entryNode.id);

		// Unconnected: the body fell off its end, so no trailing statement.
		if (returnNode.inputs[1])
			bodyStatements.push(this.makeReturn(this.resolveOperand(returnNode.id, 1)));
		this.names.pop();
		return bodyStatements;
	}

	// `control`'s reconstruction among the pure nodes GCM co-scheduled with it: DEPENDENCIES first (a value shared by CSE is registered before the
	// branch resolves it), then `middle()`, then DEPENDENTS. `middle` is a thunk so its emitChain runs after the dependency half.
	withCoScheduled(nodes: NodeId[], controlId: NodeId, middle: () => S[]): S[] {
		const sortedIds	= this.localTopologicalSort(nodes);
		const i			= sortedIds.indexOf(controlId);
		// Array-literal elements evaluate left to right, so the dependency half runs before `middle()`.
		return [
			...this.emitLocalStatements(sortedIds.slice(0, i)),
			...middle(),
			...this.emitLocalStatements(sortedIds.slice(i + 1)),
		];
	}

	// A control anchor's contribution to its statement list: the if/switch/try/while/function it anchors with its co-scheduled pure nodes, or just
	// those nodes for an anchor with no nested structure (a call, a declaration, PROGRAM_START).
	emitControlNode(control: Node<E, S, T>): S[] {
		const nodes = this.nodesAt(control.id);

		if (control.type === 'gamma')
			return this.withCoScheduled(nodes, control.id, () => {
				// Ports: 0 = predecessor, 1 = condition, 2 = true tail, 3 = false tail.
				const predecessorId	= control.inputs[0].nodeId;
				const trueStmts		= this.emitChain(control.inputs[2].nodeId, predecessorId);
				// A false tail that never left the branch point means no `else`; a genuinely empty one still prints `else {}`.
				const falseStmts	= control.inputs[3].nodeId !== predecessorId ? this.emitChain(control.inputs[3].nodeId, predecessorId) : undefined;
				// Unless BOTH arms are empty: the branch's content is the value it merges, printed where consumed, and `if (c) {}` would repeat the condition.
				// The condition stays when it carries an effect (it prints nowhere else), unless it has a temp of its own.
				const conditionId = control.inputs[1].nodeId;
				if (trueStmts.length === 0 && !falseStmts?.length
					&& (this.nodeVariableNames.has(conditionId) || this.graph.isPureSubgraph(this.graph.getNode(conditionId))))
					return [];
				return [this.makeIf(this.resolveOperand(control.id, 1), trueStmts, falseStmts)];
			});

		if (control.type === 'break_scope')
			return this.withCoScheduled(nodes, control.id, () => {
				// A real `switch`/`case`: break_scope's one creation site always stamps switchCases.

				// The discriminant's and case tests' schedule follows their graph consumers, so it usually lands where this reconstruction never visits:
				// forced here, unless another surviving value forced it under the same name.
				const forceDeclare = (id: NodeId): S[] => {
					const n = this.graph.getNode(id);
					return n.type === 'var' && !this.names.has(n.name)
						? this.emitLocalStatements([id]) : [];
				};
				const cases = control.switchCases!.map(c => ({
					test:		c.testNodeId ? this.resolveNode(c.testNodeId) : undefined,
					consequent:	this.emitChain(c.tailId, c.boundaryId),
				}));

				// A case body left with only its `break;` (its value elided into the merge): if every case is, the dispatch is a no-op and drops.
				const isNoOp = (stmts: S[]) => stmts.length === 0 || (stmts.length === 1 && this.isBreakStmt(stmts[0]));

				return [
					...forceDeclare(control.switchDiscriminantId!),
					...control.switchCases!.flatMap(c => c.testNodeId ? forceDeclare(c.testNodeId) : []),
					...(cases.every(c => isNoOp(c.consequent)) ? [] : [this.makeSwitch(this.resolveNode(control.switchDiscriminantId!), cases)]),
				];
			});

		if (control.type === 'except')
			return this.withCoScheduled(nodes, control.id, () => {
				// Ports: 0 = predecessor, 1 = try's tail, 2 = catch's tail, 3 = finally's tail.
				const predecessorId	= control.inputs[0].nodeId;
				const tryStmts		= this.emitChain(control.inputs[1].nodeId, predecessorId);
				const catchStmts	= this.emitChain(control.inputs[2].nodeId, predecessorId);
				// finally's tail (port 3) anchors on `control` itself: its first statement's predecessor is the except node.
				const finallyEdge	= control.inputs[3];
				const finallyStmts	= finallyEdge ? this.emitChain(finallyEdge.nodeId, control.id) : undefined;
				const handlerType	= control.handlerTypeNodeId !== undefined ? this.resolveNode(control.handlerTypeNodeId) : undefined;
				return [this.makeTry(tryStmts, { param: control.catchParam, type: handlerType, body: catchStmts }, finallyStmts)];
			});

		// A DECLARATION; a function EXPRESSION is a value, emitted by emitLocalStatements.
		if (control.type === 'function' && !control.expr)
			return this.withCoScheduled(nodes, control.id, () => [
				this.rebuildFunctionDecl(control, this.rebuildFunctionBody(control)),
			]);

		if (control.type === 'mu') {
			const thetaEdge	= (control.outputs[0] ?? []).find(e => this.graph.get(e.nodeId)!.type === 'theta');
			const thetaNode	= thetaEdge && this.graph.getNode(thetaEdge.nodeId);

			// The mu's block holds the mu and loop-body computation depending only on it; anything with a real effect continues from the body's entry (port 1).
			const ownIds		= nodes.filter(id => id !== control.id);

			const statements: S[] = [];

			if (thetaNode) {
				const testId	= thetaNode.inputs[1].nodeId;
				const testNode	= this.graph.getNode(testId);
				// The test's only REAL reader (besides itself) is normally the state-theta's own
				// condition port -- everything else pointing at it is vestigial.
				const onlyReadByLoopExit = (testNode.outputs[0] ?? []).filter(e => !this.graph.getNode(e.nodeId).isVestigialEdge(e.port))
					.every(e => e.nodeId === thetaNode!.id);
				// Emitted before restOfBody, same CSE-registration reasoning as the gamma case above.
				const testStatements	= onlyReadByLoopExit ? [] : this.emitLocalStatements([testId]);
				const restStatements	= this.emitLocalStatements(ownIds.filter(id => id !== testId));
				const restOfBody		= this.emitChain(control.inputs[1].nodeId, control.id);

				if (control.loopKind === 'do') {
					// No rotation: a do-while's body already runs before the test (seeing the mu's INITIAL value first).
					statements.push(this.makeDoWhile([
						...restOfBody,
						...restStatements,
						...testStatements
					], this.resolveOperand(thetaNode.id, 1)));
				} else {
					// LOOP ROTATION: the condition needs values that exist only inside the body, so `while (true) { <cond>; if (!cond) break; body }`. A condition
					// resolving to the literal `true` (`for(;;)`, a for-in desugar) drops its dead check.
					const condExpr = this.resolveOperand(thetaNode.id, 1);
					statements.push(this.makeLoop([
						...testStatements,
						...(this.dialect.truthy(this.dialect.literalValue(condExpr)) ? [] : [this.makeIf(this.makeNot(condExpr), [this.makeBreak()])]),
						...restStatements,
						...restOfBody
					]));
				}
			} else {
				// No exit condition found (every loop makes a state-theta, so not normally): reconstructed without rotation.
				const restStatements = this.emitLocalStatements(ownIds);
				const restOfBody = this.emitChain(control.inputs[1].nodeId, control.id);
				statements.push(this.makeLoop([...restStatements, ...restOfBody]));
			}

			if (thetaNode) {
				// What GCM scheduled into the state-theta's own block is emitted right after the loop: a pure value depending only on a named theta's exported value
				// has nothing to state-chain through.
				statements.push(...this.emitLocalStatements(this.nodesAt(thetaNode.id).filter(id => id !== thetaNode!.id)));
			}

			return statements;
		}

		return this.emitLocalStatements(nodes);
	}

	// The statement span (fromId, boundaryId] in execution order: walking inputs[0] backward (one state predecessor per anchor), each node's own part
	// appended AFTER recursing. A forward walk would tie between several consumers of one state token (each branch's entry and the merge).
	emitChain(fromId: NodeId | undefined, boundaryId: NodeId): S[] {
		if (fromId === undefined || fromId === boundaryId)
			return [];
		const node = this.graph.getNode(fromId);
		// A state-theta's predecessor IS its loop's mu, which reconstructs the whole loop once; theta prints nothing itself.
		if (node.type === 'theta')
			return this.emitChain(node.inputs[0]?.nodeId, boundaryId);
		return [...this.emitChain(node.inputs[0]?.nodeId, boundaryId), ...this.emitControlNode(node)];
	}

	// A declaration's initializer needs no printed value when nothing needs it under the name: dead, or its one reader recomputes the pure initializer.
	// Only when pure; never for a capturedRead, as recomputing is safe only within one execution.
	isInlinableVarDecl(node: Node<E, S, T>): boolean {
		// declKind: a PARAM is also a bare 'var' node, its input the entry (plumbing, not an initializer); resolveNode reads it by name.
		if (node.type !== 'var' || !node.inputs[0] || node.capturedRead || node.declKind === undefined)
			return false;
		// needsTemp's reuse heuristic avoids recomputing an expensive expression, which a literal is not (`allowReuse`); its structural checks stay.
		return !this.needsTemp(node, isLiteral(this.dialect, this.graph.getNode(node.inputs[0].nodeId)));
	}

	// True if another node bound to `name` is forcedPrint: it prints its own `name = ...;`, so dropping the declaration would leave it undeclared.
	// A graph-wide scan, as forcedPrint is final only after BuildVSDG.
	hasForcedSibling(name: string, excludeId: NodeId): boolean {
		for (const other of this.graph.values()) {
			if (other.id !== excludeId && slotName(other) === name && other.forcedPrint)
				return true;
		}
		return false;
	}

	resolveOperand(to: NodeId, slot: number): E {
		const edge = this.graph.getNode(to).inputs[slot];
		if (!edge)
			throw new Error(`Missing operand edge for slot ${slot} on node ${to}`);
		return this.resolveNode(edge.nodeId);
	}

	// A mutation TARGET (a member/index address, stamped `freshTarget`) always reconstructs fresh: the object or property may hold a DIFFERENT value once
	// the mutation runs, so a cached temp would name the wrong thing. Every other shape resolves through resolveNode.
	resolveTarget(to: NodeId, slot: number): E {
		const edge = this.graph.getNode(to).inputs[slot];
		if (!edge)
			throw new Error(`Missing operand edge for slot ${slot} on node ${to}`);
		const opNode = this.graph.getNode(edge.nodeId);
		return opNode.freshTarget ? this.buildExpr(opNode) : this.resolveNode(opNode.id);
	}

	resolveNode(id: NodeId): E {
		const node = this.graph.getNode(id);

		// Switch's bookkeeping always resolves by name: its mutation is never printed, and folding its value into a ternary would merge a flag meant
		// to stay independent at every read.
		const switchInternalName = node.switchInternal ? slotName(node) : undefined;
		if (switchInternalName !== undefined)
			return this.dialect.identifier(switchInternalName);

		// A name rebound inside a statement printed VERBATIM is defined only by that text: resolved by name, not folded (`x = 1; with f(): x = 2; print(x)`).
		const suppressedName = node.suppressed ? slotName(node) : undefined;
		if (suppressedName !== undefined)
			return this.dialect.identifier(suppressedName);

		switch (node.type) {
			// A declaration left bare (`isInlinableVarDecl`) never assigned its name: its sole reader inlines the initializer. Not with a forced sibling,
			// which resolves by name, and a merge combining them would lose the `cond ? x : x` collapse.
			case 'var':
				if (this.isInlinableVarDecl(node) && !this.hasForcedSibling(node.name, node.id))
					return this.resolveOperand(id, 0);
				// A param (no declKind) is safe by name. A local declaration rebuilds its initializer inline unless `names` confirms it printed: a bare 'var'
				// read always means this declaration's initializer.
				if (!node.declKind || this.names.has(node.name))
					return this.dialect.identifier(node.name);
				return this.resolveOperand(id, 0);

			// A muValue is a real loop-carried variable, always materialized: safe by name.
			case 'muValue':
				return this.dialect.identifier(node.name);

			// A thetaValue's value IS its mu's: it only marks where a loop-carried variable is readable again after the loop.
			case 'thetaValue':
				return this.resolveOperand(id, 1);
		}

		// `names` confirms the statement printed somewhere reachable; else it rebuilds inline rather than name an undeclared identifier.
		const name = slotName(node);
		if (name !== undefined && !this.isInlinableSlot(node) && this.names.has(name))
			return this.dialect.identifier(name);

		const varName = this.nodeVariableNames.get(id);
		if (varName)
			return this.dialect.identifier(varName);

		// Not printed anywhere reachable (typically a pure value in a block no wrapper reaches): built inline, which for a pure value is safe;
		// an effect goes through emitLocalStatements, so no call runs twice.
		return this.buildExpr(node);
	}

	// A simple local dependency sorter for a single block's nodes
	localTopologicalSort(ids: NodeId[]): NodeId[] {
		const sorted: NodeId[] = [];
		const visited = new Set<NodeId>();
		const nodeSet = new Set(ids);
		// Nodes OUTSIDE nodeSet searched through, never pushed to `sorted`, with their own cycle guard.
		const walkedThrough = new Set<NodeId>();

		// mu/theta/literal (and a bare 'var' read) resolve directly; following a mu's feedback edge would be both unneeded and cyclic.
		const hasOrderedInputs = (node: Node<E, S, T>) =>
			node.type !== 'mu' && node.type !== 'muValue' && node.type !== 'theta' && node.type !== 'thetaValue' && !isLiteral(this.dialect, node)
			&& (node.type !== 'var' || node.declKind !== undefined);

		// Everything `node` depends on is emitted first, TRANSITIVELY through inlined inputs: `let e = i + len;` orders `i` before `e`.
		const visitDeps = (node: Node<E, S, T>) => {
			if (!hasOrderedInputs(node))
				return;
			for (const edge of node.inputs) {
				if (!edge)
					continue;
				if (nodeSet.has(edge.nodeId)) {
					visit(edge.nodeId);
				} else if (!walkedThrough.has(edge.nodeId)) {
					walkedThrough.add(edge.nodeId);
					visitDeps(this.graph.getNode(edge.nodeId));
				}
			}
		};

		const visit = (id: NodeId) => {
			if (visited.has(id))
				return;
			// Visited BEFORE recursing: a mu's feedback edge is a genuine back-edge, so a cycle reaching back here is skipped.
			visited.add(id);
			visitDeps(this.graph.getNode(id));
			sorted.push(id);
		};

		for (const id of ids)
			visit(id);

		return sorted;
	}

	emitLocalStatements(ids: NodeId[]): S[] {
		const statements: S[] = [];

		for (const id of this.localTopologicalSort(ids)) {
			const node = this.graph.getNode(id);

			// What a verbatim statement says in full: emitting it again would run its insides twice.
			if (node.suppressed)
				continue;

			if (node.type === 'marker') {
				// Most markers print nothing, but a user's break/continue/throw/return does (a bare `return;` leaves port 1 unconnected).
				if (node.name === 'BREAK_MARKER')
					statements.push(this.makeBreak());
				else if (node.name === 'CONTINUE_MARKER')
					statements.push(this.makeContinue());
				else if (node.name === 'THROW_MARKER')
					statements.push(this.makeThrow(this.resolveOperand(id, 1)));
				else if (node.name === 'EARLY_RETURN_MARKER')
					statements.push(this.makeReturn(node.inputs[1] ? this.resolveOperand(id, 1) : undefined));
				continue;
			}

			// An effectful call, or a function/arrow/lambda EXPRESSION (both a value and a sequence point).
			if (node.type === 'effect' || (node.type === 'function' && node.expr)) {
				// buildExpr: a function expression's payload IS this language's expr, so no language spells that case out.
				const value = this.buildExpr(node);
				// Inlined with EXACTLY ONE live consumer: its fixed position caps the consumer's schedule, and rebuilding keeps state-chain order. A consumer
				// printed nowhere (an inlinable slot) counts only through its own, followed all the way down; with none, it prints as a bare statement.
				const live = this.valueConsumers(node).filter(e => this.surfacesValue(this.graph.getNode(e.nodeId)));
				if (live.length === 1)
					continue; // deferred -- the sole consumer inlines it via resolveNode's fallback
				// A dialect-declared "only rewrites that binding" effect with no live reader is a dead store (`i++;` never read again). Readers are scanned raw:
				// a loop-carried read arrives on a mu's feedback port (`for (...; i++)` stays). A member target or a call cannot claim this, and still prints.
				const mutated	= node.type === 'effect' && node.mutatesBindingId !== undefined
					? this.graph.getNode(node.mutatesBindingId) : undefined;
				const observed	= !!mutated && (mutated.outputs[0] ?? [])
					.some(e => !this.graph.getNode(e.nodeId).isVestigialEdge(e.port)
						&& this.surfacesValue(this.graph.getNode(e.nodeId)));
				if (live.length === 0 && mutated && !observed)
					continue;
				statements.push(live.length
					? this.makeTempDecl(this.makeTempVar(id), value)
					: this.makeExpressionStmt(value)
				);
				continue;
			}

			const name = slotName(node);
			if (name !== undefined) {
				// A reassignment or merge prints under its name only if reused; forcedPrint (an exited branch's reassignment) always prints.
				if (this.isInlinableSlot(node))
					continue;
				// A named except gets no statement: each branch prints its own `x = ...;` (forcedPrint); it exists for GCM's placement of readers.
				if (node.type === 'exceptValue')
					continue;
				const namedStmt = this.emitNamedSlot(name, node);
				if (namedStmt)
					statements.push(namedStmt);
				continue;
			}

			// A pure literal is read directly by resolveNode, never a statement of its own.
			if (isLiteral(this.dialect, node))
				continue;

			switch (node.type) {
				case 'var':
				case 'mu':
				case 'muValue':
				case 'theta':
				case 'thetaValue':
					// No statement of their own -- read directly by resolveNode. (markers and effect/
					// function-expression values are already handled above.)
					break;

				case 'passthru':
					// A codeless declaration (interface/alias/enum, or a construct this language does not model) prints verbatim, whatever its references.
					statements.push(this.emitPassthru(node));
					break;

				case 'class_decl':
					// The language's own rebuildClass splices VSDG's resolution of heritage/keys/
					// method-bodies back into the otherwise-verbatim class before printing.
					statements.push(this.rebuildClassDecl(node));
					break;

				case 'function':
					// A declaration is intercepted by emitControlNode and a function expression handled above: a no-op rather than a misprint.
					break;

				default:
					// forcedPrint: an unnamed effect with no value consumer, which needsTemp alone would drop. A mutation rebuilds as a STATEMENT (a language may lack
					// assignment expressions), not its value form (`y = (x = 1)` reads only the right-hand side).
					if (node.forcedPrint) {
						statements.push(node.type === 'mutation'
							? this.rebuildMutationStatement(node)
							: this.makeExpressionStmt(this.buildExpr(node)));
					} else if (this.needsTemp(node)) {
						statements.push(this.makeTempDecl(this.makeTempVar(id), this.buildExpr(node)));
					}
					// Else single-use and same-block: unmaterialized, its consumer inlines it.
			}
		}

		return statements;
	}

	// A node reached by the state chain's port-2 rebind convention that prints under its own name wherever placed: a rebind or a local declaration,
	// unlike a merge (a pure value with no state anchor).
	needsDirectPlacement(node: Node<E, S, T>): boolean {
		switch (node.type) {
			case 'unary_post':	return true;
			// A TYPE is a declaration too (C++ has no declaration keyword); a declKind would let `isInlinableVarDecl` elide the value, making a target `0 = 1`.
			case 'var':			return node.declKind !== undefined || node.typeAnnotation !== undefined;
			case 'mutation':	return !(node.plainAssign && this.isInlinableSlot(node));
			default:			return false;
		}
	}

	// Which nodes GCM scheduled into a block, grouped once. A node missing from blockIds is in no block's list: resolveNode inlines it where read.
	blockNodes(blockId: BlockId): NodeId[] {
		if (!this.blockNodesCache) {
			this.blockNodesCache = new Map();
			for (const id of this.graph.keys()) {
				const bId = this.blockIds?.get(id);
				if (bId === undefined)
					continue;
				if (!this.blockNodesCache.has(bId))
					this.blockNodesCache.set(bId, []);
				this.blockNodesCache.get(bId)!.push(id);
			}
		}
		return this.blockNodesCache.get(blockId) ?? [];
	}
	// Which nodes GCM scheduled with an anchor: at least the anchor itself (GCM's convention), so emitControlNode prints a plain call. Also a rebind whose
	// port-2 trigger is this anchor: needsTemp forces it, so it needs a real, positioned statement even unscheduled.
	nodesAt(anchorId: NodeId): NodeId[] {
		const bId = this.blockIds?.get(anchorId);
		if (bId !== undefined)
			return this.blockNodes(bId);
		const ids = [anchorId];
		for (const edges of this.graph.getNode(anchorId).outputs) {
			if (!edges)
				continue;
			for (const e of edges) {
				if (e.port === 2 && this.needsDirectPlacement(this.graph.getNode(e.nodeId)))
					ids.push(e.nodeId);
			}
		}
		return ids;
	}

	// A per-variable merge (gammaValue, or a 'conditional' floating) as a ternary; the state gamma is a real if/else (emitControlNode).
	buildConditional(node: Node<E, S, T>): E {
		const consequent	= this.resolveOperand(node.id, 1);
		const alternate		= this.resolveOperand(node.id, 2);
		// Both operands may resolve to the SAME name (a broken-out merge): `cond ? x : x` is `x`, while the condition is PURE, since this ternary
		// is the condition's one printed place.
		const cName = this.dialect.identifierName(consequent);
		if (cName !== undefined && cName === this.dialect.identifierName(alternate)
			&& this.graph.isPureSubgraph(this.graph.getNode(node.inputs[0].nodeId)))
			return consequent;
		return this.makeConditional(this.resolveOperand(node.id, 0), consequent, alternate);
	}

	buildExpr(node: Node<E, S, T>): E {
		switch (node.type) {
			case 'gammaValue':
				return this.buildConditional(node);

			// An unmaterialized effectful call or function expression, resolved by its consumer (a function expression prints verbatim). A 'mutation' read as a
			// VALUE was superseded by a merge (`y = (x = 1)`): its value is what is needed.
			case 'floating':
			case 'mutation':
			case 'effect':
			case 'member':
			case 'unary_post':
			case 'unary_post_old':
				return this.rebuildPayload(node);
			case 'function':
				if (node.expr)
					return node.expr;
				break;
		}
		throw new Error(`not handling value node ${node.type}`);
	}

	// ---- this language's reconstruction half ----

	/** Rebuilds a node's own expression payload: a pure value, a mutation read as a VALUE, an effect, a member select, a ++/--. */
	abstract rebuildPayload(node: Node<E, S, T>): E;
	/** Rebuilds a mutation as its own STATEMENT (Python's assignment isn't an expression at all). */
	abstract rebuildMutationStatement(node: Node<E, S, T>): S;
	/** A name's own printed statement: its declaration, its first assignment, or a reassignment. */
	abstract emitNamedSlot(name: string, node: Node<E, S, T>): S | undefined;
	abstract emitPassthru(node: NodeOf<E, S, T, 'passthru'>): S;
	abstract rebuildClassDecl(node: NodeOf<E, S, T, 'class_decl'>): S;
	abstract rebuildFunctionDecl(node: NodeOf<E, S, T, 'function'>, body: S[]): S;

	/**
	* The structural statements a reconstruction needs. Bodies are STATEMENT ARRAYS, wrapped by the language (js/c take one statement, py a list).
	* An `undefined` alternate is no else; an EMPTY body is a genuinely empty one, still spelled (`else {}`, `else: pass`).
	*/
	abstract makeBlock(body: S[] | undefined): S|S[]|undefined;
	abstract makeSwitch(discriminant: E, cases: { test?: E, consequent: S[] }[]): S;
	/**
	* A try/handler/finally; a handler is a bound name, the type it MATCHES (where `except` can be typed), and its body.
	*/
	abstract makeTry(body: S[], handler: { param?: string, type?: E, body: S[] }, finalizer?: S[]): S;
	abstract makeThrow(argument: E): S;
	abstract makeTempDecl(name: string, value: E): S;

	// Shapes every AST SHARES (common.ts's constructors), overridden only where a language differs. Handing one back as `S`/`E` takes ONE assertion:
	// a constraint is a lower bound, so `S` may not contain `Common.If` as far as the compiler knows; it is stated once, in `admit`/`admitExpr`.


	makeIf(test: E, cons: S[], alt?: S[]): S		{ return admit(If(test, this.makeBlock(cons), this.makeBlock(alt))); }
	makeLoop(body: S[]): S							{ return admit(While(Literal(true), this.makeBlock(body))); }
	makeDoWhile(body: S[], test: E): S				{ return admit(DoWhile(this.makeBlock(body), test)); }
	makeReturn(argument?: E): S 					{ return admit(Return(argument)); }
	makeBreak(): S									{ return admit({ type: 'break' }); }
	makeContinue(): S								{ return admit({ type: 'continue' }); }
	makeExpressionStmt(value: E): S					{ return admit(ExprStmt(value)); }
	makeConditional(test: E, cons: E, alt: E): E	{ return admitExpr(Conditional(test, cons, alt)); }
	makeNot(value: E): E							{ return admitExpr(Unary('!', value)); }
	isBreakStmt(stmt: S): boolean					{ return stmt.type === 'break'; }
}

const CONTROL = new Set<string>(['effect', 'marker', 'gamma', 'gammaValue', 'mu', 'muValue', 'theta', 'thetaValue', 'break_scope', 'except', 'exceptValue', 'function', 'passthru', 'class_decl']);

// ===================================================================
//  Optimisation
// ===================================================================

export function optimize<E, S, T>(graph: VSDG, dialect: Dialect<E, S, T>): void {
	const protectedIds = collectProtectedNodeIds(graph);
	for (let changed = true; changed; ) {
		changed = false;

		for (const node of graph.values()) {
			// 1. Fold constant operations.
			if (node.type === 'floating' && foldConstants(graph, dialect, node))
				changed = true;

			// 2. Eliminate dead if/else branches.
			if (foldDeadBranches(graph, dialect, node, protectedIds))
				changed = true;
		}

		// 3. Merge identical pure computations, once per round: folding can make two expressions identical, and CSE a condition constant.
		if (optimizeStructuralCSE(graph, dialect, protectedIds))
			changed = true;
	}
}

function foldConstants<E, S, T>(graph: VSDG, dialect: Dialect<E, S, T>, node: NodeOf<E, S, T, 'floating'>): boolean {
	// A 'mutation' never folds: a bare literal would discard its effect. The dialect's `foldable` decides the rest.
	const arity = dialect.foldable(node.expr);
	if (!arity)
		return false;

	const operands: unknown[] = [];
	for (let i = 0; i < arity; i++) {
		const edge = node.inputs[i];
		const producer = edge && graph.get(edge.nodeId);
		if (!producer || !isLiteral(dialect, producer))
			return false;
		operands.push(dialect.literalValue(producer.expr));
	}

	const r = dialect.fold(node.expr, operands);
	if (r === undefined)
		return false;

	// Folded in place into the language's literal form (the same 'floating' tag, so no consumer is rewired), its incoming edges dropped;
	// `dialect.literalValue` reads it back. `foldable` already proved an expr-carrying tag.
	(node as Node<E, S, T> & { expr: E }).expr	= r;
	graph.removeInputs(node);
	return true;
}

// Every NodeId referenced OUTSIDE the inputs/outputs graph (switchCases, returnNodeId, classInfo, ...): the optimiser only rewires edges, so a
// node reachable only this way must never be removed or merged.
export function collectProtectedNodeIds(graph: VSDG): Set<NodeId> {
	// `[graph.root]`: a NodeId is a string, and `new Set('gamma7')` is its CHARACTERS.
	const ids = new Set<NodeId>([graph.root]);
	for (const node of graph.values()) {
		if (node.type === 'function')
			ids.add(node.returnNodeId);
		if (node.type === 'except' && node.handlerTypeNodeId !== undefined)
			ids.add(node.handlerTypeNodeId);
		if (node.type === 'break_scope') {
			if (node.switchDiscriminantId !== undefined)
				ids.add(node.switchDiscriminantId);
			for (const c of node.switchCases ?? []) {
				if (c.testNodeId !== undefined)
					ids.add(c.testNodeId);
				ids.add(c.boundaryId);
				ids.add(c.tailId);
			}
		}
		if (node.classInfo) {
			if (node.classInfo.superClassNodeId !== undefined)
				ids.add(node.classInfo.superClassNodeId);
			for (const m of node.classInfo.members) {
				if (m.keyNodeId !== undefined)
					ids.add(m.keyNodeId);
				if (m.entryNodeId !== undefined)
					ids.add(m.entryNodeId);
				if (m.valueNodeId !== undefined)
					ids.add(m.valueNodeId);
			}
		}
	}
	return ids;
}

function foldDeadBranches<E, S, T>(graph: VSDG, dialect: Dialect<E, S, T>, node: Node<E, S, T>, protectedIds: Set<NodeId>): boolean {
	// We are looking for Gamma nodes (gammaValue or the state gamma)
	if (node.type !== 'gamma' && node.type !== 'gammaValue')
		return false;
	// Never remove a node an out-of-band NodeId field points at (`collectProtectedNodeIds`). The ROOT is a reference that can be MOVED instead,
	// so a constant-conditioned if/else at the end of a program still collapses.
	const wasRoot = node.id === graph.root;
	if (!wasRoot && protectedIds.has(node.id))
		return false;

	// A gammaValue has [condition, true, false] at ports 0/1/2; the state gamma has an extra
	// state-predecessor at port 0, shifting those three to ports 1/2/3.
	const port = node.type === 'gammaValue' ? 0 : 1;

	// Find the edge supplying the condition
	const condEdge = node.inputs[port];
	if (!condEdge)
		return false;

	const condNode = graph.getNode(condEdge.nodeId);

	// If the condition is a known constant (or truthy/falsy value)
	if (isLiteral(dialect, condNode)) {
		// Find the edge representing the winning path (true path, then false path)
		const winningEdge = node.inputs[dialect.truthy(dialect.literalValue(condNode.expr)) ? port + 1 : port + 2];
		if (!winningEdge)
			return false;

		// Bypass the gamma: each downstream consumer reads the winning branch's source directly (its own inputs[] changes).
		const winningNode = graph.getNode(winningEdge.nodeId);
		for (const subscribers of node.outputs) {
			for (const consumerEdge of subscribers) {
				graph.getNode(consumerEdge.nodeId).inputs[consumerEdge.port] = { nodeId: winningEdge.nodeId, port: winningEdge.port };
				(winningNode.outputs[winningEdge.port] ??= []).push({ nodeId: consumerEdge.nodeId, port: consumerEdge.port });
			}
		}
		// What read the merge now reads the surviving branch's tail, the end of the state chain.
		if (wasRoot)
			graph.root = winningEdge.nodeId;
		
		graph.removeNode(node);
		return true; // Graph was modified!
	}

	return false;
}

function getStructuralKey<E, S, T>(graph: VSDG, dialect: Dialect<E, S, T>, node: Node<E, S, T>): string {
	let key = node.type;
	// Three separate fields (expr/name/stmt); a 'member' never reaches here (excluded by the caller). How a 'floating' payload is told apart is the
	// dialect's business (`exprKey`).
	const payload = node as Node<E, S, T> & { expr?: E, name?: string, stmt?: S };
	if (payload.expr) {
		key += dialect.exprKey(payload.expr);
	} else if (payload.name !== undefined) {
		key += payload.name;
	} else if (payload.stmt) {
		key += dialect.stmtKey(payload.stmt);
	}

	return key + ':' + node.inputs.map(e => e ? `${e.nodeId}:${e.port}` : '').join(',');
}

export function optimizeStructuralCSE<E, S, T>(graph: VSDG, dialect: Dialect<E, S, T>, protectedIds: Set<NodeId>): boolean {
	let anyChanges = false;

	const structuralTable = new Map<string, Node<E, S, T>>();

	for (const node of graph.values()) {
		// Effects and control tokens are sequence-dependent; a 'mutation' is a distinct effect each time. Anything else whose VALUE may differ between two
		// identical-looking occurrences is the dialect's call (`isCSEUnsafe`).
		if (['mu', 'muValue', 'theta', 'thetaValue', 'gamma', 'gammaValue', 'effect', 'marker', 'function', 'member', 'mutation'].includes(node.type))
			continue;
		if (dialect.isCSEUnsafe(node))
			continue;

		const key = getStructuralKey(graph, dialect, node);

		const masterNode = structuralTable.get(key);

		// A protected node is never the one removed, nor registered as a later duplicate's master.
		if (masterNode && masterNode.id !== node.id && protectedIds.has(node.id))
			continue;

		if (masterNode && masterNode.id !== node.id) {

			// Every downstream consumer of `node` reads the master instead.
			node.outputs.forEach((subscribers, outputPort) => {
				for (const consumerEdge of subscribers) {
					const consumerNode = graph.getNode(consumerEdge.nodeId);

					consumerNode.inputs[consumerEdge.port] = {
						nodeId: masterNode.id,
						port: outputPort
					};

					(masterNode.outputs[outputPort] ??= []).push({
						nodeId: consumerNode.id,
						port: consumerEdge.port
					});
				}
			});

			graph.removeNode(node);
			anyChanges = true;
		} else {
			structuralTable.set(key, node);
		}
	}

	return anyChanges;
}

// ===================================================================
//  GCM
// ===================================================================

function findLeastCommonAncestor<N>(tree: Map<N, N>, a: N, b: N): N|null {
	const pathA = new Set<N>();

	for (let i: N|undefined = a; i; i = tree.get(i))
		pathA.add(i);

	for (let i: N|undefined = b; i; i = tree.get(i)) {
		if (pathA.has(i))
			return i; // Found the intersection point!
	}
	return null;
}

function isDeeperThan<N>(tree: Map<N, N>, a: N, b: N): boolean {
	let depthA = 0;
	for (let i: N|undefined = a; i; i = tree.get(i))
		depthA++;

	let depthB = 0;
	for (let i: N|undefined = b; i; i = tree.get(i))
		depthB++;

	return depthA > depthB;
}

// The program's branch/loop structure, from control anchors and their state predecessors alone; where floating nodes go is applyGlobalCodeMotion's job.

export class BlockTree {
	roots	= new Map<NodeId, BlockId>();
	control = new Map<BlockId, NodeId>();	// The reverse of rootBlocks
	tree	= new Map<BlockId, BlockId>();	// Maps a Block ID to its immediate parent Block ID in the Dominator Tree
	loopDepthMemo = new Map<BlockId, number>();

	constructor(public graph: VSDG) {
		// PROGRAM_START is the well-known 'block_entry', where BuildProgram starts.
		let blockCounter = 0;
		for (const [id, node] of graph.entries()) {
			switch (node.type) {
				case 'marker':
					if (node.name === 'PROGRAM_START') {
						this.roots.set(id, 'block_entry');
						break;
					}
					//fallthrough
				case 'effect':
				case 'function': case 'passthru': case 'class_decl':
				case 'gamma': case 'mu': case 'theta': case 'break_scope':
				case 'except':
					this.roots.set(id, `${node.type}_${blockCounter++}`);
					break;
			}
		}

		for (const [nodeId, blockId] of this.roots) {
			this.control.set(blockId, nodeId);
			const incomingStateEdge = graph.get(nodeId)?.inputs[0];
			if (incomingStateEdge)
				this.tree.set(blockId, this.roots.get(incomingStateEdge.nodeId) ?? '');
		}
	}
	// How many loops enclose a block: a state-mu's block is one deeper than its parent; a state-theta's block is its mu's EXIT, run once after
	// the loop, so at the loop's own parent's depth; any other inherits its parent's.
	getLoopDepth(id?: BlockId): number {
		if (id === undefined)
			return 0;
		const cached = this.loopDepthMemo.get(id);
		if (cached !== undefined)
			return cached;
		
		this.loopDepthMemo.set(id, 0); // defensive cycle guard; block_entry has no parent, so real cycles shouldn't occur
		const parentDepth	= this.getLoopDepth(this.getParent(id));
		const node			= this.control.has(id) ? this.graph.get(this.control.get(id)!) : undefined;

		let depth = parentDepth;
		if (node?.type === 'mu') {
			depth = parentDepth + 1;
		} else if (node?.type === 'theta') {
			const muBlockId		= this.roots.get(node.inputs[0].nodeId); // the state-theta's own mu
			depth = this.getLoopDepth(muBlockId && this.getParent(muBlockId));
		}
		this.loopDepthMemo.set(id, depth);
		return depth;
	}
	getRoot(id: BlockId) 								{ return this.roots.get(id); }
	getControl(id: BlockId) 							{ return this.control.get(id); }
	getParent(id: BlockId) 								{ return this.tree.get(id); }
	isDeeperThan(idA: BlockId, idB: BlockId) 			{ return isDeeperThan(this.tree, idA, idB); }
	findLeastCommonAncestor(idA: BlockId, idB: BlockId) { return findLeastCommonAncestor(this.tree, idA, idB); }

}

export function applyGlobalCodeMotion<E, S, T>(graph: VSDG) {
	const blockIds = new Map<NodeId, BlockId>();
	const blocks = new BlockTree(graph);

	// The function region a block belongs to: up the tree to 'block_entry' or a function's FUNCTION_BODY_START. Not the 'function' entry's block,
	// which both the body and the code after the declaration reach; only the body threads from the start marker.
	const regionRootMemo = new Map<BlockId, BlockId>();
	function regionRootOf(blockId: BlockId): BlockId {
		const cached = regionRootMemo.get(blockId);
		if (cached !== undefined)
			return cached;
		const control = blockId !== 'block_entry' ? graph.get(blocks.getControl(blockId)!) : undefined;
		let root = blockId;
		if (blockId !== 'block_entry' && !(control?.type === 'marker' && control.name === 'FUNCTION_BODY_START')) {
			const parent = blocks.getParent(blockId);
			root = parent !== undefined ? regionRootOf(parent) : blockId;
		}
		regionRootMemo.set(blockId, root);
		return root;
	}

	// A PARAM reading the function entry (ports >= 1) is unconditionally inside the function, unlike the entry's own block: scheduleEarly floors such
	// an edge here, or a value derived only from params is stranded outside the function.
	const functionBodyBlockMemo = new Map<NodeId, BlockId>();
	function functionBodyBlockOf(functionDeclId: NodeId): BlockId {
		const cached = functionBodyBlockMemo.get(functionDeclId);
		if (cached !== undefined)
			return cached;
		const bodyStart = (graph.get(functionDeclId)!.outputs[0] ?? [])
			.map(e => graph.get(e.nodeId)!)
			.find(n => n.type === 'marker' && n.name === 'FUNCTION_BODY_START');
		const block = (bodyStart && blocks.getRoot(bodyStart.id)) ?? blocks.getRoot(functionDeclId)!;
		functionBodyBlockMemo.set(functionDeclId, block);
		return block;
	}

	// Phase 1: everything as early as possible.
	const visitedEarly = new Set<NodeId>();

	function scheduleEarly(nodeId: NodeId) {
		if (visitedEarly.has(nodeId))
			return;
		visitedEarly.add(nodeId);


		// Anchors (control flow, effects) are pinned to their own blocks.
		const root = blocks.getRoot(nodeId);
		if (root) {
			blockIds.set(nodeId, root);
			return;
		}

		const node = graph.get(nodeId)!;// as NodeWithBlock;

		// The program's entry block, unless `scopeAnchorId` floors a `this`/`super` (no input edges) in its function.
		let earliestBlock = node.scopeAnchorId !== undefined ? functionBodyBlockOf(node.scopeAnchorId) : "block_entry";

		node.inputs.forEach((edge, port) => {
			if (!edge)
				return;
			// A mu's port 1 is its FEEDBACK, a genuine back-edge: its earliest position needs only its initial value (port 0) and anchors.
			if ((node.type === 'mu' || node.type === 'muValue') && port === 1)
				return;
			// A muValue's port 2 ties it to its mu's block, wrong for a trivial self-loop feedback, which proves it loop-invariant: skipping that floor is
			// what makes loop-invariant hoisting fall out of scheduleEarly.
			if (node.type === 'muValue' && port === 2 && node.inputs[1]?.nodeId === nodeId)
				return;
			scheduleEarly(edge.nodeId);
			// After its inputs: the deepest block among them. A param edge (port >= 1) of a 'function' (declaration or expression) uses its body block.
			const edgeBlock	= graph.get(edge.nodeId)!.type === 'function' && edge.port !== 0
				? functionBodyBlockOf(edge.nodeId)
				: blockIds.get(edge.nodeId);
			if (edgeBlock !== undefined && blocks.isDeeperThan(edgeBlock, earliestBlock))
				earliestBlock = edgeBlock;
		});

		blockIds.set(nodeId, earliestBlock);
	}

	for (const nodeId of graph.keys())
		scheduleEarly(nodeId);

	// Phase 2: down, to save execution.
	const visitedLate = new Set<NodeId>();

	function scheduleLate(nodeId: NodeId) {
		if (visitedLate.has(nodeId))
			return;
		visitedLate.add(nodeId);


		if (blocks.getRoot(nodeId))
			return;

		const node = graph.get(nodeId)!;

		for (const portChannels of node.outputs) {
			if (portChannels)
				for (const consumerEdge of portChannels)
					scheduleLate(consumerEdge.nodeId);
		}

		const isSchedulingIrrelevant = (consumerNode: Node<E, S, T>, port: number): boolean => {
			switch (consumerNode.type) {
				case 'mu':
				case 'muValue':		return port === 1;
				case 'gammaValue':	return port !== 0;
				case 'exceptValue': return true;
				case 'theta':		return port === 1;
				// A postfix's snapshot edge: vestigial as a value, but what keeps the snapshot from sinking past the increment.
				case 'unary_post':	return false;
				default:			return consumerNode.isVestigialEdge(port);
			}
		};

		let latestBlock: BlockId | null = null;

		for (const portChannels of node.outputs) {
			if (portChannels) {
				for (const consumerEdge of portChannels) {
					const consumerNode = graph.get(consumerEdge.nodeId)!;
					if (isSchedulingIrrelevant(consumerNode, consumerEdge.port))
						continue;

					let consumerBlock = blockIds.get(consumerEdge.nodeId)!;

					// A mu's port 0 (its INITIAL value) belongs to the block before the loop, its pre-header.
					if ((consumerNode.type === 'mu' || consumerNode.type === 'muValue') && consumerEdge.port === 0)
						consumerBlock = blocks.getParent(consumerBlock) || "block_entry";

					// A consumer in ANOTHER function's region (a captured variable read after its function returns) runs at a point this schedule cannot place;
					// as a constraint it would drag the node out of its function. forcedPrint keeps it from being dropped.
					if (regionRootOf(consumerBlock) !== regionRootOf(blockIds.get(nodeId)!))
						continue;

					latestBlock = latestBlock === null
						? consumerBlock
						: blocks.findLeastCommonAncestor(latestBlock, consumerBlock);
				}
			}
		}

		// Click's sinking: from the latest valid block up to the earliest, the SHALLOWEST (fewest loops), never above the inputs' floor. On a depth tie,
		// the one nearer the consumers, or a node is hoisted away from its sole consumer. Known gap: `let i = off, e = i + len;` can swap.
		const earliestBlock	= blockIds.get(nodeId)!;
		const floor			= blocks.getLoopDepth(earliestBlock);
		let bestDepth		= Infinity, bestBlock;

		// `currentBlock` guards a tree dead end that misses earliestBlock.
		let currentBlock: BlockId | undefined = latestBlock || earliestBlock;
		while (currentBlock !== undefined) {
			const depth = blocks.getLoopDepth(currentBlock);
			if (depth >= floor && depth < bestDepth) {
				bestDepth = depth;
				bestBlock = currentBlock;
			}
			// earliestBlock (depth === floor) is always a candidate, so `bestBlock` is set; the walk stops after it.
			currentBlock = currentBlock === earliestBlock ? undefined : blocks.getParent(currentBlock);
		}

		blockIds.set(nodeId, bestBlock!);
	}
	for (const nodeId of graph.keys())
		scheduleLate(nodeId);

	return { blocks, blockIds };
}
