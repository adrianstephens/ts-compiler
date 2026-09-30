import * as fs from 'fs';
import * as path from 'path';
import * as TS from './ts-parser';
import * as JS from './js-parser';
import * as T from './type-utils';
import * as W from '../wasm/codegen';
import { Literal, Identifier, Binary, Assign, Conditional, Member, hasMod, Module as CModule } from '@isopodlabs/tison/ast';
import { checkHoisted, checkImported, typeOf as checkerQuery, isOptionalChainLink, narrow, inferTypeArgMap as checkerInferTypeArgMap, isConstContext, flowSlotOf, checkedTypeOf, checkedCallOf, type CheckedCall, isPurePath, assignsToThis, collectHoistedLocals } from './checker';
import { Walker, walker, walkerB } from './walker';
import { makeAsm as makeAsm0 } from '../wasm/codegen';
import { foldConstants, BuildStateMachine, StateMachine, SuspendBoundary } from './transform';
import * as wasm from '@isopodlabs/binary_libs/wasm';
import * as WAT from '../wasm/wat-parser';

// TStoWasm -- TS-AST-to-wasm backend for a narrow static subset.
// Assumes ast already passed TStypeCheck. Emits a wasm.WasmModule directly (no WAT stage).
// Every gap below throws a clear error rather than silently miscompiling. Unlisted = fully supported;
// an item under a category is either a whole missing construct or the one unsupported edge of an
// otherwise-working one -- never a description of what does work.
//  - Control flow:
//    - a suspend point ('yield'/'await') directly inside a 'try' -- a separate, permanent scope
//      boundary (see the Async section below), unrelated to try/catch/throw/finally themselves,
//      which are fully supported everywhere else, including inside a generator/async function, a
//      constructor, or a 'reassignsThis' method
//    - labeled break/continue
//    - for-in over an extended (possibly-subclassed) class instance -- a dynamic object (a structural
//      '{[k: string]: V}'-typed value, or a mapped type resolving to that shape, e.g. walker.ts's own
//      'NodeMap<N>') takes the efficient '.keys()' path; any other, *sealed* (never-subclassed) class/
//      object-shape falls back to 'Object.entries', same restriction that has -- the receiver's real
//      runtime type isn't visible here, only its declared one, so a correct key set can't be produced
//    - for-of over a string or a general iterable
//  - Async (real suspend/resume generators and async/await exist -- see 'flattenStateMachine' in
//    transform.ts and 'compileGeneratorFunc'/'compileAsyncFunc' here; this compiler has no
//    host-driven asynchrony at all, so "async" only ever means internal ordering between compiled
//    code, never real external concurrency -- a permanent scope boundary, not a gap):
//    - 'yield*' delegation
//    - '.return()'/'.throw()' on a generator
//    - 'for-of'/'for-await-of' over a generator or other iterable (stays under the general
//      for-of-over-an-iterable gap below; call '.next()' manually instead)
//    - 'Promise.race'/'Promise.any'/'Promise.allSettled' (only 'Promise.all' exists)
//    - the standard 'new Promise((resolve, reject) => ...)' executor form ('resolve' is a plain
//      public method on this compiler's 'Promise<T>' instead)
//    - Promise rejection/'.catch' -- this compiler's 'Promise<T>' has no rejected state at all, so
//      there's nothing yet for a real 'try'/'catch' to observe even where one could otherwise wrap
//      an 'await' (which it still can't -- a suspend point directly inside a 'try' is its own,
//      separate, permanent boundary, listed under Control flow above)
//    - a generic async or generator function
//    - an async function or generator nested inside another closure, capturing that enclosing
//      function's own free variables (its own params/locals are captured into its frame fine --
//      only capturing an *outer* function's variables is unsupported)
//    - a non-nullable object/array/closure-typed local that's hoisted into a generator/async frame
//      (i.e. assigned before its first suspend point) without ever having a real initial value at
//      frame-construction time -- the frame is built via one real 'struct.new', which needs a
//      concrete value for every non-nullable field up front; declare it nullable, or give it a real
//      initial value at declaration, instead
//  - Classes:
//    - 'abstract'
//    - computed field names
//    - a field cycle (a field can't be of its own class's type, directly or indirectly)
//    - an object-typed field anywhere in a hierarchy that also uses 'extends' (needs 'struct.new' with
//      real values up front, instead of 'struct.new_default')
//    - a generic superclass reference's own type args being anything but a plain name/instantiation
//    - extending an array/scalar-backed class (a constructor with its own explicit 'return', e.g.
//      'Array<T>'-style)
//    - a static generic method whose own type parameter shares a name with its class's type parameter
//      (the method's own substitution silently collides with the class's -- give it a differently-named
//      type parameter instead)
//  - Functions:
//    - generic arrow/function expressions
//    - a function expression's own 'this'
//    - a named function expression referencing its own name
//    - a nested function declaration called above its own textual position in the same block (no
//      hoisting -- only callable from below it, same as a 'let'/'const' would be)
//    - a nested function declaration referencing itself as a value rather than calling itself directly
//      (only 'name(...)' inside its own body is supported, not e.g. returning/reassigning it)
//    - a closure literal referencing a top-level 'let'/'const' global directly (only its own enclosing
//      function's locals/params are recognized as capturable free variables -- assign the global to a
//      local first and capture that instead)
//  - Expressions:
//    - an object literal with no statically-known nominal target type (a plain 'type X = {...}' alias
//      from a var_decl/param/field/return annotation, or anywhere else a concrete target type threads
//      through -- see 'ensureObjectShape'; general structural inference/subtyping is not this case) --
//      a structural index-signature target ('{[k: string]: V}') is the one exception, routed to a
//      real dynamic object (see 'indexSignatureValueType')
//    - 'delete'/'in' on anything but a dynamic object's own bracket-indexed property ('delete obj[k]',
//      'k in obj') -- a plain object/class field, or an array element, has no real 'delete' to give
//      either one
//    - a tag function typed against the real 'TemplateStringsArray' specifically, rather than a plain
//      'string[]' ('.raw' isn't modeled)
//    - calling a closure read directly off an array element ('arr[i](x)') when the array's element
//      type is a named type alias to a function type rather than an inline function type (e.g.
//      'type Fn = () => number; arr: Fn[]') -- a checker 'declScope' stamping gap ('stampScope' skips
//      a ref that already carries a scope, so a type-arg node resolved once under the wrong scope
//      during generic instantiation stays stuck with it) leaves the alias unresolved at the call site
//      even though the same alias resolves fine as a plain variable's declared type; bind the element
//      to a local first ('const f = arr[i]; f(x);', which 'for...of' already does for you) instead
//    - narrowing an 'any'-typed value (e.g. a caught 'catch(e)') down to a concrete class for a
//      subsequent field/method access -- 'unwrapAs' deliberately discards an 'as' cast's asserted
//      type for every codegen-facing owner/field lookup, and even guarding with a real 'instanceof'
//      check (which the checker does correctly narrow on) doesn't reach codegen's own owner/field
//      resolution inside the guarded branch -- there is currently no way to narrow a caught 'any'
//      down to a concrete class by either route
//    - writing through an index ('arr[i] = x') on a receiver whose static type is a real union of
//      different struct-backed array-likes (e.g. 'Uint8Array | number[]') -- a *read* ('arr[i]')
//      dispatches per-member same as '.property' access does ('ensureUnionIndexDispatch'/
//      'ensureUnionFieldDispatch'), but there's no write-side equivalent ('set(i,v)' dispatch) yet
//  - Numbers:
//    - an i32/u32-targeted float-to-int coercion (bitwise ops, an explicit i32/u32-typed local, etc.)
//      of a non-finite (NaN/+-Infinity) or huge finite f64 value doesn't replicate real JS's exact
//      'ToInt32'/'ToUint32' (always 0 for a non-finite value, true modulo-2^32 wraparound for a huge
//      finite one) -- saturates to 0/i32::MIN/i32::MAX instead ('coerceTop', 'i32.trunc_sat_f64_s'/'_u')
//      -- well-defined and never trapping, just not bit-perfect for these edge values
//  - Destructuring:
//    - a rest property inside an *object* pattern ('{a, ...rest}' -- needs a genuinely new object type
//      holding an arbitrary 'all fields except these' shape, not modeled yet)
//  - Optional chaining ('?.'):
//    - chaining onto a getter (direct '?.' or continued from an earlier one)
//    - a guarded method call that isn't a plain user method (e.g. a 'Math'/prelude intrinsic)
//    - a guarded method call returning 'void'
//  - Types:
//    - enums
//    - namespaces
//    - decorators
//    - '++'/'--' on a nullable primitive (needs narrowing to non-null first, which codegen has no way
//      to track -- narrow into a local first instead)

type Expr			= TS.Expr;
type Type			= TS.Type;
type Stmt			= TS.Stmt;
type Module			= CModule<Stmt>;
type BindingTarget	= JS.BindingTarget;
type FunctionDecl	= JS.FunctionDecl<Type>;
type MethodMember	= JS.Method<Type>;
type CallNode		= Expr & { type: 'call' | 'new' };
// Its source node, or only the arguments of a call codegen makes itself.
type CallSite		= CallNode | Expr[];
const argsOf		= (call: CallSite) => Array.isArray(call) ? call : call.arguments;
const typeArgsOf	= (call: CallSite) => Array.isArray(call) ? undefined : call.typeArgs;
// What a parameter can escape from: a named function or a constructor.
type Callable		= { params: JS.Param<Type>[]; body?: Stmt[] };
type Scope			= T.Scope;
const Scope			= T.Scope;
const I				= wasm.I;

// ===================================================================
//  The TypeScript-side vocabulary
// ===================================================================
// The language-neutral half -- the physical type vocabulary, the codegen context and the module sections -- lives in `../wasm/codegen`, imported as `WT`.
// What is left here is either about a compiled FUNCTION's shape (`FuncSig` and friends, `Local`/`Global`), or a rule about TypeScript's own type *spellings*
// (`rawElemKind`); neither belongs in a language-neutral module. `T.isNullLiteral`/`T.LITERAL_PRIMITIVES`/`READONLY_ALIAS` are those spelling rules.
// `FuncSig` extends `WT.ClosureSig` with the binding data only argument-binding reads (`defaults`/`resolvedParams`/`restElem`), which is what lets `WT.Type` name no language type at all.
// That binding data is kept BESIDE each closure payload (`closureWtype`), not in it.

// A node codegen synthesized has no stamp of its own, and is typed over its parts' stamps.
const checkerTypeOf = (e: Expr, scope: Scope, widen = true, expected?: Type) => checkerQuery(e, scope, widen, expected, undefined, undefined, false, !checkedTypeOf(e));

// The element kind of a `RawArray<T>`: a typed-array tag names its own PACKED kind directly, since
// resolving it as a type would widen `u8` to `u32` and silently give byte storage an i32 element.
// A binding's type as its slot: an integer range named as the machine int it fits -- a bare range would widen back to
// `number` wherever the local is read through the scope.
function slotType<T0 extends Type | undefined>(t: T0): T0 | Type {
	const r = t && T.toRange(t);
	if (r?.base !== 'number' || !r.integer || r.min === undefined || r.max === undefined)
		return t;
	const w = W.intType(Number(r.min), Number(r.max));
	return w === 'f64' ? T.NUMBER : TS.RefType(w);
}

function rawElemKind(a: Type | undefined, resolve: (t: Type) => W.Type | undefined): W.ElementI {
	const m = a && T.machineOf(a, LIB_TYPES);
	return m ? W.notUnsigned(m) : W.elementKind(a && resolve(a));
}

// A machine type's slot, as a value or an asm operand: a narrow int is held in the 32-bit type it widens to.
const machineSlot = (m: T.Machine): W.Type => m === 'i8' || m === 'i16' ? 'i32' : m === 'u8' || m === 'u16' ? 'u32' : m;

const elementValueType = (kind: W.ElementI): W.Type => kind === 'ref' ? W.REF_ANY_NULLABLE : kind === 'i8' || kind === 'i16' ? 'i32' : kind;

const isInt32 = (w: W.Type | undefined): boolean => {
	const k = W.scalarKind(w);
	return k === 'i32' || k === 'u32';
};

const isBigLimbs = (w: W.Type): boolean => W.typeEq(W.isNullable(w) ? { ...w, nullable: false } : w, W.ARRAY.i32);

// A function value's own properties that its closure struct stores, by field index (after `code` and `env`).
export const CLOSURE_FIELDS = new Map([['length', 2]]);

// `defaults`: only ever set for a function TYPE with a bare `p?: T` (optional, no `=`) trailing param (`case 'function'`'s own comment);
// a closure *literal*'s own params can never be optional (a real, separate restriction, unaffected), so this stays `undefined` for every other producer.
// `resolvedParams`: those same params before flattening to bare `WasmType`s, needed by `emitCallArgs` when a default value itself reads an earlier parameter (`resolveParams`'s own comment), not a standalone literal.
// Set for a real user function/method/constructor, and for a function TYPE that carries defaults of its own -- a type derived from a declaration (`typeof f`, a method's type) keeps them.
interface FuncSig extends W.ClosureSig	{ defaults?: (Expr | undefined)[]; resolvedParams?: ResolvedParam[]; restElem?: ResolvedParam }
// A signature with `hasRest`/`defaults` definitely settled -- but `resolvedParams`/`restElem` are
// genuinely absent (no params at all, no rest), so they stay optional through `Required`.
type FullSig = Required<Omit<FuncSig, 'resolvedParams' | 'restElem'>> & Pick<FuncSig, 'resolvedParams' | 'restElem'>;
interface FuncInfo extends FuncSig	{ funcIndex: number; typeIndex: number, body?: wasm.FuncBody; reassignsThis?: boolean }
export interface Inline extends FuncSig	{ inline: wasm.Instr[] }
interface ClosureTypeInfo			{ funcTypeIndex: number; structTypeIndex: number; sig: FuncSig }

const LIB_DIR		= path.join(__dirname, 'lib');
// Globbed, not listed: a hardcoded list fails SILENTLY when a new lib file is forgotten -- the declarations simply do not exist, and the first sign is an unrelated "unknown class"/"unresolved identifier".
// `readdirSync` order is filesystem-dependent, so it is sorted for a reproducible build, with `lib.d.ts` pinned first: it declares the pseudo-types and ambient host modules the rest are written against.
// `lib/node/*` is deliberately NOT included -- on-demand modules resolved through the loader (see `ModuleLoader.nodeBuiltin`), not part of this always-linked flat scope.
const LIB_FILES		= ['lib.d.ts', ...fs.readdirSync(LIB_DIR).filter(f => f.endsWith('.ts') && f !== 'lib.d.ts').sort()];
export const LIB_AST	= LIB_FILES.flatMap(f => TS.parse(fs.readFileSync(path.join(LIB_DIR, f), 'utf8')).body);
const LIB_EXPORTS	= LIB_AST.filter(n => n.type === 'export_decl').map(n =>n.declaration);
// The lib's type aliases alone, where each machine type is declared (`T.machineOf`), for what runs before any compile scope exists.
const LIB_TYPES		= new T.Scope(T.TS_SEMANTICS);
for (const n of LIB_AST)
	if (n.type === 'type_alias_decl')
		LIB_TYPES.addType(n.name, n.value, n.typeParams);
// A `declare global` block's declarations are the lib's own globals, as the checker binds them.
const LIB_STMTS		= [...LIB_EXPORTS, ...LIB_AST.flatMap(n => n.type === 'module_decl' && n.name === 'global' ? n.body.map(d => d.type === 'var_decl' ? { ...d, ambient: true } : d) : [n])];
const LIB_DECLS		= [
	...LIB_STMTS.filter(n => n.type === 'function_decl' || n.type === 'class_decl'),
	...LIB_STMTS.filter(n => n.type === 'var_decl').flatMap(d => d.declarations.map(decl => ({type: 'var_decl', ambient: d.ambient, kind: d.kind, ...decl} as const)))
];

// An ambient `declare class`/`declare function` stub (`.ambient === true`, no body) exists only for the checker -- codegen must prefer a real same-named implementation.
// `LIB_DECLS`'s own ordering can't guarantee that (an exported real decl sits earlier than a non-exported ambient one), so plain last-wins would pick the ambient stub.
const LIB_DECL_MAP = new Map<string, typeof LIB_DECLS[number]>();
for (const d of LIB_DECLS) {
	const existing = LIB_DECL_MAP.get(d.name as string);
	if (existing && 'ambient' in d && d.ambient && !('ambient' in existing && existing.ambient))
		continue; // a real decl, once registered, is never displaced by a later ambient stub of the same name
	LIB_DECL_MAP.set(d.name as string, d);
}

// A lib file declares a real host (wasm) import with ordinary TS syntax -- `declare module 'name' {...}` plus `import {f} from 'name'` -- instead of a hand-registered one per feature.
// `source` matching an *ambient* `module_decl` (not a filename) discriminates a host import from an ordinary intra-lib one (e.g. regexp.ts's `import { StringParser } from './string'`).
interface HostImport { source: string; name: string; params: Type[]; returnType?: Type }
// The ambient `declare module '...'` blocks are always the LIB's own (`lib.d.ts` is always loaded); only the `import` statements naming one have to be looked for per body.
// `source` matching an *ambient* `module_decl` (not a filename) discriminates a host import from an ordinary intra-lib one (e.g. regexp.ts's `import { StringParser } from './string'`).
// So an on-demand `lib/node/*` module can declare a host import of its own instead of having to register it in a static lib file.
const LIB_AMBIENT_MODULES = new Map(LIB_AST.filter((n): n is Extract<TS.Stmt, { type: 'module_decl' }> => n.type === 'module_decl' && !!n.ambient).map(n => [n.name, n]));

function hostImportsIn(body: TS.Stmt[]): HostImport[] {
	return body.filter((n): n is JS.Import => n.type === 'import' && LIB_AMBIENT_MODULES.has(n.source)).flatMap(imp => (imp.specifiers ?? []).flatMap(s => {
		const decl = LIB_AMBIENT_MODULES.get(imp.source)!.body.find(d => d.type === 'function_decl' && d.name === s.imported);
		return decl?.type === 'function_decl' ? [{ source: imp.source, name: s.local, params: decl.params.map(p => p.typeAnnotation!), returnType: decl.returnType }] : [];
	}));
}

const LIB_HOST_IMPORTS: HostImport[] = hostImportsIn(LIB_AST);

interface MethodDelegate 			{ owner: ClassInfo; method: string }
// Per-operand info for builtin dispatch -- wtype for kind-polymorphic dispatch, owner for identity dispatch.
interface OperandInfo { wtype: W.Type | undefined; owner?: ClassInfo }
// `typeArgs`: the call site's own type arguments, for an inline whose declared types mention the METHOD's own type parameters (`Array._alloc<T>(n): T[]`).
// Class-level defines are baked once per instantiation and cannot carry these -- see `makeAsm`'s `$ret`.
export type Builtin<T = Inline | MethodDelegate | FunctionDecl> = (args: OperandInfo[], ctx: FunctionContext, typeArgs?: Type[]) => T



class ClassInfo extends W.ClassInfo {
	methodDecls		= new Map<string, MethodMember[]>();
	inlineMethods?:	Map<string, Builtin<Inline>>;
	// Where this class was DECLARED: its own module's scope and canonical path, so a method body compiled from
	// another module can resolve the names its own file declares. Absent for a lib class or a synthesized shape.
	declScope?:		Scope;
	// Built for an unnamed object type, so reached only through that type (`ensureAnonObjectShape`), never matched for another.
	anonymous		= false;
	// One instantiation of a generic class, each its own struct: `instanceof` must test them all.
	instantiation	= false;
	// Its constructor needs `this` before every required field has a value (`ctorNeedsEarlyThis`), so the object is
	// built up front: the fields are stored nullable and it takes `ensureCtor`'s `struct.new_default` path.
	earlyThis		= false;
	// Narrows the base's own recursive member, or every walk of the chain would lose the fields above.
	declare superClass?:	ClassInfo;

	constructor(name: string, typeIndex: number, public decl: TS.Class, public thisTsType: Type) {
		super(name, typeIndex);
	}

	// The type `key` accepts, `| undefined` when optional: `decl` first, then the resolved shape. A composite cache key
	// (`Field<Type>`) is never a resolvable name, so `thisTsType` is what named and anonymous shapes both carry.
	fieldDeclaredType(key: string, scope: Scope): Type | undefined {
		const m = this.decl.body.find((m): m is JS.Field<Type> => m.type === 'field' && m.key === key);
		if (m)
			return m.typeAnnotation && T.optional(m.typeAnnotation, hasMod(m, 'optional'));
		const resolved = T.resolveObjectType(this.thisTsType, scope);
		if (resolved) {
			const p = resolved.members.find(p => p.type === 'property' && p.key === key);
			if (p?.type === 'property')
				return T.optional(p.typeAnnotation, hasMod(p, 'optional'));
		}
		return undefined;
	}
}



// What a plain `return expr;` means here -- ordinarily coerce `expr` to `ctx.result` and emit a wasm `return` (`plainReturn`).
// A generator/async step function, a constructor or a `reassignsThis` method each redefine it.
// Those redefinitions are the IteratorResult protocol, Promise resolution, implicit/appended `this`, ... -- set once by `compileGeneratorFunc`, `compileAsyncFunc`, `ensureCtor` or `ensureMethod`.
// Read by `case 'return'`; a `case 'try'` with a `finally` temporarily swaps in the *outer* meaning to reconstruct a real return once `finally` has run.
interface ReturnHandler {
	wtype(ctx: FunctionContext): W.Type | undefined;
	emit(ctx: FunctionContext, argument: Expr|undefined): void;
};
// `calleeDefault`: a default no call site can re-emit (a call, a capture, `this`). Its slot is an optional one and
// `declareParams` applies the default in the callee, which is where JS evaluates it anyway.
interface ResolvedParam { key: BindingTarget; wtype: W.Type; tsType: Type; calleeDefault?: { value: Expr; tsType: Type } }

interface Global extends W.Local {init?: Expr, initInstrs?: wasm.Instr[], mut: boolean, stringData?: { offset: number; length: number }}

class FunctionContext extends W.FunctionContext {
	// Set when this FuncCtx is a nested `function_decl`'s own body that's allowed to call itself by name: a call to `name` resolves to a direct, statically-known `call funcIndex` (reusing the same env).
	// It can't go through a closure struct, since the struct being constructed can't reference itself while it's still being built -- see `emitClosureLiteral`'s `allowSelfCall`.
	selfCall?:			FuncInfo;

	// Populated once by `collectDefinePropertyTargets`: the plain local names (not full scope-aware identity like the checker's range widening, an accepted simplification)
	// ever used as `Object.defineProperty`'s own target later in this same body, so that declarator can allocate its class's own extension subclass instead of the plain one.

	// This function's own top-level statement list (not descending into a nested closure's own body -- the same boundary `ownBoundNames`/`collectFreeVars` use), consulted only by `ensureForwardHolder`.
	// It finds a sibling `const`/`let` declared LATER in this same body that an EARLIER closure literal needs to forward-reference; set once after construction.
	ownBody?:			Stmt[];
	readonly vars		= new Set<string>();
	// Declarators whose initializers are compiling right now, innermost last -- see `ensureForwardHolder`.
	initializing?:		JS.Var<Type>[];

	// A one-shot hint for the *very next* expression about to be compiled: the enclosing declaration's own real TS type (a var_decl's `Expr[]`, or one array literal element's own `Expr`).
	// Set by `case 'var_decl'` and `case 'array'`'s per-element loop; always consumed-then-cleared by a `call` (`emitExpr`'s own entry), so it never leaks into an unrelated sub-expression (a call's own arguments, a nested literal).
	// Deliberately narrow -- not a general "expected type" channel threaded through every expression.
	contextualReturn?:	Type;
	// The contextual type of the CALL being compiled, for a generic method's instantiation (`ensureMethod`); every call sets it afresh, so a nested one never reads its parent's.
	callContext?:		Type;


	constructor(name: string, public scope: Scope, public onReturn: ReturnHandler, public owner?: ClassInfo, public homeModule = '.') {
		super(name);

	}

	declareValue(name: string, wtype: W.Type, tsType: Type, pinned = false): W.Local {
		this.scope.addValue(name, tsType);
		return this.declareLocal(name, wtype, pinned);
	}

	// No real wasm local -- storage is a closureEnv struct field.
	declareCaptured(name: string, tsType: Type) {
		this.scope.addValue(name, tsType);
	}


	// `tsType` is the caller's already-resolved effective `Type` (annotation, or inferred from a default) via
	// `paramType`; re-deriving it here would also need a `checker` this top-level class doesn't have.
	declareParams(params: ResolvedParam[]): JS.Stmt<Type>[] {
		const pending: JS.Stmt<Type>[] = [];
		params.forEach((p, i) => {
			if (typeof p.key === 'string' && !p.calleeDefault) {
				this.declareValue(p.key, p.wtype, p.tsType);
			} else {
				const tmpName = `#param$${i}`;
				this.declareValue(tmpName, p.wtype, p.tsType);
				const incoming: Expr = Identifier(tmpName);
				pending.push(JS.VarDecl('let', JS.Var<Type>(p.key,
					p.calleeDefault ? Binary<Expr, '??'>('??', incoming, p.calleeDefault.value) : incoming, p.calleeDefault?.tsType)));
			}
		});
		return pending;
	}

	narrowedTypeOf(e: Expr): Type {
		const unwrapped = unwrapAs(e);
		const t = this.narrowedValueTypeOf(unwrapped);
		// A value typed `never` (an exhausted switch's `default:`, tocode.ts `(type as any).type`) has no type but the asserted one.
		return unwrapped !== e && !T.unionMembers(t, this.scope).length ? this.typeAt(e) : t;
	}

	// Where `e`'s physical type is decided. A call has no slot: its value is what the instance built, and a generic
	// instance is chosen with the NARROWED arguments (`box(v)` inside `if (v === null)` builds `{value: null}`).
	// Nor does an array literal: its storage is its elements' as narrowed (`p.t ? [p.t] : []` is a `number[]`) --
	// which is what the checker gave the node, so those read their stamp; everything else reads its slot.
	physicalTypeOf(e: Expr): Type {
		return openReads.has(e) ? OPEN_SLOT : e.type === 'call' || e.type === 'new' || e.type === 'array' ? this.typeAt(e) : checkerTypeOf(e, this.scope);
	}

	narrowedValueTypeOf(unwrapped: Expr): Type {
		const base = this.physicalTypeOf(unwrapped);
		// An open slot's value is whatever storage reached it: no narrowing of its type says which.
		if (base === OPEN_SLOT)
			return base;
		// `any` counts as well as a real union: a field read off a NARROWED union receiver (`w.body` inside `if (w.kind === 'w')`)
		// has no baseline, since `ctx.scope` still sees the whole union, on which `body` doesn't exist.
		if (!(T.isAny(base) || T.resolve(this.scope, base).type === 'union'))
			return base;
		const narrowed = this.stampedTypeOf(unwrapped);
		return !narrowed || T.isAny(narrowed) ? base : backToDeclaredMembers(narrowed, base, this.scope);
	}

	// The type the checker gave `e` where it stands, narrowed; a method's polymorphic `this` read as the class this body is compiled for.
	stampedTypeOf(e: Expr): Type | undefined {
		const t = checkedTypeOf(e);
		return t && this.owner?.thisTsType ? T.substituteThisType(t, this.owner.thisTsType) : t;
	}

	// `e`'s checked type, widened as `checkerTypeOf` widens; a node synthesized after the check pass has no stamp and is typed where it stands.
	typeAt(e: Expr, widen = true): Type {
		const t = this.stampedTypeOf(e);
		return t ? (widen ? T.widenLiterals(t) : t) : checkerTypeOf(e, this.scope, widen);
	}

	// A namespace import naming its members, not a value of its own: there is no object to build for it.
	isNamespaceQualifier(e: Expr): e is Expr & { type: 'identifier' } {
		return e.type === 'identifier' && !this.lookup(e.name) && !!this.scope.namespace(e.name);
	}
	isNamespaceValue(e: Expr & { type: 'member' }): boolean {
		return this.isNamespaceQualifier(e.object) && this.scope.namespace(e.object.name)?.decl(e.property)?.type === 'var_decl';
	}

	withCallContext<R>(callContext: Type | undefined, fn: () => R): R {
		const saved = this.callContext;
		this.callContext = callContext;
		try {
			return fn();
		} finally {
			this.callContext = saved;
		}
	}

	withContext<R>(contextual: Type | undefined, fn: () => R): R {
		const saved = this.contextualReturn;
		this.contextualReturn = contextual;
		try {
			return fn();
		} finally {
			this.contextualReturn = saved;
		}
	}

	// A type guard call (`x is P`, not `asserts`) its argument's type settles: `true` when every value of that type is a `P`,
	// `false` when none can be, `undefined` when only the value can tell. Decided by the checker's own comparability.
	staticGuard(test: Expr): boolean | undefined {
		if (test.type === 'unary' && test.operator === '!') {
			const inner = this.staticGuard(test.operand);
			return inner === undefined ? undefined : !inner;
		}
		if (test.type !== 'call')
			return undefined;
		const scope	= this.scope;
		const fn	= T.resolveOwn(checkerTypeOf(test.callee, scope), scope);
		if (fn.type !== 'function' || fn.typeParams?.length)
			return undefined;
		const pred = fn.returnType;
		if (pred?.type !== 'predicate' || pred.asserts || !pred.assertedType)
			return undefined;
		const arg = test.arguments[fn.params.findIndex(p => p.key === pred.paramName)];
		if (!arg || arg.type === 'spread')
			return undefined;
		const a = this.narrowedTypeOf(arg), p = pred.assertedType;
		if (T.isAny(a))
			return undefined;
		if (T.isAssignable(a, p, scope, scope, true))
			return true;
		return T.unionMembers(a, scope).some(m => T.isAssignable(m, p, scope, scope, true) || T.isAssignable(p, m, scope, scope, true)) ? undefined : false;
	}


	// A resumable step's loop (`emitResumableBody`): `case 'switch'`'s dispatch + nested blocks (innermost = segment 0), over
	// resume states. A resumed call has no structured nesting, so 'goto'/'branch' write the new state and `br` back to the loop,
	// which `loadState` re-reads. 'suspend'/'complete' are the caller's (both `return`); `onSegmentStart` runs each segment's first.
	emitResumableDispatch(
		machine:		StateMachine,
		loadState:		() => void,
		setFrame:		(state: number) => void,
		emitTest: 		(test: Expr) => void,
		onSegmentStart: (segmentId: number) => void,
		onSuspend:		(next: SuspendBoundary, resumeId: number, loopMark: number) => void,
		onComplete:		() => void,
	): void {
		const gotoLoop = (depth: number) => this.emit(I.br(this.depth - depth));
		// The whole dispatch is the loop's body, and each iteration re-reads the state first.
		const outer		= this.swapOut();
		loadState();
		const loopMark = this.enterLabel();

		this.enterLabel(machine.segments.length);
		this.emit(I.br_table(Array.from({ length: machine.segments.length }, (_, i) => i), 0));

		machine.segments.forEach((seg, k) => {
			this.exitLabel();
			this.emit(I.block(undefined, this.swapOut()));
			onSegmentStart(k);
			const next = seg.next;

			switch (next.type) {
				case 'goto':
					setFrame(next.target);
					gotoLoop(loopMark);
					break;

				case 'branch': {
					emitTest(next.test);
					const old = this.swapOut();
					this.enterLabel();
					setFrame(next.then);
					gotoLoop(loopMark);
					const thenInstrs = this.swapOut();
					setFrame(next.else);
					gotoLoop(loopMark);
					this.exitLabel();
					this.emit(I.if(undefined, thenInstrs, this.swapOut(old)));
					break;
				}
				case 'suspend':
					onSuspend(next, next.resumeId, loopMark);
					break;

				case 'complete':
					setFrame(machine.completeId);
					onComplete();
					break;
			}
		});

		this.exitLabel();	// the outer loop's own label
		this.emit(I.loop(undefined, this.swapOut(outer)));
	}
}


// ===================================================================
// Inline `__asm` -- the TypeScript spelling
// ===================================================================
// The island itself is in `../wasm/codegen` and is language-free. What is here is only what TypeScript alone can
// answer: the SPELLING (recognising the call, and reading the WAT text and the declared types off it) and
// the types -- what a declared type lowers to, and what a `TYPEINDEX` operand names against the signature
// its own call settled on.

function isAsm(e?: Expr): e is JS.Call<Type> {
	return e?.type === 'call' && e.callee.type === 'identifier' && e.callee.name === '__asm';
}

function isAsmMethod(m: JS.Method<Type>): JS.Call<Type> | undefined {
	if (m.body?.[0]?.type === 'return') {
		const outer = m.body[0].argument;
		if (outer?.type === 'call' && isAsm(outer.callee)) {
			const paramNames = m.params.map(p => typeof p.key === 'string' ? p.key : undefined);
			const argNames = outer.arguments.map(a => a.type === 'identifier' ? a.name : undefined);
			if (paramNames.length === argNames.length && paramNames.every((p, i) => p !== undefined && p === argNames[i]))
				return outer.callee;
		}
	}
}

// A structural `{[k: string]: V}` type has no nominal class; it is the lib's `DynamicObject<V>`, whose `get`/`set` (`case 'index'`) plus `delete`/`has`/`keys` cover it.
// Purely a shared-implementation choice, invisible to the source: real `{}`/bracket/`delete`/`in`/`for...in` stays genuine syntax.
const isDynamicObject = (cls: ClassInfo) => cls.decl.name === 'DynamicObject' && cls.homeModule === undefined;

export function indexSignatureValueType(w: Type): Type | undefined {
	if (w.type !== 'object' || w.members.length !== 1)
		return undefined;
	const m = w.members[0];
	return m.type === 'index' && m.paramType.type === 'ref' && m.paramType.name === 'string' ? m.typeAnnotation : undefined;
}

interface AsmCodegen {
	// The general declared-type mapper, for a declared type `asmDeclaredType` has no case for (an alias, a
	// class). Absent at the module-level builtin registry, which is built before any compile scope exists.
	typeOf?: (t: Type) => W.Type | undefined;
	// The wasm type index a representation was registered at. A `TYPEINDEX` operand needs one, and only a
	// caller with the type section in hand can answer.
	typeIndexOf?: (w: W.Type) => number | undefined;
}

// What a declared type in an asm signature STORES -- not `typeOf`, since a signature may name a packed element
// kind (`i8`/`u8`) that `T.resolve` leaves unresolved and `builtinTypes` doesn't carry, so it comes from the
// neutral `WT.pseudoValueType`; `resolve` answers the rest.
function asmDeclaredType(t: Type, resolve?: (t: Type) => W.Type | undefined): W.Type | undefined {
	if (t.type === 'ref') {
		if (t.name === 'RawArray')
			return W.ARRAY[rawElemKind(t.typeArgs?.[0], x => asmDeclaredType(x, resolve))];
		if (!t.typeArgs) {
			const builtin = builtinTypes.get(t.name)?.wtype;
			if (builtin)
				return builtin;
		}
		const m = T.machineOf(t, LIB_TYPES);
		if (m)
			return machineSlot(m);
	}
	if (t.type === 'array') {
		const m = T.machineOf(t.element, LIB_TYPES);
		if (m)
			return W.ARRAY[W.notUnsigned(m)];
		const arr = W.notUnsigned(W.scalarKind(asmDeclaredType(t.element, resolve)));
		return arr ? { arr } : W.ARRAY.ref;
	}
	return resolve?.(t);
}


// A `const f = __asm<[...], R>('...')` declaration or a bare `__asm<...>('...')(args)` call -- the two
// spellings `isAsm`/`isAsmMethod` recognise. Everything about the BODY is `../wasm/codegen`'s; read here is the
// island's TypeScript spelling, and answered here are its types.
function makeAsm(call: JS.Call<Type>, codegen: AsmCodegen, defines?: Record<string, string|number>, typeParams?: string[]): Builtin<Inline> {
	let		asm		= (call.arguments[0] as Literal<string | JS.TemplatePart<Expr>[]>).value;

	if (typeof asm !== 'string') {
		if (Array.isArray(asm)) {
			if (asm.some(p => p.exp !== undefined))
				throw 'inline asm: template-literal interpolation is not supported, only a plain static string';
			asm = asm.map(p => p.str).join('');
		} else {
			throw 'inline asm: expected a string literal';
		}
	}

	const [paramsTuple, resultType] = call.typeArgs ?? [];
	const declared = paramsTuple?.type === 'tuple' ? paramsTuple.elements.map(te => {
		const el = T.tupleElementType(te);
		if (!el)
			throw `unsupported inline-asm param type '${T.tocode.tupleElement(te)}'`;
		return el;
	}) : [];
	const isOpenParam = (t: Type | undefined): boolean => !t ? false
		: t.type === 'ref' ? !!typeParams?.includes(t.name)
		: t.type === 'array' ? isOpenParam(t.element)
		: false;
	// An OPEN type parameter, unsubstituted because this call site gave no explicit type arguments: `T[]` still
	// falls back to `arr:ref` in `asmDeclaredType`, but a bare `T` had none, so `Array._fill(a, i, x, n)` threw
	// instead of letting the per-call signature take the argument's real physical type (`isOpenParam`, in `sigFor` below).
	const resolveType = (t: Type): W.Type | undefined => isOpenParam(t) ? W.REF_ANY_NULLABLE : asmDeclaredType(t, codegen.typeOf);

	// The signature ONE call settled on, and the `TYPEINDEX` resolver that must agree with it: a `T[]` operand is looked up
	// among the types this call's own params and result took, since an open `T` re-resolved alone falls back to `arr:ref`
	// where the arguments made it `arr:f64` -- and an `array.copy` whose operand type disagrees with its operands is invalid wasm.
	const settle = (params: W.Type[], result: W.Type) => {
		const known = new Map<string, W.Type>(declared.map((t, i) => [T.typeKey(t), params[i]]));
		if (resultType)
			known.set(T.typeKey(resultType), result);
		const typeIndex = (text: string): number | undefined => {
			const m = /^\s*([A-Za-z_$][A-Za-z0-9_$]*)\s*((?:\[\s*\]\s*)*)$/.exec(text);
			if (!m)
				throw `inline asm '${asm}': TYPEINDEX("${text}") is not a name-and-'[]' type expression`;
			let t: Type = TS.RefType(m[1]);
			for (let i = m[2].split('[').length - 1; i > 0; i--)
				t = TS.ArrayType(t);
			const wt = known.get(T.typeKey(t)) ?? resolveType(t);
			const index = wt && codegen.typeIndexOf?.(wt);
			if (index === undefined)
				throw `inline asm '${asm}': TYPEINDEX("${text}") has no wasm type index`;
			return index;
		};
		return { sig: { params, result }, typeIndex };
	};

	// Declared types are substituted with the call's type arguments first, so `__asm<[i32], T[]>` resolves `T[]` to a real element
	// kind. With none (`Array._copy(dst, 0, src, 0, n)`) an open parameter takes its ARGUMENT's physical type -- but only there: a
	// closed position (`start: i32`) still needs its declared type, or a coercion the caller's emit would have inserted disappears.
	const sigFor = (typeArgs?: readonly Type[], argWtypes: readonly (W.Type | undefined)[] = []) => {
		const subs	= typeParams && typeArgs?.length ? new Map(typeParams.map((n, i) => [n, typeArgs[i]])) : undefined;
		const sub	= (t: Type) => subs ? T.substituteType(t, subs) : t;
		const params = declared.map((t, i) => {
			const wt = !subs && isOpenParam(t) && argWtypes[i] || resolveType(sub(t));
			if (!wt)
				throw `unsupported inline-asm param type '${T.tocode.type(t)}'`;
			return wt;
		});
		const result = resultType ? resolveType(sub(resultType)) : 'void';
		if (!result)
			throw `unsupported inline-asm result type '${T.tocode.type(resultType)}'`;
		return settle(params, result);
	};

	// The island, prepared once. A `$T`-switched body needs no signature at all -- the numeric type its arguments
	// agree on IS its signature -- so `PreparedAsm` distinguishes it rather than taking an optional one.
	const prepared = makeAsm0(asm, defines, declared.length, !!typeParams?.length || asm.includes(WAT.TYPEINDEX_MACRO));
	if (prepared.switched)
		return (args, ctx) => prepared.render(args.map(a => a.wtype), ctx);
	if (typeParams?.length) {
		return (args, ctx, typeArgs) => {
			const { sig, typeIndex } = sigFor(typeArgs, args.map(a => a.wtype));
			return prepared.render(args.map(a => a.wtype), ctx, sig, typeIndex);
		};
	}
	// Settled at the first call, not here: builtins are made for every island up front, and one no call reaches must
	// neither throw nor build types.
	let fixed: ReturnType<typeof settle> | undefined;
	return (args, ctx) => {
		fixed ??= sigFor();
		return prepared.render(args.map(a => a.wtype), ctx, fixed.sig, fixed.typeIndex);
	};
}

// `Uint8Array`/`Int32Array`/`Uint32Array` are real generic instantiations of `TypedArray<T>`
// (`lib/typedarray.ts`, reached through `ensureClass`'s alias resolution -- see its own comment), a struct
// wrapping a real GC byte-array `ArrayBuffer`, so they skip `types.array`'s own monomorphization entirely.
//
// `class` names which real lib class backs a primitive-level type, resolved lazily through `ensureClass`
// (`builtinTypeOwner`) for all of them alike; `Boolean` simply has none (no decl exists at all).
// Maps, not objects, here and below: indexed by names from source, where `constructor`/`toString` must not find `Object.prototype`'s.
const builtinTypes = new Map<string, { wtype: W.Type; class?: string }>([
	['void',	{ wtype: 'void' }],
	// No `class`: `any` has no single owner to dispatch a method call against (`ensureAnyDispatch` handles that
	// dynamically). NULLABLE: an `any` can hold `undefined` (a missing rest arg, an unmatched regex group), which is `ref.null`.
	['any',		{ wtype: W.REF_ANY_NULLABLE }],
	// `unknown` has no dedicated physical representation of its own -- same boxed storage as `any` (the
	// checker's own `T.isAny` already treats the two alike), just without `any`'s implicit-assignability
	// laxness on the *checking* side, which doesn't affect codegen at all.
	['unknown',	{ wtype: W.REF_ANY_NULLABLE }],
	// `object` is any non-primitive value and never null or undefined -- the same boxed storage as `any`, not nullable.
	// Without it a type parameter bounded by `object` (`<N extends object>(n: N) => ...`, erased to its bound) had no representation.
	['object',	{ wtype: W.REF_ANY }],
	['boolean',	{ wtype: 'i32', 			class: 'Boolean' }],
	['Boolean',	{ wtype: 'i32', 			class: 'Boolean' }],
	['number',	{ wtype: 'f64', 			class: 'Number' }],
	['Number',	{ wtype: 'f64', 			class: 'Number' }],
	['string',	{ wtype: W.ARRAY.i16,		class: 'String' }],
	['String',	{ wtype: W.ARRAY.i16,		class: 'String' }],
	['bigint',	{ wtype: W.ARRAY.i32,		class: 'BigInt' }],
	['symbol',	{ wtype: { ref: 'Symbol' },	class: 'Symbol' }],
]);

const UNARY_OP_NAMES = {
	'-':	'neg',
	'~':	'not',
	'++':	'inc',
	'--':	'dec',
} as const;
const BIG_ARITHMETIC = new Set(['add', 'sub', 'mul', 'neg']);
const isNativeBigMethod = (m: string): m is 'add' | 'sub' | 'mul' | 'neg' | 'eq' | 'ne' | 'lt' | 'gt' | 'le' | 'ge' =>
	BIG_ARITHMETIC.has(m) || m === 'eq' || m === 'ne' || m === 'lt' || m === 'gt' || m === 'le' || m === 'ge';
const BINARY_OP_NAMES = {
	'+':	'add',
	'-':	'sub',
	'*':	'mul',
	'/':	'div',
	'%':	'mod',
	'**':	'pow',
	'&':	'and',
	'|':	'or',
	'^':	'xor',
	'<<':	'shl',
	'>>':	'shr_s',
	'>>>':	'shr_u',
	'==':	'eq',
	'===':	'eq',
	'!=':	'ne',
	'!==':	'ne',
	'<':	'lt',
	'>':	'gt',
	'<=':	'le',
	'>=':	'ge',
} as const;

// Every entry is a real callable (a plain lib function hands back its own `FunctionDecl`, see `emitCall`).
// `Math.abs`/`Array.alloc`/etc aren't here -- registered into each owner's own `inlineMethods` instead (`builtinOwner`).
const builtins = new Map<string, Builtin>([
	...LIB_DECLS.filter(d => d.type === 'function_decl').filter(d => d.body).map(d => [d.name, () => d] as const),
	...LIB_DECLS.filter(d => d.type === 'var_decl').flatMap(d => {
		if (isAsm(d.init)) {
			const builtin = makeAsm(d.init, {}, {});
			return builtin ? [[d.name as string, builtin] as const] : [];
		}
		return [];
	}),
]);

interface AssignTarget { wtype: W.Type; old?: number; write(tee: boolean): void }



// An overload set's implementation with an inferred return returns its signatures' type: a shape of its own would depend on compile order.
function overloadedReturn(fn: TS.CallSig, checked: Type | undefined): Type | undefined {
	if (!fn.inferredReturn || checked?.type !== 'object')
		return undefined;
	const returns = checked.members.flatMap(m => m.type === 'call' ? [m.returnType ?? T.VOID] : []);
	return returns.length > 1 && returns.length === checked.members.length ? T.combineTypes(returns) : undefined;
}

// A top-level `const f = (...) => ...` is never reassigned, so it is a `function_decl` (`functionDeclByName`); `promotedConsts` keeps `__toplevel` from also building it.
// Not when the const is annotated: its callers see the annotation (optional parameters, overloads), not the arrow.
function arrowOrFunctionToDecl(name: string, e: JS.Arrow<Type> | JS.FunctionExpr<Type>): FunctionDecl {
	return {
		type: 'function_decl', name,
		params: e.params, rest: e.rest, typeParams: e.typeParams, returnType: e.returnType,
		body: Array.isArray(e.body) ? e.body : e.body !== undefined ? [JS.Return(e.body)] : [],
	};
}

// The type a short-circuiting operator (`&&`/`||`/`??`) gives both its arms: the caller's, when both it and the
// self-inferred one are object refs -- only then does building at it rather than converting to it matter (invariance).
function wantedShape(want: W.Type | undefined, self: W.Type): W.Type {
	return W.isRef(want) && W.isRef(self) ? want : self;
}

// A discriminant: a field declared as literals must share one of `values`; either side naming no literals admits anything.
function admitsLiterals(declared: Type | undefined, values: readonly unknown[] | undefined): boolean {
	const declaredVals = values && T.literalValues(declared ?? T.ANY);
	return !values || !declaredVals || declaredVals.some(v => values.includes(v));
}
const writtenLiteral = (e: Expr) => e.type === 'literal' ? [e.value] : undefined;

interface LocalField { index: number; wtype: W.Type; tsType: Type }

// ===================================================================
//  AST queries -- names, free variables, and expression shape
// ===================================================================
// Nothing here knows about wasm: every function answers a question about the TypeScript AST.
// `collectCapturedMutables` is the substantive one -- which of a body's bindings a nested closure both captures and assigns, i.e. the locals that must become shared heap holders.

// `as` is a pure pass-through in codegen (`case 'as'` just compiles `e.expression`), but `checkerTypeOf` still honors the
// asserted type -- any codegen-facing type/owner lookup must unwrap it first or it sees a fictional type, losing method/owner dispatch.
function unwrapAs(e: Expr): Expr {
	while (e.type === 'as')
		e = e.expression;
	return e;
}

// For error messages only.
function describeBinding(t: BindingTarget): string {
	return typeof t === 'string' ? t : t.type === 'array_pattern' ? '[...]' : '{...}';
}

// ===================================================================
//  Closures -- free-variable analysis
// ===================================================================

function paramNames(params: JS.Param<Type>[], rest?: JS.Rest<Type>): string[] {
	const names = params.flatMap(p => T.bindingNames(p.key));
	return rest ? [...names, ...T.bindingNames(rest.key)] : names;
}

// Every name body binds directly (own params + var_decls), not descending into nested arrow/function bodies.
function ownBoundNames(names: string[], body: Stmt[] | Expr, selfName?: string): Set<string> {
	const bound = new Set(names);
	if (selfName)
		bound.add(selfName);
	// A `for`'s own `init` (e.g. `for (let i = ...)`) reaches this same `var_decl` case too -- walker.ts
	// routes it through the real statement walk, not just a bare declarator walk, so no separate case is
	// needed here to keep a closure's own loop variable from being mistaken for a free (captured) one.
	walkerB(
		(s, process) => {
			// A nested `function_decl` binds its own name in the enclosing scope (like a `var_decl`
			// would), but its body is a separate closure boundary -- its own params/locals/further-nested
			// declarations must not leak into `bound` here, same reasoning as the `arrow`/`function` stop below.
			if (s.type === 'function_decl') {
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
		(e, process) => (e.type === 'arrow' || e.type === 'function' || e.type === 'object') ? false : process(e)
	).body(body);
	return bound;
}

// Recursively collects free variables into `free`. A nested closure's bound names merge into `bound`
// before recursing, so a level-2 capture of a level-0 variable transitively appears in level-1's set.
function collectFreeVars(bound: Set<string>, body: Stmt[] | Expr, free: Set<string>) {
	walkerB(
		(s, process) => {
			// Mirrors the `arrow`/`function` expression handling below, but for a nested function
			// *declaration* statement -- its own name is already bound (see `ownBoundNames`), so this only
			// needs to stop descent and collect its body's free vars under its own (merged) bound set.
			if (s.type === 'function_decl') {
				collectClosureFreeVars(bound, s, s.name, free);
				return false;
			}
			return process(s);
		},
		(e, process) => {
			if (e.type === 'identifier') {
				if (!bound.has(e.name))
					free.add(e.name);
				return false;
			}
			if (e.type === 'this') {
				if (!bound.has('this'))
					free.add('this');
				return false;
			}
			if (e.type === 'arrow' || e.type === 'function') {
				collectClosureFreeVars(bound, e, e.type === 'function' ? e.name : undefined, free);
				return false;
			}
			if (e.type === 'object') {
				for (const p of e.properties) {
					if (p.type !== 'spread' && typeof p.key === 'object')
						collectFreeVars(bound, p.key.computed, free);
					if (p.type === 'spread') {
						collectFreeVars(bound, p.operand, free);
					} else if (p.type !== 'field') {
						// A method's `this` is the literal's, not the enclosing closure's.
						const own = new Set<string>();
						collectClosureFreeVars(bound, p, undefined, own);
						own.delete('this');
						own.forEach(n => free.add(n));
					} else if (p.value) {
						collectFreeVars(bound, p.value, free);
					}
				}
				return false;
			}
			return process(e);
		}
	).body(body);
}

const usesThis = (fn: { body?: Stmt[] }) => walkerB(undefined, (x, process) => x.type === 'this' || process(x)).statements(fn.body ?? []);

// `this` is a real object only once every required field has a value (`ensureCtor`'s `materializeThis`) -- until then the
// constructor holds them in locals and a direct `this.f` is served from `f`'s own local. What needs the OBJECT is a nested
// function mentioning `this` (it captures it and runs later), a method or accessor called on it, or `this` used as a value.
// A data field is deliberately not one: reading one not yet collected stays the error it is today (TS2565 rejects the source).
// Mirrors `emitCtorStatements`' own order: parameter properties and field initializers, then the body in sequence, a top-level
// `this.f = v` being the one write that does not need `this` to exist yet.
function ctorNeedsEarlyThis(decl: TS.Class): boolean {
	const mentionsThis	= (x: Expr) => walkerB(undefined, (y, process) => y.type === 'this' || process(y)).expression(x);
	const fields		= decl.body.filter((m): m is JS.Field<Type> => m.type === 'field' && !m.modifiers?.includes('static'));
	const dataFields	= new Set(fields.flatMap(f => typeof f.key !== 'object' ? [String(f.key)] : []));
	const check			= () => walkerB(undefined, (x, process) =>
			x.type === 'arrow' || x.type === 'function'		? mentionsThis(x)
		:	x.type === 'member' && x.object.type === 'this'	? !(typeof x.property === 'string' && dataFields.has(x.property))
		:	x.type === 'this' || process(x));
	if (fields.some(f => f.value && check().expression(f.value)))
		return true;
	const ctor = decl.body.find((m): m is MethodMember => m.type === 'method' && m.key === 'constructor' && !!m.body);
	if (!ctor)
		return false;
	const remaining = new Set(fields.filter(f => !f.value && typeof f.key !== 'object' && !f.modifiers?.includes('optional')).map(f => String(f.key)));
	for (const p of ctor.params) {
		if (T.isParamProperty(p) && typeof p.key === 'string') {
			remaining.delete(p.key);
			dataFields.add(p.key);
		}
	}
	for (const st of ctor.body!) {
		if (!remaining.size)
			return false;
		// Built in the narrowed branch, so the field name and value carry their types out with them.
		const write = st.type === 'expression' && st.expression.type === 'assign' && !st.expression.operator
			&& st.expression.target.type === 'member' && st.expression.target.object.type === 'this'
			&& typeof st.expression.target.property === 'string'
			? { field: st.expression.target.property, value: st.expression.value }
			: undefined;
		if (!write) {
			if (check().statement(st))
				return true;
		} else if (check().expression(write.value)) {
			return true;
		} else {
			remaining.delete(write.field);
		}
	}
	return false;
}

// Whether a nested function's body names it other than as the callee of a direct self-call: a value use, or any mention
// inside a closure within it (a capture). Such a body needs its own name bound (`emitClosureLiteral`).
function namesSelfAsValue(body: Stmt[] | Expr, name: string): boolean {
	let found = false;
	const inClosure = (fn: Parameters<typeof collectClosureFreeVars>[1], self: string | undefined) => {
		const free = new Set<string>();
		collectClosureFreeVars(new Set(), fn, self, free);
		return free.has(name);
	};
	walkerB(
		(st, process) => {
			if (found)
				return false;
			if (st.type === 'function_decl') {
				found = inClosure(st, st.name);
				return false;
			}
			return process(st);
		},
		(e, process) => {
			if (found)
				return false;
			if (e.type === 'identifier') {
				found = e.name === name;
				return false;
			}
			if (e.type === 'arrow' || e.type === 'function') {
				found = inClosure(e, e.type === 'function' ? e.name : undefined);
				return false;
			}
			if (e.type === 'call' && e.callee.type === 'identifier' && e.callee.name === name) {
				found = e.arguments.some(a => namesSelfAsValue(a as Expr, name));
				return false;
			}
			return process(e);
		}
	).body(body);
	return found;
}

// A closure's free variables: its body's and its parameter defaults', since a default runs inside the callee.
function collectClosureFreeVars(outer: Set<string>, fn: { params: JS.Param<Type>[]; rest?: JS.Rest<Type>; body?: Stmt[] | Expr }, selfName: string | undefined, free: Set<string>) {
	const body = fn.body ?? [];
	const bound = new Set([...outer, ...ownBoundNames(paramNames(fn.params, fn.rest), body, selfName)]);
	collectFreeVars(bound, body, free);
	for (const p of fn.params)
		if (p.default)
			collectFreeVars(bound, p.default, free);
}

// Names this body declares that a nested closure captures AND something assigns -- the locals that must
// become shared heap holders rather than plain wasm locals. A closure captures a BINDING in JS, not a
// value: `let n = 1; const f = () => n + 1; n = 4;` must have `f()` see 4, and a write inside the
// closure must be visible outside it (the counter idiom). Copying the value into the env struct gives
// neither. `ensureForwardHolder` already builds exactly the right thing -- and `emitClosureLiteral`
// already captures the HOLDER rather than its contents -- but only ever fired for a name used before its
// own declaration ran, so a local declared before the closure was silently captured by value.
// Deliberately over-approximate: a name assigned anywhere at all (including only inside the closure, or
// only before it is ever captured) is holder-backed, and an outer-scope name reaching the set is harmless
// because the answer is only ever consulted when DECLARING a local of that name here. A needless holder
// costs an allocation and an indirection; a missing one is a wrong answer.
// Not yet applied to a captured+mutated PARAMETER, which has the same problem and no `var_decl` to hang
// the holder off.
function collectCapturedMutables(body: Stmt[]): Set<string> {
	const captured	= new Set<string>();
	const assigned	= new Set<string>();
	// A `for (let i = ...)` binding is PER-ITERATION in JS: every iteration gets a fresh one, so each
	// closure created in the loop captures its own. Copying the value into the env -- what capture already
	// did -- is therefore already right, and one shared holder is actively wrong: every closure would then
	// see the loop's final value. `Promise.all`'s own `promises[i].then(v => { values[i] = v; })` is
	// exactly this, and a shared holder had it writing past the end of `values`.
	// (A body that REASSIGNS the variable after creating the closure still isn't modelled -- that needs a
	// fresh holder per iteration, which is the real general answer.)
	// `var` is the exact opposite and must NOT be listed here: it is function-scoped, so the whole loop
	// shares ONE binding and every closure sees its final value -- the shared holder is the correct answer
	// there, and copying by value gave `for (var i...) fs.push(() => i)` a 0 where JS says 3.
	const perIteration = new Set<string>();
	walkerB(
		(st, process) => {
			// A nested function is a closure boundary: everything free in it is captured from here (or
			// from further out, which is harmless -- an outer name simply isn't one of our locals).
			if (st.type === 'for' && st.init && !Array.isArray(st.init) && st.init.type === 'var_decl' && st.init.kind !== 'var') {
				for (const d of st.init.declarations)
					if (typeof d.name === 'string')
						perIteration.add(d.name);
			}
			if (st.type === 'function_decl') {
				const nested = st.body ?? [];
				collectFreeVars(ownBoundNames(paramNames(st.params, st.rest), nested, st.name), nested, captured);
				walkerB(undefined, (e, p) => { noteAssignExpr(e, assigned); return p(e); }).statements(nested);
				return false;
			}
			return process(st);
		},
		(e, process) => {
			if (e.type === 'arrow' || e.type === 'function') {
				const nested = e.body ?? [];
				collectFreeVars(ownBoundNames(paramNames(e.params, e.rest), nested, e.type === 'function' ? e.name : undefined), nested, captured);
				// ...and assignments INSIDE the closure count too: `() => { n = n + 1; }` is the whole point.
				walkerB(undefined, (x, p) => { noteAssignExpr(x, assigned); return p(x); }).body(nested);
				return false;
			}
			// An object literal's METHOD closes over this scope exactly as an arrow does -- a `defineProperty` accessor
			// (`get() { resolving = true; ... }`) mutates the very locals it closes over, and a copy loses the write.
			if (e.type === 'object')
				for (const m of e.properties)
					if (m.type === 'method' || m.type === 'get' || m.type === 'set') {
						const nested = m.body ?? [];
						collectFreeVars(ownBoundNames(paramNames(m.params, m.rest), nested, undefined), nested, captured);
						walkerB(undefined, (x, p) => { noteAssignExpr(x, assigned); return p(x); }).statements(nested);
					}
			noteAssignExpr(e, assigned);
			return process(e);
		}
	).statements(body);
	return new Set([...captured].filter(n => assigned.has(n) && !perIteration.has(n)));
}

// Every identifier this expression assigns to -- `x = v`, any compound form, and `++`/`--`.
function noteAssignExpr(e: Expr, into: Set<string>) {
	if (e.type === 'assign' && e.target.type === 'identifier')
		into.add(e.target.name);
	else if ((e.type === 'unary' || e.type === 'unary_post') && (e.operator === '++' || e.operator === '--') && e.operand.type === 'identifier')
		into.add(e.operand.name);
}

// `Object.defineProperty(target, key, {value, ...})` -- the one real, general escape hatch for dynamically attaching a
// property to an otherwise fixed-shape value (see `ensureClassExtension`'s own comment for how this compiles). Matched
// structurally (a `call` through `Object.defineProperty` by name), not by any special-cased identifier elsewhere --
// this is the one and only place that shape is recognized.
// A call to one of `Object`'s compiler intrinsics (lib.d.ts's `declare var Object`): compiled by its own emitter, never
// through `Object` as a value, which has no runtime shape to build an owner from.
const OBJECT_INTRINSICS = new Set(['entries', 'keys', 'values', 'defineProperty', 'assign', 'is']);
function objectIntrinsic(e: Expr): string | undefined {
	return e.type === 'call' && e.callee.type === 'member' && e.callee.object.type === 'identifier' && e.callee.object.name === 'Object'
		&& OBJECT_INTRINSICS.has(e.callee.property) ? e.callee.property : undefined;
}
function isDefinePropertyCall(e: Expr): e is JS.Call<Type> & { callee: JS.Member<Type> } {
	return objectIntrinsic(e) === 'defineProperty';
}

// `Object.assign(target, {k: v}, ...)` -- `Object.defineProperty`'s other spelling, attaching several keys at once, and
// recognized the same structural way. Only sources that WRITE THEIR KEYS OUT: what a source holds at run time names no
// slot, and a struct has no key walk to copy one with.
function objectAssignCall(e: Expr): { target: Expr; writes: { key: string; value: Expr }[] } | undefined {
	if (objectIntrinsic(e) !== 'assign' || e.type !== 'call' || !e.arguments[0])
		return undefined;
	const props: (JS.ObjectProperty<Type> | undefined)[] = e.arguments.slice(1).flatMap(s => s.type === 'object' ? [...s.properties] : [undefined]);
	const writes = props.flatMap(p => p?.type === 'field' && typeof p.key !== 'object' && p.value ? [{ key: String(p.key), value: p.value }] : []);
	return writes.length === props.length ? { target: e.arguments[0], writes } : undefined;
}

// Whole-body presence check only, run before a generic function's substituted body compiles: decides conservatively
// (across every one of its own type arguments at once, not which specific one) whether `everExtended` needs poking
// *now*, before any of them could get `ensureClass`'d and their own struct type finalized first (`ensureGenericFunc`'s own comment).
function containsDefineProperty(body: Stmt[]): boolean {
	return walkerB(undefined, (e, process) => isDefinePropertyCall(e) || process(e)).statements(body);
}

// The plain local names (see `FunctionContext.definePropertyTargets`'s own comment on why this is
// name-based, not full scope-aware identity) ever used as
// `Object.defineProperty`'s own target argument anywhere in this function body, together with the
// literal keys ever defineProperty'd onto each -- `'dynamic'` once any one of them isn't a compile-
// time-literal string, since a non-enumerable key set can't be given real, individually-named fields

// `modules`/`namedImports` come from the caller via the same `ModuleLoader` the checking pass used --
// `TStoWasm` has no loader and no async boundary to make one. `namedImports` maps a local name to
// `{module, name}` (the target's declared name, possibly not the alias); `import * as X` needs no entry,
// since the checker binds `X` to the target module's `Scope` (both the declarations and their home module).
// Only top-level functions cross modules so far -- a cross-module class or scalar global still throws.
// `onTopLevelError` reports and skips a failing top-level statement rather than failing the whole module
// (they share one start function): one unrepresentable module-level `const` otherwise takes every other
// declaration in the file down with it. Omitted, it rethrows. `checkedModules` is module-level, not per
// compile: a module record outlives one `TStoWasm` call, and its stamps are first-wins.
const checkedModules = new WeakSet<Module>();


// JS `fn.length`: the parameters before the first defaulted one; a rest parameter and a TS `this` parameter never count.
function jsLength(params: { key: unknown; default?: unknown }[]): number {
	const own = params.filter(p => p.key !== 'this');
	const i = own.findIndex(p => p.default !== undefined);
	return i < 0 ? own.length : i;
}

// A `get`/`set` accessor's `methodDecls`/`inlineMethods`/`funcs` key, mangled apart from a plain same-named
// method so a getter and a setter for one property can coexist as two entries instead of overwriting each other.
function accessorKey(kind: 'get' | 'set', name: string): string {
	return `${kind}:${name}`;
}

// Call signatures alone are a plain closure; with fields beside them, a callable object (`ClassInfo.callable`).
const onlyCalls = (members: readonly TS.TypeMember[]) => members.length > 0 && members.every(m => m.type === 'call');
const isStructLayout = (members: readonly TS.TypeMember[]) => !onlyCalls(members) && members.every(m => m.type === 'property' || m.type === 'method' || m.type === 'call');

// A structural shape's expando identity: its member names. A named shape and its anonymous twin share it, so they get
// the same expando fields and `layoutTwin` can still merge them.
function shapeKey(members: readonly TS.TypeMember[]): string {
	return `#shape#${members.flatMap(m => (m.type === 'property' || m.type === 'method') ? T.memberKey(m.key) ?? [] : []).sort().join(',')}`;
}
function structuralKey(name: string, params: JS.Param<Type>[]): string {
	return `${name}#struct<${params.map(p => p.typeAnnotation ? T.typeKey(p.typeAnnotation) : '_').join(',')}>`;
}


// Keyed as a class instantiation is (`layoutArgKey`): `i32` resolves to `number` but is laid out apart from it.
function genericKey(name: string, typeParams: readonly TS.TypeParam[], map: Map<string, Type>, scope: Scope) {
	return layoutKey(name, typeParams.map(p => map.get(p.name)!), scope);
}

// What each imported module's own flows open (`collectOpenShapes`), by its body: the same walk over the same stamped AST, so a
// later compile in the same process replays it instead of repeating it. `DBG_VERIFYSHAPES=1` walks anyway and checks it matches.
const openedByModule		= new WeakMap<object, { shapes: string[]; slots: Slot[] }>();
// An open slot's type, and this compile's reads of one: `any` physically, while the checker's type still names what it holds.
const OPEN_SLOT: Type	= { type: 'ref', name: 'any' };
// A slot with a declaration of its own: a declarator, a parameter (a parameter property is its field too), or a class field.
type Slot = T.Declarator | JS.Field<Type>;
let openReads: ReadonlySet<Expr> = new Set();
const VERIFY_OPEN_SHAPES	= !!process.env.DBG_VERIFYSHAPES;

// A class's constructor implementations: `ensureCtor` specializes each for its arguments' layouts, as a named function is.
// The stamp, else the one a checker query leaves on a node codegen built.
function callOf(e: CallNode, scope: Scope): CheckedCall | undefined {
	if (!checkedCallOf(e))
		checkerTypeOf(e, scope);
	return checkedCallOf(e);
}

// A generic class instance's members are copies (`substituteClassTypeParam`); a signature's `origin` may name a copy or the template.
const memberTemplate	= new WeakMap<object, unknown>();
const templateOf		= (m: unknown) => (typeof m === 'object' && m && memberTemplate.get(m)) || m;

function namedBody<M>(bodies: M[], checked: CheckedCall | undefined, label: string): M {
	const origin	= templateOf(checked?.sig.origin);
	const body		= bodies.find(d => templateOf(d) === origin);
	if (!body)
		throw `internal: the checker's resolution of '${label}' names none of its bodies`;
	return body;
}

function importedFunction(imports: Map<string, Map<string, { module: string; name: string }>>, decls: Map<string, FunctionDecl>, name: string, home: string) {
	const imported = imports.get(home)?.get(name);
	return imported && decls.has(homeKey(imported.module, imported.name)) ? imported : undefined;
}

const ctorsOf = (cls: TS.Class) => (cls.body as TS.ClassMember[]).filter((m): m is MethodMember => m.type === 'method' && m.key === 'constructor' && !!m.body);

function collectOpenShapes(
	stmtHomeModule: Map<object, string>,
	moduleBodies: Map<string, Module>,
	functionDeclByName: Map<string, FunctionDecl>,
	namedImportsByModule: Map<string, Map<string, {module: string; name: string }>>
) {
	const escaping		= escapingParams();
	const openShapes	= new Set<string>();
	// A SLOT (`Slot`) that holds more than one array storage is opened alone, and so is every read of it.
	const openSlots		= new Set<Slot>();
	const openReads		= new Set<Expr>();
	// The slot each flowing value lands in, where that slot is a declaration of its own.
	const slotOf		= new WeakMap<Expr, Slot>();

	// The class a value of type `t` is an instance of, and the declaration of its field `key`, inherited ones included.
	const classDeclOf = (t: Type, scope: Scope): TS.Class | undefined => {
		const n = T.nonNullable(t, scope);
		const d = n.type === 'ref' ? T.ownScope(n, scope).decl(n.name) ?? LIB_DECL_MAP.get(n.name) : undefined;
		return d?.type === 'class_decl' ? d : undefined;
	};
	const fieldSlot = (cls: TS.Class | undefined, key: string, scope: Scope): Slot | undefined => {
		if (!cls)
			return undefined;
		for (const m of cls.body as TS.ClassMember[]) {
			if (m.type === 'field' && m.key === key)
				return m;
			if (m.type === 'method' && m.key === 'constructor') {
				const p = m.params.find(p => T.isParamProperty(p) && p.key === key);
				if (p)
					return p;
			}
		}
		const base = cls.superClass?.type === 'identifier' ? scope.decl(cls.superClass.name) : undefined;
		return base?.type === 'class_decl' ? fieldSlot(base, key, scope) : undefined;
	};
	const memberSlot = (e: Expr & { type: 'member' }, scope: Scope) => fieldSlot(classDeclOf(checkerTypeOf(e.object, scope), scope), e.property, scope);

	const readsOpen = (e: Expr, scope: Scope): boolean => propagating && readsOpenIn(e, scope);
	const readsOpenIn = (e: Expr, scope: Scope): boolean => {
		const u = unwrapAs(e);
		return u.type === 'identifier' ? (d => !!d && openSlots.has(d))(scope.declarator(u.name))
			: u.type === 'member' ? (f => !!f && openSlots.has(f))(memberSlot(u, scope))
			: u.type === 'conditional' ? readsOpenIn(u.consequent, scope) || readsOpenIn(u.alternate, scope)
			: u.type === 'binary' && (u.operator === '??' || u.operator === '||' || u.operator === '&&') ? readsOpenIn(u.left, scope) || readsOpenIn(u.right, scope)
			: u.type === 'assign' && !u.operator && readsOpenIn(u.value, scope);
	};
	const open = (id: Slot | undefined, slot: Type, scope: Scope) => id ? openSlots.add(id) : openShapes.add(openKey(slot, scope));

	// A declared slot meeting a VALUE: an object/array literal is built AT the slot and has no layout of its own yet, so only what it holds can widen anything -- hence the descent.
	// `erased`: an array ELEMENT slot does not survive to the literal's emit site -- `Array<T>` collapses `T` to `any` -- so the literal builds its own shape, and only then can it widen anything.
	// `id`: the declaration the slot is, when it is one -- only that slot opens, not every slot of its type.
	function noteSlot(slot: Type | undefined, value: Expr, scope: Scope, depth = 4, erased = false, id?: Slot): void {
		if (!slot || depth < 0)
			return;
		// `a = b` is `b`, and `c ? a : b` or `a ?? b` either; a `new` of the slot's own class takes the slot's type arguments, built there as a literal is.
		if (value.type === 'assign' && !value.operator)
			return noteSlot(slot, value.value, scope, depth, erased, id);
		if (value.type === 'conditional') {
			noteSlot(slot, value.consequent, narrow(value.test, scope, true), depth, erased, id);
			return noteSlot(slot, value.alternate, narrow(value.test, scope, false), depth, erased, id);
		}
		if (value.type === 'binary' && (value.operator === '??' || value.operator === '||' || value.operator === '&&')) {
			noteSlot(slot, value.left, scope, depth, erased, id);
			return noteSlot(slot, value.right, value.operator === '??' ? scope : narrow(value.left, scope, value.operator === '&&'), depth, erased, id);
		}
		// A value read from an open slot may be any storage of its type, so an array slot it reaches holds more than one.
		if (readsOpen(value, scope) && T.unionMembers(slot, scope).some(m => arrayPartOf(m, scope)))
			return void open(id, slot, scope);
		const part = T.nonNullable(slot, scope);
		if (value.type === 'new' && value.callee.type === 'identifier' && part.type === 'ref' && (READONLY_ALIAS.get(part.name) ?? part.name) === value.callee.name)
			return;
		const s = resolvedShape(slot, scope);
		if ((value.type === 'object' || value.type === 'array') && s.type === 'union')
			// Built as the member it matches, even as an array element: only what it holds can widen anything.
			return s.types.filter(m => T.isAssignable(checkerTypeOf(value, scope, false, m), m, scope)).forEach(m => noteSlot(m, value, scope, depth, false, id));
		if (value.type === 'object' && s.type === 'object') {
			for (const f of value.properties) {
				if (f.type === 'field' && typeof f.key !== 'object' && f.value)
					noteSlot(T.lookupMember(s, String(f.key), scope), f.value, scope, depth - 1);
				// A SPREAD fills the same fields a written one does, from whatever its operand may be: each key of each member.
				if (f.type === 'spread')
					for (const m of T.unionMembers(checkerTypeOf(unwrapAs(f.operand), scope), scope))
						for (const key of T.collectMembers(m, scope).flatMap(p => p.type === 'property' ? [T.memberKey(p.key)] : []))
							if (key)
								noteTypes(T.lookupMember(s, key, scope), T.lookupMember(m, key, scope), scope, depth - 1);
			}
			// Literal types widened first, or every `const m: M = {...}` differs from `M` by its own `key: "k"` vs `string`.
			if (erased)
				noteTypes(slot, T.widenLiterals(checkerTypeOf(unwrapAs(value), scope)), scope, depth);
			return;
		}
		// An array literal is built as an array whatever its context, and a shape's struct is never one -- where it fits: of the overloads noted for a call, only one takes it.
		if (value.type === 'array' && s.type === 'object' && !T.unionMembers(slot, scope).some(m => arrayPartOf(m, scope))) {
			const built = checkerTypeOf(value, scope, true, slot);
			if (T.isAssignable(built, slot, scope))
				openShapes.add(openKey(slot, scope));
			return noteTypes(slot, built, scope, depth);
		}
		if (value.type === 'array' && s.type === 'array') {
			for (const el of value.elements)
				if (el && el.type !== 'spread')
					noteSlot(s.element, el, scope, depth - 1, true);
			return;
		}
		// Typed in the slot's context, as it is built: an uncontextual `new Map` is `Map<any, any>`, and a literal may fit only in context.
		// A call's type arguments may come from that context (`xs.find(isCtor)` as a `CallSig`), yet it returns what it was given.
		noteTypes(slot, checkerTypeOf(unwrapAs(value), scope, true, slot), scope, depth, id);
		if (unwrapAs(value).type === 'call')
			noteTypes(slot, checkerTypeOf(unwrapAs(value), scope), scope, depth, id);
	}
	// The same question with no expression to descend: a value's TYPE meeting a slot's, member-wise and through elements.
	function noteTypes(slot: Type | undefined, value: Type | undefined, scope: Scope, depth = 4, id?: Slot): void {
		if (!slot || !value || depth < 0)
			return;
		// A nullable slot holds its non-null part's values, and a readonly view is its container, physically.
		const physical	= (x: Type): Type => (n => n.type === 'ref' && READONLY_ALIAS.has(n.name) ? { ...n, name: READONLY_ALIAS.get(n.name)! } : n)(T.nonNullable(x, scope));
		const s			= resolvedShape(physical(slot), scope), v = resolvedShape(physical(value), scope);
		if (T.typeId(s) === T.typeId(v))
			return;
		const se = T.arrayLikeElement(s), ve = T.arrayLikeElement(v);
		if (se && ve) {
			// Element STORAGE is the array's own layout (packed `u8`, `f64`, boxed `any`); an element's own shape is the element's business.
			const storage = (t: Type) => rawElemKind(t, x => wasmTypeOf(x, scope));
			if (storage(se) !== storage(ve) && T.isAssignable(v, s, scope))
				open(id, physical(slot), scope);
			return noteTypes(se, ve, scope, depth - 1);
		}
		// What a method of the value returns is what the slot's method is read as returning. Not a level deeper: the member step that reached it was.
		// A PARAMETER is contravariant: what the slot's signature passes is what the value's own parameter has to hold, so the two
		// swap sides. Without this a function value's parameter never meets the layouts its callers actually send it, and a slot
		// whose argument is a different struct reaches `ensureClosureCoercionWrapper` as an unconvertible pair.
		if (s.type === 'function' && v.type === 'function') {
			s.params.forEach((p, i) => noteTypes(v.params[i]?.typeAnnotation, p.typeAnnotation, scope, depth - 1));
			return noteTypes(s.returnType, v.returnType, scope, depth);
		}
		// A value member meets the slot member it is another instantiation of (`A<number>` in `A<any>`'s place), never every member it happens to fit.
		if (s.type === 'union') {
			for (const vm of T.unionMembers(v, scope))
				s.types.filter(sm => sm.type === 'ref' && vm.type === 'ref' && sm.name === vm.name && T.typeKey(sm) !== T.typeKey(vm)).forEach(sm => noteTypes(sm, vm, scope, depth - 1));
			return;
		}
		// Two instantiations of one generic class are distinct structs when their arguments' layouts differ, as two shapes are.
		const instance = s.type === 'ref' && v.type === 'ref' && s.name === v.name && !!s.typeArgs?.length && T.isClassRef(s, scope);
		if (s.type !== 'object' && !instance)
			return;
		if (s.type === 'object')
			for (const m of s.members) {
				const key = (m.type === 'property' || m.type === 'method') && T.memberKey(m.key);
				if (key)
					noteTypes(T.lookupMember(s, key, scope), T.lookupMember(v, key, scope), scope, depth - 1);
			}
		// An `any` value is the program's own promise about what it holds, kept by the `ref.cast` every read of one already
		// emits -- widening on it would open nearly every shape, since `any` reaches everywhere.
		if (T.isAny(v) || (v.type === 'ref' && v.name === 'unknown'))
			return;
		// `interface LP<T> extends P<T>` resolves to `P<T> & {...}` and is laid out OVER `P`'s struct (`ensureIntersectionShape`),
		// a wasm subtype that needs no conversion: such a value is already what the slot holds.
		// Only an interface's own `extends` part: a CLASS that merely satisfies the slot structurally (`Array` for `Iterable`) is a
		// different struct, which must open the slot as before. An ARRAY-backed one is laid out over nothing -- `typeOf`'s own
		// `arrayPartOf` branch erases it to the array, whose extras are expando slots -- so it opens the slot like any other class.
		const overSlot = !T.isClassRef(physical(value), scope) && !arrayPartOf(v, scope)
			&& T.flattenIntersection(T.resolveMembers(physical(value), scope), scope).some(p => p !== v && !T.isClassRef(p, scope) && T.typeId(resolvedShape(p, scope)) === T.typeId(s));
		// Only a value of a genuinely different LAYOUT widens: two types that share one are already interchangeable.
		if (!overSlot && layoutSketch(s, scope) !== layoutSketch(v, scope) && T.isAssignable(v, s, scope))
			openShapes.add(openKey(physical(slot), scope));
	}
	// A generic construct signature (`new <K, V>(...) => Map<K, V>`) over the type arguments of the instance it built.
	function instantiateConstruct(sig: TS.CallSig, built: Type): TS.CallSig {
		const ret = sig.returnType;
		if (!sig.typeParams?.length || ret?.type !== 'ref' || built.type !== 'ref' || !ret.typeArgs || ret.typeArgs.length !== built.typeArgs?.length)
			return sig;
		const map = new Map(ret.typeArgs.flatMap((a, i) => a.type === 'ref' && sig.typeParams!.some(p => p.name === a.name) ? [[a.name, built.typeArgs![i]] as const] : []));
		if (map.size !== sig.typeParams.length)
			return sig;
		const sub = (p: JS.Param<Type>) => ({ ...p, typeAnnotation: p.typeAnnotation && T.substituteType(p.typeAnnotation, map) });
		return { ...sig, typeParams: undefined, params: sig.params.map(sub), rest: sig.rest && sub(sig.rest) };
	}
	// A named function's or constructor's parameters whose value LEAVES it -- stored, returned, or passed where no per-layout instance is
	// compiled (a closure call) -- so an instance cannot retype them. A least fixpoint: an argument to another named function escapes only if its parameter does.
	function escapingParams(): Map<Callable, Set<string>> {
		const escaping	= new Map<Callable, Set<string>>();
		const classes	= [...[...moduleBodies.values()].flatMap(m => m.body.map(s => s.type === 'export_decl' ? s.declaration : s)), ...LIB_DECL_MAP.values()];
		const ctors		= classes.flatMap(c => c?.type === 'class_decl' ? ctorsOf(c) : []);
		// A parameter property is stored in its field.
		for (const c of ctors)
			escaping.set(c, new Set(c.params.flatMap(p => T.isParamProperty(p) && typeof p.key === 'string' ? [p.key] : [])));
		const decls: Callable[] = [...[...new Set(functionDeclByName.values())].filter(d => d.body), ...ctors];
		const calleeOf	= (callee: Expr, home: string) => callee.type === 'identifier'
			? functionDeclByName.get(homeKey(home, callee.name)) ?? (imp => imp && functionDeclByName.get(homeKey(imp.module, imp.name)))(importedFunction(namedImportsByModule, functionDeclByName, callee.name, home))
			: undefined;
		for (let changed = true; changed; ) {
			changed = false;
			for (const decl of decls) {
				const names	= new Set(decl.params.flatMap(p => typeof p.key === 'string' ? [p.key] : []));
				const found	= escaping.get(decl) ?? new Set<string>();
				const home	= stmtHomeModule.get(decl) ?? '.';
				const inert	= new WeakSet<Expr>();
				walkerB(
					(st, process) => {
						if (st.type === 'if' || st.type === 'while' || st.type === 'do_while' || (st.type === 'for' && st.kind === 'normal' && st.test))
							inert.add(st.test!);
						return process(st);
					},
					(e, process) => {
						if (e.type === 'member' || e.type === 'index') {
							inert.add(e.object);
						} else if (e.type === 'binary' && ['===', '!==', '==', '!='].includes(e.operator)) {
							inert.add(e.left);
							inert.add(e.right);
						} else if (e.type === 'unary' && (e.operator === '!' || e.operator === 'typeof')) {
							inert.add(e.operand);
						} else if (e.type === 'call') {
							const callee = calleeOf(unwrapAs(e.callee), home);
							e.arguments.forEach((a, i) => {
								const p = callee?.params[i];
								if (callee && p && typeof p.key === 'string' && !escaping.get(callee)?.has(p.key))
									inert.add(a);
							});
						} else if (e.type === 'identifier' && names.has(e.name) && !inert.has(e) && !found.has(e.name)) {
							found.add(e.name);
							changed = true;
						}
						return process(e);
					}).statements(decl.body!);
				escaping.set(decl, found);
			}
		}
		return escaping;
	}


	// One walk of every module's flows. `propagating`: a read of an open slot opens the slots it reaches, which crosses modules, so
	// only the first walk (which does not) may replay an imported module's result from an earlier compile.
	let propagating = false;
	function walk() {
		for (const [moduleId, m] of moduleBodies) {
			const modScope = m.scope as Scope;
			if (!modScope)
				continue;
			// An imported module's own flows open the same shapes every time -- the same walk over the same stamped AST -- so what it
			// opened is remembered and replayed. Only the ENTRY is walked afresh: it is the module that differs from call to call.
			const remembered = !propagating && moduleId !== '.' ? openedByModule.get(m.body) : undefined;
			if (remembered && !VERIFY_OPEN_SHAPES) {
				remembered.shapes.forEach(k => openShapes.add(k));
				remembered.slots.forEach(d => openSlots.add(d));
				continue;
			}
			const before = new Set(openShapes), slotsBefore = new Set(openSlots);
			let scope = modScope;
			const within = <R>(inner: Scope | undefined, fn: () => R): R => {
				const saved = scope;
				scope = inner ?? scope;
				const r = fn();
				scope = saved;
				return r;
			};
			// A named function's declared parameter is NOT a slot: the callee is compiled per argument layout.
			// A literal argument is still built AS that parameter's type, so what it holds does meet that type's members.
			const notASlot = new WeakSet<object>();
			walkerB(
				(st, process) => {
					if (st.type === 'var_decl')
						for (const d of st.declarations)
							if (typeof d.name === 'string' && d.init)
								slotOf.set(d.init, d);
					if (st.type === 'class_decl')
						for (const m of st.body as TS.ClassMember[])
							if (m.type === 'field' && m.value)
								slotOf.set(m.value, m);
					return within((st as unknown as { scope?: Scope }).scope, () => process(st));
				},
				(e, process) => {
					if (e.type === 'arrow' || e.type === 'function')
						return within((e as unknown as { scope?: Scope }).scope, () => process(e));
					if (e.type === 'assign') {
						const d = e.target.type === 'identifier' ? scope.declarator(e.target.name) : e.target.type === 'member' ? memberSlot(e.target, scope) : undefined;
						if (d)
							slotOf.set(e.value, d);
					}
					// A class's constructor, as a named function below: an argument lands in its parameter (a parameter property's field too),
					// and one that does not escape is no slot, since the constructor is compiled per argument layout.
					const ctors = e.type === 'new' ? (all => all.length > 1 && !e.arguments.some(a => T.isAny(checkerTypeOf(a, scope))) ? [namedBody(all, callOf(e, scope), T.exprKey(e))] : all)
						((c => c ? ctorsOf(c) : [])(classDeclOf(checkerTypeOf(e, scope), scope))) : [];
					if (e.type === 'new' && ctors.length)
						e.arguments.forEach((a, i) => {
							const p = ctors.length === 1 ? ctors[0].params[i] : undefined;
							if (p && typeof p.key === 'string')
								slotOf.set(a, p);
							if (a.type !== 'object' && a.type !== 'array' && ctors.every(c => (p => !!p && typeof p.key === 'string' && !escaping.get(c)?.has(p.key)
								&& !(p.typeAnnotation && T.resolve(scope, p.typeAnnotation).type === 'function'))(c.params[i])))
								notASlot.add(a);
						});
					if (readsOpen(e, scope))
						openReads.add(e);
					if (e.type === 'call' || e.type === 'new') {
						const callee		= unwrapAs(e.callee);
						const calleeDecl	= callee.type === 'identifier' ? scope.decl(callee.name)
							: callee.type === 'member' && callee.object.type === 'identifier' ? scope.namespace(callee.object.name)?.decl(callee.property) : undefined;
						const imported		= callee.type === 'identifier' && (!calleeDecl || calleeDecl.type === 'import') ? namedImportsByModule.get(moduleId)?.get(callee.name) : undefined;
						const monomorphized	= calleeDecl?.type === 'function_decl' || (!!imported && functionDeclByName.has(homeKey(imported.module, imported.name)));
						if (monomorphized) {
							// ...except at a FUNCTION-typed parameter: `structuralParams` only ever retypes one whose argument is a
							// different STRUCT, so a closure argument gets no instance of its own and has to meet the parameter's
							// declared signature as written -- every layout in that signature is a slot after all.
							const decl	= calleeDecl?.type === 'function_decl' ? calleeDecl : imported && functionDeclByName.get(homeKey(imported.module, imported.name));
							const fnAt	= (i: number) => { const a = decl?.params[i]?.typeAnnotation; return !!a && T.resolve(scope, a).type === 'function'; };
							const escapes = (i: number) => { const k = decl?.params[i]?.key; return typeof k === 'string' && !!escaping.get(decl!)?.has(k); };
							e.arguments.forEach((a, i) => {
								const p = decl?.params[i];
								if (p && typeof p.key === 'string')
									slotOf.set(a, p);
								if (a.type !== 'object' && a.type !== 'array' && !fnAt(i) && !escapes(i))
									notASlot.add(a);
							});
						// The compiled body need not be the chosen signature (an overload's implementation, the widest for an `any` argument), so every candidate's parameter is a slot this value may reach.
						// Over-approximating costs speed; missing a slot miscompiles.
						} else {
							const fn	= T.resolve(scope, checkerTypeOf(unwrapAs(e.callee), scope));
							const sigs	= (fn.type === 'object' ? fn.members.filter(m => m.type === (e.type === 'new' ? 'construct' : 'call')) : [])
								.map(sig => e.type === 'new' ? instantiateConstruct(sig as TS.CallSig, checkerTypeOf(e, scope)) : sig as TS.CallSig);
							for (const sig of sigs.length > 1 ? sigs : []) {
								if (!sig.rest && sig.params.length < e.arguments.length)
									continue;
								e.arguments.forEach((arg, i) => {
									const declared = sig.params[i]?.typeAnnotation;
									// A parameter written over the signature's own type parameters is no slot's type.
									if (arg.type !== 'spread' && declared && !notASlot.has(arg) && !sig.typeParams?.some(p => T.mentionsTypeParam(declared, p.name)))
										noteSlot(declared, arg, scope);
								});
							}
						}
					}
					// Every flow the CHECKER accepted, stamped on the value it accepted (`checkFlow`): a declaration, an assignment,
					// an argument, a return, a yield, a field. Enumerating them here instead left spreads, returns and generic calls out.
					// An unannotated declarator's initializer has no stamp, yet is what the declarator holds.
					const flow	= flowSlotOf(e);
					const id	= flow?.element ? undefined : slotOf.get(e);
					if (flow && !notASlot.has(e))
						noteSlot(flow.type, e, scope, 4, flow.element, id);
					else if (!flow && id)
						noteSlot(checkerTypeOf(e, scope), e, scope, 4, false, id);
					return process(e);
				}).statements(m.body);
			if (propagating)
				continue;
			const opened	= { shapes: [...openShapes].filter(k => !before.has(k)), slots: [...openSlots].filter(d => !slotsBefore.has(d)) };
			const key		= (r: typeof opened) => [...r.shapes].sort().join('\n') + `\n${r.slots.length} slots`;
			if (remembered && key(remembered) !== key(opened))
				throw `internal: '${moduleId}' opened different shapes than the compile before it (${remembered.shapes.length} then, ${opened.shapes.length} now)`;
			if (moduleId !== '.')
				openedByModule.set(m.body, opened);
		}
	}
	walk();
	propagating = true;
	for (let n = -1; openSlots.size && openSlots.size !== n; walk())
		n = openSlots.size;
	return { openShapes, openSlots, openReads };
}

// The expando fields `collectExpandoFields` found for this shape, appended before its struct type is finalized. `optional`, because no
// construction site ever supplies one: source cannot spell `#ext`, and a statically-named one (`scope`, `pos`) is only written afterwards.
// A field on the shape ITSELF, not a subtype: known before the type exists, so nothing is cast and every instance has the slot.
// A class declared outside the entry module is known by its module too, as its key is (`ensureClass`): `W.ClassInfo` and
// wasm-backend.ts's own `ClassInfo extends W.ClassInfo` are two classes, and a key written onto one is not the other's.
function moduleTag(home: string | undefined): string {
	return home && home !== '.' ? `@${home}` : '';
}

function classIdentity(stmtHomeModule: Map<object, string>, ref: TS.RefType, scope: Scope): string {
	const dot	= ref.name.lastIndexOf('.');
	const leaf	= ref.name.slice(dot + 1);
	const decl	= LIB_DECL_MAP.get(leaf) ?? (dot > 0 ? scope.lookupScope(ref.name.slice(0, dot).split('.')) : scope)?.decl(leaf);
	return leaf + (decl?.type === 'class_decl' ? moduleTag(stmtHomeModule.get(decl)) : '');
}

function collectExpandoFields(
	stmtHomeModule: Map<object, string>,
	moduleBodies: Map<string, Module>,
	namedImportsByModule: Map<string, Map<string, {module: string; name: string }>>
) {
	const accessorKeys = new Map<string, Set<string>>();
	const pendingExtensions = new Map<string, string[] | 'dynamic'>();

	// A local's declared ANNOTATION, by name: a parameter already types as its annotation, but `const p: P = {...}` types as the literal's inferred shape, its declared name gone, and only the local's name identifies the shape to grow.
	// towasm's own local wtype comes from the annotation for exactly this reason. Not scope-precise: over-approximating adds an unused optional field, which costs a slot and breaks nothing.
	const annots = new Map<string, Type>();
	// Every member of a union gets the slot: the write lands on whichever one it turns out to be at runtime. A generic instantiation shares its shape's one struct, keyed by the bare name (`ensureObjectShape`); an array is `Array`'s.
	// A structural shape (an interface, an alias, an inline object type) by its member names -- `shapeKey`, the identity `layoutTwin` merges by, so a named shape and its anonymous twin keep one layout; a class by name.
	// A shape with no name (an inline object type) or a type parameter has nowhere to put one; nor has `{}`, whose empty literal is a dynamic object.
	const noteType = (raw: Type, key: string | undefined, scope: Scope, accessor = false) => {
		for (const member of T.unionMembers(raw, scope)) {
			const part = member.type === 'array' || member.type === 'tuple' ? TS.RefType('Array') : member;
			if (part.type === 'ref' && (T.isAny(part) || scope.type(part.name)?.isTypeParam))
				continue;
			const isClass	= part.type === 'ref' && (T.isClassRef(part, scope) || LIB_DECL_MAP.get(part.name)?.type === 'class_decl');
			const shape		= part.type === 'object' ? part : part.type === 'ref' && !isClass ? T.resolveObjectType(part, scope) : undefined;
			const name		= shape ? shape.members.length ? shapeKey(shape.members) : undefined : part.type === 'ref' ? classIdentity(stmtHomeModule, part, scope) : undefined;
			if (!name)
				continue;
			if (accessor && key !== undefined)
				(accessorKeys.get(name) ?? accessorKeys.set(name, new Set()).get(name)!).add(key);
			const prior = pendingExtensions.get(name);
			if (prior === 'dynamic')
				continue;
			if (key === undefined)
				pendingExtensions.set(name, 'dynamic');
			else if (!(shape ? shape.members.some(m => 'key' in m && m.key === key) : T.lookupMember(part, key, scope)))
				pendingExtensions.set(name, [...new Set([...(prior ?? []), key])]);
		}
	};
	// The RAW type, never `T.resolve`'s: resolving a ref expands it to its object shape and loses the NAME.
	const note = (recv: Expr, key: string | undefined, scope: Scope, accessor = false) => {
		const bare = unwrapAs(recv);
		noteType((bare.type === 'identifier' ? annots.get(bare.name) : undefined) ?? checkerTypeOf(bare, scope), key, scope, accessor);
	};
	for (const [_, m] of moduleBodies) {
		const modScope = m.scope as Scope;
		if (!modScope)
			continue;
		// The checker stamps its scope on STATEMENTS, so the enclosing statement's scope is what types the receiver -- a parameter or a local is resolvable there and nowhere else.
		// Tracked down the statement walk; the module scope is only the outermost fallback.
		let scope = modScope;
		walkerB(
			(st, process) => {
				const saved = scope;
				scope = (st as unknown as { scope?: Scope }).scope ?? scope;
				if (st.type === 'var_decl')
					for (const d of st.declarations)
						if (typeof d.name === 'string' && d.typeAnnotation)
							annots.set(d.name, d.typeAnnotation);
				const r = process(st);
				scope = saved;
				return r;
			},
			(e, process) => {
				if (e.type === 'assign' && e.target.type === 'member') {
					note(e.target.object, e.target.property, scope);
				} else if (e.type === 'object') {
					// A literal's own accessor: the shape it is built as -- where it flows, else its own type -- gets the key's companions.
					for (const q of e.properties)
						if ((q.type === 'get' || q.type === 'set') && typeof q.key !== 'object')
							noteType(flowSlotOf(e)?.type ?? checkerTypeOf(e, scope), String(q.key), scope, true);
				} else if (isDefinePropertyCall(e) && e.arguments[0]) {
					const desc = e.arguments[2];
					note(e.arguments[0], e.arguments[1]?.type === 'literal' && typeof e.arguments[1].value === 'string' ? e.arguments[1].value : undefined, scope,
						desc?.type === 'object' && desc.properties.some(q => (q.type === 'field' || q.type === 'method') && (q.key === 'get' || q.key === 'set')));
				} else {
					const assign = objectAssignCall(e);
					for (const w of assign?.writes ?? [])
						note(assign!.target, w.key, scope);
				}
				return process(e);
			}).statements(m.body);
	}

	// A key written onto a receiver whose static type names no struct -- a type parameter, `any`, `object` -- lands on whatever it holds at runtime, and only its SOURCES say what that is.
	// So the receiver is followed backwards to types that name a struct -- with function values tracked, since a stamper passed as a value (`makeRule(stampPos)`) is called through a parameter.
	// Flow- and context-insensitive: over-approximating only adds an unused optional slot. Not followed: a function value stored into an object or array field and called from there.
	interface Fn		{ params: (Binding | undefined)[]; returns: Site[]; declaredReturn?: Type; callers: Set<Call> }
	interface Binding	{ param?: { fn: Fn; index: number }; fn?: Fn; values: Site[]; declared?: Type; declScope?: Scope }
	interface Container	{ parent?: Container; names: Map<string, Binding>; moduleId: string; fn?: Fn }
	interface Site		{ e: Expr; c: Container; scope: Scope; from?: Fn }
	interface Call		{ callee: Site; args: (Site | undefined)[] }

	const fnOf			= new Map<object, Fn>();
	const moduleOf		= new Map<object, string>();
	const containerOf	= new Map<string, Container>();
	const bindings: Binding[]	= [];
	const calls: Call[]			= [];
	const assigns: { target: Site; value: Site }[]	= [];
	const seeds: { s: Site; key: string }[]			= [];

	const bindingIn = (c: Container, name: string): Binding => {
		let b = c.names.get(name);
		if (!b) {
			c.names.set(name, b = { values: [] });
			bindings.push(b);
		}
		return b;
	};
	const enter = (node: object, sig: TS.CallSig, c: Container, scope: Scope): Container => {
		const contextual	= (node as { contextualType?: Type }).contextualType;
		const fn: Fn		= { params: [], returns: [], callers: new Set(), declaredReturn: sig.returnType ?? (contextual?.type === 'function' ? contextual.returnType : undefined) };
		fnOf.set(node, fn);
		const inner: Container = { parent: c, names: new Map(), moduleId: c.moduleId, fn };
		sig.params.forEach((p, index) => {
			if (typeof p.key === 'string') {
				const b: Binding = { param: { fn, index }, values: [], declared: p.typeAnnotation, declScope: scope };
				inner.names.set(p.key, fn.params[index] = b);
				bindings.push(b);
			}
		});
		return inner;
	};
	// Some part of the receiver's own type names no struct, so its own type cannot say where the key lands.
	const untyped = (recv: Expr, scope: Scope) => T.unionMembers(checkerTypeOf(unwrapAs(recv), scope), scope).some(m =>
		m.type !== 'ref' || T.isAny(m) || m.name === 'object' || !!scope.type(m.name)?.isTypeParam);

	for (const [moduleId, m] of moduleBodies) {
		const modScope = m.scope as Scope;
		if (!modScope)
			continue;
		let c: Container = { names: new Map(), moduleId };
		containerOf.set(moduleId, c);
		for (const st of m.body)
			moduleOf.set(st.type === 'export_decl' ? st.declaration : st, moduleId);
		let scope = modScope;
		const site = (e: Expr): Site => ({ e, c, scope });
		const within = (inner: Container, process: () => boolean) => {
			const saved = c;
			c = inner;
			const r = process();
			c = saved;
			return r;
		};
		walkerB(
			(st, process) => {
				const savedScope = scope;
				scope = (st as unknown as { scope?: Scope }).scope ?? scope;
				let r: boolean;
				if (st.type === 'function_decl' && st.body) {
					const inner = enter(st, st, c, scope);
					bindingIn(c, st.name).fn ??= fnOf.get(st);
					r = within(inner, () => process(st));
				} else {
					if (st.type === 'var_decl') {
						for (const d of st.declarations) {
							if (typeof d.name !== 'string')
								continue;
							const b = bindingIn(c, d.name);
							b.declared ??= d.typeAnnotation;
							b.declScope ??= scope;
							if (d.init)
								b.values.push(site(d.init));
						}
					} else if (st.type === 'return' && st.argument && c.fn) {
						c.fn.returns.push(site(st.argument));
					}
					r = process(st);
				}
				scope = savedScope;
				return r;
			},
			(e, process) => {
				if (e.type === 'arrow' || e.type === 'function') {
					const inner = enter(e, e, c, scope);
					const fn = fnOf.get(e)!;
					if (e.type === 'function' && e.name)
						inner.names.set(e.name, { fn, values: [] });
					return within(inner, () => {
						if (e.type === 'arrow' && !Array.isArray(e.body))
							fn.returns.push(site(e.body));
						return process(e);
					});
				}
				if (e.type === 'call') {
					calls.push({ callee: site(e.callee), args: e.arguments.map(a => a.type === 'spread' ? undefined : site(a)) });
					const key = e.arguments[1];
					if (isDefinePropertyCall(e) && e.arguments[0] && key?.type === 'literal' && typeof key.value === 'string' && untyped(e.arguments[0], scope))
						seeds.push({ s: site(e.arguments[0]), key: key.value });
					const assign = objectAssignCall(e);
					if (assign && untyped(assign.target, scope))
						for (const w of assign.writes)
							seeds.push({ s: site(assign.target), key: w.key });
				} else if (e.type === 'assign') {
					if (e.target.type === 'identifier')
						assigns.push({ target: site(e.target), value: site(e.value) });
					else if (e.target.type === 'member' && untyped(e.target.object, scope))
						seeds.push({ s: site(e.target.object), key: e.target.property });
				}
				return process(e);
			},
			undefined,
			(member, process) => (member.type === 'method' || member.type === 'get' || member.type === 'set') && 'body' in member && member.body
				? within(enter(member, member as TS.CallSig, c, scope), () => process(member))
				: process(member)
		).statements(m.body);
	}

	const lookup = (name: string, c: Container): Binding | undefined => {
		for (let k: Container | undefined = c; k; k = k.parent) {
			const b = k.names.get(name);
			if (b)
				return b;
		}
		const imported = namedImportsByModule.get(c.moduleId)?.get(name);
		return imported && containerOf.get(imported.module)?.names.get(imported.name);
	};
	// An identifier, or `NS.name` through an `import * as NS`.
	const bindingOf = (s: Site, e: Expr): Binding | undefined => {
		if (e.type === 'identifier')
			return lookup(e.name, s.c);
		if (e.type === 'member' && e.object.type === 'identifier' && !lookup(e.object.name, s.c)) {
			const decl = s.scope.namespace(e.object.name)?.decl(e.property);
			const home = decl && moduleOf.get(decl);
			return home !== undefined ? containerOf.get(home)?.names.get(e.property) : undefined;
		}
		return undefined;
	};
	for (const { target, value } of assigns)
		bindingOf(target, target.e)?.values.push(value);

	// The functions each parameter or local may hold -- to a fixpoint, since a parameter holds what its callers
	// pass, and who its callers are depends on which functions each callee expression may hold.
	const held = new Map<Binding, Set<Fn>>();
	const fnsOf = (s: Site, seen = new Set<Expr>()): Set<Fn> => {
		const e	= unwrapAs(s.e);
		const out	= new Set<Fn>();
		if (seen.has(e))
			return out;
		seen.add(e);
		const add = (x: Expr) => fnsOf({ ...s, e: x }, seen).forEach(f => out.add(f));
		if (e.type === 'arrow' || e.type === 'function') {
			out.add(fnOf.get(e)!);
		} else if (e.type === 'identifier' || e.type === 'member') {
			const b = bindingOf(s, e);
			if (b?.fn)
				out.add(b.fn);
			else if (b)
				held.get(b)?.forEach(f => out.add(f));
		} else if (e.type === 'call') {
			for (const g of fnsOf({ ...s, e: e.callee }, seen))
				for (const r of g.returns)
					fnsOf(r, seen).forEach(f => out.add(f));
		} else if (e.type === 'conditional') {
			add(e.consequent);
			add(e.alternate);
		} else if (e.type === 'binary' && (e.operator === '&&' || e.operator === '||' || e.operator === '??')) {
			add(e.left);
			add(e.right);
		}
		return out;
	};
	for (let changed = true; changed;) {
		changed = false;
		const hold = (b: Binding | undefined, fs: Set<Fn>) => {
			if (!b || b.fn || !fs.size)
				return;
			let set = held.get(b);
			if (!set)
				held.set(b, set = new Set());
			for (const f of fs)
				if (!set.has(f)) {
					set.add(f);
					changed = true;
				}
		};
		for (const call of calls)
			for (const g of fnsOf(call.callee)) {
				if (!g.callers.has(call)) {
					g.callers.add(call);
					changed = true;
				}
				g.params.forEach((p, i) => {
					const a = call.args[i];
					if (a)
						hold(p, fnsOf(a));
				});
			}
		for (const b of bindings)
			for (const v of b.values)
				hold(b, fnsOf(v));
	}

	const reached	= new Map<string, Set<Expr>>();
	const work		= [...seeds];
	while (work.length) {
		const { s, key } = work.pop()!;
		// A cast states the type the value is used as -- which names its struct where the value's own type may not.
		let e = s.e;
		for (; e.type === 'as'; e = e.expression)
			noteType(e.typeAnnotation, key, s.scope);
		let seen = reached.get(key);
		if (!seen)
			reached.set(key, seen = new Set());
		if (seen.has(e))
			continue;
		seen.add(e);
		const follow = (x: Expr, from = s.from) => work.push({ s: { ...s, e: x, from }, key });
		let followed = false;
		const b = e.type === 'identifier' || e.type === 'member' ? bindingOf(s, e) : undefined;
		if (b && !b.fn) {
			if (b.declared)
				noteType(b.declared, key, b.declScope ?? s.scope);
			if (b.param)
				for (const call of b.param.fn.callers) {
					const a = call.args[b.param.index];
					if (a) {
						work.push({ s: a, key });
						followed = true;
					}
				}
			for (const v of b.values) {
				work.push({ s: v, key });
				followed = true;
			}
		} else if (e.type === 'call') {
			for (const g of fnsOf({ ...s, e: e.callee }))
				for (const r of g.returns) {
					work.push({ s: { ...r, from: g }, key });
					followed = true;
				}
		} else if (e.type === 'conditional') {
			follow(e.consequent);
			follow(e.alternate);
			followed = true;
		} else if (e.type === 'binary' && (e.operator === '&&' || e.operator === '||' || e.operator === '??')) {
			follow(e.left);
			follow(e.right);
			followed = true;
		} else if (e.type === 'object') {
			for (const p of e.properties)
				if (p.type === 'spread')
					follow(p.operand, undefined);
		}
		if (followed)
			continue;
		// Nothing further to follow: the value is made here, or comes from where this analysis does not look.
		if (s.from?.declaredReturn)
			noteType(s.from.declaredReturn, key, s.scope);
		noteType(checkerTypeOf(e, s.scope), key, s.scope);
	}

	return { accessorKeys, pendingExtensions };
}

// A class's `extends` operand as the type it names: `Base`, a namespace-qualified `NS.Base`, either with type arguments.
function superClassRef(e: Expr | undefined): TS.RefType | undefined {
	const dotted = (x: Expr): string | undefined => x.type === 'identifier' ? x.name
		: x.type === 'member' ? (o => o && `${o}.${x.property}`)(dotted(x.object)) : undefined;
	const target	= e?.type === 'instantiation' ? e.expression : e;
	const name		= target && dotted(target);
	return name ? TS.RefType(name, e?.type === 'instantiation' ? e.typeArgs : undefined) : undefined;
}

function homeKey(homeModule: string, name: string) {
	return homeModule === '.' ? name : homeModule + '\0' + name;
}


// What iterating `t` yields, and returns once done (TS's iteration types): read off its `[Symbol.iterator]()` iterator's
// `next()` result (`for await` tries `[Symbol.asyncIterator]` first). Without the protocol (an ES5 lib) only arrays and strings iterate.
// `iterator.next()`: JS sends `undefined` to a `next` that takes a value (a generator's).
function nextCall(iterator: Expr, it: T.IterationTypes, typeScope: Scope): Expr {
	return JS.Call(JS.Member(iterator, 'next'), T.isNullish(it.next, typeScope) ? [] : [{ type: 'identifier', name: 'undefined' }]);
}

// Substitutes a generic class's type parameters throughout its decl.
function substituteClassTypeParam(decl: JS.ClassDecl<Type>, map: ReadonlyMap<string, Type>): JS.ClassDecl<Type> {
	const out = substituteTypeParams(map).statement(decl) as JS.ClassDecl<Type>;
	// A STATIC member is restored verbatim: real TS forbids one referencing its class's type parameters, so
	// substituting into one can only corrupt a static's OWN same-named type parameter -- `Array<any>`'s
	// `_alloc<T>(n): T[]` became `any[]`, allocating `arr:ref` whatever it was called with, so `$ret` never had a chance to resolve it.
	// Order is structural, so `out.body[i]` is `decl.body[i]` throughout.
	out.body = out.body.map((m, i) => {
		if (hasMod(decl.body[i] as { modifiers?: string[] }, 'static'))
			return decl.body[i];
		memberTemplate.set(m, templateOf(decl.body[i]));
		return m;
	});
	return out;
}

// Applies a whole set of type-param substitutions in one `walk` pass; the caller resolves `map` for both the
// explicit-type-args and inferred-from-arguments cases (see `ensureGenericFunc`).
function substituteTypeParams(map: ReadonlyMap<string, Type>): Walker {
	return walker(
		// The checker's stamps are the TEMPLATE's, where `T` is opaque: stale for an instance, which is re-checked
		// (`instantiateDecl`, `ensureClass`) so its own scopes and types, on the concrete types, are stamped afresh.
		(s, process) => unstamped(process(s)),
		(e, process) => unstamped(process(e)),
		(t, process) => t.type === 'ref' && map.has(t.name) ? map.get(t.name)! : process(t),
		undefined,
		(m, process) => unstamped(process(m))
	);
}
// A fresh node even where nothing was substituted: the walk hands an untouched node back as itself, and an instance re-check
// stamps its types ON the node, so two instances sharing one would each read the other's.
function unstamped<N extends object>(built: N): N {
	const { scope, checkedType, checkedCall, ...rest } = built as N & { scope?: unknown; checkedType?: unknown; checkedCall?: unknown };
	// A declarator is no node of its own: its binding's hull (`flowType`) is the template's too.
	const decl = rest as { type?: unknown; declarations?: JS.Var<Type>[] };
	if (decl.type === 'var_decl')
		decl.declarations = decl.declarations!.map(({ flowType, ...d }) => d);
	return rest as N;
}

// A guard can refine a union member past anything physical (`Lit<string>` out of `Lit<string | number>`),
// but a value's struct is fixed when it is built: each refined part maps back to the one member it came from.
function backToDeclaredMembers(narrowed: Type, base: Type, scope: Scope): Type {
	const r = T.resolve(scope, base);
	if (r.type !== 'union')
		return narrowed;
	const members	= T.unionMembers(r, scope);
	const declared	= new Set(members.map(m => T.typeKey(m)));
	const refined	= T.unionMembers(T.resolve(scope, narrowed), scope);
	const parts		= refined.map(p => {
		if (declared.has(T.typeKey(p)))
			return p;
		const from = members.filter(m => !T.isAny(m) && T.isAssignable(p, m, scope));
		return from.length === 1 ? from[0] : p;
	});
	return parts.some((p, i) => p !== refined[i]) ? T.combineTypes(parts) : narrowed;
}

// A default reading an earlier parameter (`b.length`) has its references rewritten to the scratch local `emitCallArgs`
// binds into, matching the grammar `isReemittableDefault` accepts.
function substituteEarlierParamRefs(e: Expr, rename: ReadonlyMap<string, string>): Expr {
	const sub = (x: Expr) => substituteEarlierParamRefs(x, rename);
	// A node actually REBUILT here loses its branch stamp (`stampBranch`, checker.ts), same as `substituteTypeParams`: the
	// stamp was taken where the original parameter names were bound and cannot resolve the scratch locals they become at the
	// call site. A node returned untouched was not rewritten, so its stamp still means what it said.
	const out = rebuild();
	if (out !== e)
		delete (out as any).scope;
	return out;

	function rebuild(): Expr {
		switch (e.type) {
			case 'identifier': {
				const to = rename.get(e.name);
				return to ? { ...e, name: to } : e;
			}
			case 'member':		return { ...e, object: sub(e.object) };
			// The operator shapes `isReemittableDefault` accepts must be descended into as well, or the
			// `a` in `b = a * 2` stayed pointing at a name the call site has never heard of.
			case 'binary':		return { ...e, left: sub(e.left), right: sub(e.right) };
			case 'unary':		return { ...e, operand: sub(e.operand) };
			case 'conditional':	return { ...e, test: sub(e.test), consequent: sub(e.consequent), alternate: sub(e.alternate) };
			case 'array':		return { ...e, elements: e.elements.map(el => el && el.type !== 'spread' ? sub(el) : el) };
			default:			return e;
		}
	}
}

// A CLOSURE default (`sort(compareFn = (a, b) => ...)`) is judged by what it CAPTURES: only its own params and the earlier
// params the call site already passes -- anything else is an enclosing local re-emitted out of scope.
function closureDefaultIsSelfContained(e: Expr, earlierNames?: ReadonlySet<string>): boolean {
	if (e.type !== 'arrow' && e.type !== 'function')
		return false;
	const bound = new Set<string>(earlierNames);
	for (const p of e.params)
		if (typeof p.key === 'string')
			bound.add(p.key);
	let ok = true;
	walker(undefined, (x, process) => {
		if (x.type === 'identifier' && !bound.has(x.name))
			ok = false;
		return process(x);
	}).body(e.body);
	return ok;
}

// A default is re-emitted verbatim at each omitted call site (`emitCallArgs`), so it may reference only literals or an *earlier*
// parameter (`len = b.length`); anything else would resolve against the call site's scope, so it is applied in the callee instead.
function isReemittableDefault(e: Expr, earlierNames?: ReadonlySet<string>): boolean {
	return e.type === 'literal'
		// `undefined` is a language CONSTANT, not a name to resolve: self-contained and side-effect-free, which is the property this predicate actually tests.
		// The AST has a `null` literal but no `undefined` one, so it arrives as an identifier -- and `defaultsWithImplicitUndefined` synthesizes exactly this node.
		|| (e.type === 'identifier' && e.name === 'undefined')
		|| closureDefaultIsSelfContained(e, earlierNames)
		|| (e.type === 'array' && e.elements.every(el => el !== undefined && el.type !== 'spread' && isReemittableDefault(el, earlierNames)))
		// Same reasoning as the array case, and `{}` -- an all-defaults options bag -- is the common one.
		|| (e.type === 'object' && e.properties.every(pr => pr.type === 'field' && typeof pr.key !== 'object' && !!pr.value && isReemittableDefault(pr.value, earlierNames)))
		|| (e.type === 'identifier' && !!earlierNames?.has(e.name))
		|| (e.type === 'member' && !e.optional && isReemittableDefault(e.object, earlierNames))
		// An OPERATOR over things already re-emittable (`b = a * 2`, `n = -1`, `x = a ? 1 : 2`) adds no new name to resolve at the call site,
		// so it carries none of the cross-module hazard a default that *called* something would.
		|| (e.type === 'binary' && isReemittableDefault(e.left, earlierNames) && isReemittableDefault(e.right, earlierNames))
		|| (e.type === 'unary' && isReemittableDefault(e.operand, earlierNames))
		|| (e.type === 'conditional' && isReemittableDefault(e.test, earlierNames) && isReemittableDefault(e.consequent, earlierNames) && isReemittableDefault(e.alternate, earlierNames));
}

// A bare `p?: T` gets a synthesized `undefined` default, so an optional-but-defaultless trailing param can be omitted at a call site.
// A default only the callee can evaluate (`calleeDefault`) is applied there, so callers pass `undefined` for it too.
function defaultsWithImplicitUndefined(params: readonly { key: BindingTarget; default?: Expr; modifiers?: string[] }[]): (Expr | undefined)[] {
	return params.map((p, i) => p.default && isReemittableDefault(p.default, new Set(params.slice(0, i).flatMap(q => typeof q.key === 'string' ? [q.key] : []))) ? p.default
		: p.default || hasMod(p, 'optional') ? { type: 'identifier', name: 'undefined' } : undefined);
}

// An accessor's halves as `Object.defineProperty` stores them: one canonical `() => any` getter and `(v: any) => void`
// setter, so every accessor slot of a kind shares one type whatever the descriptor's own closures declared.
function getterSig(): TS.FunctionType { return { type: 'function', params: [], returnType: T.ANY }; }

function setterSig(): TS.FunctionType { return { type: 'function', params: [{ key: 'v', typeAnnotation: T.ANY }], returnType: T.VOID }; }

// The TS type of a HIDDEN field (`#ext`, an accessor's `#get:`/`#set:` companion) -- named in one place, so a derived shape
// repeating its base's hidden fields repeats them exactly and stays that base's wasm subtype. Plain expandos are `any`.
function hiddenFieldType(name: string): Type {
	return name === '#ext' ? TS.RefType('Map', [T.STRING, T.ANY])
		: name.startsWith('#get:') ? getterSig()
		: name.startsWith('#set:') ? setterSig()
		: T.ANY;
}

// A type argument that changes a generic's physical layout: a value stored unboxed, or a typed-array tag. Any other
// occupies one ref slot whatever it is, and keying on the finite set of these also bounds `Box<T[]>`-style recursion.
function ownsLayout(t: Type, scope: Scope): boolean {
	if (T.machineOf(t, scope))
		return true;
	// Only through a scalar part (a branded `number & {...}`): resolving a whole intersection distributes its unions, and a
	// fluent builder's `B<T & F<T>>` doubles at every step.
	if (t.type === 'intersection')
		return t.types.some(p => ownsLayout(p, scope));
	const r = T.resolve(scope, t);
	return r.type === 'ref' && (r.name === 'number' || r.name === 'boolean' || r.name === 'any');
}

// The tag is read UNRESOLVED on purpose: `T.resolve` collapses every `TypedArray` tag alike to plain `number`.
function layoutArgKey(t: Type, scope: Scope): string {
	const m = T.machineOf(t, scope);
	if (m)
		return m;
	// A structural shape keys by its members in sorted order: `E & {id}` and a literal's `{id, ...E's}` are one type and one layout.
	const r		= resolveParts(t, scope);
	const shape	= r.type === 'object' || r.type === 'intersection' ? T.resolveObjectType(r, scope) : undefined;
	const byKey	= (m: TS.TypeMember) => T.typeKey({ type: 'object', members: [m] });
	return T.typeKey(shape ? { ...shape, members: [...shape.members].sort((a, b) => byKey(a).localeCompare(byKey(b))) } : r);
}
// One struct per LAYOUT (`ownsLayout`): `Box<number>`'s `T[]` is a real `number[]`, while every reference argument
// erases to its constraint -- wasm fields are invariant, so separate `R<C>`/`R<{x}>` could never convert.
function layoutArgs(typeParams: readonly TS.TypeParam[] | undefined, typeArgs: readonly Type[] | undefined, scope: Scope): Type[] {
	const chosen = new Map<string, Type>();
	return (typeParams ?? []).map((p, i) => {
		const arg = typeArgs?.[i] ?? (p.default ? T.substituteType(p.default, chosen) : p.constraint ?? T.ANY);
		chosen.set(p.name, arg);
		return ownsLayout(arg, scope) ? arg : p.constraint ?? T.ANY;
	});
}
function layoutKey(name: string, args: readonly Type[], scope: Scope): string {
	return args.length ? `${name}<${args.map(a => layoutArgKey(a, scope)).join(',')}>` : name;
}
// A shape opens under its struct's key, so `Iterable<[string, X]>` opens `Iterable<Y>` too; a class instantiation by its own.
// An alias opens what it names (`TS.CallSig` is `JS.CallSig<Type>`), under the bare name its struct is registered by.
function openKey(t: Type, scope: Scope): string {
	let part = (n => n.type === 'array' ? TS.RefType('Array', [n.element]) : n)(T.nonNullable(t, scope));
	for (let next = T.expandRefOnce(scope, part); next.type === 'ref' && part.type === 'ref' && next.name !== part.name; next = T.expandRefOnce(scope, part))
		part = next;
	const entry	= part.type === 'ref' && part.typeArgs?.length && !T.isClassRef(part, scope) ? T.ownScope(part, scope).lookupType(part.name) : undefined;
	return part.type === 'ref' && entry?.typeParams?.length ? layoutKey(part.name.slice(part.name.lastIndexOf('.') + 1), layoutArgs(entry.typeParams, part.typeArgs, scope), scope) : T.typeId(T.resolve(scope, part));
}

// `t`'s non-nullish part resolved, an interface's `extends` intersection merged into the one object it describes.
function resolvedShape(t: Type, scope: Scope): Type {
	const r = T.resolve(scope, T.nonNullable(t, scope));
	return r.type === 'intersection' ? T.resolveObjectType(r, scope) ?? r : r;
}

// `t` resolved, and so are the parts of the tuples, arrays and unions it is built from: one type spelled two ways
// (`[string, TS.TypeParam]`, `[string, TypeParam<Type>]`) keyed two instantiations of one class, which could not convert.
function resolveParts(t: Type, scope: Scope, depth = 3): Type {
	const r = T.resolve(scope, t);
	if (depth === 0)
		return r;
	const part = (x: Type) => resolveParts(x, scope, depth - 1);
	const elem = (e: TS.TupleElement): TS.TupleElement => e.type === 'optional' || e.type === 'labeled' ? { ...e, element: part(e.element) }
		: e.type === 'spread' ? { ...e, argument: part(e.argument) } : part(e);
	return	r.type === 'tuple'	? { ...r, elements: r.elements.map(elem) }
		:	r.type === 'array'	? TS.ArrayType(part(r.element), r.readonly)
		:	r.type === 'union'	? TS.UnionType(r.types.map(part))
		:	r;
}

// A non-class generic's layout is the instantiation `layoutArgs` makes of it, as `openKey` keys it: `Spread<Type>` and `Spread<any>` are
// one struct. A class keeps its own arguments' layouts, since `ensureClass` collapses them only for a method-less class.
function genericSketch(t: Type & { type: 'ref' }, scope: Scope): string {
	const typeParams = t.typeArgs?.length && !T.isClassRef(t, scope) ? T.ownScope(t, scope).lookupType(t.name)?.typeParams : undefined;
	return typeParams ? layoutKey(t.name, layoutArgs(typeParams, t.typeArgs, scope), scope)
		: `${t.name}<${(t.typeArgs ?? []).map(a => ownsLayout(a, scope) ? layoutArgKey(a, scope) : 'ref').join(',')}>`;
}

// Would these two types occupy the same wasm slot? Answered WITHOUT building a shape -- this runs before codegen -- by the same collapse `ensureClass`
// applies: a reference type argument erases, so `TemplatePart<unknown>` and `TemplatePart<Type>` are one layout (widening one would leave it unbuilt, with nothing for a dynamic read to find).
function layoutSketch(t: Type | undefined, scope: Scope, depth = 3): string {
	if (!t || depth < 0)
		return 'any';
	// A GENERIC's reference is sketched unresolved: `ensureClass` collapses reference type arguments, so
	// `TemplatePart<unknown>` and `TemplatePart<Type>` are one instantiation, which substituting them apart would hide.
	if (t.type === 'ref' && t.typeArgs?.length && !scope.type(t.name)?.isTypeParam)
		return genericSketch(t, scope);
	const machine = T.machineOf(t, scope);
	if (machine)
		return machine;
	// A literal is stored as its base type: `'k'` is a string and `1 | 2` a number.
	const r = T.widenLiterals(T.resolve(scope, t), false, true);
	const members = T.unionMembers(r, scope).filter(m => !T.isNullish(m, scope));
	// A union of references is one `anyref`, and so is `any`/`unknown`/`object` -- `TemplatePart<unknown>`'s `exp?` and
	// `TemplatePart<Type>`'s (a union) are the same slot, while `Sig` and `Meth` are two distinct struct references.
	if (members.length > 1)
		return members.every(m => !!typeOfScalar(m, scope)) ? 'num' : 'any';
	if (r.type === 'ref') {
		if (T.isAny(r) || r.name === 'unknown' || r.name === 'object')
			return 'any';
		const scalar = typeOfScalar(r, scope);
		return scalar ?? genericSketch(r, scope);
	}
	if (r.type === 'array' || r.type === 'tuple') {
		// A tuple is an `Array` of its combined element type, which is a reference whenever the positions differ.
		const el = r.type === 'array' ? r.element : T.ANY;
		return `arr:${ownsLayout(el, scope) ? layoutSketch(el, scope, depth - 1) : 'ref'}`;
	}
	if (r.type === 'object')
		return `{${r.members.flatMap(m => {
			const key = (m.type === 'property' || m.type === 'method') && T.memberKey(m.key);
			return key ? [`${key}:${layoutSketch(T.lookupMember(r, key, scope), scope, depth - 1)}`] : [];
		}).sort().join(',')}}`;
	return 'ref';
}

// `number`/`boolean` are the only types stored unboxed; everything else is one reference slot.
function typeOfScalar(t: Type, scope: Scope): string | undefined {
	const r = T.resolve(scope, t);
	return r.type === 'ref' && (r.name === 'number' || r.name === 'boolean') ? r.name
		: r.type === 'literal' ? (typeof r.value === 'number' ? 'number' : typeof r.value === 'boolean' ? 'boolean' : undefined)
		: undefined;
}

// A readonly view is a checker-only distinction over the very same physical container.
const READONLY_ALIAS = new Map([['ReadonlyArray', 'Array'], ['ReadonlyMap', 'Map'], ['ReadonlySet', 'Set']]);

// The array-backed part of an intersection with one physical shape (an ARRAY carrying extra properties, e.g.
// `TemplateStringsArray`): the value IS the array. Flattened over the RAW parts, never `flattenIntersection`.
function arrayPartOf(t: Type, scope: Scope): { part: Type; element: Type } | undefined {
	// Matched on the part's own written shape, never through `resolve` -- that expands `Array<string>` into the
	// class's own object shape and loses the very thing being looked for. A TUPLE part is physically the same
	// `arr:ref`, its element the union of every position.
	const elementOf = (x: Type) => x.type === 'tuple' ? T.combineTypes(T.elementTypes(x, scope)) : T.arrayLikeElement(x);
	const arrays = T.flatParts([t], 'intersection').flatMap(part => {
		// A part whose array-ness is one resolution step away -- an alias, or a mapped type over an array.
		const element = elementOf(part) ?? elementOf(T.resolve(scope, part));
		return element ? [{ part, element }] : [];
	});
	return arrays.length && new Set(arrays.map(a => T.typeKey(a.element))).size === 1 ? arrays[0] : undefined;
}

// The primitive member of an intersection, by its own `typeofName`.
function primitivePart(t: TS.IntersectionType, scope: Scope): Type | undefined {
	return t.types.find(p => T.LITERAL_PRIMITIVES.has(T.typeofName(p, scope) ?? ''));
}


// A value with `[Symbol.iterator]()` iterates by the protocol, as JS iterates every iterable. An array is read by position:
// its own `[Symbol.iterator]` is for a value known only as an `Iterable`.
function iteratesByProtocol(e: Expr, ctx: FunctionContext): T.IterationTypes | undefined {
	const t = ctx.narrowedTypeOf(e);
	if (T.unionMembers(t, ctx.scope).every(m => arrayPartOf(m, ctx.scope)) || !T.lookupMember(t, '[Symbol.iterator]', ctx.scope))
		return undefined;
	const it = T.iterationTypes(t, ctx.scope);
	if (!it)
		throw `'${T.typeKey(t)}' has '[Symbol.iterator]()' but its iterator has no 'next()'`;
	return it;
}

// A spread argument whose expression has a TUPLE type has a statically known length -- exactly the case real TS allows in a
// fixed-arity call ("A spread argument must either have a tuple type or be passed to a rest parameter") -- and is expanded
// into that many positional index reads, in place, so nothing is reordered. Restricted to a re-emittable expression (an
// identifier or plain property chain off one), since each element re-evaluates it; anything else still gets the error below.
function expandTupleSpreads(args: Expr[], ctx: FunctionContext): Expr[] {
	const reemittable = (e: Expr): boolean => e.type === 'identifier' || e.type === 'this'
		|| (e.type === 'member' && !e.optional && reemittable(e.object));
	return args.flatMap(a => {
		if (a.type !== 'spread' || !reemittable(a.operand))
			return [a];
		const t = T.resolve(ctx.scope, ctx.narrowedTypeOf(a.operand));
		if (t.type !== 'tuple')
			return [a];
		return t.elements.map((_, i): Expr => JS.Index(a.operand, Literal(i)));
	});
}



// Reads `name`'s own physical storage slot (captured field or real local) exactly as-is -- never unboxing a forward-holder,
// unlike the ordinary identifier read (`case 'identifier'`). The one caller that needs this is `emitClosureLiteral`'s
// env-capture step, which must capture the holder's real, shared storage itself, never a snapshot of what it holds now.
// An index read TS types as possibly `undefined` (`args[1]` on `[A] | [A, B]`, an optional tuple element, `(T | undefined)[]`):
// JS reads past the end as `undefined`, where `array.get` traps, so such a read is bounds-checked.
function readsPastEnd(e: Expr, ctx: FunctionContext): boolean {
	return T.unionMembers(T.resolve(ctx.scope, ctx.narrowedTypeOf(e)), ctx.scope).some(m => T.isNullish(m, ctx.scope));
}

// `proven`: the type the result fits. 32-bit `+ - *` stays 32-bit only when that is `i32`/`u32`, else it is the exact `f64`.
function numericOpInline(method: string, a: W.Type | undefined, b: W.Type | undefined, ctx: FunctionContext, proven?: W.Type): Inline {
	const at = W.scalarKind(a), bt = W.scalarKind(b);
	const t	=	at === 'i64' || bt === 'i64' ? 'i64'
		:		(at === 'i32' || at === 'u32') && (bt === 'i32' || bt === 'u32') ? 'i32'
		:		at === 'f32' && bt === 'f32' ? 'f32'
		:		'f64';

	switch (method) {
		case 'add': case 'sub': case 'mul':
			if (t !== 'i32')
				return { params: [t, t], result: t, inline: [I[t][method]] };
			return proven === 'i32' || proven === 'u32'
				? { params: ['i32', 'i32'], result: proven, inline: [I.i32[method]] }
				: { params: ['f64', 'f64'], result: 'f64', inline: [I.f64[method]] };
		// Always float division, matching real JS `number` semantics -- never truncating, never traps on `0/0`, regardless of the operands' own transient wasm representation
		case 'div':
			return t === 'f32'
				? { params: ['f32', 'f32'], result: 'f32', inline: [I.f32.div] }
				: { params: ['f64', 'f64'], result: 'f64', inline: [I.f64.div] };
		case 'mod':
			return builtins.get('__towasm_mod')!([{wtype: t}], ctx) as Inline;
		case 'and': case 'or': case 'xor': case 'shl': case 'shr_s':
			return { params: ['i32', 'i32'], result: 'i32', inline: [I.i32[method]] };
		case 'shr_u':
			return { params: ['i32', 'i32'], result: 'u32', inline: [I.i32[method]] };

		case 'eq': case 'ne':
		case 'lt': case 'gt': case 'le': case 'ge':
			if ((t === 'i32' || t === 'i64')) {
				// Mixed signedness compares as the number both are: `f64` holds each exactly (an `i64` would be a bigint's unboxing).
				if (t === 'i32' && at !== bt)
					return { params: ['f64', 'f64'], result: 'i32', inline: [I.f64[method]] };
				return method === 'ne' || method === 'eq'
					? { params: [t, t], result: 'i32', inline: [I[t][method]] }
					: { params: [t, t], result: 'i32', inline: [I[t][`${method}_${at === 'u32' ? 'u' : 's'}`]] };
			}
			return { params: [t, t], result: 'i32', inline: [I[t][method]] };
	}
	throw `internal: unsupported compound-assignment method '${method}'`;
}

// Whether any instruction touches linear memory (a load/store or `memory.*` op), following only the lists that
// nest: `body` (block/loop/try_table) and `then`/`else` (if). Those are `LooseInstr` -- `Instr` can't name itself.
function touchesMemory(instrs: readonly wasm.LooseInstr[]): boolean {
	return instrs.some(i => /^(memory\.|(i32|i64|f32|f64|v128)\.(load|store))/.test(i.op)
		|| ('body' in i && touchesMemory(i.body))
		|| ('then' in i && (touchesMemory(i.then) || !!i.else && touchesMemory(i.else))));
}

// Checks builtinTypes before T.resolve to avoid expanding a hoisted class name and losing it.
function wasmTypeOf(t: Type, global: Scope): W.Type | undefined {
	const m = T.machineOf(t, global);
	if (m)
		return machineSlot(m);
	if (t.type === 'ref' && !t.typeArgs && builtinTypes.has(t.name))
		return builtinTypes.get(t.name)!.wtype;
	if (t.type === 'range' && t.base === 'number')
		return t.integer && t.min !== undefined && t.max !== undefined ? W.intType(t.min as number, t.max as number) : 'f64';
	// A bigint whose range the checker PROVED fits a machine int is held as one -- `const v = 1n + 2n` is an `i32`, not a heap
	// magnitude array. Nothing is checked at run time: a value without a proven range simply keeps the array, and `coerceTop`
	// widens at every boundary. An unbounded or too-wide range falls through to `bigint`'s own representation below.
	if (t.type === 'range' && t.base === 'bigint' && typeof t.min === 'bigint' && typeof t.max === 'bigint') {
		const w = W.bigIntType(t.min, t.max);
		if (w)
			return w;
	}
	// rangeToType collapses a single-value range to a Literal -- needs the same bounds check or it widens to f64.
	if (t.type === 'literal' && typeof t.value === 'number')
		return T.isIntValue(t.value) ? W.intType(t.value, t.value) : 'f64';
	if (t.type === 'literal' && typeof t.value === 'bigint') {
		const w = W.bigIntType(t.value, t.value);
		if (w)
			return w;
	}
	// A type with no inhabitant but null/undefined (`Literal<null>` from a narrowed `e.value === null`) holds only `ref.null`.
	if (T.isNullish(t, global) && !T.isRef(T.resolveOwn(t, global), 'void'))
		return W.REF_ANY_NULLABLE;

	// Resolve each union member first so alias duplicates collapse before arrayElemKind.
	const w = T.widenLiterals(t.type === 'union' ? T.combineTypes(t.types.map(m => T.resolve(global, m))) : T.resolve(global, t), false, true);
	if (w.type === 'array' || (w.type === 'ref' && (w.name === 'Array' || w.name === 'ReadonlyArray'))) {
		const elemType = w.type === 'array' ? w.element : w.typeArgs![0];
		const em = T.machineOf(elemType, global);
		const we = em === 'i8' || em === 'u8' ? 'i8' : W.elementKind(wasmTypeOf(elemType, global));
		return we ? W.ARRAY[we] : undefined;
	}

	// A tuple's own elements can be heterogeneous, so there's no single per-element wasm kind to pick the way a real array's element type gives one.
	// Physically it's just the same boxed-`anyref` "everything else" storage a mixed/`any`-typed array already uses (`ARR_WTYPE.ref`).
	// The checker already fully tracks each element's own precise type (`type-utils.ts`'s own extensive 'tuple' handling); codegen needed only this one physical-representation mapping, nothing else.
	if (w.type === 'tuple')
		return W.ARRAY.ref;

	if (w.type === 'ref')
		return builtinTypes.get(w.name)?.wtype;

	return undefined;
}

export function TStoWasm(ast: Module, modules?: Map<string, Module>, namedImports?: Map<string, Map<string, { module: string; name: string }>>, onTopLevelError?: (e: unknown) => void): wasm.WasmModule {
	const global = ast.scope as Scope;
	if (!global)
		throw new W.Error('ast must be checked (TStypeCheck/TStypeCheckAsync) before TStoWasm');

	// `libGlobal` must be `global` itself, not a lib-only scope: one would sever the ancestor chain and hide
	// every user declaration from anything built off it (`ctx.scope`) -- confirmed real (`Point`/`Wrapper` broke).
	const libGlobal			= global;

	const classes			= new Map<string, ClassInfo>();
	// User-declared *generic* top-level classes can't be eagerly seeded into `classes` under their bare name
	// (no single physical representation for `Box<T>` alone, only each concrete instantiation) -- `ensureClass`/`resolveGenericClassRef` look here instead, the user-class equivalent of `LIB_DECL_MAP`.
	const userGenericClassDecls = new Map<string, JS.ClassDecl<Type>>();

	const funcs				= new Map<string, FuncInfo>();
	const functionDeclByName = new Map<string, FunctionDecl>();
	// A module-level function by what the checker's call stamps name it (`CallSig.origin`): its declaration, an overload signature, a `const`'s arrow.
	const moduleFunctions = new Map<unknown, { name: string; home: string }>();

	// Every module reachable from `ast`, entry included under `'.'`; non-entry top-level functions are keyed
	// `homeKey(canonical, name)`, so a same-named function in two files never collides in the shared caches.
	// `LIB_MODULE`: one identity for the whole static lib (see `lazyGlobalFor`) -- not a real `moduleBodies`
	// entry, since `LIB_AST` is a flat concatenation with no per-file identity; the `moduleId === '.'` cases
	// below are entry-only by design.
	const LIB_MODULE			= '#lib';
	const moduleBodies			= new Map<string, Module>([['.', ast], ...(modules ?? [])]);
	// The checker only HOISTS an imported module; codegen needs its bodies' stamps (narrowing, local annotations).
	for (const m of modules?.values() ?? []) {
		if (m.scope && !checkedModules.has(m)) {
			checkedModules.add(m);
			checkImported(m.body, m.scope as Scope);
		}
	}
	// The entry's scope comes from its own `Program`, an imported module's from `makeScope` (see `compileFunc`);
	// `homeModule` is optional on a `ClassInfo`, and "no module" or "no scope yet" both mean: use your own.
	function moduleScopeOf(homeModule: string | undefined): Scope | undefined {
		return homeModule === undefined ? undefined : homeModule === '.' ? global : moduleBodies.get(homeModule)?.scope as Scope | undefined;
	}

	function moduleFilename(homeModule: string): string | undefined {
		return moduleBodies.get(homeModule)?.filename;
	}
	const namedImportsByModule = namedImports ?? new Map<string, Map<string, { module: string; name: string }>>();
	// `Scope.decl(name)` gives back the declaration object but not the file it came from, and a plain top-level
	// `var_decl` (unlike a function/class) has no module-scoped registration -- so the home module is recorded here.
	const stmtHomeModule		= new Map<object, string>();
	// The entry module's top-level `const`/`let` declarators, by name -- see the `moduleBodies` scan's own
	// comment on why `Scope.decl` can't answer this for the entry module.
	const topLevelVars			= new Map<string, { stmt: TS.Stmt; d: JS.Var<Type> }>();	// keyed by `homeKey(module, name)`
	// An enum is COMPILE-TIME here: no runtime object, a member read folds to its constant (see `case 'member'`)
	// and the declaration emits nothing. `enumNames` lets `resolvesGlobally` report one needs no capture slot.
	const enumMembers			= new Map<string, number | string>();
	const enumNames				= new Set<string>();
	// The backing slot of each `ensureLazyGlobal` wrapper, so a WRITE can reach the same storage the
	// wrapper reads. Keyed exactly like `lazyGlobals`.
	const lazyGlobalSlots		= new Map<string, { index: number; wtype: W.Type }>();


	// `const f = __asm<...>('...')` in a user module: `builtins` is built once from `LIB_DECLS` for `lib/*.ts`
	// only, so the same declaration elsewhere failed as "call to unknown function" -- hence a per-module map.
	const moduleAsmBuiltins = new Map<string, Builtin<Inline>>();
	for (const [moduleId, body] of moduleBodies) {
		for (let s of body.body) {
			if (s.type === 'export_decl')
				s = s.declaration;
			if (s.type !== 'var_decl')
				continue;
			for (const d of s.declarations) {
				if (typeof d.name === 'string' && isAsm(d.init))
					moduleAsmBuiltins.set(homeKey(moduleId, d.name), makeAsm(d.init, {}, {}));
			}
		}
	}
	// The one place an unqualified (or namespace-resolved) name turns into a `FunctionDecl` -- a lib
	// declaration is always homeModule-independent, checked only after the calling module's own.
	function resolveDecl(homeModule: string, name: string) {
		return functionDeclByName.get(homeKey(homeModule, name)) ?? LIB_DECL_MAP.get(name);
	}
	// True for a name that resolves without ever needing a closure capture slot: reachable from anywhere via
	// the ordinary `case 'identifier'` fallback chain, regardless of lexical nesting.
	function resolvesGlobally(homeModule: string, name: string): boolean {
		return globals.has(name) || LIB_DECL_MAP.get(name)?.type === 'var_decl' || !!resolveDecl(homeModule, name)
			|| !!namedImportsByModule.get(homeModule)?.has(name)
			// A namespace import binds a compile-time namespace, not a value, so it never needs a capture slot:
			// without this, `TS.parse(...)` inside a callback read as a free variable and threw "unresolved identifier".
			|| !!moduleScopeOf(homeModule)?.namespace(name)
			// A class name is a declaration, not a value, resolved at its own use site -- `collectFreeVars` cannot
			// tell the two apart, so without this ANY closure or nested function mentioning a module-level class threw.
			|| moduleScopeOf(homeModule)?.decl(name)?.type === 'class_decl'
			// An ENUM name, for the same reason: every read of it folds to a constant at its own site.
			|| enumNames.has(homeKey(homeModule, name))
			// The same for the entry module's own top-level `const`/`let`: `hoist` deliberately doesn't hoist a
			// plain `var_decl` into a scope, so `resolveDecl` cannot see one -- `topLevelVars` is where they live,
			// and without this a closure referencing one read as a free variable ("unresolved identifier 'LIB_DIR'").
			|| topLevelVars.has(homeKey(homeModule, name));
	}

	const worklist:			(()=>void)[] = [];
	const lateWorklist: 	(()=>void)[] = [];
	// A named function used as a *value*, not called directly: one shared zero-capture wrapper per function
	// name, not per use site -- populated the first time another expression shape needs it (callback, return...).
	const functionValueWrappers = new Map<string, FuncInfo>();
	const methodValueWrappers	= new Map<string, FuncInfo>();
	// A closure *value* whose concrete signature has a narrower/nullable-mismatched result than the slot it is
	// coerced into (real TS covariant-return assignability, e.g. `(x: number) => number` fitting one returning
	// `number | undefined`) -- one shared trampoline per (source, wanted) pair. See `ensureClosureCoercionWrapper`.
	const closureCoercionWrappers = new Map<string, { info: FuncInfo; wantStructTypeIndex: number; envTypeIndex: number }>();
	// `adoptingDecl`'s answer per class, `null` for one that adopts no storage.
	const adoptingDecls = new Map<ClassInfo, { decl: MethodMember; storage: W.Type & { arr: W.ElementI } } | null>();

	const closureLiterals: FuncInfo[] = [];
	const closureTypes		= new Map<string, ClosureTypeInfo>();
	// Which DECLARATION each object shape was built from (`Scope.type`'s own entry): two modules can declare the
	// same name (`Common.Member` and js-parser's own `Member`, which adds `optional?`), and a shape keyed by
	// name alone handed the second one the first's struct.
	const shapeEntries		= new Map<ClassInfo, unknown>();
	const shapeModuleTag	= new Map<unknown, string>();
	const moduleTagOf = (name: string, entry: unknown): string => {
		let tag = shapeModuleTag.get(entry);
		if (tag === undefined) {
			tag = '';
			for (const [mod, body] of moduleBodies)
				if (mod !== '.' && (body.scope as Scope | undefined)?.type(name) === entry) {
					tag = mod;
					break;
				}
			shapeModuleTag.set(entry, tag);
		}
		return tag;
	};
	// A hit on `name` that belongs to a DIFFERENT declaration of that name. Only a real type name can say so:
	// `ensureClass` is also asked for a shape by its own key (`want.ref`), which names no declaration at all.
	// A CLASS is compared only where the caller names a scope: a bare lookup (a shared dispatch reading `thisTsType`) means the
	// entry module no more than any other.
	const classEntries = new Map<ClassInfo, unknown>();
	const otherDeclaration = (info: ClassInfo, name: string, declScope?: Scope): boolean => {
		const own	= shapeEntries.get(info) ?? (declScope ? classEntries.get(info) : undefined);
		const asked	= own && (declScope ?? global).type(name);
		return !!asked && asked !== own;
	};
	const data				= new W.DataSection;
	const globals			= new Map<string, Global>;
	// `ensureLazyGlobal`'s own wrapper `FuncInfo`s, keyed the same `homeKey` way as `funcs` itself.
	const lazyGlobals		= new Map<string, FuncInfo>;

	const types	= new W.Types;

	// One tag for the whole module -- JS/TS `catch(e)` is untyped and catches any thrown value regardless of its real TS type, so there's no reason for more than one
	const tags				= new W.TagSection;
	const ensureExceptionTag = () => tags.exception(types);

	// A closure referencing a SIBLING const/let declared later in the same block (mutually recursive local
	// closures, e.g. walker.ts's `mapStatementC` capturing `mapStatement`) has no local to capture: the
	// ordinary capture copies the current value into the closure's env at creation time (`rawSlot`).
	// Make the missing local an `ensureHolderType` holder -- closure and sibling's var_decl share one storage,
	// so the value is visible once assigned, whichever order they compile in.
	// Its type comes from a shallow scan of `ctx.ownBody`'s top-level `var_decl`s (never into a nested closure,
	// whose locals are never siblings); only a plain single-name declarator is handled, and a non-sibling name
	// returns `undefined`, leaving the "unresolved identifier" throw.
	function ensureForwardHolder(ctx: FunctionContext, name: string): W.Local | undefined {
		// Its own initializer's declarator first: a self-reference may sit in any nested block (a switch case,
		// `objectKeyNames`), which the shallow top-level scan misses -- and its holder then lands in the right scope.
		const d = ctx.initializing?.slice().reverse().find(d => d.name === name)
			?? ctx.ownBody?.flatMap(s => s.type === 'var_decl' ? s.declarations : []).find(d => d.name === name);
		// A sibling function declaration not yet created: mutual recursion (checker.ts `typeOf`'s `recurse` and `recurseUncached`).
		const fd = d ? undefined : ctx.ownBody?.find((s): s is Extract<Stmt, { type: 'function_decl' }> => s.type === 'function_decl' && s.name === name && !!s.body);
		if (fd) {
			const fnType = (fd as { scope?: Scope }).scope?.value(name) ?? checkerTypeOf({ ...fd, type: 'function' } as Expr, ctx.scope);
			const fnWtype = typeOf(fnType);
			return fnWtype ? declareHolder(ctx, name, fnWtype, fnType) : undefined;
		}
		if (!d)
			return undefined;
		const tsType = d.typeAnnotation ?? (d.init && checkerTypeOf(d.init, ctx.scope));
		if (!tsType)
			return undefined;
		const wt = typeOf(tsType);
		return wt ? declareHolder(ctx, name, wt, tsType) : undefined;
	}


	// Promotes `name` to a shared, heap-allocated one-field holder -- the physical form a captured BINDING
	// needs, so that a write from either side of the capture is seen by the other.
	function declareHolder(ctx: FunctionContext, name: string, wt: W.Type, tsType: Type): W.Local {
		if (process.env.DBGHOLDER)
			console.error(`HOLDER ${ctx.name}.${name}`);
		// The holder's field must be DEFAULTABLE (allocated before the declaration that fills it runs): a reference is
		// nullable, but a scalar stays RAW -- `types.nullable` would box it, and `holderInner` must describe the value.
		const holderTypeIndex = types.holder(toValType(typeof wt === 'string' ? wt : types.nullable(wt)));
		const local = ctx.declareValue(name, { typeIndex: holderTypeIndex, nullable: false }, tsType);
		local.holderInner = wt;
		ctx.emit(I.struct.new_default(holderTypeIndex), I.local.set(local.index));
		return local;
	}

	// Memoized per function: which of this body's own locals a nested closure captures AND something
	// assigns (`collectCapturedMutables`). Those must be holders, not plain wasm locals.
	function needsHolder(ctx: FunctionContext, name: string): boolean {
		// Never at module scope: a top-level binding is already shared (a real wasm global or `ensureLazyGlobal`'s
		// slot), so a holder there would leave the global and the holder as two separate storages.
		if (!ctx.ownBody || ctx.ownBody === ast.body)
			return false;
		ctx.holderNames ??= collectCapturedMutables(ctx.ownBody);
		return ctx.holderNames.has(name);
	}

	function toResults(result: W.Type): wasm.ValType[] {
		return result === 'void' ? [] : [toValType(result)];
	}
	function toParams(params: W.Type[]): wasm.ParamType[] {
		return params.map(p => ({ type: toValType(p) }));
	}
	function toParams2(params: ResolvedParam[]): wasm.ParamType[] {
		return params.map((p) => ({ type: toValType(p.wtype), id: typeof p.key === 'string' ? p.key : undefined }));
	}
	function builtinTypeOwner(name: string) {
		const bt = builtinTypes.get(name);
		return bt?.class ? ensureClass(bt.class) : undefined;
	}

	// Whether `init` is something a real wasm global can be initialized from -- a folded scalar literal, and
	// nothing else. A string is still a `literal` node but its physical value is an i16 array built at runtime,
	// and a `bigint` only qualifies on a real `i64` slot; everything rejected here belongs to `ensureLazyGlobal`.
	// Returns the FOLDED initializer the global must actually be registered with (`-99` is a `unary` node and
	// the emitter accepts only a literal), so the test and the value used can't drift apart.
	// Only a value a wasm global can be initialized from; anything else is `lazyGlobalFor`'s.
	function libGlobalFor(name: string) {
		const decl	= LIB_DECL_MAP.get(name);
		const eager	= decl?.type === 'var_decl' && decl.init ? eagerGlobalInit(decl.init, decl.typeAnnotation) : undefined;
		return decl?.type === 'var_decl' && eager ? ensureGlobal(name, typeOf(decl.typeAnnotation!)!, eager, decl.kind !== 'const') : undefined;
	}

	function eagerGlobalInit(init: Expr, typeAnnotation?: Type): Expr | undefined {
		const folded = foldConstants(init);
		if (folded?.type !== 'literal')
			return undefined;
		const kind = W.notUnsigned(W.scalarKind(typeOf(typeAnnotation ?? checkerTypeOf(init, libGlobal))));
		return kind && (typeof folded.value === 'number' || typeof folded.value === 'boolean' || (typeof folded.value === 'bigint' && kind === 'i64'))
			? folded : undefined;
	}

	function ensureGlobal(name: string, wtype: W.Type, init: Expr, mut: boolean) {
		if (!globals.has(name))
			globals.set(name, {wtype, index: globals.size, init, mut});
		return globals.get(name)!;
	}

	// A top-level `const X = someFactory(...)` -- the pervasive declarative-DSL idiom -- has no wasm representation
	// until something calls the factory, and real globals can only be initialized from a compile-time constant,
	// so it is lazy-on-first-use (the user's explicit call over eager cross-module init ordering): a mutable
	// nullable global starts `null` and a wrapper computes and caches the real value on first call.
	// `d.init` is compiled with `declScope` as the wrapper's own home scope, so any name it references (another
	// lazy global, a sibling function) resolves against ITS OWN declaring module, not the caller's -- `hoist()`'s
	// `exportScope` loop stamps `addDecl` for exactly this shape.
	function ensureLazyGlobal(name: string, homeModule: string, d: JS.Var<Type>, declScope: Scope): FuncInfo | undefined {
		// `const f = __asm<[...], R>('...')` DECLARES a builtin and holds no value, so returning `undefined` lets the
		// reference fall through to `moduleAsmBuiltins`. Guarded here rather than in `lazyGlobalFor` because
		// `case 'call'`'s closure-valued-const path reaches this function directly.
		if (d.init && isAsm(d.init))
			return undefined;
		const key = homeKey(homeModule, name);
		const existing = lazyGlobals.get(key);
		if (existing)
			return existing;

		// An imported module's scope only carries its EXPORTS, so a non-exported module-level binding has
		// no declared type there -- ask the checker for its initializer's instead, in that same scope.
		const checkedType = declScope.value(name) ?? (d.init && checkerTypeOf(d.init, declScope));
		// `typeOf` has no answer for a bare anonymous object shape (only a named class, an index signature or
		// an all-call-signature one), so give it the same synthesized struct an object literal targeting that
		// shape already gets, or a `const D: {a: number} = {...}` has no representation to cache into.
		const resolved = checkedType && T.resolve(global, checkedType);
		const wt = (checkedType && typeOf(openedAs(d, checkedType)))
			?? (resolved?.type === 'object' ? ensureAnonObjectShape(resolved)?.thisType : undefined);
		if (!wt || wt === 'void' || !d.init)
			return undefined;
		const g = ensureGlobal(`$lazy$${key}`, types.nullable(wt), Identifier('undefined'), true);
		lazyGlobalSlots.set(key, g);

		const { funcIndex, typeIndex } = types.func([], toResults(wt));
		const info: FuncInfo = { params: [], result: wt, funcIndex, typeIndex };
		lazyGlobals.set(key, info);
		worklist.push(W.withCatch(() => {
			const ctx = new FunctionContext(name, new Scope(declScope), plainReturn(wt), undefined, homeModule);
			// Hand-emitted, not `emitStmt`/AST-synthesized like the file's other desugarings -- `wtypeOf`/`checkerTypeOf`
			// can't see `slotName` at all (never real source the checker type-checked); only `d.init` itself goes through the
			// checker-aware `emitAs`. Emits `if (slot === null) slot = <init>; return slot!;`.
			ctx.emit(I.global.get(g.index), I.ref.is_null);
			ctx.emitIf(undefined, () => {
				// The declared type is the initializer's context, as for a local: `[{...}]` builds `Rules<Mod>`'s own shape. Built as the
				// VALUE type, then boxed into the slot: a bigint literal only takes an `i64` form when that is what it is built as.
				ctx.withContext(checkedType, () => emitAs(d.init!, ctx, wt));
				coerceValue(d.init!, wt, ctx, g.wtype);
				ctx.emit(I.global.set(g.index));
			});
			// `coerceTop`, not a bare `ref.as_non_null`: `types.nullable` BOXES a scalar slot, so for an
			// `i32`/`f64` const the slot holds a box while this wrapper's signature promises the scalar.
			ctx.emit(I.global.get(g.index));
			coerceTop(g.wtype, ctx, wt);
			ctx.emit(I.return);
			info.body = ctx.toFuncBody(0, toValType);
		}, name, homeModule));
		return info;
	}


	// A class REFERENCE written as an expression -- a bare name or a namespace-qualified one (`T.Scope`, through an
	// `import * as T`) -- resolved to the class's own name plus the scope to look it up in. A qualified reference
	// resolves in the NAMESPACE's own scope, not the caller's, so both names land on the same physical class.
	function classRefTarget(e: Expr, scope: Scope, seen?: Set<string>): { name: string; scope: Scope } | undefined {
		if (e.type === 'identifier')
			return scope.decl(e.name)?.type === 'class_decl' ? { name: e.name, scope } : classAliasTarget(e.name, scope, seen);
		if (e.type === 'member' && e.object.type === 'identifier') {
			const ns = scope.namespace(e.object.name);
			if (ns?.decl(e.property)?.type === 'class_decl')
				return { name: e.property, scope: ns };
		}
		return undefined;
	}

	// A top-level `const X = C`/`const X = T.C`: a class has no runtime value here (nominal, never first-class), so such a const is a compile-time alias, not a global to evaluate.
	// `ensureClass` resolves through it and `__toplevel` emits nothing; `seen` guards a self- or mutually-referential chain.
	function classAliasTarget(name: string, scope: Scope, seen = new Set<string>(), homeModule = '.'): { name: string; scope: Scope } | undefined {
		if (seen.has(name))
			return undefined;
		seen.add(name);
		const varStmt	= scope.decl(name);
		const d			= varStmt?.type === 'var_decl' ? varStmt.declarations.find(v => v.name === name) : topLevelVars.get(homeKey(homeModule, name))?.d;
		return d?.init ? classRefTarget(d.init, scope, seen) : undefined;
	}

	// `scope`: where to resolve `name` -- the reading function's own by default, or an `import * as NS`
	// namespace's scope for an `NS.name` read, reaching the same const its qualified name does (`case 'member'`).
	function lazyGlobalFor(name: string, ctx: FunctionContext, scope: Scope = ctx.scope) {
		const varStmt	= scope.decl(name);
		const own		= varStmt?.type === 'var_decl'
			? { stmt: varStmt as TS.Stmt, d: varStmt.declarations.find(d => d.name === name) }
			: scope === ctx.scope ? topLevelVars.get(homeKey(ctx.homeModule, name)) : undefined;
		if (!own?.d) {
			// A named import of another module's const (`import { isJsStatement } from './walker'` in printer.ts): the same lazy
			// global under its DECLARING module's identity, since the reading module's own scope never declares it.
			const imported	= scope === ctx.scope ? namedImportsByModule.get(ctx.homeModule)?.get(name) : undefined;
			const target	= imported && topLevelVars.get(homeKey(imported.module, imported.name));
			if (imported && target?.d) {
				const wrapper	= ensureLazyGlobal(imported.name, imported.module, target.d, moduleScopeOf(imported.module) ?? scope);
				const slot		= lazyGlobalSlots.get(homeKey(imported.module, imported.name));
				return wrapper && slot ? { wrapper, slot } : undefined;
			}
			// A module-level binding in a STATIC lib file (`LIB_AST`): those files are never in `moduleBodies`, so they are
			// absent from `topLevelVars`, but share one flat `libGlobal` -- so the identity must be a FIXED one, since falling
			// back to `ctx.homeModule` would give each referencing module its own copy of the same shared state.
			const lib = LIB_DECL_MAP.get(name);
			if (lib?.type === 'var_decl' && lib.init && !isAsm(lib.init)) {
				const wrapper	= ensureLazyGlobal(name, LIB_MODULE, lib as unknown as JS.Var<Type>, libGlobal);
				const slot		= lazyGlobalSlots.get(homeKey(LIB_MODULE, name));
				return wrapper && slot ? { wrapper, slot } : undefined;
			}
			return undefined;
		}
		const homeModule	= stmtHomeModule.get(own.stmt) ?? ctx.homeModule;
		// `scope` is only where `name` was FOUND: an `NS.name` read finds it in the module's export scope, which lacks
		// that module's own imports. The initializer compiles in its home module's own scope, as its functions do.
		const wrapper		= ensureLazyGlobal(name, homeModule, own.d, moduleScopeOf(homeModule) ?? scope);
		const slot			= lazyGlobalSlots.get(homeKey(homeModule, name));
		return wrapper && slot ? { wrapper, slot } : undefined;
	}

	// A top-level `const` naming something already declared elsewhere (a class, a cross-module binding) has no module-init effect: reads resolve through `ensureClass`/`lazyGlobalFor` to the real declaration.
	// The start function must emit nothing for it -- evaluating it would demand a physical representation in EVERY module declaring the alias.
	function isAliasInit(e: Expr, scope: Scope): boolean {
		// `const JSBinary = Binary<Expr, binaryOps>` -- naming a generic declaration with explicit type
		// arguments is still just naming it.
		if (e.type === 'instantiation')
			return isAliasInit(e.expression, scope);
		// `const f = __asm<[...], R>('...')` DECLARES a builtin (`moduleAsmBuiltins`); there is no value to
		// evaluate, and the start function trying to call `__asm` is exactly the "unknown function" it got.
		return isAsm(e)
			|| !!classRefTarget(e, scope)
			|| (e.type === 'identifier' && scope.decl(e.name)?.type === 'function_decl')
			|| (e.type === 'member' && e.object.type === 'identifier' && !!scope.namespace(e.object.name));
	}

	// Every class in the program, scanned once for a plain named `superClass` reference: shared by `ensureClass`'s `final` flag and virtual dispatch, which both need the whole inheritance graph known up front.
	// `final` can't be decided lazily: wasm-GC only lets a non-final struct be another's `supertypes` entry once its type is registered. Keyed by bare declared name (`Box<T>` matches `Box`).
	const directSubclasses	= new Map<string, TS.Class[]>();
	const everExtended		= new Set<string>();


	// Whether any class transitively extending `className` declares its own non-static `methodName` -- decided from whole-program source (`directSubclasses`), not the lazily populated `classes` set.
	// `emitMethodCall` uses this to skip `ensureVirtualDispatch`: with no override reachable, a direct `ensureMethod` call is already correct and optimal. Memoized per pair.
	const declaredOverrideCache = new Map<string, boolean>();
	// `classId`: the class's name and declaring module (`classIdentity`).
	function hasDeclaredOverride(classId: string, methodName: string): boolean {
		const key = `${classId}.${methodName}`;
		let cached = declaredOverrideCache.get(key);
		if (cached === undefined) {
			cached = (directSubclasses.get(classId) ?? []).some(sub => sub.body.some(m => m.type === 'method' && m.key === methodName && !hasMod(m, 'static')) || hasDeclaredOverride(sub.name! + moduleTag(stmtHomeModule.get(sub)), methodName));
			declaredOverrideCache.set(key, cached);
		}
		return cached;
	}


	// The raw {params, result, hasRest, defaults} for one `TS.CallSig`-shaped signature -- shared by a bare function TYPE (`case 'function'`) and each member of an overloaded object type (`mergeOverloadSigs`).
	// Both are the same shape, so the substitution logic isn't duplicated. `undefined` only when the return type can't be represented -- an unrepresentable param still throws.
	// A rest parameter's own physical type, which must be an array or `emitCallArgs` cannot pack into it.
	function restParamWtype(t: Type): W.Type | undefined {
		const wt = typeOf(t);
		if (storageKindOf(wt) !== undefined)
			return wt;
		const elems = T.elementTypes(t, global);
		return elems.length ? typeOf(TS.ArrayType(T.combineTypes(elems))) : wt;
	}

	function closureSigParts(sig: TS.CallSig): FullSig | undefined {
		// The type-annotation-side twin of `emitClosureLiteral`'s own comment: same bound substitution, same free-when-bounded reasoning.
		const func = T.baseSignature(sig, T.ANY);
		// Naming the whole signature, not just the parameter: one of these reaches a caller from some
		// enclosing declaration's own type, and the parameter name alone rarely says which.
		const sigText = () => T.typeKey({ type: 'function', ...sig } as Type);
		const defaults = defaultsWithImplicitUndefined(func.params);
		const omittable = (i: number) => !!defaults[i] && T.nullLiteralKind(defaults[i]!) === 'undefined';
		const params = func.params.map((p, i) => {
			// `void` is valid TS in a param position but has no wasm value, so box it as `any` like any other "no meaningful value" position rather than rejecting valid source.
			const wt = p.typeAnnotation && typeOf(p.typeAnnotation);
			const boxed = wt === 'void' ? W.REF_ANY : wt;
			if (!boxed)
				throw `function type parameter '${describeBinding(p.key)}': '${p.typeAnnotation ? T.typeKey(p.typeAnnotation) : '<no annotation>'}' has no representation, in '${sigText()}'`;
			// A slot a caller may fill with `undefined` (a bare `p?: T`, or a default only the callee can apply) is nullable;
			// a re-emitted default always arrives. Same rule as `resolveParam`, or the two physical signatures disagree.
			return omittable(i) ? types.nullable(boxed) : boxed;
		});
		// Always built: an UNANNOTATED closure parameter takes its type from the callee's declared
		// signature (`emitClosureLiteral`), which needs the TS type and not just the physical one. It widens with a nullable
		// slot, as `resolveParam`'s does: an imported module's callback reaches here unannotated, and `x === undefined` needs it.
		const resolvedParams = func.params.map((p, i) => ({ key: p.key, wtype: params[i], tsType: omittable(i) ? T.combineTypes([p.typeAnnotation!, T.UNDEFINED]) : p.typeAnnotation! }));
		let hasRest = false;
		// The rest ELEMENT as well as the array: a closure literal with more parameters than the
		// signature has fixed ones takes each extra one from here, and binds it out of the rest array.
		let restElem: ResolvedParam | undefined;
		if (func.rest?.typeAnnotation) {
			const wt = restParamWtype(func.rest.typeAnnotation);
			if (!wt || wt === 'void')
				throw "a function type's rest parameter needs an explicit array type";
			params.push(wt);
			resolvedParams.push({ key: func.rest.key, wtype: wt, tsType: func.rest.typeAnnotation });
			hasRest = true;
			const element = arrayPartOf(func.rest.typeAnnotation, global)?.element;
			const ewt = element && typeOf(element);
			if (element && ewt)
				restElem = { key: func.rest.key, wtype: ewt === 'void' ? W.REF_ANY : ewt, tsType: element };
		}
		let result = func.returnType ? typeOf(func.returnType) : 'void';
		// A function TYPE's return annotation is a genuine declared-type position (unlike `typeOf`'s own 'object' case, see `ensureAnonObjectShape`): an inline `{value: T; consumed: number}` still needs a representation.
		// Scoped to exactly this spot, not a general `typeOf` fallback -- that collides with a NAMED type whose `ref` wrapper `T.combineTypes` flattened away.
		if (!result && func.returnType) {
			const returnResolved = T.resolve(global, func.returnType);
			if (returnResolved.type === 'object' && !indexSignatureValueType(returnResolved)) {
				const cls = ensureAnonObjectShape(returnResolved);
				result = cls?.thisType;
			}
		}
		if (!result)
			return undefined;
		return { params, result, hasRest, defaults, resolvedParams, restElem };
	}

	// An overload set as a VALUE has one underlying function and no name to pick an implementation by.
	// So the overloads' physical signatures merge into ONE position by position: a param in every overload keeps its type, one missing from some becomes optional/nullable.
	function mergeOverloadSigs(sigs: FullSig[]): FullSig | undefined {
		if (!sigs.length)
			return undefined;
		const maxParams = Math.max(...sigs.map(s => s.params.length));
		const params: W.Type[] = [];
		const defaults: (Expr | undefined)[] = [];
		for (let i = 0; i < maxParams; i++) {
			const present = sigs.filter(s => s.params.length > i);
			const distinct = new Set(present.map(s => W.typeKey(s.params[i])));
			const shared = distinct.size === 1 ? present[0].params[i] : W.REF_ANY;
			if (present.length < sigs.length) {
				params.push(types.nullable(shared));
				defaults.push(Identifier('undefined'));
			} else {
				params.push(shared);
				defaults.push(undefined);
			}
		}
		const resultKinds = new Set(sigs.map(s => W.typeKey(s.result)));
		return { params, result: resultKinds.size === 1 ? sigs[0].result : W.REF_ANY, hasRest: sigs.some(s => s.hasRest), defaults };
	}


	// The `ClassInfo` a type REFERENCE names. A namespace-qualified ref resolves its leaf in the NAMESPACE's scope, since `ensureClass` never splits on '.'.
	// Without that it built a shape-only stand-in colliding with the real class. Scoped to a leaf that really is a CLASS there: a dotted interface or alias keeps its structural path.
	function ensureClassRef(t: TS.RefType): ClassInfo | undefined {
		const dot = t.name.lastIndexOf('.');
		if (dot > 0) {
			const leaf	= t.name.slice(dot + 1);
			const ns	= ((t.declScope as Scope | undefined) ?? global).lookupScope(t.name.slice(0, dot).split('.'));
			// A class by its declaration, an interface or alias by its TYPE entry (`JS.CallSig<Type>`): both resolve in the
			// namespace's own scope, so the dotted and the bare spelling reach the one struct.
			if (ns && (ns.decl(leaf)?.type === 'class_decl' || ns.type(leaf)))
				return ensureClass(leaf, t.typeArgs, ns);
		}
		// A readonly view IS its mutable class physically, though the lib declares it an interface of its own.
		return ensureClass(READONLY_ALIAS.get(t.name) ?? t.name, t.typeArgs, t.declScope as Scope | undefined);
	}

	// A SELF-REFERENTIAL type has no single physical shape, so re-entering `typeOf` on one already being computed boxes as `any` (as the union case does for an unrepresentable member).
	// The cycle is between `typeOf` calls, not inside one, so `T.resolve`'s cycle guard never sees it -- a function type taking itself overflowed the stack on checker.ts's declarations.
	const typeOfActive = new Set<Type>();
	function typeOf(t: Type): W.Type | undefined {
		if (typeOfActive.has(t))
			return W.REF_ANY;
		typeOfActive.add(t);
		try {
			return typeOfUncached(t);
		} finally {
			typeOfActive.delete(t);
		}
	}
	// A shape's call signatures as one closure. Every overload must resolve: a partial merge would silently
	// misrepresent the physical signature rather than fall through to the caller's own unresolved-type error.
	function callSignaturesWtype(members: TS.TypeMember[]): W.ClosureType | undefined {
		const sigs		= members.filter(m => m.type === 'call').map(closureSigParts);
		const merged	= sigs.every((s): s is FullSig => !!s) ? mergeOverloadSigs(sigs) : undefined;
		return merged && closureWtype(merged);
	}

	function typeOfUncached(t: Type): W.Type | undefined {
		// A machine type's representation is the slot it names, which resolving (to its value type) would lose.
		if (T.machineOf(t, global))
			return wasmTypeOf(t, global);
		if (t.type === 'ref' && t.name === 'RawArray')
			return W.ARRAY[rawElemKind(t.typeArgs?.[0], typeOf)];

		// An open shape is stored as `any` and may hold any layout (`ownerFor` agrees); a union's nullable part is its members' business.
		if (openShapes.size && t.type !== 'union' && openShapes.has(openKey(t, global)))
			return W.REF_ANY;
		// `T[]` is `Array<T>`, an ORDINARY lib class -- the compiler has no array representation of its own (see
		// [[tison-array-identity]]); `Array<T>`/`ReadonlyArray<T>` already reach the class via the generic-ref branch below.
		if (t.type === 'array') {
			const cls = ensureClass('Array', [t.element]);
			if (cls)
				return cls.thisType;
		}
		// A tuple is an array in TS too, and `ownerFor` already dispatches its methods through `Array` (`tupleArrayOwner`) -- same representation, or a tuple read back out would be cast to a type nothing built.
		if (t.type === 'tuple') {
			const cls = tupleArrayOwner([t]);
			if (cls)
				return cls.thisType;
		}
		if (t.type === 'ref' && t.typeArgs?.length) {
			const name = READONLY_ALIAS.get(t.name) ?? t.name;
			const decl = LIB_DECL_MAP.get(name) ?? userGenericClassDecls.get(name);
			if (decl?.type === 'class_decl' && decl.typeParams?.length) {
				const cls = ensureClass(name, t.typeArgs);
				if (cls)
					return cls.thisType;
			}
		}

		const resolved = T.resolve(global, t);
		switch (resolved.type) {
			// A type that RESOLVES to an array or tuple (an alias, an indexed access `N[K]`) is an `Array` like the `T[]` spelling
			// above -- falling through to `wasmTypeOf` gave it RAW storage, which nothing casts back to.
			case 'array': {
				const cls = ensureClass('Array', [resolved.element]);
				if (cls)
					return cls.thisType;
				break;
			}
			case 'tuple': {
				const cls = tupleArrayOwner([resolved]);
				if (cls)
					return cls.thisType;
				break;
			}
			case 'object': {
				const vt	= indexSignatureValueType(resolved);
				const cls	= vt && ensureClass('DynamicObject', [vt]);
				if (cls)
					return cls.thisType;
				// A NUMBER index signature (`ArrayLike<T>`) is met by arrays, strings, typed arrays and plain objects alike: no one layout.
				// Nor is `{}`, which holds any value but `null`/`undefined` (a truthy `unknown` narrows to it).
				if (!resolved.members.length || resolved.members.some(m => m.type === 'index' && m.paramType.type === 'ref' && m.paramType.name === 'number'))
					return W.REF_ANY;
				if (onlyCalls(resolved.members)) {
					const closure = callSignaturesWtype(resolved.members);
					if (closure)
						return closure;
				}
				break;
			}
			// An ARRAY carrying extra properties (`TemplateStringsArray`, `WithTextPos<T> = T & {pos}`, `interface RegExpMatchArray extends Array<string>`)
			// is physically just the array: the extras get no slot, so reading one is an honest `unknown field` rather than a wrong answer, and erasing them
			// keeps such a value assignable to a plain array parameter with no conversion, the way real TS subtyping already allows. Only the array part is
			// typed -- an ordinary `Array` -- so object parts never build (or register) anonymous shapes merely because someone asked whether they're
			// array-backed; falls through to the flatten-and-merge path below when no part is array-backed at all (an interface extending another
			// interface), or when two parts disagree on the element kind.
			case 'intersection': {
				const arr = arrayPartOf(resolved, global);
				if (arr)
					return typeOf(TS.ArrayType(arr.element));
				const prim = primitivePart(resolved, global);
				if (prim)
					return typeOf(prim);
				break;
			}
			case 'union': {
				const nonNullish = resolved.types.filter(m => !T.isNullish(m, global));
				if (nonNullish.length < resolved.types.length && nonNullish.length > 0) {
					const base = typeOf(nonNullish.length === 1 ? nonNullish[0] : TS.UnionType(nonNullish));
					if (!base)
						return undefined;
					// A number's box is the `f64` one whatever its compact form: `u8 | undefined` is boxed as `number | undefined` is.
					const number = (base === 'i32' || base === 'u32' || base === 'f32') && nonNullish.every(m => T.typeofName(m, global) === 'number');
					return types.nullable(number ? 'f64' : base);
				}
				// A real union of >=2 members (not the nullable-collapse case above): `unionStructOwners`/`ensureUnionFieldDispatch` own the separate
				// "which classes member-access can dispatch to" question, still scoped to struct-backed unions because `ref.test` needs a per-member target.
				// Here the question is only whether every member's representation collapses to the same `WasmType`: `IteratorResult<Y,R>.value` with `Y`/`R` both
				// `number` must stay a plain `f64`, not box as `any` just for having >1 syntactic member; genuinely differing members (class vs class, scalar vs
				// scalar, scalar vs struct/array, e.g. `Literal.value: string | number | boolean | null | TemplatePart[]`) box as `any`, like every other
				// "could be one of several shapes" value (an unconstrained generic, a caught exception).
				if (nonNullish.length > 1) {
					const memberWtypes = nonNullish.map(typeOf);
					// A member with no representation of its own (a nested union hitting this same case, or an unrepresentable shape) is trivially
					// "not the same physical type as everything else" -- still a reason to box as `any`, not to give up on the whole union.
					if (!memberWtypes.every((w): w is W.Type => w !== undefined))
						return W.REF_ANY;
					return W.combineUnion(memberWtypes);
				}
				break;
			}
			// A type predicate (`t is Foo`) is a checking-time refinement with no representation of its own: as a plain value it IS a boolean,
			// and an `asserts` one yields nothing at all -- exactly the reduction the checker applies at a call site whose result is used as a value.
			case 'predicate':
				return resolved.asserts ? 'void' : typeOf(T.BOOLEAN);

			case 'function': {
				const parts = closureSigParts(resolved);
				if (!parts)
					throw `a function type has an unsupported return type: '${resolved.returnType ? T.typeKey(resolved.returnType) : 'void'}' in '${T.typeKey(resolved)}'`;
				const { params, result, hasRest, defaults } = parts;
				// Not memoized by physical signature: `resolvedParams` carries this signature's own TS types, and an unannotated
				// closure parameter takes its type from them -- `(x?: Stmt) => boolean` and `(x?: Stmt[]) => boolean` share one physical shape.
				return closureWtype({ params, result, hasRest, defaults, resolvedParams: parts.resolvedParams, restElem: parts.restElem });
			}
		}
		if (t.type === 'ref') {
			const cls = ensureClassRef(t);
			if (cls)
				return cls.thisType;
		}
		// `ensureClass` never resolves a dotted ref (`TS.TypeParam`), and an interface `extends`ing another resolves to an intersection: both are
		// flattened through `resolveObjectType` to the shape `ownerFor` sees.
		const flat = resolved.type === 'object' ? resolved : resolved.type === 'intersection' ? T.resolveObjectType(resolved, global) : undefined;
		if (flat) {
			const shapeMatch = objectShapeOf(t, flat);
			if (shapeMatch)
				return shapeMatch.thisType;
		}
		return wasmTypeOf(t, global);
	}


	// A name held in a machine scalar reads as it, though its type's representation is wider (a small bigint's `i32`, not the limb array).
	function scalarBinding(e: Expr, ctx: FunctionContext): W.Type | undefined {
		const binding = e.type === 'identifier' ? ctx.resolvedWtype(e.name) : undefined;
		return W.scalarKind(binding) ? binding : undefined;
	}

	// The `WasmType` a value expression resolves to; `unwrapAs`, since the checker must see the real (post-`as`) expression.
	function wtypeOf(e: Expr, ctx: FunctionContext): W.Type | undefined {
		const unwrapped	= unwrapAs(e);
		const scalar	= scalarBinding(unwrapped, ctx);
		if (scalar)
			return scalar;
		// The slot's type before the narrowed one: narrowing never changes a slot's representation, which may still be nullable.
		// `narrowedTypeOf` fills in only where the slot has no answer (a read off a receiver narrowed out of `T | undefined`).
		const base		= ctx.physicalTypeOf(unwrapped);
		const w			= !T.isAny(base) ? typeOf(base) : undefined;
		// A local of one concrete class holds that class, though its type reads `any` (an opened type, a dispatcher's arm).
		const local		= unwrapped.type === 'identifier' && (!w || W.isAny(w)) ? ctx.lookup(unwrapped.name)?.wtype : undefined;
		if (W.isRef(local) && !W.isAny(local))
			return local;
		if (w)
			return w;
		// A narrowing to just null/undefined (`a = undefined`) says nothing about the slot, which is still `any`; `void` is not
		// one of those -- it is a real answer. A call that yields nothing (`u.forEach(...)`, whose receiver `ctx.scope` alone
		// sees as possibly-undefined, so `base` is `any`) must stay `void`, or the union dispatch that compiles it asks every
		// arm for a boxed value it never had.
		const narrowed = ctx.narrowedTypeOf(e);
		const isVoid   = T.isRef(T.resolveOwn(narrowed, ctx.scope), 'void');
		return typeOf(isVoid || !T.isNullish(narrowed, ctx.scope) ? narrowed : base);
	}




	// Every remaining value of an iterator, into a new array: what JS's `...` does with an iterable, and a rest pattern.
	function drainIterator(iterator: Expr, it: T.IterationTypes, ctx: FunctionContext): Expr {
		const arrName = `#iter$${ctx.tempCounter++}`, rName = `#iter$${ctx.tempCounter++}`;
		const arr: Expr = Identifier(arrName), r: Expr = Identifier(rName);
		emitStmt(JS.VarDecl('const', JS.Var(arrName, { type: 'array', elements: [] } as Expr, TS.ArrayType(it.yield))), ctx);
		emitStmt(JS.For(
			JS.VarDecl('let', JS.Var(rName, nextCall(iterator, it, ctx.scope))),
			JS.JSUnary('!', JS.Member(r, 'done')),
			Assign<Expr, never>(r, nextCall(iterator, it, ctx.scope)),
			{ type: 'expression' as const, expression: JS.Call(JS.Member(arr, 'push'), [JS.Member(r, 'value')]) },
		), ctx);
		return arr;
	}

	// A spread operand as an array: a non-array iterable's iterator drained into one, anything else as it is.
	function spreadSource(operand: Expr, ctx: FunctionContext): Expr {
		const it = iteratesByProtocol(operand, ctx);
		if (!it)
			return operand;
		const itName = `#iter$${ctx.tempCounter++}`;
		emitStmt(JS.VarDecl('const', JS.Var(itName, JS.Call(JS.Member(operand, '[Symbol.iterator]'), []))), ctx);
		return drainIterator(Identifier(itName), it, ctx);
	}

	// A destructuring pattern bound from `value` one level at a time: each level is materialized into a typed temp first, so
	// an array pattern indexes an array/tuple and iterates anything else, decided from that level's own type.
	function emitPatternBinding(kind: JS.DeclarationKind, target: BindingTarget, value: Expr, typeAnnotation: Type | undefined, ctx: FunctionContext): void {
		if (typeof target === 'string') {
			emitStmt(JS.VarDecl(kind, JS.Var(target, value, typeAnnotation)), ctx);
			return;
		}
		const temp = (): Expr => Identifier(`#destructure$${ctx.tempCounter++}`);
		const declare = (id: Expr, init: Expr, type?: Type) => emitStmt(JS.VarDecl('const', JS.Var((id as { name: string }).name, init, type)), ctx);
		const tmp = temp();
		declare(tmp, value, typeAnnotation);

		if (target.type === 'array_pattern') {
			const it = iteratesByProtocol(tmp, ctx);
			if (!it) {
				// A default applies where the element is `undefined`: past the end (the length guard -- reading past an array's end traps in
				// wasm), or present as `undefined` where the element type admits it. Never for `null`, which is a value JS keeps.
				target.elements.forEach((el, i) => {
					if (!el)
						return;
					const elem = JS.Index(tmp, Literal(i));
					emitPatternBinding(kind, el.target, el.default
						? Conditional<Expr>(
							Binary<Expr, '<'>('<', Literal(i), JS.Member(tmp, 'length')),
							readsPastEnd(elem, ctx)
								? Conditional<Expr>(Binary<Expr, '==='>('===', elem, Identifier('undefined')), el.default, elem)
								: elem,
							el.default)
						: elem, undefined, ctx);
				});
				if (target.rest)
					emitPatternBinding(kind, target.rest, JS.Call(JS.Member(tmp, 'slice'), [Literal(target.elements.length)]), undefined, ctx);
				return;
			}
			const iterator = temp();
			declare(iterator, JS.Call(JS.Member(tmp, '[Symbol.iterator]'), []));
			for (const el of target.elements) {
				const r = temp();
				declare(r, nextCall(iterator, it, ctx.scope));	// a hole still advances
				if (!el)
					continue;
				const got = JS.Member(r, 'value');
				emitPatternBinding(kind, el.target, el.default
					? Conditional<Expr>(JS.Member(r, 'done'), el.default, Binary('??', got, el.default))
					: got, el.default ? undefined : it.yield, ctx);
			}
			if (target.rest)
				emitPatternBinding(kind, target.rest, drainIterator(iterator, it, ctx), undefined, ctx);
			return;
		}

		if (target.rest)
			throw "a rest property ('...') in an object destructuring pattern is not supported";
		for (const prop of target.properties) {
			if (typeof prop.key === 'object')
				throw "a computed key ('[expr]') in an object destructuring pattern is not supported";
			const propExpr = JS.Member(tmp, String(prop.key));
			emitPatternBinding(kind, prop.value, prop.default ? Binary('??', propExpr, prop.default) : propExpr, undefined, ctx);
		}
	}

	// Type arguments for a `new C(...)` that spells none out. Nothing is inferred: the checker solves them from the constructor's
	// own arguments (`new Set(['a'])` answers `Set<string>`), and `ctx.contextualReturn` -- the same contextual channel
	// array/object literals already read -- carries the surrounding declaration's declared type, all a no-argument `new Map`
	// has to go on. Merged per position, solved winning and contextual filling an `any`, because for some real call site each is
	// the only one that knows. Learning nothing from either deliberately falls through to `ensureClass`'s own "needs N explicit
	// type argument(s)" throw rather than silently building an `any`-typed instance.
	function newTypeArgs(name: string, explicit: Type[] | undefined, e: Expr, ctx: FunctionContext, want?: W.Type): Type[] | undefined {
		if (explicit?.length)
			return explicit;
		// Headed for another instantiation of this same class (`Map<string, Ty>` from `[[k, lit]]`): build that
		// one. Two instantiations are two different structs, so the checker's narrower answer could never convert.
		const dest = W.isRef(want) ? classes.get(want.ref)?.thisTsType : undefined;
		if (dest?.type === 'ref' && dest.name === name && dest.typeArgs?.length)
			return dest.typeArgs;
		// Through a union, because an optional field's own read type is `C<...> | undefined` -- that still
		// contextually types a `new C` written into it.
		// An INFORMATIVE member first, not merely the first one: a ternary whose other arm is the real
		// `Set<Terminal>` types as `Set<any> | Set<Terminal>` (lalr.ts's `laForClosure`), and both arms have to be
		// one physical struct, so the member that names something is the one that decides. Same preference the
		// `pick` below already applies per argument.
		const argsFor = (t: Type | undefined): Type[] | undefined =>
			t?.type === 'union'	? (as => as.find(a => a && !a.every(T.isAny)) ?? as.find(a => a))(t.types.map(argsFor))
			:	t?.type === 'ref' && t.name === name ? t.typeArgs
			:	undefined;
		const solved		= argsFor(checkerTypeOf(e, ctx.scope));
		const contextual	= argsFor(ctx.contextualReturn);
		const merged: Type[] = [];
		for (let i = 0; i < Math.max(solved?.length ?? 0, contextual?.length ?? 0); i++) {
			const s = solved?.[i];
			const pick = s && !T.isAny(s) ? s : contextual?.[i] ?? s;
			if (!pick)
				return explicit;
			merged.push(pick);
		}
		return merged.length && !merged.every(t => T.isAny(t)) ? merged : explicit;
	}

	// A spread operand is read by the spread's copy, through its OWN type: the enclosing literal's context is not its reader's.
	function emitSpreadOperand(operand: Expr, ctx: FunctionContext, want: W.Type): W.Type {
		return ctx.withContext(ctx.narrowedTypeOf(operand), () => emitAs(operand, ctx, want));
	}

	// The keys a spread operand may provide: what its TYPE says a value carries -- of a union, any member's. Not a struct's field
	// list, which may hold more (an optional field the type lacks, an accessor's `#get:` companion) that no value ever supplies.
	function spreadKeys(operand: Expr, ctx: FunctionContext): string[] | undefined {
		const parts		= T.unionMembers(ctx.narrowedTypeOf(operand), ctx.scope).filter(m => !T.isNullish(m, ctx.scope));
		const members	= parts.flatMap(m => T.collectMembers(m, ctx.scope));
		return parts.every(m => ['object', 'intersection'].includes(T.resolveMembers(m, ctx.scope).type)) && !members.some(m => m.type === 'index')
			? [...new Set(members.flatMap(m => m.type === 'property' ? [T.memberKey(m.key)] : []))].filter((k): k is string => !!k)
			: undefined;
	}

	// `{...x, k: v}` where `x` is `any` (js-parser.ts's `{...decl, default: {...}}`, `decl` being `$[2]` off a
	// `WithTextPos<any[]>`): TS types the whole literal `any` too, so nothing here names a shape -- but the runtime CLASS
	// does, so this is the same `ref.test` cascade every other `any` dispatch is, in `ensureAnySpreadClone`.
	function emitAnySpreadClone(e: JS.ObjectExpr<Type>, ctx: FunctionContext): W.Type | undefined {
		const spreads	= e.properties.flatMap(p => p.type === 'spread' ? [p] : []);
		const written	= e.properties.flatMap(p => p.type === 'field' && typeof p.key !== 'object' && p.value ? [{ key: String(p.key), value: p.value }] : []);
		// The PHYSICAL type decides, not the written one: a genuinely `any` operand and one whose shape is OPEN
		// (`openShapes` -- it holds more than one layout, so it is stored as `any` too) are the same value here, and in
		// both the runtime class is the only thing that knows what to rebuild.
		const operand = spreads.length === 1 && typeOf(ctx.narrowedTypeOf(spreads[0].operand));
		if (!operand || !W.isAny(operand) || written.length + 1 !== e.properties.length)
			return undefined;
		// Every operand in WRITTEN order and each exactly once, as JS evaluates them -- the spread first only if it is written first.
		for (const p of e.properties) {
			if (p.type === 'spread')
				emitAs(p.operand, ctx, W.REF_ANY);
			else if (p.type === 'field' && p.value)
				emitAs(p.value, ctx, W.REF_ANY_NULLABLE);
		}
		// The arguments are on the stack in written order; the dispatcher declares them in that same order.
		ctx.emit(I.call(ensureAnySpreadClone(e.properties.map(p => p.type === 'spread' ? undefined : p.type === 'field' && typeof p.key !== 'object' ? String(p.key) : undefined)).funcIndex));
		return W.REF_ANY;
	}

	// One shared cloner per written-key list (`undefined` marks the spread's own position, so the parameter order matches the
	// call site's evaluation order). Each arm rebuilds the class the value turns out to be, with the written keys overridden and
	// every other field carried across -- which is what a spread means. Built on the LATE worklist: the candidate set is "every
	// class that can hold these keys", which only the finished `classes` map knows, exactly as `ensureAnyField` scans it.
	function ensureAnySpreadClone(slots: (string | undefined)[]): FuncInfo {
		return synthesize(`<any spread>.${slots.map(k => k ?? '...').join(',')}`, () => ({
			params: slots.map((k, i) => k === undefined ? anyParam('src') : anyParam(`val$${i}`, W.REF_ANY_NULLABLE)), result: W.REF_ANY,
		}), (dctx, locals, { result }) => {
			// Only a key written AFTER the spread overrides it -- one written before is what the spread overwrites, so it comes
			// off the source like any other field. Both are still evaluated at the call site, in written order, as JS does.
			const spreadAt	= slots.indexOf(undefined);
			const vals		= new Map(slots.flatMap((k, i) => k !== undefined && i > spreadAt ? [[k, locals[i]] as const] : []));
			const written	= slots.flatMap(k => k === undefined ? [] : [k]);
			// Only a STRUCT is rebuilt field by field: with no written key every class qualifies, a string's or array's storage too.
			const isStruct	= (t: wasm.SubType) => ('type' in t ? t.type : t).kind === 'struct';
			const owners	= distinctHeaps(dynamicReceivers(false).filter(({ cls }) => cls.typeIndex !== -1 && isStruct(types.get(cls.typeIndex)) && written.every(w => cls.fieldIndex.has(w))));
			if (!owners.length)
				throw `no reachable class can hold every key of '{...${written.map(w => `, ${w}`).join('')}}' -- a spread of an 'any' rebuilds the class the value turns out to be`;
			// A value of no candidate class cannot be rebuilt as one, and answering with some other shape would be worse than stopping.
			emitTypeCascade(dctx, locals[spreadAt], owners.map(({ heap, cls }) => ({ heap, emit: () => {
				const src = dctx.temp(`$spreadsrc$${heap}`, cls.thisWtype!);
				dctx.emit(I.local.set(src));
				for (const f of cls.fields) {
					const val = vals.get(f.name);
					if (val !== undefined) {
						dctx.emit(I.local.get(val));
						coerceTop(W.REF_ANY_NULLABLE, dctx, f.wtype);
					} else if (f.name.startsWith('#')) {
						// A spread copies VALUES, so an accessor companion never carries over -- the field's own read already called it.
						dctx.emitDefaultValue(f.wtype, types, toValType);
					} else {
						dctx.emit(I.local.get(src));
						emitFieldRead(cls, cls.fieldIndex.get(f.name)!, dctx);
					}
				}
				dctx.emit(I.struct.new(heap as number));
				coerceTop(cls.thisWtype!, dctx, result);
			} })), trap(dctx), result);
		});
	}

	// A literal whose SHAPE is a runtime fact: a spread of a union (`{ ...e }`, `e: Expr`), or a written discriminant
	// whose value is a union of literals (`{ type, ...sig }`, `type: 'call' | 'construct'`): the deciding value is
	// evaluated once, then pinned per arm (a typed local for the spread, the literal itself for the discriminant), so
	// ordinary shape matching picks that arm's struct -- only when every earlier property is effect-free, so reordering is safe.
	function emitUnionShapedLiteral(e: JS.ObjectExpr<Type>, ctx: FunctionContext, want: W.Type | undefined): W.Type | undefined {
		const pure = (x: Expr): boolean => x.type === 'literal' || x.type === 'identifier' || x.type === 'this' || (x.type === 'member' && pure(x.object));
		const result: W.Type = W.isAny(want) ? want : W.REF_ANY;
		// What `f` emits, as instructions, leaving the context's own buffer as it was.
		const capture = (f: () => void): wasm.Instr[] => {
			const outer = ctx.swapOut();
			f();
			return ctx.swapOut(outer);
		};
		interface Arm { test: () => void; build: () => void }
		// `otherwise`: the arm no test can pick -- a member stored as `any` (an open shape) has no struct to `ref.test` for.
		const cascade = ([arm, ...rest]: Arm[], otherwise?: () => void): wasm.Instr[] => arm
			? [...capture(arm.test), I.if(toValType(result), capture(arm.build), cascade(rest, otherwise))]
			: otherwise ? capture(otherwise) : [I.unreachable];
		const emitArms = (arms: Arm[], otherwise?: () => void) => {
			ctx.emit(...cascade(arms, otherwise));
			return result;
		};
		const withProp = (i: number, q: JS.ObjectExpr<Type>['properties'][number]) => ({ ...e, properties: e.properties.map((p, j) => j === i ? q : p) }) as Expr;
		for (const [i, p] of e.properties.entries()) {
			if (!e.properties.slice(0, i).every(q => q.type === 'spread' ? pure(q.operand) : q.type === 'field' && (!q.value || pure(q.value))))
				break;
			if (p.type === 'spread') {
				const members	= T.unionMembers(T.resolve(ctx.scope, ctx.narrowedTypeOf(p.operand)), ctx.scope).filter(m => !T.isNullish(m, ctx.scope));
				const owners	= members.map(m => ownerFor(m));
				// A member held as `any` (an OPEN shape) has no struct to test for, so it can only be the arm no other test picked:
				// one such member is the `else`, two are indistinguishable at run time.
				const openAt	= owners.findIndex(o => !o || o.typeIndex === -1);
				if (members.length < 2 || owners.filter(o => !o || o.typeIndex === -1).length > 1)
					continue;
				const n		= ctx.tempCounter++;
				const src	= ctx.declareLocal(`$usrc$${n}`, W.REF_ANY_NULLABLE);
				emitSpreadOperand(p.operand, ctx, W.REF_ANY_NULLABLE);
				ctx.emit(I.local.set(src.index));
				const buildArm = (k: number) => () => {
					const name	= `$uvar$${n}$${k}`, o = owners[k];
					ctx.emit(I.local.get(src.index), o ? I.ref.cast(o.typeIndex) : I.ref.as_non_null, I.local.set(ctx.declareValue(name, o?.thisWtype ?? W.REF_ANY, members[k]).index));
					coerceTop(emitExpr(withProp(i, JS.Spread(Identifier(name))), ctx), ctx, result);
				};
				return emitArms(members.flatMap((_, k) => k === openAt ? [] : [{
					test: () => ctx.emit(I.local.get(src.index), I.ref.test(owners[k]!.typeIndex)),
					build: buildArm(k),
				}]), openAt >= 0 ? buildArm(openAt) : undefined);
			}
			if (p.type === 'field' && p.value && typeof p.key !== 'object') {
				// Unwidened: the question is which LITERALS it can hold (`narrowedTypeOf` widens, for physical representation).
				const precise	= ctx.typeAt(unwrapAs(p.value), false);
				const values	= T.unionMembers(T.resolve(ctx.scope, precise), ctx.scope).map(m => T.resolveOwn(m, ctx.scope));
				// Each arm's discriminant as a real literal EXPRESSION. A literal type and a literal expression are
				// both `Common.Literal`, but a type carries `fresh`/`frozen` that only widening reads, and a template
				// literal's parts are TYPES -- which has no runtime value to compare, so it can't be an arm at all.
				const literals	= values.flatMap(v => v.type === 'literal' && !Array.isArray(v.value) ? [v.value] : []);
				if (values.length < 2 || literals.length !== values.length)
					continue;
				const name	= `$udisc$${ctx.tempCounter++}`;
				const wt	= wtypeOf(p.value, ctx) ?? W.REF_ANY;
				emitAs(p.value, ctx, wt);
				ctx.emit(I.local.set(ctx.declareValue(name, wt, precise).index));
				return emitArms(literals.map(lit => ({
					test: () => { emitAs(Binary<Expr, '==='>('===', Identifier(name), Literal(lit)), ctx, 'i32'); },
					build: () => coerceTop(emitExpr(withProp(i, { ...p, value: Literal(lit) }), ctx), ctx, result),
				})));
			}
		}
		return undefined;
	}

	// `{ ...t, returnType: r }`: a spread operand with ONE known shape that already has every key the literal provides
	// IS the literal's shape, as in TS. Every key, the other spreads' too: `{ ...m, ...extra }` is not `extra`'s shape.
	function spreadOwner(e: JS.ObjectExpr<Type>, ctx: FunctionContext): ClassInfo | undefined {
		const provided = e.properties.flatMap(p => p.type === 'spread' ? spreadKeys(p.operand, ctx) ?? [undefined] : [JS.keyName(p.key)]);
		return e.properties.flatMap(p => p.type === 'spread' ? [ownerOf(p.operand, ctx)] : [])
			.find(cls => cls && cls.typeIndex !== -1 && provided.every(k => k !== undefined && cls.fieldIndex.has(k)));
	}

	// Can a field declared `declared` hold a value already laid out as `t`? A `{key: string}` struct is no `Rest`, though assignable:
	// only the same layout, `any` either side, or an open field will do -- per union member, which one `anyref` sketch would hide.
	function holdsLayout(declared: Type, t: Type): boolean {
		const members = T.unionMembers(t, global).filter(m => !T.isNullish(m, global));
		if (members.length > 1)
			return members.every(m => holdsLayout(declared, m));
		// Compared as SLOTS: a field's own nullish part is not a layout, an alias resolves to what it names, and every array of
		// references is one physical array (`arr:any` is `arr:ref`).
		const sketch	= (x: Type) => layoutSketch(T.resolve(global, T.nonNullable(x, global)), global).replace(/arr:any/g, 'arr:ref');
		const want		= sketch(declared), got = sketch(t);
		return want === got || want === 'any' || got === 'any' || openShapes.has(openKey(declared, global));
	}

	// A bare object literal with no single resolvable target type (`case 'object'`'s own `want` doesn't name one class) -- a
	// last-resort structural match against every reachable, struct-backed class/object-shape (the same "every class ever
	// discovered" scan `findAnyDispatchCandidates` uses for method dispatch, just picking which shape a literal builds as).
	function matchObjectShape(e: JS.ObjectExpr<Type>, ctx: FunctionContext, anon = true): ClassInfo | undefined {
		// `props`: every key the literal PROVIDES, a spread's included: no class names this literal's target, so it is read
		// through its own type, and a struct lacking one of its keys would lose it. `explicit`: the fields actually WRITTEN.
		const props		= new Map<string, Expr>();
		const explicit	= new Set<string>();
		for (const p of e.properties) {
			if (p.type === 'spread') {
				const keys = spreadKeys(p.operand, ctx);
				if (!keys)
					return undefined;
				// Last source wins, in written order, as it does at runtime. A spread-sourced value is never
				// a literal, so such a key simply takes no part in the discriminant tiebreak below.
				for (const k of keys)
					props.set(k, p.operand);
				continue;
			}
			if (p.type !== 'field' || typeof p.key === 'object' || !p.value)
				return undefined;
			props.set(String(p.key), p.value);
			explicit.add(String(p.key));
		}
		// A candidate names every key given, leaves no required field unfilled, and its field types accept the values: a written one is built in its
		// field's context, a spread's already has a layout the field must hold. `new Set`: one class may be reachable under two keys.
		const fits = (cls: ClassInfo) => [...props].every(([k, value]) => {
			const declared = cls.fieldDeclaredType(k, global);
			if (!declared)
				return true;
			if (explicit.has(k))
				return T.isAssignable(checkerTypeOf(unwrapAs(value), ctx.scope), declared, ctx.scope);
			// Per member: a key only some members of a union carry has no common type to look up.
			return T.unionMembers(ctx.narrowedTypeOf(value), ctx.scope).every(m => {
				const got = T.lookupMember(m, k, ctx.scope);
				return !got || holdsLayout(declared, got);
			});
		});
		const candidates = [...new Set(classes.values())].filter(cls =>
			!!laidOut(cls) && !cls.anonymous && [...props.keys()].every(k => cls.fieldIndex.has(k)) && cls.fields.every(f => props.has(f.name) || f.optional) && fits(cls)
		);
		if (candidates.length === 1)
			return candidates[0];
		// No declared shape fits, or several do with nothing to decide and no context (`any` is none) to read it through: it is
		// read through its own type, so it is built as that type's owner (`objectShapeOf`, one answer per type) -- what every reader expects.
		const fallback = () => {
			if (!anon)
				return undefined;
			const resolved = T.resolve(ctx.scope, checkerTypeOf(e, ctx.scope));
			return resolved.type === 'object' && !indexSignatureValueType(resolved) ? objectShapeOf(resolved, resolved) : undefined;
		};
		if (candidates.length === 0)
			return fallback();

		const matches = candidates.filter(cls => [...props].every(([key, value]) => admitsLiterals(cls.fieldDeclaredType(key, global), writtenLiteral(value))));
		return matches.length === 1 ? matches[0] : matches.length === 0 || !ctx.contextualReturn || T.isAny(ctx.contextualReturn) ? fallback() : undefined;
	}

	// `matchObjectShape`'s type-level counterpart, used by `typeOf`'s 'object' case when a real object TYPE (not a
	// literal expression) needs a nominal class: e.g. a generic parameter's structural bound (`Record<string, any>`)
	// substituted with an interface-typed argument. `ensureClass`/`ownerFor` preserve name identity only for a `class`
	// ref, never a plain `interface` (a bare `T.resolve` fully expands it), so its name is gone; self-hosting
	// `walker.ts`'s `mapObject` hit exactly this (`local 'r' has an unsupported type`). Same exact-field-set-then-
	// literal-discriminant matching as the literal version above, but against declared field *types* not expression
	// *values*; ambiguous or partial cases (computed/non-string key, non-property member) return `undefined`, never a guess.
	// One answer per type for the whole compile: which classes exist changes as codegen proceeds, and a value built under
	// one answer is unconvertible to a later one (a local typed before `FunctionType` was built, read after it was).
	function matchObjectShapeByType(t: TS.ObjectType, orElse = () => indexSignatureValueType(t) ? undefined : ensureAnonObjectShape(t)): ClassInfo | undefined {
		const key	= T.typeKey(t);
		const found	= classes.get(key) ?? findObjectShapeByType(t, orElse);
		if (found)
			classes.set(key, found);
		return found;
	}

	// A struct still being BUILT has a placeholder type with no `final` yet, and its fields so far match shapes it is not.
	function laidOut(cls: ClassInfo) {
		const t = types.get(cls.typeIndex);
		return t && 'final' in t ? t : undefined;
	}

	// `orElse` answers when no declared shape has these members; an ambiguous match answers `undefined`.
	function findObjectShapeByType(t: TS.ObjectType, orElse: () => ClassInfo | undefined): ClassInfo | undefined {
		const props = new Map<string, Type>();
		for (const m of t.members) {
			if (m.type !== 'property' || typeof m.key === 'object')
				return undefined;
			props.set(String(m.key), m.typeAnnotation);
		}
		// See `matchObjectShape`'s own comment -- same optional-field-omission tolerance and the same `new Set` reason.
		// The field TYPES must agree too, not just their names: `NodeMap<Obj>`'s `values` is a mapper `(x: number[]) =>
		// number[]` where `Obj`'s own is `number[]`, and the literal was then built against the wrong one. Asked of the
		// CHECKER, never `typeOf`: this runs while a shape is being resolved, and `typeOf` builds shapes, so asking it
		// re-enters (ts-parser.ts's `CallSig` -> `Param[]` -> the recursive `Type` union did not terminate). A field
		// whose declared type is unknown to `fieldDeclaredType` is not judged. Nor may a member's layout differ from its field's (`holdsLayout`).
		// A required field needs a required member: `Partial<FunctionDecl>` is no `FunctionDecl`.
		const certain = new Set(t.members.flatMap(m => m.type === 'property' && !hasMod(m, 'optional') ? [T.memberKey(m.key)] : []));
		const candidates = [...new Set(classes.values())].filter(cls =>
			!!laidOut(cls) && !cls.anonymous && [...props.keys()].every(k => cls.fieldIndex.has(k)) && cls.fields.every(f => certain.has(f.name) || f.optional)
			&& [...props].every(([k, pt]) => { const declared = cls.fieldDeclaredType(k, global); return !declared || T.isAssignable(pt, declared, global) && holdsLayout(declared, pt); })
		);
		if (candidates.length === 1)
			return candidates[0];
		// No declared shape has this field set, or (below) every candidate's discriminant rules it out: the type is anonymous.
		if (candidates.length === 0)
			return orElse();

		const matches = candidates.filter(cls => [...props].every(([key, propType]) => admitsLiterals(cls.fieldDeclaredType(key, global), T.literalValues(propType))));
		return matches.length === 1 ? matches[0] : matches.length === 0 ? orElse() : undefined;
	}

	// Index syntax (`a[i]`, `a[i] = v`) calls a class's own INDEX accessor, `__get`/`__set`, never a real API of that name
	// (`Uint8Array.set(array, offset)`). An index-signature object is routed to `Map`, and indexes through its real `get`/`set`.
	function indexAccessor(cls: ClassInfo, receiver: Expr, kind: 'get' | 'set', ctx: FunctionContext): string | undefined {
		// Whether it EXISTS: an overloaded accessor (a typed array's `__set` for a number or a bigint) has no one signature until a call's arguments pick it.
		if (hasMethod(cls, `__${kind}`))
			return `__${kind}`;
		return indexSignatureValueType(T.resolve(ctx.scope, ctx.narrowedTypeOf(receiver))) && methodSig(cls, kind, ctx) ? kind : undefined;
	}

	// A read that may find nothing: the representation of its type, `T | undefined` -- a number's box is the `f64` one whatever the
	// getter's compact result (`u32`) -- else the getter's own result made nullable.
	function mayBeAbsent(e: Expr, got: W.Type, ctx: FunctionContext): W.Type {
		const w = typeOf(ctx.narrowedTypeOf(e));
		return w && W.isNullable(w) ? w : types.nullable(got);
	}

	// Whether `cls` has a method `name`, its own or inherited (as `ensureMethod` finds one).
	function hasMethod(cls: ClassInfo, name: string): boolean {
		return !!cls.inlineMethods?.has(name) || cls.methodDecls.has(name) || (!!cls.superClass && hasMethod(cls.superClass, name));
	}

	// A class read by POSITION, as JS's array-likes are: an index getter keyed by a number, and a real `length` (a field or
	// `get length`) -- not a keyed `get`, whose index signature makes any name, `length` too, look like a member.
	function isPositional(cls: ClassInfo, ctx: FunctionContext): boolean {
		const sig = methodSig(cls, '__get', ctx);
		const key = sig?.params[sig.params.length - 1];
		return key !== undefined && W.scalarKind(key) !== undefined
			&& (cls.fields.some(f => f.name === 'length') || !!methodSig(cls, accessorKey('get', 'length'), ctx));
	}

	// `cls.name`'s own method signature -- whether inline-asm or a plain declared method.
	function methodSig(cls: ClassInfo, name: string, ctx: FunctionContext): { params: W.Type[]; result: W.Type } | undefined {
		const inline = cls.inlineMethods?.get(name);
		if (inline) {
			const b = inline([], ctx);
			return { params: b.params, result: b.result };
		}
		return ensureMethod(cls, name, [], ctx);
	}

	// The constructor by which `cls` adopts raw storage: its overload taking exactly one parameter, a `RawArray` (`Array`'s
	// `constructor(d: RawArray<T>)`, a typed array's over an `ArrayBuffer`). Boxing raw storage into `cls` is a call to it.
	function adoptingDecl(cls: ClassInfo): { decl: MethodMember; storage: W.Type & { arr: W.ElementI } } | undefined {
		let found = adoptingDecls.get(cls);
		if (found === undefined) {
			found = null;
			for (const decl of cls.methodDecls.get('constructor') ?? []) {
				const w = decl.params.length === 1 && !decl.rest ? resolveParams(decl.params, cls.declScope ?? libGlobal)[0].wtype : undefined;
				if (W.isArr(w)) {
					found = { decl, storage: w };
					break;
				}
			}
			adoptingDecls.set(cls, found);
		}
		return found ?? undefined;
	}

	// The element kind of a value's STORAGE: the value IS storage, or its class adopts storage of that kind (`adoptingDecl`).
	function storageKindOf(w: W.Type | undefined): W.ElementI | undefined {
		if (W.isArr(w))
			return w.arr;
		const o = W.isRef(w) ? classes.get(w.ref) : undefined;
		return o && adoptingDecl(o)?.storage.arr;
	}

	// The ELEMENT representation of an array-ish value: a raw array (`RawArray`, string, `ArrayBuffer`) carries it in
	// its own wtype; an `Array<T>` is an ordinary class, so its element kind is a fact about its TYPE, not the stack struct -- see [[tison-type-vs-representation]].
	function elementKindOfType(t: Type | undefined, scope: Scope): W.ElementI | undefined {
		if (!t)
			return undefined;
		const r  = T.resolve(scope, t);
		const el = r.type === 'array' ? r.element
			: r.type === 'ref' && (r.name === 'Array' || r.name === 'ReadonlyArray' || r.name === 'RawArray') ? r.typeArgs?.[0]
			: undefined;
		return el ? W.elementKind(typeOf(el)) : undefined;
	}

	// The element kind an array-valued expression resolves to -- raw storage's own, else its `Array` type's -- or `undefined`.
	function arrayKindOf(e: Expr, ctx: FunctionContext): W.ElementI | undefined {
		const wt = wtypeOf(e, ctx);
		return storageKindOf(wt) ?? elementKindOfType(checkerTypeOf(e, ctx.scope), ctx.scope);
	}

	// `arrayKindOf` for a value about to be indexed into (`e[i]`). The ref-collapse below is DISABLED: an inner
	// array keeps its own declared kind (`x[0]` of `number[][]` is a real f64 array), and every read casts back down to it.
	function objectArrayKind(e: Expr, ctx: FunctionContext): W.ElementI | undefined {
		//if (e.type === 'index' && objectArrayKind(e.object, ctx) === 'ref')
		//	return 'ref';
		// `narrowedTypeOf`, not `arrayKindOf`'s plain `ctx.scope` view: a value NARROWED out of `T | undefined` still reads
		// as the whole union there, so a field off it comes back `any` with no array kind (`[...a.rights, ...b.rights]` after `a && b`).
		// A value STORED as `any` (an opened `u8[]`) holds whatever storage reached it, whatever its type's element says.
		const nt = ctx.narrowedTypeOf(e);
		const wt = typeOf(nt);
		return W.isAny(wt) ? undefined : storageKindOf(wt) ?? elementKindOfType(nt, ctx.scope);
	}

	// `ownerOf` for a value about to be indexed into (`e[i]`) via generic class-method dispatch (`Array<T>.get(i)`); the
	// Array-at-`any` override below is DISABLED, same reason as `objectArrayKind`'s: an inner array is a real `Array<number>`.
	// A value STORED as `any` has no statically bound members, whatever its checker type names -- an open shape
	// (`openShapes`), or a genuinely dynamic value; its members are reached by the runtime dispatchers instead.
	function physicallyAny(e: Expr, ctx: FunctionContext): boolean {
		return W.isAny(wtypeOf(e, ctx));
	}

	// Each argument of a call dispatched at run time, as its own representation: a bare `null`/`undefined` has none, so it goes as a null `any`.
	function emitDynamicArgs(args: Expr[], ctx: FunctionContext): W.Type[] {
		return args.map(a => T.isNullLiteral(a) ? emitAs(a, ctx, W.REF_ANY_NULLABLE) : emitExpr(a, ctx));
	}

	function dispatchesAsAny(recv: Expr, args: Expr[], ctx: FunctionContext): boolean {
		return (T.isAny(ctx.narrowedTypeOf(recv)) || physicallyAny(recv, ctx)) && !args.some(a => a.type === 'spread');
	}

	function classOfForIndexing(e: Expr, ctx: FunctionContext): ClassInfo | undefined {
		if (physicallyAny(e, ctx))
			return undefined;
		const cls = ownerOf(e, ctx);
		//if (cls?.decl.name === 'Array' && e.type === 'index' && objectArrayKind(e.object, ctx) === 'ref')
		//	return ensureClass('Array', [T.ANY]);
		// A union of array types (`string[] | never[]`) names no single class, but its members share ONE physical class --
		// dispatch through that one's own accessors. Members of genuinely different shapes are `any`, and dispatch below.
		const w = cls ? undefined : wtypeOf(e, ctx);
		return cls ?? (W.isRef(w) ? classes.get(w.ref) : undefined);
	}

	// The `WasmType`/`ClassInfo` a builtin-operator operand resolves to -- `wtypeOf`/`ownerOf` alone can't see an indexed read's element kind, so `numericPairWtype`/etc would silently fall back to `f64`.
	// The width a bigint op on machine-int operands runs at natively, nothing checked at run time; undefined leaves it to the magnitude
	// array. Arithmetic needs its result proven to fit a machine int, a comparison does not; a `u64` compares only with another.
	function nativeBigint(method: string | undefined, operands: { expr: Expr; wtype: W.Type | undefined }[], e: Expr, ctx: FunctionContext) {
		const kinds = operands.map(o => W.scalarKind(o.wtype));
		if (!method || !isNativeBigMethod(method) || kinds.some(k => !k) || operands.some(o => T.typeofName(ctx.narrowedTypeOf(o.expr), ctx.scope) !== 'bigint'))
			return undefined;
		const compare	= !BIG_ARITHMETIC.has(method);
		const unsigned	= kinds.some(k => k === 'u64');
		if (unsigned && (!compare || !kinds.every(k => k === 'u64')))
			return undefined;
		const result = compare ? 'i32' : typeOf(ctx.typeAt(e, false));
		if (result !== 'i32' && result !== 'i64')
			return undefined;
		const t = unsigned || (!compare && result === 'i64') || kinds.includes('i64') ? 'i64' : 'i32';
		return { method, t, unsigned, result: compare ? result : t } as const;
	}

	function emitNativeBigint(method: string | undefined, operands: { expr: Expr; wtype: W.Type | undefined }[], e: Expr, ctx: FunctionContext): W.Type | undefined {
		const n = nativeBigint(method, operands, e, ctx);
		if (!n)
			return undefined;
		const m = n.method;
		if (m === 'neg')
			ctx.emit(I[n.t](0));
		operands.forEach(o => emitAs(o.expr, ctx, n.unsigned ? 'u64' : n.t));
		ctx.emit(m === 'neg' ? I[n.t].sub
			: m === 'lt' || m === 'gt' || m === 'le' || m === 'ge' ? I[n.t][`${m}_${n.unsigned ? 'u' : 's'}`]
			: I[n.t][m]);
		return n.result;
	}

	function operandInfo(e: Expr, ctx: FunctionContext): OperandInfo {
		if (e.type === 'index') {
			// `owner` (for owner-based operator dispatch -- '+' on a string/bigint element, etc) is a TS-level identity
			// question, resolved through the checker; `wtype` must match what `case 'index'` leaves on the stack, in its
			// priority order: a class's own `get(i)` signature first (authoritative over the checker's width-blind element
			// type, e.g. plain `number` for `Uint8Array`'s transiently-`i32` reads), then a raw array's physical element
			// kind, and the checker's type last (a ref-kind element -- a class or `string` -- has no narrower physical kind).
			const t		= ctx.narrowedTypeOf(e);
			const owner	= T.isAny(t) ? undefined : ownerFor(t);

			const cls		= classOfForIndexing(e.object, ctx);
			const getter	= cls && indexAccessor(cls, e.object, 'get', ctx);
			const sig		= cls && getter && methodSig(cls, getter, ctx);
			if (sig)
				return { wtype: sig.result, owner };

			const kind = objectArrayKind(e.object, ctx);
			if (kind === 'f64' || kind === 'i32'/* || kind === 'u32'*/)
				return { wtype: kind, owner };
			if (!T.isAny(t))
				return { wtype: typeOf(t), owner };
		}
		const t		= ctx.narrowedTypeOf(e);
		const owner	= ownerFor(t);
		const [method, parts] = e.type === 'binary' ? [BINARY_OP_NAMES[e.operator as keyof typeof BINARY_OP_NAMES], [e.left, e.right]]
			: e.type === 'unary' && e.operator === '-' ? ['neg', [e.operand]] : [undefined, []];
		const operands	= method ? parts.map(x => ({ expr: x, wtype: operandInfo(x, ctx).wtype })) : [];
		const big		= nativeBigint(method, operands, e, ctx);
		if (big)
			return { wtype: big.result, owner };
		if (e.type === 'binary' && (e.operator === '+' || e.operator === '-' || e.operator === '*')) {
			const [l, r] = operands.map(o => o.wtype);
			// 32-bit arithmetic is what its own op emits: the width the checker proved, as `numericOpInline` picks it.
			if (isInt32(l) && isInt32(r))
				return { wtype: numericOpInline(BINARY_OP_NAMES[e.operator], l, r, ctx, typeOf(ctx.typeAt(e, false))).result, owner };
		}
		// A literal is emitted as a constant of any width, so its own value's range is its representation, not its widened type.
		return { wtype: scalarBinding(e, ctx) ?? typeOf(e.type === 'literal' ? ctx.typeAt(e, false) : t), owner };
	}

	// The `ClassInfo` a static `Type` dispatches method calls against -- derived directly from the `Type` itself, never by reverse-decoding an already-collapsed `WasmType`
	// A tuple is an `Array` over REF storage whatever its elements: its element is the union of every position when that is
	// ref-kind, else `any` (`[number, number]` would otherwise name `f64` storage). Asked of the element -- no class built to ask.
	function tupleArrayOwner(tuples: TS.Tuple[]): ClassInfo | undefined {
		const el = T.combineTypes(tuples.flatMap(tu => T.elementTypes(tu, global)));
		return ensureClass('Array', [rawElemKind(el, typeOf) === 'ref' ? el : T.ANY]);
	}

	function ownerFor(t: Type): ClassInfo | undefined {
		// An open shape is stored as `any` and may hold any layout, so nothing owns it statically.
		if (openShapes.size && openShapes.has(openKey(t, global)))
			return undefined;
		// Same fast path `wasmTypeOf` needs, for the same reason -- a hoisted `builtinTypes` name would
		// otherwise fully expand via its own `declScope` before reaching the `w.type === 'ref'` check below.
		if (t.type === 'ref') {
			const m = T.machineOf(t, global);
			if (m)
				return builtinTypeOwner(T.machineRange(m).base);
			if (builtinTypes.has(t.name))
				return builtinTypeOwner(t.name);
/*
			if (t.typeArgs?.length) {
				const decl = LIB_DECL_MAP.get(name) ?? userGenericClassDecls.get(name);
				if (decl?.type === 'class_decl' && decl.typeParams?.length)
					return ensureClass(name, t.typeArgs);
			}
*/

			// Try the raw, unresolved reference's own name directly (via `ensureClass`'s shallow, single-level
			// `resolveClassAlias` lookup and its own `classes` cache check) before `T.resolve`'s full expansion below: that
			// no longer just unwraps one alias level (`Uint8Array` -> `TypedArray<u8>`) -- for a name with *both* a real
			// class and a separate ambient `interface` (`TypedArray`, same dual-declaration pattern as `String`), it fully
			// expands and merges both into an `intersection` with no traceable class name/typeArgs at all. Safe
			// unconditionally: `ensureClass` returns `undefined`, no throw, for a name that's neither, so this falls through.
			const direct = ensureClassRef(t);
			if (direct)
				return direct;
		}
		// Widening only ever matters for a scalar/array/union/ref shape here (matching `wasmTypeOf`'s own reasoning) --
		// a real `'object'` shape must NOT be widened: `widenLiterals`'s recursive object case would widen every
		// member's declared type too, including a discriminant field (`{type:'static_block';...}`'s `type`) down to plain
		// `string`, corrupting the literal precision `matchObjectShapeByType`'s discriminant tiebreak needs to tell union members apart.
		// Nor is one that is a union's MEMBER: widened, `{type: 'as'} | {type: 'satisfies'}` became one `{type: string}` object.
		const resolvedForOwner = T.resolve(global, t);
		// `obj?.method(...)`'s receiver is nullable by construction -- strip `null`/`undefined` before
		// dispatching; there's no "owner of `null`", only "owner of the non-nullish part `?.` already guarded".
		// Before widening: widened, `{type: 'keyof'} | undefined`'s tag became `string` and matched another struct.
		const nonNullish = resolvedForOwner.type === 'union' ? T.nonNullable(resolvedForOwner, global) : resolvedForOwner;
		if (nonNullish !== resolvedForOwner)
			return ownerFor(nonNullish);
		const widenOwner = (x: Type): Type => x.type === 'object' ? x : x.type === 'union' ? T.combineTypes(x.types.map(widenOwner)) : T.widenLiterals(x, false, true);
		const w = widenOwner(resolvedForOwner);

		switch (w.type) {
			case 'union': {
				// A union of tuples (js-parser.ts `CallSigParams<T>`, a rest's type) is one `arr:ref` whichever member it is.
				const members = T.unionMembers(w, global).map(m => T.resolve(global, m));
				if (members.every(m => m.type === 'tuple'))
					return tupleArrayOwner(members as TS.Tuple[]);
				// Members all owned alike (`assignableOps | ''`, string literals behind an alias beside another): that owner.
				const owners = new Set(members.map(ownerFor));
				return owners.size === 1 ? [...owners][0] : undefined;
			}
			case 'array':
				// `T[]`/`Array<T>`/`ReadonlyArray<T>` all resolve to `Array`'s own methods -- `ReadonlyArray` has no
				// separate lib declaration, it's a checker-only "readonly view" of the same structural shape.
				return ensureClass('Array', [w.element]);
			case 'tuple':
				return tupleArrayOwner([w]);

			case 'ref': {
				const mutable = READONLY_ALIAS.get(w.name);
				if (mutable)
					return ensureClass(mutable, w.typeArgs);
				if (w.name === 'Array')
					return ensureClass('Array', w.typeArgs);
				// A plain lib class (or alias -- `resolveClassAlias`) not reached by the raw-`t.name` `ensureClass` try above,
				// e.g. a param typed `Uint8Array` with no earlier `new Uint8Array(...)` to have lazily populated `classes`.
				// Safe to call unconditionally: `ensureClass` returns `undefined`, no throw, for a name that's neither.
				// `w.typeArgs`, not just `w.name`: `global` now sees lib type aliases, so `T.resolve` can already expand a
				// bare alias (`Uint8Array` -> `TypedArray<u8>`), and a generic class needs them to resolve at all, same
				// as the `Array`/`ReadonlyArray` case just above.
				return builtinTypeOwner(w.name) ?? ensureClass(w.name, w.typeArgs);
			}

			case 'object': {
				const vt = indexSignatureValueType(w);
				if (vt)
					return ensureClass('DynamicObject', [vt]);
				// Genuinely last resort, same guard as `typeOf`'s own -- only reached once `t.type === 'ref'` had its shot
				// above (a plain class/interface ref, even one mid-construction resolving its own name, is *never* funneled
				// here: that early check returns first). A generic parameter's structural bound substituted with a real
				// interface-typed argument is the one case anonymous by construction (`matchObjectShapeByType`'s own
				// comment). ...and when nothing declared matches either, synthesize the shape -- the same last resort
				// `matchObjectShape` applies on the literal side, so a bare anonymous object (an inferred field, a spread
				// result) has an owner to read fields off.
				return objectShapeOf(t, w);
			}
			// An interface `extends`ing another (`Method<T> extends CallSig<T>`) resolves to an intersection, not an
			// 'object'; `resolveObjectType` flattens+merges it into the flat object `matchObjectShapeByType` expects.
			case 'intersection': {
				// See `arrayPartOf` -- an array carrying extra properties dispatches against `Array` itself.
				const arr = arrayPartOf(w, global);
				if (arr)
					return ensureClass('Array', [arr.element]);
				const prim = primitivePart(w, global);
				if (prim)
					return ownerFor(prim);
				const merged = T.resolveObjectType(w, global);
				return merged && objectShapeOf(t, merged);
			}
		}
		return undefined;
	}


	// An object literal assigned against a real union target (`const m: ClassMember = {type:'field', ...}`) must pick
	// the ONE member it represents first: `matchObjectShape` only scans already-*registered* classes (`classes`), so the
	// first literal of a shape (nothing yet built the interface's "official" struct via `ownerFor`) would build a
	// narrower anon struct from its written properties than `ownerFor` later builds -- the exact mismatch that makes
	// The context may BE this literal's shape, with no name of its own: a field's declared type, an unannotated arrow's inferred
	// return (`{ sig: { params, result }, typeIndex }`). Resolved by TYPE, which settles declared-vs-anonymous the same way a
	// named target does -- `matchObjectShape` cannot, since several declared shapes may carry the same field NAMES.
	function contextualShapeOwner(e: JS.ObjectExpr<Type>, ctx: FunctionContext): ClassInfo | undefined {
		const target	= ctx.contextualReturn && T.nonNullable(ctx.contextualReturn, ctx.scope);
		const shape		= target && T.resolveObjectType(target, ctx.scope);
		if (!shape || indexSignatureValueType(shape))
			return undefined;
		// Only where the context accounts for every key WRITTEN here: a literal carrying more than it declares (`{...}` into a
		// wider member, `Other` into `Sig`) is the shape that has them, not the context's. A spread's keys are its operand's.
		const declares = new Set(shape.members.flatMap(m => m.type === 'property' || m.type === 'method' ? JS.keyName(m.key) ?? [] : []));
		if (e.properties.some(p => p.type === 'spread' || typeof p.key === 'object' || !declares.has(String(p.key))))
			return undefined;
		// Its OWN shape where several declared ones share these field names: the context is anonymous, so that is what it says.
		return matchObjectShapeByType(shape) ?? ensureAnonObjectShape(shape);
	}

	// A literal whose CONTEXT is an index-signature type is the dynamic object `typeOf` routes one to (`DynamicObject<V>`). Read through
	// the context, not `want`: an optional parameter's `Record<...> | undefined` boxes to `any`, which names no shape at all.
	// So is an empty literal whose context names no layout (`any`, `unknown`, `{}`, `object`, none): any key it gets is added later.
	function contextualDynamicOwner(e: JS.ObjectExpr<Type>, ctx: FunctionContext): ClassInfo | undefined {
		const target	= ctx.contextualReturn && T.resolve(global, T.nonNullable(ctx.contextualReturn, ctx.scope));
		const value		= target && indexSignatureValueType(target) || (!e.properties.length && (!target || namesNoLayout(target)) ? T.ANY : undefined);
		return value ? ensureClass('DynamicObject', [value]) : undefined;
	}
	const namesNoLayout = (t: Type) => T.isAny(t) || t.type === 'ref' && t.name === 'object' || t.type === 'object' && !t.members.length;

	// The declared union member (`ctx.contextualReturn`) the literal's written discriminants pick, before any structural guess.
	function matchContextualUnionMember(e: JS.ObjectExpr<Type>, ctx: FunctionContext): ClassInfo | undefined {
		if (!ctx.contextualReturn)
			return undefined;
		const props = new Map<string, Expr>();
		for (const p of e.properties) {
			// A spread is never excess-checked (as in TS): only the fields written out must fit and discriminate.
			if (p.type === 'spread')
				continue;
			if (p.type !== 'field' || typeof p.key === 'object' || !p.value)
				return undefined;
			props.set(String(p.key), p.value);
		}
		// ...but it does supply required fields. Unknown keys may supply any: the context can't make `{ modifiers }` a `Method`.
		const spreads	= e.properties.flatMap(p => p.type === 'spread' ? [spreadKeys(p.operand, ctx)] : []);
		const supplied	= spreads.every(k => k) ? new Set([...props.keys(), ...spreads.flat()]) : undefined;
		// With nothing to discriminate by (no written field, no known key), only a context of ONE shape decides (`xs.push({})`).
		const shapes = T.objectShapes(ctx.contextualReturn, ctx.scope);
		if (!props.size && !supplied && shapes.length !== 1)
			return undefined;
		const matches = shapes.filter(({ objT }) => {
			const fieldNames = new Set(objT.members.flatMap(m => m.type === 'property' ? JS.keyName(m.key) ?? [] : []));
			// Excess-property style: the literal names no field this member doesn't declare, and a declared discriminant admits its value.
			const required = objT.members.flatMap(m => m.type === 'property' && !hasMod(m, 'optional') ? [T.memberKey(m.key)] : []);
			return [...props.keys()].every(k => fieldNames.has(k)) && (!supplied || required.every(k => supplied.has(k)))
				&& [...props].every(([key, value]) => admitsLiterals(objT.members.find((m): m is TS.TypeMember & { type: 'property' } => m.type === 'property' && m.key === key)?.typeAnnotation, writtenLiteral(value)));
		});
		const owners = matches.map(m => ownerFor(m.raw) ?? matchObjectShapeByType(m.objT));
		if (owners.length === 1)
			return owners[0];
		// Several fit (`{params, rest}` for `CallSig | Params`): the one that is a SUBTYPE of all the others is
		// acceptable to every consumer (`interface CallSig extends Params` makes its struct a `Params` too).
		return owners.find(o => o && owners.every(q => q && isSubclassOf(o.name, q.name)));
	}

	// A union's own members can themselves resolve to a further union (e.g. a re-exported cross-module alias like
	// `JS.ClassMember<T>`) -- `T.resolve` only ever expands a type's outermost level, never recursing into a union's own members
	// (`typeOf`'s own 'union' case does that recursion itself), and `ownerFor`'s union case only handles the nullable-collapse
	// shape -- a genuine multi-member union has no single owner, so this flattens to the concrete owners a multi-owner dispatch
	// caller (`ensureUnionFieldDispatch`) needs.
	function flattenOwners(t: Type, scope: Scope): ClassInfo[] | undefined {
		// `ownerFor(t)` is tried on the RAW member first -- its `t.type === 'ref'` fast path needs the real nominal ref (a real
		// class's own name/typeArgs/declScope), and pre-resolving would expand a real class to its bare structural shape and land
		// on `matchObjectShapeByType`'s anonymous-shape path instead of its real struct (a regression the `A | B` test catches).
		// Only after that fails does resolving reveal a nested union.
		const direct = ownerFor(t);
		if (direct)
			return [direct];
		const resolved = T.resolve(scope, t);
		if (resolved.type === 'union') {
			const parts = T.unionMembers(resolved, scope).filter(m => !T.isNullish(m, scope)).map(m => flattenOwners(m, scope));
			return parts.every((p): p is ClassInfo[] => !!p) ? parts.flat() : undefined;
		}
		return undefined;
	}

	// The union members a `u.m(...)` call could dispatch to: every member must be a struct-backed owner declaring a matching
	// `m` -- a partial answer would be a silent wrong dispatch, so anything less falls through to the caller's own error.
	// Deduped by `typeIndex`: several members can share one physical type, and a repeated `ref.test` arm is dead code.
	function unionMethodOwners(obj: Expr, name: string, args: Expr[], ctx: FunctionContext): ClassInfo[] | undefined {
		const t = T.resolve(ctx.scope, ctx.narrowedTypeOf(obj));
		if (t.type !== 'union')
			return undefined;
		const owners = T.unionMembers(t, ctx.scope).filter(m => !T.isNullish(m, ctx.scope))
			.flatMap(m => flattenOwners(m, ctx.scope) ?? [undefined]);
		if (owners.length < 2 || !owners.every(o => o && o.typeIndex !== -1 && methodSig(o, name, ctx)))
			return undefined;
		const seen = new Set<number>();
		return (owners as ClassInfo[]).filter(o => !seen.has(o.typeIndex) && (seen.add(o.typeIndex), true));
	}

	// A namespace-style reference (`Box.describe()`) never carries real type arguments, and real TS forbids a static member from
	// referencing its class's own type parameters (checker-enforced), so `T.ANY` uniformly fills each one rather than
	// `ensureClass`'s "needs N explicit type argument(s)" throw -- always `REF_ANY`, so even another member's type that happens
	// to mention the type param (the static member itself never does) still resolves without failing. `undefined` for a
	// non-generic class leaves `ensureClass(name)` exactly as it was.
	function staticTypeArgsFor(name: string): Type[] | undefined {
		const decl = LIB_DECL_MAP.get(name) ?? userGenericClassDecls.get(name);
		return decl?.type === 'class_decl' ? decl.typeParams?.map(() => T.ANY) : undefined;
	}

	// The owner for a *namespace-style* reference (`Math.sqrt`, `Array.alloc`) -- not a value expression, so
	// `ownerFor` (needs a checker `Type`) doesn't apply; `builtinTypeOwner` covers it directly.
	function namespaceOwner(name: string, ctx: FunctionContext) {
		// A self-referential call site (`X.method()`) can match either name a class goes by: a generic
		// instantiation's `name` is the composite cache key while `decl.name` stays plain `Array`; a typed-array alias's `decl.name` stays canonical `Uint8Array` while `name` is the real alias, e.g. `Int32Array`.
		// Up the SUPERCLASS chain too: an inherited body (a base constructor inlined into a subclass's, say)
		// names its own declaring class, which is a base of the one being compiled -- and that base's
		// INSTANTIATION is what its `$T` asm is keyed to. `class B extends TypedArray<u8>` compiling the base's
		// `TypedArray.elemSize()` otherwise reached the uninstantiated generic, whose `$T` has no argument to
		// switch on and silently picked `f64`: an i32 then boxed into an f64 slot, rejected only by the runtime.
		const self = (c: ClassInfo | undefined): ClassInfo | undefined =>
			!c ? undefined : c.decl.name === name || c.name === name ? c : self(c.superClass);
		return builtinTypeOwner(name) ?? self(ctx.owner) ?? ensureClass(name, staticTypeArgsFor(name));
	}

	// Field access stays `classOf`-only (arrays/scalars have no fields), but method-call dispatch is
	// otherwise identical across real classes, array kinds, and scalar box kinds -- all handled by `ownerFor` above.
	function ownerOf(e: Expr, ctx: FunctionContext) {
		const owner	= ownerFor(ctx.narrowedTypeOf(e));
		// A local holding the ERASED twin of the checker's layout (`var_decl`'s `erasedTwin`) is read through what it holds.
		const slot	= e.type === 'identifier' ? ctx.resolvedWtype(e.name) : undefined;
		return owner?.thisWtype && slot && erasedTwin(slot, owner.thisWtype) && W.isRef(slot) ? classes.get(slot.ref) : owner;
	}

	// Populated by the "index space" pass below, before any body is built -- a class ref's `WasmType`
	// only carries its *name*, but the binary format needs the struct's numeric type index.
	function toValType(w: W.Type): wasm.ValType {
		if (w === 'void')
			throw 'internal: void has no value representation';
		if (w === 'u32')
			return 'i32';
		if (w === 'u64')
			return 'i64';
		if (typeof w === 'string')
			return w;
		if ('ref' in w) {
			// `any`/`exn` are wasm's own abstract heap types (real strings, not type-section indices) --
			// resolve directly, not have `ensureClass` treat either as an unknown user class name.
			if (w.ref === 'any' || w.ref === 'exn')
				return { ref: w.ref, nullable: !!w.nullable };
			// Lazy like every other class use -- a not-yet-reached class still needs a real `typeIndex` now, not the stale `-1` `classes` seeded it with.
			const cls = ensureClass(w.ref);
			if (!cls)
				throw `internal: unresolved class '${w.ref}'`;
			return { ref: cls.typeIndex, nullable: !!w.nullable };
		}
		if ('closure' in w)
			return { ref: ensureClosureType(w.closure).structTypeIndex, nullable: !!w.nullable };
		if ('typeIndex' in w)
			return { ref: w.typeIndex, nullable: !!w.nullable };
		return { ref: types.array(w.arr), nullable: !!w.nullable };
	}

	// The heap type a `ref.null` needs -- just `toValType`'s `.ref`, unwrapped from the `wasm.ValType` shape.
	function heapTypeIndexOf(w: W.Type): wasm.HeapType {
		const vt = toValType(w);
		if (typeof vt === 'string' || !('ref' in vt))
			throw 'internal: expected a reference type';
		return vt.ref;
	}

	// ===================================================================
	//  Expression lowering -- every case leaves exactly one value on the stack
	// ===================================================================

	// `array.new_data`'s two `i32` operands are a byte offset and an *element* count into the module's one shared passive data
	// segment -- `intern`'s return value and `s.length` already match both. It is a CONSTANT expression, so each distinct string
	// is materialized once into a global rather than per evaluation: a literal in a loop allocated a fresh array every iteration.
	// Sharing one array is unobservable -- a JS string is a value, and `===` on strings compares contents (`String.eq`).
	function emitStringConst(s: string, ctx: FunctionContext): void {
		const offset	= data.intern(s);
		const name		= `#str$${offset}$${s.length}`;
		if (!globals.has(name))
			globals.set(name, { wtype: W.ARRAY.i16, index: globals.size, mut: true, stringData: { offset, length: s.length },
				initInstrs: [I.array.new_fixed(types.array('i16'), 0)] });
		ctx.emit(I.global.get(globals.get(name)!.index));
	}

	// Looked up by name against `classes` rather than taking `ClassInfo`s, since `coerceTop`'s callers only ever have the bare
	// `WasmType`'s own ref name. Every class named here is already resolved -- a value of a class ref type requires `ensureClass`.
	function isSubclassOf(subName: string, baseName: string): boolean {
		return classes.get(baseName)?.isBaseOf(classes.get(subName)) ?? false;
	}

	// Which box a value belongs in, by its LOGICAL type rather than its physical form: `i32` is this compiler's representation for
	// both a real `boolean` and a compact-integer `number`, and a `number` boxes as the `f64` box however narrowly it is held --
	// or a reader, which unboxes by the type it wants, casts to a box the value was never in. `canonicalOf` is the same rule.
	function boxesAsBoolean(e: Expr, ctx: FunctionContext): boolean {
		return ownerFor(ctx.typeAt(unwrapAs(e)))?.name === 'Boolean';
	}

	// `coerceTop` for a value whose EXPRESSION is known: `coerceTop` has only physical types, so it would box and unbox a compact
	// `i32` as a boolean. Every conversion of an emitted value into a wanted representation goes through here.
	function coerceValue(e: Expr, got: W.Type, ctx: FunctionContext, want: W.Type, adoptErased = false): W.Type {
		// A bigint's canonical `any` form is its magnitude array, never a number box: `typeof` tests the heap type, and a reader
		// unboxes by the type it wants. So a machine-int bigint widens before it is boxed -- the same canonical-form rule boxing
		// a compact `number` as the `f64` box follows.
		if (W.isAny(want) && typeof got === 'string' && T.typeofName(ctx.narrowedTypeOf(e), ctx.scope) === 'bigint') {
			const big = builtinTypes.get('bigint')!.wtype;
			coerceTop(got, ctx, big);
			got = big;
		}
		if ((want === 'i32' || want === 'u32') && W.isAny(got) && !boxesAsBoolean(e, ctx)) {
			coerceTop(got, ctx, 'f64');
			got = 'f64';
		}
		// A number's box is the `f64` one, whatever its compact form (`i32`, `u32`, `f32`).
		if ((got === 'i32' || got === 'u32' || got === 'f32') && W.isAny(want) && !boxesAsBoolean(e, ctx)) {
			coerceTop(got, ctx, 'f64');
			got = 'f64';
		}
		if (adoptErased && erasedTwin(got, want))
			return got;
		coerceTop(got, ctx, want);
		return want;
	}

	function libFuncIndex(name: string): number {
		const decl = LIB_DECL_MAP.get(name);
		if (decl?.type !== 'function_decl')
			throw `internal: no lib function '${name}'`;
		return ensureFunc(name, decl).funcIndex;
	}

	function coerceTop(got: W.Type, ctx: FunctionContext, want: W.Type): void {
		if (W.typeEq(got, want))
			return;
		// A callable object IS its closure (a wasm subtype), so it meets a function slot as that closure would.
		const callable = W.isClosure(want) ? callableOf(got) : undefined;
		if (callable)
			return coerceTop(callable, ctx, want);

		// Differing only in result, or having FEWER params than `want` declares, is ordinary JS/TS callback convention (`arr.map(x =>
		// x*2)` ignoring `index`/`array`) -- wrap rather than reject. A real incompatibility in a shared param position, or `got`
		// wanting MORE params than `want` offers, still falls through to the "cannot convert" throw. See `ensureClosureCoercionWrapper`.
		if (W.isClosure(got) && W.isClosure(want)) {
			// The same signature differing only in nullability is the same value, as for a ref or array below.
			if (W.typeEq({ ...got, nullable: false }, { ...want, nullable: false })) {
				if (got.nullable && !want.nullable)
					ctx.emit(I.ref.as_non_null);
				return;
			}
			const gotSig = closureSigOf(got), wantSig = closureSigOf(want);
			// A shared param may DIFFER, so long as adapting it is a reference narrowing the wrapper can do with a cast: `Array<T>`'s
			// methods compile at `T = any` for every non-scalar element (one physical `arr:ref` store for all of them), so a
			// callback declared `(x: string)` meets a `(x: any)` slot. Both sides must be REFERENCE types -- a scalar mismatch
			// (`f64` caller, `i32` callback) would silently truncate, which is worse than the error it replaces; scalar vs a
			// boxed `any` converts by (un)boxing in the wrapper.
			const paramFits = (p: W.Type, i: number) => W.typeEq(p, wantSig.params[i])
				|| (typeof p !== 'string' && typeof wantSig.params[i] !== 'string')
				|| (typeof p === 'string' && W.isAny(wantSig.params[i])) || (typeof wantSig.params[i] === 'string' && W.isAny(p));
			// MORE params than the slot offers still fits when the wrapper can supply every extra one: checker.ts passes
			// `narrowByDiscriminant(m: Type, depth = 6)` as a `(m: Type) => ...`, ordinary TS since a default makes its JS arity 1.
			if ((gotSig.params.length <= wantSig.params.length || gotSig.params.slice(wantSig.params.length).every((p, i) => {
				const d = gotSig.defaults?.[wantSig.params.length + i];
				return (!!d && isReemittableDefault(d)) || W.isNullable(p);
			})) && !!gotSig.hasRest === !!wantSig.hasRest
				&& gotSig.params.slice(0, wantSig.params.length).every(paramFits)) {
				const orig = ctx.temp(`$origClosure$${ctx.tempCounter++}`, got);
				ctx.emit(I.local.set(orig));
				const { info, wantStructTypeIndex, envTypeIndex } = ensureClosureCoercionWrapper(gotSig, wantSig);
				// The wrapper is the same JS function, so it keeps the original's `length`.
					ctx.emit(I.ref.func(info.funcIndex), I.local.get(orig), I.struct.new(envTypeIndex),
						I.local.get(orig), I.struct.get(types.closureBase(), CLOSURE_FIELDS.get('length')!), I.struct.new(wantStructTypeIndex));
				return;
			}
		}

		// A nullable primitive (`number | null`/`boolean | null`, boxed via `types.box`): into `any` it goes as-is (a box IS
		// an `anyref`, and one holding null must arrive as that null); for a bare scalar it is unboxed, trusting the checker
		// already required narrowing (the same `ref.as_non_null`-traps-on-null contract as for nullable objects). Reassigning
		// `got` lets every scalar-conversion branch below run as if it had been bare all along.
		const gotBox = W.unboxedPrimitive(got);
		if (gotBox) {
			if (W.isAny(want)) {
				if (W.isNullable(got) && !want.nullable)
					ctx.emit(I.ref.as_non_null);
				return;
			}
			ctx.emit(I.ref.as_non_null, I.struct.get(gotBox.typeIndex, 0));
			got = gotBox.kind;
			if (W.typeEq(got, want))
				return;
		}
		// `u32`/`i32` are the same physical wasm value -- `u32` only exists so `coerceTop` always knows which conversion direction
		// (`_s` vs `_u`) a value needs; `u64`/`i64` likewise. Checked after unboxing: a boxed `i32` meets a `u32` too.
		if ((got === 'u32' && want === 'i32') || (got === 'i32' && want === 'u32') || (got === 'u64' && want === 'i64') || (got === 'i64' && want === 'u64'))
			return;
		// The opposite direction: a bare scalar meeting a nullable-primitive consumer -- widen/convert
		// to the box's own kind first (recursing into this same function), then box it.
		const wantBox = W.unboxedPrimitive(want);
		if (wantBox && typeof got === 'string') {
			if (got !== wantBox.kind)
				coerceTop(got, ctx, wantBox.kind);
			ctx.emit(I.struct.new(wantBox.typeIndex));
			return;
		}

		// A bare scalar has no heap identity of its own -- unlike ref/array (already a valid `anyref`), a raw
		// `f64`/`i32` needs a real box (`types.box`) to occupy an `any` slot. `u32` reads as `i32` here, same as everywhere else.
		if ((got === 'f64' || got === 'i32' || got === 'u32') && W.isAny(want)) {
			ctx.emit(I.struct.new(types.box(got === 'f64' ? 'f64' : 'i32')));
			return;
		}

		if (typeof got !== 'string') {
			if (W.isAny(got)) {
				// Narrowing anyref down to a bare scalar (e.g. unboxing an async step function's own `#sent` param, boxed at its
				// trampoline via this same function's scalar->any branch above) -- unbox via the same box shape a scalar->any box
				// always uses (`types.box`), then widen/convert further via a recursive call when `want` isn't exactly that
				// box's own kind (e.g. an `i32` box read back as `u32`/`i64`).
				if (want === 'f64' || want === 'i32' || want === 'u32' || want === 'i64' || want === 'f32') {
					const boxKind = (want === 'f64' || want === 'f32') ? 'f64' : 'i32';
					ctx.emit(I.ref.cast(types.box(boxKind)), I.struct.get(types.box(boxKind), 0));
					if (boxKind !== want)
						coerceTop(boxKind, ctx, want);
					return;
				}
				// `want.nullable`, not the 1-arg default (non-nullable) -- casting a shared nullable `anyref` read into a nullable
				// target (e.g. a `(number | null)[]` element, stored as a shared nullable `anyref` slot) as non-nullable would
				// trap on a genuinely-null element instead of letting it be checked against `null`.
				if (typeof want !== 'string')
					ctx.emit(I.ref.cast(heapTypeIndexOf(want), !!want.nullable));
				return;
			}

			// The opposite direction: any concrete class ref or array/string value is already a valid `anyref` (structural
			// subtyping), so widening to `any` needs no instruction -- only `ref.as_non_null` if also narrowing nullability.
			// `W.isArr(got)` covers writing a string/array into a ref-kind slot the same way; `W.isClosure(got)` a closure's
			// `{code,env}` struct (e.g. storing one into a generic `Array<() => void>`'s `any`-typed backing slot).
			if ((W.isRef(got) || W.isArr(got) || W.isClosure(got)) && W.isAny(want)) {
				if (got.nullable && !want.nullable)
					ctx.emit(I.ref.as_non_null);
				return;
			}

		// Nullable<->non-null, same underlying ref/array kind -- or `got` a real subclass of `want` (`super.method()`'s receiver,
		// or any other upcast): wasm-GC struct subtyping (`ensureClass`'s own `supertypes`) already makes the value valid
		// wherever `want`'s ref type is declared -- only nullability may still need narrowing.
			if (typeof want !== 'string') {
				const gotKind	= W.isRef(got) ? got.ref : W.isArr(got) ? got.arr : undefined;
				const wantKind	= W.isRef(want) ? want.ref : W.isArr(want) ? want.arr : undefined;
				if (gotKind !== undefined && (gotKind === wantKind || (W.isRef(got) && wantKind !== undefined && isSubclassOf(gotKind, wantKind)))) {
					if (got.nullable && !want.nullable)
						ctx.emit(I.ref.as_non_null);
					return;
				}
				// The opposite direction, `want` a real subclass of `got`: a trusted downcast (a `this`-typed method's checker-inferred
				// return type is more specific than the shared, inherited method body can know). Unlike the free upcast above this needs
				// a real `ref.cast` -- the runtime value must actually be `want`'s type here, the same trust as any other narrowing cast.
				if (wantKind !== undefined && W.isRef(want) && gotKind !== undefined && isSubclassOf(wantKind, gotKind)) {
					ctx.emit(I.ref.cast(heapTypeIndexOf(want), !!want.nullable));
					return;
				}
			}
		}

		if (got === 'f64') {
			switch (want) {
				// Direct native saturating conversions -- not an `i64.trunc_sat_f64_s` + `i32.wrap_i64` detour: saturating to
				// i64's range then wrapping to i32 discards the saturation for any out-of-i32-range input (e.g. `+Infinity`
				// saturated to `i64::MAX` wraps to `-1`), defeating the point of a saturating conversion (never trapping, e.g.
				// on `0/0`). `NaN` saturates to `0` like JS's `ToInt32`; `±Infinity` gives `i32::MAX`/`MIN` where JS gives `0` --
				// the same accepted non-finite gap as a huge finite float, well-defined and non-trapping, not bit-perfect JS.
				case 'i32': ctx.emit(I.i32.trunc_sat_f64_s); return;
				case 'u32': ctx.emit(I.i32.trunc_sat_f64_u); return;
				case 'i64': ctx.emit(I.i64.trunc_sat_f64_s); return;
				case 'f32':	ctx.emit(I.f32.demote_f64); return;
			}
		}
		// Raw storage meeting a class that adopts it (`adoptingDecl`) -- `[1,2,3]` (physically `{arr:f64}`) where an `Array<number>` is
		// wanted -- is that class's own constructor call. A literal stays the cheap form and boxes only where a context needs the class.
		if (W.isArr(got) && W.isRef(want)) {
			const owner = classes.get(want.ref);
			const adopt = owner && adoptingDecl(owner);
			if (adopt && W.typeEq(adopt.storage, got)) {
				ctx.emit(I.call(ensureCtorDecl(owner!, adopt.decl).funcIndex));
				return;
			}
		}

		// A bigint (its limb array) to a NUMBER -- the mirror of `bigFromNumber` below: `6 > 5n` needs it, because a mixed comparison
		// dispatches on the LEFT operand, so a number on the left never reaches `BigInt.compare`.
		if (want === 'f64' && isBigLimbs(got)) {
			ctx.emit(I.call(libFuncIndex('bigToNumber')));
			return;
		}
		if (want === 'f64') {
			switch (got) {
				case 'i32':	ctx.emit(I.f64.convert_i32_s); return;
				case 'u32':	ctx.emit(I.f64.convert_i32_u); return;
				case 'i64': ctx.emit(I.f64.convert_i64_s); return;
				case 'u64': ctx.emit(I.f64.convert_i64_u); return;
				case 'f32':	ctx.emit(I.f64.promote_f32); return;
			}
		}
		if (want === 'f32') {
			switch (got) {
				case 'i32':	ctx.emit(I.f32.convert_i32_s); return;
				case 'u32':	ctx.emit(I.f32.convert_i32_u); return;
				case 'i64': ctx.emit(I.f32.convert_i64_s); return;
			}
		}

		if (want === 'i64') {
			switch (got) {
				case 'i32': ctx.emit(I.i64.extend_i32_s); return;
				case 'u32': ctx.emit(I.i64.extend_i32_u); return;
			}
		}
		// A bigint into a machine slot keeps the low bits of its two's complement, as a `BigInt64Array` element does. Only a range
		// the checker proved fits gives a bigint an `i32` slot.
		if (want === 'i32' && isBigLimbs(got)) {
			ctx.emit(I.i32.const(0), I.call(libFuncIndex('bigWord')));
			return;
		}
		if ((want === 'i64' || want === 'u64') && isBigLimbs(got)) {
			const word	= libFuncIndex('bigWord');
			const big	= ctx.temp('$big', got);
			ctx.emit(
				I.local.tee(big), I.i32.const(0), I.call(word), I.i64.extend_i32_u,
				I.local.get(big), I.i32.const(1), I.call(word), I.i64.extend_i32_u, I.i64.const(32n), I.i64.shl,
				I.i64.or
			);
			return;
		}
		// Must track `bigint`'s own physical representation (`builtinTypes.bigint.wtype`, currently `{arr:'u32'}`, see `lib/bigint.ts`),
		// not assume a fixed `{arr:'i32'}`. Nullability is ignored: a non-nullable `(ref array)` is already a subtype of the nullable slot.
		if (isBigLimbs(want)) {
			const array = I.array(types.array('i32'));

			// Limbs are two's complement, so an UNSIGNED value whose top bit is set takes one more, zero, limb for its sign.
			switch (got) {
				case 'i32':
					ctx.emit(array.new(1));
					return;
				case 'u32':
					ctx.emit(I.i32.const(0), array.new(2));
					return;
				case 'i64': case 'u64': {
					const tmp64 = ctx.temp('$tmp64', 'i64');
					ctx.emit(
						I.local.tee(tmp64),
						I.i64.const(0xffffffffn),
						I.i64.and,
						I.i32.wrap_i64,
						I.local.get(tmp64),
						I.i64.const(32n),
						I.i64.shr_u,
						I.i32.wrap_i64,
						...got === 'u64' ? [I.i32.const(0), array.new(3)] : [array.new(2)]
					);
					return;
				}
				case 'f32':
					ctx.emit(I.f64.promote_f32);
				// `bigFromNumber` (lib/bigint.ts) is the real, tested conversion, and calling it is the only way this stays in
				// step with the limb encoding it has to produce. A mixed `bigint`/`number` comparison -- legal TS, and what
				// `BigInt.toString`'s own `i > 0` loop depends on -- needs it.
					//fall through
				case 'f64':
					ctx.emit(I.call(libFuncIndex('bigFromNumber')));
					return;

			}
		}
		throw `internal: cannot convert ${W.typeKey(got)} to ${W.typeKey(want)}`;
	}

	// `coerceTop`, but for one arm of a union dispatch (`ensureUnionFieldDispatch`/`ensureUnionIndexDispatch`) whose overall
	// `result` boxes as `any` because its sibling arms genuinely differ (not this arm's own fault): every scalar arm must land
	// in the SAME canonical box kind (`f64`, `combineUnionWtypes`'s own comment), not its own narrower physical storage. A
	// caller unboxing a `number` result always assumes the `f64` box, so an arm boxing by its own kind would make its
	// `ref.cast` trap; widening every scalar arm to `f64` first (a cheap numeric conversion, not a box) keeps them consistent.
	function coerceUnionArm(got: W.Type, ctx: FunctionContext, result: W.Type): void {
		if (W.isAny(result) && !result.nullable && got !== 'f64' && W.scalarKind(got) !== undefined) {
			coerceTop(got, ctx, 'f64');
			got = 'f64';
		}
		coerceTop(got, ctx, result);
	}

	// `adoptErased`: a caller that stores what it gets (an unannotated local) takes a value read through an erased instantiation as it
	// was built (`erasedTwin`), there being no conversion to `want`'s precise layout. Returns what it left on the stack.
	function emitAs(e: Expr, ctx: FunctionContext, want: W.Type, adoptErased = false): W.Type {
		// `null`/`undefined` alone (`emitExpr` has no target type to pick a heap type from) is only legal into a nullable slot,
		// the same restriction `typeOf`'s union handling enforces -- except a non-nullable `any` target, which is what a real
		// `void`-typed param/field/local is boxed to (`void` only ever holds `undefined` in real TS), so assigning it there is
		// ordinary source: box the same placeholder `emitDefaultValue` would, rather than reject it.
		if (T.isNullLiteral(e)) {
			if (W.isAny(want) && !want.nullable)
				ctx.emit(I.f64.const(0), I.struct.new(types.box('f64')));
			else if (!W.isNullable(want))
				throw "'null'/'undefined' is only supported where a nullable object type (class/array/string) is expected";
			else
				ctx.emit(I.ref.null(heapTypeIndexOf(want)));

		} else {
			let got = emitExpr(e, ctx, want);
			// A raw array erased into a non-raw slot (`any`, a field, a `??=` default) is boxed first: read back, it is cast to an
			// `Array` class -- its OWN type's if that adopts this storage, else its context's, else (an array all the same) this storage's.
			// A slot that is itself such a class is what the literal was built AS: `coerceValue` boxes straight into it.
			if (W.isArr(got) && !W.isArr(want) && !(W.isRef(want) && storageKindOf(want) === got.arr)) {
				const k = got.arr;
				// An array's own class even where its type is an OPEN slot (stored as `any`): the value in that slot is still that class.
				const classOf = (t: Type) => (el => el ? ensureClass('Array', [el])?.thisType : typeOf(t))(T.arrayLikeElement(T.nonNullable(t, ctx.scope)));
				const owner = (t: Type | undefined) => { const w = t && classOf(t); return W.isRef(w) && storageKindOf(w) === k ? w : undefined; };
				const ownT = checkerTypeOf(unwrapAs(e), ctx.scope);
				const ownW = typeOf(ownT);
				const isArrayValue = W.isRef(ownW) && storageKindOf(ownW) !== undefined;
				const own = owner(ownT) ?? owner(ctx.contextualReturn)
					?? (isArrayValue && (k === 'ref' || k === 'f64') ? owner(TS.ArrayType(k === 'ref' ? T.ANY : T.NUMBER)) : undefined);
				if (own && !W.typeEq(own, want)) {
					coerceTop(got, ctx, own);
					got = own;
				}
			}
			// UNboxing from `any`, the mirror of the boxing rule just below: a number was boxed as `f64` whatever its compact
			// integer storage, a real `boolean` as `i32`, so the checker's own type picks which box this value is in.
			return coerceValue(e, got, ctx, want, adoptErased);
		}
		return want;
	}

	// A runtime TYPE TEST, not a string comparison -- no `typeof` string ever needs to exist. Leaves an `i32` on the stack;
	// returns false, emitting nothing, when the tag has neither a static answer nor a physical form, so the caller errors.
	function emitTypeofTest(operand: Expr, tag: string, ctx: FunctionContext): boolean {
		const t		= ctx.narrowedTypeOf(operand);
		const answer = (v: 0 | 1) => {
			emitDiscarded(operand, ctx);
			ctx.emit(I.i32.const(v));
			return true;
		};
		const known = T.typeofName(t, ctx.scope);
		if (known !== undefined)
			return answer(known === tag ? 1 : 0);

		// Nullable, but every NON-null inhabitant shares one tag: `'undefined'` asks exactly "is it null",
		// the matching tag asks exactly "is it not null", and any other tag can never hold.
		const r		= T.resolve(ctx.scope, t);
		const nnTag	= r.type === 'union' ? T.typeofName(TS.UnionType(r.types.filter(m => !T.isNullish(m, ctx.scope))), ctx.scope) : undefined;
		if (tag === 'undefined' || nnTag !== undefined) {
			if (nnTag !== undefined && nnTag !== tag && tag !== 'undefined')
				return answer(0);
			emitAs(operand, ctx, W.REF_ANY_NULLABLE);
			ctx.emit(I.ref.is_null);
			if (tag !== 'undefined')
				ctx.emit(I.i32.eqz);
			return true;
		}

		// Only a boxed `any` slot can carry a runtime test: two types sharing a physical form (`number` and `boolean` are both
		// `f64` here) are indistinguishable at runtime, so anything else would be a WRONG answer, not merely an unsupported one.
		const heap = types.heapType(tag) ?? builtinTypeOwner(tag)?.typeIndex;
		const w    = wtypeOf(operand, ctx);
		if (!W.isAny(w))
			return false;
		if (heap !== undefined) {
			emitAs(operand, ctx, W.REF_ANY_NULLABLE);
			ctx.emit(I.ref.test(heap));
			return true;
		}
		// `'object'` is the COMPLEMENT of the tags that have a physical form, so a plain OR of those tests answers it with no
		// branching (`guard()`'s own `typeof node === 'object'` is the shape). A null slot reads as `'undefined'` here, so JS's
		// `typeof null === 'object'` is deliberately not reproduced -- that value cannot be told from a real `undefined` either way.
		if (tag === 'object') {
			const tmp = ctx.temp(`$typeofobj$${ctx.tempCounter++}`, W.REF_ANY_NULLABLE);
			emitAs(operand, ctx, W.REF_ANY_NULLABLE);
			ctx.emit(I.local.set(tmp), I.local.get(tmp), I.ref.is_null);
			for (const h of [types.box('f64'), types.box('i32'), types.array('i16'), types.closureBase(), builtinTypeOwner('symbol')!.typeIndex])
				ctx.emit(I.local.get(tmp), I.ref.test(h), I.i32.or);
			ctx.emit(I.i32.eqz);
			return true;
		}
		return false;
	}

	// `typeof x` as a VALUE when its type allows several tags: the operand is held once, then each allowed tag is tested
	// (`emitTypeofTest`), `'object'` last and untested as the complement. `null` and `undefined` share one representation, so a
	// type admitting both cannot be answered.
	function emitTypeofValue(operand: Expr, ctx: FunctionContext): W.Type {
		const t			= ctx.narrowedTypeOf(operand);
		const members	= T.unionMembers(t, ctx.scope);
		const hasNull	= members.some(m => T.isLiteral(m, 'null') || T.isRef(m, 'null'));
		if (hasNull && members.some(m => T.isRef(m, 'undefined') || T.isRef(m, 'void')))
			throw `'typeof' of '${T.typeKey(t)}': null and undefined share one representation here, so a null slot cannot be told apart`;
		const ALL		= ['undefined', 'number', 'boolean', 'string', 'bigint', 'symbol', 'function', 'object'];
		const named		= members.map(m => T.isNullish(m, ctx.scope) ? (hasNull ? 'object' : 'undefined') : T.typeofName(m, ctx.scope));
		const tags		= named.some(n => n === undefined) ? ALL : ALL.filter(tag => named.includes(tag));
		const held		= `#typeof$${ctx.tempCounter++}`;
		emitStmt(JS.VarDecl('const', JS.Var(held, operand, t)), ctx);
		const id: Expr	= Identifier(held);
		const str		= typeOf(T.STRING)!;
		const cascade = (i: number): void => {
			const tag = tags[i];
			if (i === tags.length - 1) {
				emitAs(Literal(tag), ctx, str);
				return;
			}
			// A null slot is tested by `emitTypeofTest('undefined')`; its tag is the type's own null tag.
			if (!emitTypeofTest(id, tag === 'object' && hasNull ? 'undefined' : tag, ctx))
				throw `'typeof' of '${T.typeKey(t)}' cannot be told apart at run time (tag '${tag}')`;
			ctx.emitIf(toValType(str), () => emitAs(Literal(tag), ctx, str), () => cascade(i + 1));
		};
		cascade(0);
		return str;
	}

	function emitTruthy(e: Expr, ctx: FunctionContext): void {
		// In a CONDITION `a && b` only has to decide the branch -- both readings agree there -- so this keeps the cheap boolean
		// lowering rather than materialising the operand `case 'binary'` yields; neither side needs a representable value type.
		if (e.type === 'binary' && (e.operator === '&&' || e.operator === '||')) {
			emitTruthy(e.left, ctx);
			const isAnd	= e.operator === '&&';
			const test	= () => emitTruthy(e.right, ctx);
			ctx.emitIf('i32', isAnd ? test : () => ctx.emit(I.i32.const(1)), isAnd ? () => ctx.emit(I.i32.const(0)) : test);
			return;
		}
		emitTruthyOf(emitExpr(e, ctx), ctx.narrowedTypeOf(e), ctx);
	}

	function emitDiscarded(e: Expr, ctx: FunctionContext): void {
		if (emitExpr(e, ctx, 'void') !== 'void')
			ctx.emit(I.drop);
	}

	// `a && b`/`a || b`/`a ?? b` over a left already on the stack: `right` runs in the arm the operator hands over to, `keep` in the other.
	function emitShortCircuit(operator: '&&' | '||' | '??', leftWtype: W.Type, leftType: Type, wtype: W.Type, right: () => void, keep: (held: W.Local) => void, ctx: FunctionContext): void {
		const held = ctx.declareLocal(`$logic$${ctx.tempCounter++}`, leftWtype);
		ctx.emit(I.local.tee(held.index));
		if (operator === '??')
			ctx.emit(I.ref.is_null);
		else
			emitTruthyOf(leftWtype, leftType, ctx);
		const takesRight = operator !== '||';
		ctx.emitIf(toValType(wtype), takesRight ? right : () => keep(held), takesRight ? () => keep(held) : right);
	}

	// Split out of `emitTruthy` so `&&`/`||` can test their left operand after teeing it into a local -- re-emitting the
	// expression would evaluate its side effects twice. `got` is its physical type, `t` the checker's.
	function emitTruthyOf(gotIn: W.Type, t: Type, ctx: FunctionContext): void {
		let got = gotIn;
		// A boxed primitive (`number | undefined`, `boolean | null`) has no truthiness of its own -- unbox it and test the
		// underlying scalar. A NULLABLE one tests for null first and answers falsy, as JS does for an omitted optional parameter
		// (`r?: number`), which otherwise dereferenced the null box. Same shape the nullable-string case below uses.
		const box = W.unboxedPrimitive(got);
		if (box) {
			if (W.isNullable(got)) {
				const tmp = ctx.declareLocal(`$numtruthy$${ctx.tempCounter++}`, got);
				ctx.emit(I.local.tee(tmp.index), I.ref.is_null);
				ctx.emitIf('i32', () => ctx.emit(I.i32.const(0)), () => {
					ctx.emit(I.local.get(tmp.index));
					coerceTop(got, ctx, box.kind);
					emitTruthyOf(box.kind, t, ctx);
				});
				return;
			}
			coerceTop(got, ctx, box.kind);
			got = box.kind;
		}
		switch (got) {
			case 'u32':
			case 'i32': return;
			case 'u64':
				got = 'i64';
				//fallthrough
			case 'i64': ctx.emit(I[got](0), I[got].ne); return;
			// `abs(x) > 0`, not `x != 0`: NaN is FALSY in JS, but wasm's `ne` is true for an unordered compare, so a bare
			// `x != 0` called it truthy. `gt` is false for NaN and collapses `-0` correctly, needing no scratch local unlike
			// `x != 0 && x == x`.
			case 'f64':
			case 'f32': ctx.emit(I[got].abs, I[got](0), I[got].gt); return;
		}
		// A string is falsy when EMPTY, so it tests its own length rather than its reference. A nullable one
		// is falsy when null too, and `array.len` would trap there -- hence the null test first.
		if (T.isStringLike(t, ctx.scope) && W.isArr(got)) {
			if (got.nullable) {
				const tmp = ctx.declareLocal(`$strtruthy$${ctx.tempCounter++}`, got);
				ctx.emit(I.local.tee(tmp.index), I.ref.is_null);
				ctx.emitIf('i32',
					() => ctx.emit(I.i32.const(0)),
					() => ctx.emit(I.local.get(tmp.index), I.ref.as_non_null, I.array.len, I.i32.const(0), I.i32.ne));
			} else {
				ctx.emit(I.array.len, I.i32.const(0), I.i32.ne);
			}
			return;
		}
		// A real wasm ARRAY slot holds an array whatever the checker's type degraded to, and an array is truthy -- so this is a
		// null test too. `arr:i16` is the exception: a string shares that form and `''` is falsy, so it was handled above.
		if (W.isArr(got) && got.arr !== 'i16') {
			if (got.nullable)
				ctx.emit(I.ref.is_null, I.i32.eqz);
			else
				ctx.emit(I.drop, I.i32.const(1));
			return;
		}
		// A real object/array/closure reference is always truthy in JS -- only null/undefined isn't -- so this is exactly a null
		// test (a non-nullable one is unconditionally true, `drop`ping the value still evaluated for side effects). A boxed `any`
		// qualifies when the CHECKER's type says every non-null thing it can hold is an object (`alwaysTruthy`; `Stmt | undefined`
		// is the common case, the union's members differing physically, not a possible primitive), or `got` names a non-primitive
		// class (printer.ts's `!!expr.operator.match(...)`, typed `any` there).
		const refCls = W.isRef(got) && got.ref !== 'any' && got.ref !== 'exn' ? ensureClass(got.ref) : undefined;
		if (typeof got === 'object' && ((!('ref' in got && (got.ref === 'any' || got.ref === 'exn'))
				? !T.isAny(T.resolveOwn(t, ctx.scope))
				: T.alwaysTruthy(t, ctx.scope))
				|| (!!refCls && !['number', 'boolean', 'string', 'bigint'].some(k => builtinTypeOwner(k) === refCls)))) {
			if (got.nullable)
				ctx.emit(I.ref.is_null, I.i32.eqz);
			else
				ctx.emit(I.drop, I.i32.const(1));
			return;
		}
		// A genuinely dynamic `any` slot -- the checker's type rules nothing out, so decide it at runtime.
		if (W.isAny(got)) {
			ctx.emitAnyTruthy(got, types);
			return;
		}
		throw `'${T.typeKey(t)}' (${W.typeKey(got)}) cannot be used as a boolean condition`;
	}

	// `got` is `want`'s layout with reference fields erased to `any`: what a value read through an erased generic instantiation is.
	function erasedTwin(got: W.Type, want: W.Type): boolean {
		const g = W.isRef(got) ? classes.get(got.ref) : undefined;
		const w = W.isRef(want) ? classes.get(want.ref) : undefined;
		return !!g && !!w && g !== w && g.fields.length === w.fields.length
			&& g.fields.every((f, i) => f.name === w.fields[i].name && (W.typeEq(f.wtype, w.fields[i].wtype) || W.isAny(f.wtype)));
	}

	// `{...a, ...(c ? {k: v} : {}), ...}` is the literal either arm makes: `c ? {...a, k: v, ...} : {...a, ...}`, a spread of a plain literal
	// being its properties. What precedes the conditional is evaluated first, into temps, so each value is still read once and in order.
	function conditionalSpread(e: JS.ObjectExpr<Type>, ctx: FunctionContext): Expr | undefined {
		const picks = (p: JS.ObjectExpr<Type>['properties'][number]) => {
			const c = p.type === 'spread' ? unwrapAs(p.operand) : undefined;
			const a = c?.type === 'conditional' ? unwrapAs(c.consequent) : undefined, b = c?.type === 'conditional' ? unwrapAs(c.alternate) : undefined;
			return c?.type === 'conditional' && a?.type === 'object' && b?.type === 'object' ? { test: c.test, arms: [a.properties, b.properties] } : undefined;
		};
		const at = e.properties.findIndex(p => picks(p));
		if (at < 0)
			return undefined;
		const { test, arms } = picks(e.properties[at])!;
		const temp = (value: Expr): Expr => {
			const name = `#cspread$${ctx.tempCounter++}`;
			emitStmt(JS.VarDecl('const', JS.Var(name, value)), ctx);
			return Identifier(name);
		};
		const before = e.properties.slice(0, at).map(p => p.type === 'spread' ? { ...p, operand: temp(p.operand) }
			: p.type === 'field' && p.value ? { ...p, key: typeof p.key === 'object' ? { computed: temp(p.key.computed) } : p.key, value: temp(p.value) }
			: p);
		const [yes, no] = arms.map(props => ({ ...e, properties: [...before, ...props, ...e.properties.slice(at + 1)] }));
		return Conditional<Expr>(test, yes, no);
	}

	// `value`'s elements, read through its own `length` and index and converted to `want`, into new storage `typeIndex` left in
	// `dst`. Read where `value` is evaluated, so a later element of the same literal (`[...a, a.pop()]`) cannot change them.
	function copyElements(value: Expr, got: W.Type, ctx: FunctionContext, want: W.Type, typeIndex: number, dst: number): void {
		const n			= ctx.tempCounter++;
		const fromName	= `$spread$from$${n}`, atName = `$spread$at$${n}`;
		const from		= Identifier(fromName);
		const slot		= wtypeOf(value, ctx) ?? got;
		coerceTop(got, ctx, slot);
		ctx.emit(I.local.set(ctx.declareValue(fromName, slot, ctx.narrowedTypeOf(value)).index));
		const i = ctx.declareValue(atName, 'i32', T.NUMBER).index;
		emitAs(JS.Member(from, 'length'), ctx, 'i32');
		ctx.emit(I.array.new_default(typeIndex), I.local.set(dst), I.i32.const(0), I.local.set(i));
		ctx.emitLoop(() => {
			ctx.emit(I.local.get(i), I.local.get(dst), I.array.len, I.i32.ge_u, I.br_if(1), I.local.get(dst), I.local.get(i));
			emitAs(JS.Index(from, Identifier(atName)), ctx, want);
			ctx.emit(I.array.set(typeIndex), I.local.get(i), I.i32.const(1), I.i32.add, I.local.set(i), I.br(0));
		});
	}

	// `elementTsType` may name each position separately -- a TUPLE rest parameter's arguments.
	function emitArrayElements(elements: readonly (Expr | undefined)[], ctx: FunctionContext, want: W.Type, kind: W.ElementI, typeIndex: number, elementTsType?: Type | ((i: number) => Type | undefined)): void {
		const contextAt		= (el: Expr) => typeof elementTsType === 'function' ? elementTsType(elements.indexOf(el)) : elementTsType;
		const emitElement	= (el: Expr) => ctx.withContext(contextAt(el), () => emitAs(el, ctx, want));
		if (elements.some(el => el?.type === 'spread')) {
			// A `[...]` array literal with at least one spread element. Every element is evaluated exactly once, in source order, into a
			// scratch local (a spread into storage of the literal's own kind); the result is then allocated to the true total and filled.
			type Part = { spread: false; value: number } | { spread: true; src: number; len: number };
			const parts: Part[] = [];

			elements.forEach((el, i) => {
				if (!el) {
					ctx.emitDefaultValue(want, types, toValType);
					const value = ctx.temp(`$spread$elem$${i}`, want);
					ctx.emit(I.local.set(value));
					parts.push({ spread: false, value });
				} else if (el.type === 'spread') {
					const operand	= spreadSource(el.operand, ctx);
					const src		= ctx.temp(`$spread$src$${i}`, W.ARRAY[kind]);
					const len		= ctx.temp(`$spread$len$${i}`, 'i32');
					// Hint the operand's OWN representation, never the storage this literal wants: a hard consumer of the hint (a
					// conditional, whose arms must agree) would otherwise be asked for storage an `Array` arm cannot produce.
					const got		= emitExpr(operand, ctx, wtypeOf(operand, ctx) ?? W.ARRAY[kind]);
					if (W.isArr(got) && got.arr === kind) {
						coerceTop(got, ctx, W.ARRAY[kind]);
						ctx.emit(I.local.set(src));
					} else {
						copyElements(operand, got, ctx, want, typeIndex, src);
					}
					ctx.emit(I.local.get(src), I.array.len, I.local.set(len));
					parts.push({ spread: true, src, len });
				} else {
					emitElement(el);
					const value = ctx.temp(`$spread$elem$${i}`, want);
					ctx.emit(I.local.set(value));
					parts.push({ spread: false, value });
				}
			});

			ctx.emit(I.i32.const(parts.filter(p => !p.spread).length));
			for (const p of parts) {
				if (p.spread)
					ctx.emit(I.local.get(p.len), I.i32.add);
			}
			const dst		= ctx.temp('$spread$dst', W.ARRAY[kind]);
			const offset	= ctx.temp('$spread$offset', 'i32');
			ctx.emit(I.array.new_default(typeIndex), I.local.set(dst), I.i32.const(0), I.local.set(offset));

			for (const p of parts) {
				if (p.spread) {
					ctx.emit(
						I.local.get(dst), I.local.get(offset),
						I.local.get(p.src), I.i32.const(0), I.local.get(p.len),
						I.array.copy(typeIndex, typeIndex),
						I.local.get(offset), I.local.get(p.len), I.i32.add, I.local.set(offset)
					);
				} else {
					ctx.emit(
						I.local.get(dst), I.local.get(offset), I.local.get(p.value),
						I.array. set(typeIndex),
						I.local.get(offset), I.i32.const(1), I.i32.add, I.local.set(offset)
					);
				}
			}
			ctx.emit(I.local.get(dst));

		} else {
			for (const el of elements) {
				if (el)
					emitElement(el);
				else
					ctx.emitDefaultValue(want, types, toValType);
			}
			ctx.emit(I.array.new_fixed(typeIndex, elements.length));
		}
	}

	function emitInline(name: string, inline: Inline, args: Expr[], ctx: FunctionContext): W.Type {
		if (args.length !== inline.params.length)
			throw `'${name}' takes exactly ${inline.params.length} argument(s)`;
		args.forEach((a, i) => emitAs(a, ctx, inline.params[i]));
		ctx.emit(...inline.inline);
		return inline.result;
	}


	function emitCallArgs(label: string, params: W.Type[], defaults: (Expr | undefined)[] | undefined, hasRest: boolean, args: Expr[], ctx: FunctionContext, resolvedParams?: ResolvedParam[]): void {
		// A closure literal passed where the parameter is a UNION with a function member (`String.replace`'s
		// `string | ((substring: string, ...args: any[]) => string)`) must compile to THAT member's physical signature, not its own
		// parameter list -- the callee only calls it through the declared one, and the union's boxed `any` says nothing.
		const wantForArg = (i: number, a: Expr): W.Type => {
			const declared = resolvedParams?.[i]?.tsType;
			if (declared && (a.type === 'arrow' || a.type === 'function')) {
				const r = T.resolveOwn(declared, ctx.scope);
				const fn = r.type === 'union' ? r.types.find(t => T.resolveOwn(t, ctx.scope).type === 'function') : undefined;
				const wt = fn && typeOf(fn);
				if (W.isClosure(wt))
					return wt;
			}
			return params[i];
		};
		// JS applies a parameter's DEFAULT when the argument is `undefined`, so passing it explicitly is exactly the same as
		// omitting it -- `null` is a real value and does NOT trigger the default. Without this, an explicit
		// `resolve(scope, t, undefined, stopAtRef)` tried to emit `undefined` into the scalar slot `depth = 10` declares.
		const argOrDefault = (i: number, a: Expr): Expr => T.nullLiteralKind(a) === 'undefined' && defaults?.[i] ? defaults[i]! : a;
		// Each argument's parameter type is its context: a literal or generic call there builds what the callee reads.
		const emitArg = (i: number, a: Expr) => ctx.withContext(resolvedParams?.[i]?.tsType, () => { const arg = argOrDefault(i, a); return emitAs(arg, ctx, wantForArg(i, arg)); });
		if (!hasRest) {
			if (args.some(a => a.type === 'spread'))
				args = expandTupleSpreads(args, ctx);
			if (args.some(a => a.type === 'spread'))
				throw `'${label}' takes no rest parameter -- a spread argument has nowhere to expand into`;

			if (args.length !== params.length) {
				if (args.length > params.length || !defaults)
					throw `'${label}' takes exactly ${params.length} argument(s)`;
				const missing = defaults.slice(args.length);
				if (missing.some(d => !d))
					throw `'${label}' takes exactly ${params.length} argument(s)`;

				// A non-literal default must be reading an earlier parameter (the only other shape `isReemittableDefault` accepts), so bind
				// every argument into its own scratch local first, in declaration order: each default sees its earlier siblings' real
				// values once, matching JS's left-to-right evaluation rather than re-emitting an expression that could have a side effect.
				if (missing.some(d => !isReemittableDefault(d!))) {
					if (!resolvedParams)
						throw `internal: '${label}' has a non-literal default with no resolved parameter info`;
					const rename = new Map<string, string>();
					ctx.openScope();
					const locals = resolvedParams.map((p, i) => {
						const a = i < args.length ? args[i] : substituteEarlierParamRefs(missing[i - args.length]!, rename);
						emitAs(a, ctx, params[i]);
						const name = `$default$${ctx.tempCounter++}`;
						const local = ctx.declareLocal(name, params[i]);
						ctx.scope.addValue(name, p.tsType);
						ctx.emit(I.local.set(local.index));
						if (typeof p.key === 'string')
							rename.set(p.key, name);
						return local;
					});
					locals.forEach(local => ctx.emit(I.local.get(local.index)));
					ctx.closeScope();
					return;
				}

				args = [...args, ...missing as Expr[]];
			}
			args.forEach((a, i) => emitArg(i, a));
		} else {
			const fixedCount = params.length - 1;
			if (args.length < fixedCount)
				throw `'${label}' needs at least ${fixedCount} argument(s)`;
			const fixedArgs = args.slice(0, fixedCount);
			if (fixedArgs.some(a => a.type === 'spread'))
				throw `'${label}': a spread argument can only appear among the trailing rest arguments -- its length isn't known at compile time, so it can't fill a fixed parameter position`;
			fixedArgs.forEach((a, i) => emitArg(i, a));
			// The bundle is built as raw storage and then coerced to whatever the parameter actually is --
			// a `RawArray` takes it as-is, an `Array<T>` boxes it (`coerceTop`), and neither needs a branch here.
			const restArrWtype = params[fixedCount];
			const kind = storageKindOf(restArrWtype) ?? elementKindOfType(resolvedParams?.[fixedCount]?.tsType, ctx.scope);
			if (!kind)
				throw `internal: '${label}' rest param has a non-array type`;
			const restTs = resolvedParams?.[fixedCount]?.tsType;
			emitArrayElements(args.slice(fixedCount), ctx, elementValueType(kind), kind, types.array(kind), restTs && (k => T.restArgType(restTs, k, ctx.scope)));
			coerceTop(W.ARRAY[kind], ctx, restArrWtype);
		}
	}

	// A struct argument where the parameter is a DIFFERENT struct it does not subtype (`hasMod(e: {modifiers?: string[]})` given
	// a `Param`): TS accepts it structurally and no conversion exists between two unrelated structs, so the callee is compiled
	// once per concrete argument type, as a generic is. The same object goes in, not a copy.
	function ensureStructuralInstance(name: string, decl: FunctionDecl, args: Expr[], ctx: FunctionContext, homeModule: string): FuncInfo | undefined {
		const params = decl.body && structuralParams(decl.params, args, ctx);
		if (!params)
			return undefined;
		const key = structuralKey(name, params);
		return funcs.get(homeKey(homeModule, key)) ?? compileFunc(key, { ...decl, params }, homeModule, name);
	}

	// `declared` with each parameter whose argument is a different struct retyped as that argument; `undefined` when none is.
	function structuralParams(declared: JS.Param<Type>[], args: Expr[], ctx: FunctionContext): JS.Param<Type>[] | undefined {
		let changed = false;
		const params = declared.map((p, i) => {
			const arg = args[i];
			// A literal is built AS the parameter's type (its context), unless an array literal meets a type holding no array storage (an `Iterable`);
			// an index-signature parameter is a dynamic object read by key. Neither is a struct to specialize for.
			if (!arg || arg.type === 'spread' || arg.type === 'object' || !p.typeAnnotation || indexSignatureValueType(T.resolve(global, p.typeAnnotation)))
				return p;
			const want = typeOf(p.typeAnnotation);
			if (arg.type === 'array' && storageKindOf(want))
				return p;
			// A read of an open slot may be any storage of its type: an instance of its own takes it as it is.
			if (ctx.narrowedTypeOf(arg) === OPEN_SLOT && W.isRef(want) && !W.isAny(want)) {
				changed = true;
				return { ...p, typeAnnotation: OPEN_SLOT };
			}
			const got = wtypeOf(arg, ctx);
			if (!W.isRef(want) || !W.isRef(got) || (want.ref === got.ref && want.ref !== 'any') || isSubclassOf(got.ref, want.ref))
				return p;
			if (got.ref === 'any' && want.ref !== 'any')
				return p;
			// A union parameter is held as `any` whatever its members' structs: those decide, each the argument's must be one of the parameter's.
			if (want.ref === 'any') {
				const mine = flattenOwners(p.typeAnnotation, ctx.scope), theirs = flattenOwners(ctx.narrowedTypeOf(arg), ctx.scope);
				if (!mine || !theirs || theirs.every(o => mine.some(m => m.typeIndex === o.typeIndex || isSubclassOf(o.name, m.name))))
					return p;
			}
			changed = true;
			return { ...p, typeAnnotation: ctx.narrowedTypeOf(arg) };
		});
		return changed ? params : undefined;
	}


	type CallRecv	= { expr: Expr; optional: boolean };
	type Callee		=
		| { kind: 'asm'; asm: Expr & { type: 'call' } }
		| { kind: 'callMethod'; fn: Expr }
		| { kind: 'self'; name: string }
		| { kind: 'function'; name: string; home: string }
		| { kind: 'construct'; cls: ClassInfo; label: string; lowered: boolean }
		| { kind: 'intrinsic'; which: string; call: Expr & { type: 'call' } }
		| { kind: 'builtin'; name: string }
		| { kind: 'static'; owner: ClassInfo; name: string }
		| { kind: 'method'; owner: ClassInfo; name: string; recv: CallRecv; bypassVirtual?: boolean }
		| { kind: 'union'; owners: ClassInfo[]; name: string; recv: CallRecv }
		| { kind: 'dynamic'; name: string; recv: CallRecv }
		| { kind: 'closure'; wtype: W.ClosureType; optional: boolean }
		| { kind: 'anyValue' };

	function classifyCall(e: CallNode, ctx: FunctionContext, want?: W.Type): Callee {
		const callee = e.callee;
		if (e.type === 'new') {
			// A plain identifier naming a lib class (`Map`) has no `Scope.decl` for `classRefTarget` to follow.
			const target	= classRefTarget(callee, ctx.scope) ?? (callee.type === 'identifier' ? { name: callee.name, scope: ctx.scope } : undefined);
			const cls		= target && ensureClass(target.name, newTypeArgs(target.name, e.typeArgs, e, ctx, want), target.scope);
			if (!cls)
				throw `'new' is only supported for a known class`;
			return { kind: 'construct', cls, label: target.name, lowered: false };
		}
		if (callee.type === 'call' && isAsm(callee))
			return { kind: 'asm', asm: callee };
		if (callee.type === 'member' && callee.property === 'call' && !callee.optional && isFunctionTyped(callee.object, ctx))
			return { kind: 'callMethod', fn: callee.object };
		if (callee.type === 'identifier' && ctx.selfCall && ctx.name === callee.name)
			return { kind: 'self', name: callee.name };
		// A signature's origin travels with any value holding the function: only a callee that is no value binding is that function.
		const nsDecl	= callee.type === 'member' && callee.object.type === 'identifier' ? ctx.scope.namespace(callee.object.name)?.decl(callee.property) : undefined;
		const origin	= callee.type === 'identifier' || nsDecl ? callOf(e, ctx.scope)?.sig.origin : undefined;
		const direct	= callee.type === 'identifier' ? !ctx.resolvesName(callee.name) && !isModuleValue(callee.name, ctx)
			: nsDecl?.type === 'function_decl' || (nsDecl?.type === 'var_decl' && nsDecl.declarations.some(d => d.init === origin));
		const fn		= direct ? moduleFunctions.get(origin) : undefined;
		if (fn)
			return { kind: 'function', ...fn };
		if (callee.type === 'identifier') {
			const named = namedCallee(callee.name, e, ctx);
			if (named)
				return named;
		}
		if (callee.type === 'member' && !ctx.isNamespaceValue(callee)) {
			const { object: obj, property: name } = callee;
			const optional = isOptionalChainLink(callee);
			if (optional) {
				const w = wtypeOf(obj, ctx);
				if (!w || typeof w === 'string')
					throw `'a?.${name}(...)' needs an object-typed value on its left`;
			} else if (obj.type === 'super') {
				// Never virtual: the ancestor's own implementation, however far up it is declared.
				const superClass = (ctx.owner && 'fields' in ctx.owner ? ctx.owner as ClassInfo : undefined)?.superClass;
				if (!superClass)
					throw `'super.${name}(...)' has no superclass to resolve against`;
				return { kind: 'method', owner: superClass, name, recv: { expr: { type: 'this' }, optional }, bypassVirtual: true };
			} else if (obj.type === 'identifier') {
				const intrinsic = objectIntrinsic(e);
				if (intrinsic)
					return { kind: 'intrinsic', which: intrinsic, call: e };
				const owner = namespaceOwner(obj.name, ctx);
				if (owner)
					return { kind: 'static', owner, name };
				if (builtins.has(`${obj.name}.${name}`))
					return { kind: 'builtin', name: `${obj.name}.${name}` };
			}
			const recv	= { expr: obj, optional };
			const owner	= ownerOf(obj, ctx);
			if (owner)
				return { kind: 'method', owner, name, recv };
			const owners = unionMethodOwners(obj, name, e.arguments, ctx);
			if (owners)
				return { kind: 'union', owners, name, recv };
			if (dispatchesAsAny(obj, e.arguments, ctx))
				return { kind: 'dynamic', name, recv };
			throw `unknown method '${name}' (its receiver's type: '${T.typeKey(ctx.narrowedTypeOf(obj)).slice(0, 160)}')`;
		}
		// A local's own slot, not its checker type rebuilt: an unannotated parameter with a default has no representation of its own.
		const physical	= callee.type === 'identifier' && ctx.resolvesName(callee.name) ? ctx.resolvedWtype(callee.name) : wtypeOf(callee, ctx);
		const narrowed	= !closurePart(physical) && isFunctionTyped(callee, ctx) ? typeOf(ctx.narrowedTypeOf(callee)) : undefined;
		const closure	= closurePart(physical) ?? closurePart(narrowed);
		if (closure)
			return { kind: 'closure', wtype: closure, optional: !!e.optional };
		if ((T.isAny(ctx.narrowedTypeOf(callee)) || physicallyAny(callee, ctx)) && !e.arguments.some(a => a.type === 'spread'))
			return { kind: 'anyValue' };
		throw 'only direct calls to named functions, methods, or Math intrinsics are supported';
	}

	// What no module declares -- a builtin, a host import, a class -- is known by name alone.
	function namedCallee(name: string, e: CallNode, ctx: FunctionContext): Callee | undefined {
		const home = ctx.homeModule;
		if (ctx.resolvesName(name) || isModuleValue(name, ctx) || closurePart(lazyGlobalFor(name, ctx)?.wrapper.result))
			return undefined;
		if (builtins.has(name) || moduleAsmBuiltins.has(homeKey(home, name)) || funcs.has(name))
			return { kind: 'function', name, home };
		// A class is callable: its constructor is the conversion (`String(x)`).
		const cls = ensureClass(name, e.typeArgs, ctx.scope);
		return cls ? { kind: 'construct', cls, label: name, lowered: true } : { kind: 'function', name, home };
	}

	function emitCallee(c: Callee, e: CallNode, ctx: FunctionContext, want?: W.Type, callContext?: Type): W.Type {
		switch (c.kind) {
			case 'asm': {
				if (e.arguments.some(a => a.type === 'spread'))
					throw 'inline asm does not support spread call arguments';
				const owner = ctx.owner;
				try {
					const builtin = makeAsm(c.asm, { typeOf }, owner?.typeIndex ? { this: owner?.typeIndex } : {});
					return emitInline('<inline>', builtin(e.arguments.map(a => operandInfo(a, ctx)), ctx), e.arguments, ctx);
				} catch (err) {
					throw `inline asm failed to resolve ${err}`;
				}
			}
			case 'callMethod':
				return emitFunctionCallMethod(c.fn, e.arguments, ctx, want);
			case 'self': {
				const { funcIndex, params, result, hasRest } = ctx.selfCall!;
				ctx.emit(I.local.get(ctx.closureEnv!.envLocal.index));
				emitCallArgs(c.name, params, undefined, !!hasRest, e.arguments, ctx);
				ctx.emit(I.call(funcIndex));
				return result;
			}
			case 'function':
				return emitCall(c.name, e, ctx, callContext ?? (() => checkerTypeOf(e, ctx.scope)), c.home);
			case 'construct': {
				const ctor = ensureCtor(c.cls, c.lowered ? e.arguments : e, ctx);
				emitCallArgs(`${c.label}'s constructor`, ctor.params, ctor.defaults, !!ctor.hasRest, e.arguments, ctx, ctor.resolvedParams);
				ctx.emit(I.call(ctor.funcIndex));
				return c.cls.thisWtype!;
			}
			case 'intrinsic':
				return c.which === 'defineProperty' ? emitObjectDefineProperty(e.arguments, ctx)
					: c.which === 'assign' ? emitObjectAssign(c.call, ctx)
					// SameValue, decided at run time by typed lib code: an operand is often a boxed union value.
					: c.which === 'is' ? emitCall('__towasm_same_value', e.arguments, ctx)
					: emitObjectEntries(e.arguments, ctx, c.which as 'entries' | 'keys' | 'values');
			case 'builtin':
				return emitCall(c.name, e.arguments, ctx);
			case 'static':
				return emitMethodCall(c.owner, c.name, e, ctx);
			case 'method':
			case 'union':
			case 'dynamic': {
				const recv = c.recv.expr;
				if (c.recv.optional) {
					const w = wtypeOf(e, ctx);
					const [held, result] = c.kind === 'method'
						? [c.owner.thisWtype && typeof c.owner.thisWtype !== 'string' ? c.owner.thisWtype : wtypeOf(recv, ctx)!, ensureMethod(c.owner, c.name, e, ctx)?.result]
						: [W.REF_ANY, c.kind === 'union' ? w ?? want ?? W.REF_ANY : w && w !== 'void' ? w : W.REF_ANY];
					if (!result)
						throw `'a?.${c.name}(...)' is not supported -- only a plain user-defined method (not a 'Math'/prelude intrinsic) can be guarded by '?.' in this pass`;
					return emitGuardedCall(recv, held, result, want, push => emitReceiverCall(c, e, ctx, push, result === 'void' ? result : types.nullable(result)), ctx);
				}
				// A method that reassigns `this` writes its updated receiver back to where it came from, an lvalue.
				if (c.kind === 'method' && !c.bypassVirtual && ensureMethod(c.owner, c.name, e, ctx)?.reassignsThis)
					return ctx.inScope((): W.Type => {
						const target = emitAssignTarget(recv, ctx, 'keep');
						coerceTop(target.wtype, ctx, c.owner.thisWtype!);
						const result = emitMethodCall(c.owner, c.name, e, ctx);
						target.write(false);
						return result;
					});
				return emitReceiverCall(c, e, ctx, w => emitAs(recv, ctx, w), c.kind === 'union' ? wtypeOf(e, ctx) ?? want ?? W.REF_ANY : want ?? W.REF_ANY);
			}
			case 'closure': {
				const call = () => emitClosureCall(c.wtype, sourceArgs('<closure>', c.wtype, e.arguments, ctx), ctx);
				if (!c.optional || !c.wtype.nullable) {
					emitAs(e.callee, ctx, c.wtype);
					return call();
				}
				return emitGuardedCall(e.callee, c.wtype, closureSigOf(c.wtype).result, want, push => (push(c.wtype), call()), ctx);
			}
			case 'anyValue': {
				emitAs(e.callee, ctx, W.REF_ANY);
				const info = ensureAnyCallDispatch(emitDynamicArgs(e.arguments, ctx), want ?? W.REF_ANY);
				ctx.emit(I.call(info.funcIndex));
				return info.result;
			}
		}
	}

	// A union's members are dispatched inline, since the arguments are expressions here: re-emitted per arm, evaluated once.
	function emitReceiverCall(c: Callee & { kind: 'method' | 'union' | 'dynamic' }, e: CallNode, ctx: FunctionContext, push: (w: W.Type) => void, result: W.Type): W.Type {
		if (c.kind === 'method') {
			push(c.owner.thisWtype!);
			return emitMethodCall(c.owner, c.name, e, ctx, c.bypassVirtual);
		}
		if (c.kind === 'union') {
			const recv = ctx.declareLocal(`$udisp$${ctx.tempCounter++}`, W.REF_ANY_NULLABLE);
			push(W.REF_ANY_NULLABLE);
			ctx.emit(I.local.set(recv.index));
			emitTypeCascade(ctx, recv.index, c.owners.map(m => ({ heap: m.typeIndex, emit: () => coerceTop(emitMethodCall(m, c.name, e, ctx), ctx, result) })), trap(ctx), result);
			return result;
		}
		push(W.REF_ANY);
		const info = ensureAnyDispatch(c.name, emitDynamicArgs(e.arguments, ctx), e.arguments.map(a => ctx.narrowedTypeOf(a)), result, ctx);
		ctx.emit(I.call(info.funcIndex));
		return info.result;
	}

	// As a statement, a `?.` call builds no `undefined` for its skipped arm.
	function emitGuardedCall(recv: Expr, recvWtype: W.Type, result: W.Type, want: W.Type | undefined, call: (push: (w: W.Type) => void) => W.Type, ctx: FunctionContext): W.Type {
		const held = types.nullable(recvWtype);
		const push = (local: number) => (w: W.Type) => ctx.emit(I.local.get(local), ...W.typeEq(w, held) ? [] : [I.ref.as_non_null]);
		emitAs(recv, ctx, held);
		if (want === 'void') {
			const local = ctx.declareLocal(`$optcall$${ctx.tempCounter++}`, held);
			ctx.emit(I.local.tee(local.index), I.ref.is_null, I.i32.eqz);
			ctx.emitIf(undefined, () => {
				if (call(push(local.index)) !== 'void')
					ctx.emit(I.drop);
			});
			return 'void';
		}
		if (result === 'void')
			throw `a '?.' call whose callee returns 'void' can't become 'void | undefined'`;
		const resultWtype = types.nullable(result);
		return ctx.emitOptionalAccess(held, resultWtype, toValType, local => coerceTop(call(push(local)), ctx, resultWtype));
	}

	function emitCall(name: string, call: CallSite, ctx: FunctionContext, expected?: Expected, homeModule: string = ctx.homeModule): W.Type {
		const args = argsOf(call);
		let decl;
		const builtin = builtins.get(name) ?? moduleAsmBuiltins.get(homeKey(homeModule, name));
		if (builtin) {
			const result = builtin(args.map(a => operandInfo(a, ctx)), ctx);
			if ('inline' in result)
				return emitInline(name, result, args, ctx);
			// Only a binary operator's own `builtins` entry can resolve to a `MethodDelegate` -- a bare call
			// has no receiver, so getting one here is an internal inconsistency, not a user error.
			if ('owner' in result)
				throw `internal: '${name}' resolved to a method delegate outside operator dispatch`;

			decl = result;
		} else {
			decl = functionDeclByName.get(homeKey(homeModule, name));
			// A pre-seeded host import (`LIB_HOST_IMPORTS`) has no `FunctionDecl` to compile a body from -- a missing `decl` is only a real error when `funcs` doesn't already know the name either.
		}

		// A pre-seeded host import (`LIB_HOST_IMPORTS`) has no `FunctionDecl` and belongs to no module, so it is registered
		// under its BARE name, not `homeKey(homeModule, name)`; looking it up the latter way missed and `compileFunc` then crashed.
		const info = decl
			? (decl.typeParams?.length
				? ensureGenericFunc(name, decl, call, ctx, expected, homeModule)
				: ensureStructuralInstance(name, decl, args, ctx, homeModule) ?? ensureFunc(name, decl, homeModule))
			: funcs.get(name);
		if (!info)
			throw `call to unknown function '${name}'`;
		emitCallArgs(name, info.params, info.defaults, !!info.hasRest, args, ctx, info.resolvedParams);
		ctx.emit(I.call(info.funcIndex));
		return info.result;
	}

	// Dispatches a `receiver.name(...args)` call against any `ClassInfo` -- `inlineMethods` (checked first) splices its instructions into the caller with no `call`.
	// `receiver` is `undefined` for a namespace-style call (`Math.sqrt(x)`), where there is no real value to push, just a bare name used to look up `owner`.
	// `bypassVirtual` is set only by `super.method(...)`, which is by definition never virtual regardless of whether `owner` has overriding subclasses.
	function emitMethodCall(owner: ClassInfo, name: string, call: CallSite, ctx: FunctionContext, bypassVirtual?: boolean): W.Type {
		const args		= argsOf(call);
		const typeArgs	= typeArgsOf(call);
		const inline	= owner.inlineMethods?.get(name);
		if (inline) {
			if (args.some(a => a.type === 'spread'))
				throw 'spread call arguments are not supported';
			return emitInline(name, inline(args.map(a => operandInfo(a, ctx)), ctx, typeArgs), args, ctx);
		}

		// `owner.decl.name`, not `owner.name`: `hasDeclaredOverride` is keyed by the bare declared name, while a generic
		// instantiation's `owner.name` is a mangled composite -- which `ensureVirtualDispatch` doesn't support, so it never matches.
		const method = !bypassVirtual && !typeArgs && owner.decl.name && hasDeclaredOverride(owner.decl.name + moduleTag(stmtHomeModule.get(owner.decl)), name) ? ensureVirtualDispatch(owner, name, ctx)
			: ensureMethod(owner, name, call, ctx);
		if (!method) {
			// Not a declared method -- a closure-typed *field* called via member syntax ('this.step(v)') is a real, general
			// capability: read the field off the receiver already on the stack, then the same call_ref dance `case 'call'` does.
			const fieldIndex = owner.fieldIndex.get(name);
			const fieldClosure = closurePart(fieldIndex !== undefined ? owner.fields[fieldIndex].wtype : undefined);
			if (fieldClosure) {
				ctx.emit(I.struct.get(owner.typeIndex, fieldIndex!));
				return emitClosureCall(fieldClosure, sourceArgs(name, fieldClosure, args, ctx), ctx);
			}
			if (process.env.MDBG)
				console.error('MDBG', name, 'owner', owner.name, new Error().stack!.split('\n').slice(2, 8).join('\n'));
			throw `unknown method '${name}' on ${owner.name}`;
		}
		emitCallArgs(name, method.params, method.defaults, !!method.hasRest, args, ctx, method.resolvedParams);
		ctx.emit(I.call(method.funcIndex));
		return method.result;
	}

	// `Object.entries(x)` -- a known, fixed-identity global intrinsic (`declare var Object` in lib.d.ts), not a name to special-case
	// the way a user method would be: what fields exist depends on `x`'s concrete type, which only the compiler itself can see.
	// A `Map`-backed dynamic object already has a correct, efficient `entries()`, so this forwards to it; a struct that is statically
	// known and never subclassed reads `owner.fields` directly, and anything else needs `ensureAnyEntries`' own `ref.test` cascade.
	// `which` selects the projection: `entries`/`keys`/`values` differ only in what each element is, and `Map` implements all three by name.
	function emitObjectEntries(args: Expr[], ctx: FunctionContext, which: 'entries' | 'keys' | 'values' = 'entries'): W.Type {
		if (args.length !== 1)
			throw `'Object.${which}' takes exactly one argument`;
		const arg	= args[0];
		const owner = ownerOf(arg, ctx);
		// No static field list (`object`, a narrowed `unknown`), or a class whose instances may really be a subclass carrying more
		// fields -- either way only the RECEIVER'S RUNTIME TYPE answers this, so box and go through the `ref.test` cascade.
		if (!owner || (owner.decl.name && everExtended.has(owner.decl.name))) {
			emitAs(arg, ctx, W.REF_ANY);
			ctx.emit(I.call(ensureAnyEntries(which).funcIndex));
			return W.ARRAY.ref;
		}

		emitAs(arg, ctx, owner.thisWtype!);
		if (isDynamicObject(owner))
			return emitMethodCall(owner, which, [], ctx);
		return emitEntriesOf(owner, which, ctx);
	}

	// The projection itself, for a receiver whose concrete struct type is already known and on the stack: `owner.fields` is a
	// compile-time-known list, so this synthesizes a real array literal and hands it to the ordinary array-literal codegen.
	// Shared by the static path and every `ensureAnyEntries` arm, so the two cannot disagree about a class's entries.
	function emitEntriesOf(owner: ClassInfo, which: 'entries' | 'keys' | 'values', ctx: FunctionContext): W.Type {
		const objName	= `#objEntries$${ctx.tempCounter++}`;
		const objLocal	= ctx.declareValue(objName, owner.thisWtype!, owner.thisTsType!);
		ctx.emit(I.local.set(objLocal.index));

		// The outer array's own kind is always `ref` (a boxed tuple per field), known outright, so this calls `emitArrayElements`
		// directly rather than routing through `emitAs`/`arrayKindOf` inference. Each tuple element stays a real `Expr` so the usual
		// per-element coercion delegates back to `case 'array'`, reusing the logic every other array literal already relies on.
		if (which === 'keys') {
			emitArrayElements(owner.fields.map((f): Expr => Literal(f.name)), ctx, W.ARRAY.i16, 'ref', types.array('ref'));
			return W.ARRAY.ref;
		}
		const value = (f: { name: string }): Expr => JS.Member(Identifier(objName), f.name);
		emitArrayElements(owner.fields.map((f): Expr => which === 'values' ? value(f) : ({
			type: 'array',
			elements: [Literal(f.name), value(f)],
		})), ctx, W.REF_ANY_NULLABLE, 'ref', types.array('ref'));
		return W.ARRAY.ref;
	}

	// `Object.defineProperty(target, key, {value, ...})` -- a known global intrinsic (`isDefinePropertyCall`), checked the same way
	// `Object.entries` is. Only a plain value descriptor is supported, never a getter/setter: a struct field has no live-computation
	// concept, and `enumerable`/`configurable`/`writable` have no effect without general struct-field reflection. `target` must be a
	// plain local variable, because only then does `case 'var_decl'`'s extension redirect leave it a real slot to write into.
	function emitObjectDefineProperty(args: Expr[], ctx: FunctionContext): W.Type {
		if (args.length !== 3)
			throw "'Object.defineProperty' takes exactly 3 arguments";
		const [targetExpr, keyExpr, descExpr] = args;
		if (targetExpr.type !== 'identifier')
			throw "'Object.defineProperty': the target must be a plain local variable";
		if (keyExpr.type !== 'literal' || typeof keyExpr.value !== 'string')
			throw "'Object.defineProperty' needs a compile-time literal string key";
		const key = keyExpr.value;
		if (descExpr.type !== 'object')
			throw "'Object.defineProperty': the descriptor must be a literal object";
		// Data (`value`) or an accessor (`get`/`set`). An accessor's halves land in the key's `#get:`/`#set:` companions, which every
		// read and write consults first; a later DATA definition clears them, which is how a self-replacing lazy getter memoizes.
		const member	= (name: string) => descExpr.properties.find(p => (p.type === 'field' || p.type === 'method') && p.key === name);
		const valueProp	= member('value'), getProp = member('get'), setProp = member('set');
		const valueExpr	= valueProp?.type === 'field' ? valueProp.value : undefined;
		if (valueProp && !valueExpr)
			throw "'Object.defineProperty': a descriptor's `value` must be a plain property";
		if (!valueExpr && !getProp && !setProp)
			throw "'Object.defineProperty': the descriptor needs a `value`, a `get` or a `set`";
		if ([getProp, setProp].some(p => p?.type === 'method' && usesThis(p)))
			throw "'Object.defineProperty': an accessor method that uses `this` is not supported -- its `this` is the target, which a closure cannot bind";
		const emitHalf = (p: NonNullable<typeof getProp>, want: W.Type) => {
			if (p.type === 'method')
				coerceTop(emitClosureLiteral(p, ctx, false, want), ctx, want);
			else if (p.type === 'field' && p.value)
				emitAs(p.value, ctx, want);
			else
				throw "'Object.defineProperty': an accessor must be a function";
		};

		// The target's own *real, physical* class, not `ownerOf`'s checker-type-based resolution: `case 'var_decl'`'s extension
		// redirect changes what the identifier's wasm local physically is, which its checker-level TS type cannot express.
		// `resolvedWtype`, not `lookup`: the target may be CAPTURED by the closure this runs in, where it is a closure-env field.
		const wt     = ctx.resolvedWtype(targetExpr.name);
		const owner  = W.isRef(wt) ? ensureClass(wt.ref) : undefined;
		// An erased receiver (a generic's `T`, `any`): the key's slot is on whichever structs reach it (`collectReceivedExpandos`),
		// so the write dispatches on the runtime struct.
		if (!owner && W.isAny(wt)) {
			if (valueExpr) {
				emitAs(targetExpr, ctx, W.REF_ANY);
				emitAs(valueExpr, ctx, W.REF_ANY_NULLABLE);
				ctx.emit(I.call(ensureAnyFieldWrite(key).funcIndex));
			}
			for (const [half, p, w] of [['get', getProp, getterWtype()], ['set', setProp, setterWtype()]] as const)
				if (p) {
					emitAs(targetExpr, ctx, W.REF_ANY);
					emitHalf(p, w);
					coerceTop(w, ctx, W.REF_ANY_NULLABLE);
					ctx.emit(I.call(ensureAnyFieldWrite(`#${half}:${key}`).funcIndex));
				}
			return emitExpr(targetExpr, ctx);
		}
		if (!owner)
			throw `'Object.defineProperty': '${targetExpr.name}' needs a known class type`;

		const scratch = ctx.declareLocal(`$defineProperty$${ctx.tempCounter++}`, owner.thisWtype!);
		emitAs(targetExpr, ctx, owner.thisWtype!);
		ctx.emit(I.local.set(scratch.index));

		// An accessor sets both companions (a half not given is cleared, as JS makes it `undefined`); data clears whichever exist.
		for (const [half, p] of [['get', getProp], ['set', setProp]] as const) {
			const idx = owner.fieldIndex.get(`#${half}:${key}`);
			if (idx === undefined) {
				if (getProp || setProp)
					throw `internal: '${owner.name}' has no ${half}ter slot for '${key}' -- every accessor target should have been collected`;
				continue;
			}
			ctx.emit(I.local.get(scratch.index));
			if (p && !valueExpr)
				emitHalf(p, owner.fields[idx].wtype);
			else
				ctx.emitDefaultValue(owner.fields[idx].wtype, types, toValType);
			ctx.emit(I.struct.set(owner.typeIndex, idx));
		}
		if (!valueExpr) {
			ctx.emit(I.local.get(scratch.index));
			return owner.thisWtype!;
		}

		ctx.emit(I.local.get(scratch.index));
		const fieldIdx = owner.fieldIndex.get(key);
		if (fieldIdx !== undefined) {
			// Already a real declared field -- inherited from the base, or synthesized by `ensureClassExtension`: both are
			// ordinary struct fields by this point, no distinction needed.
			emitAs(valueExpr, ctx, owner.fields[fieldIdx].wtype);
			ctx.emit(I.struct.set(owner.typeIndex, fieldIdx));
		} else {
			// The catch-all `Map<string, any>` extension field -- lazily allocated (nullable) on first use, then a real `.set`,
			// the same dynamic-object write a structural index-signature target already uses.
			const extIdx = owner.fieldIndex.get('#ext');
			if (extIdx === undefined)
				throw `'Object.defineProperty': '${owner.name}' has no extension slot for '${key}' -- an internal inconsistency (every real defineProperty target should already have one)`;
			const mapCls = ensureClass('Map', [TS.RefType('string'), T.ANY]);
			if (!mapCls)
				throw `internal: 'Map' isn't available for '${owner.name}''s own dynamic extension`;
			ctx.emit(I.local.get(scratch.index), I.struct.get(owner.typeIndex, extIdx), I.ref.is_null);
			const _cond = ctx.swapOut();
			ctx.emit(I.local.get(scratch.index));
			const ctor = ensureCtor(mapCls, [], ctx);
			emitCallArgs(`${mapCls.name}'s constructor`, ctor.params, ctor.defaults, !!ctor.hasRest, [], ctx, ctor.resolvedParams);
			ctx.emit(I.call(ctor.funcIndex), I.struct.set(owner.typeIndex, extIdx));
			const _allocBranch = ctx.swapOut();
			ctx.emit(I.if(undefined, _cond, _allocBranch));
			ctx.emit(I.local.get(scratch.index), I.struct.get(owner.typeIndex, extIdx), I.ref.as_non_null);
			emitMethodCall(mapCls, 'set', [Literal(key), valueExpr], ctx);
			ctx.emit(I.drop);
		}
		ctx.emit(I.local.get(scratch.index));
		return owner.thisWtype!;
	}

	// `Object.assign(target, {k: v}, ...)` (`objectAssignCall`) IS the writes it performs, so it compiles as exactly those:
	// the target through a local, then an ordinary `t.k = v` per source key, then the local. Written out rather than emitted
	// here so accessors, expando slots, `#ext` and every coercion stay the assignment path's own, in one place.
	function emitObjectAssign(e: JS.Call<Type>, ctx: FunctionContext): W.Type {
		const call = objectAssignCall(e);
		if (!call)
			throw "'Object.assign' needs a target and sources that write their keys out (`{k: v}`) -- a source whose keys are only known at run time is not supported";
		const target	= call.target;
		const tsType	= ctx.narrowedTypeOf(target);
		const wtype		= typeOf(tsType);
		if (W.isClosure(wtype)) {
			const result	= typeOf(ctx.typeAt(e));
			const cls		= W.isRef(result) ? classes.get(result.ref) : undefined;
			if (!cls?.callable)
				throw `'Object.assign' onto a function: '${T.typeKey(ctx.typeAt(e))}' is no callable object`;
			return emitCallableObject(cls, target, call.writes, ctx);
		}
		if (!W.isRef(wtype))
			throw `'Object.assign': '${T.typeKey(tsType)}' is not an object to assign onto`;
		const name	= `$assign$${ctx.tempCounter++}`;
		const local	= ctx.declareValue(name, wtype, tsType);
		emitAs(target, ctx, wtype);
		ctx.emit(I.local.set(local.index));
		for (const w of call.writes) {
			const slot: Expr = Member(Identifier(name), w.key);
			emitDiscarded(Assign(slot, w.value), ctx);
		}
		ctx.emit(I.local.get(local.index));
		return wtype;
	}

	// A function given its properties where it is made (`Object.assign(fn, {k: v})`, a literal typed as a callable object) is built as one
	// callable object: a struct cannot gain fields later. `fn` and each value run in written order, then fill the struct in its layout's.
	function emitCallableObject(cls: ClassInfo, fn: Expr, writes: { key: string; value: Expr }[], ctx: FunctionContext): W.Type {
		const callable = cls.callable!;
		const { structTypeIndex } = ensureClosureType(callable.closure);
		const held = ctx.temp(`$fn$${ctx.tempCounter++}`, callable);
		if (fn.type === 'arrow' || fn.type === 'function')
			emitClosureLiteral(fn, ctx, false, callable);
		else
			emitAs(fn, ctx, callable);
		ctx.emit(I.local.set(held));
		const values = new Map(writes.map(w => {
			const field = cls.fields[cls.fieldIndex.get(w.key) ?? -1];
			if (!field)
				throw `unknown field '${w.key}'`;
			const local = ctx.temp(`$field$${ctx.tempCounter++}`, field.wtype);
			emitAs(w.value, ctx, field.wtype);
			ctx.emit(I.local.set(local));
			return [w.key, local];
		}));
		for (let i = 0; i < W.CALLABLE_PREFIX; i++)
			ctx.emit(I.local.get(held), I.struct.get(structTypeIndex, i));
		for (const f of cls.fields.slice(W.CALLABLE_PREFIX)) {
			const local = values.get(f.name);
			if (local !== undefined)
				ctx.emit(I.local.get(local));
			else
				ctx.emitDefaultValue(f.wtype, types, toValType);
		}
		ctx.emit(I.struct.new(cls.typeIndex));
		return cls.thisType;
	}

	// Operands (a receiver, an index) are emitted at a representation their `emit` is given; `load` makes the value, `store` takes it above them.
	// No `store`: read-only. `tee` stores and keeps the value where cheaper; `bounded` reads an element past the end as absent.
	interface Operand { wtype: W.Type; emit(w: W.Type): void }
	interface Place { wtype: W.Type; operands: Operand[]; load(): void; store?(): void; tee?(): void; bounded?(resultWtype: W.Type): void }

	// One classification for reads and writes, so the two cannot drift; a kind whose type differs by direction (getter vs setter) picks by `write`.
	function resolvePlace(target: Expr, ctx: FunctionContext, write = false): Place | undefined {
		// The value into a named local, for a store that calls a method with it; a chainable result (`Map.set`'s `this`) is dropped.
		const storeByCall = (wtype: W.Type, call: (name: string) => W.Type) => () => {
			const name = `$new$${ctx.tempCounter++}`;
			ctx.emit(I.local.set(ctx.temp(name, wtype)));
			if (call(name) !== 'void')
				ctx.emit(I.drop);
		};
		const fixed	= (wtype: W.Type, emit: () => void): Operand => ({ wtype, emit });
		const expr	= (e: Expr, wtype: W.Type): Operand => ({ wtype, emit: w => void emitAs(e, ctx, w) });

		// `this = expr` (only inside a `reassignsThis` method) parses as its own `this` node.
		if (target.type === 'identifier' || target.type === 'this') {
			const name = target.type === 'this' ? 'this' : target.name;
			// A holder holds the binding, not a copy, so every read and write of the name goes through it (`declareHolder`).
			const viaHolder = (holder: Operand, inner: W.Type): Place => {
				const holderType = (holder.wtype as { typeIndex: number }).typeIndex;
				return { wtype: inner, operands: [holder], load: () => ctx.emitHolderRead(holderType, inner), store: () => ctx.emit(I.struct.set(holderType, 0)) };
			};
			const captured = ctx.closureEnv?.fields.get(name);
			if (captured) {
				const { envLocal, envTypeIndex } = ctx.closureEnv!;
				const pushEnv = () => ctx.emit(I.local.get(envLocal.index));
				if (captured.holderInner)
					return viaHolder(fixed(captured.wtype, () => { pushEnv(); ctx.emit(I.struct.get(envTypeIndex, captured.index)); }), captured.holderInner);
				return { wtype: captured.wtype, operands: [fixed(envLocal.wtype, pushEnv)],
					load:	() => ctx.emit(I.struct.get(envTypeIndex, captured.index)),
					store:	() => ctx.emit(I.struct.set(envTypeIndex, captured.index)) };
			}
			const local = ctx.lookup(name);
			if (local?.holderInner)
				return viaHolder(fixed(local.wtype, () => ctx.emit(I.local.get(local.index))), local.holderInner);
			if (local)
				return { wtype: local.wtype, operands: [], load: () => ctx.emit(I.local.get(local.index)), store: () => ctx.emit(I.local.set(local.index)), tee: () => ctx.emit(I.local.tee(local.index)) };
			const g = globals.get(name) ?? libGlobalFor(name);
			if (g)
				return { wtype: g.wtype, operands: [], load: () => ctx.emit(I.global.get(g.index)), store: () => ctx.emit(I.global.set(g.index)) };
			// A lazily-initialized module-level value (`lazyGlobalFor`) is read through its wrapper -- the slot is null until that runs once.
			const lazy = lazyGlobalFor(name, ctx);
			if (lazy) {
				const wtype = lazy.wrapper.result;
				return { wtype, operands: [],
					load:	() => ctx.emit(I.call(lazy.wrapper.funcIndex)),
					store:	() => { coerceTop(wtype, ctx, lazy.slot.wtype); ctx.emit(I.global.set(lazy.slot.index)); } };
			}
			return undefined;
		}

		if (target.type === 'member') {
			const prop		= target.property;
			const cls		= write ? ownerOf(target.object, ctx) : classOfForIndexing(target.object, ctx);
			// `emitAs`: the receiver may be a boxed `anyref` (a ref-kind array element), and a struct access needs the real narrowed ref.
			const receiver	= (wtype: W.Type) => expr(target.object, wtype);

			// A dynamic object (`{[k: string]: V}`, a `Map`): `o.a` is the key's entry, never one of the map's own members.
			if (cls && !isOptionalChainLink(target) && indexSignatureValueType(T.resolve(ctx.scope, ctx.narrowedTypeOf(target.object))) && methodSig(cls, 'get', ctx)) {
				const key: Expr = Literal(prop);
				if (!write)
					return { wtype: methodSig(cls, 'get', ctx)!.result, operands: [receiver(cls.thisWtype!)], load: () => void emitMethodCall(cls, 'get', [key], ctx) };
				const wtype = methodSig(cls, 'set', ctx)?.params[1];
				if (!wtype)
					throw `internal: '${cls.name}' has a 'get' but no 'set(key, value)'`;
				return { wtype, operands: [receiver(cls.thisWtype!)], load: () => coerceValue(target, emitMethodCall(cls, 'get', [key], ctx), ctx, wtype),
					store: storeByCall(wtype, name => emitMethodCall(cls, 'set', [key, Identifier(name)], ctx)) };
			}

			// An accessor, before the field: a real getter (`Array<T>.length`) wins over any field of the name.
			if (write ? cls?.setterNames?.has(prop) : cls?.getterNames?.has(prop)) {
				const get = accessorKey('get', prop), set = accessorKey('set', prop);
				const getLoad = () => {
					if (!cls!.getterNames?.has(prop))
						throw `'${prop}' has no getter -- its old value can't be read for a compound assignment/'++'/'--'`;
					emitMethodCall(cls!, get, [], ctx);
				};
				const sig = methodSig(cls!, write ? set : get, ctx);
				if (!sig)
					throw `internal: accessor '${prop}' has no signature`;
				const wtype = write ? sig.params[0] : sig.result;
				return { wtype, operands: [receiver(cls!.thisWtype!)], load: getLoad,
					store: write ? storeByCall(wtype, name => emitMethodCall(cls!, set, [Identifier(name)], ctx)) : undefined };
			}

			const fieldIdx = cls?.fieldIndex.get(prop);
			if (cls && fieldIdx === undefined && cls.methodDecls.has(prop) && !write)
				return { wtype: typeOf(T.resolve(ctx.scope, ctx.narrowedTypeOf(target)))!, operands: [], load: () => void emitMethodValue(target, cls, ctx) };
			if (cls && fieldIdx !== undefined) {
				const wtype = cls.fields[fieldIdx].wtype;
				return { wtype, operands: [receiver(cls.thisWtype!)], load: () => void emitFieldRead(cls, fieldIdx, ctx), store: () => emitFieldWrite(cls, fieldIdx, wtype, ctx) };
			}

			// No single owner. A union of object shapes (`unionClassMembers`): the member's dispatch picks the struct at run time.
			const anyWrite = () => ctx.emit(I.call(ensureAnyFieldWrite(prop).funcIndex));
			const t = T.resolve(ctx.scope, ctx.narrowedTypeOf(target.object));
			if (t.type === 'union') {
				const owners = T.unionMembers(t, ctx.scope).filter(m => !T.isNullish(m, ctx.scope)).flatMap(m => flattenOwners(m, ctx.scope) ?? [undefined]);
				// Only a member that has `prop` can serve it: a key none declares (an expando written through `as any`) is the dynamic path's.
				if (owners.length > 1 && owners.every(o => o && o.typeIndex !== -1) && owners.some(o => o!.fieldIndex.has(prop) || !!o!.getterNames?.has(prop))) {
					const info = ensureUnionFieldDispatch(owners as ClassInfo[], prop, T.lookupMember(T.nonNullable(t, ctx.scope), prop, ctx.scope));
					return { wtype: write ? W.REF_ANY_NULLABLE : info.result, operands: [receiver(W.REF_ANY)], load: () => ctx.emit(I.call(info.funcIndex)), store: anyWrite };
				}
			}
			if (!write) {
				// A physically-extended local (`Object.defineProperty`, `ensureClassExtension`): its wasm local already holds the extended
				// form, which the checker type never reflects.
				const identExpr = unwrapAs(target.object);
				const local		= identExpr.type === 'identifier' ? ctx.lookup(identExpr.name) : undefined;
				const physCls	= local && W.isRef(local.wtype) ? ensureClass(local.wtype.ref) : undefined;
				const physIdx	= physCls?.fieldIndex.get(prop);
				if (physCls && physIdx !== undefined)
					return { wtype: physCls.fields[physIdx].wtype, operands: [], load: () => { ctx.emit(I.local.get(local!.index)); emitFieldRead(physCls, physIdx, ctx); } };
				const extIdx = physCls?.fieldIndex.get('#ext');
				const mapCls = extIdx !== undefined && ensureClass('Map', [TS.RefType('string'), T.ANY]);
				if (physCls && extIdx !== undefined && mapCls) {
					// The catch-all map may never have been allocated (null): the key is then absent, `undefined`, as `Map.get` gives on an allocated one.
					return { wtype: W.REF_ANY, operands: [], load: () => {
						ctx.emit(I.local.get(local!.index), I.struct.get(physCls.typeIndex, extIdx), I.ref.is_null);
						ctx.emitIf(toValType(W.REF_ANY), () => emitAs(Identifier('undefined'), ctx, W.REF_ANY), () => {
							ctx.emit(I.local.get(local!.index), I.struct.get(physCls.typeIndex, extIdx), I.ref.as_non_null);
							emitMethodCall(mapCls, 'get', [Literal(prop)], ctx);
						});
					} };
				}
				// Every non-nullish member a closure (or callable object): the closure struct stores `CLOSURE_FIELDS` itself.
				const closureField = CLOSURE_FIELDS.get(prop);
				if (closureField !== undefined && T.unionMembers(t, ctx.scope).filter(m => !T.isNullish(m, ctx.scope)).every(m => closurePart(typeOf(m)))) {
					const base = types.closureBase();
					return { wtype: 'u32', operands: [receiver(W.REF_ANY_NULLABLE)], load: () => ctx.emit(I.ref.cast(base), I.struct.get(base, closureField)) };
				}
			}
			// An erased receiver -- typed `any`, stored as `any` (an open shape), or narrowed to a shape its declared type lacks (`'type' in c`):
			// the field is found at run time (`ensureAnyField`). A write also reaches one through any receiver some class has the field for.
			const refined	= !write && ctx.stampedTypeOf(unwrapAs(target.object));
			const dynamic	= T.isAny(T.resolveOwn(ctx.narrowedTypeOf(target.object), ctx.scope)) || physicallyAny(target.object, ctx)
				|| (!!refined && !!T.lookupMember(refined, prop, ctx.scope) && !T.lookupMember(checkerTypeOf(unwrapAs(target.object), ctx.scope), prop, ctx.scope))
				|| (write && [...classes.values()].some(c => c.fieldIndex.has(prop) && c.typeIndex !== -1));
			if (dynamic)
				return { wtype: W.REF_ANY_NULLABLE, operands: [receiver(W.REF_ANY)], load: () => ctx.emit(I.call(ensureAnyField(prop).funcIndex)), store: anyWrite };
			throw `unknown field '${prop}'`;
		}

		if (target.type === 'index') {
			const cls		= classOfForIndexing(target.object, ctx);
			const getter	= cls && indexAccessor(cls, target.object, 'get', ctx);
			const getSig 	= cls && getter && methodSig(cls, getter, ctx);
			if (cls && getter && getSig) {
				// The index is held by name, typed for overload resolution: an overloaded accessor is chosen by its arguments' types.
				const indexName	= `$index$${ctx.tempCounter++}`;
				ctx.scope.addValue(indexName, ctx.narrowedTypeOf(target.index));
				const idxExpr: Expr	= Identifier(indexName);
				const setIndex	= () => ctx.emit(I.local.set(ctx.temp(indexName, getSig.params[0])));
				const operands	= [expr(target.object, cls.thisWtype!), expr(target.index, getSig.params[0])];
				const bounded	= readsPastEnd(target, ctx) && isPositional(cls, ctx) ? (resultWtype: W.Type) => void emitBoundedRead(target, cls.thisWtype!, resultWtype, ctx, (obj, idx) => {
					ctx.emit(I.local.get(obj.index));
					coerceValue(target, emitMethodCall(cls, getter, [Identifier(idx.name)], ctx), ctx, resultWtype);
				}) : undefined;
				// A read evaluates the index as the call's own argument; only a write, which may read first, holds it.
				if (!write)
					return { wtype: getSig.result, operands: [operands[0]], bounded, load: () => void emitMethodCall(cls, getter, [target.index], ctx) };
				const setter = indexAccessor(cls, target.object, 'set', ctx);
				if (!setter)
					throw `'${cls.name}' has an index getter but no setter`;
				// What a write STORES is the setter's value parameter for the overload the element's type picks (a typed array's
				// `__set` takes a `number` or a `bigint`), not the getter's result.
				const elementT	= ctx.narrowedTypeOf(target);
				const probe		= `$set$${ctx.tempCounter++}`;
				ctx.scope.addValue(probe, elementT);
				const setSig	= cls.inlineMethods?.has(setter) ? methodSig(cls, setter, ctx) : ensureMethod(cls, setter, [idxExpr, Identifier(probe)], ctx);
				const wtype		= setSig ? setSig.params[setSig.params.length - 1] : getSig.result;
				return { wtype, operands,
					load:	() => { setIndex(); coerceValue(target, emitMethodCall(cls, getter, [idxExpr], ctx), ctx, wtype); },
					store:	storeByCall(wtype, name => {
						setIndex();
						ctx.scope.addValue(name, elementT);
						return emitMethodCall(cls, setter, [idxExpr, Identifier(name)], ctx);
					}) };
			}

			// A union of indexable classes (`Uint8Array | number[]`): the element's dispatch picks the class's `__get` at run time.
			const t = T.resolve(ctx.scope, ctx.narrowedTypeOf(target.object));
			if (!write && t.type === 'union') {
				const owners = T.unionMembers(t, ctx.scope).filter(m => !T.isNullish(m, ctx.scope)).map(m => ownerFor(m));
				if (owners.length > 1 && owners.every(o => o && o.typeIndex !== -1 && methodSig(o, '__get', ctx))) {
					const info = ensureUnionIndexDispatch(owners as ClassInfo[]);
					return { wtype: info.result, operands: [expr(target.object, W.REF_ANY), expr(target.index, 'i32')], load: () => ctx.emit(I.call(info.funcIndex)) };
				}
			}

			const stringKey = T.isAssignable(ctx.narrowedTypeOf(target.index), T.STRING, ctx.scope);
			const keyWtype	= typeOf(T.STRING)!;
			// A computed STRING key on a struct: the field the key names, compared at run time; a key naming none reads `undefined`
			// and writes nothing, since a struct has no slot to grow.
			if (cls && cls.typeIndex !== -1 && cls.fields.length && stringKey) {
				const n		= ctx.tempCounter++;
				const ids	= { obj: Identifier(`#keyobj$${n}`), key: Identifier(`#key$${n}`), val: Identifier(`#keyval$${n}`) };
				const isKey	= (f: { name: string }) => Binary<Expr, '==='>('===', ids.key, Literal(f.name));
				const hold	= (id: Identifier, wtype: W.Type, t: Type) => ctx.emit(I.local.set((ctx.lookup(id.name) ?? ctx.declareValue(id.name, wtype, t)).index));
				const holdOperands = () => { hold(ids.key, keyWtype, T.STRING); hold(ids.obj, cls.thisWtype!, cls.thisTsType!); };
				return { wtype: W.REF_ANY_NULLABLE, operands: [expr(target.object, cls.thisWtype!), expr(target.index, keyWtype)],
					load: () => {
						holdOperands();
						emitAs(cls.fields.reduce<Expr>((alternate, f) => Conditional<Expr>(isKey(f), JS.Member(ids.obj, f.name), alternate), Identifier('undefined')), ctx, W.REF_ANY_NULLABLE);
					},
					store: () => {
						hold(ids.val, W.REF_ANY_NULLABLE, T.ANY);
						holdOperands();
						cls.fields.forEach(f => emitStmt({ type: 'if', test: isKey(f), consequent: JS.ExprStmt(Assign<Expr, never>(JS.Member(ids.obj, f.name), ids.val)) } as Stmt, ctx));
					} };
			}

			// A key on an erased receiver -- typed `any`, or a union of differing structs boxed as one: each class's arm is picked
			// by `ref.test` at run time, as JS reads `x[k]`.
			if (T.isAny(ctx.narrowedTypeOf(target.object)) || physicallyAny(target.object, ctx)) {
				if (stringKey)
					return { wtype: W.REF_ANY_NULLABLE, operands: [expr(target.object, W.REF_ANY), expr(target.index, keyWtype)],
						load:	() => ctx.emit(I.call(ensureAnyKey('get').funcIndex)),
						store:	() => ctx.emit(I.call(ensureAnyKey('set').funcIndex)) };
				if (T.isNumberLike(ctx.narrowedTypeOf(target.index), ctx.scope))
					return { wtype: W.REF_ANY_NULLABLE, operands: [expr(target.object, W.REF_ANY), expr(target.index, 'f64')],
						load:	() => ctx.emit(I.call(ensureAnyIndex('get').funcIndex)),
						store:	() => ctx.emit(I.call(ensureAnyIndex('set').funcIndex)) };
			}

			// `i16`/`i8` (`string`/packed-byte storage) are read and written through their classes' accessors, not as raw elements.
			const kind = objectArrayKind(target.object, ctx);
			if (!kind || kind === 'i16' || kind === 'i8') {
				if (write)
					throw "this operation is not supported";
				throw `'${T.exprKey(target.object)}' is indexed but is not an array, a typed array, or a class with index accessors (its type: '${T.typeKey(ctx.narrowedTypeOf(target.object))}')`;
			}
			const typeIndex	= types.array(kind);
			// A ref-kind array's storage is nullable `anyref`, shared by every non-scalar element, whatever the element's declared type.
			const wtype		= kind === 'ref' ? W.REF_ANY_NULLABLE : kind;
			return { wtype, operands: [expr(target.object, W.ARRAY[kind]), expr(target.index, 'i32')],
				load:		() => ctx.emit(I.array.get(typeIndex)),
				store:		() => ctx.emit(I.array.set(typeIndex)),
				bounded:	readsPastEnd(target, ctx) ? resultWtype => void emitBoundedRead(target, W.ARRAY[kind], resultWtype, ctx, (obj, idx) => {
					ctx.emit(I.local.get(obj.index), I.local.get(idx.index), I.array.get(typeIndex));
					coerceTop(wtype, ctx, resultWtype);
				}) : undefined };
		}
		return undefined;
	}

	function emitPlaceRead(e: Expr, place: Place, ctx: FunctionContext): W.Type {
		const [recv, ...rest] = place.operands;
		// The absent-able value as its own type is held (a number's box is `f64`, whatever the place's compact form).
		const absent = () => mayBeAbsent(e, place.wtype, ctx);
		if (recv && isOptionalChainLink(e)) {
			if (place.wtype === 'void')
				throw "'a?.[i]' is not supported -- 'get' returns 'void', which can't become 'void | undefined'";
			const objWtype		= types.nullable(recv.wtype);
			const resultWtype	= absent();
			recv.emit(objWtype);
			return ctx.emitOptionalAccess(objWtype, resultWtype, toValType, objLocal => {
				ctx.emit(I.local.get(objLocal), I.ref.as_non_null);
				rest.forEach(o => o.emit(o.wtype));
				place.load();
				coerceValue(e, place.wtype, ctx, resultWtype);
			});
		}
		if (place.bounded) {
			const resultWtype = absent();
			place.bounded(resultWtype);
			return resultWtype;
		}
		place.operands.forEach(o => o.emit(o.wtype));
		place.load();
		return place.wtype;
	}

	// `old`: `'none'` for a plain `=`, `'keep'` for postfix `++`/`--`, else `'discard'`.
	// `held`: operands go into locals even for `'none'` -- a conditional target's arms cannot leave them on the stack.
	function emitAssignTarget(target: Expr, ctx: FunctionContext, old: 'none' | 'discard' | 'keep', held = old !== 'none'): AssignTarget {
		if (target.type === 'assign' && isPurePath(target.target)) {
			// `(a.b ??= []).push(x)`: the assignment runs first, and its own target is where the write-back goes (a wasm array's
			// `push` builds a new one). Only for a target without side effects, which is read again rather than held.
			emitStmt(JS.ExprStmt(target), ctx);
			const inner = emitAssignTarget(target.target, ctx, old, held);
			// The kept value is the assignment's result, non-null when that is (`??=`), though its slot may be nullable.
			const result = wtypeOf(target, ctx);
			if (old === 'keep' && typeof inner.wtype !== 'string' && inner.wtype.nullable && result && typeof result !== 'string' && !result.nullable)
				ctx.emit(I.ref.as_non_null);
			return inner;
		}
		if (target.type === 'conditional') {
			// `(c ? a : b).push(x)`: a `this`-reassigning method's write-back goes to whichever branch the receiver came from,
			// so the test is held and both the read and the write branch on it.
			const test = ctx.temp(`$ctarget$${ctx.tempCounter++}`, 'i32');
			emitTruthy(target.test, ctx);
			ctx.emit(I.local.set(test));
			const _outer	= ctx.swapOut();
			const a			= emitAssignTarget(target.consequent, ctx, old, true);
			const _readA	= ctx.swapOut();
			const b			= emitAssignTarget(target.alternate, ctx, old, true);
			const _readB	= ctx.swapOut(_outer);
			if (!W.typeEq(a.wtype, b.wtype))
				throw `cannot assign to a conditional whose branches differ ('${W.typeKey(a.wtype)}' and '${W.typeKey(b.wtype)}')`;
			ctx.emit(I.local.get(test), I.if(old === 'none' ? undefined : toValType(a.wtype), _readA, _readB));
			const savedOld = old === 'keep' ? ctx.temp(`$old$${ctx.tempCounter++}`, a.wtype) : undefined;
			if (savedOld !== undefined)
				ctx.emit(I.local.tee(savedOld));
			return { wtype: a.wtype, old: savedOld, write: tee => {
				const val = ctx.temp(`$new$${ctx.tempCounter++}`, a.wtype);
				ctx.emit(I.local.set(val));
				const _o = ctx.swapOut();
				ctx.emit(I.local.get(val));
				a.write(false);
				const _writeA = ctx.swapOut();
				ctx.emit(I.local.get(val));
				b.write(false);
				ctx.emit(I.local.get(test), I.if(undefined, _writeA, ctx.swapOut(_o)));
				if (tee)
					ctx.emit(I.local.get(val));
			} };
		}

		const place = resolvePlace(target, ctx, true);
		if (!place)
			throw target.type === 'identifier' ? `unresolved identifier '${target.name}'` : `cannot assign to ${target.type}`;
		const { wtype, operands } = place;
		const store = place.store;
		if (!store)
			throw `cannot assign to '${T.exprKey(target)}'`;
		operands.forEach(o => o.emit(o.wtype));
		// Operands left on the stack sit under the value the caller emits next, where `store` expects them.
		if (!held) {
			return { wtype, write: tee => {
				if (tee && place.tee)
					return place.tee();
				const val = tee ? ctx.temp(`$new$${ctx.tempCounter++}`, wtype) : undefined;
				if (val !== undefined)
					ctx.emit(I.local.tee(val));
				store();
				if (val !== undefined)
					ctx.emit(I.local.get(val));
			} };
		}
		const locals = operands.map(o => ctx.temp(`$place$${ctx.tempCounter++}`, o.wtype));
		[...locals].reverse().forEach(l => ctx.emit(I.local.set(l)));
		const reload = () => locals.forEach(l => ctx.emit(I.local.get(l)));
		let savedOld: number | undefined;
		if (old !== 'none') {
			reload();
			place.load();
			if (old === 'keep') {
				savedOld = ctx.temp(`$old$${ctx.tempCounter++}`, wtype);
				ctx.emit(I.local.tee(savedOld));
			}
		}
		return { wtype, old: savedOld, write: tee => {
			const val = ctx.temp(`$new$${ctx.tempCounter++}`, wtype);
			ctx.emit(I.local.set(val));
			reload();
			ctx.emit(I.local.get(val));
			store();
			if (tee)
				ctx.emit(I.local.get(val));
		} };
	}


	// Shared by `case 'arrow'`/`case 'function'` (an expression, `allowSelfCall: false`) and `case 'function_decl'` (a statement
	// nested in another function's body, `allowSelfCall: true`) -- builds the `{code, env}` closure struct and leaves it on the
	// stack, returning its `{closure}` wtype. `allowSelfCall` lifts the "can't reference own name" restriction and instead lets
	// calls to `selfName` from inside the body resolve to a direct `call` (see `ctx.selfCall`), since a self-*capture* is
	// impossible -- the struct can't be a field of itself before it exists.
	function emitClosureLiteral(
		e: TS.CallSig & {type: string, name?: string, modifiers?: string[], body?: Stmt[] | Expr },
		ctx: FunctionContext,
		allowSelfCall: boolean,
		want?: W.Type,
		thisHolder?: { holder: W.Local; tsType: Type },
	): W.Type {
		if (hasMod(e, 'async'))
			throw 'an async arrow/function expression is not supported';
		if (hasMod(e, 'generator'))
			throw 'a generator function expression is not supported';
		// A closure literal inside a non-entry module's function body can reach here with its own param/return annotations never
		// stamped with a `declScope` (`makeLibScope`'s own "muted" comment documents the same class of gap). `ctx.scope` is exactly
		// the right scope regardless -- wherever `e` was written is `ctx`'s own home module -- and `T.stampScope` skips anything
		// already tagged, so this is safe unconditionally, before any of the literal's own types are asked for a wtype.
		e.params.forEach(p => p.typeAnnotation && T.stampScope(p.typeAnnotation, ctx.scope));
		if (e.returnType)
			T.stampScope(e.returnType, ctx.scope);
		// A generic closure *value* (unlike a generic function called directly, monomorphized per call site) is one physical closure
		// that has to work across every instantiation. Substituting each type param with its own upper bound (defaulting to `any` when
		// unconstrained) throughout params/return/body is enough, because a bounded value is already physically valid as its bound.
		if (e.typeParams?.length) {
			const map = T.constraintMap(e.typeParams, T.ANY);
			e = { ...T.instantiateSig(e, map), body: substituteTypeParams(map).body(e.body) };
		}

		const body	= e.body ?? [];
		if (e.name && !allowSelfCall && walkerB(undefined, (e1, process) => e1.type === 'identifier' ? e1.name === e.name : process(e1)).body(body))
			throw `a named function expression referencing its own name ('${e.name}') is not supported`;

		// The call site's expected closure signature (`want`, forwarded by `case 'arrow'`/`case 'function'`) wins over this literal's own `e.returnType` guess, when available
		// (`Rule([...], $ => ({type: 'spread', ...}))`-shaped calls in ts-parser.ts/js-parser.ts/binary-libs/wasm.ts). An unannotated arrow still gets *a* `e.returnType`
		// -- the checker's structural/anonymous inference back-filled into the same field real TS would have inferred, `checkFunctionBody`'s inference branch --
		// but an anonymous structural object type has no nominal identity for `typeOf`: it degrades to boxed `any`, and `case 'object'` rejects the body as needing a
		// known target type even though the caller's declared signature names the exact shape. An explicit annotation is safe too (the checker verified assignability,
		// so the physical wtypes are equivalent, upcast is free); a later, genuinely different but compatible use of the same closure value still hits `coerceTop`'s wrapper.
		const wantSig	= W.isClosure(want) ? closureSigOf(want) : undefined;
		const overloaded	= e.name ? overloadedReturn(e, (e as { scope?: Scope }).scope?.value(e.name)) : undefined;
		const result	= wantSig?.result ?? (overloaded ? typeOf(overloaded) : e.returnType ? typeOf(e.returnType) : 'void');
		if (!result)
			throw 'closure has an unsupported return type';

		// Parameters past the callee's fixed ones are covered by its REST, physically a single array, so they are not wasm
		// params: `restBound` names them and the prologue binds each from `restArray[k]`, e.g. `(_, a, b) => ...` against `(s: string, ...args: any[])`.
		const fixedCount	= wantSig?.hasRest ? wantSig.params.length - 1 : e.params.length;
		const restBound		= wantSig?.hasRest && !e.rest ? e.params.slice(fixedCount) : [];
		const ownParams		= restBound.length ? e.params.slice(0, fixedCount) : e.params;

		// A defaulted parameter resolves as a declaration's does (`resolveParam`), typed by the contextual signature
		// when unannotated, with the earlier parameters in scope for its default.
		const earlier = new Set<string>(), defaultScope = new Scope(ctx.scope);
		const noteEarlier = (p: JS.Param<Type>, r: ResolvedParam) => {
			if (typeof p.key === 'string') {
				earlier.add(p.key);
				defaultScope.addValue(p.key, r.tsType);
			}
			return r;
		};
		const wantParam = (i: number) => i < fixedCount ? wantSig?.resolvedParams?.[i] : undefined;
		const params = ownParams.map((p, i): ResolvedParam => {
			if (p.default) {
				const fromWant = p.typeAnnotation ? undefined : wantParam(i);
				// Called through the wanted type: where its slot is optional, an omitted argument arrives as `undefined` (checker.ts's
				// `widen = true` as a `typeOf`'s `widen?: boolean`), so the literal applies its own default.
				const slot = i < fixedCount ? wantSig?.params[i] : undefined;
				return noteEarlier(p, resolveParam(fromWant ? { ...p, typeAnnotation: fromWant.tsType } : p, earlier, defaultScope, W.isNullable(slot)));
			}
			// An UNANNOTATED parameter takes the callee's declared one, for the same reason `result` does above -- `Rules<T>(self => [...])`
			// and every `Rule([...], $ => ...)` can name it no other way. An annotation the checker wrote back names types from the
			// SIGNATURE's own module (printer.ts's `m` over `stmt.body` is annotated `ClassMember<Type>`, js-parser's), which need
			// not resolve here -- the wanted signature is the physical truth.
			const annotated = p.typeAnnotation && typeOf(p.typeAnnotation);
			const ctx = annotated ? undefined : wantParam(i);
			// See `closureFuncSigType`'s own identical comment -- box a real but wasm-unrepresentable
			// `void` as `any` rather than reject otherwise-valid source.
			const wt = annotated || ctx?.wtype;
			const boxed = wt === 'void' ? W.REF_ANY : wt;
			if (!boxed) {
				if (process.env.SHOWPARAM)
					console.error(`PARAM '${describeBinding(p.key)}' of ${e.name ?? '<anon>'}: want=${want ? W.typeKey(want) : '-'} wantSig=${!!wantSig} fromWantTs=${ctx ? T.typeKey(ctx.tsType).slice(0, 100) : '-'} ann=${p.typeAnnotation ? T.typeKey(p.typeAnnotation).slice(0, 100) : '-'}`);
				throw `closure parameter '${describeBinding(p.key)}' needs an explicit number/boolean/object type`;
			}
			// A bare `p?: T` needs a nullable physical slot to receive whatever a *caller* passes for an omitted argument -- omission
			// itself is entirely the caller's concern (`closureFuncSigType`'s `defaults`, built from the field/variable's own
			// declared TYPE, not this literal), since `call_ref` always supplies a real value for every physical param. The type
			// widens with the slot, as `resolveParam`'s does: left bare, `x ?? d` read `x` as never nullish and dropped `?? d`.
			const tsType = (annotated ? p.typeAnnotation : ctx?.tsType ?? p.typeAnnotation)!;
			return hasMod(p, 'optional') ? noteEarlier(p, { key: p.key, wtype: types.nullable(boxed), tsType: T.combineTypes([tsType, T.UNDEFINED]) })
				: noteEarlier(p, { key: p.key, wtype: boxed, tsType });
		});
		// The callee's own rest array becomes this literal's last physical parameter, whether or not the
		// literal spelled a rest -- the two must agree on the physical signature.
		if (restBound.length) {
			const restType = wantSig!.restElem;
			if (!restType)
				throw `closure parameter '${describeBinding(restBound[0].key)}' needs an explicit number/boolean/object type`;
			params.push({ key: '#rest', wtype: wantSig!.params[fixedCount], tsType: TS.ArrayType(restType.tsType) });
		}
		if (e.rest?.typeAnnotation) {
			const wt = restParamWtype(e.rest.typeAnnotation);
			if (!wt || wt === 'void')
				throw "a closure's rest parameter needs an explicit array type";
			params.push({key: e.rest.key, wtype: wt, tsType: e.rest.typeAnnotation });
		}

		const free = new Set<string>();
		collectClosureFreeVars(new Set(), e, e.name, free);

		if (e.type !== 'arrow' && free.has('this') && !thisHolder)
			throw "'this' inside a function expression is not supported -- only an arrow function's lexical 'this' is";

		for (const name of free) {
			// `undefined`/`NaN`/`Infinity` are always-valid identifiers `case 'identifier'` handles directly (`isNullLiteral` for
			// `undefined` specifically), not real bindings `collectFreeVars` should have marked for capture/resolution -- treating
			// them as free vars made any nested closure using one (e.g. `extra !== undefined`) throw here unconditionally.
			if (name === 'undefined' || name === 'NaN' || name === 'Infinity' || (name === 'this' && thisHolder))
				continue;
			// Module-scoped, so `resolvesGlobally` can never see them; the read site substitutes a constant.
			if ((name === '__dirname' || name === '__filename') && moduleFilename(ctx.homeModule))
				continue;
			if (!ctx.resolvesName(name) && !resolvesGlobally(ctx.homeModule, name) && !ensureForwardHolder(ctx, name))
				throw `unresolved identifier '${name}'`;
		}

		// Zero captures reuse `$envBase` directly -- no distinct type, no cast in the compiled body. A globally
		// resolvable free name (a top-level function, or a real wasm global) needs no capture slot either: the
		// body's own `case 'identifier'` fallback reaches it regardless of this closure's lexical nesting.
		const envBase		= types.envBase();
		const isHeld		= (name: string) => name === 'this' && !!thisHolder;
		const capturedNames = [...free].filter(name => isHeld(name) || ctx.resolvesName(name));
		const fields		= capturedNames.length ? new Map<string, { index: number; wtype: W.Type; holderInner?: W.Type }>() : undefined;
		let envTypeIndex	= envBase;
		if (fields) {
			// `rawWtype`, not `resolvedWtype`: a forward-holder has to be captured as the SHARED, mutable holder itself, so a later
			// write through it -- from wherever its own var_decl actually runs -- stays visible to this capture; `holderInner` lets
			// every READ unbox back to the logical value (`case 'identifier'`'s own read path).
			envTypeIndex = types.add({ final: true, supertypes: [envBase], type: { kind: 'struct', fields: capturedNames.map((name, i) => {
				const wt = isHeld(name) ? thisHolder!.holder.wtype : ctx.rawWtype(name)!;
				const holderInner = isHeld(name) ? thisHolder!.holder.holderInner : ctx.closureEnv?.fields.get(name)?.holderInner ?? ctx.lookup(name)?.holderInner;
				fields.set(name, { index: i, wtype: wt, holderInner });
				return { type: toValType(wt), mut: true };
			}) } });
		}

		const sig: FuncSig = { params: params.map(p => p.wtype), result, hasRest: !!e.rest || !!restBound.length, defaults: ownParams.map((p, i) => params[i].calleeDefault || (!p.default && hasMod(p, 'optional')) ? Identifier('undefined') : p.default), resolvedParams: params };
		// Captured now: the body compiles later, once this literal's own context (`Rule<CallSig>`'s action) is gone.
		// The checker's own contextual type wins: it saw the chosen OVERLOAD, where `ctx` only has the implementation's.
		const contextFn		= (e as { contextualType?: Type }).contextualType ?? ctx.contextualReturn;
		const fnContext		= contextFn && T.resolve(ctx.scope, contextFn);
		// This function's OWN declared return type is the literal's context: `return { type: kind, ...sig }` against a declared
		// union picks the member it names (`matchContextualUnionMember`), where an untargeted literal matches every same-shaped
		// class in the program and shape matching then refuses to guess. One the checker only INFERRED yields to the caller's context,
		// which is what reads the value: `rules<F | H>(rule(x => ({ type: 'f', ... })))` builds an `F`, not its own `{type; n}`.
		const contextReturn	= fnContext?.type === 'function' ? fnContext.returnType : undefined;
		const returnContext	= overloaded ?? (e.inferredReturn ? contextReturn ?? e.returnType : e.returnType ?? contextReturn);
		const { funcTypeIndex, structTypeIndex } = ensureClosureType(sig);
		const { funcIndex, typeIndex }	= types.funcAt(funcTypeIndex);
		const info: FuncInfo = { ...sig, funcIndex, typeIndex };
		closureLiterals.push(info);
		// A body naming itself as a VALUE (checker.ts `typeOf`'s `recurse`, captured by arrows inside it) binds its name to the
		// closure it runs as: its own code over the env it was given. A direct self-call stays direct (`selfCall` is tried first).
		// Not where a parameter or the body re-binds the name (printer.ts `function typeArgs(typeArgs?: Type[])`): those references
		// are to that binding, and a local for the function itself would collide with it.
		const selfType = allowSelfCall && e.name && !ownBoundNames(paramNames(e.params, e.rest), body).has(e.name) && namesSelfAsValue(body, e.name)
			? (e as { scope?: Scope }).scope?.value(e.name) ?? checkerTypeOf({ ...e, type: 'function' } as Expr, ctx.scope)
			: undefined;

		worklist.push(W.withCatchAt(() => {
			const fnCtx		= new FunctionContext(e.name ?? '<anonymous>', new Scope(moduleScopeOf(ctx.homeModule) ?? libGlobal), plainReturn(result, returnContext), undefined, ctx.homeModule);
			// Env param first (real wasm param index 0), then this literal's own params -- `toFuncBody`'s `numParams` assumes the first `1 + params.length` declared locals are the real wasm params, in order.
			const envParam	= fnCtx.declareLocal('#envParam', { typeIndex: envBase, nullable: false });
			const pending	= fnCtx.declareParams(params);
			// Each rest-covered parameter is read back out of that one array as a real `let x = #rest[k]`, so the
			// ordinary indexing path types and emits it; the declared type must ride along or it reads back as the element type.
			pending.unshift(...restBound.map((p, k) => JS.VarDecl('let', JS.Var<Type>(p.key,
				JS.Index(Identifier('#rest'), Literal(k)), p.typeAnnotation ?? wantSig!.restElem!.tsType))));
			// The cast-down env local (or, with no captures, just the param itself) is declared after the real params, so it's a genuine local, not mistaken for one more wasm param.
			let envLocal	= envParam;
			if (fields) {
				envLocal = fnCtx.declareLocal('#env', { typeIndex: envTypeIndex, nullable: false });
				fnCtx.emit(I.local.get(envParam.index), I.ref.cast(envTypeIndex), I.local.set(envLocal.index));
			}
			fnCtx.closureEnv = { envLocal, envTypeIndex, fields: fields ?? new Map() };
			if (allowSelfCall && e.name)
				fnCtx.selfCall = info;
			if (selfType) {
				fnCtx.emit(I.ref.func(funcIndex), I.local.get(envParam.index), I.i32.const(jsLength(e.params)), I.struct.new(structTypeIndex));
				fnCtx.emit(I.local.set(fnCtx.declareValue(e.name!, closureWtype(sig), selfType).index));
			}
			for (const name of capturedNames) {
				const tsType = isHeld(name) ? thisHolder!.tsType : ctx.scope.value(name);
				if (tsType)
					fnCtx.declareCaptured(name, tsType);
			}
			if (Array.isArray(body)) {
				fnCtx.ownBody = body;
				hoistVars(body, params, fnCtx);
			}
			pending.forEach(st => emitStmt(st, fnCtx));
			if (Array.isArray(body)) {
				emitStmts(body, fnCtx);
				fnCtx.emitTrailingUnreachable(result);
			} else {
				// The checker stamps an expression body with the scope it checked it in, as it stamps a block body's statements.
				emitStmt(Object.assign(JS.Return(body) as Stmt, { scope: (body as any).scope }), fnCtx);
			}
			info.body = fnCtx.toFuncBody(1 + params.length, toValType);
		}, e, ctx.homeModule, `${e.name ?? '<closure>'} in ${ctx.name}`));

		// `struct.new` pops fields in declaration order (`ensureClosureType`'s `[code, env]`), so the code pointer goes on the
		// stack before the env struct. Each capture is read raw (`rawSlot`, not the ordinary identifier-read case): a
		// forward-holder must be captured as the holder itself (see `rawWtype`'s own comment just above), never unboxed here; a
		// capture-of-a-capture (an ordinary, non-holder name) resolves identically either way.
		ctx.emit(I.ref.func(funcIndex));
		for (const name of capturedNames) {
			if (isHeld(name))
				ctx.emit(I.local.get(thisHolder!.holder.index));
			else if (name === 'this' && !ctx.closureEnv?.fields.get(name)?.holderInner)
				emitExpr({ type: 'this' }, ctx);
			else
				ctx.rawSlot(name);
		}
		ctx.emit(fields ? I.struct.new(envTypeIndex) : I.struct.new_default(envBase));
		ctx.emit(I.i32.const(jsLength(e.params)), I.struct.new(structTypeIndex));
		return closureWtype(sig);
	}

	// A plain named function used as a *value* rather than called directly by name (`case 'call'` resolves that straight to
	// `funcs.get(name)`, no closure struct ever involved). A top-level function captures nothing, so it is compiled with no `env`
	// param and its own `funcIndex` can't fill a closure's `code` field (always `(env, ...params)`). This builds one shared
	// zero-capture trampoline per function name instead -- same shape `emitClosureLiteral`'s own zero-capture case builds (`env`
	// ignored, `envBase` reused directly, no distinct env type) -- forwarding to the real, already- or newly-compiled function.
	function ensureFunctionValueWrapper(name: string, decl: FunctionDecl, homeModule = '.', want?: W.Type, typeArgs?: Type[]): { info: FuncInfo; structTypeIndex: number } {
		const key = typeArgs ? `${homeKey(homeModule, name)}<${typeArgs.map(T.typeKey).join(',')}>` : homeKey(homeModule, name);
		const existing = functionValueWrappers.get(key);
		if (existing) {
			const { structTypeIndex } = ensureClosureType({ params: existing.params, result: existing.result, hasRest: existing.hasRest });
			return { info: existing, structTypeIndex };
		}
		// A GENERIC function used as a VALUE has no call site to infer from, so its type parameters erase to their bounds --
		// exactly what `closureSigParts` already does for a generic function TYPE, and what the value's own declared type
		// (`CommonAction<C> = <T>(value: T, ...) => any`) erases to on the other side of the assignment. One instantiation,
		// since the erasure is fixed; explicit type arguments (an instantiation expression, `f<A>`) pick the instantiation instead.
		const erased	= decl.typeParams?.length
			? new Map(decl.typeParams.map((p, i) => [p.name, (typeArgs?.[i] ?? (typeArgs && p.default) ?? p.constraint ?? T.ANY) as Type]))
			: undefined;
		const instance	= erased && genericKey(name, decl.typeParams!, erased, global);
		const target	= funcs.get(instance || key) ?? (instance
			? compileFunc(instance, instantiateDecl(decl, erased!, homeModule), homeModule, name)
			: compileFunc(name, decl, homeModule));
		if (!target)
			throw `'${name}' can't be used as a value`;

		// `defaults` travel with it: a slot with fewer params converts by supplying them (`ensureClosureCoercionWrapper`).
		const sig: FuncSig = { params: target.params, result: target.result, hasRest: target.hasRest, defaults: target.defaults };
		const { funcTypeIndex, structTypeIndex } = ensureClosureType(sig);
		const { funcIndex, typeIndex } = types.funcAt(funcTypeIndex);
		// Erasure answers only where the WANTED signature is itself erased (`CommonAction<C> = <T>(value: T, ...) => any`); a
		// concrete one needs the real instantiation, which nothing here can infer (`want` is physical and carries no type
		// arguments), so say that rather than let it surface as an `internal: cannot convert (ref:any)=>ref:any to (f64)=>f64` further out.
		if (erased && !typeArgs && W.isClosure(want)
			&& want.closure.params.length === sig.params.length
			&& !want.closure.params.every((p, i) => W.typeEq(p, sig.params[i])))
			throw `generic function '${name}' as a value only erases to its bounds -- a concrete instantiation is not supported`;

		const info: FuncInfo = { ...sig, funcIndex, typeIndex, defaults: target.defaults };
		closureLiterals.push(info);
		functionValueWrappers.set(key, info);

		worklist.push(() => {
			const wctx		= new FunctionContext(`<fnvalue>.${name}`, new Scope(libGlobal), plainReturn(target.result), undefined);
			wctx.declareLocal('#envParam', { typeIndex: types.envBase(), nullable: false });
			const argLocals = target.params.map((p, i) => wctx.declareLocal(`$arg$${i}`, p));
			argLocals.forEach(l => wctx.emit(I.local.get(l.index)));
			wctx.emit(I.call(target.funcIndex));
			info.body = wctx.toFuncBody(1 + argLocals.length, toValType);
		});
		return { info, structTypeIndex };
	}

	// A method's closure env: the `this` it runs on. JS binds a method's `this` at the CALL, so a method value carries it
	// in this one shape, and `.call(t, ...)` rebuilds the closure with `t` (an arrow's env is its own, and keeps its `this`).
	function envThis(): number {
		return types.register({ final: true, supertypes: [types.envBase()], type: { kind: 'struct', fields: [{ type: toValType(W.REF_ANY_NULLABLE), mut: false }] } });
	}

	// `obj.m` read, not called: a closure over `envThis(obj)`, whose code calls `this.m(...)` as any call site would --
	// overloads and overrides included. Called with no receiver, the null `this` traps where JS would throw.
	function emitMethodValue(e: Expr & { type: 'member' }, cls: ClassInfo, ctx: FunctionContext): W.Type {
		const fnType	= T.resolve(ctx.scope, ctx.narrowedTypeOf(e));
		const w			= typeOf(fnType);
		if (fnType.type !== 'function' || !W.isClosure(w))
			throw `method '${e.property}' as a value needs a function type, got '${T.typeKey(fnType)}'`;
		const sig		= closureSigOf(w);
		const { funcTypeIndex, structTypeIndex } = ensureClosureType(sig);
		const key		= `${cls.name}.${e.property}:${W.typeKey(w)}`;
		let info		= methodValueWrappers.get(key);
		if (!info) {
			const made: FuncInfo = { ...sig, ...types.funcAt(funcTypeIndex) };
			info = made;
			closureLiterals.push(made);
			methodValueWrappers.set(key, made);
			worklist.push(() => {
				const wctx	= new FunctionContext(`<method value>.${cls.name}.${e.property}`, new Scope(libGlobal), plainReturn(sig.result), undefined, ctx.homeModule);
				const env	= wctx.declareLocal('#envParam', { typeIndex: types.envBase(), nullable: false });
				const args	= sig.params.map((p, i) => {
					wctx.declareValue(`$arg$${i}`, p, sig.resolvedParams![i].tsType);
					return sig.hasRest && i === sig.params.length - 1 ? JS.Spread(Identifier(`$arg$${i}`)) : Identifier(`$arg$${i}`);
				});
				const self	= wctx.declareValue('this', cls.thisWtype!, cls.thisTsType);
				wctx.emit(I.local.get(env.index), I.ref.cast(envThis()), I.struct.get(envThis(), 0), I.ref.cast(cls.typeIndex), I.local.set(self.index));
				emitStmt(JS.Return(JS.Call(JS.Member({ type: 'this' }, e.property), args)) as Stmt, wctx);
				wctx.emitTrailingUnreachable(sig.result);
				made.body = wctx.toFuncBody(1 + sig.params.length, toValType);
			});
		}
		ctx.emit(I.ref.func(info.funcIndex));
		emitAs(e.object, ctx, W.REF_ANY_NULLABLE);
		ctx.emit(I.struct.new(envThis()), I.i32.const(jsLength(fnType.params)), I.struct.new(structTypeIndex));
		return w;
	}

	const isFunctionTyped = (e: Expr, ctx: FunctionContext) =>
		T.unionMembers(ctx.narrowedTypeOf(e), ctx.scope).every(m => T.resolveOwn(m, ctx.scope).type === 'function');

	// `f.call(t, ...args)`: `f` with `t` as its `this` -- a method value's `envThis` refilled -- then called as `f(...args)`.
	function emitFunctionCallMethod(fn: Expr, [thisArg, ...args]: Expr[], ctx: FunctionContext, want?: W.Type): W.Type {
		const w			= emitExpr(fn, ctx);
		const closure	= W.isClosure(w) && !w.nullable;
		if (!closure && !W.isAny(w))
			throw `'.call' needs a function value, got '${W.typeKey(w)}'`;
		const n			= ctx.tempCounter++;
		const fnName	= `$callfn$${n}`;
		const fnLocal	= ctx.declareValue(fnName, w, ctx.narrowedTypeOf(fn));
		ctx.emit(I.local.set(fnLocal.index));
		const emitThis	= () => thisArg ? emitAs(thisArg, ctx, W.REF_ANY_NULLABLE) : ctx.emitDefaultValue(W.REF_ANY_NULLABLE, types, toValType);
		if (closure) {
			const { structTypeIndex }	= ensureClosureType(closureSigOf(w));
			const thisLocal				= ctx.declareLocal(`$callthis$${n}`, W.REF_ANY_NULLABLE);
			emitThis();
			ctx.emit(I.local.set(thisLocal.index), I.local.get(fnLocal.index), I.struct.get(structTypeIndex, 1), I.ref.test(envThis()));
			ctx.emitIf(undefined, () => ctx.emit(...rebuildWithThis(structTypeIndex, [I.local.get(fnLocal.index)], [I.local.get(thisLocal.index)]), I.local.set(fnLocal.index)));
		} else {
			ctx.emit(I.local.get(fnLocal.index));
			emitThis();
			ctx.emit(I.call(ensureAnyRebindThis().funcIndex), I.local.set(fnLocal.index));
		}
		return emitExpr(JS.Call(Identifier(fnName), args), ctx, want);
	}

	// The closure `held` with its env replaced by `envThis(thisVal)`: same code, same `length`.
	const rebuildWithThis = (structTypeIndex: number, held: wasm.Instr[], thisVal: wasm.Instr[]): wasm.Instr[] => [
		...held, I.struct.get(structTypeIndex, 0), ...thisVal, I.struct.new(envThis()), ...held, I.struct.get(structTypeIndex, 2), I.struct.new(structTypeIndex),
	];

	// `.call`'s rebinding for a function held as `any` (a union of signatures): which closure type it is, is known only at run
	// time, so every closure type the program has is a candidate. Built by `lateWorklist`, once that set is final.
	function ensureAnyRebindThis(): FuncInfo {
		return synthesize('<any dispatch>.#rebindThis', () => ({ params: [anyParam('callee'), anyParam('this', W.REF_ANY_NULLABLE)], result: W.REF_ANY }), (dctx, [callee, thisVal]) => {
			const base = types.closureBase();
			const arms = [...closureTypes.values()].reduceRight<wasm.Instr[]>((rest, c) => [
				I.local.get(callee), I.ref.test(c.structTypeIndex),
				I.if(toValType(W.REF_ANY), rebuildWithThis(c.structTypeIndex, [I.local.get(callee), I.ref.cast(c.structTypeIndex)], [I.local.get(thisVal)]), rest),
			], [I.unreachable]);
			dctx.emit(I.local.get(callee), I.ref.test(base));
			dctx.emitIf(undefined, () => {
				dctx.emit(I.local.get(callee), I.ref.cast(base), I.struct.get(base, 1), I.ref.test(envThis()));
				dctx.emitIf(undefined, () => dctx.emit(...arms, I.return));
			});
			dctx.emit(I.local.get(callee));
		});
	}

	// `++x`/`x++` (`postfix`): the target read once, stepped, written back; the value is the new one, or the old one kept.
	function emitIncDec(operand: Expr, op: '++' | '--', postfix: boolean, ctx: FunctionContext, want?: W.Type): W.Type {
		return ctx.inScope((): W.Type => {
			const target = emitAssignTarget(operand, ctx, postfix ? 'keep' : 'discard');
			emitStep(target.wtype, ctx.narrowedTypeOf(operand), op === '++' ? 'add' : 'sub', ctx);
			target.write(!postfix && want !== 'void');
			if (want === 'void')
				return want;
			if (postfix)
				ctx.emit(I.local.get(target.old!));
			return target.wtype;
		});
	}

	// `++`/`--`'s step on the value on the stack: a number's is 1, a bigint's `1n` (its own `add`/`sub`), and a boxed `any` -- a
	// `number | bigint` -- takes whichever its value is, as JS decides at run time, told apart as `typeof` tells them.
	function emitStep(wtype: W.Type, t: Type, method: 'add' | 'sub', ctx: FunctionContext): void {
		const machine = typeof wtype === 'string' && wtype !== 'void' ? toValType(wtype) : undefined;
		if (machine === 'i32' || machine === 'f32' || machine === 'f64')
			return void ctx.emit(I[machine].const(1), I[machine][method]);
		if (machine === 'i64')
			return void ctx.emit(I.i64.const(1n), I.i64[method]);
		const big = builtinTypeOwner('bigint')!;
		if (T.typeofName(t, ctx.scope) === 'bigint')
			return void emitMethodCall(big, method, [Literal(1n)], ctx);
		if (!W.isAny(wtype)) {
			// A nullable primitive gets a specific, actionable message: narrowing it to non-null would need per-read tracking codegen does for no type.
			if (W.unboxedPrimitive(wtype))
				throw "'++'/'--' on a nullable primitive needs narrowing to non-null first, and isn't supported even then";
			throw "'++'/'--' needs a number, a bigint, or an 'any' holding one";
		}
		const heap	= types.heapType('bigint')!;
		const v		= ctx.temp(`$step$${ctx.tempCounter++}`, wtype);
		ctx.emit(I.local.set(v), I.local.get(v), I.ref.test(heap));
		ctx.emitIf(toValType(wtype), () => {
			ctx.emit(I.local.get(v), I.ref.cast(heap));
			emitMethodCall(big, method, [Literal(1n)], ctx);
		}, () => {
			ctx.emit(I.local.get(v));
			coerceTop(wtype, ctx, 'f64');
			ctx.emit(I.f64.const(1), I.f64[method]);
			coerceTop('f64', ctx, wtype);
		});
	}

	// A bare `f` or a namespace-qualified `NS.f` read as a VALUE resolves to a top-level function exactly as a call would.
	function functionValueDecl(e: Expr, ctx: FunctionContext): { name: string; decl: FunctionDecl; module: string } | undefined {
		if (e.type === 'identifier') {
			const own = resolveDecl(ctx.homeModule, e.name);
			if (own)
				return own.type === 'function_decl' && own.body ? { name: e.name, decl: own, module: ctx.homeModule } : undefined;
			const imported = namedImportsByModule.get(ctx.homeModule)?.get(e.name);
			const decl = imported && functionDeclByName.get(homeKey(imported.module, imported.name));
			return decl?.type === 'function_decl' && decl.body ? { name: imported!.name, decl, module: imported!.module } : undefined;
		}
		if (e.type === 'member' && e.object.type === 'identifier' && !ctx.lookup(e.object.name)) {
			const nsDecl	= ctx.scope.namespace(e.object.name)?.decl(e.property);
			const module	= nsDecl && stmtHomeModule.get(nsDecl);
			const decl		= module !== undefined ? functionDeclByName.get(homeKey(module, e.property)) : undefined;
			return decl?.type === 'function_decl' && decl.body ? { name: e.property, decl, module: module! } : undefined;
		}
		return undefined;
	}


	// `e.object[e.index]` held in locals, `read` run only when the index is below the length (unsigned, so a negative index is past the end too), `null` otherwise.
	function emitBoundedRead(e: Expr & { type: 'index' }, objWtype: W.Type, resultWtype: W.Type, ctx: FunctionContext, read: (obj: W.Local, idx: W.Local & { name: string }) => void): W.Type {
		const n		= ctx.tempCounter++;
		const objName	= `$bobj$${n}`;
		const obj		= ctx.declareValue(objName, objWtype, ctx.narrowedTypeOf(e.object));
		const idx		= Object.assign(ctx.declareValue(`$bidx$${n}`, 'i32', T.NUMBER), { name: `$bidx$${n}` });
		emitAs(e.object, ctx, objWtype);
		ctx.emit(I.local.set(obj.index));
		emitAs(e.index, ctx, 'i32');
		ctx.emit(I.local.set(idx.index), I.local.get(idx.index));
		// Raw storage is its own bound; anything else answers through its own `length`, as JS reads it.
		if (W.isArr(objWtype))
			ctx.emit(I.local.get(obj.index), I.array.len);
		else
			emitAs(JS.Member(Identifier(objName), 'length'), ctx, 'i32');
		ctx.emit(I.i32.lt_u);
		ctx.emitIf(toValType(resultWtype), () => read(obj, idx), () => ctx.emitDefaultValue(resultWtype, types, toValType));
		return resultWtype;
	}

	// A bare name bound to a module-level VALUE, not a function (`walker.ts`'s `export const isJsStatement = guard<TS.Stmt>(...)`,
	// called by name in `printer.ts`): the call calls the value it holds, as a namespace member's does.
	function isModuleValue(name: string, ctx: FunctionContext): boolean {
		if (ctx.resolvesName(name) || resolveDecl(ctx.homeModule, name) || funcs.has(homeKey(ctx.homeModule, name)))
			return false;
		const imported	= namedImportsByModule.get(ctx.homeModule)?.get(name);
		const decl		= imported ? moduleScopeOf(imported.module)?.decl(imported.name) : moduleScopeOf(ctx.homeModule)?.decl(name);
		// Not an inline-asm intrinsic (`const loadI32 = __asm<[i32], i32>('i32.load')`): that IS the instruction, not a value.
		const init		= decl?.type === 'var_decl' ? decl.declarations.find(d => d.name === (imported?.name ?? name))?.init : undefined;
		return !!init && !(init.type === 'call' && isAsm(init));
	}


	function emitFunctionValue(fn: { name: string; decl: FunctionDecl; module: string }, want: W.Type | undefined, ctx: FunctionContext, typeArgs?: Type[]): W.Type {
		const { info, structTypeIndex } = ensureFunctionValueWrapper(fn.name, fn.decl, fn.module, want, typeArgs);
		ctx.emit(I.ref.func(info.funcIndex), I.struct.new_default(types.envBase()), I.i32.const(jsLength(fn.decl.params)), I.struct.new(structTypeIndex));
		return closureWtype({ params: info.params, result: info.result, hasRest: info.hasRest, defaults: info.defaults });
	}

	// A closure *value* whose own concrete signature doesn't match some slot it's being coerced into, but real TS/JS would still
	// allow it -- either a covariant return (`(x: number) => number` fitting `(x: number) => number | undefined`, the common
	// shape a mapped type's own homomorphic value type produces: `Partial<{...}>`'s `?`-optional value widens every property
	// with `| undefined`, though a real property/callback value written against one key rarely bothers writing that itself),
	// or fewer declared params than `wantSig` offers (`arr.map(x => x*2)` never declares `index`/`array` at all; found via
	// `lib/map.ts`'s own `entries()` calling `Array<K>.map((k, i) => ...)`, itself two short of the real 3-param `callbackfn`).
	// Unlike a scalar (`coerceTop` alone converts one already-on-the-stack value in place), a closure's own compiled signature
	// is fixed at its own `funcTypeIndex`, so there is no in-place conversion, only wrapping: one small, shared trampoline per
	// (source, wanted) signature pair, not one per use site, that declares `wantSig`'s full param list (the wrapper's real arity
	// -- a caller through `wantFuncTypeIndex` always passes all of them), forwards only the leading `gotSig.params.length` to the
	// original closure (silently dropping the rest, as real JS ignores a shorter callback's trailing arguments) and coerces just
	// the return. Contravariant widening of a *shared* leading param is not attempted.
	function ensureClosureCoercionWrapper(gotSig: FuncSig, wantSig: FuncSig): { info: FuncInfo; wantStructTypeIndex: number; envTypeIndex: number } {
		const key = `(${gotSig.params.map(W.typeKey).join(',')})=>${W.typeKey(gotSig.result)}=>(${wantSig.params.map(W.typeKey).join(',')})=>${W.typeKey(wantSig.result)}`;
		const existing = closureCoercionWrappers.get(key);
		if (existing)
			return existing;

		const { structTypeIndex: gotStructTypeIndex } = ensureClosureType(gotSig);
		const { funcTypeIndex: wantFuncTypeIndex, structTypeIndex: wantStructTypeIndex } = ensureClosureType(wantSig);
		const { funcIndex, typeIndex } = types.funcAt(wantFuncTypeIndex);
		const info: FuncInfo = { ...wantSig, funcIndex, typeIndex };
		closureLiterals.push(info);
		// A dedicated one-field env struct (a real `envBase` subtype, like any other closure's own capture struct) holding just the
		// original closure value: the {code,env} pair is *not* an `envBase` subtype (no supertypes, see `ensureClosureType`), so unlike
		// `emitClosureLiteral`'s zero-capture case it can't reuse `envBase` as this wrapper's own env directly.
		const envTypeIndex = types.add({ final: true, supertypes: [types.envBase()], type: { kind: 'struct', fields: [
			{ type: toValType({ typeIndex: gotStructTypeIndex, nullable: false }), mut: false },
		] } });
		const result = { info, wantStructTypeIndex, envTypeIndex };
		closureCoercionWrappers.set(key, result);

		worklist.push(() => {
			const wctx		= new FunctionContext(`<coerce>.${key}`, new Scope(libGlobal), plainReturn(wantSig.result), undefined);
			const envParam	= wctx.declareLocal('#envParam', { typeIndex: types.envBase(), nullable: false });
			const argLocals	= wantSig.params.map((p, i) => wctx.declareLocal(`$arg$${i}`, p));
			const env		= wctx.declareLocal('#env', { typeIndex: envTypeIndex, nullable: false });
			wctx.emit(I.local.get(envParam.index), I.ref.cast(envTypeIndex), I.local.set(env.index));
			wctx.emit(I.local.get(env.index), I.struct.get(envTypeIndex, 0));
			emitClosureCall({ closure: gotSig }, () => {
				// Each argument coerced from what the CALLER passes to what the callback declared -- see the `paramFits` guard: a `ref.cast` for a reference, a no-op when the two agree.
				argLocals.slice(0, gotSig.params.length).forEach((l, i) => {
					wctx.emit(I.local.get(l.index));
					coerceTop(wantSig.params[i], wctx, gotSig.params[i]);
				});
				// Params the caller never passes get the callback's own defaults, exactly as a call site omitting them would.
				gotSig.params.slice(argLocals.length).forEach((p, i) => {
					const d = gotSig.defaults?.[argLocals.length + i];
					if (d)
						emitAs(d, wctx, p);
					else
						wctx.emitDefaultValue(p, types, toValType);
				});
			}, wctx);
			coerceTop(gotSig.result, wctx, wantSig.result);
			info.body = wctx.toFuncBody(1 + argLocals.length, toValType);
		});
		return result;
	}

	// Real `ToInt32`: truncate, then keep the low 32 bits. The plain saturating `i32.trunc_sat_f64_s` that `coerceTop` uses
	// everywhere else would answer `i32::MAX` for `2147483648 | 0` and `(4294967296 + 5) | 0`, which are -2147483648 and 5.
	// Saturation deliberately stays the rule for an index or a length (see `coerceTop`'s own comment); `ToInt32` applies exactly
	// where JS specifies it, the bitwise operators. A non-finite input has no meaningful `i64` truncation, so it answers 0, as JS says.
	function emitToInt32(e: Expr, ctx: FunctionContext): void {
		emitAs(e, ctx, 'f64');
		const tmp = ctx.temp(`$toint32$${ctx.tempCounter++}`, 'f64');
		ctx.emit(I.local.set(tmp), I.local.get(tmp), I.f64.abs, I.f64.const(Infinity), I.f64.lt);
		ctx.emitIf(toValType('i32'),
			() => ctx.emit(I.local.get(tmp), I.i64.trunc_sat_f64_s, I.i32.wrap_i64),
			() => ctx.emit(I.i32.const(0)));
	}

	const BITWISE_METHODS = new Set(['and', 'or', 'xor', 'shl', 'shr_s', 'shr_u']);


	// `want`, when passed, is a hint only -- lets a literal pick its physical representation directly instead
	// of `coerceTop` immediately converting it back. The returned `WasmType` is always the actual physical type left on the stack.
	function emitExpr(e: Expr, ctx: FunctionContext, want?: W.Type, callContext?: Type): W.Type {
		// A call consumes the hint for its own type-argument inference (`callContext`) and it is cleared for everything the call
		// compiles: a callee and its arguments are unrelated expressions, and a literal among them would read it as its own
		// target. Only the identifier-callee path had cleared it, so `Object.keys(spec.rules ?? {})` leaked into the `{}`.
		if (e.type === 'call' && ctx.contextualReturn !== undefined) {
			const saved = ctx.contextualReturn;
			return ctx.withContext(undefined, () => emitExpr(e, ctx, want, saved));
		}
		if (e.type === 'call' && ctx.callContext !== callContext)
			return ctx.withCallContext(callContext, () => emitExpr(e, ctx, want, callContext));
		try { switch (e.type) {
			case 'literal':
				switch (typeof e.value) {
					case 'number':
						// `typeof want === 'string'`: the i32 shortcut only makes sense when the caller wants a
						// plain scalar -- `want` being an object (e.g. boxing into `any`) means a bare `'i32'` here would be indistinguishable from a real boolean once `coerceTop` has to pick a box.
						if (typeof want === 'string' && want !== 'f64' && e.value === (e.value | 0)) {
							ctx.emit(I.i32.const(e.value));
							return 'i32';
						}
						ctx.emit(I.f64.const(e.value));
						return 'f64';

					case 'boolean':
						ctx.emit(I.i32.const(e.value ? 1 : 0));
						return 'i32';

					case 'string':
						emitStringConst(e.value, ctx);
						return W.ARRAY.i16;

					case 'bigint': {
						// A `bigint` VALUE is a two's-complement little-endian `u32[]` (see `typeOf`, and `lib/bigint.ts`'s own limb walks), so that
						// is what a literal must build. An `i64` here disagrees with every other bigint: `10n - 4n` reinterprets it as limbs and
						// gives -1, `Number(5n)` cannot convert, past 64 bits truncate. A real `i64` slot (an `i64` param or global) still gets
						// the constant directly -- the one place the two agree.
						// A machine-int representation takes the constant directly; `coerceTop` widens it to the limb array at any boundary.
						if (want === 'i64' || want === 'i32') {
							ctx.emit(want === 'i64' ? I.i64.const(e.value) : I.i32.const(Number(e.value)));
							return want;
						}
						// Limbs in exactly the form `lib/bigint.ts` reads back: little-endian `u32`, TWO'S COMPLEMENT (not sign-magnitude), sign-
						// extended so the top limb's high bit IS the sign, and trimmed the way `bigTrim` trims -- no top limb merely repeating the sign below.
							
						const limbs: number[] = [];
						let x = e.value;
						if (x >= 0n) {
							while (x > 0n) {
								limbs.push(Number(x & 0xffffffffn));
								x >>= 32n;
							}
							// `0n`, and a value whose top limb would otherwise read as negative, both need a limb of room.
							if (!limbs.length || (limbs[limbs.length - 1] & 0x80000000))
								limbs.push(0);
						} else {
							// `>>` on a negative bigint is arithmetic in JS, so this converges on `-1n`, which is exactly
							// the infinite sign extension the encoding wants.
							while (x < -1n) {
								limbs.push(Number(x & 0xffffffffn));
								x >>= 32n;
							}
							if (!limbs.length || !(limbs[limbs.length - 1] & 0x80000000))
								limbs.push(0xffffffff);
						}
						for (const l of limbs)
							ctx.emit(I.i32.const(l | 0));
						ctx.emit(I.array.new_fixed(types.array('i32'), limbs.length));
						return W.ARRAY.i32;
					}

					case 'object':
						if (e.value instanceof RegExp) {
							// desugars to an ordinary `new RegExp(source, flags)` against `lib/regexp.ts`'s own self-hosted class
							return emitExpr({
								type: 'new',
								callee: Identifier('RegExp'),
								arguments: [Literal(e.value.source), Literal(e.value.flags)],
							}, ctx, want);
						}
						if (Array.isArray(e.value)) {
							if (e.value.length === 1 && !e.value[0].exp) {
								emitStringConst(e.value[0].str, ctx);
								return W.ARRAY.i16;
							}

							// Resolved first: `stringTemplate` takes REAL arrays (`string[]`, `any[]`), so each storage array built below is coerced to its parameter as soon as it exists.
							// A missing lib entry would otherwise emit the arrays and silently skip the call.
							const decl = LIB_DECL_MAP.get('stringTemplate');
							const info = decl && decl.type === 'function_decl' ? ensureFunc('stringTemplate', decl) : undefined;
							if (!info)
								throw "internal: lib 'stringTemplate' is unavailable";
							for (const p of e.value)
								emitStringConst(p.str, ctx);
							const hasTrailingLiteral = !e.value[e.value.length - 1].exp;
							if (!hasTrailingLiteral)
								emitStringConst('', ctx);
							ctx.emit(I.array.new_fixed(types.array('ref'), e.value.length + (hasTrailingLiteral ? 0 : 1)));
							coerceTop(W.ARRAY.ref, ctx, info.params[0]);
							let valueCount = 0;
							for (const p of e.value) {
								if (p.exp) {
									emitAs(p.exp, ctx, W.REF_ANY);
									valueCount++;
								}
							}
							ctx.emit(I.array.new_fixed(types.array('ref'), valueCount));
							coerceTop(W.ARRAY.ref, ctx, info.params[1]);
							ctx.emit(I.call(info.funcIndex));
							return W.ARRAY.i16;
						}
						throw `unsupported literal type '${typeof e.value}'`;

					default:
						throw `unsupported literal type '${typeof e.value}'`;
				}

			case 'identifier': {
				// There's no way to write NaN or Infinity without using themselves
				if (e.name === 'NaN') {
					ctx.emit(I.f64.const(NaN));
					return 'f64';
				}
				if (e.name === 'Infinity') {
					ctx.emit(I.f64.const(Infinity));
					return 'f64';
				}
			}
			//fall through
			case 'this': {
				const name = e.type === 'this' ? 'this' : e.name;
				// During `ensureCtor`'s collect-then-`struct.new` path `this` does not exist yet (`ctx.ctorFields` is set until the
				// last field is collected); a collected field read off `this` has its own shortcut in `case 'member'`.
				if (e.type === 'this' && ctx.ctorFields)
					throw `'this' can't be used yet in '${ctx.owner?.name}'s constructor -- it has at least one object-typed field, which needs every field's real value collected up front (for 'struct.new') before 'this' exists at all; assign every field via a plain 'this.field = value' statement before using 'this' any other way`;
				const place = resolvePlace(e, ctx);
				if (place)
					return emitPlaceRead(e, place, ctx);
				const fnValue = functionValueDecl(e, ctx);
				if (fnValue)
					return emitFunctionValue(fnValue, want, ctx);
				// CommonJS's per-module names (`checker.bindModuleNames`): compile-time constants, as a bundler substitutes them.
				if (name === '__dirname' || name === '__filename') {
					const file = moduleFilename(ctx.homeModule);
					if (file)
						return emitExpr(Literal(name === '__dirname' ? path.dirname(file) : file), ctx, want);
				}
				throw `unresolved identifier '${name}'`;
			}

			case 'member': {
				// An `enum` MEMBER folds to its constant: an enum has no runtime object (`enumMembers`).
				if (e.object.type === 'identifier') {
					const v = enumMembers.get(homeKey(ctx.homeModule, `${e.object.name}.${e.property}`));
					if (v !== undefined)
						return emitExpr(Literal(v), ctx, want);
					const owner = namespaceOwner(e.object.name, ctx);
					if (owner) {
						const f = owner.decl.body.find(m => m.type === 'field' && m.key === e.property && m.modifiers?.includes('static'));
						if (!f || f.type !== 'field' || !f.value)
							throw `unknown static field '${owner.name}.${e.property}'`;
						return emitExpr(f.value, ctx);
					}
					// `NS.x` through `import * as NS`, unless a local shadows `NS`: another module's lazy const, or a function read as a
					// value -- resolved in the target module as a namespace-qualified call is.
					const ns = ctx.lookup(e.object.name) ? undefined : ctx.scope.namespace(e.object.name);
					if (ns) {
						const lazy = lazyGlobalFor(e.property, ctx, ns);
						if (lazy) {
							ctx.emit(I.call(lazy.wrapper.funcIndex));
							return lazy.wrapper.result;
						}
						const fnValue = functionValueDecl(e, ctx);
						if (fnValue)
							return emitFunctionValue(fnValue, want, ctx);
					}
				}
				// Mid-construction, before a real `this` exists (`ensureCtor`), a collected field reads from its own scratch local.
				if (e.object.type === 'this' && ctx.ctorFields?.has(e.property)) {
					const local = ctx.ctorFields.get(e.property)!;
					ctx.emit(I.local.get(local.index));
					return local.wtype;
				}
				return emitPlaceRead(e, resolvePlace(e, ctx)!, ctx);
			}

			case 'index':
				return emitPlaceRead(e, resolvePlace(e, ctx)!, ctx);

			// The asserted type is compile-time-only: compile the inner expression and pass its actual `WasmType` straight through, ignoring the assertion.
			case 'as':
				// The asserted type is the expression's own context: `{ type: 'array', ... } as Expr` names the union
				// member to build, where an untargeted literal matches every same-shaped class in the program. `as const` names no type.
				return isConstContext(e.typeAnnotation) ? emitExpr(e.expression, ctx, want) : ctx.withContext(e.typeAnnotation, () => emitExpr(e.expression, ctx, want));

			// `f<A>` / `NS.f<A>` read as a VALUE (`ts-parser.ts`'s `export const CallSig = JS.CallSig<Type>`): the generic function instantiated at those type arguments,
			// as a closure. A call through one goes the same way.
			case 'instantiation': {
				const fnValue = functionValueDecl(e.expression, ctx);
				if (!fnValue)
					throw `'${T.exprKey(e.expression)}' with type arguments names no generic function`;
				return emitFunctionValue(fnValue, want, ctx, e.typeArgs);
			}

			// Every expression but the last runs purely for its side effects (`emitStmt`'s own `'void'`-then-`I.drop` idiom); only the last one's value (and `want`) matters.
			case 'sequence':
				for (let i = 0; i < e.expressions.length - 1; i++)
					emitDiscarded(e.expressions[i], ctx);
				return emitExpr(e.expressions[e.expressions.length - 1], ctx, want);

			// A ref-kind element (`string[]`, a class array, ...) needs `REF_ANY` as the per-element target -- `coerceTop`'s widen-to-`any` case boxes each one, not
			// the bare `kind` string, which only coincides with a real `WasmType` for scalar kinds.
			// `want` naming a real class wins outright; otherwise `matchObjectShape` resolves the literal structurally, against a declared interface/class first and
			// a freshly synthesized anonymous shape (`ensureAnonObjectShape`) only when no declared type matches. Fields push in the *shape's own declared order*
			// (`struct.new` needs every field value up front, in that fixed order), not the literal's written order -- looked up from its properties by name.
			case 'object': {
				// A declared shape first (the one `ownerFor` builds for that type), then the union-shaped literal, and an anonymous shape last: a discriminant
				// whose value is a union of literals fits no single member, and as anonymous it would build a struct no reader of the union tests for.
				const split = conditionalSpread(e, ctx);
				if (split)
					return emitExpr(split, ctx, want);
				const declared = (W.isRef(want) ? ensureClass(want.ref) : undefined)
					?? contextualDynamicOwner(e, ctx)
					?? matchContextualUnionMember(e, ctx)
					?? contextualShapeOwner(e, ctx)
					?? spreadOwner(e, ctx)
					?? matchObjectShape(e, ctx, false);
				if (!declared) {
					const variants = emitUnionShapedLiteral(e, ctx, want);
					if (variants)
						return variants;
				}
				const owner = declared ?? matchObjectShape(e, ctx);
				if (!owner) {
					// No shape is knowable here, but a spread of an `any` still has one at RUNTIME.
					const cloned = emitAnySpreadClone(e, ctx);
					if (cloned)
						return cloned;
					throw "an object literal needs a known target type (e.g. a 'const x: Point = {...}' with a plain 'type Point = {...}' alias) -- not supported here";
				}

				// A dynamic object (`{[k: string]: V}`) is its constructor plus one `set` per key. Without a spread, each `set`'s
				// returned `this` is the next one's receiver; a spread walks its operand's keys, so the object is held in a local.
				if (isDynamicObject(owner)) {
					const ctor = ensureCtor(owner, [], ctx);
					emitCallArgs(`${owner.name}'s constructor`, ctor.params, ctor.defaults, !!ctor.hasRest, [], ctx, ctor.resolvedParams);
					ctx.emit(I.call(ctor.funcIndex));
					const entry = (p: (typeof e.properties)[number]): Expr[] => {
						if (p.type !== 'field' || typeof p.key === 'object' || !p.value)
							throw `object literal for '${owner.name}' can only have plain 'key: value' properties (no methods or computed keys)`;
						return [Literal(String(p.key)), p.value];
					};
					if (!e.properties.some(p => p.type === 'spread')) {
						for (const p of e.properties)
							emitMethodCall(owner, 'set', entry(p), ctx);
						return owner.thisWtype!;
					}
					const n			= ctx.tempCounter++;
					const mapName	= `#dynobj$${n}`;
					const mapLocal	= ctx.declareValue(mapName, owner.thisWtype!, owner.thisTsType!);
					ctx.emit(I.local.set(mapLocal.index));
					let spreadIndex = 0;
					for (const p of e.properties) {
						if (p.type === 'spread') {
							const srcCls = ownerOf(p.operand, ctx);
							if (srcCls && !isDynamicObject(srcCls)) {
								const srcName	= `#spread$${n}$${spreadIndex++}`;
								const srcLocal	= ctx.declareValue(srcName, srcCls.thisWtype!, srcCls.thisTsType!);
								emitSpreadOperand(p.operand, ctx, srcCls.thisWtype!);
								ctx.emit(I.local.set(srcLocal.index));
								for (const key of srcCls.fieldIndex.keys()) {
									ctx.emit(I.local.get(mapLocal.index));
									emitMethodCall(owner, 'set', [Literal(key), JS.Member(Identifier(srcName), key)] as Expr[], ctx);
								}
								continue;
							}
							const spreadName	= `#spread$${n}$${spreadIndex}`;
							const kName			= `#spreadkey$${n}$${spreadIndex++}`;
							const spreadLocal	= ctx.declareValue(spreadName, owner.thisWtype!, owner.thisTsType!);
							emitSpreadOperand(p.operand, ctx, owner.thisWtype!);
							ctx.emit(I.local.set(spreadLocal.index));
							emitStmt({
								type: 'for', kind: 'of',
								init: JS.VarDecl('const', JS.Var(kName)),
								right: JS.Call(JS.Member(Identifier(spreadName), 'keys'), []),
								body: JS.Block({
									type: 'expression', expression: {
										type: 'call',
										callee: JS.Member(Identifier(mapName), 'set'),
										arguments: [Identifier(kName), JS.Call(JS.Member(Identifier(spreadName), 'get'), [Identifier(kName)])],
									},
								}),
							} as Stmt, ctx);
							continue;
						}
						const args = entry(p);
						ctx.emit(I.local.get(mapLocal.index));
						if (emitMethodCall(owner, 'set', args, ctx) !== 'void')
							ctx.emit(I.drop);
					}
					ctx.emit(I.local.get(mapLocal.index));
					return owner.thisWtype!;
				}

				// Each spread operand is evaluated once, into a local, and only the fields this class declares are read back off it.
				interface FieldSource { expr?: Expr; method?: JS.Method<Type>; spreadLocal?: W.Local; spreadCls?: ClassInfo; unionCls?: ClassInfo[]; dynamic?: TS.ObjectType[]; nullable?: boolean }
				// Every source for a field, in written order -- not just the last one. `{...D, ...opts}` is the reason: an OPTIONAL property of a later operand is only
				// "last wins" when it is actually present at runtime, so an absent one has to fall back to whatever came before it.
				const sources = new Map<string, FieldSource[]>();
				const addSource = (key: string, src: FieldSource) => sources.set(key, [...(sources.get(key) ?? []), src]);
				for (const p of e.properties) {
					if (p.type === 'spread') {
						// An anonymous object shape has no nominal class for `ownerOf` to find, so it gets the same synthesized struct a literal targeting that shape would.
						const spreadT	= T.resolve(ctx.scope, ctx.narrowedTypeOf(p.operand));
						// An OPEN shape holds any layout, so it has no struct to read fields off -- not even a synthesized one, which the
						// value would have to be cast to. Its keys are read by name below, as a union member stored as `any` is.
						const spreadCls	= ownerOf(p.operand, ctx) ?? (spreadT.type === 'object' && !openShapes.has(openKey(spreadT, global)) ? ensureAnonObjectShape(spreadT) : undefined);
						// A NULLABLE operand is one too (`{ ...more }`, `more?: Partial<Decl>`): spreading `undefined` supplies nothing.
						if (!spreadCls || T.unionMembers(spreadT, ctx.scope).some(m => T.isNullish(m, ctx.scope))) {
							// A union operand reads each field off whichever member the value is, absent where it has none. A member stored as `any` (an open shape)
							// has no struct to test for, so each key its type names is read at run time, by name.
							const parts		= T.unionMembers(spreadT, ctx.scope);
							const solid		= parts.filter(m => !T.isNullish(m, ctx.scope));
							const owners	= spreadT.type === 'union' ? solid.flatMap(m => flattenOwners(m, ctx.scope) ?? [undefined]) : [];
							const unionCls	= owners.length && owners.every((o): o is ClassInfo => !!o && o.typeIndex !== -1) ? owners : undefined;
							const shapes	= solid.map(m => T.resolveObjectType(m, ctx.scope));
							const dynamic	= !unionCls && solid.length && shapes.every((m): m is TS.ObjectType => !!m) ? shapes : undefined;
							// An `any` operand names no keys, so the target's are read by name at run time (`dynamic: []`); it may hold `undefined`, so it is
							// always nullable.
							const anyOperand = !unionCls && !dynamic && T.isAny(spreadT);
							if (!unionCls && !dynamic && !anyOperand)
								throw `object literal for '${owner.name}': a spread operand needs a known object type, got '${T.typeKey(spreadT)}'`;
							const spreadLocal = ctx.declareLocal(`$spread$${ctx.tempCounter++}`, W.REF_ANY_NULLABLE);
							emitSpreadOperand(p.operand, ctx, W.REF_ANY_NULLABLE);
							ctx.emit(I.local.set(spreadLocal.index));
							const src: FieldSource = { spreadLocal, unionCls, dynamic: anyOperand ? [] : dynamic, nullable: anyOperand || solid.length < parts.length };
							const keys = unionCls ? unionCls.flatMap(m => m.fields.map(f => f.name))
								: anyOperand ? owner.fields.filter(f => !f.name.startsWith('#')).map(f => f.name)
								: dynamic!.flatMap(m => m.members.map(k => k.type === 'property' && T.memberKey(k.key)).filter((k): k is string => !!k));
							for (const name of new Set(keys))
								addSource(name, src);
							continue;
						}
						const spreadLocal = ctx.declareValue(`$spread$${ctx.tempCounter++}`, spreadCls.thisWtype!, spreadCls.thisTsType!);
						emitSpreadOperand(p.operand, ctx, spreadCls.thisWtype!);
						ctx.emit(I.local.set(spreadLocal.index));
						for (const f of spreadCls.fields)
							addSource(f.name, { spreadLocal, spreadCls });
						continue;
					}
					const src: FieldSource | undefined = p.type === 'field' ? p.value && { expr: p.value } : { method: p };
					if (typeof p.key === 'object' || !src)
						throw `object literal for '${owner.name}' can only have plain 'key: value' properties, methods, accessors or a spread (no computed keys)`;
					// An accessor is a closure in the key's `#get:`/`#set:` companion, which every read and write of the key consults.
					const slot = p.type === 'get' || p.type === 'set' ? `#${p.type}:${p.key}` : String(p.key);
					if (!owner.fieldIndex.has(slot))
						throw `object literal for '${owner.name}' has unknown property '${p.key}'`;
					addSource(slot, src);
				}
				// "Certain" means the source always yields a value: an explicit `k: v`, a spread of a field that isn't optional, or -- for a union spread -- a field every
				// member declares and none optionally, with a never-nullish operand.
				const certain	= (src: FieldSource, name: string) => !!src.expr || !!src.method || (src.dynamic
					? !src.nullable && src.dynamic.every(o => o.members.some(m => m.type === 'property' && T.memberKey(m.key) === name && !hasMod(m, 'optional')))
					: src.unionCls
					? !src.nullable && src.unionCls.every(m => { const i = m.fieldIndex.get(name); return i !== undefined && !m.fields[i].optional; })
					: !src.spreadCls!.fields[src.spreadCls!.fieldIndex.get(name)!].optional);
				const rawWtype	= (src: FieldSource, name: string) => src.spreadCls!.fields[src.spreadCls!.fieldIndex.get(name)!].wtype;
				const readSpread = (src: FieldSource, name: string, want: W.Type): void => {
					if (src.dynamic) {
						const read = () => {
							ctx.emit(I.local.get(src.spreadLocal!.index), I.ref.as_non_null, I.call(ensureAnyField(name).funcIndex));
							coerceTop(W.REF_ANY_NULLABLE, ctx, want);
						};
						// A slot with no zero is this key's only source, which the program's type promised: an absent key traps in the read's cast
						// rather than inventing a value.
						if (!src.nullable || !ctx.hasDefaultValue(want, toValType))
							return read();
						ctx.emit(I.local.get(src.spreadLocal!.index), I.ref.is_null);
						return void ctx.emitIf(toValType(want), () => ctx.emitDefaultValue(want, types, toValType), read);
					}
					if (!src.unionCls) {
						const idx = src.spreadCls!.fieldIndex.get(name)!;
						ctx.emit(I.local.get(src.spreadLocal!.index));
						emitFieldRead(src.spreadCls!, idx, ctx);
						coerceTop(src.spreadCls!.fields[idx].wtype, ctx, want);
						return;
					}
					const members = src.unionCls;
					const arm = (i: number): wasm.Instr[] => {
						if (i >= members.length)
							return [I.unreachable];
						const m = members[i], idx = m.fieldIndex.get(name);
						ctx.emit(I.local.get(src.spreadLocal!.index), I.ref.test(m.typeIndex));
						const _cond = ctx.swapOut();
						if (idx === undefined) {
							ctx.emitDefaultValue(want, types, toValType);
						} else {
							ctx.emit(I.local.get(src.spreadLocal!.index), I.ref.cast(m.typeIndex));
							emitFieldRead(m, idx, ctx);
							coerceTop(m.fields[idx].wtype, ctx, want);
						}
						return [..._cond, I.if(toValType(want), ctx.swapOut(), arm(i + 1))];
					};
					if (!src.nullable)
						return void ctx.emit(...arm(0));
					ctx.emit(I.local.get(src.spreadLocal!.index), I.ref.is_null);
					ctx.emitIf(toValType(want), () => ctx.emitDefaultValue(want, types, toValType), () => ctx.emit(...arm(0)));
				};
				// A spread copies VALUES: JS reads each property through [[Get]] into a plain data property, so an accessor's getter never carries over -- the key's own
				// read (`emitFieldRead`) already called it, and the copy's slot stays empty.
				const copiesGetter = (f: { name: string }) => f.name.startsWith('#get:') || f.name.startsWith('#set:');
				// A method that uses `this` captures a holder the finished object is stored into, since the closure is built before the struct it belongs to.
				const thisHolder = [...sources.values()].some(c => c.some(s => s.method && usesThis(s.method)))
					? { holder: declareHolder(ctx, `#this$${ctx.tempCounter++}`, owner.thisWtype!, owner.thisTsType!), tsType: owner.thisTsType! }
					: undefined;
				const emitOne	= (src: FieldSource, f: { name: string; wtype: W.Type }) => {
					if (!src.expr && !src.method && copiesGetter(f))
						return void ctx.emitDefaultValue(f.wtype, types, toValType);
					if (src.method) {
						coerceTop(emitClosureLiteral(src.method, ctx, false, f.wtype, usesThis(src.method) ? thisHolder : undefined), ctx, f.wtype);
					} else if (src.expr) {
						// The field's declared type is the value's context: a nested literal picks its union member from it.
						ctx.withContext(owner.fieldDeclaredType(f.name, global), () => emitAs(src.expr!, ctx, f.wtype));
					} else {
						readSpread(src, f.name, f.wtype);
					}
				};
				// `last ?? (the one before it ?? ...)`, lowered like the `??` operator.
				const emitChain = (chain: FieldSource[], f: { name: string; wtype: W.Type }): void => {
					if (copiesGetter(f) && !chain[chain.length - 1].method)
						return void ctx.emitDefaultValue(f.wtype, types, toValType);
					const last = chain[chain.length - 1];
					if (chain.length === 1 || certain(last, f.name))
						return emitOne(last, f);
					const srcWtype	= last.dynamic ? W.REF_ANY_NULLABLE : last.unionCls ? types.nullable(f.wtype) : rawWtype(last, f.name);
					const tmp		= ctx.declareLocal(`$spread$${f.name}$${ctx.tempCounter++}`, srcWtype);
					readSpread(last, f.name, srcWtype);
					ctx.emit(I.local.tee(tmp.index), I.ref.is_null);
					ctx.emitIf(toValType(f.wtype), () => emitChain(chain.slice(0, -1), f), () => {
						ctx.emit(I.local.get(tmp.index));
						coerceTop(srcWtype, ctx, f.wtype);
					});
				};
				for (const f of owner.fields) {
					const chain = sources.get(f.name);
					if (!chain?.length) {
						if (!f.optional)
							throw `object literal for '${owner.name}' is missing property '${f.name}'`;
						ctx.emitDefaultValue(f.wtype, types, toValType);
					} else {
						// Trim before the last certain source: it can never be observed.
						const from = chain.reduce((acc, src, i) => certain(src, f.name) ? i : acc, 0);
						emitChain(chain.slice(from), f);
					}
				}
				ctx.emit(I.struct.new(owner.typeIndex));
				if (thisHolder) {
					const self = ctx.declareLocal(`$self$${ctx.tempCounter++}`, owner.thisWtype!);
					ctx.emit(I.local.set(self.index), I.local.get(thisHolder.holder.index), I.local.get(self.index), I.struct.set((thisHolder.holder.wtype as { typeIndex: number }).typeIndex, 0), I.local.get(self.index));
				}
				return owner.thisWtype!;
			}

			case 'array': {
				// `want`'s own kind wins whenever it asks for something boxable-as-`any`, either directly (`{arr:'ref'}`, a real `any[]` target) or because this literal
				// is itself about to be boxed as one `anyref` value (`const values: any[] = [1, 2, 3]`) -- `arrayKindOf` only sees the elements, so it would otherwise
				// build a real `number[]`, and a scalar-kind wasm array and a ref-kind one are physically incompatible types (not just a missing cast).
				//
				// The `{ref:'any'}` case covers one more shape: a literal merely an *element* of an outer ref-kind array (`[1,2]` inside `number[][]`), where the array
				// reference itself upcasts to `anyref` for free and only its elements would need boxing if it were genuinely `any`-typed, which it isn't --
				// `ctx.contextualReturn` says `number[]`, not `any[]`. Force boxed storage only when that contextual type is itself `any`/unknown or unavailable.
				// The wanted STORAGE kind: either `want` is the storage itself, or it is a class that owns some (an `Array<T>`), whose single field says which --
				// an empty literal has no elements to infer from and would otherwise default to boxed-`any`.
				const wantArr = storageKindOf(want);
				// A union context names the literal's own member, as the checker takes it (`string | number[]`): reads narrowed to that member expect its representation.
				const contextual	= ctx.contextualReturn && T.resolve(ctx.scope, ctx.contextualReturn);
				const arrayMembers	= contextual?.type === 'union' ? T.unionMembers(contextual, ctx.scope).map(m => T.resolve(ctx.scope, m)).filter(m => m.type === 'array') : [];
				const contextualArr = arrayMembers.length === 1 ? arrayMembers[0] : contextual;
				const contextualElement = contextualArr?.type === 'array' ? contextualArr.element : undefined;
				const contextForcesAny = !contextualElement || T.isAny(T.resolve(ctx.scope, contextualElement));
				// An empty literal has no elements for `arrayKindOf` to read and the checker types it `never[]`/`any[]` (always 'ref'): `want`'s kind, else the CONTEXTUAL
				// element type, which is what its non-empty sibling would infer (`[]` beside `[1,2]` in `number[][]` must be the same `f64` array, not boxed-`any`).
				// A slot naming its storage is what the literal is built AS (a `u8[]` is packed bytes), whatever its elements' own kind.
				const contextKind = contextualElement && (e.elements.length === 0 || !contextForcesAny) ? rawElemKind(contextualElement, typeOf) : undefined;
				const kind = wantArr === 'ref' || (W.isAny(want) && contextForcesAny) ? 'ref' : wantArr ?? contextKind ?? arrayKindOf(e, ctx);
				if (!kind)
					throw 'array literals are only supported for number[]/boolean[]/T[]';
				emitArrayElements(e.elements, ctx, elementValueType(kind), kind, types.array(kind), contextualElement);
				return W.ARRAY[kind];
			}

			case 'unary': {
				if (e.operator === '++' || e.operator === '--')
					return emitIncDec(e.operand, e.operator, false, ctx, want);

				// `delete obj[k]`, like `++`/`--`, needs the target's own object+key rather than its evaluated value, so it gets its own branch before the generic
				// operand dispatch below. Only a dynamic object has a real `delete` to dispatch to.
				if (e.operator === 'delete') {
					if (e.operand.type !== 'index' && e.operand.type !== 'member')
						throw "'delete' is only supported on a property ('delete obj[k]' or 'delete obj.p')";
					const object	= e.operand.object;
					const key: Expr	= e.operand.type === 'index' ? e.operand.index : Literal(e.operand.property);
					const cls		= classOfForIndexing(object, ctx);
					if (cls && isDynamicObject(cls)) {
						emitAs(object, ctx, cls.thisWtype!);
						return emitMethodCall(cls, 'delete', [key], ctx);
					}
					if (T.isAny(ctx.narrowedTypeOf(object))) {
						emitAs(object, ctx, W.REF_ANY);
						emitAs(T.isNumberLike(ctx.narrowedTypeOf(key), ctx.scope) ? JS.Call(Identifier('String'), [key]) : key, ctx, typeOf(T.STRING)!);
						ctx.emit(I.call(ensureAnyKey('delete').funcIndex));
						return 'i32';
					}
					// A struct cannot lose a slot, and an absent optional field is already one holding `undefined` (an omitted literal
					// field), so deleting stores that. A required field has no such state: its non-null cast traps, as TS forbids it.
					// A union of structs boxed as one `anyref` counts; a value typed `any` may be a dynamic object, where that is no delete.
					if (!(cls && cls.typeIndex !== -1 && cls.fields.length) && !(physicallyAny(object, ctx) && !T.isAny(ctx.narrowedTypeOf(object))))
						throw "'delete' is only supported on a struct's field or a dynamic object's key";
					emitExpr(Assign<Expr, never>(e.operand, Identifier('undefined')), ctx, 'void');
					ctx.emit(I.i32.const(1));
					return 'i32';
				}

				const info = operandInfo(e.operand, ctx);
				const nativeBig = emitNativeBigint(e.operator === '-' ? 'neg' : undefined, [{ expr: e.operand, wtype: info.wtype }], e, ctx);
				if (nativeBig)
					return nativeBig;
				if (info.owner) {
					const method = UNARY_OP_NAMES[e.operator as keyof typeof UNARY_OP_NAMES];
					if (method && info.owner.methodDecls?.get(method)) {
						emitAs(e.operand, ctx, info.owner.thisWtype!);
						return emitMethodCall(info.owner, method, [], ctx);
					}
				}

				// A bare `typeof x` as a VALUE: the tag itself when the checker's type gives every inhabitant the same one, else a run-time cascade over the tags its
				// type allows (`emitTypeofValue`).
				if (e.operator === 'typeof') {
					const known = T.typeofName(ctx.narrowedTypeOf(e.operand), ctx.scope);
					if (known !== undefined) {
						emitDiscarded(e.operand, ctx);
						return emitExpr(Literal(known), ctx, want);
					}
					return emitTypeofValue(e.operand, ctx);
				}

				// `!x` is exactly "is x falsy", so it answers for every operand shape `emitTruthy` understands -- a nullable object reference, a string (empty is
				// falsy), an array, a scalar -- not just the scalar-kinded ones. The old scalar-only path also coerced the operand to `i32` first, which TRUNCATED a real
				// `f64`: `!0.5` came out `true`.
				if (e.operator === '!') {
					emitTruthy(e.operand, ctx);
					ctx.emit(I.i32.eqz);
					return 'i32';
				}

				// `+s` is ToNumber, which for a string is exactly `Number(s)`: the lib wrapper's string constructor parses it (trimmed, '' is 0, trailing junk is NaN).
				if (e.operator === '+' && T.typeofName(ctx.narrowedTypeOf(e.operand), ctx.scope) === 'string')
					return emitExpr(JS.Call(Identifier('Number'), [e.operand]), ctx, want);
				const t = W.notUnsigned(W.scalarKind(info.wtype));
				if (t) {
					switch (e.operator) {
						case '-': {
							// A 32-bit negation only where the checker proved the result an int: `-0` is a float's alone.
							const nt = t === 'i32' && !isInt32(typeOf(ctx.typeAt(e, false))) ? 'f64' : t;
							if (nt === 'i64' || nt === 'i32') {
								ctx.emit(I[nt](0));
								emitAs(e.operand, ctx, nt);
								ctx.emit(I[nt].sub);
							} else {
								emitAs(e.operand, ctx, nt);
								ctx.emit(I[nt].neg);
							}
							return nt;
						}
						case '+':
							emitAs(e.operand, ctx, t);
							return t;
						case '~':
							emitAs(e.operand, ctx, 'i32');
							ctx.emit(I.i32(-1), I.i32.xor);
							return 'i32';
					}
				}
				throw `unsupported unary operator '${e.operator}'`;
			}

			case 'unary_post':
				if (e.operator === '!')
					return emitExpr(e.operand, ctx, want);
				if (e.operator === '++' || e.operator === '--')
					return emitIncDec(e.operand, e.operator, true, ctx, want);
				throw `unsupported postfix operator '${e.operator}'`;

			case 'assign': {
				const { operator, target, value } = e;

				return ctx.inScope((): W.Type => {
					const slot		= emitAssignTarget(target, ctx, operator ? 'discard' : 'none');
					const wtype		= slot.wtype;

					// The target's own declared type is the value's contextual type -- the same channel `case 'var_decl'` seeds from an annotation, which a bare `new C` on
					// the value needs to find its own type arguments (`scope.resolveCache ??= new WeakMap`).
					const emitValue = () => {
						const saved = ctx.contextualReturn;
						ctx.contextualReturn = checkerTypeOf(target, ctx.scope);
						emitAs(value, ctx, wtype);
						ctx.contextualReturn = saved;
					};

					// Both arms unbraced: a braced `if` with a bare `switch` for its `else` is the one shape `custom-control-block-style` rejects.
					if (!operator)
						emitValue();
					else switch (operator) {
						case '&&':
						case '||':
						case '??':
							if (operator === '??' && !W.isNullable(wtype))
								throw "'??=' needs a nullable object-typed target (no boxing in this subset)";
							emitShortCircuit(operator, wtype, ctx.narrowedTypeOf(target), wtype, emitValue, held => ctx.emit(I.local.get(held.index)), ctx);
							break;

						default: {
							// The operator's own decision over the old value held by name, its result typed as the assignment's (a step's range for `+=`).
							const old = `$compound$${ctx.tempCounter++}`;
							ctx.emit(I.local.set(ctx.declareValue(old, wtype, ctx.narrowedTypeOf(target)).index));
							emitAs(Object.assign(Binary(operator, Identifier(old), value), { checkedType: ctx.typeAt(e, false) }), ctx, wtype);
						}
					}

					const tee = want !== 'void';
					slot.write(tee);
					return tee ? wtype : 'void';
				});
			}

			case 'binary': {
				const { operator, left, right } = e;
				if (operator === '===' || operator === '!==' || operator === '==' || operator === '!=') {
					const asTypeof = (a: Expr, b: Expr) => a.type === 'unary' && a.operator === 'typeof'
						&& b.type === 'literal' && typeof b.value === 'string' ? { operand: a.operand, tag: b.value } : undefined;
					const test = asTypeof(left, right) ?? asTypeof(right, left);
					if (test && emitTypeofTest(test.operand, test.tag, ctx)) {
						if (operator === '!==' || operator === '!=')
							ctx.emit(I.i32.eqz);
						return 'i32';
					}
				}
				const rightInfo = operandInfo(right, ctx);


				switch (operator) {
					// `a && b`, `a || b` and `a ?? b` yield an OPERAND, not a boolean (`0.5 && 7` is `7`); `emitTruthy` keeps the boolean form for a condition.
					case '&&':
					case '||':
					case '??': {
						// As a statement only the short-circuit is observable, and neither operand needs a value (`a && f()` with a `void` `f`).
						if (want === 'void' && operator !== '??') {
							emitTruthy(left, ctx);
							if (operator === '||')
								ctx.emit(I.i32.eqz);
							ctx.emitIf(undefined, () => emitDiscarded(right, ctx));
							return 'void';
						}
						const leftWtype		= wtypeOf(left, ctx);
						const rightWtype	= operator === '??' ? undefined : wtypeOf(right, ctx);
						if (!leftWtype || leftWtype === 'void' || rightWtype === 'void')
							throw `'${operator}' needs both operands to have a representable value type`;
						// Both sides' form when they agree, else the whole expression's type (the checker's alone can be narrower than both operands).
						// A right with no representation of its own (a bare `undefined`) is emitted into that type, as a conditional's branch is.
						const self = rightWtype && W.typeEq(leftWtype, rightWtype) ? leftWtype : wtypeOf(e, ctx);
						if (!self)
							throw `'${operator}' has an unsupported result type`;
						// An object-shaped result is BUILT at the caller's type: struct fields are invariant, so a literal operand can't be converted afterwards.
						const wtype = wantedShape(want, self);
						// A left that is never nullish makes the right of `??` dead code, as TS concludes (`emitPatternBinding`'s defaults rely on it).
						if (operator === '??' && !W.isNullable(leftWtype)) {
							emitAs(left, ctx, wtype);
							return wtype;
						}
						emitAs(left, ctx, leftWtype);
						emitShortCircuit(operator, leftWtype, ctx.narrowedTypeOf(left), wtype, () => emitAs(right, ctx, wtype), held => {
							// When the kept part of the left is only null/undefined, the result is its type's own `undefined`, not the left's physical value.
							if (T.isNullish(T.logicalLeftPart(ctx.narrowedTypeOf(left), operator, ctx.scope), ctx.scope))
								return void emitAs(Identifier('undefined'), ctx, wtype);
							ctx.emit(I.local.get(held.index));
							coerceTop(leftWtype, ctx, wtype);
						}, ctx);
						return wtype;
					}

					// A `ref.test` against the non-nullable struct, so `null instanceof C` is false. One rec group for every struct is what lets it tell
					// structurally identical sibling classes apart.
					case 'instanceof': {
						if (right.type !== 'identifier')
							throw "'instanceof' is only supported against a plain class name";
						const cls = ensureClass(right.name, undefined, ctx.scope);
						if (!cls)
							throw `'instanceof' against unknown class '${right.name}'`;
						const leftWtype = wtypeOf(left, ctx);
						if (!leftWtype || typeof leftWtype === 'string')
							throw "'instanceof' needs an object-typed left-hand value";
						// Each instantiation of a generic class is its own struct, and `instanceof C` is true for all of them.
						if (cls.instantiation) {
							emitAs(left, ctx, W.REF_ANY_NULLABLE);
							ctx.emit(I.call(ensureInstanceTest(cls).funcIndex));
							return 'i32';
						}
						emitAs(left, ctx, leftWtype);
						ctx.emit(I.ref.test(cls.typeIndex));
						return 'i32';
					}

					case 'in': {
						// On a union, `'k' in u` is a TYPE test: which member `u` is. A member declaring `k` optionally counts, as in TS's narrowing: a field is
						// always physically present, so an omitted optional property cannot be told from a set one.
						const key = left.type === 'literal' && typeof left.value === 'string' ? left.value : undefined;
						const flat = key === undefined ? [] : T.unionMembers(checkerTypeOf(unwrapAs(right), ctx.scope), ctx.scope)
							.filter(m => !T.isNullish(m, ctx.scope));
						if (key !== undefined && flat.length > 1) {
							const owners = flat.map(m => ownerFor(m));
							const state = owners.map(o => {
								if (!o || o.typeIndex === -1)
									return undefined;
								const idx = o.fieldIndex.get(key);
								return { o, has: idx !== undefined };
							});
							if (state.every(x => !!x)) {
								const declaring = state.filter(x => x!.has).map(x => x!.o);
								if (!declaring.length || declaring.length === state.length) {
									emitDiscarded(right, ctx);
									ctx.emit(I.i32.const(declaring.length ? 1 : 0));
									return 'i32';
								}
								const recv = ctx.declareLocal(`$in$${ctx.tempCounter++}`, W.REF_ANY_NULLABLE);
								emitAs(right, ctx, W.REF_ANY_NULLABLE);
								ctx.emit(I.local.set(recv.index));
								declaring.forEach((o, i) => {
									ctx.emit(I.local.get(recv.index), I.ref.test(o.typeIndex));
									if (i)
										ctx.emit(I.i32.or);
								});
								return 'i32';
							}
						}
						const cls = ownerOf(right, ctx);
						if (!cls?.methodDecls.get('has')) {
							// The runtime struct decides, since a value typed as a base may be a subtype declaring the key; a scalar or array receiver is an error.
							if (W.isRef(wtypeOf(right, ctx))) {
								if (key === undefined)
									emitAs(left, ctx, typeOf(T.STRING)!);
								emitAs(right, ctx, W.REF_ANY_NULLABLE);
								ctx.emit(I.call(ensureAnyIn(key).funcIndex));
								return 'i32';
							}
							throw "'in' is only supported over a dynamic object (a structural '{[k: string]: V}'-typed value)";
						}
						emitAs(right, ctx, cls.thisWtype!);
						return emitMethodCall(cls, 'has', [left], ctx);
					}

					case '==': case '===': case '!=': case '!==': {
						const negate		= operator[0] === '!';
						const leftIsNull	= T.isNullLiteral(left);
						const rightIsNull	= T.isNullLiteral(right);
						if (leftIsNull || rightIsNull) {
							if (leftIsNull && rightIsNull) {
								ctx.emit(I.i32.const(negate ? 0 : 1));
								return 'i32';
							}
							const valueExpr	= leftIsNull ? right : left;
							const wt		= wtypeOf(valueExpr, ctx);
							if (!W.isNullable(wt))
								throw "comparing to 'null'/'undefined' needs a nullable object-typed value on the other side";
							// `null` and `undefined` are both `ref.null`, so a strict comparison separates them only statically: when the type carries the other kind
							// and not this one. Never for a type carrying neither: a missing `{[k: string]: V}` key is a physical `undefined` its type denies.
							if (operator.length === 3) {
								const kind	= T.nullLiteralKind(leftIsNull ? left : right)!;
								const t		= T.resolve(ctx.scope, ctx.narrowedTypeOf(valueExpr));
								const members = T.isAny(t) ? [] : t.type === 'union' ? T.unionMembers(t, ctx.scope) : [t];
								const has	= (want: 'null' | 'undefined') => !members.length || members.some(m => {
									const r = T.resolveOwn(m, ctx.scope);
									return want === 'null'
										? r.type === 'literal' && r.value === null
										: r.type === 'ref' && (r.name === 'undefined' || r.name === 'void');
								});
								if (!has(kind) && has(kind === 'null' ? 'undefined' : 'null')) {
									emitDiscarded(valueExpr, ctx);
									ctx.emit(I.i32.const(negate ? 1 : 0));
									return 'i32';
								}
							}
							emitAs(valueExpr, ctx, wt);
							ctx.emit(I.ref.is_null);
							if (negate)
								ctx.emit(I.i32.eqz);
							return 'i32';
						}
					}
					//fall through
					default: {
						const leftInfo	= operandInfo(left, ctx);
						const method	= BINARY_OP_NAMES[operator as keyof typeof BINARY_OP_NAMES];
						const equality	= method === 'eq' || method === 'ne';
						const identity	= (w: W.Type, test: () => void): W.Type => {
							emitAs(left, ctx, w);
							emitAs(right, ctx, w);
							test();
							if (method === 'ne')
								ctx.emit(I.i32.eqz);
							return 'i32';
						};

						// A boxed `any` or a nullable ref on either side: `===` is decided at run time, and a method (`String.eq`) would trap on null.
						const isRuntimeEq = (w: W.Type | undefined) => W.isAny(w) || W.isNullable(w);
						if (equality && (isRuntimeEq(leftInfo.wtype) || isRuntimeEq(rightInfo.wtype)))
							return identity(W.REF_ANY_NULLABLE, () => ctx.emit(I.call(ensureAnyStrictEq().funcIndex)));

						// `**` has no instruction, so a numeric one is `Math.pow`; an owner with its own `pow` (`BigInt`) dispatches to it below.
						if (method === 'pow' && !leftInfo.owner?.methodDecls?.get(method))
							return emitExpr(JS.Call(JS.Member(Identifier('Math'), 'pow'), [left, right]), ctx, want);

						// `+` concatenates when exactly one side is a string, as the template literal `${a}${b}` does, through its one stringifier.
						// A `string | number` operand is decided at run time, which this cannot model, so only all-string members count.
						if (method === 'add') {
							const definitelyString = (x: Expr) => {
								const ms = T.unionMembers(T.resolve(ctx.scope, ctx.narrowedTypeOf(x)), ctx.scope);
								return ms.length > 0 && ms.every(m => T.isStringLike(m, ctx.scope));
							};
							if (definitelyString(left) !== definitelyString(right))
								return emitExpr(Literal([{ str: '', exp: left }, { str: '', exp: right }]), ctx, want);
						}

						const nativeBig = emitNativeBigint(method, [{ expr: left, wtype: leftInfo.wtype }, { expr: right, wtype: rightInfo.wtype }], e, ctx);
						if (nativeBig)
							return nativeBig;
						const lk = W.scalarKind(leftInfo.wtype), rk = W.scalarKind(rightInfo.wtype);

						const owner = leftInfo.owner;
						if (owner?.methodDecls?.get(method)) {
							emitAs(left, ctx, owner.thisWtype!);
							return emitMethodCall(owner, method, [right], ctx);
						}
						if ((equality || method === 'lt' || method === 'gt' || method === 'le' || method === 'ge') && owner?.methodDecls?.get('compare')) {
							emitAs(left, ctx, owner.thisWtype!);
							const w = W.notUnsigned(W.scalarKind(emitMethodCall(owner, 'compare', [right], ctx)));
							if (!w)
								throw 'result of compare must be a scalar';
							if ((w === 'i32' || w === 'i64') && equality) {
								if (method === 'eq')
									ctx.emit(I[w].eqz);
								return w;
							}
							ctx.emit(I[w](0));
							const inline = numericOpInline(method, w, w, ctx);
							ctx.emit(...inline.inline);
							return inline.result;
						}

						if (equality && leftInfo.wtype && !lk && !rk)
							return identity(leftInfo.wtype, () => ctx.emit(I.ref.eq));

						const inline	= numericOpInline(method, leftInfo.wtype, rightInfo.wtype, ctx, typeOf(ctx.typeAt(e, false)));
						// Only a float operand needs the real `ToInt32` sequence; an `i32`/`u32` one is its own low 32 bits.
						const asInt32	= (x: Expr, w: W.Type | undefined, want: W.Type) =>
							BITWISE_METHODS.has(method) && want === 'i32' && (W.scalarKind(w) === 'f64' || W.scalarKind(w) === 'f32')
								? emitToInt32(x, ctx)
								: emitAs(x, ctx, want);
						asInt32(left, leftInfo.wtype, inline.params[0]);
						asInt32(right, rightInfo.wtype, inline.params[1]);
						ctx.emit(...inline.inline);
						return inline.result;
					}
				}
			}

			case 'conditional': {
				// `want`, when the caller has one, not just this expression's own self-inferred type -- self-inference can legitimately pick a *narrower* physical
				// representation than the context needs (a small integer literal branch of a `number | null` conditional self-infers as an `i32` box, not the `f64` box
				// the declared type uses), and both branches need to agree with whatever the caller will consume.
				const wtype = want ?? wtypeOf(e, ctx);
				if (!wtype)
					throw 'conditional expression has an unsupported type';
				emitTruthy(e.test, ctx);
				ctx.emitIf(toValType(wtype),
					() => emitAs(e.consequent, ctx, wtype),
					() => emitAs(e.alternate, ctx, wtype));
				return wtype;
			}

			case 'new':
			case 'call':
				return emitCallee(classifyCall(e, ctx, want), e, ctx, want, callContext);

			// `` tag`Hello ${name}` `` -- synthesized as `tag(strings, ...values)` and re-entered via `emitExpr`, so it reuses the
			// ordinary `case 'call'` path below and coercion comes free from `emitCallArgs`.
			// `.raw` isn't modeled: the strings are a plain cooked-text `string[]` (`case 'literal'`'s own untagged handling),
			// so a tag typed against `TemplateStringsArray` isn't supported -- typing the parameter `string[]` works.
			case 'tagged_template': {
				// `e.quasi` has no trailing empty-string part when the template ends right after a `${...}` (no text after) -- the
				// same gap `case 'literal'`'s own untagged handling pads for (`hasTrailingLiteral`), so `strings.length` is interpolation count + 1.
				const strings = e.quasi.map(p => Literal(p.str));
				if (e.quasi[e.quasi.length - 1].exp)
					strings.push(Literal(''));
				return emitExpr(JS.Call(
					e.tag,
					[JS.ArrayLit(strings), ...e.quasi.filter(p => p.exp).map(p => p.exp!)],
				) as Expr, ctx, want);
			}

			// Closures: a captured arrow/function-expression literal compiles to a 2-field `{code, env}`
			// wasm-GC struct -- building it here is "closure creation"; `case 'call'` handles *using* the result. v1 restrictions are all explicit throws, never silent misbehavior.
			case 'arrow':
			case 'function': {
				const target = W.isRef(want) ? classes.get(want.ref) : undefined;
				return target?.callable ? emitCallableObject(target, e, [], ctx) : emitClosureLiteral(e, ctx, false, want);
			}

			default:
				throw `unsupported expression '${e.type}'`;
		} } catch (err) {
			throw new W.Error(err as any, e).inModule(ctx.homeModule);
		}
	}

	// ===================================================================
	//  Statement lowering
	// ===================================================================

	// The ordinary `return` -- a plain function/method/arrow with no generator/async/constructor/`reassignsThis` override of `ctx.onReturn`; shared rather than a
	// `FunctionContext` field because the class, defined before this closure, can't reach `emitAs` -- see `ReturnHandler`'s own comment for who overrides this and why.
	// `result` has two equivalent "no value" spellings -- the `WasmType` string `'void'` (a real `: void` function's own `result`) and a bare omitted argument
	// (a caller with no meaningful `WasmType` at all, e.g. a resumable step function) -- normalized to `undefined` here once, rather than every caller agreeing.
	// `context` is the returned value's TS target, so a literal or generic call there builds what the caller reads.
	function plainReturn(result?: W.Type, context?: Type): ReturnHandler {
		if (result === 'void')
			result = undefined;
		return {
			wtype: () => result,
			emit(ctx, argument) {
				if (result === undefined) {
					// A `void` slot accepts a concise body that produces a value (TS's return-type bivariance), and JS discards it.
					if (argument)
						emitDiscarded(argument, ctx);
				} else if (argument) {
					// A `void` expression returned where a value is declared: real JS gives `undefined`, so it runs for its effects and the declared result's placeholder is pushed;
					// reached when a `() => void` closure is adapted to an `any`-returning signature -- `Array<T>`'s single physical bucket for every non-scalar element
					// makes the element type `any`, so `q.push(() => sideEffect())` compiles at `result = any`. Decided from the argument's own CHECKER type, so everything
					// else keeps going through `emitAs` (whose null-literal handling emitting directly would skip). Not `wtypeOf`: `typeOf` registers anonymous object
					// shapes as a side effect, perturbing `matchObjectShape`'s candidate set for an unrelated `makeRule(() => ({...}))` elsewhere.
					const argT = checkerTypeOf(unwrapAs(argument), ctx.scope);
					if (argT.type === 'ref' && argT.name === 'void') {
						emitExpr(argument, ctx, 'void');
						ctx.emitDefaultValue(result, types, toValType);
					} else {
						ctx.withContext(context, () => emitAs(argument, ctx, result));
					}
				}
				ctx.emit(I.return);
			},
		};
	}

	// `let x: T;` -- definite assignment guarantees a write before any read, so the starting value is never observed.
	// A non-nullable ref has no default at all, so it starts as an empty holder, exactly as a forward reference does.
	function emitUninitialized(name: string, tsType: Type, ctx: FunctionContext) {
		const wtype = typeOf(tsType);
		if (!wtype || wtype === 'void')
			throw `local '${name}' has an unsupported type`;
		const defaultable = typeof wtype === 'string' || W.isNullable(wtype) || W.isAny(wtype);
		const hoisted = ctx.closureEnv?.fields.get(name);
		if (hoisted) {
			if (defaultable) {
				ctx.emit(I.local.get(ctx.closureEnv!.envLocal.index));
				ctx.emitDefaultValue(wtype, types, toValType);
				ctx.emit(I.struct.set(ctx.closureEnv!.envTypeIndex, hoisted.index));
			}
		} else if (ctx.lookup(name)?.holderInner) {
			// an earlier sibling closure's forward reference already made the (empty) holder
		} else if (!defaultable || needsHolder(ctx, name)) {
			declareHolder(ctx, name, wtype, tsType);
		} else {
			ctx.emitDefaultValue(wtype, types, toValType);
			ctx.emit(I.local.set(ctx.declareValue(name, wtype, tsType).index));
		}
	}

	// A nested `function` declaration is hoisted: callable before its own line. It is created just before the first
	// statement in its list that mentions it -- closure creation has no side effects, and forward holders cover later siblings.
	function emitStmts(stmts: readonly Stmt[], ctx: FunctionContext) {
		const pending = new Map(stmts.flatMap(s => s.type === 'function_decl' && s.body ? [[s.name, s] as const] : []));
		const freeNames = (s: Stmt) => {
			const free = new Set<string>();
			collectFreeVars(new Set(), [s], free);
			return free;
		};
		const materialize = (fn: Extract<Stmt, { type: 'function_decl' }>) => {
			pending.delete(fn.name);
			const free = freeNames(fn);
			for (const other of [...pending.values()])
				if (pending.has(other.name) && free.has(other.name))
					materialize(other);
			emitStmt(fn, ctx);
		};
		for (const st of stmts) {
			if (pending.size) {
				const free = freeNames(st);
				for (const fn of [...pending.values()])
					if (fn !== st && pending.has(fn.name) && free.has(fn.name))
						materialize(fn);
			}
			if (st.type === 'function_decl' && st.body) {
				if (pending.has(st.name))
					materialize(st);
				continue;
			}
			emitStmt(st, ctx);
		}
	}

	function emitStmt(s: Stmt, ctx: FunctionContext): void {
		switch (s.type) {
			case 'empty':
				return;

			case 'block':
				ctx.inScope(() => emitStmts(s.body, ctx));
				return;

			case 'var_decl':
				for (const d of s.declarations) {
					if (s.kind === 'var' && typeof d.name === 'string' && ctx.vars.has(d.name)) {
						if (d.init)
							emitExpr(Assign<Expr, never>(Identifier(d.name), d.init), ctx, 'void');
						continue;
					}
					if (!d.init) {
						if (typeof d.name !== 'string')
							throw `local '${describeBinding(d.name)}' needs an initializer`;
						emitUninitialized(d.name, openedAs(d, d.typeAnnotation ?? slotType(d.flowType) ?? T.ANY), ctx);
						continue;
					}
					if (typeof d.name !== 'string') {
						// Desugars into plain `var_decl`s reading their own piece off a hidden scratch local (`#destructure$<n>`), emitted directly rather than
						// wrapped in a `block`: these bindings share the original `var_decl`'s scope, not a nested one.
						emitPatternBinding(s.kind, d.name, d.init, d.typeAnnotation, ctx);
						continue;
					}
					// Type computed before emitting the init, so the init can be emitted via `emitAs` straight into the local's declared representation.
					// `checker.scopeOfStmt(s)` -- the real, narrowing-aware scope the checker type-checked this statement under -- not `ctx.scope` (towasm's own,
					// separately-tracked scope, which never reflects flow-sensitive narrowing the way the checker's internal scope tree does). Without it, a
					// narrowed-non-null receiver (e.g. `if (m === null) return; ...; m.group(0)`) would still look nullable to `checkerTypeOf` here and member/call
					// resolution could fail on it. Unset for a real minority of statements -- see the two reasons spelled out at the `narrowedTypeOf` fallback below.
					const stamped	= (s as any).scope as Scope | undefined;
					const stmtScope = stamped ?? ctx.scope;
					const {methodOwner, methodName, calleeOptional} = d.init.type === 'call' && d.init.callee.type === 'member' && !objectIntrinsic(d.init) && !ctx.isNamespaceQualifier(d.init.callee.object)
						? {methodOwner: ownerOf(d.init.callee.object, ctx), methodName: d.init.callee.property, calleeOptional: d.init.callee.optional}
						: {};

					// No `Array<T>` substitution needed -- `substElemMethods` already monomorphized a method's whole body once, up front, so `d.typeAnnotation` is already concrete here.

					// The widened range before `T.literalTypeOf`: a loop-reassigned local's widened range must win over its initializer's narrower literal type,
					// or its wasm local gets fixed too tight and a later out-of-range reassignment corrupts it.
					let tsType = d.typeAnnotation ?? slotType(d.flowType) ?? T.literalTypeOf(d.init);
					if (!tsType && d.init.type === 'index') {
						// The real declared element `Type`: `T[]`/`Array<T>` give `T`, but `Uint8Array`/etc resolve (`resolveClassAlias`, before `T.resolve`
						// expands the alias) to `TypedArray<T>`, whose elements read back as `number` -- a physical-storage tag, not the real TS element type.
						const objT = checkerTypeOf(d.init.object, stmtScope);
						if (objT.type === 'ref' && !objT.typeArgs && resolveClassAlias(objT.name)?.name === 'TypedArray') {
							tsType = T.NUMBER;
						} else {
							const w = T.widenLiterals(T.resolve(global, objT), false, true);
							if (w.type === 'array') {
								tsType = w.element;
							} else if (w.type === 'ref') {
								switch (w.name) {
									case 'Array':
									case 'ReadonlyArray':	tsType = w.typeArgs?.[0]; break;
								}
							}
						}
						// `arr?.[i]` short-circuits to `undefined` like any `?.`, but this bypasses `checkerTypeOf`, so the optional flag has to be
						// reattached here too -- same as `case 'member'`'s own `e.optional` handling. A read the program TESTS for
						// absence (the checker's `markAbsenceTests`) reads `T | undefined` for the same reason, and is reattached alike.
						if (tsType && (d.init.optional || (d.init as { testedForAbsence?: boolean }).testedForAbsence))
							tsType = T.combineTypes([tsType, T.UNDEFINED]);
					}
					if (!tsType && methodOwner) {
						// The method's raw declared return type read off the class decl, not `checkerTypeOf(d.init, stmtScope)`: `stmtScope`'s stamp only exists for a lib
						// method body when `makeLibScope`'s one-time check wasn't muted for it (see its own comment) -- deliberately not always the case, since a GENERIC
						// lib class method's stamp (`Array<T>.reverse`/`.fill`) would reflect the template's unresolved `T` and permanently block (`??=` first-wins) the real
						// per-instantiation substituted scope (`ctx.scope`) codegen needs. A `?.` call's `undefined` is reattached here too, and a `this`-typed return
						// (`sort(): this`) is substituted the way `ensureMethod` resolves it -- the declaring class's own type, since this bypass has no receiver inference.
						const method		= methodOwner.decl.body.find(m => m.type === 'method' && m.key === methodName) as MethodMember | undefined;
							// A return naming the method's OWN type parameter (`map<U>(...): U[]`) is only known from call-site inference; one naming its CLASS's
							// (`Array<T>.filter(): T[]`) is only known from the receiver: this owner is the ERASED instantiation (`Array<any>` backs every array of a
							// non-scalar element), whose decl already reads `any[]`. The original generic declaration says which, and the checker knows the real instantiation.
						const ownerName		= methodOwner.decl.name;
						const generic		= ownerName ? LIB_DECL_MAP.get(ownerName) ?? userGenericClassDecls.get(ownerName) : undefined;
						const genericReturn	= generic?.type === 'class_decl' ? (generic.body.find(m => m.type === 'method' && m.key === methodName) as MethodMember | undefined)?.returnType : undefined;
						const methodReturn	= method?.returnType && !method.typeParams?.some(p => T.mentionsTypeParam(method.returnType!, p.name)) ? method.returnType : undefined;
						const substituted = methodReturn && T.substituteThisType(methodReturn, methodOwner.thisTsType);
						tsType = substituted && calleeOptional ? T.combineTypes([substituted, T.UNDEFINED]) : substituted;
						// An erased `filter(): T[]` owner is `any`-shaped, so the checker -- which knows the real instantiation -- wins, unless it has no
						// answer either: a structural dynamic object routed to `Map` has no `keys()` for the checker to see at all.
						if (tsType && genericReturn && (generic?.type === 'class_decl' ? generic.typeParams ?? [] : []).some(p => T.mentionsTypeParam(genericReturn, p.name))) {
							const checked = checkerTypeOf(d.init, stmtScope);
							if (!T.isAny(checked))
								tsType = checked;
						}
					}

					// A `const` takes its initializer's PRECISE type only where that lands on a scalar: precise types make `[1, 2]` a
					// TUPLE, not the widened `number[]`. A `let` takes its flow's hull (`flowType`), which covers every assignment.
					const precise = s.kind === 'const' ? ctx.typeAt(d.init, false) : undefined;
					tsType ??= precise && W.scalarKind(typeOf(precise)) ? slotType(precise) : checkerTypeOf(d.init, stmtScope);
					// Unstamped = synthesized after the check pass, or a generic template's stamp suppressed/stripped.
					// `narrowedTypeOf`, not `ctx.scope`: a narrowed scope turns a nominal `Map<K,V>` structural.
					if (T.isAny(tsType) && !stamped)
						tsType = ctx.narrowedTypeOf(d.init);

					// The declared type stays the initializer's context: a literal is built as a `u8[]` even into an open slot.
					const slotT = openedAs(d, tsType);
					const wtype = typeOf(slotT);
					if (!wtype) {
						// Let the actual lowering throw its own more specific error first (e.g. indexing a `string`) -- only fall back to this generic message if it didn't.
						emitExpr(d.init, ctx);
						throw `local '${d.name}' has an unsupported type`;
					}
					if (wtype === 'void')
						throw `local '${d.name}' cannot have type 'void'`;
					// A generator's own hoisted local (`compileGeneratorFunc`): storage is a frame struct field, not a real wasm local, same as a real closure
					// capture would be (`declareCaptured` already registered its scope type upfront, so only the write itself is new here).
					const hoisted = ctx.closureEnv?.fields.get(d.name);
					// `tsType` is the one real TS type this declaration has, seeding `ctx.contextualReturn` (see its own comment) while `d.init` compiles --
					// e.g. an array literal whose element is a generic call (`const rules: Expr[] = [makeRule(() => ({...}))]`).
					const savedContextualReturn = ctx.contextualReturn;
					ctx.contextualReturn = tsType;
					const initializing = (ctx.initializing ??= []);
					initializing.push(d);
					try {
						if (hoisted) {
							ctx.emit(I.local.get(ctx.closureEnv!.envLocal.index));
							emitAs(d.init, ctx, wtype);
							ctx.emit(I.struct.set(ctx.closureEnv!.envTypeIndex, hoisted.index));
						} else {
							// An EARLIER sibling closure may already have forward-referenced this name (`ensureForwardHolder`, from `emitClosureLiteral`'s own free-var check) --
							// but so may `d.init` ITSELF, compiled next (a self-recursive arrow, e.g. walker.ts's own `mapBindingTarget` calling its not-yet-declared name
							// from inside its own body). A plain `declareValue` after the fact would silently shadow the holder with a second, independent local, leaving
							// whatever captured it forever empty -- so the check has to happen AFTER `d.init` compiles; the value goes through a scratch local first
							// (`struct.set` needs the holder's own ref pushed before the value, but the value is what's already on the stack). A captured-and-assigned local
							// must BE a holder from the start (`needsHolder`), declared before `d.init` compiles so a closure inside the initializer captures the holder too,
							// and the store below goes through the same path a forward reference already took.
							if (!ctx.lookup(d.name)?.holderInner && needsHolder(ctx, d.name))
								declareHolder(ctx, d.name, wtype, slotT);
							// A value read through an ERASED instantiation (`Parser<Expr[]>` is `Parser<any>`) is built with `any` where the checker's type
							// names a reference, and no conversion reaches the precise layout; the local keeps what was built, and its reads cast back.
							const mayKeep	= s.kind === 'const' && !d.typeAnnotation && !ctx.lookup(d.name)?.holderInner && typeof wtype === 'string';
							const built		= mayKeep ? emitExpr(d.init, ctx, wtype) : emitAs(d.init, ctx, wtype, !ctx.lookup(d.name)?.holderInner);
							// An initializer may build a wider form than the proven scalar (a bigint op with no native form builds the magnitude
							// array); a `const` keeps what was built, since its reads can use either.
							const keep		= mayKeep && (typeof built === 'string' || !W.typeEq(built, wtype));
							if (mayKeep && !keep)
								coerceValue(d.init, built, ctx, wtype);
							const storage	= !mayKeep || keep ? built : wtype;
							const forwardHolder = ctx.lookup(d.name);
							if (forwardHolder?.holderInner) {
								const scratch = ctx.temp(`$fwd$${d.name}`, wtype);
								ctx.emit(I.local.set(scratch), I.local.get(forwardHolder.index), I.local.get(scratch));
								ctx.emit(I.struct.set((forwardHolder.wtype as { typeIndex: number }).typeIndex, 0));
							} else {
								ctx.emit(I.local.set(ctx.declareValue(d.name, storage, slotT).index));
							}
						}
					} finally {
						initializing.pop();
					}
					ctx.contextualReturn = savedContextualReturn;
				}
				return;

			case 'expression':
				emitDiscarded(s.expression, ctx);
				return;

			case 'if': {
				// A type guard its argument's type settles is decided here, and the dead branch is never compiled: it may not
				// even compile for this instantiation (lib `flat`'s array branch for a `number` element). The test still runs.
				const known = ctx.staticGuard(s.test);
				if (known !== undefined) {
					emitTruthy(s.test, ctx);
					ctx.emit(I.drop);
					const live = known ? s.consequent : s.alternate;
					if (live)
						emitStmt(live, ctx);
					return;
				}
				emitTruthy(s.test, ctx);
				const alternate = s.alternate;
				ctx.emitIf(undefined, () => emitStmt(s.consequent, ctx), alternate ? () => emitStmt(alternate, ctx) : undefined);
				return;
			}

			case 'while': {
				ctx.emitLoop(() => {
					emitTruthy(s.test, ctx);
					ctx.emit(I.i32.eqz, I.br_if(1));
					emitStmt(s.body, ctx);
					ctx.emit(I.br(0));
				});
				return;
			}
			case 'do_while': {
				ctx.emitLoop(() => {
					emitStmt(s.body, ctx);
					emitTruthy(s.test, ctx);
					ctx.emit(I.br_if(0));
				});
				return;
			}
			case 'continue': {
				if (s.label)
					throw "labeled 'continue' is not supported";
				if (!ctx.continueTargets.length)
					throw "'continue' outside of a loop";
				ctx.emitContinue();
				return;
			}

			case 'break': {
				if (s.label)
					throw "labeled 'break' is not supported";
				if (!ctx.breakTargets.length)
					throw "'break' outside of a loop or switch";
				ctx.emitBreak();
				return;
			}

			case 'return':
				// Same reasoning as `case 'this'`'s own guard -- a `return` inside a constructor implicitly needs `this` to exist too (that's the whole value being
				// returned), even a bare one: `ctx.onReturn` is still the generic `plainReturn(thisWtype)` handler here (not yet swapped to the constructor-specific
				// one, which only happens once every field is collected), so it would emit invalid wasm or coerce an arbitrary value into the class's own struct type.
				if (ctx.ctorFields)
					throw `'return' can't be used yet in '${ctx.owner?.name}'s constructor -- not every field has been assigned yet (this class has at least one object-typed field, needing 'struct.new' with every field's real value up front, before 'this' -- and so a valid return -- exists at all)`;
				ctx.onReturn.emit(ctx, s.argument);
				return;

			case 'for':
				switch (s.kind) {
					case 'normal':
						ctx.inScope(() => {
							// `s.init`'s own declaration (`for (let t = ...; ...)`) is scoped to the loop itself, same as real JS -- opened here rather than relying on
							// `s.body`'s own block scope, which may not exist at all if the body is a single bare statement.
							if (s.init)
								emitStmt(s.init.type === 'var_decl' ? s.init : JS.ExprStmt(s.init), ctx);

							// A `block` wrapping a `loop`, same idiom as `while`, except the body gets its own *inner*
							// block as the real `continue` target -- a plain `while` can reuse its restart label since it has no separate update step, but this desugared `for` has one (`s.update`) that must still run first.
							ctx.emitLoop(() => {
								emitTruthy(s.test ?? Literal(true), ctx);
								ctx.emit(I.i32.eqz, I.br_if(1));
								ctx.emitContinueBlock(() => emitStmt(s.body, ctx));
								if (s.update)
									emitStmt(JS.ExprStmt(s.update), ctx);
								ctx.emit(I.br(0));
							});
						});
						return;

					case  'of': {
						// The loop variable's own `name` (`v.name`) may be a plain identifier or a real destructuring pattern (`for (const [k, v] of pairs)`) -- `JS.Var`'s
						// own `name: BindingTarget` carries either through unchanged, and the synthesized `var_decl` (`JS.VarDecl(s.init.kind, JS.Var(v.name, ...))`) is
						// handled the same generic way any pattern-typed `var_decl` already is (`hoistVar`/`emitPatternBinding`) -- nothing here needs to know which shape.
						if (s.init.type !== 'var_decl' || s.init.declarations.length !== 1)
							throw "'for...of' loop variable must be a single declaration";

						const v			= s.init.declarations[0];
						const n			= ctx.tempCounter++;
						// A non-array with `[Symbol.iterator]()` iterates by the protocol, as JS iterates every iterable: `next()` until
						// `done`. `for...of` sends `undefined` to a `next` that takes a value (a generator's). Arrays stay indexed below.
						const it = iteratesByProtocol(s.right, ctx);
						if (it) {
							const itId: Expr	= Identifier(`#for${n}$it`);
							const rId: Expr		= Identifier(`#for${n}$r`);
							emitStmt(JS.Block<Stmt>(
								JS.VarDecl('const', JS.Var(`#for${n}$it`, JS.Call(JS.Member(s.right, '[Symbol.iterator]'), []))),
								JS.For(
									JS.VarDecl('let', JS.Var(`#for${n}$r`, nextCall(itId, it, ctx.scope))),
									JS.JSUnary('!', JS.Member(rId, 'done')),
									Assign<Expr, never>(rId, nextCall(itId, it, ctx.scope)),
									JS.Block<Stmt>(JS.VarDecl(s.init.kind, JS.Var(v.name, JS.Member(rId, 'value'), v.typeAnnotation ?? it.yield)), s.body),
								),
							), ctx);
							return;
						}
						const arrId: Expr = Identifier(`#for${n}$arr`);
						const idxId: Expr = Identifier(`#for${n}$i`);

						emitStmt(JS.Block<Stmt>(
							JS.VarDecl('const', JS.Var(arrId.name, s.right)),
							JS.For(
								JS.VarDecl('let', JS.Var(idxId.name, Literal(0))),
								JS.JSBinary('<', idxId, JS.Member(arrId, 'length')),
								JS.JSUnary('++', idxId),
								JS.Block<Stmt>(
									JS.VarDecl(s.init.kind, JS.Var(v.name, JS.Index(arrId, idxId), v.typeAnnotation)),
									s.body
								),
							),
						), ctx);
						return;
					}
					// `for (const k in obj)` -- most efficiently over a dynamic object (structural `{[k: string]: V}`, routed to `Map<string, V>`; see `indexSignatureValueType`),
					// which has a real, live key set: desugars to `for (const k of obj.keys())`, already-supported syntax, `keys()` being a real snapshot array (see
					// `lib/map.ts`'s own comment on why) -- so it iterates the live key set as the loop starts, matching real `for...in` closely enough for every real
					// use this project has (none mutate the object mid-loop). Anything else falls back to `Object.entries`, pulling just the key out of each `[k, v]`
					// pair via ordinary array-destructuring: deferring to `emitObjectEntries`'s own dispatch covers a *sealed* struct/class instance the same way, and
					// throws its own "not supported yet" for an extended class, for free.
					case 'in': {
						if (s.init.type !== 'var_decl' || s.init.declarations.length !== 1)
							throw "'for...in' loop variable must be a single declaration";

						// Anything read by POSITION (`isPositional`) enumerates its INDICES, as strings. Falling through to `Object.entries` below bound the entries instead,
						// so `for (const i in [5, 6])` gave the wrong values and the wrong count. `Array._indexKeys` builds them in ordinary typed lib code -- a synthesized
						// `String(i)` here has no checker stamp to resolve `toString` through.
						const indexed = ownerOf(s.right, ctx);
						if (indexed && isPositional(indexed, ctx)) {
							emitStmt({
								type: 'for', kind: 'of',
								init: s.init,
								right: JS.Call(JS.Member(Identifier('Array'), '_indexKeys'), [JS.Member(s.right, 'length')]),
								body: s.body,
							}, ctx);
							return;
						}

						if (ownerOf(s.right, ctx)?.methodDecls.get('keys')) {
							emitStmt({
								type: 'for', kind: 'of',
								init: s.init,
								right: JS.Call(JS.Member(s.right, 'keys'), []),
								body: s.body,
							}, ctx);
							return;
						}

						const v = s.init.declarations[0];
						emitStmt({
							type: 'for', kind: 'of',
							init: JS.VarDecl(s.init.kind, { ...v, name: JS.ArrayPattern([{ target: v.name }]) }),
							right: JS.Call(JS.Member(Identifier('Object'), 'entries'), [s.right]),
							body: s.body,
						}, ctx);
						return;
					}
					default:
						throw `'for...${s.kind}' is not supported`;
				}

			// Lowers to `n` nested `block`s (innermost = case 0), all wrapped in one outer `block` (the `break`
			// target). The discriminant is compared against each `test` in source order; a match branches into that case's block. Falling off a case's block end lands inside the next case's block -- real JS fallthrough.
			case 'switch': {
				const n = s.cases.length;
				if (n === 0) {
					// No cases -- the discriminant is still evaluated once for its side effects, same as real JS.
					emitStmt(JS.ExprStmt(s.discriminant), ctx);
					return;
				}

				/*if (wtypeOf(s.discriminant, ctx) === 'f64')*/ {
					const values = new Map<number, number>;
					let linear = true;
					for (let i = 0; i < n; i++) {
						if (s.cases[i].test) {
							const test = foldConstants(s.cases[i].test!)!;
							if (test.type !== 'literal' || typeof test.value !== 'number') {
								linear = false;
								break;
							}
							values.set(i, test.value);
						}
					}
					// Needs at least 2 distinct test values -- a single value has no meaningful gcd/stride.
					if (linear && values.size >= 2) {
						function gcd(a: number, b: number) {
							while (b > 1e-10)
								[a, b] = [b, a % b];
							return a;
						}
						const sorted = [...values.values()].sort((a, b) => a - b);
						let g = sorted[0];
						sorted.slice(1).forEach((v, i) =>
							g = gcd(g, v - sorted[i])
						);

						const tableSize = Math.ceil((sorted.at(-1)! - sorted[0]) / g) + 1;
						if (tableSize < values.size * 4) {

							const old = ctx.swapOut();

							ctx.enterBreakTarget();
							ctx.enterLabel(n);

							// `br`/`br_table` labels are relative to the branch point: case `i`'s block is the `i`-th opened above (case 0 innermost), and "no default"
							// falls through all `n` case-blocks to the enclosing break-target block at relative depth `n`.
							const defaultIndex	= s.cases.findIndex(c => !c.test);
							const defaultBr		= defaultIndex >= 0 ? defaultIndex : n;

							const table = new Array<number>(tableSize).fill(defaultBr);
							values.forEach((v, i) => table[Math.round((v - sorted[0]) / g)] = i);

							emitAs(JS.JSBinary('*', JS.JSBinary('-', s.discriminant, Literal(sorted[0])), Literal(1 / g)), ctx, 'i32');
							ctx.emit(I.br_table(table, defaultBr));

							let content = ctx.out;
							for (let k = 0; k < n; k++) {
								ctx.exitLabel();
								ctx.out = [I.block(undefined, content)];
								emitStmts(s.cases[k].consequent, ctx);
								content = ctx.out;
							}
							ctx.exitBreakTarget();
							ctx.out = old;
							ctx.emit(I.block(undefined, content));
							return;

						}
					}
				}

				// One shared scope for the whole switch -- real JS gives every case a common lexical scope unless a case wraps its body in `{}`,
				// which nests its own block via `case 'block'` as usual.
				ctx.inScope(() => {
					const discName = `#switch$${ctx.tempCounter++}`;
					emitStmt(JS.VarDecl('const', JS.Var(discName, s.discriminant)), ctx);
					const discId: Expr = Identifier(discName);

					const old = ctx.swapOut();

					ctx.enterBreakTarget();
					ctx.enterLabel(n);

					for (let i = 0; i < n; i++) {
						const c = s.cases[i];
						if (c.test) {
							emitAs(JS.JSBinary('===', discId, c.test), ctx, 'i32');
							ctx.emit(I.br_if(i));
						}
					}

					const defaultIndex = s.cases.findIndex(c => !c.test);
					ctx.emit(I.br(defaultIndex >= 0 ? defaultIndex : n));

					let content = ctx.out;
					for (let i = 0; i < n; i++) {
						ctx.exitLabel();
						ctx.out = [I.block(undefined, content)];
						emitStmts(s.cases[i].consequent, ctx);
						content = ctx.out;
					}
					ctx.exitBreakTarget();
					ctx.out = old;
					ctx.emit(I.block(undefined, content));
				});
				return;
			}

			case 'function_decl':
				// A bodyless declaration is one signature of a local overload group (`hoist()`'s own top-level handling already treats these the same way -- only the
				// one real, bodied implementation a group always has gets registered/compiled; the signatures exist purely for the checker's own overload resolution,
				// nothing to emit here at all). Without this, two or more overload signatures sharing a name each tried to declare their own same-named local, hitting
				// the genuine "redeclared" guard below meant for real, user-visible shadowing.
				if (!s.body)
					return;
				// A sibling created earlier already captured this name's forward holder (`ensureForwardHolder`): fill that.
				if (ctx.lookup(s.name)?.holderInner) {
					ctx.inScope(() => {
						const target = emitAssignTarget(Identifier(s.name), ctx, 'none');
						coerceTop(emitClosureLiteral(s, ctx, true), ctx, target.wtype);
						target.write(false);
					});
					return;
				}
				ctx.emit(I.local.set(ctx.declareLocal(s.name, emitClosureLiteral(s, ctx, true)).index));
				return;

			case 'throw':
				emitAs(s.argument, ctx, W.REF_ANY);
				ctx.emit(I.throw(ensureExceptionTag()));
				return;

			// `try_table`'s catch dispatch is branch-based, not legacy EH's inline-handler style: two nested blocks -- `$after` (the shared landing point once either
			// the try body or the catch handler completes) wraps `$catchLand` (the catch clause's own branch target, delivering the caught `anyref` payload as its
			// result). The try body's success path explicitly `br`s past the handler to `$after`, so `$catchLand`'s wrapped `try_table` never falls through to its
			// own end -- `unreachable` closes that dead edge; without it the validator checks the block's declared (anyref) result against the fallthrough's nothing
			// and rejects the module. JS's grammar allows at most one `catch`, so `handlers` is only ever empty or a single clause here.
			case 'try':
				if (!s.handlers.length && !s.finalizer)
					throw "'try' needs a 'catch' or 'finally'";

				if (!s.finalizer) {
					const saved			= ctx.swapOut();
					ctx.enterLabel(3);
					ctx.inScope(() => emitStmts(s.body, ctx));
					
					ctx.emit(I.br(2));	//ctx.depth - $after
					ctx.exitLabel();
					ctx.emit(I.try_table(undefined, [wasm.Catch.tag(ensureExceptionTag(), 0)], ctx.swapOut()));
					ctx.emit(I.unreachable);
					ctx.exitLabel();
					ctx.emit(I.block(toValType(W.REF_ANY), ctx.swapOut()));

					ctx.inScope(() => {
						if (s.handlers[0].param) {
							if (typeof s.handlers[0].param !== 'string')
								throw "a destructured catch parameter ('catch ({...})'/'catch ([...])') is not supported";
							ctx.emit(I.local.set(ctx.declareValue(s.handlers[0].param, W.REF_ANY, T.ANY).index));
						} else {
							ctx.emit(I.drop);
						}
						emitStmts(s.handlers[0].body, ctx);
					});

					ctx.exitLabel();
					ctx.emit(I.block(undefined, ctx.swapOut(saved)));

				} else {

					// With a 'finally', every exit -- normal completion, a caught or uncaught exception, an escaping break/continue/return -- funnels through one shared
					// landing point ($land) that runs 'finally' once, then re-dispatches on a recorded action code; break/continue/return redirect here via
					// `ctx.finallyGuards` (see those `case`s above), while the exception path needs no interception (`throw_ref` propagates on its own). A
					// return/throw/break/continue written directly inside 'finally' needs no special handling either -- guards and `onReturn` are restored to their outer
					// values before 'finally' compiles, so it executes as a real exit or redirects through the next-outer guard. Works in a generator/async function, a
					// constructor, or a `reassignsThis` method too: `onReturn` rebuilds the real per-context return (IteratorResult/Promise/`this`), exactly as if
					// compiling that shape fresh.
					const actionLocal		= { wtype: 'i32' as const, index: ctx.temp('#finally$action', 'i32') };
					const exnLocal			= { wtype: W.REF_EXN, index: ctx.temp('#finally$exn', W.REF_EXN) };
					const savedOnReturn		= ctx.onReturn;
					const outerOnReturn		= savedOnReturn;
					const outerWtype		= outerOnReturn.wtype(ctx);
					const returnValueLocal	= outerWtype !== undefined ? { wtype: outerWtype, index: ctx.temp('#finally$retval', outerWtype) } : undefined;

					const saved				= ctx.swapOut();
					const landDepth			= ctx.enterLabel();			// $land
					const catchAllDepth 	= ctx.enterLabel();			// $catchAllLand
					const afterDepth		= ctx.enterLabel();			// $after

					const guard = {
						actionLocal,
						breakTargetsLenAtEntry:		ctx.breakTargets.length,
						continueTargetsLenAtEntry:	ctx.continueTargets.length,
						landingDepth:				landDepth,
					};
					ctx.finallyGuards.push(guard);
					// A `return` in the protected region must stash its value and redirect here too; only one return meaning is ever current (no stack needed
					// as with nested loops' `break`), so a plain swap-and-restore mirrors `ctx.swapOut()`'s idiom.
					ctx.onReturn = {
						wtype: () => outerWtype,
						emit(ctx, argument) {
							if (returnValueLocal) {
								if (argument)
									emitAs(argument, ctx, returnValueLocal.wtype);
								else
									ctx.emitDefaultValue(returnValueLocal.wtype, types, toValType);
								ctx.emit(I.local.set(returnValueLocal.index));
							} else if (argument) {
								// Same rejection the real (outer) 'return' gives -- delegate to it for that message (a 'void' function vs. a constructor say this differently)
								// rather than inventing a second copy of the same decision here.
								outerOnReturn.emit(ctx, argument);
							}
							ctx.emit(I.i32.const(1), I.local.set(actionLocal.index), I.br(ctx.depth - landDepth));
						},
					};

					if (s.handlers.length) {
						// A's own exceptions: our single project-wide tag is the only thing this compiler ever throws, so the ordinary tag-catch below already covers 'try' exhaustively --
						// no 'catch_all_ref' needed on *this* try_table (unlike the one below, for B).
						ctx.enterLabel(2);			// $catchLand, try_table (A)'s own implicit level
						ctx.inScope(() => emitStmts(s.body, ctx));
						ctx.emit(I.br(ctx.depth - afterDepth));
						ctx.exitLabel();
						ctx.emit(I.try_table(undefined, [wasm.Catch.tag(ensureExceptionTag(), 0)], ctx.swapOut()));
						ctx.emit(I.unreachable);
						ctx.exitLabel();
						ctx.emit(I.block(toValType(W.REF_ANY), ctx.swapOut()));

						// The catch param binds `$catchLand`'s own delivered value -- outside and *before* try_table (B) starts: a block's body doesn't inherit values left
						// on the outer stack unless declared as real params (none of these are), so try_table (B) itself must start from a clean slate, not reach back for a
						// value produced before it began.
						ctx.openScope();
							if (s.handlers[0].param) {
								if (typeof s.handlers[0].param !== 'string')
									throw "a destructured catch parameter ('catch ({...})'/'catch ([...])') is not supported";
								ctx.emit(I.local.set(ctx.declareValue(s.handlers[0].param, W.REF_ANY, T.ANY).index));
							} else {
								ctx.emit(I.drop);
							}

							// B (the catch handler) gets its *own* safety net -- unlike A, nothing else already
							// guarantees every exception B might throw is caught before 'finally' needs to run.
							const catchHandlerSaved = ctx.swapOut();
							ctx.enterLabel();			// try_table (B)'s own implicit level
							emitStmts(s.handlers[0].body, ctx);
						ctx.closeScope();

						ctx.emit(I.br(ctx.depth - afterDepth));
						ctx.exitLabel();
						ctx.emit(I.try_table(undefined, [wasm.Catch.allRef(ctx.depth - catchAllDepth)], ctx.swapOut(catchHandlerSaved)));
						ctx.emit(I.unreachable);
					} else {
						// No 'catch' clause -- 'finally' alone needs only the safety net around A itself.
						ctx.enterLabel();			// try_table's own implicit level
						ctx.inScope(() => emitStmts(s.body, ctx));
						ctx.emit(I.br(ctx.depth - afterDepth));
						ctx.exitLabel();
						ctx.emit(I.try_table(undefined, [wasm.Catch.allRef(ctx.depth - catchAllDepth)], ctx.swapOut()));
						ctx.emit(I.unreachable);
					}

					ctx.finallyGuards.pop();
					ctx.onReturn = savedOnReturn;

					ctx.exitLabel();				// exit $after
					ctx.emit(I.block(undefined, ctx.swapOut()));
					ctx.emit(I.i32.const(0), I.local.set(actionLocal.index), I.br(ctx.depth - landDepth));
					ctx.exitLabel();				// exit $catchAllLand
					ctx.emit(I.block(toValType(W.REF_EXN), ctx.swapOut()));
					ctx.emit(I.local.set(exnLocal.index), I.i32.const(4), I.local.set(actionLocal.index));
					ctx.exitLabel();				// exit $land
					ctx.emit(I.block(undefined, ctx.swapOut(saved)));

					ctx.inScope(() => emitStmts(s.finalizer!, ctx));

					// Exactly one action code is ever set, and each arm is gated by its own 'if' so the validator only checks one small branch at a time.
					const dispatch = (code: number, build: () => void) => {
						ctx.emit(I.local.get(actionLocal.index), I.i32.const(code), I.i32.eq);
						ctx.emitIf(undefined, build);
					};
					dispatch(1, () => outerOnReturn.emit(ctx, returnValueLocal ? Identifier('#finally$retval') : undefined));
					// Skip an arm entirely when no such target was enclosing this construct (those action codes can then never be set), since
					// 'case break'/'case continue' would otherwise reject the synthesized statement outright.
					if (guard.breakTargetsLenAtEntry > 0)
						dispatch(2, () => ctx.emitBreak());
					if (guard.continueTargetsLenAtEntry > 0)
						dispatch(3, () => ctx.emitContinue());
					dispatch(4, () => ctx.emit(I.local.get(exnLocal.index), I.throw_ref));
				}
				return;

			// Nothing to emit: an enum declares compile-time constants, collected into `enumMembers` by
			// the module scan and folded at each read.
			case 'enum_decl':
				return;

			// Nothing to emit either, and for a simpler reason: these declare only TYPES. The checker has already put
			// them in the scope it stamped, which is what `ensureClass`/`resolve` read, so a FUNCTION-LOCAL one
			// (lalr.ts's `interface LR0Item` inside `buildLALR`) needs no more than being stepped over.
			case 'interface_decl':
			case 'type_alias_decl':
				return;

			default:
				throw `unsupported statement '${s.type}'`;
		}
	}

	// ===================================================================
	//  Function/Method
	// ===================================================================


	// A closure `WasmType` plus the language's own binding data for it. `WasmType.closure` is only the PHYSICAL shape (`ClosureSig`), so
	// `defaults`/`resolvedParams`/`restElem` live beside the payload rather than in it -- keyed by the payload OBJECT, not by its physical shape: two
	// same-shaped signatures legitimately differ in `resolvedParams` (see `case 'function'`), while `ensureClosureType` already memoizes by shape, so a
	// shape-keyed store would answer with the wrong one.
	const closureBindings = new WeakMap<W.ClosureSig, FuncSig>();
	// The closure a callable object carries, as a value of its own nullability.
	function callableOf(w: W.Type | undefined): W.ClosureType | undefined {
		if (!W.isRef(w))
			return undefined;
		const callable = classes.get(w.ref)?.callable;
		return callable && { ...callable, nullable: w.nullable };
	}
	// What calls a value of `w`: a closure, or a callable object's own.
	function closurePart(w: W.Type | undefined): W.ClosureType | undefined {
		return W.isClosure(w) ? w : callableOf(w);
	}
	function closureWtype(sig: FuncSig): W.ClosureType {
		closureBindings.set(sig, sig);
		return { closure: sig };
	}
	// Total for anything `closureWtype` built, so a miss is an internal inconsistency: throwing keeps a payload assembled some
	// other way from silently looking like "no defaults".
	// Calls the closure on the stack top: `call_ref` takes its env before the arguments and its code pointer after them.
	function emitClosureCall(w: W.ClosureType, pushArgs: () => void, ctx: FunctionContext): W.Type {
		const { funcTypeIndex, structTypeIndex } = ensureClosureType(w.closure);
		const held = ctx.temp(`$closure$${ctx.tempCounter++}`, w);
		ctx.emit(I.local.tee(held), I.struct.get(structTypeIndex, 1));
		pushArgs();
		ctx.emit(I.local.get(held), I.struct.get(structTypeIndex, 0), I.call_ref(funcTypeIndex));
		return w.closure.result;
	}
	// Source-level arguments bound to `w`'s parameters, defaults and rest included.
	function sourceArgs(label: string, w: W.ClosureType, args: Expr[], ctx: FunctionContext) {
		const sig = closureSigOf(w);
		return () => emitCallArgs(label, sig.params, sig.defaults, !!sig.hasRest, args, ctx, sig.resolvedParams);
	}

	function closureSigOf(w: W.Type): FuncSig {
		if (!W.isClosure(w))
			throw 'internal: expected a closure WasmType';
		const sig = closureBindings.get(w.closure);
		if (!sig)
			throw 'internal: closure WasmType was not built by closureWtype';
		return sig;
	}

	// One shared pair of wasm types per distinct TS function signature (memoized by `wasmTypeKey` -- every
	// literal still gets its own concrete env type and `funcIndex`): `funcTypeIndex` is shared so every literal of this signature is callable via one `call_ref`; `structTypeIndex` is the 2-field `{code, env}` value type.
	// `closureTypes` is the ENUMERATION of every signature seen (`an`-dispatch scans its `sig`s); the struct itself
	// is `types.closure`, which dedupes structurally, so this map is only about which signatures exist.
	function ensureClosureType(sig: FuncSig): ClosureTypeInfo {
		const key = `(${sig.params.map(W.typeKey).join(',')})=>${W.typeKey(sig.result)}`;
		let info = closureTypes.get(key);
		if (!info) {
			const funcTypeIndex	= types.funcType([{ type: {ref: types.envBase(), nullable: false}, id: 'env' }, ...toParams(sig.params)], toResults(sig.result));
			info = { funcTypeIndex, structTypeIndex: types.closure(funcTypeIndex), sig };
			closureTypes.set(key, info);
		}
		return info;
	}




	// `earlierNames`/`scope` are only ever passed by `resolveParams` below -- needed both to validate an earlier-parameter-referencing default
	// (`isReemittableDefault`) and to infer that default's type against a scope that actually has those earlier parameters declared (`libGlobal` can't see them).
	function resolveParam(p: JS.Param<Type>, earlierNames?: ReadonlySet<string>, scope: Scope = libGlobal, calleeOnly = false): ResolvedParam {
		let tsType = p.typeAnnotation && openedAs(p, p.typeAnnotation);
		const calleeSide = !!p.default && (calleeOnly || !isReemittableDefault(p.default, earlierNames));
		if (p.default)
			tsType ??= checkerTypeOf(p.default, scope);
		if (!tsType)
			throw `'param '${describeBinding(p.key)}' needs an explicit type`;
		const rawWtype = typeOf(tsType);
		if (!rawWtype)
			throw `'param '${describeBinding(p.key)}' needs an explicit type`;
		// See `closureFuncSigType`'s own comment -- box a real but wasm-unrepresentable `void` as `any`
		// rather than reject otherwise-valid source.
		const boxed = rawWtype === 'void' ? W.REF_ANY : rawWtype;
		// A bare `p?: T` widens to `T | undefined`, the same nullable-slot treatment `closureFuncSigType` already gives a function TYPE's own optional param:
		// an ordinary top-level function must likewise accept an explicit `undefined`/an omitted trailing argument for such a param.
		// `tsType` widens with the slot: it is what goes into `ctx.scope`, and leaving it as the bare annotation made `wtypeOf` derive a plain scalar
		// for a slot that is physically a nullable box -- so `b === undefined` on `b?: number` was rejected even though the box answers exactly that.
		if (calleeSide && T.unionMembers(tsType, scope).some(m => { const r = T.resolveOwn(m, scope); return r.type === 'literal' ? r.value === null : r.type === 'ref' && r.name === 'null'; }))
			throw `param '${describeBinding(p.key)}': a default applied in the callee needs a type without 'null' -- an omitted argument arrives as null, so an explicit null would take the default too`;
		return calleeSide ? { key: p.key, wtype: types.nullable(boxed), tsType: T.combineTypes([tsType, T.UNDEFINED]), calleeDefault: { value: p.default!, tsType } }
			: !p.default && hasMod(p, 'optional')
			? { key: p.key, wtype: types.nullable(boxed), tsType: T.combineTypes([tsType, T.UNDEFINED]) }
			: { key: p.key, wtype: boxed, tsType };
	}

	// Resolves a whole param list left to right, growing the earlier-names/scope `resolveParam` needs to validate and type a default that reads an earlier parameter:
	// each param sees every param resolved before it (real JS default-evaluation order), never one declared after it.
	function resolveParams(params: readonly JS.Param<Type>[], home: Scope = libGlobal): ResolvedParam[] {
		const earlierNames = new Set<string>();
		const scope = new Scope(home);
		return params.map(p => {
			const r = resolveParam(p, earlierNames, scope);
			if (typeof p.key === 'string') {
				earlierNames.add(p.key);
				scope.addValue(p.key, r.tsType);
			}
			return r;
		});
	}

	// The type arguments the checker resolved `decl` with, or under which `decl` realizes the signature it resolved (an overload's implementation).
	// A storage refinement (`i32`) stays, unless the context names its base type: the result is stored as that, so it instantiates there.
	type Expected = Type | (() => Type);
	// Declared types matched against declared types: none of inference's policies for an argument's value (a machine type read as `number`).
	function implementationTypeArgs(decl: JS.CallSig<Type>, inst: TS.CallSig, scope: Scope): Map<string, Type> {
		const typeParams	= decl.typeParams!;
		const found			= new Map<string, Type>();
		const match			= (d: Type | undefined, r: Type | undefined) => d && r && T.inferTypeArgs(d, r, new Map(typeParams.map(p => [p.name, p])), found, scope);
		decl.params.forEach((p, i) => match(p.typeAnnotation, inst.params[i]?.typeAnnotation));
		match(decl.rest?.typeAnnotation, inst.rest?.typeAnnotation);
		match(decl.returnType, inst.returnType);
		return new Map(typeParams.map(p => [p.name, found.get(p.name) ?? p.default ?? p.constraint ?? T.ANY]));
	}
	// Every non-nullish member an object shape with no index signature: a type held as structs (not `any`, a `Map`, a scalar).
	function isStructShapes(t: Type, scope: Scope): boolean {
		const n = T.nonNullable(t, scope);
		const shapes = T.objectShapes(n, scope);
		return shapes.length > 0 && shapes.length === T.unionMembers(n, scope).length && shapes.every(s => !indexSignatureValueType(s.objT));
	}
	// Whether each argument still fits its parameter under `map`: what lets codegen instantiate a call with other type arguments than the checker's.
	function argsFit(decl: JS.CallSig<Type>, map: Map<string, Type>, args: Expr[], scope: Scope): boolean {
		const restEl = decl.rest?.typeAnnotation && T.arrayLikeElement(T.resolve(scope, T.substituteType(decl.rest.typeAnnotation, map)));
		return args.every((a, i) => {
			const param = i < decl.params.length ? decl.params[i].typeAnnotation && T.substituteType(decl.params[i].typeAnnotation!, map) : restEl;
			return a.type === 'spread' || !param || T.isAssignable(checkerTypeOf(a, scope), param, scope);
		});
	}
	function callTypeArgs(decl: JS.CallSig<Type>, checked: CheckedCall | undefined, ctx: FunctionContext, explicit: boolean, args: Expr[], expected?: Expected): Map<string, Type> {
		const typeParams	= decl.typeParams!;
		if (!checked)
			throw `internal: a call of a generic has no resolution`;
		const { sig, lifted } = checked;
		// A lifted parameter makes the call's result a generic function VALUE: one physical closure, at its constraints (as `emitClosureLiteral`).
		const erased		= lifted && T.constraintMap(lifted, T.ANY);
		const typeArgs		= erased && checked.typeArgs ? new Map([...checked.typeArgs].map(([k, t]) => [k, T.substituteType(t, erased)])) : checked.typeArgs;
		const scope			= ctx.scope;
		const inst			= typeArgs ? T.instantiateSig(sig, typeArgs) : sig;
		const map			= templateOf(sig.origin) === templateOf(decl)
			? new Map(typeParams.map((p, i) => [p.name, typeArgs!.get(sig.typeParams![i].name)!]))
			: implementationTypeArgs(decl, inst, scope);
		const want			= typeof expected === 'function' ? expected() : expected;
		if (want && decl.returnType && !explicit) {
			const context = checkerInferTypeArgMap({ params: [], returnType: decl.returnType, typeParams }, [], undefined, scope, undefined, want);
			for (const [name, t] of map) {
				const wanted = context.get(name);
				if (wanted && (T.isRef(wanted, 'number') || T.isRef(wanted, 'bigint')) && T.machineOf(t, scope) && T.isAssignable(t, wanted, scope))
					map.set(name, wanted);
				// An anonymous shape inferred from a literal has no layout worth keeping: the call builds its result as the struct shapes it lands in.
				else if (wanted && T.nonNullable(t, scope).type === 'object' && isStructShapes(wanted, scope) && T.isAssignable(t, wanted, scope) && argsFit(decl, new Map([...map, [name, wanted]]), args, scope))
					map.set(name, wanted);
			}
		}
		return map;
	}


	function ensureFunc(name: string, decl: FunctionDecl, homeModule = '.'): FuncInfo {
		return funcs.get(homeKey(homeModule, name)) ?? compileFunc(name, decl, homeModule)!;
	}

	// Resolves a generic top-level function call to its monomorphized `FuncInfo`, cached under the same composite-key shape `ensureClass` uses for `Box<number>` (`identity<number>`).
	// The instance is checked as a declaration of its own: its narrowing depends on the type arguments (`typeof x === 'string'` on `T | string` after `Array.isArray`), which the template can't see.
	function instantiateDecl(decl: FunctionDecl, map: Map<string, Type>, homeModule: string): FunctionDecl {
		const inst = { ...substituteTypeParams(map).statement(decl)!, typeParams: undefined } as FunctionDecl;
		checkHoisted([inst], new Scope(moduleScopeOf(homeModule) ?? libGlobal));
		return inst;
	}

	function ensureGenericFunc(name: string, decl: FunctionDecl, call: CallSite, ctx: FunctionContext, expected?: Expected, homeModule = '.'): FuncInfo {
		if (Array.isArray(call))
			throw `internal: codegen's own call of generic '${name}' has no node to resolve`;
		const typeParams	= decl.typeParams!;
		const args			= call.arguments;
		const map			= callTypeArgs(decl, callOf(call, ctx.scope), ctx, !!call.typeArgs, args, expected);
		// A class instance filling a structural parameter specializes the instantiation further, as it does a plain function.
		const substituted	= decl.params.map(p => p.typeAnnotation ? { ...p, typeAnnotation: T.substituteType(p.typeAnnotation, map) } : p);
		const structural	= decl.body && structuralParams(substituted, args, ctx);
		// Bare (unmangled) composite key -- `compileFunc` applies `homeKey` itself when it caches, so this
		// must match without a second wrapping here.
		const key			= structural ? structuralKey(genericKey(name, typeParams, map, global), structural) : genericKey(name, typeParams, map, global);
		const existing		= funcs.get(homeKey(homeModule, key));
		if (existing)
			return existing;
		// `ensureClassExtension`'s ordering requirement: if this function's body ever calls `Object.defineProperty`, any of this specific instantiation's own
		// concrete type arguments might be the target (which one isn't resolved until the body compiles), so all of them get marked conservatively now,
		// before `compileFunc` ever reaches an `ensureClass` call for any of them and finalizes its struct type one way or the other.
		if (decl.body && containsDefineProperty(decl.body)) {
			for (const t of map.values())
				if (t.type === 'ref' && !t.typeArgs)
					everExtended.add(t.name);
		}
		const inst = instantiateDecl(decl, map, homeModule);
		return compileFunc(key, structural ? { ...inst, params: inst.params.map((p, i) => structural[i] === substituted[i] ? p : structural[i]) } : inst, homeModule, name)!;
	}

	// `realName` is the function's own real, DECLARED name; for a generic instantiation `name` is a mangled per-instantiation cache key (`ensureGenericFunc`'s `genericKey(...)`)
	// that `global.value()` could never find anything under. Defaults to `name` in the ordinary, non-generic case, where they are identical.
	function compileFunc(name: string, decl: FunctionDecl, homeModule = '.', realName: string = name): FuncInfo | undefined {
		try {
			if (hasMod(decl, 'async'))
				return compileAsyncFunc(name, decl, homeModule);

			if (hasMod(decl, 'generator'))
				return compileGeneratorFunc(name, decl, homeModule);

			if (decl.typeParams?.length)
				throw `generic function '${name}' is not supported`;

			// No annotation defaults to `void` (matching real TS's inference), but an annotation that is present and does not resolve is still a real error, not silently `void` too.
			// A cross-module function's own `decl` never gets its inferred return type back-filled at all -- that only ever happens on a throwaway synthetic clone `hoist()` builds
			// for the declaring module's own scope entry (`exportScope`'s lazy, self-memoizing `returnType` accessor -- see its own comment), never copied back onto `decl`.
			// `global.value(name)`, when this name is imported directly into the entry module (the reachable case), recovers the exact same already-correctly-inferred signature --
			// far safer than re-deriving inference here with no way to see the declaring module's own local names. Falls through to the old `'void'` default whenever this doesn't apply.
			// The declaring module's own internal scope (`exportScope` stamps it on the body it hoisted). Without it a non-entry function's body rooted at `libGlobal`,
			// so every module-local name -- a sibling function's RETURN TYPE included -- resolved to `any`, and every lowering that reads the checker's type rather than the
			// physical one (indexing, `.length`, a field read) silently lost. `global.value` only ever found a name imported DIRECTLY into the entry, so a function
			// reached through a namespace import (`path.join`) never resolved at all.
			const moduleScope = moduleScopeOf(homeModule);
			const checkedType = moduleScope?.value(realName) ?? global.value(realName);
			const inferredReturnType = !decl.returnType && checkedType?.type === 'function' ? checkedType.returnType : undefined;
			const overloaded = overloadedReturn(decl, checkedType);
			const result = overloaded ? typeOf(overloaded)
				: decl.returnType ? typeOf(decl.returnType)
				: inferredReturnType ? typeOf(inferredReturnType)
				: 'void';
			if (!result)
				throw `'${name}' has an unsupported return type`;

			// This function's own declaring module's scope (`stampSig` stamps `declScope` onto a hoisted signature once, using the exact scope `hoist()` was given for that module) --
			// rooting the compiled body's own scope here, instead of always `libGlobal`, is what lets a bare identifier referenced inside the body (a sibling class in the same file,
			// another top-level const, ...) resolve against ITS OWN module's declarations rather than only the entry's. Same reachability limitation as the return-type fallback above
			// (only when `name` is directly reachable via `global`) -- `homeScope` is simply `undefined` otherwise, falling back to `libGlobal` exactly as before.
			const homeScope = (checkedType?.type === 'function' ? checkedType.declScope as Scope | undefined : undefined) ?? moduleScope;

			const params	= resolveParams(decl.params, homeScope ?? libGlobal);
			if (decl.rest?.typeAnnotation)
				params.push({key: decl.rest.key, wtype: restParamWtype(decl.rest.typeAnnotation)!, tsType: decl.rest.typeAnnotation});

			const {funcIndex, typeIndex} = types.func(toParams2(params), toResults(result));
			const info: FuncInfo = {params: params.map(r => r.wtype), result, funcIndex, typeIndex, defaults: defaultsWithImplicitUndefined(decl.params), resolvedParams: params, hasRest: !!decl.rest?.typeAnnotation};
			funcs.set(homeKey(homeModule, name), info);
			worklist.push(W.withCatchAt(() => {
				const ctx	= new FunctionContext(name, new Scope(homeScope ?? libGlobal), plainReturn(result, overloaded ?? decl.returnType as Type | undefined), undefined, homeModule);
				ctx.ownBody = decl.body!;
				ctx.declareParams(params).forEach(st => emitStmt(st, ctx));
				hoistVars(decl.body!, params, ctx);
				emitStmts(decl.body!, ctx);
				ctx.emitTrailingUnreachable(result);
				info.body		= ctx.toFuncBody(params.length, toValType);
			}, decl, homeModule, name));
			return info;

		} catch (e) {
			//console.log(e);
			throw new W.Error(e as any, undefined, name, homeModule);
		}
	}

	// Shared by compileGeneratorFunc/compileAsyncFunc -- both restrict a resumable function's own params identically (plain identifier, no default, not optional, no rest);
	// `kind` only changes the error wording.
	function resolveResumableParams(decl: FunctionDecl): ResolvedParam[] {
		if (decl.rest)
			throw `rest parameter is not yet supported`;
		return decl.params.map(p => {
			if (typeof p.key !== 'string')
				throw `destructured is not supported`;
			if (p.default)
				throw `parameter '${p.key}' cannot have a default value`;
			if (hasMod(p, 'optional'))
				throw `parameter '${p.key}' cannot be optional`;
			return resolveParam(p);
		});
	}

	// `var` is function-scoped: each is declared once, before the body, and its declarations assign it (`case 'var_decl'`).
	// Its type is the checker's binding in the body's own scope, stamped on the first statement; a `var` redeclaring a parameter is that parameter.
	function hoistVars(body: Stmt[], params: ResolvedParam[], ctx: FunctionContext) {
		const home = (body[0] as { scope?: Scope } | undefined)?.scope;
		for (const [name, { decl }] of collectHoistedLocals(body, true)) {
			const declared = decl.typeAnnotation ?? slotType(decl.flowType) ?? home?.declared(name);
			if (!declared)
				throw `internal: 'var ${name}' has no checked type`;
			if (!params.some(p => p.key === name))
				emitUninitialized(name, openedAs(decl, declared), ctx);
			ctx.vars.add(name);
		}
	}

	// Shared by compileGeneratorFunc/compileAsyncFunc -- the frame's own field map (one per param, then one per hoisted local -- state and any extra hidden field,
	// e.g. async's own result Promise, are each caller's own concern, appended before/after this). `resumeValueType`, when given, overrides a suspend-boundary
	// declarator's own init-derived type -- needed only for a generator's `const v = yield x;` (see `compileGeneratorFunc`'s own comment on why `checkerTypeOf` can't
	// be trusted there); an async `await` needs no such override, so `compileAsyncFunc` never passes one.
	function buildFrameFields(decl: FunctionDecl, params: ResolvedParam[]) {
		const hoisted		= collectHoistedLocals(decl.body!);
		const localFields	= new Map<string, LocalField>();
		const frameFields: wasm.FieldType[] = [{ type: 'i32', mut: true }];
		for (const p of params) {
			localFields.set(p.key as string, { index: frameFields.length, wtype: p.wtype, tsType: p.tsType });
			frameFields.push({ type: toValType(p.wtype), mut: true });
		}
		for (const [localName, { stmt, decl: d }] of hoisted) {
			if (localFields.has(localName))
				continue;	// already a param field -- real JS forbids a body-level redeclaration of a param name anyway
			if (!d.init && !d.typeAnnotation)
				throw `local '${localName}' needs an initializer or an explicit type`;
			const tsType = d.typeAnnotation ?? slotType(d.flowType) ?? (d.init && T.literalTypeOf(d.init)) ?? checkerTypeOf(d.init!, (stmt as any).scope as Scope ?? libGlobal);
			const wt = typeOf(tsType);
			if (!wt || wt === 'void')
				throw `local '${localName}' has an unsupported type`;
			localFields.set(localName, { index: frameFields.length, wtype: wt, tsType });
			frameFields.push({ type: toValType(wt), mut: true });
		}
		return { localFields, frameFields };
	}

	// The frame a resumable function keeps between calls: its state, then every local the body declares (params first), then any
	// field the driver needs (`extra`, at `extraAt`). Hoisted locals take the type `case 'var_decl'` would give them, via the same widenings.
	function resumableFrame(decl: FunctionDecl, params: ResolvedParam[], extra: wasm.FieldType[] = []) {
		const { localFields, frameFields } = buildFrameFields(decl, params);
		const extraAt		= frameFields.push(...extra) - extra.length;
		// `envBase` as supertype: the frame is stored as a closure's env, whose declared param type is `(ref $envBase)`.
		const typeIndex		= types.add({ final: true, supertypes: [types.envBase()], type: { kind: 'struct', fields: frameFields } });
		return { localFields, typeIndex, extraAt, machine: BuildStateMachine(decl.body!) };
	}
	type ResumableFrame = ReturnType<typeof resumableFrame>;

	// A resumable function's step body. Every hoisted local reads and writes through the frame (`closureEnv`, as a closure capture
	// does), a resumed call re-enters through the dispatch loop, and a suspension's sent value lands in the local it names -- looked
	// up once by the segment it resumes INTO, since the flattener records it on the suspending one. `driver` is what differs: its
	// `return`, which suspensions resume with a value and how `#sent` converts to the field, and its suspend and completion arms.
	function emitResumableBody(fnCtx: FunctionContext, frame: ResumableFrame, frameLocal: W.Local, sent: W.Local, driver: {
		onReturn:			(setFrame: (state: number) => void) => ReturnHandler;
		resumesWithValue:	(next: SuspendBoundary) => boolean;
		fromSent:			(field: LocalField) => void;
		suspend:			(next: SuspendBoundary, resumeId: number, loopMark: number, setFrame: (state: number) => void) => void;
		complete:			() => void;
	}): void {
		fnCtx.closureEnv	= { envLocal: frameLocal, envTypeIndex: frame.typeIndex, fields: frame.localFields };
		for (const [localName, { tsType }] of frame.localFields)
			fnCtx.declareCaptured(localName, tsType);
		const setFrame		= (state: number) => fnCtx.emit(I.local.get(frameLocal.index), I.i32.const(state), I.struct.set(frame.typeIndex, 0));
		fnCtx.onReturn		= driver.onReturn(setFrame);
		const sentBindings	= new Map<number, LocalField>();
		for (const seg of frame.machine.segments)
			if (seg.next.type === 'suspend' && seg.next.resultVar && driver.resumesWithValue(seg.next))
				sentBindings.set(seg.next.resumeId, frame.localFields.get(seg.next.resultVar)!);
		fnCtx.emitResumableDispatch(frame.machine,
			() => fnCtx.emit(I.local.get(frameLocal.index), I.struct.get(frame.typeIndex, 0)),
			setFrame,
			test => emitTruthy(test, fnCtx),
			id => {
				const field = sentBindings.get(id);
				if (field) {
					fnCtx.emit(I.local.get(frameLocal.index), I.local.get(sent.index));
					driver.fromSent(field);
					fnCtx.emit(I.struct.set(frame.typeIndex, field.index));
				}
				emitStmts(frame.machine.segments[id].stmts, fnCtx);
			},
			(next, resumeId, loopMark) => driver.suspend(next, resumeId, loopMark, setFrame),
			driver.complete);
	}

	// The frame's leading field values, in declaration order: the entry state, a param's own value, every other hoisted local its
	// default. A real `struct.new` needs them all up front -- a non-nullable object-typed field (a `Promise<T>` param) has no default.
	function emitFrameInit(ctx: FunctionContext, params: ResolvedParam[], frame: ResumableFrame): void {
		const paramNames = new Set(params.map(p => p.key as string));
		ctx.emit(I.i32.const(frame.machine.entryId));
		for (const [localName, field] of frame.localFields) {
			if (paramNames.has(localName))
				ctx.emit(I.local.get(ctx.lookup(localName)!.index));
			else
				ctx.emitDefaultValue(field.wtype, types, toValType);
		}
	}

	// The function a caller actually calls. Registered module-qualified, as `compileFunc` registers: two modules declaring the same
	// name otherwise overwrote one another, leaving a reserved `funcIndex` with no body -- a malformed module (`70edf4d`).
	function compileResumableOuter(name: string, homeModule: string, params: ResolvedParam[], result: W.Type, build: (ctx: FunctionContext) => void): FuncInfo {
		const { funcIndex, typeIndex } = types.func(toParams2(params), toResults(result));
		const info: FuncInfo = { params: params.map(p => p.wtype), result, funcIndex, typeIndex, hasRest: false };
		funcs.set(homeKey(homeModule, name), info);
		worklist.push(W.withCatch(() => {
			const ctx = new FunctionContext(name, new Scope(moduleScopeOf(homeModule) ?? libGlobal), plainReturn(result), undefined, homeModule);
			ctx.declareParams(params).forEach(st => emitStmt(st, ctx));
			build(ctx);
			info.body = ctx.toFuncBody(params.length, toValType);
		}, name, homeModule));
		return info;
	}

	// A `function*` is two wasm functions: the named one (calling it runs no body, as a JS generator call runs none until `.next()` --
	// it captures a fresh frame and hands it to `new Generator(step)`) and a resumable "step" shaped like a closure, `{code, env}`,
	// whose env is the frame. `Generator<Y,R,N>`/`IteratorResult<Y,R>` (`lib/generator.ts`) are ordinary generic lib classes.
	function compileGeneratorFunc(name: string, decl: FunctionDecl, homeModule = '.'): FuncInfo {
		if (decl.typeParams?.length)
			throw `generic generator function '${name}' is not supported`;
		const params = resolveResumableParams(decl);

		const rt = decl.returnType;
		if (rt?.type !== 'ref' || rt.name !== 'Generator' || (rt.typeArgs?.length ?? 0) !== 3)
			throw `unexpected inferred return type`;
		const [Y, R, N] = rt.typeArgs!;
		const yWtype = typeOf(Y), nWtype = typeOf(N);
		if (!yWtype || yWtype === 'void')
			throw `unsupported yielded type`;
		if (!typeOf(R))
			throw `unsupported return type`;
		if (!nWtype || nWtype === 'void')
			throw `unsupported '.next()' argument type`;

		const resultClass	= ensureClass('IteratorResult', [Y, R]);
		const genClass		= ensureClass('Generator', [Y, R, N]);
		if (!resultClass || !genClass)
			throw `internal: the generator lib classes were not found`;
		const resultWtype	= resultClass.thisType;

		const sig: FuncSig = { params: [nWtype], result: resultWtype, hasRest: false };
		const { funcTypeIndex, structTypeIndex } = ensureClosureType(sig);
		const frame			= resumableFrame(decl, params);
		const { funcIndex: stepFuncIndex } = types.funcAt(funcTypeIndex);
		const stepInfo: FuncInfo = { params: sig.params, result: sig.result, hasRest: false, funcIndex: stepFuncIndex, typeIndex: funcTypeIndex };
		closureLiterals.push(stepInfo);

		worklist.push(W.withCatch(() => {
			const fnCtx			= new FunctionContext(name, new Scope(moduleScopeOf(homeModule) ?? libGlobal), plainReturn(resultWtype), undefined, homeModule);
			// Param order is `ensureClosureType`'s (env, then `sig.params`); the cast-down frame is one more local after them.
			const envParam		= fnCtx.declareLocal('#envParam', { typeIndex: types.envBase(), nullable: false });
			const sentParam		= fnCtx.declareLocal('#sent', nWtype);
			const frameLocal	= fnCtx.declareLocal('#frame', { typeIndex: frame.typeIndex, nullable: false });
			fnCtx.emit(I.local.get(envParam.index), I.ref.cast(frame.typeIndex), I.local.set(frameLocal.index));

			const resultCtor = ensureCtor(resultClass, [], fnCtx);
			// `IteratorResult.value`'s RESOLVED representation, not `Y`/`R`'s: a `void` `R` was boxed to `any` by `ensureClass`, and
			// both a `yield` and a `return` must push what the one constructor param was built to accept.
			const valueWtype = resultCtor.params[0];
			const result = (done: 0 | 1) => fnCtx.emit(I.i32.const(done), I.call(resultCtor.funcIndex), I.return);
			const value = (x: Expr | undefined, ctx: FunctionContext) => x ? void emitAs(x, ctx, valueWtype) : ctx.emitDefaultValue(valueWtype, types, toValType);

			emitResumableBody(fnCtx, frame, frameLocal, sentParam, {
				// A `return expr;` means "done": the step's wasm result is always an `IteratorResult`, never `expr` itself.
				onReturn: setFrame => ({
					wtype: () => valueWtype,
					emit(ctx, argument) {
						setFrame(frame.machine.completeId);
						value(argument, ctx);
						ctx.emit(I.i32.const(1), I.call(resultCtor.funcIndex), I.return);
					},
				}),
				resumesWithValue:	() => true,
				fromSent:			() => {},
				suspend(next, resumeId, _loopMark, setFrame) {
					if (next.kind !== 'yield')
						throw "'await' is not supported in generators yet";
					if (next.delegate)
						throw "'yield*' delegation is not supported";
					value(next.operand, fnCtx);
					setFrame(resumeId);
					result(0);
				},
				// Natural completion, or a repeat call once already here: idempotent, done forever after.
				complete() {
					fnCtx.emitDefaultValue(valueWtype, types, toValType);
					result(1);
				},
			});
			fnCtx.emitTrailingUnreachable(resultWtype);
			stepInfo.body = fnCtx.toFuncBody(2, toValType);
		}, name, homeModule));

		return compileResumableOuter(name, homeModule, params, genClass.thisType, ctx => {
			const genCtor = ensureCtor(genClass, [], ctx);
			ctx.emit(I.ref.func(stepFuncIndex));
			emitFrameInit(ctx, params, frame);
			ctx.emit(I.struct.new(frame.typeIndex), I.i32.const(sig.params.length), I.struct.new(structTypeIndex), I.call(genCtor.funcIndex), I.return);
		});
	}

	// An `async function` shares the generator's frame and dispatch but is driven differently: its body runs at once, synchronously,
	// up to its first real suspension, and nothing external asks it to resume -- a suspended `await` registers a continuation through
	// `Promise.then()`. So its step needs no `IteratorResult` (`void`) and no closure shape: both callers call its `funcIndex` directly,
	// with the frame as its first param. `closureLiterals` is reused only as "a body needing placement".
	function compileAsyncFunc(name: string, decl: FunctionDecl, homeModule = '.'): FuncInfo {
		if (decl.typeParams?.length)
			throw `generic async function '${name}' is not supported`;
		const params = resolveResumableParams(decl);

		const rt = decl.returnType;
		if (rt?.type !== 'ref' || rt.name !== 'Promise' || (rt.typeArgs?.length ?? 0) !== 1)
			throw `function '${name}' has an unexpected inferred return type`;
		const promiseClass	= ensureClass('Promise', rt.typeArgs);
		if (!promiseClass)
			throw `the 'Promise' lib class was not found`;
		const promiseWtype	= promiseClass.thisType;

		// One hidden field after the locals: the function's own result Promise, resolved by every `return` and by completion.
		const frame			= resumableFrame(decl, params, [{ type: toValType(promiseWtype), mut: true }]);
		const resultPromise	= frame.extraAt;
		const { funcIndex: stepFuncIndex, typeIndex: stepFuncTypeIndex } = types.func(
			[{ type: { ref: frame.typeIndex, nullable: false }, id: 'frame' }, { type: toValType(W.REF_ANY), id: 'sent' }], []);
		const stepInfo: FuncInfo = { params: [{ typeIndex: frame.typeIndex, nullable: false }, W.REF_ANY], result: 'void', hasRest: false, funcIndex: stepFuncIndex, typeIndex: stepFuncTypeIndex };
		closureLiterals.push(stepInfo);

		worklist.push(W.withCatch(() => {
			const fnCtx			= new FunctionContext(name, new Scope(moduleScopeOf(homeModule) ?? libGlobal), plainReturn(), undefined, homeModule);
			const frameLocal	= fnCtx.declareLocal('#frame', { typeIndex: frame.typeIndex, nullable: false });
			const sentParam		= fnCtx.declareLocal('#sent', W.REF_ANY);
			const resolveMethod	= ensureMethod(promiseClass, 'resolve', [], fnCtx)!;
			// `resolve`'s RESOLVED param, not `T`: a `Promise<void>`'s `T` was boxed to `any` by `ensureClass`.
			const valueWtype	= resolveMethod.params[0];
			const resolve		= (x: Expr | undefined, ctx: FunctionContext) => {
				ctx.emit(I.local.get(frameLocal.index), I.struct.get(frame.typeIndex, resultPromise));
				if (x)
					emitAs(x, ctx, valueWtype);
				else
					ctx.emitDefaultValue(valueWtype, types, toValType);
				ctx.emit(I.call(resolveMethod.funcIndex), I.return);
			};

			// One trampoline per awaited element type, shared by every await of it: it unboxes its value and forwards it, with the frame as
			// its closure env, into the step -- whose state field, set before `.then()`, already says where the resume lands.
			const trampolines = new Map<string, { funcIndex: number; structTypeIndex: number }>();
			const ensureTrampoline = (tWtype: W.Type) => {
				const key = W.typeKey(tWtype);
				let info = trampolines.get(key);
				if (!info) {
					const { funcTypeIndex, structTypeIndex } = ensureClosureType({ params: [tWtype], result: 'void' });
					const { funcIndex } = types.funcAt(funcTypeIndex);
					const tInfo: FuncInfo = { params: [tWtype], result: 'void', hasRest: false, funcIndex, typeIndex: funcTypeIndex };
					closureLiterals.push(tInfo);
					worklist.push(() => {
						const tCtx			= new FunctionContext(fnCtx.name, new Scope(libGlobal), plainReturn(), undefined);
						const envParam		= tCtx.declareLocal('#envParam', { typeIndex: types.envBase(), nullable: false });
						const valueParam	= tCtx.declareLocal('#value', tWtype);
						tCtx.emit(I.local.get(envParam.index), I.ref.cast(frame.typeIndex), I.local.get(valueParam.index));
						coerceTop(tWtype, tCtx, W.REF_ANY);
						tCtx.emit(I.call(stepFuncIndex), I.return);
						tInfo.body			= tCtx.toFuncBody(2, toValType);
					});
					info = { funcIndex, structTypeIndex };
					trampolines.set(key, info);
				}
				return info;
			};
			let awaitTemp = 0;

			emitResumableBody(fnCtx, frame, frameLocal, sentParam, {
				// A `return expr;` resolves the result Promise and returns nothing: the step's result is `void`, and nothing reads it.
				onReturn: () => ({ wtype: () => valueWtype, emit: (ctx, argument) => resolve(argument, ctx) }),
				// Only a REAL Promise suspension resumes through `#sent`: the synchronous fast path writes the local inline, and re-writing
				// it from `#sent` would clobber it with an earlier resume's value.
				resumesWithValue:	next => !!T.asPromiseRef(checkerTypeOf(next.operand!, fnCtx.scope), fnCtx.scope),
				fromSent:			field => coerceTop(W.REF_ANY, fnCtx, field.wtype),
				suspend(next, resumeId, loopMark, setFrame) {
					if (next.kind !== 'await')
						throw "'yield' is not supported inside an async function";
					if (next.delegate)
						throw "'yield*' is not supported inside an async function";
					const operand		= next.operand!;
					const promiseRef	= T.asPromiseRef(checkerTypeOf(operand, fnCtx.scope), fnCtx.scope);
					if (!promiseRef) {
						// Not Promise-shaped, so nothing to suspend on: JS unwraps a non-thenable `await` at once. Still a state
						// transition -- no less correct than falling through, at the cost of one more dispatch iteration.
						if (next.resultVar) {
							const field = frame.localFields.get(next.resultVar)!;
							fnCtx.emit(I.local.get(frameLocal.index));
							emitAs(operand, fnCtx, field.wtype);
							fnCtx.emit(I.struct.set(frame.typeIndex, field.index));
						} else {
							emitDiscarded(operand, fnCtx);
						}
						setFrame(resumeId);
						fnCtx.emit(I.br(fnCtx.depth - loopMark));
						return;
					}
					const tType		= promiseRef.typeArgs![0];
					const tWtype	= typeOf(tType);
					if (!tWtype)
						throw "'await' on a Promise of an unsupported element type";
					const awaitedClass = ensureClass('Promise', [tType]);
					if (!awaitedClass)
						throw `the 'Promise' lib class was not found`;
					emitAs(operand, fnCtx, awaitedClass.thisType);
					const promiseLocal = fnCtx.declareLocal(`$await$${awaitTemp++}`, awaitedClass.thisType);
					fnCtx.emit(I.local.set(promiseLocal.index));
					// `state` must say where to resume BEFORE `.then()`: a settled promise calls the trampoline synchronously,
					// re-entering the step before `.then()` returns (safe -- this arm ends in `return`).
					setFrame(resumeId);
					// A trampoline is built from a resolved `W.Type`, bypassing the `void`-as-`any` boxing a field or param gets.
					const tramp = ensureTrampoline(tWtype === 'void' ? W.REF_ANY : tWtype);
					fnCtx.emit(
						I.local.get(promiseLocal.index),
						I.ref.func(tramp.funcIndex), I.local.get(frameLocal.index), I.i32.const(1), I.struct.new(tramp.structTypeIndex),
						I.call(ensureMethod(awaitedClass, 'then', [], fnCtx)!.funcIndex), I.return);
				},
				complete: () => resolve(undefined, fnCtx),
			});
			stepInfo.body = fnCtx.toFuncBody(2, toValType);
		}, name, homeModule));

		return compileResumableOuter(name, homeModule, params, promiseWtype, ctx => {
			const promiseCtor	= ensureCtor(promiseClass, [], ctx);
			const promiseLocal	= ctx.declareLocal('#resultPromise', promiseWtype);
			// The constructor's RESOLVED `initial: T` (see `valueWtype`); its value never matters -- `resolve()` overwrites it.
			ctx.emitDefaultValue(promiseCtor.params[0], types, toValType);
			ctx.emit(I.call(promiseCtor.funcIndex), I.local.set(promiseLocal.index));
			emitFrameInit(ctx, params, frame);
			ctx.emit(I.local.get(promiseLocal.index), I.struct.new(frame.typeIndex));
			// Run the body at once, up to its first real suspension, as JS does. The entry segment never reads `#sent`, but it is a
			// non-nullable `any`, so a real (unused) box keeps that true.
			ctx.emit(I.f64.const(0), I.struct.new(types.box('f64')), I.call(stepFuncIndex), I.local.get(promiseLocal.index), I.return);
		});
	}


	// Resolves a bare type-alias name (`declare type X = SomeGenericClass<...>`, e.g. lib.d.ts's own `Uint8Array = TypedArray<u8>`) to its real
	// generic target, so a name with only a type alias can still be instantiated the ordinary generic way (see `ensureClass`) -- without a
	// physical declaration or name-substituted copy per alias. General: any such alias, not just typed-array ones.
	function resolveClassAlias(name: string): { name: string; typeArgs: Type[] } | undefined {
		const target = libGlobal.type(name)?.type;
		return target?.type === 'ref' && target.typeArgs?.length && LIB_DECL_MAP.get(target.name)?.type === 'class_decl'
			? { name: target.name, typeArgs: target.typeArgs }
			: undefined;
	}

	function addExpandoFields(info: ClassInfo, name: string) {
		for (const key of accessorKeys.get(name) ?? []) {
			// The data slot holds nothing until a write, which a construction site with only an accessor for the key never makes.
			const data = info.fieldIndex.get(key);
			if (data !== undefined)
				info.fields[data] = { ...info.fields[data], wtype: (w => typeof w === 'string' ? w : types.nullable(w))(info.fields[data].wtype), optional: true };
			const slots: [string, W.Type][] = [[`#get:${key}`, getterWtype()], [`#set:${key}`, setterWtype()]];
			for (const [slot, wtype] of slots)
				if (!info.fieldIndex.has(slot)) {
					info.fieldIndex.set(slot, info.fields.length);
					info.fields.push({ name: slot, wtype, optional: true });
				}
		}
		const spec = pendingExtensions.get(name);
		if (!spec)
			return;
		if (spec === 'dynamic') {
			if (info.fieldIndex.has('#ext'))
				return;
			const map = ensureClass('Map', [TS.RefType('string'), T.ANY]);
			if (!map)
				throw `internal: 'Map' isn't available for '${name}''s own dynamic expando`;
			info.fieldIndex.set('#ext', info.fields.length);
			info.fields.push({ name: '#ext', wtype: { ...(map.thisWtype! as { ref: string }), nullable: true }, optional: true });
		} else {
			for (const key of spec)
				if (!info.fieldIndex.has(key))
					addField(info, key, T.ANY, true);
		}
	}

	function getterWtype(): W.Type { return types.nullable(typeOf(getterSig())!); }
	function setterWtype(): W.Type { return types.nullable(typeOf(setterSig())!); }

	// A field write, the receiver and the value (typed `valWtype`) on the stack. A key some `defineProperty` gave a setter
	// (`accessorKeys`) has a `#set:k` companion: while that holds a setter the write CALLS it; otherwise the field.
	function emitFieldWrite(cls: ClassInfo, idx: number, valWtype: W.Type, ctx: FunctionContext): void {
		const field	= cls.fields[idx];
		const acc	= cls.fieldIndex.get(`#set:${field.name}`);
		const set	= () => {
			coerceTop(valWtype, ctx, field.wtype);
			ctx.emit(I.struct.set(cls.typeIndex, idx));
		};
		if (acc === undefined)
			return set();
		const val		= ctx.declareLocal(`$acc$val$${ctx.tempCounter++}`, valWtype).index;
		const obj		= ctx.declareLocal(`$acc$obj$${ctx.tempCounter++}`, cls.thisWtype!).index;
		ctx.emit(I.local.set(val), I.local.set(obj));
		const plain		= () => {
			ctx.emit(I.local.get(obj), I.local.get(val));
			set();
		};
		const setterW	= cls.fields[acc].wtype;
		if (!W.isClosure(setterW))
			throw `internal: '${cls.name}'s '#set:${field.name}' is not a setter slot (${W.typeKey(setterW)})`;
		const setter	= ctx.declareLocal(`$acc$set$${ctx.tempCounter++}`, setterW);
		ctx.emit(I.local.get(obj), I.struct.get(cls.typeIndex, acc), I.local.tee(setter.index), I.ref.is_null);
		ctx.emitIf(undefined, plain, () => {
			ctx.emit(I.local.get(setter.index), I.ref.as_non_null);
			emitClosureCall({ ...setterW, nullable: false }, () => {
				ctx.emit(I.local.get(val));
				coerceTop(valWtype, ctx, setterW.closure.params[0]);
			}, ctx);
		});
	}

	// A field read, the receiver already on the stack. A field some `Object.defineProperty` gave a getter (`accessorKeys`) has
	// a `#get:k` companion: while that holds a getter the read CALLS it, as JS reads an accessor property; otherwise the field.
	function emitFieldRead(cls: ClassInfo, idx: number, ctx: FunctionContext): W.Type {
		const field	= cls.fields[idx];
		const acc	= cls.fieldIndex.get(`#get:${field.name}`);
		if (acc === undefined) {
			ctx.emit(I.struct.get(cls.typeIndex, idx));
			return field.wtype;
		}
		const getterW	= cls.fields[acc].wtype;
		if (!W.isClosure(getterW))
			throw `internal: '${cls.name}'s '#get:${field.name}' is not a getter slot (${W.typeKey(getterW)})`;
		const obj		= ctx.declareLocal(`$acc$obj$${ctx.tempCounter++}`, types.nullable(cls.thisWtype!));
		const getter	= ctx.declareLocal(`$acc$get$${ctx.tempCounter++}`, getterW);
		ctx.emit(I.local.tee(obj.index), I.struct.get(cls.typeIndex, acc), I.local.tee(getter.index), I.ref.is_null);
		ctx.emitIf(toValType(field.wtype),
			() => ctx.emit(I.local.get(obj.index), I.struct.get(cls.typeIndex, idx)),
			() => {
				ctx.emit(I.local.get(getter.index), I.ref.as_non_null);
				coerceTop(emitClosureCall({ ...getterW, nullable: false }, () => {}, ctx), ctx, field.wtype);
			});
		return field.wtype;
	}

	function addField(info: ClassInfo, key: string, typeAnnotation?: Type, optional = false) {
		// See `closureFuncSigType`'s own comment -- box a real but wasm-unrepresentable `void` as `any` rather than reject otherwise-valid source.
		const rawWt = typeAnnotation && typeOf(typeAnnotation);
		let wt	= rawWt === 'void' ? W.REF_ANY : rawWt;
		if (!wt) {
			if (process.env.DBG)
				console.error(`addField FAIL info=${info.name} key=${key} ann=${typeAnnotation ? typeAnnotation.type + ' ' + T.typeKey(typeAnnotation).replace(/\s+/g,' ').slice(0,120) : 'undefined'} resolved=${typeAnnotation ? T.typeKey(T.resolve(global, typeAnnotation)).replace(/\s+/g,' ').slice(0,120) : '-'}`);
			throw `'${key}' needs an explicit number/boolean/object type`;
		}
		// The checker tracks `optional` as a separate modifier, never folding `value?: T` into `| undefined` (same gap as optional params), so
		// `wt` alone never says a field can be absent: force nullability, or an omitted boxed `any` (default `0`, not `undefined`) defeats `??=`.
		if ((optional || info.earlyThis) && typeof wt === 'object' && !wt.nullable)
			wt = types.nullable(wt);
		// A scalar-typed optional field needs the same null-boxing an optional *parameter* already gets: without it there is no absent value
		// distinct from `0`/`false`, so `??=` and `=== undefined` fail (an unassigned `n?: number` reads back as `0`). Only `f64`/`i32` have a box.
		if (optional && (wt === 'f64' || wt === 'i32'))
			wt = types.nullable(wt);
		info.addField(key, wt, optional);
	}

	// Resolves a plain, non-generic type alias (`type Point = { x: number; y: number };`) whose target is a structural object type of only
	// 'property' members into a real wasm-GC struct -- object-literal support only, no structural inference -- cached in the same `classes` map
	// as real classes (a name can't be both a `class_decl` and a type alias), so ordinary field access works on it unchanged.
	// Shared struct-building core for `ensureObjectShape` and `ensureAnonObjectShape`: `info` enters `classes` (with a real `typeIndex`) before
	// any member's type is resolved -- `ensureClass`'s placeholder-first ordering -- so a union reached again through one of its own fields finds
	// it already there. Fields start with `base`'s (a real wasm subtype); a base still being BUILT has no `final` yet, so its link waits.
	const pendingSupertypes = new Map<ClassInfo, ClassInfo[]>();
	const subtypesOf		= new Map<ClassInfo, ClassInfo[]>();
	function linkSupertype(info: ClassInfo, base: ClassInfo): boolean {
		const baseType = laidOut(base);
		if (!baseType) {
			pendingSupertypes.set(base, [...(pendingSupertypes.get(base) ?? []), info]);
			return true;
		}
		if (!baseType.final && base.fields.every((f, i) =>
			info.fields[i]?.name === f.name && !!info.fields[i].optional === !!f.optional && W.typeEq(info.fields[i].wtype, f.wtype))) {
			info.superClass = base;
			(types.get(info.typeIndex) as { supertypes: number[] }).supertypes = [base.typeIndex];
			subtypesOf.set(base, [...(subtypesOf.get(base) ?? []), info]);
		}
		return false;
	}

	// Laid out again over a base that has since GAINED fields -- `addExpandoFields` appends its accessor companions last, well after a subtype
	// reached from one of the base's own field types copied what the base had then. The base's fields stay an exact prefix; its own must agree.
	function relayoutOverBase(info: ClassInfo, base: ClassInfo): void {
		const inherited = new Map(base.fields.map(f => [f.name, f]));
		if (!info.fields.every(f => !inherited.has(f.name)
			|| (W.typeEq(f.wtype, inherited.get(f.name)!.wtype) && !!f.optional === !!inherited.get(f.name)!.optional)))
			return;
		info.fields		= [...base.fields.map(f => ({ name: f.name, wtype: f.wtype, optional: f.optional })), ...info.fields.filter(f => !inherited.has(f.name))];
		info.fieldIndex	= new Map(info.fields.map((f, i) => [f.name, i]));
		(types.get(info.typeIndex) as { type: { fields: wasm.FieldType[] } }).type.fields = structFields(info);
		linkSupertype(info, base);
		(subtypesOf.get(info) ?? []).forEach(sub => relayoutOverBase(sub, info));
	}

	// A callable object's closure prefix is immutable, as in the closure struct it extends.
	function structFields(info: ClassInfo): wasm.FieldType[] {
		return info.fields.map((f, i) => ({ type: toValType(f.wtype), mut: !info.callable || i >= W.CALLABLE_PREFIX }));
	}

	function buildObjectShape(key: string, members: TS.TypeMember[], thisTsType: Type, declName: string, everFinal: boolean, shape = shapeKey(members)): ClassInfo {
		// Before this struct's own index: a supertype must precede its subtypes in the type section.
		const calls			= members.some(m => m.type === 'call');
		const callable		= calls ? callSignaturesWtype(members) : undefined;
		if (calls && !callable)
			throw `object-shape type '${declName}' has a call signature with no representation`;
		const closureType	= callable && ensureClosureType(callable.closure);
		const info = new ClassInfo(key, types.add({kind: 'struct', fields: []}), { name: declName, body: [] }, thisTsType);
		info.thisWtype = { ref: key };
		classes.set(key, info);

		if (closureType) {
			info.callable = callable;
			info.addField('#code', { typeIndex: closureType.funcTypeIndex });
			info.addField('#env', { typeIndex: types.envBase() });
			info.addField('#length', 'i32');
		}
		for (const m of members) {
			switch (m.type) {
				case 'call':
					break;
				case 'property':
				case 'method': {
					const key = T.memberKey(m.key);
					if (key === undefined)
						throw `object-shape type '${declName}' has a computed property name with no static spelling -- not supported`;
					addField(info, key, m.type === 'method' ? {...(m as TS.CallSig), type: 'function'} : m.typeAnnotation, hasMod(m, 'optional'));
					break;
				}
				default:
					throw `object-shape type '${declName}' can only have plain properties (no methods/index/call signatures) to be an object literal's target type`;
			}
		}

		addExpandoFields(info, declName);
		addExpandoFields(info, shape);
		types.set(info.typeIndex, {
			final: everFinal,
			supertypes: closureType ? [closureType.structTypeIndex] : [],
			type: { kind: 'struct', fields: structFields(info) },
		});
		const waiting = pendingSupertypes.get(info);
		if (waiting) {
			pendingSupertypes.delete(info);
			waiting.forEach(w => relayoutOverBase(w, info));
		}
		return info;
	}



	function ensureObjectShape(name: string, typeArgs?: Type[], declScope?: Scope): ClassInfo | undefined {
		const scope = declScope ?? global;
		const entry = scope.type(name);
		if (!entry)
			return undefined;

		const args	= layoutArgs(entry.typeParams, typeArgs, scope);
		let key		= layoutKey(name, args, scope);
		// Which MODULE declares the name is part of the key: two modules can declare the same one (`Common.Member` and js-parser's own `Member`),
		// and a shape keyed by name alone handed the second one the first's struct. The entry module and the lib keep bare keys.
		const tag = moduleTagOf(name, entry);
		if (tag)
			key += `@${tag}`;
		const existing	= classes.get(key);
		if (existing)
			return existing;

		// Via a `RefType` (not the entry's own raw, still-generic `.type`) so a reference to a generic interface/alias -- bare or explicit -- goes
		// through `resolve`'s own type-arg substitution (each param to its given arg, its default, or `any`) instead of leaving the type param
		// unresolved in every member's type. Stamped with `scope` because this exact ref becomes `thisTsType`, which `fieldDeclaredType` re-resolves.
		const ref = TS.RefType(name, args.length ? args : typeArgs);
		ref.declScope = scope;
		// `resolveObjectType` (not a hand-rolled intersection flatten): an interface `extends`ing another (`Method<T> extends CallSig<T>`) needs its
		// parts (`CallSig<T>` itself still an unresolved ref here) actually RESOLVED, not just unwrapped-if-already-an-object -- a flatten that only
		// handled already-expanded object parts silently dropped the rest, leaving `Method<Type>` with only its own directly-declared fields.
		const resolved = T.resolveObjectType(ref, scope);
		if (!resolved)
			return undefined;
		// An index-signature-shaped object (`Partial<T>`, `Record<string,V>`, ...) isn't a fixed-field struct at all -- `ownerFor`'s caller already
		// has a real, more appropriate fallback for this shape (`indexSignatureValueType`, the `Map`-backed path) once `ensureClass` declines here.

		if (!isStructLayout(resolved.members))
			return undefined;

		// Shared with the structurally-identical ANONYMOUS shape under `ensureAnonObjectShape`'s own `T.typeKey` identity: `type A = { n: number }`
		// written as `A` in one place and inlined in another is ONE type in TS, but keying a named shape by name alone built a second struct, so a
		// value built as one failed `ref.cast` to the other (an illegal cast at runtime). Only alias/interface SHAPES collapse; a `class` keeps
		// `ensureClass`'s own nominal name-based key.
		const structural	= T.typeKey(resolved);
		const shared		= classes.get(structural);
		if (shared) {
			classes.set(key, shared);
			if (!shapeEntries.has(shared))
				shapeEntries.set(shared, entry);
			return shared;
		}
		// `interface X extends Y` puts Y's fields first, so X's struct can be a wasm SUBTYPE of Y's: an X then IS a Y.
		const top		= T.resolve(scope, ref);
		// An alias of a named shape IS that shape (`type CallSig = JS.CallSig<Type>`): same struct, same supertype. Read off what the alias
		// DECLARES, not what `resolve` expands it to -- an interface that extends another expands to an intersection, and the alias then built a
		// SECOND struct nothing could convert to the first.
		const aliased	= entry.typeParams?.length ? T.substituteType(entry.type, T.typeArgMap(entry.typeParams, typeArgs)) : entry.type;
		const aliasRef	= aliased.type === 'ref' && aliased.name !== name ? aliased
						: top.type === 'ref' && top.name !== name ? top : undefined;
		if (aliasRef) {
			const target = ensureClassRef({ ...aliasRef, declScope: (aliasRef.declScope as Scope | undefined) ?? scope });
			if (target) {
				classes.set(key, target);
				return target;
			}
		}
		const baseRef	= top.type === 'intersection' && top.types[0].type === 'ref' ? top.types[0] : undefined;
		const base		= baseRef && ensureClassRef({ ...baseRef, declScope: baseRef.declScope ?? scope });
		const reached	= classes.get(key);
		if (reached)
			return reached;
		const info		= buildObjectShape(key, base ? membersOverBase(resolved.members, base) : resolved.members, ref, name, !everExtended.has(name), shapeKey(resolved.members));
		classes.set(structural, info);
		shapeEntries.set(info, entry);
		// Deferred: a shape merged into a twin could not take the supertype afterwards.
		if (base && linkSupertype(info, base))
			return info;
		return layoutTwin(info, key, structural);
	}

	// `members` ordered with `base`'s fields first, in its order, so the struct can be a wasm subtype of the base's. The base's
	// expando fields (and `#ext`) are part of its layout, so they are repeated in place, or a base gaining one stops being the supertype.
	function membersOverBase(members: TS.TypeMember[], base: ClassInfo): TS.TypeMember[] {
		const basePos	= new Map(base.fields.map((f, i) => [f.name, i]));
		const at		= (m: TS.TypeMember) => ('key' in m && typeof m.key !== 'object' ? basePos.get(String(m.key)) : undefined) ?? Infinity;
		const declared	= new Set(members.flatMap(m => 'key' in m && typeof m.key !== 'object' ? [String(m.key)] : []));
		const inherited	= base.fields.filter(f => !declared.has(f.name)).map(f => TS.TypeProperty(f.name, hiddenFieldType(f.name), ['optional']));
		return [...members, ...inherited].sort((a, b) => at(a) - at(b));
	}

	// The struct for an object type `flat` (`t` resolved, then flattened): a declared shape with these members, else -- where `t` is
	// written as an intersection over a named shape -- one laid out over it, else its own anonymous one.
	function objectShapeOf(t: Type, flat: TS.ObjectType): ClassInfo | undefined {
		const over = () => t.type === 'intersection' ? ensureIntersectionShape(t, flat) : undefined;
		return matchObjectShapeByType(flat, () => over() ?? ensureAnonObjectShape(flat)) ?? ensureAnonObjectShape(flat);
	}

	// An intersection over ONE named shape (`{type: 'call'} & CallSig`) is laid out over that shape, as `interface X extends Y` is, so a
	// value of it IS one: a wasm subtype, converting for free where an anonymous struct could not convert at all.
	function ensureIntersectionShape(t: TS.IntersectionType, flat: TS.ObjectType): ClassInfo | undefined {
		const bases = t.types.flatMap(p => {
			const cls = p.type === 'ref' ? ensureClassRef({ ...p, declScope: p.declScope ?? global }) : undefined;
			return cls && shapeEntries.has(cls) ? [cls] : [];
		});
		if (bases.length !== 1 || flat.members.some(m => m.type !== 'property' && m.type !== 'method'))
			return undefined;
		const key		= T.typeKey(t);
		const existing	= classes.get(key);
		if (existing)
			return existing;
		const info = buildObjectShape(key, membersOverBase(flat.members, bases[0]), t, key, true);
		info.anonymous = true;
		linkSupertype(info, bases[0]);
		return info;
	}

	// A STRUCTURAL shape's identity is its physical layout -- fields sorted, each by its stored wasm type -- since
	// wasm struct fields are invariant and two structs with one layout could never convert. Final, supertype-free only.
	function layoutTwin(info: ClassInfo, ...aliases: string[]): ClassInfo {
		const sub = types.get(info.typeIndex);
		if (info.superClass || !('final' in sub) || !sub.final)
			return info;
		const fieldKey	= (w: W.Type) => W.isRef(w) && classes.get(w.ref) ? `ref:${classes.get(w.ref)!.name}:${!!w.nullable}` : W.typeKey(w);
		const layout	= `#layout#${info.fields.map(f => `${f.name}${f.optional ? '?' : ''}:${fieldKey(f.wtype)}`).sort().join(',')}`;
		const twin		= classes.get(layout);
		if (!twin) {
			classes.set(layout, info);
			return info;
		}
		// Refused once a later type already names `info`'s own index: repointing the key would strand it.
		if (twin === info || types.slice(info.typeIndex + 1).some(t => W.mentionsTypeIndex(t, info.typeIndex)))
			return info;
		// The twin will hold values of both, so its TS type becomes their field-wise union: sound for either, and it
		// keeps every tag `matchObjectShape`'s discriminant tiebreak reads. No representable union, no merge.
		const merged = T.typeId(twin.thisTsType) === T.typeId(info.thisTsType) ? twin.thisTsType : T.unionShapes(twin.thisTsType, info.thisTsType, global);
		if (!merged)
			return info;
		twin.anonymous &&= info.anonymous;
		for (const k of aliases)
			classes.set(k, twin);
		if (merged !== twin.thisTsType) {
			twin.thisTsType = merged;
			classes.set(T.typeKey(merged), twin);
		}
		return twin;
	}

	// An anonymous inline object type has no name, so `T.typeKey` is its cache key and its identity is its physical layout (`layoutTwin`):
	// shapes that print differently but store alike share one struct; `anonShapeVetting` breaks the recursion a member leading back here would cause (a cyclic shape can't be built anyway).
	const anonShapeVetting = new Set<string>();

	function ensureAnonObjectShape(obj: TS.ObjectType): ClassInfo | undefined {
		if (!isStructLayout(obj.members))
			return undefined;
		const key		= T.typeKey(obj);
		const existing	= classes.get(key);
		if (existing)
			return existing;
		if (anonShapeVetting.has(key))
			return undefined;
		// Every property needs a representation before this commits to a struct: failing here, not inside `addField`, leaves the caller its `wasmTypeOf` fallback.
		// The case that forced it: a namespace object (`import * as T`) is a valid object TYPE whose members include classes and type aliases, yet is never a value.
		anonShapeVetting.add(key);
		try {
			if (obj.members.some(m => m.type === 'property' && !(m.typeAnnotation && typeOf(m.typeAnnotation)))
				|| (obj.members.some(m => m.type === 'call') && !callSignaturesWtype(obj.members)))
				return undefined;
		} finally {
			anonShapeVetting.delete(key);
		}
		const info = buildObjectShape(key, obj.members, obj, key, true);
		info.anonymous = true;
		return layoutTwin(info, key);
	}

	// Resolves fields and the struct type eagerly, but only collects method/ctor decls -- building each is
	// deferred to `ensureMethod`/`ensureCtor`, the same lazy treatment `ensureFunc` gives top-level functions.
	function ensureClass(name: string, typeArgs?: Type[], declScope?: Scope): ClassInfo | undefined {
		// A generic instantiation whose surviving type argument (`Box<number>`) is cached under a composite key -- keying off
		// the *unresolved* class name, not `T.resolve`'s expanded form, keeps identically-shaped classes from colliding.
		// A machine-type argument (`TypedArray<u8>`/`<i32>`) keys by its machine type: `T.resolve` collapses every one to plain
		// `number`, which would key `TypedArray<u8>` and `<i32>` identically and share one physical class.
		// An argument earns its own physical instantiation only when it changes the LAYOUT -- when the value is stored
		// UNBOXED. A reference type occupies one ref slot, so swapping refs cannot reshape a struct; only a scalar
		// (`number` -> f64, `boolean` -> i32) or a typed-array tag can. Everything else collapses to `any`, so a conversion
		// between those instantiations is identity rather than an unsatisfiable `cannot convert ref:X<a> to ref:X<b>` --
		// wasm struct fields are mutable, hence invariant.
		// Restricted to a class with no METHODS of its own: a method body is compiled against the instantiation it was
		// reached through (`substElemMethods`), so merging two whose methods differ runs code built for one layout against
		// the other -- measured as a wasm `invalid struct index`. `Array` is exempt: its methods are compiled for the boxed
		// `any` form, the point of collapsing to it, while a DATA-shaped generic (`Terminal<T>`, `Rule<T>`) has no such code.
		// The trigger is structural, never a class name.
		const classDecl = LIB_DECL_MAP.get(name) ?? userGenericClassDecls.get(name) ?? declScope?.decl(name);
		if (name === 'Array' || (classDecl?.type === 'class_decl' && !classDecl.body.some(m => m.type === 'method')))
			typeArgs = typeArgs?.map(t => ownsLayout(t, global) ? t : T.ANY);
		// A class declared outside the entry module is keyed by its module too, as a shape is: `W.FunctionContext` and wasm-backend.ts's own
		// `FunctionContext extends W.FunctionContext` are two classes.
		const tag	= classDecl?.type === 'class_decl' ? moduleTag(stmtHomeModule.get(classDecl)) : '';
		const key	= (typeArgs?.length ? `${name}<${typeArgs.map(t => layoutArgKey(t, global)).join(',')}>` : name) + tag;
		// A non-generic top-level class is seeded into `classes` eagerly, unprocessed; a generic one is cached here per instantiation. `thisWtype` is set once
		// the representation is decided, which is also what stops re-entry -- not `typeIndex`, which stays -1 for good on a scalar-backed class (`Number`).
		let info = classes.get(key);
		if (info && otherDeclaration(info, name, declScope))
			info = undefined;
		if (info?.thisWtype)
			return info;

		if (!info) {
			// A lib-internal class is seeded lazily on first reference. `declScope?.decl(name)` resolves a non-entry module's own class (never eagerly seeded) through
			// the same scope chain `ensureObjectShape` uses, landing on the *real* declaration rather than that fallback's structural-shape-only reconstruction, which has no methods.
			let decl = LIB_DECL_MAP.get(name) ?? userGenericClassDecls.get(name) ?? declScope?.decl(name);
			if (decl?.type !== 'class_decl') {
				// `resolveClassAlias` covers only a *lib* alias to a real class name, never a generic; a generic interface/type-alias reference
				// (with or without explicit type args, e.g. `TypeParam` bare or `TypeParam<T>`) goes straight to `ensureObjectShape`.
				if (!typeArgs?.length) {
					const alias = resolveClassAlias(name);
					if (alias)
						return ensureClass(alias.name, alias.typeArgs, declScope);
				}
				// Checked before the structural fallback, which would otherwise reconstruct a shape-only stand-in (no constructor, no methods) for what is really a known class,
				// and cache it under this very name -- so whichever of the annotation and the `new` resolves first wins for both.
				// `?? global`: a bare ref annotation often carries no `declScope`, and the alias is a top-level declaration either way.
				const aliased = classAliasTarget(name, declScope ?? global);
				if (aliased && (aliased.name !== name || aliased.scope !== (declScope ?? global)))
					return ensureClass(aliased.name, typeArgs, aliased.scope);
				return ensureObjectShape(name, typeArgs, declScope);
			}
			// Read off the ORIGINAL declaration -- a generic instantiation replaces `decl` with a
			// name-substituted copy just below, which `stmtHomeModule` has never seen.
			const homeModule	= stmtHomeModule.get(decl);
			const generic		= !!decl.typeParams?.length;
			if (decl.typeParams?.length) {
				const got = typeArgs?.length ?? 0;
				if (!typeArgs || typeArgs.length !== decl.typeParams.length) {
					for (let i = got; i < decl.typeParams.length; i++)
						if (!decl.typeParams[i].default)
							throw `class '${name}' needs ${decl.typeParams.length} explicit type argument(s)`;
				}
				decl = substituteClassTypeParam(decl, new Map(decl.typeParams.map((p, i) => [p.name, i < got ? typeArgs![i] : p.default!])));
			}
			// `thisTsType` must be a real reference to this class -- the ref itself carries the real name and type arguments, not the mangled composite cache key,
			// or `this.length`/`this[i]` can't resolve (`T.lookupMember` silently falls back to `any`).
			const home			= moduleScopeOf(homeModule);
			const thisTsType	= { ...TS.RefType(name, typeArgs), declScope: home ?? declScope };
			// Re-checked, as `instantiateDecl` re-checks a generic function's instance: its bodies' stamped types must be this
			// instantiation's, or a local initialised from `V[]` got the generic's erased `any[]` slot for a real `number[]`.
			if (generic) {
				Object.assign(decl, { instanceOf: thisTsType });
				checkHoisted([decl], new Scope(home ?? libGlobal));
			}
			info = new ClassInfo(key, -1, decl, thisTsType);
			info.declScope		= declScope;
			info.homeModule		= homeModule;
			info.instantiation	= generic;
			classes.set(key, info);
			// Known by its declaration, as a shape is: another module's same-named interface (`Predicate`) must not take this class.
			const entry = home?.type(name);
			if (entry)
				classEntries.set(info, entry);
		}

		const decl = info.decl;

		// A constructor with its own explicit 'return' overrides `this` entirely (a scalar or array result, never a struct) and must never get a struct type
		// index, not even an unused placeholder (a self-referential field would then point at a struct nothing constructs). Pre-scanned before any field
		// type resolves, so the field loop below already knows whether to allocate that placeholder; `checkerTypeOf` is the checker's own inference, not this file's `typeOf`/`ensureClass`.
		let returnType: Type | undefined;
		for (const m of decl.body as TS.ClassMember[]) {
			if (m.type === 'method' && m.key === 'constructor' && m.body) {
				const last = m.body[m.body.length - 1];
				if (last?.type === 'return' && last.argument)
					returnType = checkerTypeOf(unwrapAs(last.argument), m.scope as Scope);
				break;
			}
		}

		// Resolved *before* this class's own `typeIndex` is allocated: wasm-GC requires a `sub` type's declared supertype to be a *lower* type-section index
		// than itself (a supertype is a validation-time relationship, unlike an ordinary field reference, which may forward-reference within the same rec group).
		// This guarantees `superInfo.typeIndex < info.typeIndex` however deep the chain goes.
		// Real regression: a 3-level chain (`C extends B extends A`) fails to load with "forward-declared supertype" if the superclass is resolved
		// after this class's own placeholder -- resolving `C`'s superclass then recurses into `B`'s and `A`'s, giving `A` the *highest* index.
		// Seeding `info.fields`/`fieldIndex` here also lets `addField`'s redeclaration guard see inherited fields and keeps the supertype's fields
		// first, as the exact prefix wasm-GC struct subtyping requires.
		// Doesn't reopen the self-reference case: a field of this class's *own* type resolves later, in the per-member loop below, after the
		// placeholder exists; this block resolves only ancestors.
		if (decl.superClass && !returnType) {
			const superRef = superClassRef(decl.superClass);
			if (!superRef)
				throw `only a named superclass ('class ${name} extends Base', 'extends NS.Base' or 'extends Base<T>') is supported`;
			const superName = superRef.name;
			const superInfo = ensureClassRef({ ...superRef, declScope: info.declScope });
			if (!superInfo)
				throw `unknown superclass '${superName}' for class '${name}'`;
			if (W.isArr(superInfo.thisWtype) || superInfo.typeIndex === -1)
				throw `'${name}' can't extend '${superName}' -- extending an array/scalar-backed class (a constructor with its own explicit 'return') is not supported`;
			info.superClass = superInfo;
			info.fields.push(...superInfo.fields);
			superInfo.fieldIndex.forEach((idx, fname) => info.fieldIndex.set(fname, idx));
		}

		if (returnType) {
			if (decl.superClass)
				throw `'${name}' can't both extend '${(decl.superClass as any).name}' and have a constructor with its own explicit 'return' -- not supported`;
			const result = typeOf(returnType);
			if (!result || (typeof result !== 'string' && !W.isArr(result)))
				throw `'${name}'s constructor returns a value of an unsupported shape for 'this' -- only a scalar or array-shaped result is supported`;
			info.thisWtype = result;
			info.typeIndex = typeof result === 'string' ? -1 : types.array(result.arr);
		} else {
			// How an instance is physically represented (struct vs. array) is the separate, towasm-only `thisWtype`, allocated with a real `typeIndex`
			// before any of *this* class's own field types resolve, so a reentrant `ensureClass` for this same `key` finds `typeIndex` real and
			// short-circuits instead of recursing (see `ensureObjectShape`'s identical comment). The superclass is already resolved, so this
			// index is the largest in the chain so far, never a forward reference.
			info.thisWtype = { ref: key };
			info.typeIndex = types.add({ kind: 'struct', fields: [] });
		}

		const addMethod = (key: string, m: MethodMember) => {
			const list = info.methodDecls.get(key);
			if (list)
				list.push(m);
			else
				info.methodDecls.set(key, [m]);
		};

		const inlineDecls: { key: string; value: JS.Call<Type>; typeParams?: string[] }[] = [];

		if (decl.abstract)
			throw `abstract class '${name}' is not supported`;

		// `decl.body`'s declared element type (`JS.ClassMember<Type>`) has no `index_signature` variant -- only `TS.ClassMember` adds it, and `decl`
		// is always parsed by ts-parser.ts, so a real index-signature member can appear and is widened to what is actually parsed, not narrowed by
		// which shared interface declared `body`.
		// A field's type resolves in the class's OWN module: an un-annotated field takes its type from the constructor or initializer, which may
		// name things only that file declares, and `T.lookupMember(thisTsType, ...)` needs the class's own name resolvable -- it isn't in an
		// importer that only ever wrote `C.Output`.
		const homeScope = info.declScope ?? libGlobal;
		// Decided before the first field is added: it changes how every one of them is STORED, and a struct type is fixed once built.
		info.earlyThis = ctorNeedsEarlyThis(decl);
		for (const m of decl.body as TS.ClassMember[]) {
			try {
				if (m.type === 'field'/* && !hasMod(m, 'static')*/) {
					if (typeof m.key === 'object')
						throw `computed field names in '${name}' are not supported`;
					if (isAsm(m.value))
						inlineDecls.push({ key: String(m.key), value: m.value! });
					// A `declare` over an INHERITED field only re-narrows its type (`declare superClass?: ClassInfo`); the slot is the base's.
					else if (!m.modifiers?.includes('static') && !(hasMod(m, 'declare') && info.superClass?.fieldIndex.has(String(m.key))))
						// Neither an annotation nor an initializer (`opts;`): the type lives only in the constructor's `this.opts = ...`,
						// which `classShapes` already infers -- ask the checker for the member rather than re-deriving it from the AST here.
						addField(info, String(m.key), (t => t && openedAs(m, t))(m.typeAnnotation ?? (m.value ? checkerTypeOf(m.value, homeScope) : T.lookupMember(info.thisTsType, String(m.key), homeScope))), !m.value && (hasMod(m, 'optional') || hasMod(m, 'declare')));

				} else if (m.type === 'method') {
					// A computed name with a static spelling (`[Symbol.iterator]`, via `T.memberKey`) is registered under it:
					// the iteration protocol calls it by that name. A truly dynamic one has no name to call it by.
					const key = T.memberKey(m.key);
					if (key !== undefined) {
						const value = isAsmMethod(m);
						if (value) {
							inlineDecls.push({ key, value, typeParams: m.typeParams?.map(tp => tp.name) });
						} else {
							addMethod(key, m);
						}
					}

					if (m.key === 'constructor') {
						for (const p of m.params) {
							if (T.isParamProperty(p)) {
								if (typeof p.key !== 'string')
									throw `computed field names in '${name}' are not supported`;
								addField(info, p.key, (t => t && openedAs(p, t))(p.typeAnnotation ?? (p.default ? checkerTypeOf(p.default, libGlobal) : undefined)), !p.default && hasMod(p, 'optional'));
							}
						}
					}

				} else if (m.type === 'get' || m.type === 'set') {
					if (typeof m.key !== 'object') {
						const key = accessorKey(m.type, String(m.key));
						const value = isAsmMethod(m);
						if (value) {
							inlineDecls.push({ key, value});
						} else {
							addMethod(key, m);
						}
						(m.type === 'get' ? (info.getterNames ??= new Set()) : (info.setterNames ??= new Set())).add(String(m.key));
					}

				} else if (m.type !== 'index_signature') {
					// Type-checking-only -- real indexing goes through the generic `get`/`set`/array-kind paths (`case 'index'`), never a declared index signature itself, so there's nothing for this pass to do with it.
					throw `unsupported class member kind '${m.type}' in '${name}'`;
				}
			} catch (e) {
				//console.log(e);
				throw new W.Error(e as any, m).inModule(info.homeModule ?? '.');
			}
		}

		// An implicit constructor, as real TS synthesizes one: empty for a base class, and for a derived class the base's
		// own parameter list forwarded through `super(...)` (the real list, not the spread `super(...args)` this back end does not support).
		// Without it, `class A { x = 5 }` and `class B extends A {}` failed with "needs an explicit constructor" once instantiated.
		if (!info.methodDecls.has('constructor')) {
			const superCtor = info.superClass?.methodDecls.get('constructor');
			const params	= superCtor?.length === 1 ? superCtor[0].params : [];
			addMethod('constructor', {
				type:	'method',
				key:	'constructor',
				params,
				body:	info.superClass
					? [JS.ExprStmt(JS.Call({ type: 'super' } as Expr, params.map(p => Identifier(p.key as string))))]
					: [],
			} as unknown as MethodMember);
		}

		// The pre-scan above already fixed `thisWtype`/`typeIndex`; the ordinary struct case only patches its real field list into the placeholder registered earlier.
		if (!returnType) {
			addExpandoFields(info, name + moduleTag(stmtHomeModule.get(decl)));
			types.set(info.typeIndex, {
				final:		!everExtended.has(name),
				supertypes: info.superClass ? [info.superClass.typeIndex] : [],
				type: {
					kind: 'struct',
					fields: info.fields.map(f => ({ type: toValType(f.wtype), mut: true }))
				}
			});
		}

		const defines: Record<string, string|number> = {this: info.typeIndex};
		if (W.isArr(info.thisWtype))
			defines.elem = info.thisWtype.arr;

		if (decl.typeParams && typeArgs) {
			decl.typeParams.forEach((p, i) => {
				const m = T.machineOf(typeArgs[i], global);
				if (m) {
					defines[p.name] = m;
				} else {
					// A reference argument's tag is `ref`: a `(switch $T ...)` over it then takes its `(else ...)` arm.
					const w = typeOf(typeArgs[i]);
					defines[p.name] = typeof w === 'string' ? w : 'ref';
				}
			});
		}

		// Seeded from the base's, as `info.fields` already is: an `__asm` method is not in `methodDecls`, so a
		// subclass that does not inherit these has no `__get`/`__set` at all (`isPositional` answers no, and an
		// indexed read falls off the bounded path). The base's are keyed to the BASE's `$T` defines, which is
		// exactly what an inherited body must run with.
		const inlineMethods = new Map<string, Builtin<Inline>>(info.superClass?.inlineMethods);
		for (const i of inlineDecls) {
			try {
				inlineMethods.set(i.key, makeAsm(i.value, { typeOf, typeIndexOf: w => W.isArr(w) ? types.array(w.arr) : undefined }, defines, i.typeParams));
			} catch (err) {
				throw new W.Error(err as any, i.value).inModule(info.homeModule ?? '.');
			}
		}

		if (inlineMethods.size)
			info.inlineMethods = inlineMethods;

		return info;
	}

	// Real, general support for `Object.defineProperty(target, key, {value, ...})` when `key` isn't a declared field
	// on `target`'s class: a wasm-GC struct can't gain a field at runtime, so this is modeled as real inheritance --
	// one synthesized subclass of the *plain* base class (`ensureClassExtension` is keyed by, and only ever called
	// with, it -- never the extended form itself), never a name-specific hack or a universal field on every class.
	// It carries a real field per statically-enumerable key ever `defineProperty`'d onto any value of the class
	// anywhere in the program (unioned across every such site, boxed `any` since each call site's own `value` has its
	// own type), or a `Map<string, any>` catch-all once any key is not a compile-time literal (`pendingExtensions`'s
	// comment). `everExtended.add(base.name)` must run before `base`'s struct type is finalized -- `ensureGenericFunc`'s
	// hook (which runs before any type argument can reach `ensureClass`) is the fast path but insufficient, since
	// `base` may already be finalized through an earlier reference (found the hard way: `const p: Point = {...}`
	// before the generic call needing it); patched retroactively below as a safety net for exactly that case.

	// Emits a constructor body statement-by-statement, except a `super(...)` call is *inlined*: the superclass's body
	// runs right there against the same `this` (one physical allocation for the whole hierarchy -- see `ensureClass`'s
	// field-layout comment). Recurses for a multi-level chain, resolved against each level's own `superClass`.
	function emitCtorStatements(ctor: MethodMember, cls: ClassInfo, ctx: FunctionContext, setField: (field: string, value: Expr) => void): void {
		const params = ctor.params;
		const stmts	= ctor.body!;

		// A parameter property (`constructor(public x: number)`) has no `this.x = x` statement in `stmts`: real TS synthesizes it and
		// runs it *before* any class-level field initializer, even one textually declared above the constructor (verified against
		// real TS output; `y = this.x + 1` needs `x` assigned first). Only `ensureCtor`'s `struct.new_default` paths reach here
		// (scalar-only, or an `earlyThis` class); the explicit-collection path already assigns parameter properties itself
		// (`ensureCtor`'s own `setField` loop over `params`).
		const emitParamPropertyInits = () => {
			for (const p of params) {
				if (T.isParamProperty(p))
					setField(p.key as string, Identifier(p.key as string));
			}
		};
		// A class-level field initializer (`tag: number = 99`) isn't in the constructor's `body`; it is synthesized as `this.field = value`
		// after `super(...)` (if any) and before the rest of this constructor's body, matching real JS/TS order. Only `ensureCtor`'s
		// `struct.new_default` paths reach here; the explicit-collection path's own `initField` already does this.
		const emitOwnFieldInits = () => {
			for (const m of cls.decl.body) {
				if (m.type === 'field' && !m.modifiers?.includes('static') && m.value)
					setField(m.key as string, m.value);
			}
		};

		if (!stmts.some(st => st.type === 'expression' && st.expression.type === 'call' && st.expression.callee.type === 'super')) {
			emitParamPropertyInits();
			emitOwnFieldInits();
		}
		for (const st of stmts) {
			if (st.type === 'expression' && st.expression.type === 'call' && st.expression.callee.type === 'super') {
				const call = st.expression;
				const superClass = cls.superClass;
				if (!superClass)
					throw `no superclass -- 'super(...)' is not supported here`;
				if (call.arguments.some(a => a.type === 'spread'))
					throw `'super(...)': a spread argument is not supported`;
				const superDecls = superClass.methodDecls.get('constructor');
				if (!superDecls)
					throw `superclass '${superClass.name}' needs an explicit constructor for 'super(...)' to call`;
				const superCtor = implementationOf(superClass, undefined, superDecls, call, ctx);
				if (!superCtor.body)
					throw `needs a body (overload signatures are not supported)`;

				// Binds the base ctor's param names to this call's arguments as ordinary `var_decl`s (reusing the local-declaration path, destructuring desugaring included).
				// The nested scope closes once the base body has run, matching real TS: those params aren't visible to the rest of *this* ctor.
				ctx.inScope(() => {
					superCtor.params.forEach((p, i) => {
						const argExpr = call.arguments[i] ?? p.default;
						if (!argExpr)
							throw `'super(...)': missing argument parameter '${describeBinding(p.key)}'`;
						emitStmt(JS.VarDecl('const', JS.Var(p.key, argExpr, p.typeAnnotation)), ctx);
					});
					emitCtorStatements(superCtor, superClass, ctx, setField);
				});
				emitParamPropertyInits();
				emitOwnFieldInits();
			} else
			// An ordinary `this.field = value` in the constructor body is routed through `setField` like the two synthesized sources
			// above -- required for an object-typed field (`this.inner = new Other(...)`), whose value must be collected before
			// `struct.new`; `setField` itself (see `ensureCtor`) knows whether this is still mid-collection or `this` already exists.
			// Gated on `cls.fieldIndex` (this constructor's own level's data fields only, not an inherited one from a *further*
			// subclass, matching real TS scoping), so an accessor write (`this.someSetter = x`) falls through to `emitStmt` and is
			// caught by `case 'this'`'s guard if attempted too early -- calling a setter needs a real `this` receiver.
			if (st.type === 'expression' && st.expression.type === 'assign' && !st.expression.operator && st.expression.target.type === 'member' && st.expression.target.object.type === 'this' && cls.fieldIndex.has(st.expression.target.property)) {
				setField(st.expression.target.property, st.expression.value);
			} else {
				emitStmt(st, ctx);
			}
		}
	}

	// The checker's resolution of a call on `owner`: of its method `name`, else of its constructor. A call codegen makes itself is resolved
	// as that same call on a value of the implementation's own type, bound in a scope of its own.
	function resolvedCall(owner: ClassInfo, name: string | undefined, call: CallSite, ctx: FunctionContext): CheckedCall | undefined {
		if (!Array.isArray(call))
			return callOf(call, ctx.scope);
		const self		= owner.thisTsType;
		const recvType	= name ? self : self.type === 'ref' ? { type: 'typeof' as const, name: self.name, typeArgs: self.typeArgs, declScope: self.declScope } : undefined;
		if (!recvType)
			throw `internal: '${owner.name}' has a constructor but no class to construct`;
		const scope = new Scope(ctx.scope);
		scope.addValue('$receiver', recvType);
		const receiver: Expr = Identifier('$receiver');
		return callOf(name ? JS.Call(JS.Member(receiver, name), call) : { type: 'new', callee: receiver, arguments: call }, scope);
	}

	// A statically-`any` argument fits every overload but its type is known only at run time, so it takes the candidate whose
	// parameter accepts every other's -- the one written to tell them apart.
	function implementationOf(owner: ClassInfo, name: string | undefined, decls: MethodMember[], call: CallSite, ctx: FunctionContext): MethodMember {
		const bodied = decls.filter(d => d.body);
		if (bodied.length < 2)
			return bodied[0] ?? decls[0];
		const chosen	= namedBody(bodied, resolvedCall(owner, name, call, ctx), `${owner.name}.${name ?? 'constructor'}`);
		const args		= argsOf(call);
		const dynamic	= args.map((a, i) => T.isAny(ctx.narrowedTypeOf(a)) ? i : -1).filter(i => i >= 0);
		if (!dynamic.length)
			return chosen;
		const paramAt	= (d: MethodMember, i: number) => T.paramTypeAt(T.FixSig(d, T.ANY), i, ctx.scope);
		const fitting	= bodied.filter(d => d.params.length >= args.length);
		return fitting.find(d => dynamic.every(i => fitting.every(o => T.isAssignable(paramAt(o, i) ?? T.ANY, paramAt(d, i) ?? T.ANY, ctx.scope)))) ?? chosen;
	}

	function ensureCtor(cls: ClassInfo, call: CallSite, callerCtx: FunctionContext): FuncInfo {
		const decls = cls.methodDecls.get('constructor');
		if (!decls)
			throw `class '${cls.name}' needs an explicit constructor`;

		const chosen = implementationOf(cls, undefined, decls, call, callerCtx);
		// A parameter whose argument is a different struct specializes the constructor for it, as `ensureStructuralInstance` does a function.
		const params = chosen.body && structuralParams(chosen.params, argsOf(call), callerCtx);
		return ensureCtorDecl(cls, chosen, params ? { ...chosen, params } : undefined);
	}

	// One constructor overload's compiled function, however it was chosen: by a call's arguments, or as `adoptingDecl`'s. `specialized`:
	// the overload with parameters retyped to its arguments' structs (`structuralParams`), compiled apart.
	function ensureCtorDecl(cls: ClassInfo, overload: MethodMember, specialized?: MethodMember): FuncInfo {
		const decls			= cls.methodDecls.get('constructor')!;
		const ctor			= specialized ?? overload;
		const key			= (decls.length > 1 ? `${cls.name}.constructor#${decls.indexOf(overload)}` : `${cls.name}.constructor`)
			+ (specialized ? structuralKey('', specialized.params) : '');
		const existing		= funcs.get(key);
		if (existing)
			return existing;

		const params		= resolveParams(ctor.params, cls.declScope ?? libGlobal);
		if (ctor.rest?.typeAnnotation)
			params.push({key: ctor.rest.key, wtype: restParamWtype(ctor.rest.typeAnnotation)!, tsType: ctor.rest.typeAnnotation});

		//const thisWtype	= cls.thisType;
		const thisWtype		= cls.thisWtype!;

		const {funcIndex, typeIndex} = types.func(toParams2(params), toResults(thisWtype));
		const info: FuncInfo = { params: params.map(r => r.wtype), result: thisWtype, funcIndex, typeIndex, defaults: defaultsWithImplicitUndefined(ctor.params), resolvedParams: params, hasRest: !!ctor.rest?.typeAnnotation };
		funcs.set(key, info);

		// A constructor's own `return;` never carries a value (real TS syntax already enforces that at the checker level) -- it just means
		// "stop early, `this` is the result", the same value every real exit already emits via `ctx.ctorThis`.
		const ctorOnReturn: ReturnHandler = {
			wtype: () => undefined,
			emit(ctx, argument) {
				if (argument)
					throw 'a constructor cannot return a value';
				ctx.emit(I.local.get(ctx.ctorThis!.index), I.return);
			},
		};

		worklist.push(W.withCatch(() => {
			// The DECLARING module's own scope (`ensureClass`'s `declScope`/`homeModule`), not the entry's -- a ctor body naming something only its own file
			// declares (a non-exported module-level const, a sibling class) must resolve it there, the same pairing `compileFunc` gives a top-level function;
			// `libGlobal` remains the fallback for a lib class or a synthesized shape. `declScope` is whatever type reference first built this class, which
			// need not be its own module (a helper `use(h: Holder)` in another file), and then its body could not see its own imports at all -- an
			// `import * as TS` call inside it read as an unresolved identifier.
			const ctx		= new FunctionContext(key, new Scope(moduleScopeOf(cls.homeModule) ?? cls.declScope ?? libGlobal), plainReturn(thisWtype), cls, cls.homeModule);
			ctx.ownBody = ctor.body!;
			ctx.declareParams(params).forEach(st => emitStmt(st, ctx));
			hoistVars(ctor.body!, params, ctx);
			// This constructor supplies `this` directly via its own return value (`ctorReturnsValue`)
			// `cls`'s own `thisWtype`/`typeIndex` already say so; ordinary statement compilation does the right thing once `ctx.ctorThis` is unset.
			const last = ctor.body?.at(-1);
			if (last?.type === 'return' && last.argument) {
				emitStmts(ctor.body!, ctx);

			// Defaultability is a whole-struct-type property, not per-field -- one object-typed field forces the collect-then-`struct.new` path for the whole class.
			} else if (!cls.earlyThis && cls.fields.some(f => typeof f.wtype !== 'string')) {

				// An optional field is never *required* to be assigned, but it still needs a real value for the single `struct.new` below: seed it with its
				// own null default up front (`addField` already forced its wtype nullable) and leave it out of `remaining`.
				const remaining	= new Set(cls.fields.filter(f => !f.optional).map(f => f.name));
				const values	= new Map<string, W.Local>();
				ctx.ctorFields	= values;
				// No real local for `this` yet, but `checkerTypeOf` still needs its static type to resolve a chained read like `this.p.x` (`p` already
				// collected) down to `p`'s own class -- the same scope-only registration `declareCaptured` uses for closure captures.
				ctx.scope.addValue('this', cls.thisTsType);

				for (const f of cls.fields) {
					if (f.optional) {
						const local = ctx.declareLocal(`$field$${f.name}`, f.wtype);
						ctx.emitDefaultValue(f.wtype, types, toValType);
						ctx.emit(I.local.set(local.index));
						values.set(f.name, local);
					}
				}

				const materializeThis = () => {
					for (const f of cls.fields)
						ctx.emit(I.local.get(values.get(f.name)!.index));
					ctx.emit(I.struct.new(cls.typeIndex));
					// PINNED: `this` belongs to the constructor, not to whatever scope happened to be open when the last field landed -- a base class with a
					// param-property constructor completes it inside the `super(...)` call's own scope, and closing that took `this` with it, so any
					// `this.field = ...` after `super(...)` failed with "unresolved identifier 'this'".
					const thisLocal = ctx.declareValue('this', thisWtype, cls.thisTsType, true);
					ctx.ctorThis = thisLocal;
					ctx.onReturn = ctorOnReturn;
					ctx.ctorFields = undefined;
					ctx.emit(I.local.set(thisLocal.index));
				};
				// Every field optional (or none at all): nothing will ever empty `remaining` from inside the
				// callback below, so `this` has to exist before the body runs at all.
				if (!remaining.size)
					materializeThis();

				emitCtorStatements(ctor, cls, ctx, (field: string, value: Expr) => {
					// `this` genuinely exists (every field collected earlier, or this is a reassignment): an ordinary field write, same as the scalar-only path's `setField`.
					// Only reachable via `emitCtorStatements`'s explicit-`this.field=value` interception -- a param property/field initializer always precedes an empty `remaining`.
					if (!ctx.ctorFields) {
						emitStmt({
							type: 'expression',
							expression: Assign<Expr, JS.assignableOps>(Member<Expr>({ type: 'this' }, field), value),
						}, ctx);
						return;
					}
					const wtype = cls.fields[cls.fieldIndex.get(field)!].wtype;
					// An optional field already holds its seeded default, and a field may be assigned twice before `this` exists: one local.
					// PINNED, as `this` is: a base class's field lands inside the `super(...)` call's scope, whose close would free its slot for the next field.
					const local = values.get(field) ?? ctx.declareLocal(`$field$${field}`, wtype, true);
					emitAs(value, ctx, wtype);
					ctx.emit(I.local.set(local.index));
					values.set(field, local);
					remaining.delete(field);
					if (!remaining.size)
						materializeThis();
				});
				if (remaining.size)
					throw `never assigns field(s) ${[...remaining].join(', ')}`;
				ctx.emit(I.local.get(ctx.ctorThis!.index), I.return);

			} else {
				const thisLocal = ctx.declareValue('this', thisWtype, cls.thisTsType);
				ctx.ctorThis = thisLocal;
				ctx.onReturn = ctorOnReturn;
				ctx.emit(
					I.struct.new_default(cls.typeIndex),
					I.local.set(thisLocal.index),
				);
				emitCtorStatements(ctor, cls, ctx, (field: string, value: Expr) => emitStmt({
					type: 'expression',
					expression: Assign<Expr, JS.assignableOps>(Member<Expr>({ type: 'this' }, field), value),
				}, ctx));
				ctx.emit(I.local.get(ctx.ctorThis!.index), I.return);
			}

			info.body = ctx.toFuncBody(ctor.params.length + (ctor.rest ? 1 : 0), toValType);
		}, key));
		return info;
	}

	// An empty argument list only probes a one-body method's signature.
	function ensureMethod(owner: ClassInfo, name: string, call: CallSite, callerCtx: FunctionContext): FuncInfo | undefined {
		const decls		= owner.methodDecls.get(name);
		const fullName	= `${owner.name}.${name}`;
		// Not overridden by `owner` itself: delegate straight to the ancestor's own compiled function (cached under *its* key, e.g. `A.greet`, not `owner.name`'s) rather
		// than recompiling a duplicate. Sound and free: wasm-GC struct subtyping (`ensureClass`'s own `supertypes`) makes a `(ref Derived)` value directly callable
		// wherever `(ref A)` is declared, no cast needed -- this is why a non-overridden inherited method stays a single, plain `call`.
		if (!decls)
			return owner.superClass && ensureMethod(owner.superClass, name, call, callerCtx);
		let decl = implementationOf(owner, name, decls, call, callerCtx);
		// Qualified so it can share `funcs` with plain top-level functions (bare identifiers can't contain
		// '.') without colliding; only suffixed when there's a real overload set to disambiguate.
		let key = decls.length > 1 ? `${fullName}#${decls.indexOf(decl)}` : fullName;

		// A generic method's own type params (beyond `owner`'s already-resolved class-level ones, e.g. `class Box<T> { map<U>(f: (t: T) => U): Box<U> {...} }`): the same
		// composite-key/substitution shape `ensureGenericFunc` uses for a top-level generic function. `decl` is `owner.methodDecls`' copy, with the class's `T` already
		// substituted (from `ensureClass`), so only `U` remains; a `MethodMember` isn't a `walk` root node, so signature pieces go through `T.substituteType` individually
		// (as checker.ts's `instantiate` does) and the body through `substituteTypeParams` (a plain `Statement[]`, which `walk` does accept directly).
		if (decl.typeParams?.length) {
			const map = callTypeArgs(decl, resolvedCall(owner, name, call, callerCtx), callerCtx, !!typeArgsOf(call), Array.isArray(call) ? call : call.arguments, callerCtx.callContext);
			key		= genericKey(key, decl.typeParams, map, global);
			decl	= {
				...decl,
				typeParams: undefined,
				params:		decl.params.map(p => p.typeAnnotation ? { ...p, typeAnnotation: T.substituteType(p.typeAnnotation, map) } : p),
				rest:		decl.rest?.typeAnnotation ? { ...decl.rest, typeAnnotation: T.substituteType(decl.rest.typeAnnotation, map) } : decl.rest,
				returnType: decl.returnType ? T.substituteType(decl.returnType, map) : decl.returnType,
				body:		decl.body ? substituteTypeParams(map).statements(decl.body) : decl.body,
			};
		}

		const existing = funcs.get(key);
		if (existing)
			return existing;

		// A `this`-typed return/param (`sort(): this`) means "whatever `owner`'s own concrete type is": the checker resolves it lazily (see `T.substituteThisType`),
		// but codegen needs a real `WasmType` up front, so it is substituted in here before `typeOf` sees it; a no-op when neither mentions `this`.
		decl = {
			...decl,
			returnType: decl.returnType && T.substituteThisType(decl.returnType, owner.thisTsType),
			params:		decl.params.map(p => p.typeAnnotation ? { ...p, typeAnnotation: T.substituteThisType(p.typeAnnotation, owner.thisTsType) } : p),
		};
		if (!decl.body)
			throw `'${fullName}' needs a body (overload signatures are not supported)`;

		const result = decl.returnType ? typeOf(decl.returnType) : 'void';
		if (!result)
			throw `'${fullName}' has an unsupported return type`;

		const params		= resolveParams(decl.params, owner.declScope ?? libGlobal);
		if (decl.rest?.typeAnnotation)
			params.push({key: decl.rest.key, wtype: restParamWtype(decl.rest.typeAnnotation)!, tsType: decl.rest.typeAnnotation});

		const isStatic		= decl.modifiers?.includes('static');
		const reassignsThis = !isStatic && assignsToThis(decl.body);
		const thisWtype		= owner.thisType;
		const {funcIndex, typeIndex} = types.func(
			isStatic		? toParams2(params) : [{ type: toValType(thisWtype), id: 'this' }, ...toParams2(params)],
			reassignsThis	? [...toResults(result), toValType(thisWtype)] : toResults(result)
		);

		const info: FuncInfo = { params: params.map(r => r.wtype), result, funcIndex, typeIndex, defaults: defaultsWithImplicitUndefined(decl.params), resolvedParams: params, hasRest: !!decl.rest?.typeAnnotation, reassignsThis };
		funcs.set(key, info);
		worklist.push(W.withCatch(() => {
			// See `ensureCtor`'s own note -- a method body resolves against its class's declaring module too.
			const ctx	= new FunctionContext(key, new Scope(moduleScopeOf(owner.homeModule) ?? owner.declScope ?? libGlobal), plainReturn(result, decl.returnType as Type | undefined), owner, owner.homeModule);
			if (!isStatic)
				ctx.declareValue('this', thisWtype, owner.thisTsType);
			if (reassignsThis) {
				// A `reassignsThis` method's own (possibly just-updated) `this` rides along as one more wasm-level result on every return, on top of its
				// ordinary declared result -- see `assignsToThis`'s own comment for why a body doing this is this compiler's signal to compile it this way.
				ctx.onReturn = {
					wtype: () => result === 'void' ? undefined : result,
					emit(ctx, argument) {
						if (result === 'void') {
							if (argument)
								throw "a 'void' function cannot return a value";
						} else if (argument) {
							emitAs(argument, ctx, result);
						}
						ctx.emit(I.local.get(ctx.lookup('this')!.index), I.return);
					},
				};
			}
			ctx.ownBody = decl.body!;
			ctx.declareParams(params).forEach(st => emitStmt(st, ctx));
			hoistVars(decl.body!, params, ctx);
			emitStmts(decl.body!, ctx);
			ctx.emitTrailingUnreachable(result);
			info.body = ctx.toFuncBody((isStatic ? 0 : 1) + params.length, toValType);
		}, key));
		return info;
	}

	// A runtime helper, built once per `key`: reserved at first use so call sites can `call` it, its body built LATE (once every class the program
	// reaches is known) when its candidates are open-ended, or on the ordinary worklist when they are a bounded set.
	function synthesize<P extends { params: { key: string; wtype: W.Type; tsType: Type }[]; result: W.Type; info?: Partial<FuncInfo> }>(
		key: string, prepare: () => P, build: (ctx: FunctionContext, locals: number[], p: P) => void, late = true): FuncInfo {
		const existing = funcs.get(key);
		if (existing)
			return existing;
		const p = prepare();
		const { funcIndex, typeIndex } = types.func(toParams2(p.params), toResults(p.result));
		const info: FuncInfo = { params: p.params.map(q => q.wtype), result: p.result, funcIndex, typeIndex, ...p.info };
		funcs.set(key, info);
		(late ? lateWorklist : worklist).push(W.withCatch(() => {
			const ctx = new FunctionContext(key, new Scope(libGlobal), plainReturn(p.result), undefined);
			build(ctx, p.params.map(q => ctx.declareValue(`$${q.key}`, q.wtype, q.tsType).index), p);
			info.body = ctx.toFuncBody(p.params.length, toValType);
		}, key));
		return info;
	}
	const anyParam = (key: string, wtype: W.Type = W.REF_ANY) => ({ key, wtype, tsType: T.ANY });

	// A `ref.test` chain: the first arm whose heap type `recv` passes runs with `recv` cast to it on the stack; a value passing none runs `otherwise`.
	function emitTypeCascade(ctx: FunctionContext, recv: number, arms: { heap: wasm.HeapType; emit: () => void }[], otherwise: () => void, result?: W.Type): void {
		const blockType	= result && result !== 'void' ? toValType(result) : undefined;
		const chain		= (i: number): wasm.Instr[] => {
			if (i >= arms.length) {
				otherwise();
				return ctx.swapOut();
			}
			ctx.emit(I.local.get(recv), I.ref.cast(arms[i].heap));
			arms[i].emit();
			return [I.local.get(recv), I.ref.test(arms[i].heap), I.if(blockType, ctx.swapOut(), chain(i + 1))];
		};
		const before = ctx.swapOut();
		const instrs = chain(0);
		ctx.swapOut(before);
		ctx.emit(...instrs);
	}
	const trap = (ctx: FunctionContext) => () => ctx.emit(I.unreachable);

	// Whether `recv` passes any of `heaps`' `ref.test`s; none at all is `false`.
	function emitTestsAny(ctx: FunctionContext, recv: number, heaps: wasm.HeapType[]): void {
		if (!heaps.length)
			ctx.emit(I.i32.const(0));
		heaps.forEach((heap, i) => ctx.emit(I.local.get(recv), I.ref.test(heap), ...(i ? [I.i32.or] : [])));
	}

	// Every representation a value in an `any` slot can have, with the class owning its members: bare array storage (gated on its wasm type existing,
	// else no such value can), every class reached, and -- when asked -- the primitives. Several owners share a heap type, so a use filters, then dedupes.
	type Receiver = { heap: wasm.HeapType; cls: ClassInfo; boxed?: true };
	function dynamicReceivers(primitives: boolean): Receiver[] {
		const out: Receiver[] = [];
		const add = (cls: ClassInfo | undefined, heap: wasm.HeapType | undefined, boxed?: true) => {
			if (cls && heap !== undefined)
				out.push({ heap, cls, boxed });
		};
		if (primitives) {
			add(builtinTypeOwner('string'), types.array('i16'));
			add(builtinTypeOwner('bigint'), types.array('i32'));
			add(builtinTypeOwner('number'), types.box('f64'), true);
			add(builtinTypeOwner('boolean'), types.box('i32'), true);
		}
		for (const [kind, elem] of [['f64', T.NUMBER], ['ref', T.ANY]] as const) {
			if (types.hasArray(kind))
				add(ensureClass('RawArray', [elem]), types.array(kind));
		}
		// `-1` is `ensureClass`'s no-struct sentinel: an array-backed class still has its storage's heap type to test, a scalar-backed one none.
		// A dynamic object's keys are its entries, never its struct's fields or its class's methods: `dynamicObjectArms` answers for it.
		for (const cls of classes.values())
			if (!isDynamicObject(cls))
				add(cls, cls.typeIndex !== -1 ? cls.typeIndex : W.isArr(cls.thisWtype) || W.isIndexed(cls.thisWtype) ? heapTypeIndexOf(cls.thisWtype) : undefined);
		return out;
	}

	// Each reached `DynamicObject<V>` as a cascade arm: `use` gets a local holding it, to read or write its entries.
	function dynamicObjectArms(dctx: FunctionContext, use: (obj: Expr) => void) {
		return [...new Set(classes.values())].filter(cls => isDynamicObject(cls) && cls.typeIndex !== -1).map(cls => ({ heap: cls.typeIndex, emit: () => {
			const name = `$dynobj$${cls.typeIndex}`;
			dctx.emit(I.local.set(dctx.declareValue(name, cls.thisWtype!, cls.thisTsType).index));
			use(Identifier(name));
		} }));
	}
	const callOn = (obj: Expr, method: string, args: Expr[]): Expr => JS.Call(JS.Member(obj, method), args);
	const distinctHeaps = <R extends { heap: wasm.HeapType }>(rs: R[]) => rs.filter((r, i) => rs.findIndex(s => s.heap === r.heap) === i);
	const depthOf = (c: ClassInfo): number => c.superClass ? 1 + depthOf(c.superClass) : 0;
	const inherits = (c: ClassInfo, ancestor: ClassInfo): boolean => !!c.superClass && (c.superClass === ancestor || inherits(c.superClass, ancestor));

	// The owners of a real, non-`this`-reassigning `name` fitting `argTs` -- what a dynamic (`any`) call of `name` tests. `!assignsToThis` excludes a method
	// with no boxed-`any` write-back target (`Array<T>.push`).
	function findAnyDispatchCandidates(name: string, argTs: Type[], ctx: FunctionContext) {
		return distinctHeaps(dynamicReceivers(true).filter(r => r.cls.methodDecls.get(name)?.some(d => d.body && !d.rest && !assignsToThis(d.body) && T.argsFit(T.FixSig(d, T.ANY), argTs, ctx.scope))))
			.flatMap(r => {
				const funcInfo = ensureMethod(r.cls, name, [], ctx);
				return funcInfo ? [{ ...r, funcInfo }] : [];
			});
	}

	// `x[k]` where `x` is `any` and `k` a computed string: each class with fields chains its own names, as a known receiver's `x[k]` compiles.
	// A key no candidate declares reads `undefined`, as JS does; a write traps, since there is no honest place to put it.
	// A struct cannot lose a slot, so `delete` stores `undefined` in a field, as a typed `delete` does; a dynamic object drops its entry.
	function ensureAnyKey(kind: 'get' | 'set' | 'delete'): FuncInfo {
		return synthesize(`<any key ${kind}>`, () => ({
			params: [anyParam('recv'), { key: 'key', wtype: typeOf(T.STRING)!, tsType: T.STRING }, ...(kind === 'set' ? [anyParam('value', W.REF_ANY_NULLABLE)] : [])],
			result: kind === 'get' ? W.REF_ANY_NULLABLE : kind === 'delete' ? 'i32' : 'void' as W.Type,
		}), (dctx, [recv], { result }) => {
			const keyId: Expr	= Identifier('$key');
			const isKey			= (f: string): Expr => Binary<Expr, '==='>('===', keyId, Literal(f));
			const written: Expr	= Identifier(kind === 'set' ? '$value' : 'undefined');
			const deleted		= () => {
				if (kind === 'delete')
					dctx.emit(I.i32.const(1));
			};
			const owners		= distinctHeaps(dynamicReceivers(false).filter(r => r.cls.typeIndex !== -1 && r.cls.fields.length && r.cls.thisTsType));
			const dynamic		= dynamicObjectArms(dctx, obj => {
				if (kind === 'get')
					emitAs(callOn(obj, 'get', [keyId]), dctx, W.REF_ANY_NULLABLE);
				else
					emitStmt(JS.ExprStmt(kind === 'set' ? callOn(obj, 'set', [keyId, written]) : callOn(obj, 'delete', [keyId])), dctx);
				deleted();
			});
			emitTypeCascade(dctx, recv, [...dynamic, ...owners.map(({ heap, cls }) => ({ heap, emit: () => {
				const objName		= `$keyobj$${heap}`;
				const objId: Expr	= Identifier(objName);
				dctx.emit(I.local.set(dctx.declareValue(objName, cls.thisWtype!, cls.thisTsType!).index));
				if (kind === 'get')
					emitAs(cls.fields.reduce<Expr>((alternate, f) => Conditional<Expr>(isKey(f.name), JS.Member(objId, f.name), alternate), Identifier('undefined')), dctx, W.REF_ANY_NULLABLE);
				else
					cls.fields.forEach(f => {
						// A field that cannot hold `undefined` cannot be deleted: trap, as the typed `delete`'s non-null cast does.
						if (kind === 'delete' && !W.isNullable(f.wtype) && !W.isAny(f.wtype)) {
							emitAs(isKey(f.name), dctx, 'i32');
							dctx.emit(I.if(undefined, [I.unreachable]));
						} else {
							emitStmt({ type: 'if', test: isKey(f.name), consequent: JS.ExprStmt(Assign<Expr, never>(JS.Member(objId, f.name), written)) } as Stmt, dctx);
						}
					});
				deleted();
			} }))], kind === 'set' ? trap(dctx) : kind === 'delete' ? deleted : () => dctx.emitDefaultValue(W.REF_ANY_NULLABLE, types, toValType), result);
		});
	}

	// A number key on an erased receiver: an element holder reads or writes its own element (a read past the end is `undefined`);
	// any other key is the string key JS makes of it.
	function ensureAnyIndex(kind: 'get' | 'set'): FuncInfo {
		return synthesize(`<any index ${kind}>`, () => ({
			params: [anyParam('recv'), { key: 'idx', wtype: 'f64' as W.Type, tsType: T.NUMBER }, ...(kind === 'set' ? [anyParam('value', W.REF_ANY_NULLABLE)] : [])],
			result: kind === 'get' ? W.REF_ANY_NULLABLE : 'void' as W.Type,
		}), (dctx, [recv], { result }) => {
			const idxId: Expr	= Identifier('$idx');
			const all			= (tests: Expr[]) => tests.reduce((a, b) => Binary<Expr, '&&'>('&&', a, b));
			const integral		= [Binary<Expr, '>='>('>=', idxId, Literal(0)), Binary<Expr, '==='>('===', Binary<Expr, '%'>('%', idxId, Literal(1)), Literal(0))];
			const asKey: Expr	= JS.Index(Identifier('$recv'), JS.Call(Identifier('String'), [idxId]));
			const elementOf = (heap: wasm.HeapType, wtype: W.Type, tsType: Type) => ({ heap, emit: () => {
				const name = `$indexed$${heap}`;
				dctx.emit(I.local.set(dctx.declareValue(name, wtype, tsType).index));
				const element: Expr = JS.Index(Identifier(name), idxId);
				if (kind === 'get')
					emitAs(Conditional<Expr>(all([...integral, Binary<Expr, '<'>('<', idxId, JS.Member(Identifier(name), 'length'))]), element, Identifier('undefined')), dctx, result);
				else
					emitStmt({ type: 'if', test: all(integral), consequent: JS.ExprStmt(Assign<Expr, never>(element, Identifier('$value'))), alternate: JS.ExprStmt(Assign<Expr, never>(asKey, Identifier('$value'))) } as Stmt, dctx);
			} });
			// A string's storage is also the heap type of a class that owns its methods; the string arm reads it, and a string has nothing to write.
			const strings	= types.array('i16');
			const accessor	= kind === 'get' ? '__get' : '__set';
			const indexable	= distinctHeaps(dynamicReceivers(false).filter(r => r.heap !== strings && (r.cls.methodDecls.has(accessor) || !!r.cls.inlineMethods?.has(accessor))
				&& !!T.lookupMember(r.cls.thisTsType, 'length', libGlobal)));
			const arms		= indexable.map(r => elementOf(r.heap, r.cls.thisWtype!, r.cls.thisTsType));
			emitTypeCascade(dctx, recv, kind === 'get' ? [elementOf(strings, typeOf(T.STRING)!, T.STRING), ...arms] : arms,
				() => kind === 'get' ? emitAs(asKey, dctx, result) : emitStmt(JS.ExprStmt(Assign<Expr, never>(asKey, Identifier('$value'))), dctx), result);
		});
	}

	// `x.name` where `x` is genuinely `any`: a `ref.test` over every representation that declares `name`. Always `REF_ANY`, since the candidates' own
	// types differ; a receiver declaring nothing is an object lacking it and reads `undefined`, while a NULL receiver, which JS throws on, traps.
	function ensureAnyField(name: string): FuncInfo {
		return synthesize(`<any field>.${name}`, () => ({ params: [anyParam('recv')], result: W.REF_ANY_NULLABLE }), (dctx, [recv], { result }) => {
			// Boxed by the member's DECLARED type: `String.length` is an `array.len` and a literal's `{length: n}` may be an `i32`, but anything entering
			// an `any` slot must be its logical type's canonical form, or the reader's `f64`-box cast traps. `T.lookupMember`: an `__asm` accessor has no decl.
			const canonicalOf = (cls: ClassInfo, physical: W.Type): W.Type => {
				const declared	= cls.thisTsType && T.lookupMember(cls.thisTsType, name, dctx.scope);
				const canonical	= declared && typeof physical === 'string' && T.isNumberLike(declared, dctx.scope) ? 'f64' : (declared && typeOf(declared)) || physical;
				return canonical === 'void' ? physical : canonical;
			};
			const boxed = (physical: W.Type, want: W.Type) => {
				coerceTop(physical, dctx, want);
				coerceTop(want, dctx, result);
			};
			const readOf = ({ heap, cls }: Receiver) => {
				const idx = cls.fieldIndex.get(name);
				if (idx !== undefined && cls.typeIndex !== -1) {
					const physical = cls.fields[idx].wtype;
					return [{ heap, emit: () => {
						emitFieldRead(cls, idx, dctx);
						boxed(physical, typeof physical === 'string' ? canonicalOf(cls, physical) : physical);
					} }];
				}
				const sig = cls.getterNames?.has(name) ? methodSig(cls, accessorKey('get', name), dctx) : undefined;
				return sig ? [{ heap, emit: () => {
					emitMethodCall(cls, accessorKey('get', name), [], dctx);
					boxed(sig.result, canonicalOf(cls, sig.result));
				} }] : [];
			};
			const arms = [...dynamicObjectArms(dctx, obj => emitAs(callOn(obj, 'get', [Literal(name)]), dctx, result)), ...distinctHeaps(dynamicReceivers(true).flatMap(readOf))];
			// Gated like the arrays: with no closure type, no function value can be in an `any` slot.
			const closureField = CLOSURE_FIELDS.get(name);
			if (closureField !== undefined && closureTypes.size) {
				const base = types.closureBase();
				arms.push({ heap: base, emit: () => {
					dctx.emit(I.struct.get(base, closureField));
					boxed('u32', 'f64');
				} });
			}
			emitTypeCascade(dctx, recv, arms, () => dctx.emit(I.local.get(recv), I.ref.is_null,
				I.if(toValType(result), [I.unreachable], [I.ref.null(heapTypeIndexOf(result))])), result);
		});
	}

	// `x.name = v` where `x` is a union or `any`: the write side of `ensureAnyField`, over the struct-backed owners only (a field write needs a real
	// `struct.set`). The value arrives boxed, as every expando field holds it. A receiver matching nothing traps: dropping a write silently is worse.
	function ensureAnyFieldWrite(name: string): FuncInfo {
		return synthesize(`<any field write>.${name}`, () => ({ params: [anyParam('recv'), anyParam('value', W.REF_ANY_NULLABLE)], result: 'void' as W.Type }), (dctx, [recv, value]) => {
			const owners	= distinctHeaps(dynamicReceivers(false).filter(r => r.cls.typeIndex !== -1 && r.cls.fieldIndex.has(name)));
			const dynamic	= dynamicObjectArms(dctx, obj => emitStmt(JS.ExprStmt(callOn(obj, 'set', [Literal(name), Identifier('$value')])), dctx));
			if (!owners.length && !dynamic.length)
				throw `no reachable class declares a field '${name}' -- a dynamic write on 'any' needs at least one real candidate`;
			emitTypeCascade(dctx, recv, [...dynamic, ...owners.map(({ heap, cls }) => ({ heap, emit: () => {
				// Through the owner's own receiver type, so a key with a setter (`emitFieldWrite`) calls it here too.
				dctx.emit(I.local.get(value));
				emitFieldWrite(cls, cls.fieldIndex.get(name)!, W.REF_ANY_NULLABLE, dctx);
			} }))], trap(dctx));
		});
	}

	// `instanceof` a generic class: a `ref.test` over every instantiation of it reached.
	function ensureInstanceTest(cls: ClassInfo): FuncInfo {
		return synthesize(`<instanceof>.${homeKey(cls.homeModule ?? '.', cls.decl.name!)}`, () => ({ params: [anyParam('recv', W.REF_ANY_NULLABLE)], result: 'i32' as W.Type }), (dctx, [recv]) =>
			emitTestsAny(dctx, recv, [...classes.values()].filter(c => c.typeIndex !== -1 && c.decl.name === cls.decl.name && c.homeModule === cls.homeModule).map(c => c.typeIndex)));
	}

	// `k in x` on an erased receiver: with no runtime property metadata, "has `k`" is "is an object representation declaring `k`" -- a field, getter
	// or method, as JS finds prototype members too. A key known only at run time is compared with each representation's names; a primitive or null answers `false`.
	function ensureAnyIn(name?: string): FuncInfo {
		const names = (cls: ClassInfo) => [...cls.fieldIndex.keys(), ...cls.getterNames ?? [], ...cls.methodDecls.keys()].filter(n => !n.startsWith('#'));
		const has = (dctx: FunctionContext, key: Expr) => dynamicObjectArms(dctx, obj => emitAs(callOn(obj, 'has', [key]), dctx, 'i32'));
		if (name !== undefined)
			return synthesize(`<any in>.${name}`, () => ({ params: [anyParam('recv', W.REF_ANY_NULLABLE)], result: 'i32' as W.Type }), (dctx, [recv], { result }) =>
				emitTypeCascade(dctx, recv, [...has(dctx, Literal(name)), ...distinctHeaps(dynamicReceivers(false).filter(({ cls }) => names(cls).includes(name)))
					.map(({ heap }) => ({ heap, emit: () => dctx.emit(I.drop, I.i32.const(1)) }))], () => dctx.emit(I.i32.const(0)), result));
		return synthesize('<any in>', () => ({ params: [{ key: 'key', wtype: typeOf(T.STRING)!, tsType: T.STRING }, anyParam('recv', W.REF_ANY_NULLABLE)], result: 'i32' as W.Type }), (dctx, [, recv], { result }) => {
			const keyId: Expr = Identifier('$key');
			const owners = distinctHeaps(dynamicReceivers(false).filter(({ cls }) => names(cls).length));
			const declares = (cls: ClassInfo) => names(cls).map((n): Expr => Binary<Expr, '==='>('===', keyId, Literal(n))).reduce((a, b) => Binary<Expr, '||'>('||', a, b));
			emitTypeCascade(dctx, recv, [...has(dctx, keyId), ...owners.map(({ heap, cls }) => ({ heap, emit: () => { dctx.emit(I.drop); emitAs(declares(cls), dctx, 'i32'); } }))],
				() => dctx.emit(I.i32.const(0)), result);
		});
	}

	// `Object.keys/values/entries(x)` where what fields exist is the receiver's RUNTIME type's (no field list, or a class extended somewhere). Deepest
	// first, as a subclass passes its base's `ref.test` too. Only struct-backed classes have fields to list; `Map`'s `K[]`/`V[]` has no `any[]` form.
	function ensureAnyEntries(which: 'entries' | 'keys' | 'values'): FuncInfo {
		return synthesize(`<any ${which}>`, () => ({ params: [anyParam('recv')], result: W.ARRAY.ref }), (dctx, [recv], { result }) => {
			const owners = distinctHeaps(dynamicReceivers(false).filter(({ cls }) => cls.typeIndex !== -1 && cls.decl.name !== 'Map' && W.isRef(cls.thisWtype))
				.sort((a, b) => depthOf(b.cls) - depthOf(a.cls)));
			emitTypeCascade(dctx, recv, [...dynamicObjectArms(dctx, obj => emitAs(callOn(obj, 'anyEntries', [Literal(which)]), dctx, result)),
				...owners.map(({ heap, cls }) => ({ heap, emit: () => void emitEntriesOf(cls, which, dctx) }))], trap(dctx), result);
		});
	}

	// JS `===` when either side is a boxed `any`: a string or boxed primitive compares by VALUE, anything else by identity. Only kinds whose wasm type
	// exists are tested -- a value of an absent kind can't be in the slot.
	function ensureAnyStrictEq(): FuncInfo {
		return synthesize('<any ===>', () => ({ params: [anyParam('a', W.REF_ANY_NULLABLE), anyParam('b', W.REF_ANY_NULLABLE)], result: 'i32' as W.Type }), (dctx, [a, b]) => {
			const arms: { heap: number; compare: wasm.Instr[] }[] = [];
			if (types.hasArray('i16')) {
				const heap = types.array('i16');
				arms.push({ heap, compare: [I.local.get(a), I.ref.cast(heap), I.local.get(b), I.ref.cast(heap), I.call(ensureMethod(builtinTypeOwner('string')!, 'eq', [], dctx)!.funcIndex)] });
			}
			for (const [kind, eq] of [['f64', I.f64.eq], ['i32', I.i32.eq], ['i64', I.i64.eq]] as const) {
				if (types.hasBox(kind)) {
					const heap = types.box(kind);
					const read = (l: number) => [I.local.get(l), I.ref.cast(heap), I.struct.get(heap, 0)];
					arms.push({ heap, compare: [...read(a), ...read(b), eq] });
				}
			}
			dctx.emit(...arms.reduceRight<wasm.Instr[]>((rest, arm) => [I.local.get(a), I.ref.test(arm.heap), I.local.get(b), I.ref.test(arm.heap), I.i32.and, I.if('i32', arm.compare, rest)],
				[I.local.get(a), I.ref.cast('eq', true), I.local.get(b), I.ref.cast('eq', true), I.ref.eq]));
		});
	}

	// Whether a `got` value converts to `want` physically. `any` on either side boxes or casts; two structs only upcast; closures by the wrapper's own rule.
	function fits(got: W.Type, want: W.Type): boolean {
		const kind			= (w: W.Type) => typeof w === 'string' ? 'scalar' : 'closure' in w ? 'closure' : 'arr' in w ? `arr:${w.arr}` : 'ref';
		const closureFits	= (g: FuncSig, p: FuncSig): boolean => g.params.length <= p.params.length && !!g.hasRest === !!p.hasRest && g.params.every((x, i) => fits(p.params[i], x));
		return got !== 'void' && want !== 'void' && (W.typeEq(got, want) || W.isAny(got) || W.isAny(want)
			|| (kind(got) === kind(want) && (kind(got) === 'scalar' || kind(got).startsWith('arr')
				|| (W.isClosure(got) && W.isClosure(want) && closureFits(got.closure, want.closure))
				|| (W.isRef(got) && W.isRef(want) && isSubclassOf(got.ref, want.ref)))));
	}

	// A call through an `any` callee (core.ts `params[0](...)`): tested against every closure type the program has, each argument converted to that type's
	// parameter (one the call leaves out takes `undefined`) and the result to what the call wants. Only candidates the arguments and result fit.
	// An argument the call leaves out takes its default, else `undefined`; a `void` call discards the callee's result, as JS does.
	function dispatchArm(dctx: FunctionContext, args: number[], argWtypes: W.Type[], params: W.Type[], defaults: (Expr | undefined)[] | undefined, want: W.Type, call: (pushArgs: () => void) => W.Type, name?: string) {
		const result = call(() => params.forEach((p, j) => {
			if (j < args.length) {
				dctx.emit(I.local.get(args[j]));
				coerceTop(argWtypes[j], dctx, p);
			} else if (!defaults) {
				emitAs(Identifier('undefined'), dctx, p);
			} else if (defaults[j]) {
				emitAs(defaults[j]!, dctx, p);
			} else {
				throw `'${name}' needs more than ${args.length} argument(s)`;
			}
		}));
		if (want === 'void' && result !== 'void')
			dctx.emit(I.drop);
		else
			coerceTop(result, dctx, want);
	}

	function ensureAnyCallDispatch(argWtypes: W.Type[], want: W.Type): FuncInfo {
		return synthesize(`<any dispatch>.#call(${argWtypes.map(W.typeKey).join(',')})=>${W.typeKey(want)}`, () => ({
			params: [anyParam('callee'), ...argWtypes.map((wtype, i) => anyParam(`arg${i}`, wtype))], result: want,
		}), (dctx, [callee, ...args]) => {
			const candidates = [...closureTypes.values()].filter(c => !c.sig.hasRest && c.sig.params.length >= argWtypes.length
				&& argWtypes.every((w, i) => fits(w, c.sig.params[i])) && (want === 'void' || fits(c.sig.result, want))
				&& c.sig.params.slice(argWtypes.length).every(p => W.isNullable(p) || W.isAny(p)));
			if (!candidates.length)
				throw `no closure type in the program takes ${argWtypes.length} such argument(s) -- a call through 'any' needs at least one real candidate`;
			emitTypeCascade(dctx, callee, candidates.map(c => ({ heap: c.structTypeIndex, emit: () =>
				dispatchArm(dctx, args, argWtypes, c.sig.params, undefined, want, push => emitClosureCall({ closure: c.sig, nullable: false }, push, dctx)),
			})), trap(dctx), want);
		});
	}

	// A method call on an `any`/`unknown` receiver: tested against every reachable owner of `name` (strings and arrays too), each argument converted from
	// its static representation to that owner's parameter, and the result to what the call wants.
	function ensureAnyDispatch(name: string, argWtypes: W.Type[], argTs: Type[], want: W.Type, ctx: FunctionContext): FuncInfo {
		return synthesize(`<any dispatch>.${name}(${argWtypes.map(W.typeKey).join(',')})=>${W.typeKey(want)}`, () => ({
			params: [anyParam('recv'), ...argWtypes.map((wtype, i) => ({ key: `arg${i}`, wtype, tsType: argTs[i] }))], result: want,
		}), (dctx, [recv, ...args]) => {
			// A candidate whose result cannot become what the call wants is never the one a correct program calls.
			const methods = findAnyDispatchCandidates(name, argTs, ctx).filter(c => want === 'void' || fits(c.funcInfo.result, want));
			// A method written in an object literal (or a class's arrow field) is a closure held in a field of that name.
			const held = [...classes.values()].flatMap(cls => {
				const idx	= cls.fieldIndex.get(name);
				const wt	= idx === undefined || cls.typeIndex === -1 || methods.some(m => m.heap === cls.typeIndex) ? undefined : closurePart(cls.fields[idx].wtype);
				if (!wt)
					return [];
				const sig	= closureSigOf(wt);
				return (sig.hasRest || sig.params.length >= argTs.length) && (want === 'void' || fits(sig.result, want)) ? [{ cls, idx: idx!, wt, sig }] : [];
			});
			if (!methods.length && !held.length)
				throw `no reachable class (or 'number'/'boolean'/'string'/array) declares a '${name}' callable with ${argTs.length} such argument(s) -- a dynamic dispatch on 'any' needs at least one real candidate`;
			emitTypeCascade(dctx, recv, [
				...methods.map(c => ({ heap: c.heap, emit: () => {
					if (c.boxed)
						dctx.emit(I.struct.get(c.heap as number, 0));
					dispatchArm(dctx, args, argWtypes, c.funcInfo.params, c.funcInfo.defaults ?? [], want, push => (push(), dctx.emit(I.call(c.funcInfo.funcIndex)), c.funcInfo.result), name);
				} })),
				...held.map(({ cls, idx, wt, sig }) => ({ heap: cls.typeIndex, emit: () => {
					const callable: W.ClosureType = { ...wt, nullable: false };
					dctx.emit(I.struct.get(cls.typeIndex, idx));
					coerceTop(wt, dctx, callable);
					dispatchArm(dctx, args, argWtypes, sig.params, undefined, want, push => emitClosureCall(callable, push, dctx));
				} })),
			], trap(dctx), want);
		});
	}

	// A union member typed as a plain array has TWO physical forms: its element kind's `Array<T>` when it came from a precisely-typed slot, or `Array<any>`
	// when built as a literal in a boxed-`any` position (`case 'array'`'s rule; dwg's `updateBuffer([1,2,3])` into `Uint8Array | number[]`). Both are members.
	function expandArrayMembers(members: readonly ClassInfo[]): ClassInfo[] {
		const all = members.flatMap(m => m.decl.name === 'Array' ? [m, ensureClass('Array', [T.ANY])] : [m]).filter(m => !!m);
		return all.filter((m, i) => all.findIndex(n => n.typeIndex === m.typeIndex) === i);
	}

	// `recv.name` where `recv` is a union of >=2 object shapes (boxed as `any`), over the union's own bounded members. A member declaring neither a field
	// nor a getter `name` is one the checker's narrowing excluded, so it is left out; a receiver matching no arm traps rather than read a missing field.
	function ensureUnionFieldDispatch(members: readonly ClassInfo[], name: string, resultTsType: Type | undefined): FuncInfo {
		members = expandArrayMembers(members);
		// Keyed by the result as well: it is the call site's type, so one narrowed to non-null must not serve a site where the field can be null.
		return synthesize(`<union field dispatch>.${name}:${resultTsType ? T.typeKey(resultTsType) : ''}=>[${members.map(m => m.typeIndex).join(',')}]`, () => {
			// A getter's result type must be known now, to decide this function's signature.
			const scratch		= new FunctionContext(name, new Scope(libGlobal), plainReturn(W.REF_ANY), undefined);
			const memberFields	= members.flatMap(m => {
				const idx = m.fieldIndex.get(name);
				if (idx !== undefined)
					return [{ cls: m, getter: false, fieldIdx: idx, wtype: m.fields[idx].wtype }];
				const sig = m.getterNames?.has(name) ? methodSig(m, accessorKey('get', name), scratch) : undefined;
				return sig ? [{ cls: m, getter: true, fieldIdx: -1, wtype: sig.result }] : [];
			});
			if (!memberFields.length)
				throw `internal: no member of the union type has a field '${name}'`;
			// The property's CHECKER type, not the members' physical ones, which differ where the TS types agree (`Uint8Array.length`'s `i32` field vs
			// `Array<T>.length`'s `u32` getter) and would box inconsistently. An optional field may be absent, so it widens as `addField` widens the field.
			const declared	= resultTsType && typeOf(resultTsType) || W.REF_ANY;
			const absent	= memberFields.some(f => !f.getter && f.cls.fields[f.fieldIdx].optional);
			return { params: [anyParam('recv')], result: absent && declared !== 'void' ? types.nullable(declared) : declared, memberFields };
		}, (dctx, [recv], { result, memberFields }) => emitTypeCascade(dctx, recv, memberFields.map(f => ({ heap: f.cls.typeIndex, emit: () => {
			if (f.getter)
				emitMethodCall(f.cls, accessorKey('get', name), [], dctx);
			else
				emitFieldRead(f.cls, f.fieldIdx, dctx);
			coerceUnionArm(f.wtype, dctx, result);
		} })), trap(dctx), result), false);
	}

	// `arr[i]` on a union of indexable classes (`Uint8Array | number[]`): each member's own `__get(i)`, the one convention every indexable class shares.
	// The result compares the members' `__get` results physically: the checker types a union receiver's indexed access as plain `any`.
	function ensureUnionIndexDispatch(members: readonly ClassInfo[]): FuncInfo {
		members = expandArrayMembers(members);
		return synthesize(`<union index dispatch>.[]=>[${members.map(m => m.typeIndex).join(',')}]`, () => {
			const scratch		= new FunctionContext('[]', new Scope(libGlobal), plainReturn(W.REF_ANY), undefined);
			const memberGets	= members.map(m => {
				const sig = methodSig(m, '__get', scratch);
				if (!sig)
					throw `internal: '${m.name}' (a member of a union type) has no '__get' method`;
				return { cls: m, wtype: sig.result };
			});
			return { params: [anyParam('recv'), { key: 'idx', wtype: 'i32' as W.Type, tsType: T.NUMBER }], result: W.combineUnion(memberGets.map(m => m.wtype)), memberGets };
		}, (dctx, [recv], { result, memberGets }) => emitTypeCascade(dctx, recv, memberGets.map(m => ({ heap: m.cls.typeIndex, emit: () => {
			emitMethodCall(m.cls, '__get', [Identifier('$idx')], dctx);
			coerceUnionArm(m.wtype, dctx, result);
		} })), trap(dctx), result), false);
	}

	// `recv.name(...args)` where a reachable subclass of `recv`'s static type overrides `name` (`emitMethodCall` routes here only when `hasDeclaredOverride` says
	// so). Overrides deepest-first, as a subclass instance passes every ancestor's `ref.test`; none matching is `owner`'s own resolution. Assumed, not
	// verified: every override shares `owner`'s param/result wasm types (TS keeps override signatures compatible).
	function ensureVirtualDispatch(owner: ClassInfo, name: string, ctx: FunctionContext): FuncInfo {
		return synthesize(`<virtual dispatch>.${owner.name}.${name}<virtual>`, () => {
			// `[]` is safe for a real-arg method: arguments only pick among several bodies, which virtual dispatch does not support.
			const base = ensureMethod(owner, name, [], ctx);
			if (!base)
				throw `internal: virtual dispatch requested for unknown method '${owner.name}.${name}'`;
			return {
				params: [anyParam('recv', owner.thisWtype!), ...base.params.map((wtype, i) => anyParam(`arg$${i}`, wtype))], result: base.result, base,
				info: { params: base.params, defaults: base.defaults, hasRest: base.hasRest },
			};
		}, (dctx, [recv, ...args], { base }) => {
			const call = (f: FuncInfo) => dctx.emit(...args.map(a => I.local.get(a)), I.call(f.funcIndex));
			const overrides = [...classes.values()].filter(c => c.typeIndex !== -1 && inherits(c, owner) && c.methodDecls.get(name)?.some(d => d.body))
				.sort((a, b) => depthOf(b) - depthOf(a));
			emitTypeCascade(dctx, recv, overrides.map(cls => ({ heap: cls.typeIndex, emit: () => {
				const f = ensureMethod(cls, name, [], ctx)!;
				call(f);
				coerceTop(f.result, dctx, base.result);
			} })), () => {
				dctx.emit(I.local.get(recv));
				call(base);
			}, base.result);
		});
	}


	// ===================================================================
	//  Program lowering
	// ===================================================================

	const mod		= new wasm.WasmModule();

	const promotedConsts = new Set<string>();

	// EXPANDO fields, decided whole-program and UP FRONT: a property write the checker accepted that the receiver's shape does not declare adds a field
	// to that shape, and a wasm struct type is built the first time anything mentions it -- nothing discovered while compiling a body applies
	// retroactively (a struct type is fixed, wasm-GC cannot change an allocated object's type, `ref.cast` only TESTS one). Keyed by SHAPE, not local,
	// which is what makes a write through a PARAMETER work: the object was allocated elsewhere and the declaration site never sees it. TS width
	// subtyping (`Meth` IS a `Sig`) has no wasm analogue -- a struct subtype's extra fields must FOLLOW the supertype's, which no single ordering gives
	// for unrelated shapes -- so a shape receiving a value of another type is stored as `any`, read through the same dispatch an `any` gets.


	// Functions are registered before the layout passes, which resolve a call to the declaration it compiles.
	for (const [moduleId, body] of moduleBodies) {
		for (let s of body.body) {
			if (s.type === 'export_decl')
				s = s.declaration;
			stmtHomeModule.set(s, moduleId);
			if (s.type === 'function_decl') {
				if (s.body)
					functionDeclByName.set(homeKey(moduleId, s.name), s);
				moduleFunctions.set(s, { name: s.name, home: moduleId });
			} else if (s.type === 'var_decl' && s.kind === 'const') {
				for (const d of s.declarations)
					if (typeof d.name === 'string' && d.init && !d.typeAnnotation && (d.init.type === 'arrow' || d.init.type === 'function')) {
						functionDeclByName.set(homeKey(moduleId, d.name), arrowOrFunctionToDecl(d.name, d.init));
						moduleFunctions.set(d.init, { name: d.name, home: moduleId });
					}
			}
		}
	}
	for (const [origin, { name, home }] of moduleFunctions)
		if (!functionDeclByName.has(homeKey(home, name)))
			moduleFunctions.delete(origin);

	// Both read the functions just registered: which parameters escape, and where an imported call lands.
	const { openShapes, openSlots, openReads: opened } = collectOpenShapes(stmtHomeModule, moduleBodies, functionDeclByName, namedImportsByModule);
	openReads = opened;
	// A slot holding more than one array storage (`collectOpenShapes`) is stored as `any`, and so is what is read from it.
	const openedAs = (d: Slot, t: Type) => openSlots.has(d) ? OPEN_SLOT : t;
	const { accessorKeys, pendingExtensions } = collectExpandoFields(stmtHomeModule, moduleBodies, namedImportsByModule);

	// Only *functions* are seeded across every module; a non-entry module's classes/scalar globals aren't yet
	// module-scoped (`ensureClass`/`ensureGlobal` -- see `TStoWasm`'s header), so class/scalar promotion below stays entry-only.
	for (const [moduleId, body] of moduleBodies) {
		for (let s of body.body) {
			if (s.type === 'export_decl')
				s = s.declaration;
			if (s.type === 'enum_decl') {
				// Same numbering rule the checker's own `hoist` uses: an implicit member continues from
				// the previous explicit one, a string member has no successor to continue from.
				let next = 0;
				enumNames.add(homeKey(moduleId, s.name));
				for (const m of s.members) {
					const init = m.init;
					const value = !init ? next++
						: init.type === 'literal' && typeof init.value === 'number' ? (next = init.value + 1, init.value)
						: init.type === 'literal' && typeof init.value === 'string' ? init.value
						: undefined;
					if (value !== undefined)
						enumMembers.set(homeKey(moduleId, `${s.name}.${m.name}`), value);
				}
			} else if (moduleId === '.' && s.type === 'class_decl') {
				if (s.typeParams?.length) {
					userGenericClassDecls.set(s.name, s);
				} else {
					const info = new ClassInfo(s.name, -1, s, TS.RefType(s.name));
					classes.set(s.name, info);
					const entry = moduleScopeOf('.')?.type(s.name);
					if (entry)
						classEntries.set(info, entry);
				}
			} else if (s.type === 'var_decl' && !(s.kind === 'var' && (s.ambient || moduleId === '.'))) {
				for (const d of s.declarations) {
					if (typeof d.name !== 'string' || !d.init)
						continue;
					// Only `exportScope` stamps `Scope.addDecl` for a var_decl, and only for an EXPORTED one, so a
					// non-exported module-level `const` (js-parser.ts's `import_attributes`) resolved nowhere; keyed per module.
					topLevelVars.set(homeKey(moduleId, d.name), { stmt: s, d });
					if (s.kind === 'const' && !d.typeAnnotation && (d.init.type === 'arrow' || d.init.type === 'function')) {
						if (moduleId === '.')
							promotedConsts.add(d.name);
					} else if (moduleId === '.') {
						// `foldConstants` first: `-1`/`!true` parse as real `unary`/`binary` nodes, so a direct
						// `type === 'literal'` check missed every foldable initializer, leaving that global unregistered
						// (any function using it then threw "unresolved identifier"); `case 'switch'` folds the same way.
						const folded = foldConstants(d.init)!;
						// Only a literal a wasm global can actually be INITIALIZED from: a string literal has no
						// constant form (its physical value is an i16 array built at runtime), nor a bigint unless it
						// lands on a real `i64` slot; the rest fall through to `ensureLazyGlobal`.
						const eagerKind = folded.type === 'literal' && W.notUnsigned(W.scalarKind(typeOf(d.typeAnnotation ?? checkerTypeOf(d.init, libGlobal))));
						if (eagerKind && (typeof folded.value === 'number' || typeof folded.value === 'boolean' || (typeof folded.value === 'bigint' && eagerKind === 'i64'))) {
							// Registered eagerly (unlike `lib/console.ts`'s `heap`, which registers lazily on first
							// reference): once it's a global, its position in `ast.body` stops mattering. `mut: false` for
							// `const` -- a genuine wasm-level compile-time constant, not just an unchecked mutable slot.
							const wtype = typeOf(d.typeAnnotation ?? checkerTypeOf(d.init, libGlobal));
							if (wtype && wtype !== 'void') {
								ensureGlobal(d.name, wtype, folded, s.kind !== 'const');
								promotedConsts.add(d.name);
							}
						}
					}
				}
			}
		}
	}

	// wasm puts every import at the lowest, contiguous function indices, before any local function claims one,
	// so "is this host import needed" must be decided up front. Deliberately a name-matching over-approximation
	// -- an unused import is harmless, so this only needs to never *under*-approximate.
	const reached	= new Set<string>();
	const pending: string[] = [];

	const collectNames = walker(undefined, (e, process) => {
		if (e.type === 'identifier')
			pending.push(e.name);
		return process(e);
	});

	// `walk` already descends into every nested function/class body, so this covers everything reachable
	// syntactically; leaving it ungated by cross-module reachability is deliberate -- extra names in `reached` are harmless.
	for (const body of moduleBodies.values())
		collectNames.statements(body.body);

	while (pending.length) {
		const name = pending.shift()!;
		if (!reached.has(name)) {
			reached.add(name);
			const decl = functionDeclByName.get(name) ?? LIB_DECL_MAP.get(name);
			if (decl && (decl.type === 'function_decl' || decl.type === 'class_decl'))
				collectNames.statement(decl);
		}
	}

	// Every module's host imports, not just the static lib's; deduped by name, since the same host function
	// imported by two modules is still ONE wasm import.
	const hostImports = [...new Map(
		[...LIB_HOST_IMPORTS, ...[...moduleBodies.values()].flatMap(m => hostImportsIn(m.body))].map(hi => [hi.name, hi] as const)
	).values()];

	mod.imports = hostImports.filter(hi => reached.has(hi.name)).map(hi => {
		const params = hi.params.map(p => resolveParam({ key: '', typeAnnotation: p }).wtype);
		const result = hi.returnType ? typeOf(hi.returnType) ?? 'void' : 'void';
		const { funcIndex, typeIndex } = types.func(toParams(params), toResults(result));
		funcs.set(hi.name, { params, result, funcIndex, typeIndex });
		return { module: hi.source, name: hi.name, desc: { kind: 'func', typeIndex, id: undefined } };
	});

	for (const d of [
		...[...LIB_DECL_MAP.values()].filter(d => d.type === 'class_decl'),
		...userGenericClassDecls.values(),
		...[...classes.values()].map(c => c.decl),
	]) {
		const superRef = superClassRef(d.superClass);
		if (superRef) {
			everExtended.add(superRef.name.slice(superRef.name.lastIndexOf('.') + 1));
			// By identity, not name: `class Base extends W.Base` is not its own subclass.
			const superId	= classIdentity(stmtHomeModule, superRef, moduleScopeOf(stmtHomeModule.get(d)) ?? global);
			const list		= directSubclasses.get(superId);
			if (list)
				list.push(d);
			else
				directSubclasses.set(superId, [d]);
		}
	}
	// An `extends`ed interface's shape must stay non-final, so the extending shape can name it as its supertype.
	const markExtendedInterfaces = (body: readonly TS.Stmt[]): void => body.forEach(s => {
		if (s.type === 'interface_decl')
			s.extendsClause?.forEach(b => b.type === 'ref' && everExtended.add(b.name.slice(b.name.lastIndexOf('.') + 1)));
		else if (s.type === 'export_decl')
			markExtendedInterfaces([s.declaration as TS.Stmt]);
		else if (s.type === 'namespace_decl' || s.type === 'module_decl')
			markExtendedInterfaces(s.body as TS.Stmt[]);
	});
	// So must a named shape written as a part of an intersection (`{type: 'call'} & CallSig`): see `ensureIntersectionShape`.
	const markIntersected = walkerB(undefined, undefined, (t, process) => {
		if (t.type === 'intersection')
			t.types.forEach(p => p.type === 'ref' && everExtended.add(p.name.slice(p.name.lastIndexOf('.') + 1)));
		return process(t);
	});
	for (const body of [LIB_AST, ...[...moduleBodies.values()].map(m => m.body)]) {
		markExtendedInterfaces(body);
		markIntersected.statements(body);
	}

	// The entry module's `var`s, at any block depth: globals from the start, as JS hoists them, each declaration assigning
	// one in `__toplevel`. Held nullable where their type is a reference, since nothing has assigned them yet.
	const moduleVars = [...collectHoistedLocals(ast.body, true)].filter(([, { stmt }]) => !(stmt.type === 'var_decl' && stmt.ambient));
	for (const [name, { decl }] of moduleVars) {
		const declared = decl.typeAnnotation ?? slotType(decl.flowType) ?? global.declared(name);
		const wtype = declared && typeOf(openedAs(decl, declared));
		if (!wtype || wtype === 'void')
			throw `module-level 'var ${name}' has an unsupported type`;
		ensureGlobal(name, typeof wtype === 'string' ? wtype : types.nullable(wtype), typeof wtype === 'string' ? Literal(wtype === 'i64' || wtype === 'u64' ? 0n : 0) : Identifier('undefined'), true);
	}

	//top level
	const {funcIndex, typeIndex} = types.func([], []);
	const info: FuncInfo = {params: [], result: 'void', funcIndex, typeIndex};
	funcs.set('__toplevel', info);
	mod.start	= funcIndex;
	worklist.push(W.withCatch(() => {
		const ctx	= new FunctionContext('__toplevel', new Scope(libGlobal), plainReturn('void'), undefined);
		ctx.ownBody = ast.body!;
		moduleVars.forEach(([name]) => ctx.vars.add(name));
		// Each statement gets its own buffer so a failure discards exactly its partial output: `ctx.emit`
		// appends, so a half-emitted statement would otherwise corrupt the start function's stack balance.
		const emitTopLevel = (st: Stmt) => {
			if (!onTopLevelError)
				return emitOneTopLevel(st);
			const before = ctx.swapOut();
			try {
				emitOneTopLevel(st);
				ctx.emit(...ctx.swapOut(before));
			} catch (e) {
				ctx.swapOut(before);
				onTopLevelError(new W.Error(e as any, st, '<module init>').inModule(ctx.homeModule));
			}
		};
		const emitOneTopLevel = (st: Stmt) => {
			if (st.type === 'export_decl' || st.type === 'function_decl' || st.type === 'class_decl' || st.type === 'type_alias_decl' || st.type === 'interface_decl' || st.type === 'import')
				return;
			// A bare `export {a, b}` / `export type {T} from '...'` / `export * from '...'` binds and evaluates
			// nothing; `export default <expr>` is excluded because that one really does have a value to evaluate.
			if (st.type === 'export' && !st.default)
				return;
			if (st.type === 'var_decl') {
				// Declarator by declarator, in source order, so forcing one below never reorders it past a
				// sibling that still emits normally.
				for (const d of st.declarations) {
					// A promoted const is already a real function; an alias (`const Scope = T.Scope`) only renames
					// something declared elsewhere (`isAliasInit`). Neither leaves anything for the start function to evaluate.
					if (typeof d.name === 'string' && (promotedConsts.has(d.name) || (d.init && isAliasInit(d.init, ctx.scope))))
						continue;
					// The lazy-global wrapper already caches this into the slot every other function reads, so
					// emitting the initializer here too ran a side-effecting one a SECOND time, into an invisible local.
					const lazy = typeof d.name === 'string' && d.init ? lazyGlobalFor(d.name, ctx) : undefined;
					if (lazy)
						ctx.emit(I.call(lazy.wrapper.funcIndex), I.drop);
					else
						emitStmt({ ...st, declarations: [d] }, ctx);
				}
				return;
			}
			emitStmt(st, ctx);
		};
		ast.body!.forEach(emitTopLevel);
		//emitTrailingUnreachable(ctx, result);
		info.body = ctx.toFuncBody(0, toValType);
	}));


	// Shared by the eager-compile loop and the exports-list loop so their classification can't drift apart;
	// `[]` for anything that isn't a function export (a value global, a class, ...).
	const exportedNames = new Set(ast.body.filter(s => s.type === 'export_decl').flatMap(s => {
		if (s.declaration.type === 'function_decl' && s.declaration.body)
			return [s.declaration.name];
		if (s.declaration.type === 'var_decl')
			return s.declaration.declarations.filter(d => typeof d.name === 'string' && promotedConsts.has(d.name) && functionDeclByName.has(d.name)).map(d => d.name as string);
	}));

	// Only *exported* top-level functions compile unconditionally here -- the exports-list loop reads
	// `funcs.get(name)!.funcIndex`. Every other one is discovered from a real call site (`emitCall`'s own
	// `funcs.get(name) ?? compileFunc(...)`), the same worklist-driven design classes/instantiations already get.
	// A generic has no single physical function to eagerly compile (like a generic class, kept out of `classes`),
	// and an exported one has no fixed wasm-level signature to give an export.
	const exportedFuncs: { name: string; info: FuncInfo }[] = [];
	for (const [name, decl] of functionDeclByName) {
		if (!exportedNames.has(name))
			continue;
		if (decl.typeParams?.length)
			continue;
		const info = compileFunc(name, decl);
		if (info) {
			(mod.exports??=[]).push({ name, kind: 'func', index: info.funcIndex });
			exportedFuncs.push({ name, info });
		}
	}

	while (worklist.length)
		worklist.shift()!();

	// A host call into an export IS the job boundary -- the same thing a libuv callback is for node -- so the
	// microtask queue drains on export return, never mid-call. "Outermost" is STRUCTURAL, needing no depth
	// counter: the wrapper is reachable only via the export TABLE, never by an internal or export-to-export call.
	// Emitted solely where the lib references `microtasks` (never a hardwired policy), after the worklist.
	if (lazyGlobalSlots.has(homeKey(LIB_MODULE, 'microtasks'))) {
		const hook = (n: string) => {
			const decl = LIB_DECL_MAP.get(n);
			return decl?.type === 'function_decl' ? ensureFunc(n, decl) : undefined;
		};
		const exit = hook('__towasm_exitCall');
		if (exit) {
			for (const { name, info } of exportedFuncs) {
				const { funcIndex, typeIndex } = types.func(toParams(info.params), toResults(info.result));
				const wrapper: FuncInfo = { ...info, funcIndex, typeIndex };
				const wctx		= new FunctionContext(`<export>.${name}`, new Scope(libGlobal), plainReturn(info.result), undefined);
				const argLocals = info.params.map((p, i) => wctx.declareLocal(`$arg$${i}`, p));
				argLocals.forEach(l => wctx.emit(I.local.get(l.index)));
				wctx.emit(I.call(info.funcIndex));
				// The real result sits on the stack underneath this void call, so the drain runs before the
				// return without disturbing it; appending to the callee's own epilogue couldn't handle several `return`s.
				wctx.emit(I.call(exit.funcIndex));
				wrapper.body = wctx.toFuncBody(argLocals.length, toValType);
				closureLiterals.push(wrapper);
				const e = mod.exports!.find(x => x.kind === 'func' && x.name === name);
				if (e)
					e.index = funcIndex;
			}
			while (worklist.length)
				worklist.shift()!();
		}
	}

	// `lateWorklist` (any-dispatch cascade bodies) needs the full, final candidate set, so it starts only
	// once `worklist` drains; building a cascade can push a new candidate back, so it drains again after each item.
	while (lateWorklist.length) {
		lateWorklist.shift()!();
		while (worklist.length)
			worklist.shift()!();
	}

	// ---- assemble the module ----

	const numImports	= mod.imports.length;
	const numFuncs		= [...funcs.values()].filter(info => info.funcIndex >= numImports).length;
	mod.functionTypes	= new Array<number>(numFuncs);
	mod.code			= new Array<wasm.FuncBody>(numFuncs);

	function place(info: FuncInfo) {
		if (info.funcIndex < numImports)
			return;
		mod.functionTypes![info.funcIndex - numImports]	= info.typeIndex;
		mod.code![info.funcIndex - numImports]			= info.body!;
	}

	for (const info of funcs.values())
		place(info);

	for (const info of lazyGlobals.values())
		place(info);

	for (const info of closureLiterals)
		place(info);

	const importedFuncTypeIndices = new Set((mod.imports ?? []).flatMap(imp => imp.desc.kind === 'func' && typeof imp.desc.typeIndex === 'number' ? [imp.desc.typeIndex] : []));
	mod.types			= { types, groupSizes: types.groupSizes(importedFuncTypeIndices) };

	if (mod.code.some(b => touchesMemory(b.body))) {
		mod.memories	= [{ min: 1 }];
		// So a host can actually read back what got written to it (e.g. console.log's fd_write buffer) --
		// any consumer of real linear memory benefits, not just console.log specifically.
		(mod.exports ??= []).push({ name: 'memory', kind: 'memory', index: 0 });
	}
	
	mod.globals			= Array.from(globals.entries()).map(([name, {init, initInstrs, wtype, mut}]) => {
		if (initInstrs)
			return {type: { mut, type: toValType(wtype) }, init: initInstrs};
		if (init) {
			const type = { mut, type: toValType(wtype) };
			if (T.isNullLiteral(init)) {
				if (!W.isNullable(wtype))
					throw `global '${name}' can't be initialized to 'null'/'undefined' -- its type isn't nullable`;
				return {type, init: [I.ref.null(heapTypeIndexOf(wtype))]};
			}
			const wtype2 = W.notUnsigned(W.scalarKind(wtype));
			if (wtype2 && init?.type === 'literal') {
				if (typeof init.value === 'number' || typeof init.value === 'boolean')
					return {type, init: [I[wtype2](+init.value)]};
				if (typeof init.value === 'bigint' && wtype2 === 'i64')
					return {type, init: [I[wtype2](init.value)]};
			}
		}
		throw `global '${name}' needs a compile-time-constant initializer`;
	});

	// `array.new_data` is not a constant expression (V8 rejects it), so each string global starts as an empty array and the
	// start function fills it once, before any top-level statement runs. Still one materialization per program, not per use.
	const strings = [...globals.values()].flatMap(g => g.stringData
		? [I.i32.const(g.stringData.offset), I.i32.const(g.stringData.length), I.array.new_data(types.array('i16'), 0), I.global.set(g.index)]
		: []);
	if (strings.length) {
		const top = funcs.get('__toplevel')!.body;
		if (!top)
			throw 'internal: the start function must be compiled before its string globals are filled';
		top.body = [...strings, ...top.body];
	}

	mod.datas			= [{ mode: 'passive', bytes: data.bytes }];
	if (tags.length)
		mod.tags		= tags;

	// Every closure literal's `funcIndex` is taken by `ref.func` at its creation site -- wasm requires any function referenced that way to be "declared" first, which a declarative element segment satisfies.
	if (closureLiterals.length)
		mod.elements = [{ mode: 'declarative', reftype: { ref: 'func', nullable: true }, funcIndices: closureLiterals.map(info => info.funcIndex) }];

	return mod;
}
