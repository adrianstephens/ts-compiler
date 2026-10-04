// The language-neutral half of the wasm backend: what a value physically IS (`Type` and its helpers), codegen state (`FunctionContext`,
// `ClassInfo`), the module sections (`Types`, `DataSection`, `TagSection`) and the inline-`__asm` island. No language's AST, types or checker.
// `ClosureSig` names only a closure's PHYSICAL shape; its binding data (defaults, resolved params) is `FuncSig`'s, in the language half.

import * as wasm from '@isopodlabs/binary_libs/wasm';
import * as WAT from './wat-parser';
import { Location } from '@isopodlabs/tison/ast';

const I				= wasm.I;

export type ScalarI		= 'i32' | 'i64' | 'f32' | 'f64'
export type Scalar		= ScalarI | 'u32' | 'u64'
export type ElementI	= ScalarI | 'i8' | 'i16' | 'ref';
export type Element		= ElementI | 'u8' | 'u16' | 'u32' | 'u64';
// The PHYSICAL shape of a closure, what wasm needs to call it; `FuncSig` extends it with the binding data argument binding reads.
export interface ClosureSig	{ params: Type[]; result: Type; hasRest?: boolean }

// An asm body's physical result: a signature and instructions (`Inline` in the language half adds the binding payload).
export interface Inline extends ClosureSig { inline: wasm.Instr[] }

export type Type		= Scalar
	| 'void'	// only valid as a function result, never a param/local/field.
	| { ref:		string; nullable?: boolean }
	| { arr:		ElementI; nullable?: boolean }
	| { closure:	ClosureSig; nullable?: boolean }
	| { typeIndex:	number; nullable?: boolean }
	// A boxed nullable primitive (`number | null`): only it sets `primKind`, which tells it apart from a class or env struct (`unboxedPrimitive`)
	// even where structural memoization shares a type index with a one-scalar-field struct.
	| { typeIndex:	number; nullable?: boolean; primKind: ScalarI };


// Shared singletons -- ctx.local compares Type by object identity
export const ARRAY: Record<ElementI, Type> = {
	i8:		{ arr: 'i8' },
	i16:	{ arr: 'i16' },
	i32:	{ arr: 'i32' },
	i64:	{ arr: 'i64' },
	f32:	{ arr: 'f32' },
	f64:	{ arr: 'f64' },
	ref:	{ arr: 'ref' },
};
export const REF_ANY:			Type = { ref: 'any' };
export const REF_ANY_NULLABLE:	Type = { ref: 'any', nullable: true };
export const REF_EXN:			Type = { ref: 'exn', nullable: true };

// The scalar kind a value acts as for arithmetic and comparison: a boxed nullable primitive unwrapped, as `coerceTop` does; undefined otherwise.
export function scalarKind(wtype: Type | undefined): Scalar | undefined {
	return typeof wtype === 'string' ? (wtype !== 'void' ? wtype : undefined) : wtype && unboxedPrimitive(wtype)?.kind;
}
export function notUnsigned(wtype: Scalar): ScalarI;
export function notUnsigned(wtype: Scalar | undefined): ScalarI  | undefined;
export function notUnsigned(wtype: Element): ElementI;
export function notUnsigned(wtype: string | undefined) {
	return wtype && wtype[0] === 'u' ? `i${wtype.slice(1)}` : wtype;
}
export function elementKind(wtype: Type | undefined): ElementI {
	return typeof wtype === 'string' && wtype !== 'void' ? notUnsigned(wtype) : 'ref';
}

export type RefType		= Extract<Type, { ref: string }>;
export type ArrType		= Extract<Type, { arr: ElementI }>;
export type ClosureType	= Extract<Type, { closure: ClosureSig }>;
export type IndexedType	= Extract<Type, { typeIndex: number }>;

export function isRef(w: Type | undefined): w is RefType				{ return typeof w === 'object' && 'ref' in w; }
export function isArr(w: Type | undefined): w is ArrType				{ return typeof w === 'object' && 'arr' in w; }
export function isClosure(w: Type | undefined): w is ClosureType		{ return typeof w === 'object' && 'closure' in w; }
export function isIndexed(w: Type | undefined): w is IndexedType		{ return typeof w === 'object' && 'typeIndex' in w; }
// Their false branches keep every variant: an object variant's `nullable?: boolean` / `ref: string` is no subtype of the guarded one.
export function isNullable(w: Type | undefined): w is Extract<Type, object> & { nullable: true }	{ return typeof w === 'object' && !!w.nullable; }
export function isAny(w: Type | undefined): w is RefType & { ref: 'any' }							{ return isRef(w) && w.ref === 'any'; }

// A boxed nullable primitive's scalar kind and box type index, else undefined. Read off `primKind` on the object: by type index alone,
// an env struct capturing one `f64` may share the box's index.
export function unboxedPrimitive(wtype: Type): { kind: ScalarI; typeIndex: number } | undefined {
	return typeof wtype !== 'string' && 'primKind' in wtype ? { kind: wtype.primKind, typeIndex: wtype.typeIndex } : undefined;
}

export function typeEq(a: Type, b: Type): boolean {
	if (typeof a === 'string' || typeof b === 'string')
		return a === b;
	if ('ref' in a && 'ref' in b)
		return a.ref === b.ref && !a.nullable === !b.nullable;
	if ('arr' in a && 'arr' in b)
		return a.arr === b.arr && !a.nullable === !b.nullable;
	if ('typeIndex' in a && 'typeIndex' in b)
		return a.typeIndex === b.typeIndex && !a.nullable === !b.nullable;
	if ('closure' in a && 'closure' in b)
		return !a.nullable === !b.nullable
			&& a.closure.params.length === b.closure.params.length
			&& typeEq(a.closure.result, b.closure.result)
			&& a.closure.params.every((p, i) => typeEq(p, b.closure.params[i]))
			&& !a.closure.hasRest === !b.closure.hasRest;

	return false;
}
// The machine int a BIGINT of this range fits, or undefined for the limb array. Signed only: a `u32` at or above 2^31 written as one
// two's-complement limb would read back negative.
export function bigIntType(min: bigint, max: bigint): Type | undefined {
	return min >= -0x80000000n && max <= 0x7fffffffn ? 'i32'
		: min >= -0x8000000000000000n && max <= 0x7fffffffffffffffn ? 'i64'
		: undefined;
}

// Picks the tightest integer wasm type for a known range: i32, u32, or f64.
export function intType(min: number, max: number): 'i32' | 'u32' | 'f64' {
	if (min >= -0x80000000 && max <= 0x7fffffff)
		return 'i32';
	if (min >= 0 && max <= 0xffffffff)
		return 'u32';
	return 'f64';
}

// A stable structural key for a `Type`.
export function typeKey(w: Type): string {
	if (typeof w === 'string')
		return w;
	if ('ref' in w)
		return `ref:${w.ref}:${!!w.nullable}`;
	if ('arr' in w)
		return `arr:${w.arr}:${!!w.nullable}`;
	if ('closure' in w)
		return `(${w.closure.params.map(typeKey).join(',')})=>${typeKey(w.closure.result)}:${!!w.nullable}`;
	if ('typeIndex' in w)
		return `typeIndex:${w.typeIndex}:${!!w.nullable}`;
	return '?';
}

// The one `Type` a union of >=2 members' representations collapses to: members that physically agree stay so (`IteratorResult<number, number>
// .value` is `f64`), scalar spellings of a number widen to `f64` (`i32` vs `f64`), and anything else boxes as `any`.
export function combineUnion(wtypes: readonly Type[]): Type {
	if (new Set(wtypes.map(w => typeKey(w))).size === 1)
		return wtypes[0];
	if (wtypes.every(w => scalarKind(w) !== undefined))
		return 'f64';
	return wtypes.some(isNullable) ? REF_ANY_NULLABLE : REF_ANY;
}

export class Error {
	msg:	string;
	pos?:	Location;
	scope:	string[] = [];
	// The module `pos` is in, set where `pos` is (`inModule`): a position alone can't say which reached file it's in.
	module?: string;
	constructor(err: string|Error, node?: any, ...scope: string[]) {
		if (err instanceof Error) {
			this.msg	= err.msg;
			this.pos		= err.pos ?? node?.pos;
			this.module		= err.module;
			this.scope		= [...err.scope, ...scope];
		} else {
			this.msg	= err;
			this.pos		= node?.pos;
			this.scope		= scope;
		}
	}
	inModule(module: string): Error {
		if (this.pos && !this.module)
			this.module = module;
		return this;
	}
	get message() {
		return `tsw:${this.pos ? ` (${this.pos.line}:${this.pos.col})` : ''}${this.scope.map(i => ` in ${i}`).join('')} ${this.msg}`;
	}
}


// A body compiled later from the worklist, outside its declaration's catch: an error on a synthesized node falls back to this position and module.
export function withCatchAt(item: ()=>void, node: unknown, module: string, ...scopes: string[]) {
	return () => {
		try {
			item();
		} catch (e) {
			throw new Error(e as any, node, ...scopes).inModule(module);
		}
	};
}

export function withCatch(item: ()=>void, ...scopes: string[]) {
	return () => {
		try {
			item();
		} catch (e) {
			throw new Error(e as any, undefined, ...scopes);
		}
	};
}

export interface Local {
	wtype:			Type;
	index:			number;
	holderInner?:	Type;
}

export interface ClosureEnv {
	envLocal:		Local;
	envTypeIndex:	number;
	fields:			Map<string, Local>
};

// Pushed by `case 'try'` with a `finally`: `emitBreak`/`emitContinue` check the innermost guard first, and a target outside it stashes an action
// code and branches to the landing point, so `finally` runs first. Popped before that landing's re-dispatch, so nested guards compose.
export interface FinallyGuard {
	actionLocal:				Local;
	breakTargetsLenAtEntry:		number;
	continueTargetsLenAtEntry:	number;
	landingDepth:				number
};



// A closure's immutable fields: code, env, length.
export const CLOSURE_CORE = 3;

// A method-bearing struct (a class, a synthesized shape, a builtin owner): only physical facts. What a method DECLARES, and `declScope`,
// stay with the language (`Scope` belongs to type-utils, which imports this).
export class ClassInfo {
	// `optional` is set only for an object shape's own `key?: T` member; a real class field is never optional.
	fields:			{ name: string; wtype: Type; optional?: boolean }[] = [];
	fieldIndex		= new Map<string, number>();
	getterNames?:	Set<string>;
	setterNames?:	Set<string>;
	homeModule?:	string;
	// The class's physical `this` type, unset only while its constructor is compiled (`{ref: name}` is the answer then).
	thisWtype?:		Type;
	// `fields`/`fieldIndex` are seeded with the superclass's, in order, so wasm-GC's prefix field subtyping holds.
	superClass?:	ClassInfo;
	// A callable object with properties: its struct extends this closure's, whose fields are its first `Types.callablePrefix`.
	callable?:		ClosureType;

	// `typeIndex` is -1 until `fields` is populated; a constructor returning a scalar never gets a struct type.
	constructor(public name: string, public typeIndex: number) {}

	get thisType(): Type {
		return this.thisWtype ?? { ref: this.name };
	}

	// A name redeclaring an inherited field is an error, not a second slot.
	addField(name: string, wtype: Type, optional = false): void {
		if (this.fieldIndex.has(name))
			throw `field '${name}' redeclares an inherited field -- not supported`;
		this.fieldIndex.set(name, this.fields.length);
		this.fields.push({ name, wtype, optional });
	}

	isBaseOf(cls: ClassInfo | undefined): boolean {
		while (cls) {
			// By identity too: a shared object shape is reachable under more than one key.
			if (cls.name === this.name || cls === this)
				return true;
			cls = cls.superClass;
		}
		return false;
	}

}

// Each slot type's zero, as a thunk so no instruction object is shared; `hasDefaultValue` and `emitDefaultValue` read the same table.
const SCALAR_ZERO = new Map<string, () => wasm.Instr>([
	['f64', () => I.f64.const(0)],
	['f32', () => I.f32.const(0)],
	['i32', () => I.i32.const(0)],
	['i64', () => I.i64.const(0n)],
]);

export class FunctionContext {
	// Declarations in order; a name may repeat (a closed sibling scope's, a live nested shadow): `lookup` scans from the end skipping closed ones.
	// `pinned`: the FUNCTION's, untouched by `closeScope` (only a constructor's `this`, `materializeThis`).
	declared:	{ name: string; local: Local; closed: boolean; pinned?: boolean }[] = [];
	// Watermarks (`declared.length` at open time) for each currently open lexical block -- see `openScope`.
	scopeStack: number[] = [];
	// One type per wasm local index (params included), fixed for the function, so `freeSlots` reuses only a same-typed index.
	slotTypes:	Type[] = [];
	freeSlots	= new Map<string, number[]>();
	// One counter for every scratch-local name in this function (`$anytruthy$3`, `#switch$0`): unique per function suffices.
	tempCounter	= 0;
	out:		wasm.Instr[]	= [];
	ctorThis?:	Local;

	// Set while a collecting constructor (`ensureCtor`) gathers field values ahead of `struct.new`: `this.field` reads a collected field's local
	// before a real `this` exists. Cleared once `ctorThis` is set.
	ctorFields?: Map<string, Local>;

	depth = 0;
	breakTargets:		number[] = [];
	continueTargets:	number[] = [];

	// Set when this FuncCtx is a closure body -- captured names have no real local, reads/writes go through struct.get/set on envLocal.
	closureEnv?:		ClosureEnv;
	
	// `collectCapturedMutables(ownBody)`, computed on first use -- see `needsHolder`.
	holderNames?:		Set<string>;

	// What `case 'try'` with a `finally` pushes (`FinallyGuard`).
	finallyGuards:		FinallyGuard[] = [];

	constructor(public name: string) {}

	lookup(name: string): Local | undefined {
		for (let i = this.declared.length - 1; i >= 0; i--) {
			const d = this.declared[i];
			if (!d.closed && d.name === name)
				return d.local;
		}
		return undefined;
	}

	private allocLocal(wtype: Type): number {
		const free = this.freeSlots.get(typeKey(wtype));
		return free?.length ? free.pop()! : this.slotTypes.push(wtype) - 1;
	}
	private freeLocal(wtype: Type, index: number) {
		const key	= typeKey(wtype);
		const free	= this.freeSlots.get(key);
		if (free)
			free.push(index);
		else
			this.freeSlots.set(key, [index]);
	}

	// More levels with no `break`/`continue` target of their own.
	enterLabel(n = 1)		{ return this.depth += n; }
	exitLabel(n = 1)		{ this.depth -= n; }

	// A loop or switch's enclosing block -- what `break` (with no label) branches to.
	enterBreakTarget()		{ this.breakTargets.push(++this.depth); }
	exitBreakTarget()		{ this.breakTargets.pop(); this.depth--; }

	// A loop's own restart point -- what `continue` branches to.
	enterContinueTarget()	{ this.continueTargets.push(++this.depth); }
	exitContinueTarget()	{ this.continueTargets.pop(); this.depth--; }

	openScope() {
		this.scopeStack.push(this.declared.length);
		return this;
	}

	// Closes the innermost scope: its declarations leave `lookup`, their slots go back on the free list for same-typed reuse.
	closeScope() {
		const mark = this.scopeStack.pop();
		if (mark === undefined)
			throw 'unbalanced scope close';
		for (let i = mark; i < this.declared.length; i++) {
			const d = this.declared[i];
			if (!d.closed && !d.pinned) {
				d.closed = true;
				this.freeLocal(d.local.wtype, d.local.index);
			}
		}
		return this;
	}

	inScope<T>(fn: (ctx: FunctionContext) => T): T {
		this.openScope();
		const result = fn(this);
		this.closeScope();
		return result;
	}

	emitBreak() {
		const guard = this.finallyGuards.at(-1);
		if (guard && this.breakTargets.length <= guard.breakTargetsLenAtEntry)
			this.emit(I.i32.const(2), I.local.set(guard.actionLocal.index), I.br(this.depth - guard.landingDepth));
		else
			this.emit(I.br(this.depth - this.breakTargets.at(-1)!));
	}
	emitContinue() {
		const guard = this.finallyGuards.at(-1);
		if (guard && this.continueTargets.length <= guard.continueTargetsLenAtEntry)
			this.emit(I.i32.const(3), I.local.set(guard.actionLocal.index), I.br(this.depth - guard.landingDepth));
		else
			this.emit(I.br(this.depth - this.continueTargets.at(-1)!));
	}
	// A still-visible same-name, same-typed entry is reused.
	temp(name: string, wtype: Type): number {
		const prev = this.lookup(name);
		if (prev) {
			// Structurally: two equal types need not be one object (`Types.nullable(REF_ANY)` and `REF_ANY_NULLABLE`).
			if (typeKey(prev.wtype) !== typeKey(wtype))
				throw `local '${name}' redeclared with different type`;
			return prev.index;
		}
		const index = this.allocLocal(wtype);
		this.declared.push({ name, local: { wtype, index}, closed: false });
		return index;
	}

	declareLocal(name: string, wtype: Type, pinned = false): Local {
		const scopeStart = this.scopeStack.at(-1) ?? 0;
		for (let i = this.declared.length - 1; i >= scopeStart; i--) {
			const d = this.declared[i];
			if (!d.closed && d.name === name)
				throw `local '${name}' redeclared (shadowing within the same scope is not supported)`;
		}
		const local = {wtype, index: this.allocLocal(wtype)};
		this.declared.push({ name, local, closed: false, pinned });
		return local;
	}

	resolvesName(name: string): boolean {
		return this.lookup(name) !== undefined || !!this.closureEnv?.fields.has(name);
	}

	// The type of a name's logical VALUE: a local, an env field, or a forward-holder's inner type once unboxed (`rawWtype` is the exception).
	resolvedWtype(name: string): Type | undefined {
		const captured = this.closureEnv?.fields.get(name);
		if (captured)
			return captured.holderInner ?? captured.wtype;
		const local = this.lookup(name);
		return local?.holderInner ?? local?.wtype;
	}
	// The type of a name's STORAGE slot: a forward-holder's boxed type, which a closure capturing its shared storage needs.
	rawWtype(name: string): Type | undefined {
		return this.closureEnv?.fields.get(name)?.wtype ?? this.lookup(name)?.wtype;
	}

	// Reads a name's own storage slot: a captured name lives in `closureEnv`, everything else in a local.
	rawSlot(name: string) {
		const captured = this.closureEnv?.fields.get(name);
		if (captured) {
			this.emit(I.local.get(this.closureEnv!.envLocal.index), I.struct.get(this.closureEnv!.envTypeIndex, captured.index));
			return;
		}
		this.emit(I.local.get(this.lookup(name)!.index));
	}

	// A holder's field is nullable, allocatable empty; `holderInner` is the non-null logical type, sound because the filling declaration runs first.
	emitHolderRead(holderType: number, inner: Type) {
		this.emit(I.struct.get(holderType, 0));
		if (typeof inner !== 'string' && !inner.nullable)
			this.emit(I.ref.as_non_null);
	}

	swapOut(out: wasm.Instr[] = []) {
		const _old	= this.out;
		this.out	= out;
		return _old;
	}

	emit(...instr: (wasm.Instr|wasm.Instr[])[]) {
		this.out.push(...instr.flat());
	}

	// Each of the four below owns the levels it opens (`depth` counts them while the body runs), so a depth-relative `br` inside lands right;
	// the wrapper is built AFTER the body, whose branches are relative to it.

	// Exactly one arm, its value left on the stack; each arm in its own instruction list, so neither runs before the condition.
	emitIf(vt: wasm.ValType | undefined, then: () => void, els?: () => void): void {
		const outer		= this.swapOut();
		this.enterLabel();
		then();
		const thenArm	= this.swapOut();
		els?.();
		this.exitLabel();
		const elseArm	= this.swapOut(outer);
		this.emit(elseArm.length ? I.if(vt, thenArm, elseArm) : I.if(vt, thenArm));
	}

	emitBlock(body: () => void): void {
		const outer = this.swapOut();
		this.enterLabel();
		body();
		this.exitLabel();
		this.emit(I.block(undefined, this.swapOut(outer)));
	}

	// A block `continue` branches to instead of the loop's restart, for a `for`, whose update still runs; shadows the loop's target for this body.
	emitContinueBlock(body: () => void): void {
		this.emitBlock(() => {
			this.continueTargets.push(this.depth);
			body();
			this.continueTargets.pop();
		});
	}

	// `block` around `loop`: `break` leaves by the block, `continue` restarts at the loop, both registered here.
	emitLoop(body: () => void): void {
		const outer = this.swapOut();
		this.breakTargets.push(++this.depth);
		this.continueTargets.push(++this.depth);
		body();
		this.continueTargets.pop();
		this.breakTargets.pop();
		this.depth -= 2;
		this.emit(I.block(undefined, [I.loop(undefined, this.swapOut(outer))]));
	}

	// A non-`void` body need not end in a `return` (`if`/`while`/`switch` compile to `void` blocks): a trailing `unreachable` satisfies the
	// validator, dead wherever a return already covers every path.
	emitTrailingUnreachable(result: Type): void {
		if (result !== 'void')
			this.emit(I.unreachable);
	}

	// Truthiness of a boxed `any`, decided at RUN TIME. `0n` shares `arr:i32` with `Int32Array` and so reads as truthy: the one wrong answer.
	emitAnyTruthy(got: Type, types: Types): void {
		// The NULLABLE slot: a non-nullable local is not defaultable, and the null test is skipped when `got` rules null out.
		const tmp		= this.temp(`$anytruthy$${this.tempCounter++}`, REF_ANY_NULLABLE);
		const boxI32	= types.box('i32');
		const boxF64	= types.box('f64');
		const str		= types.array('i16');
		this.emit(I.local.set(tmp));

		const arms: (() => void)[][] = [
			// A boxed `i32` is a `boolean` or an `i32`-kind number, and `0` is the falsy one for both.
			[()	=> this.emit(I.local.get(tmp), I.ref.test(boxI32)),
			()	=> this.emit(I.local.get(tmp), I.ref.cast(boxI32), I.struct.get(boxI32, 0), I.i32.const(0), I.i32.ne)],
			// `abs(x) > 0`, for the same NaN/`-0` reasons the bare-`f64` case above gives.
			[()	=> this.emit(I.local.get(tmp), I.ref.test(boxF64)),
			()	=> this.emit(I.local.get(tmp), I.ref.cast(boxF64), I.struct.get(boxF64, 0), I.f64.abs, I.f64(0), I.f64.gt)],
			// A string is falsy when EMPTY -- same `arr:i16` test the checker-typed path above makes statically.
			[()	=> this.emit(I.local.get(tmp), I.ref.test(str)),
			()	=> this.emit(I.local.get(tmp), I.ref.cast(str), I.array.len, I.i32.const(0), I.i32.ne)],
		];
		if (typeof got === 'object' && got.nullable)
			arms.unshift([() => this.emit(I.local.get(tmp), I.ref.is_null), () => this.emit(I.i32.const(0))]);

		// Nested `if`s, innermost last: everything that matched no box is a real object/array/closure.
		const chain = (i: number): void => {
			if (i === arms.length)
				return this.emit(I.i32.const(1));
			arms[i][0]();
			const _old = this.swapOut();
			arms[i][1]();
			const _then = this.swapOut();
			chain(i + 1);
			this.emit(I.if('i32', _then, this.swapOut(_old)));
		};
		chain(0);
	}

	// Pushes `want`'s zero, which an array-literal hole (`[1, , 3]`) reads back as. A non-nullable ref/array/closure has none. `hasDefaultValue` asks
	// the same without emitting: an absent key read off an `any` spread into a non-nullable slot then traps rather than invent a value.
	hasDefaultValue(want: Type, toValType: (t: Type) => wasm.ValType): boolean {
		const vt = toValType(want);
		return typeof vt === 'string' ? SCALAR_ZERO.has(vt) : !!vt.nullable || vt.ref === 'any';
	}

	emitDefaultValue(want: Type, types: Types, toValType: (t: Type) => wasm.ValType): void {
		// The rendered form decides, not the `Type` spelling: `u32`/`u64` share their signed twin's zero.
		const vt = toValType(want);
		if (typeof vt === 'string') {
			const zero = SCALAR_ZERO.get(vt);
			if (zero) {
				this.emit(zero());
				return;
			}
		} else if (vt.nullable) {
			this.emit(I.ref.null(heapTypeOf(vt)));
			return;
		} else if (vt.ref === 'any') {
			// A non-nullable `any` slot has no `null`, so a placeholder box fills it (a type param at `any` for an unrepresentable `void`); nothing reads it.
			this.emit(I.f64.const(0), I.struct.new(types.box('f64')));
			return;
		}
		throw `a slot with no value (an array literal hole, an absent spread key) needs a nullable or scalar type, not '${typeKey(want)}'`;
	}

	// `obj?.method()`: the receiver once into a scratch local, a null result when it is null. Every optional access guards this way.
	emitOptionalAccess(objWtype: Type, resultWtype: Type, toValType: (t: Type) => wasm.ValType, readCore: (objLocal: number) => void): Type {
		const objLocal = this.temp(`$opt$obj$${this.tempCounter++}`, objWtype);
		const vt = toValType(resultWtype);
		this.emit(I.local.set(objLocal), I.local.get(objLocal), I.ref.is_null);
		this.emitIf(vt, () => this.emit(I.ref.null(heapTypeOf(vt))), () => readCore(objLocal));
		return resultWtype;
	}

	toFuncBody(numParams: number, toValType: (t: Type) => wasm.ValType): wasm.FuncBody & {id: string} {
		return { id: this.name.replace(/[^a-zA-Z0-9_]/g, '_'), locals: this.slotTypes.slice(numParams).map(t => ({ count: 1, type: toValType(t) })), body: this.out };
	}

}



// `toValType`'s `.ref`, unwrapped from the `wasm.ValType` shape -- what `ref.null` needs.
function heapTypeOf(vt: wasm.ValType): wasm.HeapType {
	if (typeof vt === 'string' || !('ref' in vt))
		throw 'internal: expected a reference type';
	return vt.ref;
}

export function mentionsTypeIndex(t: wasm.SubType, index: number): boolean {
	const comp = 'type' in t ? t.type : t;
	const is = (v: unknown) => typeof v === 'object' && v !== null && 'ref' in v && (v as { ref: unknown }).ref === index;
	return ('supertypes' in t && t.supertypes.includes(index))
		|| (comp.kind === 'struct' ? comp.fields.some(f => is(f.type))
		: comp.kind === 'array' ? is(comp.field.type)
		: comp.kind === 'func' && (comp.params.some(p => is(p.type)) || comp.results.some(is)));
}

export class Types extends Array<wasm.SubType> {
	typeMap			= new Map<string, number>();
	// Set when the program gives a function a property its type lacks: every closure then carries a mutable `#ext` map slot (null until written).
	closureExt		= false;
	// Before the first closure type exists, since every closure struct extends the base.
	enableClosureExt() {
		if (this.typeMap.has(wasm.typeKey({ final: false, supertypes: [], type: { kind: 'struct', fields: this.closureFields('func') } })!))
			throw "internal: the closure '#ext' slot was enabled after a closure type was made";
		this.closureExt = true;
	}

	array(kind: ElementI): number		{ return this.register(this.arrayDesc(kind)); }
	hasArray(kind: ElementI): boolean	{ return this.has(this.arrayDesc(kind)); }
	box(kind: ScalarI): number			{ return this.register(this.boxDesc(kind)); }
	hasBox(kind: ScalarI): boolean		{ return this.has(this.boxDesc(kind)); }

	// The nullable form: a scalar BOXES (a ref to a one-field struct; `u32`/`u64` share their signed twin's box); a reference takes the flag.
	nullable(base: Type): Type {
		if (typeof base !== 'string')
			return { ...base, nullable: true };
		if (base === 'void')
			throw "a nullable 'void' value is not supported -- 'void' has no value representation to box";
		const kind = notUnsigned(base);
		return { typeIndex: this.box(kind), nullable: true, primKind: kind };
	}

	// The supertype of every closure env struct: no fields, not final.
	envBase(): number {
		return this.register({ final: false, supertypes: [], type: { kind: 'struct', fields: [] } });
	}

	// The prefix of every closure struct (code pointer, env, arity). Its first field is `(ref $itsFuncType)` under a covariant immutable field,
	// so `ref.test` against it is exactly "is this a function", nominal.
	closureBase(): number {
		return this.register({ final: false, supertypes: [], type: { kind: 'struct', fields: this.closureFields('func') } });
	}

	// One closure struct per call signature, `closureBase` plus its func type (rendered by the caller). Not final: a callable object extends it.
	closure(funcTypeIndex: number): number {
		return this.register({ final: false, supertypes: [this.closureBase()], type: { kind: 'struct', fields: this.closureFields(funcTypeIndex) } });
	}
	closureFields(code: number | 'func'): wasm.FieldType[] {
		return [
			{ type: { ref: code, nullable: false }, mut: false },
			{ type: { ref: this.envBase(), nullable: false }, mut: false },
			{ type: 'i32', mut: false },
			...this.closureExt ? [{ type: { ref: 'any' as const, nullable: true }, mut: true }] : [],
		];
	}
	// The closure struct's own fields (code, env, length, `#ext` if any), leading a callable object's struct.
	get callablePrefix(): number	{ return CLOSURE_CORE + (this.closureExt ? 1 : 0); }

	// The one-field mutable cell a captured binding becomes, shared by the closure and the declaring scope.
	holder(vt: wasm.ValType): number {
		return this.register({ final: true, supertypes: [], type: { kind: 'struct', fields: [{ type: vt, mut: true }] } });
	}

	// Function indices come off the type section's counter (a func's type is registered first): `func` is the pair callers want.
	private nextFunc = 0;
	funcType(params: wasm.ParamType[], results: wasm.ValType[]): number {
		return this.register({ final: true, supertypes: [], type: { kind: 'func', params, results } });
	}
	funcAt(typeIndex: number): { funcIndex: number; typeIndex: number } {
		return { funcIndex: this.nextFunc++, typeIndex };
	}
	func(params: wasm.ParamType[], results: wasm.ValType[]): { funcIndex: number; typeIndex: number } {
		return this.funcAt(this.funcType(params, results));
	}

	// One rec group per contiguous run of struct/array types: equivalence is structural ACROSS groups, and singletons would canonicalize identical
	// shapes `ref.test` cannot tell apart. Each host-imported func type is a singleton (wasmtime rejected WASI's `fd_write` otherwise).
	groupSizes(importedFuncTypes: Set<number>): number[] {
		const sizes: number[] = [];
		for (let i = 0, runStart = 0; i <= this.length; i++) {
			if (i === this.length || importedFuncTypes.has(i)) {
				if (i > runStart)
					sizes.push(i - runStart);
				if (i < this.length)
					sizes.push(1);
				runStart = i + 1;
			}
		}
		return sizes;
	}

	private arrayDesc(kind: ElementI): wasm.SubType {
		return { final: true, supertypes: [], type: { kind: 'array', field: { type: kind === 'ref' ? { ref: 'any', nullable: true } : kind, mut: true } } };
	}
	private boxDesc(kind: ScalarI): wasm.SubType {
		return { final: true, supertypes: [], type: { kind: 'struct', fields: [{ type: kind, mut: false }] } };
	}


	// The heap type a `typeof` tag's run-time test needs: a scalar's box, a string's or `bigint`'s array, the closure base.
	heapType(tag: string): number | undefined {
		switch (tag) {
			case 'number':		return this.box('f64');
			case 'boolean':		return this.box('i32');
			case 'string':		return this.array('i16');
			case 'bigint':		return this.array('i32');
			case 'function':	return this.closureBase();
		}
		return undefined;
	}

	get(i: number) { return this[i]; }
	set(i: number, t: wasm.SubType) { this[i] = t; }

	add(type: wasm.SubType): number {
		return this.push(type) - 1;
	}
	// Whether this array type exists, WITHOUT creating it: a speculative scan must not add types, and an absent one means no such value exists.
	has(desc: wasm.SubType): boolean {
		const key = wasm.typeKey(desc);
		return key !== undefined && this.typeMap.has(key);
	}

	register(type: wasm.SubType): number {
		const key		= wasm.typeKey(type);
		const existing	= key !== undefined ? this.typeMap.get(key) : undefined;
		if (existing !== undefined)
			return existing;
		const typeIndex = this.add(type);
		if (key !== undefined)
			this.typeMap.set(key, typeIndex);
		return typeIndex;
	}
	
}

// The one passive data segment: bytes plus the string table. Strings are UTF-16LE, matching `charCodeAt`, so an `i16` array builds from them.
export class DataSection {
	private buffer	= new Uint8Array(0);
	private strings	= new Map<string, number>();

	// Appends `newdata` and returns its offset. `align` is 2 for the strings: a code unit must not straddle.
	add(newdata: Uint8Array, align = 1): number {
		const adjust = this.buffer.byteLength % align;
		const offset = this.buffer.byteLength + (adjust ? align - adjust : 0);
		const total	= offset + newdata.byteLength;
		if (this.buffer.buffer.byteLength < total) {
			const grown = new Uint8Array(Math.max(this.buffer.buffer.byteLength * 2, total));
			grown.set(this.buffer, 0);
			this.buffer = grown.subarray(0, total);
		}
		this.buffer = new Uint8Array(this.buffer.buffer, 0, total);
		this.buffer.set(newdata, offset);
		return offset;
	}

	intern(value: string): number {
		const existing = this.strings.get(value);
		if (existing !== undefined)
			return existing;
		const bytes = new Uint8Array(value.length * 2);
		const view	= new DataView(bytes.buffer);
		for (let i = 0; i < value.length; i++)
			view.setUint16(i * 2, value.charCodeAt(i), true);
		const offset = this.add(bytes, 2);
		this.strings.set(value, offset);
		return offset;
	}

	get bytes(): Uint8Array { return this.buffer; }
}

// One tag per language: a throw carries one boxed `any`, so `(anyref) -> ()` serves every `throw`/`try_table`.
export class TagSection extends Array<wasm.TagType> {
	private exceptionIndex?: number;

	exception(types: Types): number {
		return this.exceptionIndex ??= this.push({ attribute: 0, typeIndex: types.funcType([{ type: { ref: 'any', nullable: false } }], []) }) - 1;
	}
}

// ===================================================================
//  Inline assembly
// ===================================================================
// The inline-`__asm` island: from its WAT body and the signature its call settled on to instructions, over the representations above. Only the
// SPELLING and the type answers are per language (what a declared type lowers to, what a `TYPEINDEX` operand names).

// An island, prepared once: a `$T`-switched body's numeric type IS its signature, so the two shapes are distinct types.
type PreparedAsm =
	| { switched: true;		render(args: (Type | undefined)[], ctx: FunctionContext): Inline }
	| { switched: false;	render(args: (Type | undefined)[], ctx: FunctionContext, sig: ClosureSig, typeIndex: (text: string)=> number | undefined): Inline };


function assertFlatInstrs(instrs: WAT.WatInstr[], asm: string): wasm.Instr[] {
	return instrs.map(i => {
		if (i.op === '__switch')
			throw `inline asm '${asm}': switch '${i.key}' is unresolved -- not a ctx.defines entry, and inline asm has no enclosing macro call to bind it to a $tag argument`;
		if (i.op === '__local')
			throw `inline asm '${asm}': local '${i.id}' should already have been hoisted into a separate locals list`;
		// A `$T.<suffix>` reference with no enclosing `(switch $T ...)` is an authoring error.
		if (i.op === 'local.get' && typeof i.localIndex === 'string' && i.localIndex.startsWith('$T.'))
			throw `inline asm '${asm}': '${i.localIndex}' needs an enclosing '(switch $T ...)' declaring which types it's for`;
		return i;
	});
}

// Resolves named scratch locals to real local indices via ctx.local
function resolveAsmLocals(instrs: wasm.Instr[], locals: WAT.WatLocal[], ctx: FunctionContext, asm: string): wasm.Instr[] {
	const indices = new Map(locals.map(l => {
		if (!l.id)
			throw `inline asm '${asm}': an anonymous local can't be referenced by name`;
		if (l.type === 'i32' || l.type === 'i64' || l.type === 'f32' || l.type === 'f64')
			return [l.id, ctx.temp(l.id, l.type)];
		throw `inline asm '${asm}': unsupported local type '${typeof l.type === 'string' ? l.type : 'ref'}'`;
	}));
	return instrs.map(i => {
		if ('localIndex' in i && typeof i.localIndex === 'string') {
			const index = indices.get(i.localIndex);
			if (index === undefined)
				throw `inline asm '${asm}': undeclared local '${i.localIndex}'`;
			return { ...i, localIndex: index };
		}
		return i;
	});
}

// A `TYPEINDEX("T[]")` operand, resolved after parsing (the assembler carries the text through; only the language can say what it names).
// Every field a type index lands in, `array.copy`'s `dst`/`src` included; narrowed with `in` before each spread, as `resolveAsmLocals`.
function resolveTypeExprs(instrs: wasm.Instr[], resolveIndex: (text: string) => number | undefined): wasm.Instr[] {
	const resolve = (v: unknown): number | undefined =>
		typeof v === 'string' && v.startsWith(WAT.TYPE_EXPR) ? resolveIndex(v.slice(WAT.TYPE_EXPR.length)) : undefined;
	return instrs.map(i => {
		if ('typeIndex' in i) {
			const r = resolve(i.typeIndex);
			if (r !== undefined)
				return { ...i, typeIndex: r };
		}
		if ('dst' in i && 'src' in i) {
			const d = resolve(i.dst), sr = resolve(i.src);
			if (d !== undefined || sr !== undefined)
				return { ...i, dst: d ?? i.dst, src: sr ?? i.src };
		}
		return i;
	});
}

// The three shapes an asm body takes: a generic body resolved per call (its operands follow the type arguments), a `$T` body whose signature is
// the numeric type its arguments agree on, and anything else resolved once.
export function makeAsm(asm: string, defines: Record<string, string | number> | undefined, paramCount: number, generic = false): PreparedAsm {
	const parsed = WAT.parseAsmBody(asm, defines);

	if (generic) {
		const body		= assertFlatInstrs(parsed.body, asm);
		const locals	= parsed.locals.map(l => ({ id: l.id, count: l.count, type: l.type as wasm.ValType }));
		return {
			switched: false,
			render: (_args, ctx, decl, typeIndex) => ({
				params:	decl.params,
				result:	decl.result,
				inline:	resolveAsmLocals(resolveTypeExprs(body, typeIndex), locals, ctx, asm)
			})
		};
	}

	const sw = parsed.body.find((i): i is WAT.SwitchPlaceholder => i.op === '__switch' && i.key === '$T');
	if (sw) {
		// The numeric types in "widen to me first" order where an operand's own type has no instruction: f64 first, since widening up to it is exact.
		const NUMERIC_TYPES = ['f64', 'f32', 'i64', 'i32'] as const;
		type NumericType = typeof NUMERIC_TYPES[number];
		function isNumericType(t: Type | undefined): t is NumericType { return NUMERIC_TYPES.includes(t as NumericType); }
		// One numeric type's expansion of a `$T`-switch body.
		type TypeSwitchVariants = Partial<Record<NumericType, { locals: WAT.WatLocal[]; body: wasm.Instr[] }>>;

		// A `$T`-keyed switch, expanded once per numeric type its arms declare; an arm may declare further `$T` locals and references, so a winning arm
		// is processed by recursing as if it were the whole body.
		const variants: TypeSwitchVariants = {};

		for (const type of new Set(sw.arms.flatMap(a => a.values).filter(a => typeof a === 'string').map(a => a.slice(1) as NumericType))) {
			const locals:	WAT.WatLocal[] = [];
			const body:		WAT.WatInstr[] = [];

			const addLocals = (ls: WAT.WatLocal[]) => locals.push(...ls.map(l => ({
				id:		l.id,
				count:	l.count,
				type:	typeof l.type === 'object' && 'typeParam' in l.type ? type : l.type,
			})));

			function process(items: WAT.WatInstr[]): boolean {
				for (const i of items) {
					if (i.op === '__local') {
						addLocals([i]);
					} else if (i.op === 'local.get' && typeof i.localIndex === 'string' && i.localIndex.startsWith('$T.')) {
						const oper = i.localIndex.slice(3);
						if (!(oper in I[type]))
							return false;
						body.push((I[type] as any)[oper]);
					} else if (i.op === '__switch' && i.key === '$T') {
						const arm = WAT.pickArm(i.arms, `$${type}`);
						if (!arm)
							return false;
						if (!process(arm.body))
							return false;
					} else {
						body.push(i);
					}
				}
				return true;
			}

			addLocals(parsed.locals);
			if (!process(parsed.body))
				throw `inline asm '${asm}': switch arm '(${sw.arms.find(a => a.values.includes(`$${type}`))!.values.join(' ')})' claims '${type}' but its own body doesn't resolve for it`;
			variants[type] = { locals, body: assertFlatInstrs(body, asm) };
		}
		if (!Object.keys(variants).length)
			throw `inline asm '${asm}': switch '$T' has no arms`;

		return {
			switched: true,
			render: (args, ctx) => {
				let t = args[0];
				if (!isNumericType(t) || !variants[t] || args.length !== paramCount || !args.every(a => a === t)) {
					t = NUMERIC_TYPES.find(nt => variants[nt]);
					if (!t)
						throw 'no numeric type supports this operation';
				}
				const chosen = variants[t]!;
				return { params: Array.from({ length: paramCount }, () => t), result: t, inline: resolveAsmLocals(chosen.body, chosen.locals, ctx, asm) };
			}
		};
	}

	const locals = parsed.locals.map(l => {
		if (typeof l.type === 'object' && 'typeParam' in l.type)
			throw `inline asm '${asm}': '(local ${l.id ?? ''} $${l.type.typeParam})' needs a '$T'-generic asm`;
		return { id: l.id, count: l.count, type: l.type };
	});
	const body = assertFlatInstrs(parsed.body, asm);
	return {
		switched: false,
		render: (_args, ctx, sig, _typeIndex) => ({
			params:	sig.params,
			result:	sig.result,
			inline:	resolveAsmLocals(body, locals, ctx, asm)
		})
	};
}
