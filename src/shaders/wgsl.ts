import * as C from '../cpp/c-parser';
import * as GLSL from './glsl-parser';
import type * as Common from '@isopodlabs/tison/ast';
import { Module, Literal, Identifier, Call, ExprStmt, Return, Block } from '@isopodlabs/tison/ast';

// ===================================================================
//  WGSL emitter -- GLSL ES 3.00 AST -> WGSL source
// ===================================================================
//
// WGSL is an OUTPUT-ONLY target here: an AST retag plus a printer, not a parser. It shares nothing with the
// C-family parser layer except the `Module<Definition>` it is handed -- see `glsl-parser.ts`'s header for why
// folding a WGSL *parser* into the C grammar would have nothing to inherit.
//
// Four WGSL rules drive every decision below, because GLSL has no analogue for any of them:
//
//   * NO LOOSE UNIFORMS. GLSL's `uniform vec2 u_size;` is one binding per name. WGSL has no module-scope
//     uniform scalar/vector of its own -- its `var<uniform>` must hold a struct -- so every loose uniform is
//     folded into ONE `Uniforms` struct and each use site rewrites `u_size` -> `u.u_size`.
//   * NO IMPLICIT CONVERSION. WGSL will not widen `i32` to `f32`, mix them in an operator, or take a scalar
//     where a vector is wanted, so each operand's type is needed to insert `f32(...)` and splat scalars.
//     That is what `infer` exists for.
//   * NO TERNARY. `?:` becomes `select(f, t, cond)` -- argument order reversed.
//   * NO PREPROCESSOR. `#version`/`precision` are dropped; the caller is expected to have spliced `//@lib`
//     fragments already (those partial files are not standalone shaders).
//
// Inference is deliberately partial: it covers the constructors, operators and builtins these shaders use, and
// throws a NAMED error for anything it cannot type. Guessing a type here emits WGSL that fails to compile, so
// silence would be strictly worse than a loud failure.

// ===================================================================
//  WGSL types
// ===================================================================

type VecSize = 2 | 3 | 4;
type Scalar = 'bool' | 'i32' | 'u32' | 'f32' | 'f16';

export type WgslType =
	| { kind: 'scalar'; scalar: Scalar }
	| { kind: 'vec'; size: VecSize; scalar: Scalar }
	| { kind: 'mat'; cols: VecSize; rows: VecSize; scalar: Scalar }
	| { kind: 'array'; element: WgslType; count?: number }
	| { kind: 'atomic'; to: WgslType }
	| { kind: 'sampler' }
	| { kind: 'texture'; dim: string; sampled: Scalar | 'depth'; arrayed?: boolean }
	| { kind: 'named'; name: string }
	| { kind: 'void' };

const scalarT	= (scalar: Scalar): WgslType => ({ kind: 'scalar', scalar });
const vecT		= (size: VecSize, scalar: Scalar): WgslType => ({ kind: 'vec', size, scalar });
const namedT	= (name: string): WgslType => ({ kind: 'named', name });
const VOID: WgslType = { kind: 'void' };

export function typeText(t: WgslType): string {
	switch (t.kind) {
		case 'scalar':	return t.scalar;
		case 'vec':		return `vec${t.size}<${t.scalar}>`;
		case 'mat':		return `mat${t.cols}x${t.rows}<${t.scalar}>`;
		case 'array':	return `array<${typeText(t.element)}${t.count === undefined ? '' : `, ${t.count}`}>`;
		case 'atomic':	return `atomic<${typeText(t.to)}>`;
		case 'sampler':	return 'sampler';
		// Depth textures are `texture_depth_*` in WGSL; `sampled: 'depth'` is the marker for that.
		case 'texture':	return t.sampled === 'depth' ? `texture_depth_${t.arrayed ? '2d_array' : '2d'}` : `${t.dim}${t.arrayed ? '_array' : ''}<${t.sampled}>`;
		case 'named':	return t.name;
		case 'void':	return 'void';
	}
}

const typeKey	= (t: WgslType): string => typeText(t);
const sameType	= (a: WgslType, b: WgslType): boolean => typeKey(a) === typeKey(b);
const scalarOf	= (t: WgslType): Scalar | undefined => t.kind === 'scalar' ? t.scalar : t.kind === 'vec' ? t.scalar : undefined;
const isNumeric	= (t: WgslType): boolean => t.kind === 'scalar' ? t.scalar !== 'bool' : t.kind === 'vec' ? t.scalar !== 'bool' : false;

// ===================================================================
//  GLSL type names -> WGSL types
// ===================================================================

const SCALARS: Record<string, WgslType> = {
	'void':			VOID,
	'bool':			scalarT('bool'),
	'int':			scalarT('i32'),
	'uint':			scalarT('u32'),
	'float':		scalarT('f32'),
	'double':		scalarT('f32'),
	'atomic_uint':	{ kind: 'atomic', to: scalarT('u32') },
};

const VEC_PREFIX: Record<string, Scalar> = { '': 'f32', 'd': 'f32', 'i': 'i32', 'u': 'u32', 'b': 'bool' };

function textureDim(name: string, arrayed: boolean): string {
	switch (name) {
		case '1D':			return 'texture_1d';
		case '2D':			return 'texture_2d';
		case '3D':			return 'texture_3d';
		case 'Cube':		return 'texture_cube';
		case '2DArray':		return 'texture_2d';
		case 'CubeArray':	return 'texture_cube';
		case '2DMS':		return 'texture_multisampled_2d';
		default:			throw new Error(`wgsl: no WGSL sampler for '${name}'${arrayed ? ' arrayed' : ''}`);
	}
}

/** Resolve a GLSL type spelling to a WGSL type, or undefined if it names no builtin (a user struct, say). */
export function glslType(name: string, arraySize?: number): WgslType | undefined {
	let base: WgslType | undefined;
	if (name in SCALARS) {
		base = SCALARS[name];
	} else {
		const vec = /^([diub]?)vec([234])$/.exec(name);
		if (vec) {
			base = vecT(Number(vec[2]) as VecSize, VEC_PREFIX[vec[1]!]!);
		} else {
			const mat = /^d?mat([234])(?:x([234]))?$/.exec(name);
			if (mat) {
				const cols = Number(mat[1]) as VecSize;
				base = { kind: 'mat', cols, rows: (mat[2] ? Number(mat[2]) : cols) as VecSize, scalar: 'f32' };
			} else {
				const shadow = /^sampler([123]D|Cube|2DArray|CubeArray|2DMS)Shadow$/.exec(name);
				if (shadow) {
					base = { kind: 'texture', dim: textureDim(shadow[1]!, /Array$/.test(shadow[1]!)), sampled: 'depth', arrayed: /Array$/.test(shadow[1]!) };
				} else {
					const samp = /^([iu]?)sampler([123]D|Cube|2DArray|CubeArray|2DMS)?$/.exec(name);
					if (samp) {
						const dim = samp[2] ?? '2D';
						const sampled: Scalar = samp[1] === 'i' ? 'i32' : samp[1] === 'u' ? 'u32' : 'f32';
						base = { kind: 'texture', dim: textureDim(dim, /Array$/.test(dim)), sampled, arrayed: /Array$/.test(dim) };
					}
				}
			}
		}
	}
	if (!base)
		return undefined;
	return arraySize === undefined ? base : { kind: 'array', element: base, count: arraySize };
}

// ===================================================================
//  Builtins
// ===================================================================
//
// `ret` derives the result from the argument types. `vectorArgs` names the argument positions that WGSL
// requires to be VECTORS where GLSL accepts the component type: `pow(vec2, float)` is illegal in WGSL
// (`pow(vec2<f32>, vec2<f32>)` is the only overload), so the scalar is splatted to the vector size.
// `splatTo` picks which argument supplies that size.

interface WgslArg { text: string; type: WgslType; }

interface Builtin {
	ret:			(args: WgslType[]) => WgslType;
	name?:			string;
	/** Argument positions that must match the size of the vector argument at `splatTo`. */
	vectorArgs?:	number[];
	splatTo?:		number;
	/** Texture builtins: argument 0 is the combined GLSL sampler, argument 1 the coords. */
	sample?:		'texture' | 'texelFetch' | 'textureLod';
}

const A0		= (a: WgslType[]): WgslType => a[0]!;
const floatOf	= (a: WgslType[]): WgslType => scalarT(scalarOf(a[0]!) ?? 'f32');
const boolOf	= (a: WgslType[]): WgslType => {
	const t = a[0]!;
	return t.kind === 'vec' ? vecT(t.size, 'bool') : scalarT('bool');
};

// Componentwise unary maths: result is the argument type, no splatting needed.
const SAME: Builtin = { ret: A0 };
// Componentwise binary/ternary maths where a scalar operand must be widened to the vector's size.
const SPLAT: Builtin = { ret: A0, vectorArgs: [1, 2], splatTo: 0 };

const BUILTINS: Record<string, Builtin> = {
	radians: SAME, degrees: SAME, sin: SAME, cos: SAME, tan: SAME, asin: SAME, acos: SAME, atan: SAME,
	sinh: SAME, cosh: SAME, tanh: SAME, asinh: SAME, acosh: SAME, atanh: SAME,
	exp: SAME, log: SAME, exp2: SAME, log2: SAME, sqrt: SAME, inversesqrt: SAME,
	abs: SAME, sign: SAME, floor: SAME, trunc: SAME, round: SAME, fract: SAME, normalize: SAME,

	// `mod` has no WGSL equivalent; `pow` needs both operands the same shape.
	mod: 			{ ret: A0, vectorArgs: [1], splatTo: 0 },
	pow: 			{ ret: A0, vectorArgs: [1], splatTo: 0 },

	min: SPLAT, max: SPLAT, clamp: SPLAT, mix: SPLAT, step: SPLAT, smoothstep: SPLAT,

	length:			{ ret: floatOf },
	distance:		{ ret: floatOf },
	dot:			{ ret: floatOf },
	cross:			{ ret: A0 },
	faceforward:	SAME,
	reflect:		SAME,
	refract:		SAME,

	lessThan:		{ ret: boolOf },
	greaterThan:	{ ret: boolOf },
	lessThanEqual:	{ ret: boolOf },
	greaterThanEqual:{ ret: boolOf },
	equal:			{ ret: boolOf },
	notEqual:		{ ret: boolOf },
	not:			{ ret: boolOf },
	any:			{ ret: () => scalarT('bool') },
	all:			{ ret: () => scalarT('bool') },

	// GLSL's combined sampler splits into two WGSL bindings; `texture(s, uv)` -> `textureSample(t, s, uv)`.
	texture:		{ ret: () => vecT(4, 'f32'), sample: 'texture' },
	textureLod:		{ ret: () => vecT(4, 'f32'), sample: 'textureLod' },
	texelFetch:		{ ret: () => vecT(4, 'f32'), sample: 'texelFetch' },
	textureSize:	{ ret: () => vecT(2, 'i32') },

	dFdx: 			{ ret: A0, name: 'dpdx' },
	dFdy: 			{ ret: A0, name: 'dpdy' },
	fwidth:			SAME,
};

// ===================================================================
//  Emission context
// ===================================================================

interface Param		{ name: string; type: WgslType; }
interface StructInfo { name: string; members: { name: string; type: WgslType }[]; }
interface Uniform	{ name: string; type: WgslType; }
interface Resource	{ name: string; type: WgslType; sampler?: string; location?: number; }
interface Global	{ name: string; type: WgslType; constant: boolean; init?: string; arraySize?: number; initArgs?: string[]; isStructArray?: boolean; }

const INDENT = '\t';
const SWIZZLE = /^[xyzwrgbastpq]{1,4}$/;

// The concrete instantiation `glsl-parser.ts` produces. `C.Block` with its own defaults resolves to
// `Declarator<never, ParameterDecl, never>`, which is structurally different from what the GLSL parser
// actually builds, so every position has to be spelled with the real arguments.
type Body			= C.Block<GLSL.Declarator, GLSL.TypeSpecifierExt, GLSL.Expr, GLSL.Stmt>;
type Declaration	= C.Declaration<GLSL.Declarator, GLSL.TypeSpecifierExt, GLSL.Expr>;
type InitDecl		= C.InitDeclarator<GLSL.Declarator, GLSL.Expr>;
type Initializer	= C.Initializer<GLSL.Expr>;

export class GlslUnsupported extends Error {
	constructor(what: string) { super(`wgsl: ${what}`); }
}

export class WgslEmitter {
	private scope: Map<string, WgslType>[] = [new Map()];
	private structs		= new Map<string, StructInfo>();
	private functions	= new Map<string, { name: string; ret: WgslType; params: Param[]; body: Body }>();
	private uniforms 	= [] as Uniform[];
	private resources	= new Map<string, Resource>();
	private globals 	= [] as Global[];
	private entry?: 	{ name: string; body: Body };
	private outputVars	= [] as string[];
	private inputs		= [] as { name: string; type: WgslType; location: number }[];
	private colorOut?:	string;
	private usesFragCoord	= false;
	private usesVertexIndex	= false;
	private readonly stage: 'vertex' | 'fragment';
	/** Nesting depth inside a function body, so a block-scope shadow is popped correctly. */
	private depth = 0;
	constructor(private readonly definitions: readonly GLSL.Definition[], stage: 'vertex' | 'fragment') {
		this.stage = stage;
	}

	// --- symbol lookup ---

	private lookup(name: string): WgslType | undefined {
		for (let i = this.scope.length - 1; i >= 0; i--) {
			const hit = this.scope[i]!.get(name);
			if (hit)
				return hit;
		}
		return undefined;
	}
	private declareHere(name: string, type: WgslType) { this.scope[this.scope.length - 1]!.set(name, type); }

	// --- pass 1: collect ---

	private collect() {
		for (const def of this.definitions) {
			if (def.type === 'function_def') {
				const fnDecl	= def.declarator as C.FunctionDecl<GLSL.Declarator>;
				const name		= (fnDecl.name as Identifier).name;
				const params	= fnDecl.params.map((p, i) => ({
					name: p.declarator ? this.declaratorName(p.declarator) : `arg${i}`,
					type: this.specifierType(p.specifiers),
				}));
				const info = { name, ret: this.specifierType(def.specifiers), params, body: def.body as Body };
				this.functions.set(name, info);
				if (this.isEntryCandidate(name))
					this.entry ??= { name, body: def.body as Body };
				continue;
			}
			if (def.type === 'declaration') {
				this.registerStruct(def.specifiers.type);
				this.collectDeclaration(def);
				continue;
			}
			// `precision`/`layout_decl`/`qualifier_decl` carry no runtime meaning in WGSL.
			if (def.type === 'precision' || def.type === 'layout_decl' || def.type === 'qualifier_decl')
				continue;
			throw new GlslUnsupported(`unsupported top-level '${(def as { type: string }).type}'`);
		}
	}

	/**
	 * A `struct S { ... };` is reached through `specifier_qualifier_list`, not as a definition of its own, so
	 * its members are registered here, in declaration order. These shaders declare every struct before its
	 * first use, which is what makes a single in-order pass sufficient.
	 */
	private registerStruct(spec: GLSL.TypeSpecifier) {
		if (spec.type !== 'struct')
			return;
		if (!spec.name || this.structs.has(spec.name))
			return;
		const members = (spec.body ?? []).flatMap(m => m.declarators.map(d => ({
			name: this.declaratorName(d as C.StructDeclarator),
			type: this.specifierType(m.specifiers, this.arrayCount(d as C.StructDeclarator)),
		})));
		this.structs.set(spec.name, { name: spec.name, members });
		this.scope[0]!.set(spec.name, namedT(spec.name));
	}

	/** `main` is the entry point in every one of these shaders; an explicit stage pair is accepted too. */
	private isEntryCandidate(name: string): boolean {
		return name === 'main';
	}

	private collectDeclaration(def: Declaration) {
		const spec = def.specifiers as GLSL.DeclarationSpec;
		for (const d of def.initDeclarators ?? []) {
			const name		= this.declaratorName(d);
			const arraySize = this.arrayCount(d);
			const type		= this.specifierType(spec, arraySize);

			if (spec['uniform']) {
				if (type.kind === 'texture') {
					this.resources.set(name, { name, type, sampler: `s_${name}` });
				} else {
					this.uniforms.push({ name, type });
					this.scope[0]!.set(name, type);		// uses rewrite to `u.<name>`
				}

			} else if (spec['in']) {
				// A vertex input is a parameter of the entry point, not a module-scope resource; a fragment
				// `in` is an interpolant, which these shaders only read via `gl_FragCoord`.
				if (this.stage === 'vertex')
					this.inputs.push({ name, type, location: this.nextLocation() });
				this.scope[0]!.set(name, type);

			} else if (spec['out']) {
				this.resources.set(name, { name, type, location: this.nextLocation() });
				this.scope[0]!.set(name, type);
				if (name !== 'gl_FragColor' && name !== 'gl_FragData')
					this.outputVars.push(name);

			} else {
				// Module-scope value: `const` stays `const`, a mutable one becomes `var<private>`.
				const constant = !!spec['const'];
				const init = d && typeof d === 'object' && 'initializer' in d ? d.initializer : undefined;
				const g: Global = { name, type, constant };
				if (init) {
					if (init.type === 'initializer_list') {
						g.initArgs = init.elements.map(i => this.expression(i as GLSL.Expr));
					} else {
						g.init = this.expression(init);
					}
				}
				this.globals.push(g);
				this.scope[0]!.set(name, type);
			}
		}
	}

	private locationCounter = 0;
	private nextLocation(): number { return this.locationCounter++; }

	private declaratorName(d: InitDecl | C.Declarator | C.StructDeclarator | { declarator: C.Declarator }): string {
		const decl = (d && typeof d === 'object' && 'declarator' in d && !('type' in d)) ? (d as { declarator: C.Declarator }).declarator : d as C.Declarator;
		return C.declaratorName(decl);
	}

	/** The `[N]` on a declarator, if any (GLSL ES 3.00 array declarations). */
	private arrayCount(d: unknown): number | undefined {
		const decl = (d && typeof d === 'object' && 'declarator' in d && !('type' in d)) ? (d as { declarator: C.Declarator }).declarator : d as C.Declarator;
		if (decl && typeof decl === 'object' && decl.type === 'array') {
			const size = (decl as C.ArrayDecl<C.Declarator>).size;
			if (size && size.type === 'literal' && typeof size.value === 'number')
				return size.value;
		}
		return undefined;
	}

	private specifierType(spec: GLSL.DeclSpec, arraySize?: number): WgslType {
		const t = spec.type;
		if (t.type !== 'ref')
			throw new GlslUnsupported(`type specifier '${t.type}'`);
		const builtin = glslType(t.name, arraySize);
		return builtin ?? (arraySize === undefined ? namedT(t.name) : { kind: 'array', element: namedT(t.name), count: arraySize });
	}

	// --- inference ---

	private infer(e: GLSL.Expr, expect?: WgslType): WgslType {
		switch (e.type) {
			case 'identifier': {
				if (e.name === 'gl_FragCoord')	{
					this.usesFragCoord = true;
					return vecT(4, 'f32');
				}
				if (e.name === 'gl_VertexID') {
					this.usesVertexIndex = true;
					return scalarT('i32');
				}
				if (e.name === 'gl_FrontFacing')
					return scalarT('bool');
				if (e.name === 'gl_Position')
					return vecT(4, 'f32');
				const hit = this.lookup(e.name);
				if (hit)
					return hit;
				throw new GlslUnsupported(`unknown identifier '${e.name}'`);
			}
			case 'literal': {
				if (typeof e.value === 'string')
					return scalarT('bool');		// `true`/`false` reach here as raw text
				return this.literalType(e.raw ?? String(e.value));
			}
			case 'unary': {
				const t = this.infer(e.operand, expect);
				return e.operator === '!' ? boolOf([t]) : t;
			}
			case 'unary_post':
				return this.infer(e.operand, expect);
			case 'binary': {
				switch (e.operator) {
					case '<': case '>': case '<=': case '>=': case '==': case '!=':
						this.infer(e.left, expect); this.infer(e.right, expect);
						return scalarT('bool');
					case '&&': case '||':
						return scalarT('bool');
					default: {
						const l = this.infer(e.left, expect);
						// A scalar operand adopts the vector/matrix shape of the other side.
						const r = this.infer(e.right, scalarOf(l) !== undefined || l.kind === 'mat' ? undefined : l);
						const lm = l.kind === 'mat' ? l : undefined;
						const rm = r.kind === 'mat' ? r : undefined;
						if (lm || rm) {
							const mat = lm ?? rm!;
							// matrix * matrix yields the shape of the pair; matrix * vector/scalar keeps the matrix's.
							if (lm && rm)
								return { kind: 'mat', cols: lm.cols, rows: rm.rows, scalar: lm.scalar };
							return mat;
						}
						return	l.kind === 'vec' ? l
							:	r.kind === 'vec' ? r
							:	l;
					}
				}
			}
			case 'conditional': {
				this.infer(e.test);
				const c = this.infer(e.consequent, expect);
				const a = this.infer(e.alternate, expect);
				if (!sameType(c, a))
					throw new GlslUnsupported(`ternary branches disagree: ${typeText(c)} vs ${typeText(a)}`);
				return c;
			}
			case 'assign': {
				const target = this.infer(e.target);
				this.infer(e.value, target);
				return target;
			}
			case 'index': {
				const base = this.infer(e.object);
				this.infer(e.index);
				return base.kind === 'array' ? base.element
					: base.kind === 'vec' || base.kind === 'mat' ? base
					: base;
			}
			case 'member': {
				const base = this.infer(e.object);
				return this.memberType(base, e.property);
			}
			case 'call':
				return this.callType(e);
			case 'functional_cast': {
				const t = glslType(e.target);
				if (!t)
					throw new GlslUnsupported(`constructor for unknown type '${e.target}'`);
				for (const a of e.arguments)
					this.infer(a, t);
				return t;
			}
			default:
				throw new GlslUnsupported(`unsupported expression '${(e as { type?: string }).type ?? '?'}'`);
		}
	}

	private memberType(base: WgslType, property: string): WgslType {
		if (base.kind === 'named') {
			const info		= this.structs.get(base.name);
			const member	= info?.members.find(m => m.name === property);
			if (!member)
				throw new GlslUnsupported(`no member '${property}' on '${base.name}'`);
			return member.type;
		}
		if (base.kind === 'vec') {
			// A single-character swizzle keeps the vector size of the selector (`.rgb` on a vec4 is a vec3).
			if (!SWIZZLE.test(property))
				throw new GlslUnsupported(`bad swizzle '.${property}'`);
			const n = property.length;
			if (n === 1)
				return scalarT(base.scalar);
			if (n !== 2 && n !== 3 && n !== 4)
				throw new GlslUnsupported(`bad swizzle length '.${property}'`);
			return vecT(n, base.scalar);
		}
		if (base.kind === 'mat') {
			if (!SWIZZLE.test(property) || property.length !== 1)
				throw new GlslUnsupported(`bad matrix swizzle '.${property}'`);
			return vecT(base.rows, base.scalar);
		}
		throw new GlslUnsupported(`member access on ${typeText(base)}`);
	}

	private literalType(raw: string): WgslType {
		if (/[uU]$/.test(raw))
			return scalarT('u32');
		if (/[fF]$/.test(raw))
			return scalarT('f32');
		if (/[.eE]/.test(raw))
			return scalarT('f32');
		return scalarT('i32');
	}

	private callType(e: Common.Call<GLSL.Expr>): WgslType {
		if (e.callee.type !== 'identifier')
			throw new GlslUnsupported('call through an expression');
		const name = e.callee.name;
		// A user function.
		const user = this.functions.get(name);
		if (user) {
			user.params.forEach((p, i) => { const a = e.arguments[i]; if (a) this.infer(a, p.type); });
			return user.ret;
		}
		// A constructor for a struct the shader declares.
		if (this.structs.has(name)) {
			for (const a of e.arguments)
				this.infer(a);
			return namedT(name);
		}
		const builtin = BUILTINS[name];
		if (!builtin) {
			const ctor = glslType(name);
			if (ctor)
				throw new GlslUnsupported(`constructor '${name}' must be written as a call to a declared type`);
			throw new GlslUnsupported(`unknown function '${name}'`);
		}
		const argTypes = e.arguments.map((a, i) => {
			const	splatTo	= builtin.vectorArgs?.includes(i) ? e.arguments[builtin.splatTo ?? 0] : undefined;
			const	wanted	= splatTo ? this.infer(splatTo) : undefined;
			return this.infer(a, wanted);
		});
		return builtin.ret(argTypes);
	}

	// --- emission: expressions ---

	/** Convert and emit `e`, coercing its type to `want` where the source language would have done so. */
	private expression(e: GLSL.Expr, want?: WgslType): string {
		return want ? this.coerce(e, want) : this.raw(e);
	}

	private coerce(e: GLSL.Expr, want: WgslType): string {
		const got = this.infer(e, want);
		if (sameType(got, want))
			return this.raw(e);
		// A scalar too small for a vector: splat it to the wanted size (`vec2<f32>(p)`).
		if (want.kind === 'vec' && got.kind === 'scalar' && got.scalar !== 'bool')
			return want.size === 4 ? this.raw(e) : `${typeText(want)}(${this.raw(e)})`;
		// A different concrete scalar/vector type: an explicit constructor, WGSL's only conversion.
		if ((want.kind === 'vec' && got.kind === 'vec' && want.size === got.size) || (want.kind === 'scalar' && got.kind === 'scalar'))
			return `${typeText(want)}(${this.raw(e)})`;
		if (want.kind === 'array' && got.kind === 'array')
			return this.raw(e);
		// A matrix/struct/vector widening the source already implied: leave it, WGSL's own overload will fail
		// loudly rather than us guessing.
		return this.raw(e);
	}

	private raw(e: GLSL.Expr): string {
		switch (e.type) {
			case'identifier': {
				if (e.name === 'gl_FragCoord') {
					this.usesFragCoord = true;
					return 'frag_coord';
				}
				if (e.name === 'gl_VertexID') {
					this.usesVertexIndex = true;
					return 'vertex_index';
				}
				if (e.name === 'gl_Position')
					return 'gl_Position';
				// A loose uniform lives inside the folded `Uniforms` struct.
				if (this.uniforms.some(u => u.name === e.name))
					return `u.${e.name}`;
				return e.name;
			}
			case 'literal': {
				if (typeof e.value === 'string')
					return e.value === 'true' || e.value === 'false' ? e.value : e.value;
				const raw = e.raw ?? String(e.value);
				if (/[uU]$/.test(raw))
					return raw;
				if (/[.eE]/.test(raw) || /[fF]$/.test(raw)) {
					// WGSL has no implicit float suffix, but an unsuffixed literal is AbstractFloat and adopts the
					// f32 context, so only an explicit `f` needs normalising away.
					return raw.replace(/[fF]$/, '');
				}
				return raw;
			}
			case 'unary': {
				const operand = this.raw(e.operand);
				return e.operator === 'sizeof' ? operand : `${e.operator}${this.operandParens(e.operand, operand)}`;
			}
			case 'unary_post':
				return `${this.operandParens(e.operand, this.raw(e.operand))}${e.operator}`;
			case 'binary': {
				const l = this.raw(e.left);
				// Only an f32-widening comparison/arithmetic needs the right operand coerced, so infer the left.
				const lt = this.infer(e.left);
				const rt = this.infer(e.right, isNumeric(lt) ? lt : undefined);
				const r = isNumeric(lt) && isNumeric(rt) && !sameType(lt, rt) ? this.coerce(e.right, lt) : this.raw(e.right);
				return `${this.operandParens(e.left, l, 11)} ${e.operator} ${this.operandParens(e.right, r, 12)}`;
			}
			case 'assign': {
				const target = this.raw(e.target);
				const want = this.infer(e.target);
				return `${target} ${e.operator ?? ''}= ${this.coerce(e.value, want)}`;
			}
			case 'conditional': {
				// `?:` -> `select(f, t, c)`: WGSL's argument order is (false, true, condition).
				const want = this.infer(e.consequent);
				return `select(${this.coerce(e.alternate, want)}, ${this.coerce(e.consequent, want)}, ${this.raw(e.test)})`;
			}
			case 'index':
				return `${this.raw(e.object)}[${this.raw(e.index)}]`;
			case 'member': {
				const base = this.raw(e.object);
				const lt = this.infer(e.object);
				if (lt.kind === 'vec' && e.property.length > 1)
					return `${base}.${e.property}`;
				return `${base}.${e.property}`;
			}
			case 'call':
				return this.callText(e);
			case 'functional_cast': {
				const t = glslType(e.target);
				if (!t)
					throw new GlslUnsupported(`constructor for unknown type '${e.target}'`);
				const args = e.arguments.map(a => this.coerce(a, t));
				return `${typeText(t)}(${args.join(', ')})`;
			}
			default:
				throw new GlslUnsupported(`unsupported expression '${(e as { type?: string }).type ?? '?'}'`);
		}
	}

	private operandParens(e: GLSL.Expr, text: string, minPrec = 13): string {
		const p = this.precedence(e);
		return p < minPrec ? `(${text})` : text;
	}

	private precedence(e: GLSL.Expr): number {
		switch (e.type) {
			case 'binary': {
				switch (e.operator) {
					case '||': return 4;
					case '&&': return 5;
					case '|': return 6;
					case '^': return 7;
					case '&': return 8;
					case '==': case '!=': return 9;
					case '<': case '>': case '<=': case '>=': return 10;
					case '<<': case '>>': return 11;
					case '+': case '-': return 12;
					default: return 13;
				}
			}
			case 'conditional':
				return 3;
			case 'assign':
				return 2;
			case 'unary': case 'unary_post':
				return 14;
			default:
				return 15;
		}
	}

	private callText(e: Common.Call<GLSL.Expr>): string {
		if (e.callee.type !== 'identifier')
			throw new GlslUnsupported('call through an expression');
		const name = e.callee.name;
		const builtin = BUILTINS[name];

		if (builtin?.sample) {
			const samplerArg = e.arguments[0]!;
			if (samplerArg.type !== 'identifier')
				throw new GlslUnsupported('sampling through a non-identifier sampler');
			const texName = samplerArg.name;
			const res = this.resources.get(texName);
			if (!res || res.type.kind !== 'texture')
				throw new GlslUnsupported(`'${texName}' is not a sampler uniform`);
			const samplerName = res.sampler!;
			const rest = e.arguments.slice(1).map(a => {
				const t = this.infer(a);
				// `texelFetch` takes an int coords vector, `texture`/`textureLod` take normalised floats.
				return builtin.sample === 'texelFetch' && t.kind === 'vec' && t.scalar === 'f32'
					? `${typeText(vecT(t.size, 'i32'))}(${this.raw(a)})`
					: this.raw(a);
			});
			const fnName = builtin.sample === 'texture' ? 'textureSample' : builtin.sample === 'textureLod' ? 'textureSampleLevel' : 'textureLoad';
			// `textureSampleLevel`'s explicit-LOD argument is already float; `textureLoad`'s is an integer level.
			return `${fnName}(${texName}, ${samplerName}${builtin.sample === 'texelFetch' ? '' : ', '}${rest.join(', ')})`;
		}

		if (builtin) {
			const argTypes = e.arguments.map(a => this.infer(a));
			const text = e.arguments.map((a, i) => {
				if (builtin.vectorArgs?.includes(i)) {
					const src = this.infer(e.arguments[builtin.splatTo ?? 0]!);
					return this.coerce(a, src);
				}
				return this.raw(a);
			});
			const fnName = builtin.name ?? name;
			return `${fnName}(${text.join(', ')})`;
		}

		const user = this.functions.get(name);
		if (user) {
			const text = e.arguments.map((a, i) => user.params[i] ? this.coerce(a, user.params[i]!.type) : this.raw(a));
			return `${name}(${text.join(', ')})`;
		}
		if (this.structs.has(name)) {
			const args = e.arguments.map(a => this.raw(a));
			return `${name}(${args.join(', ')})`;
		}
		// A bare type name used as a constructor (`vec3(x)`) reaches `primary_expression` as a `functional_cast`,
		// so anything left here is genuinely unknown.
		throw new GlslUnsupported(`unknown function '${name}'`);
	}

	// --- emission: statements ---

	private statements(stmts: readonly GLSL.Stmt[]): string {
		return stmts.map(s => this.indentLine(this.statement(s))).join('\n');
	}

	private statement(s: GLSL.Stmt): string {
		switch (s.type) {
			case 'expression': {
				// A fragment colour output is the entry point's return value, so the assignment that writes it
				// becomes a `return`. Only inside the entry point (`colorOut` is set for its body alone).
				const ex = s.expression;
				if (this.colorOut && ex.type === 'assign' && ex.target.type === 'identifier' && ex.target.name === this.colorOut)
					return `return ${this.expression(ex.value, vecT(4, 'f32'))};`;
				return `${this.expression(ex)};`;
			}
			case 'declaration':	return this.localDeclaration(s);
			case 'block': {
				this.scope.push(new Map());
				const inner = this.statements(s.body);
				this.scope.pop();
				return `{\n${inner}\n}`;
			}
			case 'if': {
				const cons = this.branch(s.consequent);
				if (!s.alternate)
					return `if ${this.condition(s.test)} ${cons}`;
				return `if ${this.condition(s.test)} ${cons} else ${this.branch(s.alternate)}`;
			}
			case 'while':
				return `while ${this.condition(s.test)} ${this.branch(s.body)}`;
			case 'for': {
				this.scope.push(new Map());
				const init = s.init
					? (s.init.type === 'declaration' ? this.forInitDecl(s.init as Declaration) : `${this.expression(s.init as GLSL.Expr)}`)
					: '';
				const test = s.test ? this.expression(s.test) : '';
				const update = s.update ? this.expression(s.update) : '';
				const body = this.branch(s.body);
				this.scope.pop();
				return `for (${init} ${test}; ${update}) ${body}`;
			}
			case 'return':	return s.argument ? `return ${this.expression(s.argument)};` : 'return;';
			case 'break':	return 'break;';
			case 'continue': return 'continue;';
			case 'discard':	return 'discard;';
			case 'empty':	return '';
			case 'do_while': throw new GlslUnsupported('do/while has no WGSL equivalent');
			case 'switch': throw new GlslUnsupported('switch is not yet emitted (WGSL has no fallthrough)');
			case 'goto': case 'labeled': throw new GlslUnsupported(`${s.type} has no WGSL equivalent`);
			default: throw new GlslUnsupported(`unsupported statement '${s.type}'`);
		}
	}

	private branch(s: GLSL.Stmt): string {
		if (s.type === 'block') {
			this.scope.push(new Map());
			const inner = this.statements(s.body);
			this.scope.pop();
			return `{\n${inner}\n}`;
		}
		return `{\n${this.indentLine(this.statement(s))}\n}`;
	}

	private condition(test: GLSL.Expr): string {
		const t = this.infer(test);
		if (t.kind === 'scalar' && t.scalar !== 'bool')
			throw new GlslUnsupported(`non-boolean condition of type ${typeText(t)}`);
		return this.raw(test);
	}

	private indentLine(text: string): string {
		return text.split('\n').map(l => INDENT + l).join('\n');
	}

	private localDeclaration(s: Declaration): string {
		const spec = s.specifiers as GLSL.DeclarationSpec;
		const parts: string[] = [];
		for (const d of s.initDeclarators ?? []) {
			const name = this.declaratorName(d);
			const arraySize = this.arrayCount(d);
			const type = this.specifierType(spec, arraySize);
			const init = d && typeof d === 'object' && 'initializer' in d ? d.initializer : undefined;
			// WGSL has no uninitialised locals; GLSL's uninitialised `int x;` defaults to zero, which is the
			// same default WGSL's `var` gives, so a bare `var` is faithful here.
			const kw = spec['const'] ? 'const' : 'var';
			this.declareHere(name, type);
			const initText = init ? ` = ${this.initializerText(init, type)}` : '';
			parts.push(`${kw} ${name} : ${typeText(type)}${initText};`);
		}
		return parts.join(' ');
	}

	private forInitDecl(s: Declaration): string {
		return this.localDeclaration(s).replace(/;\s*$/, ';');
	}

	private initializerText(init: Initializer, want: WgslType): string {
		if (init.type === 'initializer_list') {
			const element = want.kind === 'array' ? want.element : want;
			const args = init.elements.map(i => this.coerce(i as GLSL.Expr, element));
			return `${typeText(want)}(${args.join(', ')})`;
		}
		return this.expression(init, want);
	}

	// --- assembly ---

	build(): string {
		this.collect();
		const sections: string[] = [];
		const res = this.resourceDeclarations();
		if (res)
			sections.push(res);
		const glob = this.globalDeclarations();
		if (glob)
			sections.push(glob);
		const fns = this.functionDeclarations();
		if (fns)
			sections.push(fns);
		sections.push(this.entryPointText());
		return sections.join('\n\n') + '\n';
	}

	private resourceDeclarations(): string {
		const out: string[] = [];
		// Structs, in declaration order.
		for (const info of this.structs.values())
			out.push(`struct ${info.name} {\n${info.members.map(m => `${INDENT}${m.name} : ${typeText(m.type)},`).join('\n')}\n}`);
		let binding = 0;
		for (const r of this.resources.values()) {
			out.push(`@group(0) @binding(${binding++}) var ${r.name} : ${typeText(r.type)};`);
			// Every sampled texture needs a companion sampler: GLSL's combined sampler is two WGSL bindings.
			if (r.sampler)
				out.push(`@group(0) @binding(${binding++}) var ${r.sampler} : sampler;`);
		}
		if (this.uniforms.length) {
			out.push(`struct Uniforms {\n${this.uniforms.map(u => `${INDENT}${u.name} : ${typeText(u.type)},`).join('\n')}\n}`);
			out.push(`@group(0) @binding(${binding++}) var<uniform> u : Uniforms;`);
		}
		for (const r of this.resources.values())
			if (r.location !== undefined && this.outputVars.includes(r.name))
				out.push(`@location(${r.location}) var<private> ${r.name} : ${typeText(r.type)};`);
		return out.join('\n');
	}

	private globalDeclarations(): string {
		return this.globals.map(g => {
			const init = g.init ? ` = ${g.init}` : g.initArgs ? ` = ${typeText(g.type)}(${g.initArgs.join(', ')})` : '';
			return g.constant
				? `const ${g.name} : ${typeText(g.type)}${init};`
				: `var<private> ${g.name} : ${typeText(g.type)}${init};`;
		}).join('\n');
	}

	private functionDeclarations(): string {
		const out: string[] = [];
		for (const fn of this.functions.values()) {
			if (fn.name === this.entry?.name)
				continue;
			out.push(this.functionText(fn.name, fn.ret, fn.params, () => this.statements(fn.body.body)));
		}
		return out.join('\n\n');
	}

	private functionText(name: string, ret: WgslType, params: Param[], body: () => string): string {
		this.scope.push(new Map());
		for (const p of params)
			this.declareHere(p.name, p.type);
		const bodyText = body();
		this.scope.pop();
		const retText = ret.kind === 'void' ? '' : ` -> ${typeText(ret)}`;
		return `fn ${name}(${params.map(p => `${p.name} : ${typeText(p.type)}`).join(', ')})${retText} {\n${bodyText}\n}`;
	}

	private entryPointText(): string {
		const entry = this.entry;
		if (!entry)
			throw new GlslUnsupported('no entry point (no main function)');
		const main = this.functions.get(entry.name)!;
		const attr = this.stage === 'vertex' ? '@vertex' : '@fragment';

		// A fragment colour output becomes the entry point's return value, so `fragColor = e;` is emitted as
		// `return e;` (`colorOut`). Any other `out` variable needs a result struct, which these shaders do not
		// use, so it is refused loudly rather than mis-emitted.
		const colorName = this.resources.has('fragColor') ? 'fragColor' : this.resources.has('gl_FragColor') ? 'gl_FragColor' : undefined;
		if (this.stage === 'fragment' && this.outputVars.length > (colorName ? 1 : 0))
			throw new GlslUnsupported('a fragment shader with outputs other than the colour needs a result struct');

		const params: string[] = [];
		if (this.usesFragCoord)
			params.push('@builtin(position) frag_coord : vec4<f32>');
		if (this.usesVertexIndex)
			params.push('@builtin(vertex_index) vertex_index : u32');
		if (this.stage === 'vertex')
			for (const i of this.inputs)
				params.push(`@location(${i.location}) ${i.name} : ${typeText(i.type)}`);

		this.scope.push(new Map());
		for (const p of this.functions.get(entry.name)!.params)
			this.declareHere(p.name, p.type);
		this.colorOut = colorName;
		let bodyText = this.statements(main.body.body);
		this.colorOut = undefined;
		this.scope.pop();

		if (this.stage === 'vertex') {
			// `gl_Position` is the position output. These shaders write it once, at the end, so it becomes a
			// local, assigned and returned -- WGSL has no predeclared variable to assign instead.
			bodyText = `${INDENT}var gl_Position : vec4<f32>;\n${bodyText}\n${INDENT}return gl_Position;`;
		}
		const ret = this.stage === 'vertex' ? ' -> @builtin(position) vec4<f32>' : colorName ? ' -> @location(0) vec4<f32>' : '';
		return `${attr}\nfn ${main.name}(${params.join(', ')})${ret} {\n${bodyText}\n}`;
	}
}

export function glslToWgsl(definitions: readonly GLSL.Definition[], stage: 'vertex' | 'fragment'): string {
	return new WgslEmitter(definitions, stage).build();
}
