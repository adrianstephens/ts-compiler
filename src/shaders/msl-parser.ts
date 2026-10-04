import * as path from 'path';
import { makeRule, Rules, termOneOf } from '@isopodlabs/tison';
import { makeCachedParser, siblingSource } from '@isopodlabs/tison/tableCache';
import { preprocess, PreprocessOptions } from '../cpp/preprocessor';
import { Module, Literal, stampPos } from '@isopodlabs/tison/ast';
import * as C from '../cpp/c-parser';
import * as CPP from '../cpp/cpp-parser';

// ===================================================================
//  MSL Parser -- an extension of cpp-parser
// ===================================================================
//
// Extends cpp-parser.ts (itself an extension of c-parser.ts) toward Metal Shading Language, which is a
// C++14 subset. Because MSL *is* C++-shaped, almost everything is cpp's: classes, templates, namespaces,
// `using namespace metal;`, references, `auto`, lambda-free device code. The additions are Metal's
// address-space and function qualifiers (`device`, `constant`, `thread`, `threadgroup`, `vertex`,
// `fragment`, `kernel`), its vector/matrix/texture/sampler type names, and qualified names used as
// values/types (`access::read`, `mem_flags::mem_threadgroup`, `metal::float4`).
//
// `[[...]]` attributes (`[[buffer(0)]]`, `[[vertex_id]]`, `[[position]]`, `[[attribute(3)]]`) need no
// grammar at all: cpp-parser.ts's lexer already skips them, so `float4 pos [[attribute(0)]];` parses as
// `float4 pos ;` and `constant Params &p [[buffer(0)]]` as `constant Params &p`. They leave no AST trace
// (the same trade cpp-parser.ts makes for `[[nodiscard]]`).
//
// Known simplifications/omissions:
//   - `access::read`-style enums are accepted syntactically; no enum-value checking.
//   - Parses, but does not validate: address-space rules, `[[...]]` placement, stage-appropriate builtins.
//   - Load order: c-parser -> cpp-parser -> this file (see the GLSL parser's header note).
//
// `discard_fragment()` and every other Metal function need no grammar -- they are ordinary calls, which
// cpp-parser.ts already parses.

// ===================================================================
//  Qualifiers
// ===================================================================

// Address-space qualifiers (`device float*`, `constant Params&`, `threadgroup float tile[]`) and function
// (stage) qualifiers (`vertex float4 main0(...)`, `kernel void compute(...)`). One terminal, so longer
// spellings never tie with shorter ones. Base qualifiers (`const`, `static`, `volatile`, ...) are not repeated.
export const MSL_QUALIFIERS = [
	'device', 'constant', 'thread', 'threadgroup', 'ray_data', 'object_data',
	'vertex', 'fragment', 'kernel',
] as const;
export type MslQualifier = typeof MSL_QUALIFIERS[number];
export type QualifierFlags = Partial<Record<MslQualifier, true>>;

export type Expr			= CPP.Expr;
export type Declarator		= CPP.Declarator;
export type TypeSpecifier	= CPP.TypeSpecifier;
export type DeclarationSpec	= CPP.DeclarationSpec & QualifierFlags;
export type Definition		= CPP.Definition;

// ===================================================================
//  Builtin type names
// ===================================================================
//
// Registered as typedef-style type names (reusing the base's IDENT callback) so `texture2d<float>` and
// `array<T, N>` reach cpp-parser.ts's existing generic-type machinery.

const VECTOR_PREFIXES = ['half', 'float', 'int', 'uint', 'short', 'ushort', 'char', 'uchar', 'bool', 'long', 'ulong'];
const TEXTURE_TYPES = [
	'texture1d', 'texture1d_array', 'texture2d', 'texture2d_array', 'texture2d_ms', 'texture2d_ms_array',
	'texture3d', 'texturecube', 'texturecube_array', 'texture_buffer',
	'depth2d', 'depth2d_array', 'depth2d_ms', 'depth2d_ms_array', 'depthcube', 'depthcube_array',
	'threadgroup_imageblock',
];

export const MSL_BUILTIN_TYPES: readonly string[] = [
	// Scalars that are not already base terminals.
	'half', 'ushort', 'uchar', 'ulong', 'size_t', 'ptrdiff_t',
	// Vectors (`float3`, `half4`, ...) and their packed variants (`packed_float3`, ...).
	...VECTOR_PREFIXES.flatMap(p => [2, 3, 4].flatMap(n => [`${p}${n}`, `packed_${p}${n}`])),
	// Matrices (`float4x4`, `half2x3`, ...).
	...VECTOR_PREFIXES.flatMap(p => [2, 3, 4].flatMap(rows => [2, 3, 4].map(cols => `${p}${rows}x${cols}`))),
	...TEXTURE_TYPES,
	// Template heads and opaque handles.
	'vec', 'matrix', 'array', 'sampler', 'atomic', 'atomic_uint', 'atomic_int', 'atomic_bool',
];

// ===================================================================
//  Grammar
// ===================================================================

const Rule = makeRule<CPP.CppCtx>(stampPos);

// Metal's half-precision literal suffix (`1.0h`, `1h`) -- c-parser.ts's FLOAT_LITERAL only knows `f`/`l`.
// Longer match than FLOAT_LITERAL's `1.0`, so it wins wherever the `h` is present; the base literal is used
// unchanged everywhere else.
const HALF_LITERAL = /[0-9]+(?:\.[0-9]*)?(?:[eE][-+]?[0-9]+)?[hH]/;
(C.primary_expression as unknown as Rules<Expr>).push(
	Rule([HALF_LITERAL], $ => Literal(parseFloat($[0]), $[0]) as Expr),
);

const specifier_qualifier_list = C.specifier_qualifier_list as unknown as Rules<DeclarationSpec>;
specifier_qualifier_list.push(
	// Leading address-space/stage qualifiers (`constant float4* p`, `vertex float4 main()`).
	Rule([termOneOf(MSL_QUALIFIERS), specifier_qualifier_list], $ => ({ ...$[1], [$[0]]: true })),
	// A qualified name whose tail is *not* a registered type -- MSL's `access::read`, `mem_flags::...` in a
	// template argument (`texture2d<float, access::read>`). cpp-parser.ts has the TYPE_NAME-tail form only;
	// this mirrors it for the IDENT tail. cpp-parser.ts's `scope_prefix` is reused, not copied.
	Rule([CPP.scope_prefix, C.IDENT],	$ => ({ type: { type: 'qualified_type', parts: [...$[0], $[1]] } })),
);

// Qualified names as *values* (`mem_flags::mem_threadgroup`, `metal::float4`), which cpp-parser.ts only
// reaches inside template arguments. `TYPE_SCOPE` is produced by the lexer for any `name::`, so this can
// only fire where the source really has `::` -- no competition with ordinary identifiers.
(C.primary_expression as unknown as Rules<Expr>).push(
	Rule([CPP.scope_prefix, C.IDENT],		$ => ({ type: 'qualified', parts: [...$[0], $[1]] } as Expr)),
	Rule([CPP.scope_prefix, C.TYPE_NAME],	$ => ({ type: 'qualified', parts: [...$[0], $[1]] } as Expr)),
);

// ===================================================================
//  Wire it up
// ===================================================================

const translation_unit = C.translation_unit as unknown as Rules<Module<Definition>>;

export const parser = makeCachedParser({
	skip: [...CPP.skip],
	terminals: [C.IDENT, CPP.TYPE_SCOPE, CPP.TEMPLATE_FN, CPP.RIGHT_SHIFT, CPP.RIGHT_SHIFT_ASSIGN],
	precedence: C.PREC,
	start: translation_unit,
	rules: { translation_unit },
}, {
	forkCtx: (ctx: CPP.CppCtx) => ({ ...ctx, typedefNames: new Set(ctx.typedefNames) }),
}, {
	// an MSL production is pushed onto C's *and* cpp's rules, so an edit to any has to invalidate this cache
	sources:	[__filename, siblingSource(__filename, 'c-parser'), siblingSource(__filename, 'cpp-parser')],
	cachePath:	path.join(__dirname, '../../.tables-cache/msl-parser.tables'),
});

export interface Options extends PreprocessOptions {
	// Extra names to treat as types before parsing (a struct from an unresolved include, a typedef, ...).
	knownTypes?: Iterable<string>;
}

export const mslParser = {
	...parser,
	parse: async (code: string, options?: Options) => {
		return parser.parse(await preprocess(code, options), {
			pendingTypedef: false,
			typedefNames: new Set<string>([...MSL_BUILTIN_TYPES, ...(options?.knownTypes ?? [])]),
			templateDepth: 0,
		});
	}
};
