import * as path from 'path';
import { makeRule, Rules, List, termOneOf, removeRules } from '@isopodlabs/tison';
import { makeCachedParser, siblingSource } from '@isopodlabs/tison/tableCache';
import { preprocess, PreprocessOptions } from '../cpp/preprocessor';
import { Module, Identifier, stampPos } from '@isopodlabs/tison/ast';
import * as C from '../cpp/c-parser';
import * as CPP from '../cpp/cpp-parser';

// ===================================================================
//  HLSL Parser -- an extension of cpp-parser
// ===================================================================
//
// Extends cpp-parser.ts (itself an extension of c-parser.ts) toward HLSL, the DirectX shader language.
// HLSL is C++-shaped, so cpp's class/template/namespace/typedef machinery is reused wholesale; the
// additions are its type names, its storage/interpolation qualifiers, resource/semantic annotations
// (`: SV_Target`, `: register(b0)`), `cbuffer`/`tbuffer` blocks, `[...]` attributes and `discard`.
//
// Cg and Slang are HLSL-family and ride this grammar for their shader-language core: Cg's `technique`/
// `pass`/`sampler_state` FX syntax and Slang's `interface`/`associatedtype` extensions are NOT included
// (the standalone, own-AST `src/cg/grammar.ts` parses full Cg FX; if those move onto this base they want
// their own extension files).
//
// Known simplifications/omissions:
//   - `interface IFoo { ... }` is not added; cpp's `class`/`struct` cover HLSL's class-shaped types.
//   - `[attributes]` are parsed on global functions/declarations only, not on statements.
//   - Parses, but does not validate: shader-model version rules, register-class/space rules, stage-appropriate
//     builtins, etc. are accepted syntactically. A front end, not a verifier.
//   - Because every extension mutates c-parser.ts's shared rule objects in place, load order matters:
//     c-parser -> cpp-parser -> this file (and this file last if MSL is also loaded). See the GLSL parser's
//     header note; the built base tables are unaffected either way.

// ===================================================================
//  Qualifiers
// ===================================================================

// One terminal per keyword set (a single terminal, so longer spellings never tie with shorter ones). All are
// HLSL reserved words; c-parser.ts's/cpp-parser.ts's own `const`/`volatile`/`static`/`extern`/`inline` are
// deliberately not repeated.
export const HLSL_QUALIFIERS = [
	'in', 'out', 'inout', 'uniform', 'precise', 'groupshared', 'shared',
	'row_major', 'column_major', 'snorm', 'unorm', 'nointerpolation', 'linear',
	'centroid', 'sample', 'noperspective', 'globallycoherent',
] as const;
export type HlslQualifier = typeof HLSL_QUALIFIERS[number];

// Same runtime convention as c-parser.ts's `const`/`volatile`: the qualifier's spelling becomes a `true` key.
export type QualifierFlags = Partial<Record<HlslQualifier, true>>;

// ===================================================================
//  AST types -- cpp's, plus HLSL's annotations and top-level forms
// ===================================================================

export type Expr			= CPP.Expr;
export type Declarator		= CPP.Declarator;
export type TypeSpecifier	= CPP.TypeSpecifier;
export type DeclarationSpec	= CPP.DeclarationSpec & QualifierFlags;

// A `:` annotation: a semantic (`SV_Target`, `POSITION`), a resource binding (`register(b0, space0)`) or a
// constant-buffer offset (`packoffset(c0.x)`).
export interface Semantic			{ type: 'semantic'; name: string }
export interface RegisterBinding	{ type: 'register'; parts: string[] }
export interface PackOffset			{ type: 'packoffset'; parts: string[] }
export type Annotation				= Semantic | RegisterBinding | PackOffset;

// An `[numthreads(8, 8, 1)]` / `[shader("vertex")]` attribute.
export interface Attribute			{ name: string; arguments?: Expr[] }

// c-parser.ts's `Initializer<X>` cannot be instantiated from here (cpp's `ExprAdditions` is private), so this
// two-line shape is restated against cpp's `Expr`.
export type Initializer				= Expr | { type: 'initializer_list'; elements: Initializer[] };

// A declarator that may carry an annotation and/or an initializer -- c-parser's `InitDeclarator` plus HLSL's
// `: SEMANTIC` and cpp's constructor-argument shape.
export interface AnnotatedInitDeclarator	{ declarator: Declarator; annotation?: Annotation; initializer?: Initializer; ctorArgs?: Expr[] }
export type InitDeclarator			= Declarator | AnnotatedInitDeclarator;

// A struct/cbuffer member: cpp's shapes plus `: SEMANTIC` (and arrays of them).
export type StructDeclarator		= CPP.StructDeclarator | { declarator: Declarator; annotation?: Annotation } | { name: string; annotation: Annotation };
export type StructMember			= C.StructMember<StructDeclarator, CPP.TypeSpecifierExt> & { modifiers?: CPP.MemberMod[] };

export type ParameterDecl			= CPP.ParameterDecl & { annotation?: Annotation };

export interface FunctionDef extends C.FunctionDef<Declarator, CPP.TypeSpecifierExt, Expr, Stmt> { annotation?: Annotation }

export interface CBufferDecl		{ type: 'cbuffer' | 'tbuffer'; name?: string; annotation?: Annotation; body: StructMember[] }
// An attribute-prefixed global (`[numthreads(8,8,1)] void main(...)`); a wrapper rather than a field on every
// definition shape, since cpp's top-level union is not ours to widen.
export interface AttributedDefinition	{ type: 'attributed'; attributes: Attribute[]; definition: Definition }

export type Stmt = CPP.Stmt | { type: 'discard' };
export type Definition = CPP.Definition<Stmt> | FunctionDef | CBufferDecl | AttributedDefinition;

// ===================================================================
//  Builtin type names
// ===================================================================
//
// Registered as typedef-style type names (reusing the base's IDENT callback) rather than as terminals, so
// `vector<float, 4>` and `ConstantBuffer<MyStruct>` reach cpp-parser.ts's existing generic-type machinery.
// The scalar keywords the base already has (`float`, `int`, `double`, `bool`, ...) stay terminals and are not
// repeated here.

const VECTOR_PREFIXES = ['float', 'half', 'double', 'int', 'uint', 'bool', 'min16float', 'min10float', 'min16int', 'min12int', 'min16uint'];

const TEXTURE_TYPES = [
	'Texture1D', 'Texture1DArray', 'Texture2D', 'Texture2DArray', 'Texture2DMS', 'Texture2DMSArray', 'Texture3D', 'TextureCube', 'TextureCubeArray',
	'RWTexture1D', 'RWTexture1DArray', 'RWTexture2D', 'RWTexture2DArray', 'RWTexture3D',
	'RasterizerOrderedTexture1D', 'RasterizerOrderedTexture1DArray', 'RasterizerOrderedTexture2D', 'RasterizerOrderedTexture2DArray', 'RasterizerOrderedTexture3D',
	'Buffer', 'RWBuffer', 'TextureBuffer', 'RWTextureBuffer', 'StructuredBuffer', 'RWStructuredBuffer', 'AppendStructuredBuffer', 'ConsumeStructuredBuffer',
	'ByteAddressBuffer', 'RWByteAddressBuffer', 'RasterizerOrderedBuffer', 'RasterizerOrderedByteAddressBuffer', 'ConstantBuffer',
	'SamplerState', 'SamplerComparisonState', 'sampler',
	'InputPatch', 'OutputPatch', 'PointStream', 'LineStream', 'TriangleStream',
	'RaytracingAccelerationStructure', 'RayQuery',
];

export const HLSL_BUILTIN_TYPES: readonly string[] = [
	// Scalars that are not already base terminals.
	'half', 'uint', 'dword', 'min16float', 'min10float', 'min16int', 'min12int', 'min16uint',
	// Vectors (`float2`...`float4`, `half3`, ...) and matrices (`float4x4`, `half2x3`, ...).
	...VECTOR_PREFIXES.flatMap(p => [1, 2, 3, 4].map(n => `${p}${n}`)),
	...VECTOR_PREFIXES.flatMap(p => [1, 2, 3, 4].flatMap(rows => [1, 2, 3, 4].map(cols => `${p}${rows}x${cols}`))),
	...TEXTURE_TYPES,
	'vector', 'matrix', 'array',
];

// ===================================================================
//  Grammar
// ===================================================================

const Rule = makeRule<CPP.CppCtx>(stampPos);

// Leading qualifiers (`uniform float4 x;`, `groupshared float tile[64];`), pushed onto c-parser.ts's
// specifier_qualifier_list exactly as cpp-parser.ts pushes its own leading `const`/`volatile` form.
const specifier_qualifier_list = C.specifier_qualifier_list as unknown as Rules<DeclarationSpec>;
specifier_qualifier_list.push(
	Rule([termOneOf(HLSL_QUALIFIERS), specifier_qualifier_list], $ => ({ ...$[1], [$[0]]: true })),
);

// --- annotations ---------------------------------------------------

const register_names = List(Rules<string>(Rule([C.IDENT], $ => $[0])), ',');
const annotation = Rules<Annotation>(
	Rule([C.IDENT],											$ => ({ type: 'semantic', name: $[0] })),
	Rule(['register', '(', register_names, ')'],			$ => ({ type: 'register', parts: $[2] })),
	Rule(['packoffset', '(', C.IDENT, ')'],					$ => ({ type: 'packoffset', parts: [$[2]] })),
	Rule(['packoffset', '(', C.IDENT, '.', C.IDENT, ')'],	$ => ({ type: 'packoffset', parts: [$[2], $[4]] })),
);

// --- struct members and cbuffer bodies -----------------------------

// HLSL has no bitfields, and a bitfield's shape (`name : constant_expression`) is exactly a semantic's
// (`name : IDENT`), so c-parser.ts's bitfield alternatives are removed before the annotated ones are added.
removeRules(C.struct_declarator, rhs => rhs[0] === ':' || (rhs.length === 3 && rhs[1] === ':'));

const array_suffix = Rules<C.Expr | undefined>(
	Rule(['[', C.constant_expression, ']'],		$ => $[1]),
	Rule(['[', ']'],							_ => undefined),
);
const array_suffixes = List(array_suffix);
const arrayOf = (element: Declarator, sizes: (C.Expr | undefined)[]): Declarator =>
	sizes.reduceRight<Declarator>((el, size) => C.ArrayDecl(el, size), element);

const struct_declarator = C.struct_declarator as unknown as Rules<StructDeclarator>;
for (const nameT of [C.IDENT, C.TYPE_NAME]) {
	struct_declarator.push(
		Rule([nameT, ':', annotation],				$ => ({ declarator: Identifier($[0]), annotation: $[2] })),
		Rule([nameT, array_suffixes, ':', annotation], $ => ({ declarator: arrayOf(Identifier($[0]), $[1]), annotation: $[3] })),
	);
}

// `cbuffer Name : register(b0) { ... }` / `tbuffer ...`.
const cbuffer_body = Rules<StructMember[]>(
	Rule(['{', '}'],						_ => []),
	Rule(['{', C.struct_body, '}'],			$ => $[1] as StructMember[]),
);
const cbuffer_decl = Rules<CBufferDecl>(
	Rule(['cbuffer', C.IDENT, cbuffer_body],					$ => ({ type: 'cbuffer', name: $[1], body: $[2] })),
	Rule(['cbuffer', C.IDENT, ':', annotation, cbuffer_body],	$ => ({ type: 'cbuffer', name: $[1], annotation: $[3], body: $[4] })),
	Rule(['cbuffer', cbuffer_body],								$ => ({ type: 'cbuffer', body: $[1] })),
	Rule(['tbuffer', C.IDENT, cbuffer_body],					$ => ({ type: 'tbuffer', name: $[1], body: $[2] })),
	Rule(['tbuffer', C.IDENT, ':', annotation, cbuffer_body],	$ => ({ type: 'tbuffer', name: $[1], annotation: $[3], body: $[4] })),
	Rule(['tbuffer', cbuffer_body],								$ => ({ type: 'tbuffer', body: $[1] })),
);

// --- declarations, parameters, functions ---------------------------

(C.parameter_declaration as unknown as Rules<ParameterDecl>).push(
	Rule([C.declaration_specifiers, C.declarator, ':', annotation],
		$ => ({ type: 'parameter', specifiers: $[0], declarator: $[1], annotation: $[3] } as unknown as ParameterDecl)),
);

(C.init_declarator as unknown as Rules<InitDeclarator>).push(
	Rule([C.declarator, ':', annotation],
		$ => ({ declarator: $[0], annotation: $[2] })),
	Rule([C.declarator, ':', annotation, '=', C.initializer],
		$ => ({ declarator: $[0], annotation: $[2], initializer: $[4] as Initializer })),
);

const external_definition = C.external_definition as unknown as Rules<Definition>;
external_definition.push(
	// Function return semantics (`float4 main(VSIn i) : SV_Target { ... }`); cpp-parser.ts's trailing-return
	// `->` form is a different token, so the two never compete.
	Rule([C.declaration_specifiers, C.declarator, ':', annotation, C.compound_statement],
		$ => ({ type: 'function_def', specifiers: $[0], declarator: $[1], annotation: $[3], body: $[4] } as unknown as FunctionDef)),
	Rule([cbuffer_decl, ';'], $ => $[0]),
);

// --- attributes ----------------------------------------------------

const attribute = Rules<Attribute>(
	Rule(['[', C.IDENT, ']'],								$ => ({ name: $[1] })),
	Rule(['[', C.IDENT, '(', C.argument_expression_list, ')', ']'],	$ => ({ name: $[1], arguments: $[3] })),
);
const attribute_list = List(attribute);
external_definition.push(
	Rule([attribute_list, C.function_definition],	$ => ({ type: 'attributed', attributes: $[0], definition: $[1] } as Definition)),
	Rule([attribute_list, C.declaration],			$ => ({ type: 'attributed', attributes: $[0], definition: $[1] } as Definition)),
);

// --- statements ----------------------------------------------------

(C.statement as unknown as Rules<Stmt>).push(
	Rule(['discard', ';'],	_ => ({ type: 'discard' })),
);

// ===================================================================
//  Wire it up
// ===================================================================

const translation_unit = C.translation_unit as unknown as Rules<Module<Definition>>;

export const parser = makeCachedParser({
	skip: [...CPP.skip],
	// IDENT must be lexed even where only TYPE_NAME is valid (the callback reclassifies registered names);
	// the rest keep cpp-parser.ts's `::`, explicit-template-arg and `>>` template-close lexing.
	terminals: [C.IDENT, CPP.TYPE_SCOPE, CPP.TEMPLATE_FN, CPP.RIGHT_SHIFT, CPP.RIGHT_SHIFT_ASSIGN],
	precedence: C.PREC,
	start: translation_unit,
	rules: { translation_unit },
}, {
	// each GLR branch mutates its own ctx (typedef registration, templateDepth), same as cpp-parser.ts
	forkCtx: (ctx: CPP.CppCtx) => ({ ...ctx, typedefNames: new Set(ctx.typedefNames) }),
}, {
	// an HLSL production is pushed onto C's *and* cpp's rules, so an edit to any has to invalidate this cache
	sources:	[__filename, siblingSource(__filename, 'c-parser'), siblingSource(__filename, 'cpp-parser')],
	cachePath:	path.join(__dirname, '../../.tables-cache/hlsl-parser.tables'),
});

export interface Options extends PreprocessOptions {
	// Extra names to treat as types before parsing (a struct from an unresolved include, a typedef, ...).
	knownTypes?: Iterable<string>;
}

export const hlslParser = {
	...parser,
	// Source runs through the preprocessor first, so `#define`/`#include`/conditional directives work, then
	// `#pragma` etc. are skipped as unknown directives. Builtin type names are seeded per parse.
	parse: async (code: string, options?: Options) => {
		return parser.parse(await preprocess(code, options), {
			pendingTypedef: false,
			typedefNames: new Set<string>([...HLSL_BUILTIN_TYPES, ...(options?.knownTypes ?? [])]),
			templateDepth: 0,
		});
	}
};
