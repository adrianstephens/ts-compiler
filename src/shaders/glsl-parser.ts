import * as path from 'path';
import { makeRule, Rules, List, termOneOf, removeRules } from '@isopodlabs/tison';
import { makeCachedParser, siblingSource } from '@isopodlabs/tison/tableCache';
import { preprocess, PreprocessOptions } from '../cpp/preprocessor';
import { Module, Identifier, stampPos } from '@isopodlabs/tison/ast';
import * as C from '../cpp/c-parser';

// ===================================================================
//  GLSL Parser -- an extension of c-parser
// ===================================================================
//
// Extends the plain-C grammar in c-parser.ts toward GLSL (desktop 4.x and ESSL), the same way
// cpp-parser.ts extends it toward C++14: the AST widens through c-parser.ts's `X`/`E`/`S` type seams,
// and every new production is pushed onto the base's exported rule arrays. GLSL has no
// pointers/references/templates, so the C declarator machinery carries over unchanged -- the additions
// are its type names, its qualifiers, `layout`, `struct` name registration, constructor calls,
// `discard` and `precision`.
//
// Known simplifications/omissions:
//   - Builtin type names (vec/mat/sampler/image/...) are registered as typedef-style type names (see
//     GLSL_BUILTIN_TYPES) rather than as terminals, so a shader cannot name a variable `vec3` -- which
//     GLSL reserves anyway. This reuses c-parser.ts's existing IDENT callback untouched.
//   - `float[3] a;` (array *type* before the name) is not supported; `float a[3];` is.
//   - `true`/`false` parse as identifiers, not boolean literals (c-parser.ts has no boolean literal, and
//     adding a keyword terminal for them buys an AST nicety at the cost of a lexer tie with IDENT).
//   - `shared`, `subroutine`, `packed`, `row_major`/`column_major` stay ordinary identifiers so they can
//     head `layout(...)` items; `shared float x;` therefore does not parse as a declaration.
//   - Parses, but does not validate: precision rules, reinterpretation, stage-appropriate builtins, etc.
//     are all accepted syntactically. Like cpp-parser.ts, this is a front end, not a verifier.
//   - Because every extension mutates c-parser.ts's shared rule objects in place, load cpp-parser.ts and
//     this file in *one* process only if this parser loads last (see cpp-parser.ts's own note); the built
//     `cParser` tables are compiled at c-parser.ts's module load and are unaffected either way.

// ===================================================================
//  Qualifiers
// ===================================================================

// Each category is ONE terminal (so `inout` can never tie with `in`), and the categories are disjoint --
// including c-parser.ts's own `const`/`volatile`, which stay on the base grammar and are deliberately not
// repeated here.
export const STORAGE_QUALIFIERS = ['in', 'out', 'inout', 'uniform', 'attribute', 'varying', 'buffer', 'coherent', 'restrict', 'readonly', 'writeonly'] as const;
export const INTERPOLATION_QUALIFIERS = ['smooth', 'flat', 'noperspective'] as const;
export const PRECISION_QUALIFIERS = ['lowp', 'mediump', 'highp'] as const;
export const AUXILIARY_QUALIFIERS = ['invariant', 'precise', 'centroid', 'sample', 'patch'] as const;

export type StorageQualifier = typeof STORAGE_QUALIFIERS[number];
export type InterpolationQualifier = typeof INTERPOLATION_QUALIFIERS[number];
export type PrecisionQualifier = typeof PRECISION_QUALIFIERS[number];
export type AuxiliaryQualifier = typeof AUXILIARY_QUALIFIERS[number];
export type GlslQualifier = StorageQualifier | InterpolationQualifier | PrecisionQualifier | AuxiliaryQualifier;

// The flags a qualifier sets on `DeclSpec` (same runtime convention as c-parser.ts's `const`/`volatile`:
// the qualifier's own spelling becomes a `true` key).
export type QualifierFlags = Partial<Record<GlslQualifier, true>>;

// `layout(...)` items: `layout(location = 0)`, `layout(std140)`, `layout(triangles)`. A bare item's value
// is left undefined; a `= expr` value is the parsed constant expression (an identifier like `std140` is one).
export interface LayoutQualifier	{ name: string; value?: Expr; }

// ===================================================================
//  AST types -- one per c-parser.ts seam
// ===================================================================

// The GLSL-only type-specifier form: an interface block head
// (`uniform Block { mat4 mvp; } ubo;`) reached through c-parser.ts's `TypeSpecifier<X>` seam.
export interface InterfaceBlock		{ type: 'interface_block'; name?: string; body?: StructMember[]; }
export type TypeSpecifierExt		= InterfaceBlock;
export type TypeSpecifier			= C.TypeSpecifier<TypeSpecifierExt>;
export type DeclSpec				= C.DeclSpec<TypeSpecifierExt> & QualifierFlags & { layout?: LayoutQualifier[] };
export type DeclarationSpec			= C.DeclarationSpec<TypeSpecifierExt> & QualifierFlags & { layout?: LayoutQualifier[] };

// GLSL takes no pointers or references, so the `R` seam stays at its `never` default. `P` supplies the
// parameter shape (a plain C parameter -- GLSL's `in`/`out`/`inout` live in the specifiers). The third `X`
// is c-parser.ts's array-size expression seam, so a `float data[4]` member's `size` is GLSL's own `Expr`.
export type Declarator				= C.Declarator<never, ParameterDecl, ExprAdditions>;
export type AbstractDeclarator		= C.AbstractDeclarator<never, ParameterDecl, ExprAdditions>;
export type TypeName				= C.TypeName<AbstractDeclarator, TypeSpecifierExt>;
export type ParameterDecl			= C.ParameterDecl<Declarator, TypeSpecifierExt>;
export type ParamList				= C.ParamList<ParameterDecl>;

// A struct member is C's bare-name/bitfield shape or a full declarator (arrays: `float data[4];`).
export type StructDeclarator		= C.StructDeclarator | { declarator: Declarator };
export type StructMember			= C.StructMember<StructDeclarator, TypeSpecifierExt>;

// `E`: the expression-widening seam. GLSL's only new expression form is the constructor/functional cast
// (`vec3(1.0)`, `float(x)`), which c-parser.ts cannot express because a registered type name is inert
// outside a declaration.
export type Expr = C.Expr<ExprAdditions>;
type ExprAdditions					= { type: 'functional_cast'; target: string; arguments: Expr[] };

// `S`: the statement-widening seam.
export type Stmt = C.Stmt<Declarator, TypeSpecifierExt, Expr, StmtAdditions>;
type StmtAdditions					= { type: 'discard' };

export type Declaration				= C.Declaration<Declarator, TypeSpecifierExt, Expr>;
export type Block					= C.Block<Declarator, TypeSpecifierExt, Expr, Stmt>;

// Top-level forms with no C analogue: `precision highp float;`, `layout(local_size_x = 8) in;`,
// `invariant gl_Position;`.
export interface PrecisionDecl		{ type: 'precision'; precision: PrecisionQualifier; specifiers: TypeSpecifier }
export interface LayoutDecl			{ type: 'layout_decl'; layout: LayoutQualifier[]; qualifier: StorageQualifier }
export interface QualifierDecl		{ type: 'qualifier_decl'; qualifiers: QualifierFlags; declarators: C.InitDeclarator<Declarator, Expr>[] }

export type Definition				= C.Definition<Declarator, TypeSpecifierExt, Expr, Stmt>
	| PrecisionDecl
	| LayoutDecl
	| QualifierDecl;

// ===================================================================
//  Builtin type names
// ===================================================================
//
// GLSL's type vocabulary is open-ended in spelling but closed in shape, so it is registered up front as
// type names rather than enumerated as grammar productions. Spelling variants that GLSL never uses are
// harmless to include (they are only *names*); the scalar keywords c-parser.ts already has (`int`, `float`,
// `double`, `void`) stay terminals and are not repeated here.

const SAMPLER_DIMS	= ['1D', '2D', '3D', 'Cube', '1DArray', '2DArray', 'CubeArray', '2DMS', '2DMSArray', 'Buffer', '2DRect'];
const SHADOW_DIMS	= ['1D', '2D', 'Cube', '1DArray', '2DArray', 'CubeArray', '2DRect'];
const IMAGE_DIMS	= ['1D', '2D', '3D', 'Cube', '1DArray', '2DArray', 'CubeArray', 'Buffer', '2DMS', '2DMSArray'];

export const GLSL_BUILTIN_TYPES: readonly string[] = [
	// Scalars that are not C keywords.
	'uint', 'bool',
	// Vectors (`vec`/`dvec`/`ivec`/`uvec`/`bvec` x 2/3/4).
	...['', 'd', 'i', 'u', 'b'].flatMap(p => [2, 3, 4].map(n => `${p}vec${n}`)),
	// Square matrices (`mat2`, `dmat3`, ...) and non-square ones (`mat2x3`, `dmat4x2`, ...).
	...['', 'd'].flatMap(p => [2, 3, 4].flatMap(c => [`${p}mat${c}`, ...[2, 3, 4].map(r => `${p}mat${c}x${r}`)])),
	// Samplers (float/int/uint), including the shadow and multisample/rect variants.
	...['', 'i', 'u'].flatMap(p => [
		...SAMPLER_DIMS.map(d => `${p}sampler${d}`),
		...SHADOW_DIMS.map(d => `${p}sampler${d}Shadow`),
	]),
	// Images.
	...['', 'i', 'u'].flatMap(p => IMAGE_DIMS.map(d => `${p}image${d}`)),
	// Subpass inputs and the atomic counter.
	'subpassInput', 'subpassInputMS', 'isubpassInput', 'isubpassInputMS', 'usubpassInput', 'usubpassInputMS',
	'atomic_uint',
];

// ===================================================================
//  Grammar
// ===================================================================

const Rule = makeRule<C.Ctx>(stampPos);

const glsl_storage_qualifier		= termOneOf(STORAGE_QUALIFIERS);
const glsl_interpolation_qualifier	= termOneOf(INTERPOLATION_QUALIFIERS);
const glsl_precision_qualifier		= termOneOf(PRECISION_QUALIFIERS);
const glsl_auxiliary_qualifier		= termOneOf(AUXILIARY_QUALIFIERS);

// Every qualifier terminal, for the one place that accepts any of them (a specifier prefix). Deliberately
// NOT wrapped in a `Rules<GlslQualifier>` nonterminal: that would need a unit reduction after the terminal,
// which conflicts with `glsl_storage_qualifier interface_block` below -- both shift a storage qualifier, and
// the parser must decide between reducing to the combined nonterminal and shifting the block's name. LALR
// resolves that the wrong way (it picks the block reading and then demands `{` where a type name belongs).
const QUALIFIERS = [glsl_storage_qualifier, glsl_interpolation_qualifier, glsl_precision_qualifier, glsl_auxiliary_qualifier] as const;

// `layout(...)`: a comma-separated list of names, each optionally `= constant-expression`.
const layout_item = Rules<LayoutQualifier>(
	Rule([C.IDENT],								$ => ({ name: $[0] })),
	Rule([C.IDENT, '=', C.constant_expression],	$ => ({ name: $[0], value: $[2] })),
);
const layout_item_list = List(layout_item, ',');
const glsl_layout = Rules<LayoutQualifier[]>(
	Rule(['layout', '(', layout_item_list, ')'], $ => $[2]),
);

// ===================================================================
//  Declarations: qualifiers, `struct`, interface blocks, `precision`
// ===================================================================

// Leading qualifiers (`uniform float x;`, `flat in vec3 n;`), pushed onto c-parser.ts's
// specifier_qualifier_list exactly as cpp-parser.ts pushes its own leading `const`/`volatile` form. The
// qualifier's spelling becomes a `true` key on the specifier, matching c-parser.ts's own convention.
const specifier_qualifier_list = C.specifier_qualifier_list as unknown as Rules<DeclarationSpec>;
specifier_qualifier_list.push(
	Rule([glsl_layout, specifier_qualifier_list],	$ => ({ ...$[1], layout: $[0] })),
	...QUALIFIERS.map(q => Rule([q, specifier_qualifier_list], $ => ({ ...$[1], [$[0]]: true }))),
);

// `struct IDENT` reduces the moment the name is seen -- before `{` is shifted -- so the name is registered
// by the time the body (and any later use) parses. This *replaces* c-parser.ts's monolithic
// `struct IDENT { ... }` form, which shifts `{` before any reduction can run: registering later is too
// late, because LALR has already peeked past the `}` at the next token (same call cpp-parser.ts makes).
removeRules(C.struct_or_union_specifier, rhs => rhs[0] === 'struct' && rhs[1] === C.IDENT);

const struct_head = Rules<string>(
	Rule(['struct', C.IDENT],		($, ctx) => { ctx.typedefNames.add($[1]); return $[1]; }),
	Rule(['struct', C.TYPE_NAME],	$ => $[1]),
);
(C.struct_or_union_specifier as unknown as Rules<C.StructSpecifier>).push(
	Rule([struct_head],							$ => ({ type: 'struct', name: $[0] })),
	Rule([struct_head, '{', '}'],				$ => ({ type: 'struct', name: $[0], body: [] })),
	Rule([struct_head, '{', C.struct_body, '}'],	$ => ({ type: 'struct', name: $[0], body: $[2] })),
);

// Struct members with arrays (`float data[4];`, `vec3 corners[8];`). C's struct_declarator is bare-name or
// bitfield only; a declarator-bearing alternative is what lets the member's own `[size]` suffix parse. The
// suffix list is a nonterminal so multi-dimensional members (`mat4 m[4][4]`) need no cross-product of shapes.
const array_suffix = Rules<Expr | undefined>(
	Rule(['[', C.constant_expression, ']'],		$ => $[1]),
	Rule(['[', ']'],							_ => undefined),
);
const array_suffixes = List(array_suffix);
const arrayOf = (element: Declarator, sizes: (Expr | undefined)[]): Declarator =>
	sizes.reduceRight<Declarator>((el, size) => C.ArrayDecl(el, size), element);
(C.struct_declarator as unknown as Rules<StructDeclarator>).push(
	Rule([C.IDENT, array_suffixes],			$ => ({ declarator: arrayOf(Identifier($[0]), $[1]) })),
);

// Interface blocks (`uniform Block { ... } ubo;`). The block name is not a type name -- the *instance* is
// the variable -- so nothing is registered. Accepts a registered spelling too, since GLSL keeps block names
// in their own namespace and a block may reuse a struct's name.
const interface_block = Rules<InterfaceBlock>(
	Rule([C.IDENT, '{', '}'],						$ => ({ type: 'interface_block', name: $[0], body: [] })),
	Rule([C.IDENT, '{', C.struct_body, '}'],		$ => ({ type: 'interface_block', name: $[0], body: $[2] })),
	Rule([C.TYPE_NAME, '{', '}'],					$ => ({ type: 'interface_block', name: $[0], body: [] })),
	Rule([C.TYPE_NAME, '{', C.struct_body, '}'],	$ => ({ type: 'interface_block', name: $[0], body: $[2] })),
);
specifier_qualifier_list.push(
	Rule([glsl_storage_qualifier, interface_block],	$ => ({ type: $[1], [$[0]]: true })),
);

// `precision highp float;` and `layout(local_size_x = 8) in;` / `layout(triangles) in;` -- global forms with
// no C analogue. `layout(...) in;` is distinguished from `layout(...) in vec3 x;` by the token after the
// storage qualifier (`;` vs a type), an ordinary one-token lookahead decision.
const external_definition	= C.external_definition as unknown as Rules<Definition>;
external_definition.push(
	Rule(['precision', glsl_precision_qualifier, C.type_specifier, ';'],	$ => ({ type: 'precision', precision: $[1], specifiers: $[2] })),
	Rule([glsl_layout, glsl_storage_qualifier, ';'],						$ => ({ type: 'layout_decl', layout: $[0], qualifier: $[1] })),
	// `invariant gl_Position;` -- a qualifier applied to an existing (here, builtin) variable, so there is no
	// type to hang it on; a dedicated node keeps the absent `type` honest instead of faking a DeclSpec.
	Rule([glsl_auxiliary_qualifier, C.init_declarator_list, ';'],			$ => ({ type: 'qualifier_decl', qualifiers: { [$[0]]: true }, declarators: $[1] })),
);

// ===================================================================
//  Expressions: constructors, zero-argument calls; `discard` statements
// ===================================================================

// `vec3(1.0)`, `mat3(x)`, `float(v)` -- GLSL's only cast form. A registered type name is otherwise inert in
// expression position, so these steal nothing. The keyword-typed scalars are spelled as the bare terminals
// c-parser.ts already interns for `int`/`float`/`double` -- a `scalar_type` nonterminal over them would
// reduce/reduce against c-parser.ts's own `type_specifier -> 'int'` and lose the declaration reading.
// A named builder keeps the `functional_cast` tag literal: object literals returned from a `flatMap` callback
// get no contextual type, so `type` would widen to `string` and stop being part of the `Expr` union.
const construct = (target: string, args: Expr[]): ExprAdditions => ({ type: 'functional_cast', target, arguments: args });

(C.primary_expression as unknown as Rules<Expr>).push(
	Rule([C.TYPE_NAME, '(', C.argument_expression_list, ')'],	$ => construct($[0], $[2])),
	Rule([C.TYPE_NAME, '(', ')'],								$ => construct($[0], [])),
	...(['int', 'float', 'double'] as const).flatMap(kw => [
		Rule([kw, '(', C.argument_expression_list, ')'],		$ => construct(kw, $[2])),
		Rule([kw, '(', ')'],									_ => construct(kw, [])),
	]),
);

// Zero-argument calls (`barrier()`, `main()`): c-parser.ts's argument list is a non-empty `List`.
(C.postfix_expression as unknown as Rules<Expr>).push(
	Rule([C.postfix_expression, '(', ')'],	$ => ({ type: 'call', callee: $[0], arguments: [] })),
);

// GLSL's `for` allows empty clauses (`for (;;)`); c-parser.ts's rules all demand a leading expression or
// declaration, so every empty-slot combination needs its own shape.
C.for_statement.push(
	Rule([';', ';'],								_ => ({ init: undefined })),
	Rule([';', ';', C.expression],					$ => ({ init: undefined, update: $[2] })),
	Rule([';', C.expression, ';'],					$ => ({ init: undefined, test: $[1] })),
	Rule([';', C.expression, ';', C.expression],	$ => ({ init: undefined, test: $[1], update: $[3] })),
	Rule([C.expression, ';', ';'],					$ => ({ init: $[0] })),
	Rule([C.expression, ';', ';', C.expression],	$ => ({ init: $[0], update: $[3] })),
	Rule([C.expression, ';', C.expression, ';'],	$ => ({ init: $[0], test: $[2] })),
	Rule([C.declaration, ';'],						$ => ({ init: $[0] })),
	Rule([C.declaration, ';', C.expression],		$ => ({ init: $[0], update: $[2] })),
	Rule([C.declaration, C.expression, ';'],		$ => ({ init: $[0], test: $[1] })),
);

(C.statement as unknown as Rules<Stmt>).push(
	Rule(['discard', ';'],	_ => ({ type: 'discard' })),
);

// ===================================================================
//  Wire it up
// ===================================================================

const translation_unit = C.translation_unit as unknown as Rules<Module<Definition>>;

export const parser = makeCachedParser({
	// C's lexical skips (comments are also removed by the preprocessor, but a direct `parser.parse` call
	// bypasses it). `#version`/`#extension`/`#define` etc. are handled by the preprocessor.
	skip: [/\s+/, /\/\/[^\n]*/, /\/\*[^]*?\*\//],
	// IDENT must be lexed even where only TYPE_NAME is grammatically valid: it is the only terminal whose
	// pattern matches the text, and its callback is what reclassifies a registered (builtin or struct) name.
	terminals: [C.IDENT],
	precedence: C.PREC,
	start: translation_unit,
	rules: { translation_unit },
}, {}, {
	// a GLSL production is pushed onto C's rules, so an edit to either has to invalidate this cache
	sources:	[__filename, siblingSource(__filename, 'c-parser')],
	cachePath:	path.join(__dirname, '../../.tables-cache/glsl-parser.tables'),
});

export interface Options extends PreprocessOptions {
	// Extra names to treat as types before parsing (a struct defined in a header, a typedef, ...).
	knownTypes?: Iterable<string>;
}

export const glslParser = {
	...parser,
	// Source runs through the preprocessor first, so `#define`/`#include`/conditional directives work and
	// `#version`/`#extension` are skipped as unknown directives. Builtin type names are seeded per parse.
	parse: async (code: string, options?: Options) => {
		return parser.parse(await preprocess(code, options), {
			pendingTypedef: false,
			typedefNames: new Set<string>([...GLSL_BUILTIN_TYPES, ...(options?.knownTypes ?? [])]),
		});
	}
};
