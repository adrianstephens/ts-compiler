import * as path from 'path';
import { makeRule, Rules, List, termOneOf } from '@isopodlabs/tison';
import { makeCachedParser, siblingSource } from '@isopodlabs/tison/tableCache';
import { preprocess, PreprocessOptions } from '../cpp/preprocessor';
import { Module, Identifier, stampPos } from '@isopodlabs/tison/ast';
import * as C from '../cpp/c-parser';
import * as CPP from '../cpp/cpp-parser';
import * as HLSL from './hlsl-parser';

// ===================================================================
//  Slang Parser -- an extension of hlsl-parser
// ===================================================================
//
// Slang (shader-slang) is an HLSL superset, so this extends hlsl-parser.ts (itself over cpp-parser.ts,
// itself over c-parser.ts): everything HLSL-shaped -- semantics, `register`, `cbuffer`, `[attributes]`,
// `discard`, templates, swizzles, the preprocessor -- is inherited unchanged. The additions here are the
// constructs that make Slang Slang:
//
//   - `interface IFoo : IBase { associatedtype T; T get(); }` (associated types register as type names at
//     head-reduce time, so a method's `T` return parses);
//   - generics: `__generic<T : IFoo>` (with `typename`/`class` optional and an optional `where` clause)
//     and the newer `T f<T>(T x) where T : IFoo` form;
//   - `extension T { ... }`, `typealias X = Y;`, `import module;`;
//   - `let` locals, `ref`/`__ref`/`__constref` parameter qualifiers;
//   - `__target_switch`/`__stage_switch`.
//
// `interface` is modelled as its own top-level definition rather than a new `type_specifier`, so the
// interface name is simply registered and used as an ordinary type -- that is what keeps this file from
// having to re-instantiate cpp-parser.ts's whole `Declarator`/`DeclSpec` chain just to widen
// `TypeSpecifierExt`.
//
// Known simplifications/omissions:
//   - `__subscript`/`__init` accessor syntax, `implementing`'s semantic effects, and module-system semantics
//     are not modelled (`implementing IFoo;` is parsed as a member, nothing resolves it).
//   - New-style generics constrain the return type to a registered type or a single unregistered name
//     (`T f<T>()`), because the return type is lexed before `<T>` can register `T`.
//   - Parses, but does not validate: generic instantiation, interface conformance, capability/target sets.
//   - Load order: c-parser -> cpp-parser -> hlsl-parser -> this file (see the GLSL parser's header note).

// ===================================================================
//  Qualifiers
// ===================================================================

// `ref` is Slang's by-reference parameter/return modifier. Deliberately disjoint from hlsl-parser.ts's own
// qualifier terminal (which already has `in`/`out`/`inout`), so the two never tie in the lexer.
export const SLANG_QUALIFIERS = ['ref', '__ref', '__constref'] as const;
export type SlangQualifier = typeof SLANG_QUALIFIERS[number];
export type QualifierFlags = HLSL.QualifierFlags & Partial<Record<SlangQualifier, true>>;
export type DeclarationSpec = HLSL.DeclarationSpec & Partial<Record<SlangQualifier, true>>;

// ===================================================================
//  AST types
// ===================================================================

export type Expr			= HLSL.Expr;
export type Declarator		= HLSL.Declarator;
export type ParameterDecl	= HLSL.ParameterDecl;
export type Annotation		= HLSL.Annotation;
export type Initializer		= HLSL.Initializer;

// An interface member: cpp's class members (methods, nested types, ...) plus Slang's own.
export interface AssociatedTypeMember	{ type: 'associatedtype'; name: string; constraint?: CPP.TypeName }
export interface ImplementingMember		{ type: 'implementing'; target: CPP.TypeName }
export type InterfaceMember				= CPP.ClassMember | AssociatedTypeMember | ImplementingMember;

export interface InterfaceDecl			{ type: 'interface'; name: string; bases?: CPP.TypeName[]; body?: InterfaceMember[] }

export interface GenericParam			{ name: string; constraint?: CPP.TypeName; nonType?: DeclarationSpec }
export interface WhereConstraint		{ param: string; constraint: CPP.TypeName }
export interface GenericDecl			{ type: 'generic_decl'; params: GenericParam[]; where?: WhereConstraint[]; declaration: Definition }

export interface ExtensionDecl			{ type: 'extension'; target: CPP.TypeName; body: CPP.ClassMember[] }
export interface TypeAlias				{ type: 'typealias'; name: string; target: CPP.TypeName }
export interface ImportDecl				{ type: 'import'; module: string }

export interface LetDecl				{ type: 'let'; specifiers?: DeclarationSpec; declarator: Declarator; initializer: Initializer }
export interface TargetCase				{ labels?: string[]; body: Stmt[] }
export interface TargetSwitch			{ type: 'target_switch'; kind: '__target_switch' | '__stage_switch'; cases: TargetCase[] }

export interface FunctionDef extends C.FunctionDef<Declarator, CPP.TypeSpecifierExt, Expr, Stmt> { annotation?: Annotation }

export type Stmt = CPP.Stmt | { type: 'discard' } | LetDecl | TargetSwitch;
export type Definition = CPP.Definition<Stmt>
	| FunctionDef
	| HLSL.CBufferDecl
	| HLSL.AttributedDefinition
	| InterfaceDecl
	| GenericDecl
	| ExtensionDecl
	| TypeAlias
	| ImportDecl;

// ===================================================================
//  Grammar
// ===================================================================

const Rule = makeRule<CPP.CppCtx>(stampPos);

const specifier_qualifier_list = C.specifier_qualifier_list as unknown as Rules<DeclarationSpec>;
specifier_qualifier_list.push(
	Rule([termOneOf(SLANG_QUALIFIERS), specifier_qualifier_list], $ => ({ ...$[1], [$[0]]: true })),
);

// --- interfaces ----------------------------------------------------
//
// `interface IDENT` reduces before the body, registering the name, so `IFoo` is usable as a type
// everywhere afterwards. `associatedtype IDENT` reduces before its `;` -- the same head-time registration
// rule that cpp-parser.ts's `struct_head`/`class_head` use, and for the same next-token-already-lexed reason.

const interface_head = Rules<string>(
	Rule(['interface', C.IDENT],		($, ctx) => { ctx.typedefNames.add($[1]); return $[1]; }),
	Rule(['interface', C.TYPE_NAME],	$ => $[1]),
);
const interface_bases = Rules<CPP.TypeName[]>(
	Rule([':', List(C.type_name, ',')], $ => $[1]),
);

const associatedtype_head = Rules<string>(
	Rule(['associatedtype', C.IDENT],		($, ctx) => { ctx.typedefNames.add($[1]); return $[1]; }),
	Rule(['associatedtype', C.TYPE_NAME],	$ => $[1]),
);
const associatedtype_member = Rules<AssociatedTypeMember>(
	Rule([associatedtype_head, ';'],					$ => ({ type: 'associatedtype', name: $[0] })),
	Rule([associatedtype_head, ':', C.type_name, ';'],	$ => ({ type: 'associatedtype', name: $[0], constraint: $[2] })),
);
const implementing_member = Rules<ImplementingMember>(
	Rule(['implementing', C.type_name, ';'], $ => ({ type: 'implementing', target: $[1] })),
);

// cpp-parser.ts's `struct_declaration` is referenced, not pushed onto, so `associatedtype` cannot leak into
// ordinary struct bodies.
const interface_member = Rules<InterfaceMember>(
	C.struct_declaration as unknown as Rules<InterfaceMember>,
	associatedtype_member,
	implementing_member,
);
const interface_body = Rules<InterfaceMember[]>(
	Rule(['{', '}'],						_ => []),
	Rule(['{', List(interface_member), '}'], $ => $[1]),
);
const interface_decl = Rules<InterfaceDecl>(
	Rule([interface_head, interface_bases, interface_body],	$ => ({ type: 'interface', name: $[0], bases: $[1], body: $[2] })),
	Rule([interface_head, interface_body],					$ => ({ type: 'interface', name: $[0], body: $[1] })),
);

// --- generics ------------------------------------------------------

// Each parameter registers its name in its own action -- exactly cpp-parser.ts's `template_param` trick --
// so by the time `>` is shifted the name is a type, and the declaration that follows (`T f(...)`) parses.
const generic_param = Rules<GenericParam>(
	Rule([C.IDENT],										($, ctx) => { ctx.typedefNames.add($[0]); return { name: $[0] }; }),
	Rule([C.TYPE_NAME],									$ => ({ name: $[0] })),
	Rule([C.IDENT, ':', C.type_name],					($, ctx) => { ctx.typedefNames.add($[0]); return { name: $[0], constraint: $[2] }; }),
	Rule([C.TYPE_NAME, ':', C.type_name],				$ => ({ name: $[0], constraint: $[2] })),
	Rule(['typename', C.IDENT],							($, ctx) => { ctx.typedefNames.add($[1]); return { name: $[1] }; }),
	Rule(['typename', C.TYPE_NAME],						$ => ({ name: $[1] })),
	Rule(['typename', C.IDENT, ':', C.type_name],		($, ctx) => { ctx.typedefNames.add($[1]); return { name: $[1], constraint: $[3] }; }),
	Rule(['typename', C.TYPE_NAME, ':', C.type_name],	$ => ({ name: $[1], constraint: $[3] })),
	Rule(['class', C.IDENT],							($, ctx) => { ctx.typedefNames.add($[1]); return { name: $[1] }; }),
	Rule(['class', C.TYPE_NAME],						$ => ({ name: $[1] })),
	Rule(['class', C.IDENT, ':', C.type_name],			($, ctx) => { ctx.typedefNames.add($[1]); return { name: $[1], constraint: $[3] }; }),
	Rule(['class', C.TYPE_NAME, ':', C.type_name],		$ => ({ name: $[1], constraint: $[3] })),
	// A non-type parameter (`int N`, `uint COUNT`): a value, so deliberately NOT registered as a type.
	Rule([C.specifier_qualifier_list, C.IDENT],			$ => ({ name: $[1], nonType: $[0] as DeclarationSpec })),
);
const generic_param_list = List(generic_param, ',');

const where_constraint = Rules<WhereConstraint>(
	Rule([C.IDENT, ':', C.type_name],		$ => ({ param: $[0], constraint: $[2] })),
	Rule([C.TYPE_NAME, ':', C.type_name],	$ => ({ param: $[0], constraint: $[2] })),
);
const where_clause = Rules<WhereConstraint[]>(
	Rule(['where', List(where_constraint, ',')], $ => $[1]),
);

const generic_head = Rules<GenericParam[]>(
	Rule(['__generic', '<', generic_param_list, '>'], $ => $[2]),
);

// `__generic<T> ...`: the head precedes the declaration, so `T` is registered before the return type is
// lexed. The `where` variants bypass cpp's `function_definition` (which has no where slot).
const functionDef = (specifiers: DeclarationSpec, declarator: Declarator, body: C.Block<Declarator, CPP.TypeSpecifierExt, Expr, Stmt>, annotation?: Annotation): FunctionDef =>
	({ type: 'function_def', specifiers, declarator, body, annotation }) as FunctionDef;

const generic_definition = Rules<GenericDecl>(
	Rule([generic_head, C.function_definition],						$ => ({ type: 'generic_decl', params: $[0], declaration: $[1] as Definition })),
	Rule([generic_head, interface_decl],							$ => ({ type: 'generic_decl', params: $[0], declaration: $[1] as Definition })),
	Rule([generic_head, interface_decl, ';'],						$ => ({ type: 'generic_decl', params: $[0], declaration: $[1] as Definition })),
	Rule([generic_head, C.declaration],								$ => ({ type: 'generic_decl', params: $[0], declaration: $[1] as Definition })),
	Rule([generic_head, C.declaration_specifiers, C.declarator, where_clause, C.compound_statement],
		$ => ({ type: 'generic_decl', params: $[0], where: $[3], declaration: functionDef($[1] as DeclarationSpec, $[2] as Declarator, $[4]) })),
	Rule([generic_head, C.declaration_specifiers, C.declarator, where_clause, ';'],
		$ => ({ type: 'generic_decl', params: $[0], where: $[3], declaration: { type: 'declaration', specifiers: $[1], initDeclarators: [$[2]] } as unknown as Definition })),
);

// `T f<T>(T x) where T : IFoo { ... }` -- the newer generic syntax. The return type is lexed *before*
// `<T>` registers `T`, so an unregistered return type is spelled as a bare `IDENT` alternative that builds
// the specifier itself (`C.declaration_specifiers` covers the registered-type case). The four-way cross
// product (empty params x where x definition/prototype) is generated; `as any` is the same concession
// cpp-parser.ts makes for its generated rule shapes.
const new_style_generic: Rules<Definition> = [];
for (const identReturn of [true, false]) {
	for (const empty of [false, true]) {
		for (const hasWhere of [false, true]) {
			for (const prototype of [false, true]) {
				const rhs: unknown[] = [identReturn ? C.IDENT : C.declaration_specifiers, CPP.TEMPLATE_FN, '<', generic_param_list, '>', '('];
				if (!empty)
					rhs.push(C.parameter_type_list);
				rhs.push(')');
				if (hasWhere)
					rhs.push(where_clause);
				rhs.push(prototype ? ';' : C.compound_statement);
				new_style_generic.push(Rule(rhs as any, ($: any[]) => {
					const specifiers = identReturn ? { type: C.RefType($[0]) } : $[0];
					const params: C.ParamList = empty ? { params: [] } : $[6];
					const declarator = C.FunctionDecl(Identifier($[1]), params.params, params.variadic);
					return {
						type: 'generic_decl',
						params: $[3],
						where: hasWhere ? $[empty ? 7 : 8] : undefined,
						declaration: prototype
							? { type: 'declaration', specifiers, initDeclarators: [declarator] }
							: { type: 'function_def', specifiers, declarator, body: $[$.length - 1] },
					} as unknown as Definition;
				}));
			}
		}
	}
}

// --- extension / typealias / import --------------------------------

const extension_body = Rules<CPP.ClassMember[]>(
	Rule(['{', '}'],						_ => []),
	Rule(['{', C.struct_body, '}'],			$ => $[1] as CPP.ClassMember[]),
);
const extension_decl = Rules<ExtensionDecl>(
	Rule(['extension', C.type_name, extension_body], $ => ({ type: 'extension', target: $[1], body: $[2] })),
);

// Registered at the `=`-less head, before the aliased type is parsed, same as every other eager head here.
const typealias_head = Rules<string>(
	Rule(['typealias', C.IDENT],	($, ctx) => { ctx.typedefNames.add($[1]); return $[1]; }),
);
const typealias_decl = Rules<TypeAlias>(
	Rule([typealias_head, '=', C.type_name, ';'], $ => ({ type: 'typealias', name: $[0], target: $[2] })),
);

const import_path = Rules<string>(self => [
	Rule([C.IDENT],						$ => $[0]),
	Rule([self, '.', C.IDENT],			$ => `${$[0]}.${$[2]}`),
	Rule([C.STRING_LITERAL],			$ => $[0].slice(1, -1)),
]);
const import_decl = Rules<ImportDecl>(
	Rule(['import', import_path, ';'], $ => ({ type: 'import', module: $[1] })),
);

const external_definition = C.external_definition as unknown as Rules<Definition>;
external_definition.push(
	generic_definition,
	new_style_generic,
	Rule([interface_decl],		$ => $[0]),
	Rule([interface_decl, ';'],	$ => $[0]),
	extension_decl,
	typealias_decl,
	import_decl,
);

// --- statements ----------------------------------------------------

// `let x = 3;` (inferred) and `let float4 w = v;` (explicit). `ref` rides specifier_qualifier_list above.
const let_decl = Rules<LetDecl>(
	Rule(['let', C.declaration_specifiers, C.declarator, '=', C.initializer, ';'],
		$ => ({ type: 'let', specifiers: $[1] as DeclarationSpec, declarator: $[2] as Declarator, initializer: $[4] as Initializer })),
	Rule(['let', C.declarator, '=', C.initializer, ';'],
		$ => ({ type: 'let', declarator: $[1] as Declarator, initializer: $[3] as Initializer })),
);
(C.statement as unknown as Rules<Stmt>).push(let_decl);

// `__target_switch { case glsl: ... default: ... }` / `__stage_switch`.
//
// A target label (`case glsl:`) is the *same token sequence* as a `switch`'s own `case` statement, so a
// dedicated `target_case` nonterminal loses the case boundary to c-parser.ts's `case` rule (LALR shifts the
// next `case` into the running body). Instead the body is parsed as a plain statement list -- c-parser.ts's
// `case`/`default` statements capture the labels exactly -- and the action folds them back into
// `TargetCase`s. Bare `case`/`default` at this level can only be target labels: a nested `switch` is one
// `statement`, so its cases never surface here.
function targetCases(stmts: CPP.Stmt[]): TargetCase[] {
	const cases: TargetCase[] = [];
	for (const s of stmts) {
		if (s.type === 'case' || s.type === 'default') {
			const labels: string[] = [];
			let isDefault = false;
			let current: CPP.Stmt | undefined = s;
			while (current && (current.type === 'case' || current.type === 'default')) {
				if (current.type === 'case') {
					if (current.test.type !== 'identifier')
						throw new Error('__target_switch case label must be a target name');
					labels.push(current.test.name);
				} else {
					isDefault = true;
				}
				current = current.body;
			}
			cases.push({ labels: isDefault ? undefined : labels, body: current ? [current] : [] });
		} else if (cases.length) {
			cases[cases.length - 1].body.push(s);
		} else {
			throw new Error('__target_switch: statement before the first case label');
		}
	}
	return cases;
}
const target_switch = Rules<TargetSwitch>(
	Rule(['__target_switch', '{', List(C.statement), '}'],	$ => ({ type: 'target_switch', kind: '__target_switch', cases: targetCases($[2]) })),
	Rule(['__target_switch', '{', '}'],						_ => ({ type: 'target_switch', kind: '__target_switch', cases: [] })),
	Rule(['__stage_switch', '{', List(C.statement), '}'],	$ => ({ type: 'target_switch', kind: '__stage_switch', cases: targetCases($[2]) })),
	Rule(['__stage_switch', '{', '}'],						_ => ({ type: 'target_switch', kind: '__stage_switch', cases: [] })),
);
(C.statement as unknown as Rules<Stmt>).push(target_switch);

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
	// a Slang production is pushed onto C's/cpp's/hlsl's rules, so an edit to any has to invalidate this cache
	sources:	[__filename, siblingSource(__filename, 'c-parser'), siblingSource(__filename, 'cpp-parser'), siblingSource(__filename, 'hlsl-parser')],
	cachePath:	path.join(__dirname, '../../.tables-cache/slang-parser.tables'),
});

export interface Options extends PreprocessOptions {
	// Extra names to treat as types before parsing (a struct from an unresolved include, a typedef, ...).
	knownTypes?: Iterable<string>;
}

export const slangParser = {
	...parser,
	parse: async (code: string, options?: Options) => {
		return parser.parse(await preprocess(code, options), {
			pendingTypedef: false,
			typedefNames: new Set<string>([...HLSL.HLSL_BUILTIN_TYPES, ...(options?.knownTypes ?? [])]),
			templateDepth: 0,
		});
	}
};
