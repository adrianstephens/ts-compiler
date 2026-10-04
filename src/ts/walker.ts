import * as TS from './ts-parser';
import * as JS from './js-parser';
import { Literal, Module, ConstantFolder } from '@isopodlabs/tison/ast';
import * as W from '@isopodlabs/tison/walker';
import {mapObject, mapArray, mapArrayA, mapDefined, makeProcess, makeProcessB} from '@isopodlabs/tison/walker';

// ===================================================================
//  Type Guards
// ===================================================================

export function guard<R>(types: string[]) {
	const set = new Set(types);
	return (node: any): node is R => node && typeof node === 'object' && 'type' in node && set.has(node.type);
}

const stmts = ['block', 'var_decl', 'expression', 'empty', 'if', 'do_while', 'while', 'for', 'for_in', 'continue', 'break', 'return', 'with', 'labeled', 'switch', 'throw', 'try', 'debugger', 'function_decl', 'import', 'export', 'export_decl', 'class_decl'];

export const isTsDeclaration	= guard<TS.Declaration>(['type_alias_decl', 'interface_decl', 'enum_decl', 'namespace_decl']);
// Tests JS statement tags but asserts the wide `TS.Statement`: since js-parser's `X` seam every JS
// statement IS one, and asserting the narrow type is what used to force casts at the call sites.
export const isJsStatement		= guard<TS.Stmt>(stmts);

type Value	= JS.Value;
type Type	= TS.Type;
type Expr	= TS.Expr;
type Stmt	= TS.Stmt;
export interface Kinds { statement: Stmt; expression: Expr; type: Type; typeMember: TS.TypeMember; classMember: TS.ClassMember }

//-----------------------------------------------------------------------------
// Constant folding
//-----------------------------------------------------------------------------

function calcUnary(op: JS.unaryOps, x: any) {
	switch (op) {
		case '!':	return !x;
		case '+':	return +x;
		case '~':	return ~x;
		case '-':	return -x;
	}
}

function calcBinary(op: JS.binaryOps, a: any, b: any) {
	switch (op) {
		case '&&':	return a && b;
		case '||':	return a || b;
		case '??':	return a ?? b;
		case '!=':	return a != b;
		case '!==':	return a !== b;
		case '==':	return a == b;
		case '===':	return a === b;
		case '<':	return a < b;
		case '<=':	return a <= b;
		case '>':	return a > b;
		case '>=':	return a >= b;
	}
	if (typeof a === 'number' && typeof b === 'number') {
		switch (op) {
			case '+':	return a + b;
			case '-':	return a - b;
			case '*':	return a * b;
			case '/':	return a / b;
			case '%':	return a % b;
			case '&':	return a & b;
			case '|':	return a | b;
			case '^':	return a ^ b;
			case '<<':	return a << b;
			case '>>':	return a >> b;
			case '>>>':	return a >>> b;
			case '**':	return a ** b;
		}
	} else if (typeof a === 'bigint' && typeof b === 'bigint') {
		switch (op) {
			case '+':	return a + b;
			case '-':	return a - b;
			case '*':	return a * b;
			case '/':	return a / b;
			case '%':	return a % b;
			case '&':	return a & b;
			case '|':	return a | b;
			case '^':	return a ^ b;
			case '<<':	return a << b;
			case '>>':	return a >> b;
			case '**':	return a ** b;
		}
	} else if (op === '+' && (typeof a === 'string' || typeof b === 'string')) {
		return a + b;
	}
}

const typeMasks = {
	number:		1,
	bigint:		2,
	string:		4,
	boolean:	8,
	undefined:	16,
	symbol:		32,
	unknown:	0,
	object:		0,
	function:	0,
} as const;

function isSimple(t: Value): t is number | bigint | string | boolean {
	return !!(typeMasks[typeof t] & 15);
}

const foldable1: Record<string, (op: Value)=>Value | undefined> = {
	Number:		op => Number(op),
	BigInt:		op => isSimple(op) ? BigInt(op) : undefined,
	String:		op => isSimple(op) ? op.toString() : undefined,
	Boolean:	op => Boolean(op),
	parseInt:	op => typeof op === 'string' ? parseInt(op) : undefined,
	parseFloat:	op => typeof op === 'string' ? parseFloat(op) : undefined,
};

const foldableMaths: Record<string, (...op: number[])=>number> = {
	abs:		op => Math.abs(op),
	floor:		op => Math.floor(op),
	ceil:		op => Math.ceil(op),
	round:		op => Math.round(op),
	fround:		op => Math.fround(op),
	max:		(...ops) => Math.max(...ops),
	min:		(...ops) => Math.min(...ops),
	pow:		(a, b) => Math.pow(a, b),
	sqrt:		op => Math.sqrt(op),
	sin:		op => Math.sin(op),
	cos:		op => Math.cos(op),
	tan:		op => Math.tan(op),
	asin:		op => Math.asin(op),
	acos:		op => Math.acos(op),
	atan:		op => Math.atan(op),
	atan2:		(a, b) => Math.atan2(a, b),
	exp:		op => Math.exp(op),
	log:		op => Math.log(op),
	log10:		op => Math.log10(op),
	log2:		op => Math.log2(op),
	trunc:		op => Math.trunc(op),
	sign:		op => Math.sign(op),
	sinh:		op => Math.sinh(op),
	cosh:		op => Math.cosh(op),
	tanh:		op => Math.tanh(op),
	asinh:		op => Math.asinh(op),
	acosh:		op => Math.acosh(op),
	atanh:		op => Math.atanh(op),
	log1p:		op => Math.log1p(op),
	cbrt:		op => Math.cbrt(op),
	hypot:		(...ops) => Math.hypot(...ops),
	imul:		(a, b) => Math.imul(a, b),
	clz32:		op => Math.clz32(op),
};

function MaybeLiteral(v: any): Expr | undefined {
	return v === undefined ? undefined : Literal(v);
}

export const constantFolder: ConstantFolder<Expr> = {
	foldable(e) {
		if (e.type === 'call') {
			if (e.callee.type === 'identifier')
				return e.callee.name in foldable1 ? 1 : 0;
			
			if (e.callee.type === 'member' && e.callee.object.type === 'identifier') {
				if (e.callee.object.name === 'Math' && e.callee.property in foldableMaths)
					return e.arguments.length;
			}
		}
		return e.type === 'binary' ? 2 : e.type === 'unary' ? 1 : 0;
	},
	fold(e, ops: Value[]) {
		switch (e.type) {
			case 'call':
				if (e.callee.type === 'identifier')
					return MaybeLiteral(foldable1[e.callee.name]?.(ops[0] as Value));
				
				if (e.callee.type === 'member' && e.callee.object.type === 'identifier') {
					if (e.callee.object.name === 'Math' && ops.every(op => typeof op === 'number'))
						return MaybeLiteral(foldableMaths?.[e.callee.property](...ops));
				}
				return undefined;
			case 'binary':
				return MaybeLiteral(calcBinary(e.operator, ops[0], ops[1]));
			case 'unary':
				return MaybeLiteral(calcUnary(e.operator, ops[0]));
		}
	},
	literalValue(e) {
		return e.type === 'literal' ? e.value : undefined;
	},
	truthy(value) {
		return !!value;
	},
};

//-----------------------------------------------------------------------------
// walk
//-----------------------------------------------------------------------------

export interface Walker extends W.Walker<Kinds> {
	statements:		<T extends Stmt>(x: readonly T[]) => T[];
	body:			<T extends Stmt>(x?: T[] | Expr) => T[] | Expr | undefined;	// a function/arrow body
	module:			<M extends Module<Stmt>>(x: M) => M;
}
type OnAST<U>		= W.OnAST<U, Walker>;

export function walker(
	onStatement?:	OnAST<TS.Stmt>,
	onExpression?:	OnAST<Expr>,
	onType?:		OnAST<Type>,
	onTypeMember?:	OnAST<TS.TypeMember>,
	onClassMember?:	OnAST<TS.ClassMember>
): Walker {

	// The bodies still reached through a `CallSig` (a function/method/arrow body) keep js-parser's own
	// narrow `Statement<T>` -- see the `X` seam comment there. Every NESTED statement slot uses
	// `mapStatement` directly now and needs no cast.
	const mapStatementC	= (stmt: TS.Stmt) => mapStatement(stmt) as JS.Stmt<any> | undefined;
	const mapTypeU		= (type: any): any => mapType(type as Type);

	const mapKey = (key: JS.Key): JS.Key =>
		typeof key === 'object' ? { computed: mapExpressionA(key.computed) } : key;

	const mapBindingTarget = (t: JS.BindingTarget): JS.BindingTarget => {
		if (typeof t === 'string')
			return t;
		if (t.type === 'object_pattern')
			return mapObject(t, {
				properties: mapArray(p => mapObject(p, {
				value: mapBindingTarget,
				default: mapExpression,
			}))});
		return mapObject(t, {elements: mapArray(e => e ? mapObject(e, {
			target: mapBindingTarget,
			default: mapExpression,
		}) : e)});
	};
	const mapTypeParam = (p: TS.TypeParam) => mapObject(p, {
		constraint:		mapType,
		default:		mapType,
	});
	const mapTypeParamU = (p: JS.TypeParam<any>) => mapTypeParam(p as TS.TypeParam) as JS.TypeParam<any>;

	// A TYPE is rebuilt only where a part changed: a rewrite (`substituteType`) keeps unchanged subtrees shared, so identity caches (`resolve`,
	// `lookupMember`, `typeId`'s memo) still hit them. An emptied array still drops its field, as `mapArray` does.
	const keep = <N extends Record<string, any>>(node: N, fields: W.NodeMap<N>): N => {
		const r = mapObject(node, fields);
		return Object.keys(fields).every(k => r[k] === node[k]) ? node : r;
	};
	const keepArrayA = <T,>(map: (x: T) => T | undefined) => (x: readonly T[]): T[] => {
		const r = mapArrayA(map)(x);
		return r.length === x.length && r.every((e, i) => e === x[i]) ? x as T[] : r;
	};
	const keepArray = <T,>(map: (x: T) => T | undefined) => (x: readonly T[]): T[] | undefined => {
		const r = keepArrayA(map)(x);
		return r.length ? r : undefined;
	};
	const keepTypeParam = (p: TS.TypeParam) => keep(p, { constraint: mapType, default: mapType });
	const keepSig = {
		params:			keepArrayA((p: TS.Param) => keep(p, {
			key:			mapBindingTarget,
			default:		mapExpression,
			typeAnnotation:	mapType
		})),
		rest:			(rest: JS.Rest<Type>): JS.Rest<Type> => (t => t === rest.typeAnnotation ? rest : {key: rest.key, typeAnnotation: t})(mapType(rest.typeAnnotation)),
		typeParams:		keepArrayA(keepTypeParam),
		thisType:		(t: Type) => mapType(t),
		returnType:		(t: Type) => mapType(t),
	};

	const mapSig = {
		params:			mapArrayA((p: TS.Param) => mapObject(p, {
			key:			mapBindingTarget,
			default:		mapExpression,
			typeAnnotation:	mapType
		})),
		rest:			(rest: JS.Rest<Type>): JS.Rest<Type> =>	({key: rest.key, typeAnnotation: mapType(rest.typeAnnotation)}),
		typeParams:		mapArrayA(mapTypeParam),
		thisType:		(t: Type) => mapType(t),
		returnType:		(t: Type) => mapType(t),
	};
	const mapSigU = {
		params:			mapArrayA((p: JS.Param<any>) => mapObject(p, {
			key:			mapBindingTarget,
			default:		mapExpression,
			typeAnnotation:	mapTypeU
		})),
		rest:			(rest: JS.Rest<any>): JS.Rest<any> =>	({key: rest.key, typeAnnotation: mapTypeU(rest.typeAnnotation)}),
		typeParams:		mapArrayA(mapTypeParamU),
		thisType:		mapTypeU,
		returnType:		mapTypeU,
	};

	const mapVarDeclarator = (x: JS.Var<any>) =>
		mapObject(x, {
			name: mapBindingTarget,
			init: mapExpression,
			typeAnnotation: mapTypeU
		});

	const objectProperty = (p: JS.ObjectProperty<any>): JS.ObjectProperty<any> => {
		switch (p.type) {
			case 'spread':	return mapObject(p, { operand: mapExpressionA });
			case 'field':	return mapObject(p, { key: mapKey, value: mapExpressionA });
			default:		return mapObject(p, {...mapSigU,
				key:		mapKey,
				body:		mapArrayA(mapStatementC),
			});
		}
	};

	const classMember = (m: TS.ClassMember): TS.ClassMember => {
		switch (m.type) {
			case 'field':	return mapObject(m, {
				key:		mapKey,
				value:		mapExpression,
				typeAnnotation: mapType
			});
			case 'method':
			case 'get':
			case 'set':		return mapObject(m, {
				...mapSig,
				key:		mapKey, 
				body:		mapArrayA(mapStatementC),
			});
			case 'static_block':	return mapObject(m, {
				body: mapArrayA(mapStatementC)
			});
			case 'index_signature':	return mapObject(m, {
				paramType:	mapType,
				typeAnnotation: mapType
			});
		}
	};

	const typeMember = (m: TS.TypeMember): TS.TypeMember => {
		switch (m.type) {
			case 'property':
				return keep(m, {key: mapKey, typeAnnotation: mapTypeA});
			case 'method':
				return keep(m, {...keepSig,
					key: mapKey,
				});
			case 'call':
			case 'construct':
				return keep(m, keepSig);
			case 'index':
				return keep(m, {paramType: mapTypeA, typeAnnotation: mapTypeA});
			default:
				return m;
		}
	};

	const type = (type: Type): Type => {
		switch (type.type) {
			case 'ref':					return keep(type, {typeArgs: keepArray(mapType)});
			case 'typeof':
			case 'import':				return keep(type, {typeArgs: keepArray(mapType)});
			case 'literal':
				return Array.isArray(type.value)
					? keep(type as Literal<JS.TemplatePart<Type>[]>, { value: keepArray(p => p.exp ? keep(p, {exp: mapType}) : p)})
					: type;
			case 'array':				return keep(type, {element: mapTypeA});
			case 'tuple':				return keep(type, {elements: keepArrayA(e =>
					e.type === 'spread'		? keep(e, {argument: mapTypeA})
					: e.type === 'optional'	? keep(e, {element: mapTypeA})
					: e.type === 'labeled'	? keep(e, {element: mapTypeA})
					: mapTypeA(e))});
			case 'union':
			case 'intersection':		return keep(type, {types: keepArrayA(mapTypeA)});
			case 'function':
			case 'constructor':			return keep(type, keepSig);
			case 'object':				return keep(type, {members: keepArrayA(mapTypeMember)});
			case 'keyof':				return keep(type, {argument: mapTypeA});
			case 'indexed_access':		return keep(type, {object: mapTypeA, index: mapTypeA});
			case 'conditional':			return keep(type, {
					checkType:		mapTypeA,
					extendsType:	mapTypeA,
					trueType:		mapTypeA,
					falseType:		mapTypeA
				});
			case 'infer':				return keep(type, {constraint: mapType});
			case 'mapped':				return keep(type, {
					constraint: 	mapTypeA,
					nameType:		mapType,
					valueType:		mapTypeA
				});
			case 'predicate':			return keep(type, {assertedType: mapTypeA});

			case 'this':				return type;
			// no nested `Type` position
			case 'range':				return type;
		}
	};

	const expression = (expr: JS.Expr): JS.Expr => {
		switch (expr.type) {
			case 'literal':		return mapObject(expr, {
				value: v => Array.isArray(v) ? v.map(p => p.exp ? mapObject(p, {exp: mapExpression}) : p) : v
			});
			case 'array':		return mapObject(expr, {
				elements: x => x.map(mapExpression)//mapArray0(mapExpression)
			});
			case 'object':		return mapObject(expr, {
				properties: mapArrayA(objectProperty)
			});
			case 'function': 	return mapObject(expr, {...mapSigU,
				body:		mapArrayA(mapStatementC),
			});
			case 'member':		return mapObject(expr, {
				object:		mapExpressionA
			});
			case 'index':		return mapObject(expr, {
				object:		mapExpressionA,
				index:	mapExpressionA
			});
			case 'call':
			case 'new':			return mapObject(expr, {
				callee:		mapExpressionA,
				arguments:	mapArrayA(mapExpressionA),
				typeArgs:	mapArray(mapTypeU)
			});
			case 'spread':
			case 'unary_post':
			case 'unary':		return mapObject(expr, {
				operand: 	mapExpressionA
			});
			case 'binary':		return mapObject(expr, {
				left:		mapExpressionA,
				right:		mapExpressionA
			});
			case 'conditional':	return mapObject(expr, {
				test:		mapExpressionA,
				consequent: mapExpressionA,
				alternate:	mapExpressionA
			});
			case 'sequence':	return mapObject(expr, {
				expressions: mapArrayA(mapExpressionA)
			});
			case 'tagged_template':	return mapObject(expr, {
				tag: 			mapExpressionA,
				quasi: 			mapArray(p => p.exp ? mapObject(p, {exp: mapExpression}) : p)
			});
			case 'import_call':	return mapObject(expr, {arguments: mapArrayA(mapExpressionA)});
			case 'arrow':		return mapObject(expr, {...mapSigU,
				body: (body: any) => Array.isArray(body) ? mapArrayA(mapStatementC)(body) : mapExpressionA(body),
			});
			case 'assign':		return mapObject(expr, {target: mapExpressionA, value: mapExpressionA});
			case 'await':		return mapObject(expr, {operand: mapExpressionA});
			case 'yield':		return mapObject(expr, {operand: mapExpression});
			case 'class':		return mapObject(expr, {
				superClass: mapExpression,
				body:		mapArrayA(mapClassMemberU),
				typeParams:	mapArray(mapTypeParamU),
				implements: mapArray(mapTypeU)
			});
			case 'instantiation':	return mapObject(expr, {
				expression: mapExpressionA,
				typeArgs:	mapArray(mapTypeU)
			});
			// The cast's own TYPE is mapped too: skipping it meant a type-rewriting walk
			// (`substituteClassTypeParam`) left `this as unknown as T[]` inside a generic class method
			// with an unsubstituted `T`, so an unannotated local initialised from it lowered to
			// `arr:ref` while the value was `arr:f64`.
			case 'as':
			case 'satisfies':
				return mapObject(expr, {
				expression: 	mapExpressionA,
				typeAnnotation:	mapTypeU
			});
			case 'jsx':	return mapObject(expr, {
				attributes:	mapArrayA(p => mapObject(p, {value: mapExpressionA})),
				children:	mapArrayA(mapExpressionA)
			});
			case 'this':
			case 'super':
			case 'identifier':
			case 'import_meta':
				return expr;
		}
	};

	const statement = (stmt: TS.Stmt): TS.Stmt => {
		switch (stmt.type) {
			case 'block':		return mapObject(stmt, {
				body:			mapArrayA(mapStatement)
			});
			case 'var_decl': 	return mapObject(stmt, {
				declarations: 	mapArray(mapVarDeclarator)
			});
			case 'expression': 	return mapObject(stmt, {
				expression:		mapExpressionA
			});
			case 'if':			return mapObject(stmt, {
				test:			mapExpressionA,
				consequent: 	mapStatementA,
				alternate:		mapStatement
			});
			case 'do_while':
			case 'while':		return mapObject(stmt, {
				test:			mapExpressionA,
				body:			mapStatementA
			});
			case 'for': 		return mapObject(stmt, {
				init:			init => init.type === 'var_decl'
					//? mapObject(init, {declarations: mapArray(mapVarDeclarator)})
					? mapStatement(init)
					: mapExpressionA(init),
				...(stmt.kind === 'normal' ? {
					test:			mapExpression,
					update:			mapExpression,
				} : {
					right:			mapExpressionA,
				}),
				body:			mapStatementA
			});
			case 'with':
			case 'throw':
			case 'return': 		return mapObject(stmt, {
				argument:		mapExpression
			});
			case 'labeled':		return mapObject(stmt, {
				body:			mapStatementA
			});
			case 'switch':		return mapObject(stmt, {
				discriminant:	mapExpressionA,
				cases:			mapArrayA(c => mapObject(c, {consequent: mapArrayA(mapStatement)}))
			});
			case 'try':			return mapObject(stmt, {
				body:			mapArrayA(mapStatement),
				handlers:		mapArrayA(h => mapObject(h, {body: mapArrayA(mapStatement)})),
				finalizer:		mapArrayA(mapStatement)
			});
			case 'function_decl':	return mapObject(stmt, {...mapSigU,
				body:			mapArrayA(mapStatementC),
			});
			case 'export':		return mapObject(stmt, {
				default: 		d => !d ? undefined : isJsStatement(d) ? mapStatement(d) : mapExpressionA(d)
			});
			case 'export_decl':	return mapObject(stmt, {
				declaration:	d => mapStatement(d)
			});
			case 'class_decl':	return mapObject(stmt, {
				superClass:		mapExpression,
				// `body` is mandatory (unlike `typeParams`/`implements`, genuinely optional) -- `mapArrayA` keeps a
				// legitimately empty class/interface body as `[]` rather than `mapArray` collapsing it to `undefined`
				// and deleting the field outright (`class Foo {}` has to stay printable).
				body:			mapArrayA(mapClassMemberU),
				typeParams:		mapArray(mapTypeParamU),
				implements:	mapArray(mapTypeU)
			});
			case 'type_alias_decl':	return mapObject(stmt, {
				typeParams:		mapArray(mapTypeParam),
				value: 			mapType
			});
			case 'interface_decl':	return mapObject(stmt,{
				typeParams:		mapArray(mapTypeParam),
				extendsClause:	mapArray(mapType),
				body:			mapArrayA(mapTypeMember)
			});
			case 'enum_decl':	return mapObject(stmt, {
				members:		mapArrayA(m => mapObject(m, {init: mapExpression}))
			});
			case 'namespace_decl':	return mapObject(stmt, {
				body:			mapArrayA(mapStatement)
			});

			default:	return stmt;
		}

	};
	const statements = <T extends Stmt>(x: readonly T[]) => mapArrayA((s: T) => mapStatement(s))(x);
	const recurse: Walker = {
		statement:		x => mapStatement(x),
		expression:		x => mapExpression(x),
		type:			x => mapType(x),
		typeMember:		x => mapTypeMember(x),
		classMember:	x => mapClassMember(x),
		statements,
		body:			x => x === undefined ? undefined : Array.isArray(x) ? statements(x) : mapExpressionA(x),
		module:			x => ({...x, body: statements(x.body)}),
	};

	const mapStatement		= makeProcess(statement, onStatement, recurse, true);
	const mapExpression		= makeProcess(expression, onExpression, recurse, !!onType);
	const mapType			= makeProcess(type, onType, recurse);
	const mapTypeMember		= makeProcess(typeMember, onTypeMember, recurse, true);
	const mapClassMember	= makeProcess(classMember, onClassMember, recurse, true);

	const mapTypeA			= mapDefined(mapType);
	const mapExpressionA	= mapDefined(mapExpression);
	const mapStatementA		= mapDefined(mapStatement);
	const mapClassMemberU	= (m: JS.ClassMember<any>) => mapClassMember(m as TS.ClassMember) as JS.ClassMember<any>;

	return recurse;
}

//-----------------------------------------------------------------------------
// walkB
//-----------------------------------------------------------------------------

export interface WalkerB extends W.WalkerB<Kinds> {
	statements:		(x: readonly Stmt[]) => boolean;
	body:			(x?: Stmt[] | Expr) => boolean;
}
type OnASTB<U>		= W.OnASTB<U, WalkerB>;

export function walkerB(
	onStatement?:	OnASTB<TS.Stmt>,
	onExpression?:	OnASTB<JS.Expr>,
	onType?:		OnASTB<Type>,
	onTypeMember?:	OnASTB<TS.TypeMember|TS.ClassMember>,
): WalkerB {

	const walkKey = (key: JS.Key) => typeof key === 'object' && walkExpression(key.computed);

	const walkBindingTarget = (t: JS.BindingTarget): boolean => {
		return typeof t === 'string' ? false
			: t.type === 'object_pattern'
			? t.properties.some(p => walkBindingTarget(p.value) || walkExpression(p.default))
			: t.elements.some(e => e && (walkBindingTarget(e.target) || walkExpression(e.default)));
	};
	const walkTypeParam = (p: TS.TypeParam) =>
		walkType(p.constraint) || walkType(p.default);

	const walkSig = (sig: TS.CallSig) => sig.params.some(p => walkBindingTarget(p.key) || walkExpression(p.default) || walkType(p.typeAnnotation))
		|| walkType(sig.rest?.typeAnnotation)
		|| walkType(sig.thisType)
		|| walkType(sig.returnType)
		|| !!sig.typeParams?.some(walkTypeParam);


	const walkVarDeclarator = (d: JS.Var<Type>) =>
		walkBindingTarget(d.name) || walkExpression(d.init) || walkType(d.typeAnnotation);

	const objectProperty = (p: JS.ObjectProperty<any>) => {
		switch (p.type) {
		 	case 'spread':				return walkExpression(p.operand);
			case 'field':				return walkKey(p.key) || walkExpression(p.value);
			default:					return walkKey(p.key) || walkSig(p as TS.CallSig) || p.body!.some(walkStatement);
		}
	};

	const classMember = (m: TS.ClassMember) => {
		switch (m.type) {
			case 'field':				return walkKey(m.key) || walkExpression(m.value) || walkType(m.typeAnnotation);
			case 'method':
			case 'get':
			case 'set':					return walkKey(m.key) || walkSig(m) || !!m.body?.some(walkStatement);
			case 'static_block':		return m.body.some(walkStatement);
			case 'index_signature':		return walkType(m.paramType) || walkType(m.typeAnnotation);
		}
	};

	const typeMember = (m: TS.TypeMember) => {
		switch (m.type) {
			case 'property':			return walkKey(m.key) || walkType(m.typeAnnotation);
			case 'method':				return walkKey(m.key) || walkSig(m);
			case 'call':
			case 'construct':			return walkSig(m);
			case 'index':				return walkType(m.paramType) || walkType(m.typeAnnotation);
			default:					return false;
		}
	};

	const type = (t: Type): boolean => {
		switch (t.type) {
			case 'ref':
			case 'typeof':
			case 'import':				return !!t.typeArgs?.some(walkType);
			case 'literal':				return Array.isArray(t.value) && t.value.some(p => walkType(p.exp));
			case 'array':				return walkType(t.element);
			case 'tuple':				return t.elements.some(e =>
				walkType(e.type === 'spread' ? e.argument : e.type === 'optional' || e.type === 'labeled' ? e.element : e)
			);
			case 'union':
			case 'intersection':		return t.types.some(walkType);
			case 'function':
			case 'constructor':			return walkSig(t);
			case 'object':				return t.members.some(walkTypeMember);
			case 'keyof':				return walkType(t.argument);
			case 'indexed_access':		return walkType(t.object) || walkType(t.index);
			case 'conditional':			return walkType(t.checkType) || walkType(t.extendsType) || walkType(t.trueType) || walkType(t.falseType);
			case 'infer':				return walkType(t.constraint);
			case 'mapped':				return walkType(t.constraint) || walkType(t.nameType) || walkType(t.valueType);
			case 'predicate':			return walkType(t.assertedType);
			// 'this': no nested Type position.
			default:					return false;
		}
	};
	
	const expression = (e: JS.Expr): boolean => {
		switch (e.type) {
			case 'literal':				return Array.isArray(e.value) && e.value.some(i => i.exp && walkExpression(i.exp));
			case 'array':				return e.elements.some(walkExpression);
			case 'object':				return e.properties.some(objectProperty);
			case 'function': 			return walkSig(e as TS.CallSig) || (!!e.body && e.body.some(walkStatement));
			case 'member':				return walkExpression(e.object);
			case 'index':				return walkExpression(e.object) || walkExpression(e.index);
			case 'call':
			case 'new':					return walkExpression(e.callee) || e.arguments.some(walkExpression) || (!!e.typeArgs && (e.typeArgs as Type[]).some(walkType));
			case 'spread':
			case 'unary_post':
			case 'unary':				return walkExpression(e.operand);
			case 'binary':				return walkExpression(e.left) || walkExpression(e.right);
			case 'conditional':			return walkExpression(e.test) || walkExpression(e.consequent) || walkExpression(e.alternate);
			case 'sequence':			return e.expressions.some(walkExpression);
			case 'tagged_template':		return walkExpression(e.tag) || e.quasi.some(p => walkExpression(p.exp));
			case 'import_call':			return e.arguments.some(walkExpression);
			case 'arrow':				return walkSig(e as TS.CallSig) || (Array.isArray(e.body) ? e.body.some(walkStatement) : walkExpression(e.body));
			case 'assign':				return walkExpression(e.target) || walkExpression(e.value);
			case 'await':
			case 'yield':				return walkExpression(e.operand);
			case 'class':				return walkExpression(e.superClass) || (e.body as TS.ClassMember[]).some(walkClassMember) || !!e.implements?.some(t => walkType(t as Type));
			case 'instantiation':		return walkExpression(e.expression) || e.typeArgs.some(t => walkType(t as Type));
			case 'as':
			case 'satisfies':			return walkExpression(e.expression) || walkType(e.typeAnnotation as Type);
			case 'jsx':					return e.attributes.some(p => walkExpression(p.value)) || e.children.some(walkExpression);
			case 'this':
			case 'super':
			case 'identifier':
			case 'import_meta':			return false;
		}
	};

	const statement = (stmt: TS.Stmt): boolean => {
		switch (stmt.type) {
			case 'block':				return stmt.body.some(walkStatement);
			case 'var_decl':			return stmt.declarations.some(walkVarDeclarator);
			case 'expression':			return walkExpression(stmt.expression);
			case 'if':					return walkExpression(stmt.test) || walkStatement(stmt.consequent) || (!!stmt.alternate && walkStatement(stmt.alternate));
			case 'do_while':
			case 'while':				return walkExpression(stmt.test) || walkStatement(stmt.body);
//			case 'for':					return (stmt.init ? (stmt.init.type === 'var_decl' ? stmt.init.declarations.some(walkVarDeclarator) : walkExpression(stmt.init)) : false)
			case 'for':					return (stmt.init ? (stmt.init.type === 'var_decl' ? walkStatement(stmt.init) : walkExpression(stmt.init)) : false)
				|| (stmt.kind === 'normal' ? (walkExpression(stmt.test) || walkExpression(stmt.update)) : walkExpression(stmt.right))
				|| walkStatement(stmt.body);
			case 'with':
			case 'throw':
			case 'return':				return walkExpression(stmt.argument);
			case 'labeled':				return walkStatement(stmt.body);
			case 'switch':				return walkExpression(stmt.discriminant)
				|| stmt.cases.some(c => walkExpression(c.test) || c.consequent.some(walkStatement));
			case 'try':					return stmt.body.some(walkStatement) || stmt.handlers.some(h => h.body.some(walkStatement)) || !!stmt.finalizer?.some(walkStatement);
			case 'function_decl':		return walkSig(stmt) || !!stmt.body?.some(walkStatement);
			case 'export':				return !!stmt.default && (isJsStatement(stmt.default) ? walkStatement(stmt.default) : walkExpression(stmt.default as JS.Expr));
			case 'export_decl':			return walkStatement(stmt.declaration);
			case 'class_decl':			return walkExpression(stmt.superClass)
				|| (stmt.body).some(walkClassMember)
				|| !!stmt.typeParams?.some(t => walkTypeParam(t))
				|| !!stmt.implements?.some(t => walkType(t));
			case 'type_alias_decl':		return !!stmt.typeParams?.some(walkTypeParam) || walkType(stmt.value);
			case 'interface_decl':		return !!stmt.typeParams?.some(walkTypeParam)
				|| !!stmt.extendsClause?.some(t => walkType(t))
				|| stmt.body.some(walkTypeMember);
			case 'enum_decl':			return stmt.members.some(m => walkExpression(m.init));
			case 'namespace_decl':		return stmt.body.some(walkStatement);
			default:					return false;
		}
	};

	const recurse: WalkerB = {
		statement:		x => walkStatement(x),
		expression:		x => walkExpression(x),
		type:			x => walkType(x),
		typeMember:		x => walkTypeMember(x),
		classMember:	x => walkClassMember(x),
		statements:		x => x.some(walkStatement),
		body:			x => Array.isArray(x) ? x.some(walkStatement) : walkExpression(x),
	};

	const walkStatement		= makeProcessB(statement, onStatement, recurse, true);
	const walkExpression	= makeProcessB(expression, onExpression, recurse);
	const walkTypeMember 	= makeProcessB(typeMember as ((x: TS.TypeMember|TS.ClassMember) => boolean), onTypeMember, recurse, true);
	const walkClassMember 	= makeProcessB(classMember as ((x: TS.TypeMember|TS.ClassMember) => boolean), onTypeMember, recurse, true);
	const walkType			= makeProcessB(type, onType, recurse);

	return recurse;
}
