import { slangParser } from '../dist/shaders/slang-parser';
import { hlslParser } from '../dist/shaders/hlsl-parser';
import { cParser } from '../dist/cpp/c-parser';
import * as CPP from '../dist/cpp/cpp-parser';

// Real Slang-shaped inputs with structural assertions; any failure sets the exit code. The last three cases
// check that loading this extension leaves every base parser intact (their tables were compiled before
// slang-parser's pushes ran).

let failures = 0;

function find(node: any, type: string): any | undefined {
	if (!node || typeof node !== 'object')
		return undefined;
	if (Array.isArray(node)) {
		for (const child of node) {
			const hit = find(child, type);
			if (hit)
				return hit;
		}
		return undefined;
	}
	if (node.type === type)
		return node;
	for (const key of Object.keys(node)) {
		if (key === 'pos' || key === 'scope')
			continue;
		const hit = find(node[key], type);
		if (hit)
			return hit;
	}
	return undefined;
}

function collect(node: any, type: string, out: any[] = []): any[] {
	if (!node || typeof node !== 'object')
		return out;
	if (Array.isArray(node)) {
		for (const child of node)
			collect(child, type, out);
		return out;
	}
	if (node.type === type)
		out.push(node);
	for (const key of Object.keys(node)) {
		if (key === 'pos' || key === 'scope')
			continue;
		collect(node[key], type, out);
	}
	return out;
}

interface Case { name: string; code: string; check: (ast: any) => string | undefined }

const cases: Case[] = [
	{
		name: 'interface: inheritance, associatedtype, methods',
		code: `
interface IBase {
	associatedtype U;
	U base();
};

interface IFoo : IBase {
	associatedtype T;
	T get();
	void set(T value);
};

struct Impl : IFoo {
	T get() { return T(); }
};

void use(IFoo f) { f.get(); }
`,
		check: ast => {
			const ifoo = collect(ast, 'interface').find(i => i.name === 'IFoo');
			if (!ifoo)
				return 'no interface IFoo';
			if (!ifoo.bases || ifoo.bases.length !== 1)
				return 'interface inheritance (: IBase) missing';
			const associated = collect(ast, 'associatedtype').map(a => a.name);
			for (const n of ['U', 'T'])
				if (!associated.includes(n))
					return `associatedtype ${n} missing (saw ${associated.join(',')})`;
			// `T get()` only parses if `associatedtype T` registered T as a type at head-reduce time.
			const getter = collect(ast, 'method').find(m => m.declarator && m.declarator.name && m.declarator.name.name === 'get');
			if (!getter)
				return 'no method `T get()` in the interface';
			if (!getter.specifiers || getter.specifiers.type.name !== 'T')
				return "method return type is not the associatedtype T";
			return undefined;
		},
	},
	{
		name: '__generic: constraints, where clause, non-type params, generic struct',
		code: `
interface IFoo { associatedtype T; T get(); };

__generic<T : IFoo> T first(T a, T b) { return a; }
__generic<T> T second(T x) where T : IFoo { return x.get(); }
__generic<T> struct Box { T value; };
__generic<typename T, int N> void fill(T x) where T : IFoo { }
`,
		check: ast => {
			const generics = collect(ast, 'generic_decl');
			if (generics.length !== 4)
				return `expected 4 generic declarations, got ${generics.length}`;
			const constrained = generics.find(g => g.params[0].name === 'T' && g.params[0].constraint);
			if (!constrained)
				return 'no `T : IFoo` constraint on a generic parameter';
			const withWhere = generics.find(g => g.where && g.where.length);
			if (!withWhere || withWhere.where[0].param !== 'T')
				return 'no `where T : IFoo` clause';
			const nonType = generics.find(g => g.params.some((p: any) => p.nonType));
			if (!nonType)
				return 'no non-type generic parameter (`int N`)';
			return undefined;
		},
	},
	{
		name: 'new-style generics: T f<T>(...) and float4 f<T>(...), with where',
		code: `
interface IFoo { associatedtype T; T get(); };

T identity<T>(T x) { return x; }
float4 scale<T>(float4 v) { return v; }
T constrained<T>(T x) where T : IFoo { return x; }
T proto<T>(T x);
`,
		check: ast => {
			const names = collect(ast, 'generic_decl')
				.map(g => find(g.declaration, 'function')?.name?.name)
				.filter(Boolean);
			for (const n of ['identity', 'scale', 'constrained', 'proto'])
				if (!names.includes(n))
					return `no generic function ${n} (saw ${names.join(',')})`;
			// `T identity<T>` -- the unregistered return type is a RefType T built by the rule, not a lexed type.
			const identity = collect(ast, 'generic_decl').find(g => find(g.declaration, 'function')?.name?.name === 'identity');
			if (!identity.declaration.specifiers || identity.declaration.specifiers.type.name !== 'T')
				return 'new-style generic return type T missing';
			return undefined;
		},
	},
	{
		name: 'extension, typealias, import',
		code: `
import my_library;
import "other.slang";
import a.b.c;

typealias MyInt = int;

struct Vec { float x; };
extension Vec {
	float length2() { return x * x; }
}
`,
		check: ast => {
			if (!find(ast, 'extension'))
				return 'no extension declaration';
			const alias = find(ast, 'typealias');
			if (!alias || alias.name !== 'MyInt')
				return 'no typealias MyInt';
			const modules = collect(ast, 'import').map(i => i.module);
			for (const m of ['my_library', 'other.slang', 'a.b.c'])
				if (!modules.includes(m))
					return `import ${m} missing (saw ${modules.join(',')})`;
			return alias.target && alias.target.specifiers ? undefined : 'typealias target missing';
		},
	},
	{
		name: 'let locals and ref parameter qualifiers',
		code: `
void addOne(ref int x, __ref float y) {
	x = x + 1;
}

float f(float4 v) {
	let float4 w = v;
	let k = 2.0;
	return w.x * k;
}
`,
		check: ast => {
			const lets = collect(ast, 'let');
			if (lets.length !== 2)
				return `expected 2 let declarations, got ${lets.length}`;
			if (!lets.some(l => l.specifiers && l.specifiers.type.name === 'float4'))
				return 'no explicitly-typed let';
			if (!lets.some(l => !l.specifiers))
				return 'no inferred let';
			if (!collect(ast, 'parameter').some(p => p.specifiers && p.specifiers.ref === true))
				return 'no `ref` parameter qualifier';
			return undefined;
		},
	},
	{
		name: '__target_switch / __stage_switch: labels grouped into cases',
		code: `
float4 pick(float4 a) {
	float4 r;
	__target_switch {
	case glsl:
		r = a * 2.0;
	case hlsl:
		r = a * 3.0;
	default:
		r = a;
	}
	return r;
}

void s() {
	__stage_switch {
	case vertex:
		int x = 1;
		x = x + 1;
	case fragment:
		int y = 2;
	}
}
`,
		check: ast => {
			const switches = collect(ast, 'target_switch');
			if (switches.length !== 2)
				return `expected 2 target switches, got ${switches.length}`;
			const target = switches.find(s => s.kind === '__target_switch');
			if (!target || target.cases.length !== 3)
				return `__target_switch should split into 3 cases, got ${target && target.cases.length}`;
			const labels = target.cases.map(c => c.labels && c.labels[0]);
			if (labels[0] !== 'glsl' || labels[1] !== 'hlsl' || labels[2] !== undefined)
				return `wrong case labels: ${JSON.stringify(labels)}`;
			const stage = switches.find(s => s.kind === '__stage_switch');
			if (!stage || stage.cases.length !== 2)
				return 'stage switch should have 2 cases';
			if (stage.cases[0].body.length !== 2)
				return 'multi-statement stage case body should keep both statements';
			return undefined;
		},
	},
	{
		name: 'HLSL-shaped Slang still works through the HLSL layer',
		code: `
struct VSOut { float4 pos : SV_Position; };
cbuffer C : register(b0) { float4x4 mvp; };
Texture2D tex : register(t0);
float4 main(VSOut i) : SV_Target { return mvp * i.pos; }
`,
		check: ast => {
			if (!find(ast, 'cbuffer'))
				return 'cbuffer lost';
			if (!collect(ast, 'semantic').some(s => s.name === 'SV_Target'))
				return 'function semantic lost';
			return undefined;
		},
	},
];

let chain = Promise.resolve();
for (const c of cases) {
	chain = chain.then(async () => {
		try {
			const ast = await slangParser.parse(c.code);
			const problem = c.check(ast);
			if (problem) {
				++failures;
				console.error(`FAIL ${c.name}: ${problem}`);
			} else {
				console.log(`ok   ${c.name}`);
			}
		} catch (e) {
			++failures;
			console.error(`FAIL ${c.name}: ${e instanceof Error ? e.message : e}`);
		}
	});
}

chain = chain.then(async () => {
	try {
		await cParser.parse('__generic<T> T f(T x) { return x; }');
		++failures;
		console.error('FAIL isolation: cParser accepted Slang-only syntax after slang-parser loaded');
	} catch {
		console.log('ok   isolation: cParser still rejects Slang-only syntax');
	}
	try {
		await hlslParser.parse('float4 f(float3 p) : SV_Target { return float4(p, 1.0); }');
		console.log('ok   isolation: hlsl-parser still parses HLSL');
	} catch (e) {
		++failures;
		console.error(`FAIL isolation: hlsl-parser broken after slang-parser loaded: ${e instanceof Error ? e.message : e}`);
	}
	try {
		await CPP.parse('struct P { int x; };\nint main() { return 0; }');
		console.log('ok   isolation: cpp-parser still parses plain C++');
	} catch (e) {
		++failures;
		console.error(`FAIL isolation: cpp-parser broken after slang-parser loaded: ${e instanceof Error ? e.message : e}`);
	}
});

chain.then(() => {
	console.log(failures ? `\n${failures} failure(s)` : '\nall Slang parser cases passed');
	process.exitCode = failures ? 1 : 0;
});
