import { hlslParser } from '../dist/shaders/hlsl-parser';
import { cParser } from '../dist/cpp/c-parser';
import * as CPP from '../dist/cpp/cpp-parser';

// Real HLSL-shaped inputs with structural assertions; any failure sets the exit code. The last two cases
// check that loading this extension leaves the base parsers (whose tables were compiled before its pushes
// ran) intact.

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

/** The semantic name on a struct member / function, wherever it landed. */
const semantics = (ast: any) => collect(ast, 'semantic').map(s => s.name);

interface Case { name: string; code: string; check: (ast: any) => string | undefined }

const cases: Case[] = [
	{
		name: 'vertex: struct semantics, cbuffer, register bindings, return semantic',
		code: `
struct VSInput {
	float3 position : POSITION;
	float3 normal   : NORMAL;
};

struct VSOutput {
	float4 position : SV_Position;
	float3 normal   : NORMAL;
};

cbuffer Constants : register(b0) {
	float4x4 worldViewProj;
	float time;
};

Texture2D albedo : register(t0);
SamplerState albedoSampler : register(s0);

VSOutput VSMain(VSInput input) : SV_Position {
	VSOutput output;
	output.position = mul(worldViewProj, float4(input.position, 1.0));
	output.normal = input.normal;
	return output;
}
`,
		check: ast => {
			const cb = find(ast, 'cbuffer');
			if (!cb)
				return 'no cbuffer node';
			if (!cb.body || cb.body.length !== 2)
				return `expected 2 cbuffer members, got ${cb.body && cb.body.length}`;
			if (!cb.annotation || cb.annotation.type !== 'register' || cb.annotation.parts[0] !== 'b0')
				return 'cbuffer missing : register(b0) annotation';
			for (const s of ['POSITION', 'NORMAL', 'SV_Position'])
				if (!semantics(ast).includes(s))
					return `missing semantic ${s} (saw ${semantics(ast).join(',')})`;
			// `Texture2D albedo : register(t0);` -- a register annotation on a plain declaration.
			const registers = collect(ast, 'register').map(r => r.parts[0]);
			for (const r of ['b0', 't0', 's0'])
				if (!registers.includes(r))
					return `missing register ${r}`;
			const fn = find(ast, 'function_def');
			if (!fn || !fn.annotation || fn.annotation.name !== 'SV_Position')
				return 'function return semantic missing';
			const ctor = find(ast, 'functional_cast');
			if (!ctor || ctor.target !== 'float4')
				return 'no float4 constructor';
			return undefined;
		},
	},
	{
		name: 'compute: [numthreads] attribute, cast, dispatch-thread id',
		code: `
RWStructuredBuffer<float> output : register(u0);

[numthreads(8, 8, 1)]
void CSMain(uint3 id : SV_DispatchThreadID) {
	output[id.x] = (float)id.x * 0.5;
}
`,
		check: ast => {
			const attr = find(ast, 'attributed');
			if (!attr || attr.attributes[0].name !== 'numthreads')
				return 'no [numthreads] attribute wrapper';
			if (!attr.attributes[0].arguments || attr.attributes[0].arguments.length !== 3)
				return 'numthreads should carry 3 arguments';
			if (!find(ast, 'cast'))
				return 'no C-style cast (float)';
			return undefined;
		},
	},
	{
		name: 'fragment: discard, interpolation modifier',
		code: `
struct PSInput {
	float4 position : SV_Position;
	nointerpolation float3 normal : NORMAL;
	float2 uv : TEXCOORD0;
};

Texture2D tex : register(t0);
SamplerState samp : register(s0);

float4 PSMain(PSInput input) : SV_Target {
	if (input.uv.x < 0.0)
		discard;
	return tex.Sample(samp, input.uv);
}
`,
		check: ast => {
			if (!find(ast, 'discard'))
				return 'no discard node';
			const nointerp = collect(ast, 'struct_member').some(m => m.specifiers && m.specifiers.nointerpolation === true);
			if (!nointerp)
				return 'nointerpolation qualifier not recorded on a struct member';
			return undefined;
		},
	},
	{
		name: 'templates and generic vector/matrix types',
		code: `
template<typename T>
T Max(T a, T b) { return a > b ? a : b; }

StructuredBuffer<float4> data : register(t0);

float4 Load(uint i) {
	vector<float, 4> v = data[i];
	matrix<float, 4, 4> m;
	return mul(m, v);
}
`,
		check: ast => {
			if (!find(ast, 'template'))
				return 'no template declaration';
			const generics = collect(ast, 'generic').map(g => g.name);
			for (const g of ['vector', 'matrix'])
				if (!generics.includes(g))
					return `no ${g}<...> type (saw ${generics.join(',')})`;
			return undefined;
		},
	},
	{
		name: 'swizzle, loop, namespace, typedef, static const',
		code: `
typedef float4 Color;

namespace N {
	static const float k = 1.0;
}

Color Tint(Color c) {
	Color r = c.wzyx;
	for (int i = 0; i < 4; ++i)
		r[i] = c[i] * N::k;
	return r;
}
`,
		check: ast => {
			const swizzle = collect(ast, 'member').find(m => m.property === 'wzyx');
			if (!swizzle)
				return 'no .wzyx swizzle';
			if (!find(ast, 'namespace'))
				return 'no namespace';
			if (!find(ast, 'for'))
				return 'no for statement';
			return undefined;
		},
	},
];

let chain = Promise.resolve();
for (const c of cases) {
	chain = chain.then(async () => {
		try {
			const ast = await hlslParser.parse(c.code);
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

// The base parsers' tables were compiled before this file's pushes ran, so both must be unchanged.
chain = chain.then(async () => {
	try {
		await cParser.parse('cbuffer C : register(b0) { float4x4 m; };');
		++failures;
		console.error('FAIL isolation: cParser accepted HLSL-only syntax after hlsl-parser loaded');
	} catch {
		console.log('ok   isolation: cParser still rejects HLSL-only syntax');
	}
	try {
		await CPP.parse('struct P { int x; };\nint main() { return 0; }');
		console.log('ok   isolation: cpp-parser still parses plain C++');
	} catch (e) {
		++failures;
		console.error(`FAIL isolation: cpp-parser broken after hlsl-parser loaded: ${e instanceof Error ? e.message : e}`);
	}
});

chain.then(() => {
	console.log(failures ? `\n${failures} failure(s)` : '\nall HLSL parser cases passed');
	process.exitCode = failures ? 1 : 0;
});
