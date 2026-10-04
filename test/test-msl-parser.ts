import { mslParser } from '../dist/shaders/msl-parser';
import { cParser } from '../dist/cpp/c-parser';
import * as CPP from '../dist/cpp/cpp-parser';

// Real MSL-shaped inputs with structural assertions; any failure sets the exit code. `[[...]]` attributes
// are lexer-skipped by cpp-parser.ts (so they leave no AST trace) -- the cases assert that the code around
// them still parses, which is the actual contract.

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
		name: 'vertex: stage qualifier, address spaces, [[...]] attributes',
		code: `
#include <metal_stdlib>
using namespace metal;

struct VertexIn {
	float3 position [[attribute(0)]];
	float3 normal   [[attribute(1)]];
};

struct VertexOut {
	float4 position [[position]];
	float3 normal;
};

vertex VertexOut vertex_main(VertexIn in [[stage_in]],
                             constant float4x4 &mvp [[buffer(1)]]) {
	VertexOut out;
	out.position = mvp * float4(in.position, 1.0);
	out.normal = in.normal;
	return out;
}
`,
		check: ast => {
			const fns = collect(ast, 'function_def');
			if (!fns.some(f => f.specifiers && f.specifiers.vertex === true))
				return 'no `vertex` stage qualifier on a function';
			if (!collect(ast, 'parameter').some(p => p.specifiers && p.specifiers.constant === true))
				return 'no `constant` address-space parameter';
			const ctor = find(ast, 'functional_cast');
			if (!ctor || ctor.target !== 'float4')
				return 'no float4 constructor';
			return undefined;
		},
	},
	{
		name: 'fragment: texture2d<...,access::read>, sampler, discard_fragment',
		code: `
using namespace metal;

fragment float4 fragment_main(constant float4 &color [[buffer(0)]],
                              texture2d<float, access::read> tex [[texture(0)]],
                              sampler s [[sampler(0)]],
                              float2 uv [[stage_in]]) {
	float4 c = tex.sample(s, uv);
	if (c.a < 0.1)
		discard_fragment();
	return c * color;
}
`,
		check: ast => {
			const generics = collect(ast, 'generic').map(g => g.name);
			if (!generics.includes('texture2d'))
				return `no texture2d<...> type (saw ${generics.join(',')})`;
			if (!collect(ast, 'member').some(m => m.property === 'sample'))
				return 'no .sample member call';
			const call = collect(ast, 'call').find(c => c.callee && c.callee.name === 'discard_fragment');
			if (!call)
				return 'no discard_fragment() call';
			return undefined;
		},
	},
	{
		name: 'kernel: threadgroup storage, threadgroup_barrier, qualified value',
		code: `
using namespace metal;

kernel void compute(texture2d<float, access::write> dst [[texture(0)]],
                    uint2 gid [[thread_position_in_grid]]) {
	threadgroup float tile[64];
	tile[0] = 1.0;
	threadgroup_barrier(mem_flags::mem_threadgroup);
	dst.write(float4(tile[0]), gid);
}
`,
		check: ast => {
			const fns = collect(ast, 'function_def');
			if (!fns.some(f => f.specifiers && f.specifiers.kernel === true))
				return 'no `kernel` qualifier';
			// `threadgroup float tile[64];` is a local declaration, not part of the function's specifiers.
			if (!collect(ast, 'declaration').some(d => d.specifiers && d.specifiers.threadgroup === true))
				return 'no `threadgroup` address space on a local declaration';
			const qualified = collect(ast, 'qualified').map(q => q.parts.join('::'));
			if (!qualified.includes('mem_flags::mem_threadgroup'))
				return `no mem_flags::mem_threadgroup value (saw ${qualified.join(',')})`;
			return undefined;
		},
	},
	{
		name: 'templates, array<T,N>, vec/matrix, half literals',
		code: `
using namespace metal;

template<typename T, int N>
struct Block { array<T, N> data; };

half4 H(half3 h) { return half4(h, 1.0h); }

kernel void k(device float *data [[buffer(0)]],
              constant Block<float, 4> &b [[buffer(1)]]) {
	vec<float, 4> v = float4(1.0);
	matrix<float, 4, 4> m;
	data[0] = v.x + m[0][0] + b.data[0];
}
`,
		check: ast => {
			const generics = collect(ast, 'generic').map(g => g.name);
			for (const g of ['array', 'vec', 'matrix'])
				if (!generics.includes(g))
					return `no ${g}<...> type (saw ${generics.join(',')})`;
			const half = collect(ast, 'literal').find(l => l.raw === '1.0h');
			if (!half)
				return 'no half literal (1.0h)';
			return undefined;
		},
	},
	{
		name: 'metal:: qualification',
		code: `
using namespace metal;

float4 Q(float4 v) { return metal::float4(v.xyz, 0.0); }
`,
		check: ast => {
			const qualified = collect(ast, 'qualified').map(q => q.parts.join('::'));
			if (!qualified.includes('metal::float4'))
				return `no metal::float4 (saw ${qualified.join(',')})`;
			return undefined;
		},
	},
];

let chain = Promise.resolve();
for (const c of cases) {
	chain = chain.then(async () => {
		try {
			const ast = await mslParser.parse(c.code);
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
		await cParser.parse('vertex float4 main0() { return float4(1.0); }');
		++failures;
		console.error('FAIL isolation: cParser accepted MSL-only syntax after msl-parser loaded');
	} catch {
		console.log('ok   isolation: cParser still rejects MSL-only syntax');
	}
	try {
		await CPP.parse('struct P { int x; };\nint main() { return 0; }');
		console.log('ok   isolation: cpp-parser still parses plain C++');
	} catch (e) {
		++failures;
		console.error(`FAIL isolation: cpp-parser broken after msl-parser loaded: ${e instanceof Error ? e.message : e}`);
	}
});

chain.then(() => {
	console.log(failures ? `\n${failures} failure(s)` : '\nall MSL parser cases passed');
	process.exitCode = failures ? 1 : 0;
});
