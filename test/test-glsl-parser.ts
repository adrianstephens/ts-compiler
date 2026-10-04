import { glslParser } from '../dist/shaders/glsl-parser';
import { cParser } from '../dist/cpp/c-parser';

// Real GLSL-shaped inputs, each with a structural assertion. Unlike the older parser tests, a failure
// here sets the exit code -- a parser that silently stops accepting shaders must not look like a pass.

let failures = 0;

// Depth-first search for the first node of a given `type` (walks arrays and object fields; `pos` is a
// stamped source location, not a child).
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

// Every node of a given `type`, in traversal order.
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
		name: 'vertex: layout, struct, uniform block, constructor, invariant',
		code: `
#version 450 core
layout(location = 0) in vec3 position;
layout(location = 1) in vec3 normal;
layout(location = 0) out vec3 vNormal;

struct Light {
	vec3 position;
	float intensity;
	vec3 colors[4];
};

layout(std140, binding = 0) uniform Camera {
	mat4 viewProjection;
} camera;

invariant gl_Position;

void main() {
	Light light;
	light.position = position;
	vNormal = normal;
	gl_Position = camera.viewProjection * vec4(position, 1.0);
}
`,
		check: ast => {
			if (!find(ast, 'interface_block'))
				return 'no interface_block node';
			if (!find(ast, 'qualifier_decl'))
				return 'no qualifier_decl node (invariant gl_Position)';
			if (!find(ast, 'struct'))
				return 'no struct node';
			const ctor = find(ast, 'functional_cast');
			if (!ctor || ctor.target !== 'vec4')
				return `expected a vec4 functional_cast, got ${ctor && ctor.target}`;
			// `struct Light` must be registered by the time `Light light;` parses: a declaration whose
			// specifier's type is the RefType `Light` can only exist if the head-time registration ran.
			const declarations = collect(ast, 'declaration');
			if (!declarations.some(d => d.specifiers?.type?.name === 'Light'))
				return 'struct name Light was never registered as a type';
			return undefined;
		},
	},
	{
		name: 'fragment: precision, sampler, discard, swizzle, array decl',
		code: `
#version 300 es
precision highp float;
precision mediump int;

uniform sampler2D uTexture;
in vec2 vUv;
out vec4 fragColor;

void main() {
	vec4 texel = texture(uTexture, vUv);
	if (texel.a < 0.1)
		discard;
	vec4 base = texel.rgba;
	fragColor = vec4(base.rgb * 0.5, base.a);
	float m[4][4];
	for (int i = 0; i < 4; i++)
		for (int j = 0; j < 4; j++)
			m[i][j] = float(i * j);
}
`,
		check: ast => {
			if (!find(ast, 'precision'))
				return 'no precision node';
			if (!find(ast, 'discard'))
				return 'no discard node';
			if (!collect(ast, 'member').some(m => m.property === 'rgba'))
				return 'no .rgba swizzle member';
			return undefined;
		},
	},
	{
		name: 'compute: standalone layout, buffer block, unsized member array',
		code: `
#version 460
layout(local_size_x = 8, local_size_y = 8, local_size_z = 1) in;

layout(std430, binding = 0) buffer Data {
	float values[];
	uint count;
};

void main() {
	uint i = gl_GlobalInvocationID.x;
	values[i] = values[i] * 2.0;
	barrier();
}
`,
		check: ast => {
			const decl = find(ast, 'layout_decl');
			if (!decl)
				return 'no layout_decl node';
			if (!decl.layout || decl.layout.length !== 3)
				return `expected 3 layout items, got ${decl.layout && decl.layout.length}`;
			if (!find(ast, 'interface_block'))
				return 'no interface_block node (buffer Data)';
			// the unsized member `float values[];` must keep its array node
			if (!collect(ast, 'array').some(a => a.size === undefined))
				return 'no unsized array declarator (float values[])';
			return undefined;
		},
	},
	{
		name: 'control flow: for(;;), while, do, switch, ternary',
		code: `
void main() {
	int i = 0;
	for (;;) {
		i++;
		if (i > 10) break;
	}
	while (i > 0) { i--; }
	do { i++; } while (i < 5);
	switch (i) {
		case 0: i = 1; break;
		default: break;
	}
	int x = i > 0 ? 1 : -1;
}
`,
		check: ast => {
			for (const type of ['for', 'while', 'do_while', 'switch', 'conditional'])
				if (!find(ast, type))
					return `no '${type}' node`;
			return undefined;
		},
	},
	{
		name: 'parameter qualifiers and out params',
		code: `
void illuminate(in vec3 normal, inout vec3 color, out float attenuation) {
	attenuation = max(dot(normal, vec3(0.0, 1.0, 0.0)), 0.0);
	color *= attenuation;
}
`,
		check: ast => {
			if (!find(ast, 'function_def'))
				return 'no function_def node';
			return undefined;
		},
	},
	{
		name: 'scalar constructors from keyword types',
		code: `
float f(int i) {
	bool b = bool(i);
	uint u = uint(i);
	double d = double(i);
	return float(d) + float(u);
}
`,
		check: ast => {
			const targets = new Set<string>();
			(function visit(node: any) {
				if (!node || typeof node !== 'object')
					return;
				if (Array.isArray(node)) { node.forEach(visit); return; }
				if (node.type === 'functional_cast')
					targets.add(node.target);
				for (const key of Object.keys(node)) 
					if (key !== 'pos' && key !== 'scope')
						visit(node[key]);
			})(ast);
			for (const t of ['bool', 'uint', 'double', 'float'])
				if (!targets.has(t))
					return `missing '${t}' constructor (saw ${[...targets].join(', ')})`;
			return undefined;
		},
	},
];

let chain = Promise.resolve();
for (const c of cases) {
	chain = chain.then(async () => {
		try {
			const ast = await glslParser.parse(c.code);
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

// The built cParser tables were compiled before this file's pushes ran, so the plain C parser must still
// reject GLSL-only syntax (see this parser's header note on load order).
chain = chain.then(async () => {
	try {
		await cParser.parse('layout(location = 0) in vec3 position;');
		++failures;
		console.error('FAIL isolation: cParser accepted GLSL-only syntax after glsl-parser loaded');
	} catch {
		console.log('ok   isolation: cParser still rejects GLSL-only syntax');
	}
});

chain.then(() => {
	console.log(failures ? `\n${failures} failure(s)` : '\nall GLSL parser cases passed');
	process.exitCode = failures ? 1 : 0;
});
