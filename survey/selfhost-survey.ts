// Whole-set, non-blocking self-hosting survey.
//
// The existing `selfhost-compile.ts` answers "does this one file compile?" and aborts at the first
// checker error, so only one layer of one file is ever visible at a time. This instead runs the whole
// self-hosting dependency set, never aborts, and attributes every failure to a specific declaration,
// so shared root causes across files show up side by side instead of as unrelated one-offs.
//
// Two stages per file:
//   1. checker  -- collect ALL error diagnostics; never throw.
//   2. codegen  -- probe each top-level declaration in isolation (export just that one, un-export the
//                  rest) so the first TSWError doesn't hide every later one. Records emitted function
//                  count, because "compiles" must mean "emitted something that runs", not "didn't throw".
//
// Run it through `selfhost-survey.sh`, which lists its modes. A full run fans its slices out over local workers; CI
// (.github/workflows/survey.yml) runs the same slices as matrix jobs: `--plan`, then `--worker` per slice, then `--merge`.

import path from 'path';
import fs from 'fs/promises';
import v8 from 'v8';
import os from 'os';
import { execFile, execFileSync } from 'child_process';
import { existsSync, readFileSync, readdirSync } from 'fs';
import { createHash } from 'crypto';
import * as TS from '../src/ts/ts-parser';
import * as T from '../src/ts/type-utils';
import { TStoWasm, LIB_AST } from '../src/ts/wasm-backend';
import { TStypeCheckAsync } from '../src/ts/transform';
import { ModuleLoader, collectModules } from '../src/ts/module-loader';
import { SEVERITY, makeLibScope } from '../src/ts/checker';
import type { Module } from '@isopodlabs/tison/ast';
import { siblingSourcePaths } from './sibling-paths';

v8.setFlagsFromString('--experimental-wasm-exnref');

const parser = TS.make();
const libScope = makeLibScope(LIB_AST);
const ROOT = path.resolve(__dirname, '../..');	// the packages root, where binary-libs/ and binary/ live
// The surveyed SOURCE is a frozen snapshot (`selfhost-snapshot.sh`), so a delta measures the compiler, not edits to its input;
// `--live` surveys the working tree instead. Files keep their logical names (`tison/src/core.ts`) either way.
const LIVE			= process.argv.includes('--live');
// A run's outputs (gitignored scratch by default) and the snapshot it surveys; paths are from the packages root, the cwd.
const OUT_ROOT		= path.resolve(process.env.SURVEY_OUT ?? 'compiler/assistant');
const SNAPSHOT		= path.resolve(process.env.SURVEY_SNAPSHOT ?? path.join(OUT_ROOT, 'selfhost-snapshot'));
const SOURCE_ROOT	= LIVE ? ROOT : SNAPSHOT;
const onDisk		= (file: string) => path.resolve(SOURCE_ROOT, file);

const TARGETS = [
	'tison/src/tison.ts',	// a re-export barrel since b1d5692 -- the declarations it held are in core.ts
	'tison/src/core.ts',	// grammar spec types, lexer, GrammarBuilder (b1d5692 broke the tison<->lalr cycle)
	'tison/src/lalr.ts',	// split out of tison.ts by 08ad816 -- the LR engine proper
	'tison/src/peg.ts',	// PEG back end over the same GrammarSpec (1e8e513)
	'compiler/src/ts/ts-parser.ts',
	'compiler/src/ts/js-parser.ts',
	'compiler/src/ts/type-core.ts',	// split out of type-utils.ts 2026-09-18
	'compiler/src/ts/type-utils.ts',
	'compiler/src/ts/printer.ts',	// type-utils.ts's typeKey/exprKey/stmtKey go through it -- on the critical path, added 2026-09-04
	'compiler/src/ts/checker.ts',
	'compiler/src/ts/transform.ts',
	'compiler/src/ts/wasm-backend.ts',	// was towasm.ts until 2026-09-17
	'compiler/src/ts/free-names.ts',	// the backend's free-variable analysis, moved out 2026-10-06 (shared with transform.ts)
	// The extracted component. It was invisible to the work queue until 2026-09-17: a declaration moved
	// out of a surveyed file read as "fixed" in the totals, which is a scope change, not progress.
	// `wasm-asm.ts` folded into it, and `TS/towasm-analysis.ts` folded back into the backend.
	'compiler/src/wasm/codegen.ts',
	'tison/src/walker.ts',
	'compiler/src/ts/walker.ts',
	'binary-libs/src/wasm.ts',
];

type Site = { file: string; decl: string; kind: string; stage: 'parse' | 'checker' | 'codegen'; pos?: string; message: string };

interface FileReport {
	file:			string;
	lines:			number;
	parseError?:	string;
	checkErrors:	Site[];
	probes:			{ decl: string; kind: string; ok: boolean; funcs: number; message?: string }[];
	sliceDecls?:	number;		// declarations this SLICE covered (absent for a whole-file run)
	sliceStart?:	number;		// the SLICE's first declaration, so the parent merges parts in order
	peakMb?:		number;		// a slice's peak RSS, from its worker
	ms?:			number;		// a slice's time, from its worker's start
	// Each slice's cost, kept on the merged report: the next run sizes and schedules this file's slices by it.
	slices?:		{ start: number; count: number; ms: number; mb: number }[];
	skipped:		{ decl: string; why: string }[];
	whole:			{ ok: boolean; funcs: number; message?: string };
}

function errText(e: unknown): string {
	// A `TSWError`'s own `msg` can be ANOTHER `TSWError` -- they nest as the error propagates out through
	// enclosing scopes -- so unwrap until a real string. Stopping at the first level fell through to
	// `String(any)` and the whole cluster rendered as "[object Object]", hiding every declaration that
	// shared it (24 of checker.ts's, in the run that turned this up). `.msg` rather than `.message`
	// throughout: the latter prepends position/scope noise that defeats clustering.
	let any = e as any;
	for (let i = 0; i < 8 && any && typeof any === 'object' && any.msg !== undefined; i++)
		any = any.msg;
	if (typeof any === 'string')
		return any;
	if (any instanceof Error)
		return any.message;
	if (any && typeof any === 'object' && typeof any.message === 'string')
		return any.message;
	return String(any);
}

// Two levels of grouping, deliberately.
//
// `cause` keeps the identifying name in the message ('resolveCache' needs ... vs 'body' needs ...) --
// that name IS the cause, so this is the work queue. Over-normalizing here merges unrelated causes into
// one row and makes a handful of blocked module-level declarations look like a hundred separate bugs.
//
// `shape` throws the names away, and is only ever a hint that two causes MIGHT share a root -- never a
// count of distinct problems.
function cause(msg: string): string {
	if (!msg) return '(no message)';
	return msg.replace(/\s+/g, ' ').replace(/ in '[\s\S]*$/, '').replace(/\{[\s\S]*?\}/g, '{...}').trim();
}

function shape(msg: string): string {
	return cause(msg).replace(/'[^']*'/g, "'X'").replace(/\b\d+\b/g, 'N');
}

const declName = (d: any): string | undefined => typeof d?.name === 'string' ? d.name : undefined;
const isProbeable = (d: any) => d && (d.type === 'function_decl' || d.type === 'class_decl');

// One variant program per top-level declaration: that declaration exported, every other function/class
// un-exported. Only *exported* non-generic top-level functions are compiled eagerly by TStoWasm, so this
// is what forces one specific declaration (and its transitive callees) through codegen on its own.
function variantBody(body: TS.Statement[], target: string): TS.Statement[] {
	return body.map(s => {
		const inner = s.type === 'export_decl' ? (s as any).declaration : s;
		if (!isProbeable(inner))
			return s;
		const name = declName(inner);
		if (name === target)
			return s.type === 'export_decl' ? s : ({ type: 'export_decl', declaration: inner } as any);
		return s.type === 'export_decl' ? inner : s;
	});
}

let reusedProgram: Module<TS.Stmt> | undefined;		// DBG_REUSE: same AST every probe, to separate per-parse from per-check retention

// The imported modules a check resolves against: parsed, scoped (`memo`, `.scope`) and codegen-checked (`checkImported`) on their
// own records, which live in `loader` and chain to `global`. Every stamp there is first-wins and the same for any entry.
type Imports = { loader: ModuleLoader; global: T.Scope };
const newImports = (file: string): Imports => ({
	loader:	new ModuleLoader(path.dirname(file), { paths: siblingSourcePaths(path.dirname(file), SOURCE_ROOT) }),
	global:	new T.Scope(process.env.DBG_FRESHLIB ? makeLibScope(LIB_AST) : libScope),
});

async function checkOnce(file: string, imports = newImports(file)) {
	const src		= await fs.readFile(file, 'utf8');
	const program	= process.env.DBG_REUSE ? (reusedProgram ??= parser.parse(src)) : parser.parse(src);
	// The entry's own `__filename`/`__dirname`, stamped the way the checker stamps `.scope`.
	program.filename = file;
	const diags		= process.env.DBG_NOCHECK ? [] : await TStypeCheckAsync(program, imports.loader, imports.global);
	return { program, loader: imports.loader, diags };
}

async function codegen(program: Module<TS.Stmt>, loader: ModuleLoader, body: TS.Statement[]) {
	const variant = { ...program, body } as Module<TS.Stmt>;
	const { modules } = await collectModules(body, loader);
	// A failing module-level statement is that statement's own problem: it used to take every other
	// declaration in the file down with it (one start function for all of them), which is what made a
	// single unrepresentable `const` look like ~35 separate blocked declarations.
	const topLevelErrors: unknown[] = [];
	const mod = TStoWasm(variant, modules, e => topLevelErrors.push(e));
	return Math.max(0, (mod.code?.length ?? 0) - 1);	// minus the always-present, often-empty `__toplevel`
}

async function survey(file: string, wholeOnly: boolean, slice?: { start: number; count: number }): Promise<FileReport> {
	const abs		= onDisk(file);
	const src		= await fs.readFile(abs, 'utf8');
	const report: FileReport = {
		file, lines: src.split('\n').length,
		checkErrors: [], probes: [], skipped: [], whole: { ok: false, funcs: 0 },
	};

	// A survey must never die on its subject: this repo is refactored while surveys run, so the parser
	// itself can be mid-change. A file that won't parse is a finding, not a crash.
	let first;
	try {
		first = await checkOnce(abs);
	} catch (e) {
		report.parseError = errText(e);
		return report;
	}
	for (const d of first.diags.filter(d => d.severity === SEVERITY.ERROR))
		report.checkErrors.push({ file, decl: '-', kind: '-', stage: 'checker', pos: `${d.pos.line}:${d.pos.col}`, message: d.message });

	// Stage 2a: the whole file as-is -- what `selfhost-compile.ts` measures today, kept for comparison.
	// Only the first slice does it: every slice would otherwise repeat the same whole-file compile.
	if (slice && slice.start > 0) {
		report.whole = { ok: false, funcs: 0, message: 'not run in this slice' };
	} else try {
		report.whole = { ok: true, funcs: await codegen(first.program, first.loader, first.program.body) };
	} catch (e) {
		report.whole = { ok: false, funcs: 0, message: errText(e) };
	}
	if (wholeOnly)
		return report;

	// Stage 2b: one declaration at a time. The ENTRY is re-parsed and re-checked per variant -- TStoWasm stamps it, and it is
	// what varies. Its imports are shared by the slice's probes (not with `first`, whose whole-file compile a slice 0 alone runs).
	const decls = probeable(first.program.body);

	// A slice bounds how many probes one process does: each probe re-checks the whole file, and 113 of them
	// (type-utils) exhausted an 8GB heap and left the file unmeasured. The parent merges the parts.
	const sliced = slice ? decls.slice(slice.start, slice.count ? slice.start + slice.count : undefined) : decls;
	if (slice) {
		report.sliceDecls = sliced.length;
		report.sliceStart = slice.start;
	}
	const imports = newImports(abs);
	for (const d of sliced) {
		const name = declName(d);
		if (!name)
			continue;
		if (d.type === 'function_decl' && !d.body) {
			report.skipped.push({ decl: name, why: 'ambient (no body)' });
			continue;
		}
		if (d.typeParams?.length) {
			// Generic: no single physical function to eagerly compile. Unreachable without a real call
			// site -- this is exactly why walker.ts "compiles" to an empty module.
			report.skipped.push({ decl: name, why: 'generic -- needs a concrete driver' });
			continue;
		}
		if (process.env.DBG_GC)
			(global as { gc?: () => void }).gc?.();
		if (process.env.DBG_MEM) {
			const m = process.memoryUsage();
			process.stderr.write(`  MEM ${(m.heapUsed / 1048576).toFixed(0)}MB heap ${(m.rss / 1048576).toFixed(0)}MB rss before ${name}\n`);
		}
		try {
			const fresh	= await checkOnce(abs, process.env.DBG_FRESHIMPORTS ? undefined : imports);
			const funcs	= process.env.DBG_NOCODEGEN ? 0 : await codegen(fresh.program, fresh.loader, variantBody(fresh.program.body, name));
			report.probes.push({ decl: name, kind: d.type, ok: true, funcs });
		} catch (e) {
			report.probes.push({ decl: name, kind: d.type, ok: false, funcs: 0, message: errText(e) });
		}
	}
	return report;
}

function groupBy(sites: Site[], key: (m: string) => string) {
	const by = new Map<string, Site[]>();
	for (const s of sites) {
		const k = key(s.message);
		(by.get(k) ?? by.set(k, []).get(k)!).push(s);
	}
	return [...by.entries()].sort((a, b) => b[1].length - a[1].length);
}
const clusters = (sites: Site[]) => groupBy(sites, cause);

const OUT_DIR	= path.join(OUT_ROOT, 'selfhost-survey');
const AGG_FILE	= path.join(OUT_ROOT, 'selfhost-survey.json');
const PREV_FILE	= path.join(OUT_ROOT, 'selfhost-survey.prev.json');
const PLAN_FILE	= path.join(OUT_ROOT, 'selfhost-survey.plan.json');

// What each declaration is failing on, keyed by file+name -- the unit the delta below is computed over.
type DeclState = Map<string, string>;	// "file::decl" -> cause, or '' when it compiles
function declStates(reports: FileReport[]): DeclState {
	const m: DeclState = new Map();
	for (const r of reports)
		for (const p of r.probes)
			m.set(`${r.file}::${p.decl}`, p.ok ? '' : cause(p.message ?? ''));
	return m;
}

// The only honest read of a run that leaves `compiled` flat. `moved` is the real signal: a declaration
// still failing, but on a DIFFERENT cause, got past a wall. A lever worth taking moves many; one that
// moves a single declaration fixed a symptom, not a cause -- which is exactly the judgement the plan
// memory asks for and nothing measured until now.
function renderDelta(prev: DeclState, now: DeclState) {
	const fixed: string[] = [], moved: string[] = [], broke: string[] = [], added: string[] = [];
	for (const [key, cur] of now) {
		const was = prev.get(key);
		if (was === undefined)			added.push(key);
		else if (was === cur)			continue;
		else if (cur === '')			fixed.push(key);
		else if (was === '')			broke.push(key);
		else							moved.push(key);
	}
	const gone = [...prev.keys()].filter(k => !now.has(k));
	const show = (label: string, keys: string[], cap = 6) => keys.length
		? `- **${label}: ${keys.length}** -- ${keys.slice(0, cap).map(k => k.split('::')[1]).join(', ')}${keys.length > cap ? `, +${keys.length - cap} more` : ''}`
		: undefined;
	const lines = [
		show('newly compile', fixed),
		show('moved to a new cause', moved, 10),
		show('REGRESSED (compiled before)', broke),
		show('newly probeable', added),
		show('no longer probed', gone),
	].filter(Boolean);
	return lines.length ? lines.join('\n') : '- nothing changed since the previous run';
}

// These numbers are only meaningful against a specific tree. This repo is worked on directly while
// surveys run, so a report with no provenance is worse than none -- a stale baseline read as current
// sends the next reader chasing failures that are really someone's in-flight edits.
// What was surveyed: the snapshot's revisions, or 'live'.
function sourceRevs(): string {
	if (LIVE)
		return 'live';
	const snap = JSON.parse(readFileSync(path.join(SNAPSHOT, 'SNAPSHOT.json'), 'utf8')) as Record<string, string>;
	return Object.entries(snap).filter(([k]) => k !== 'taken').map(([k, v]) => `${k}@${v}`).join(' ');
}

const git = (...a: string[]) => {
	try { return execFileSync('git', a, { cwd: path.resolve('compiler'), encoding: 'utf8' }).trim(); }
	catch { return '?'; }
};

// Workers load the compiler from disk when THEY start, so a run is only one compiler if `compiler/src` is the same at its start and end.
// A baseline taken while `src/` changed (2026-09-21: 3 commits and 8 dirty files mid-run) reported 52 false regressions against it.
function compilerState() {
	const src	= path.resolve('compiler/src');
	const hash	= createHash('sha1');
	for (const f of (readdirSync(src, { recursive: true }) as string[]).filter(f => f.endsWith('.ts')).sort())
		hash.update(f).update(readFileSync(path.join(src, f)));
	return { head: git('rev-parse', '--short', 'HEAD'), srcHash: hash.digest('hex').slice(0, 12), dirty: git('status', '--short').split('\n').filter(Boolean) };
}
type CompilerState = ReturnType<typeof compilerState>;
type Provenance = ReturnType<typeof provenance>;

function provenance(start: CompilerState) {
	const end = compilerState();
	return {
		head: end.head, subject: git('log', '-1', '--format=%s'), when: new Date().toISOString(), source: sourceRevs(),
		dirty:	end.dirty,
		// `dirty` paths under `src/` are uncommitted compiler: the run measured a tree no commit has.
		dirtySrc: end.dirty.filter(l => l.slice(3).startsWith('src/')),
		stable:	start.srcHash === end.srcHash,
		atStart: start,
		srcHash: end.srcHash,
	};
}

// Why a run can't serve as a baseline, or undefined when it can. An old-format provenance (no `stable`) can't show it was one.
const unreliable = (p: Partial<Provenance> | undefined) =>
	!p || p.stable === undefined	? 'it predates compiler-change tracking'
	: !p.stable						? `\`compiler/src\` changed while it ran (\`${p.atStart?.head}\` -> \`${p.head}\`)`
	: p.dirtySrc?.length			? `it measured ${p.dirtySrc.length} uncommitted compiler file(s): ${p.dirtySrc.map(l => l.slice(3)).join(', ')}`
	: undefined;

// One child process per file, so one slice's cached compiler state cannot reach another. A probe itself
// retains nothing -- heap after a forced GC is flat (~0.56GB) over 24 backend.ts probes and each probe's
// program is collected -- so a slice is bounded by WORKER_HEAP_MB, not by how many declarations it covers.
const workerFailures: string[] = [];
const SLICE = +(process.env.SURVEY_SLICE ?? 24);

// Every file runs as slices, each its own worker, drawn by a pool -- so a big file (backend.ts) spreads across workers,
// and each probe re-checking the whole file stays within one heap. Scheduled from the previous run's per-slice costs:
// a slice is sized to take about SLICE_MS, the longest go first, and a job starts only while the recorded peaks of
// those running fit MEM_BUDGET (40% of RAM, `SURVEY_MEM_GB` overrides) -- the machine is shared with other work.
const SLICE_MS	= +(process.env.SURVEY_SLICE_S ?? 300) * 1000;
const MEM_BUDGET	= +(process.env.SURVEY_MEM_GB ?? os.totalmem() / 1e9 * 0.4) * 1024;
// A wasm-backend.ts probe keeps ~2.1GB after GC (its imports' checks ~1.05GB, the entry's ~1.05GB), so 2048 OOMs every slice.
const WORKER_HEAP_MB	= +(process.env.SURVEY_HEAP_MB ?? 6144);
const MAX_JOBS	= +(process.env.SURVEY_JOBS ?? Math.max(1, os.cpus().length - 2));

type Slice = { file: string; start: number; count: number; ms: number; mb: number };

// The declarations a probe can target, as a slice counts them
const probeable = (body: TS.Statement[]) => body.map(s => s.type === 'export_decl' ? (s as any).declaration : s).filter(isProbeable);

// Every slice of `targets`, from their declarations as parsed. Sized from each file's previous report to take about SLICE_MS,
// and costed by its recorded peak. A file's last slice runs to its end: checking can add declarations (lifted class heritage).
async function planSlices(targets: string[]): Promise<Slice[]> {
	const previous	= new Map<string, FileReport>();
	for (const file of targets)
		await fs.readFile(reportPathFor(file), 'utf8').then(t => previous.set(file, JSON.parse(t))).catch(() => {});
	const seenMb	= Math.max(1024, ...[...previous.values()].flatMap(r => r.slices?.map(x => x.mb) ?? []));
	const slices	= await Promise.all(targets.map(async file => {
		const decls	= probeable(parser.parse(await fs.readFile(onDisk(file), 'utf8')).body).length;
		const r		= previous.get(file);
		const ms	= r?.slices?.reduce((n, x) => n + x.ms, 0);
		const done	= r ? r.probes.length + r.skipped.length : 0;
		const perDecl	= ms && done ? ms / done : undefined;
		const count	= perDecl ? Math.max(2, Math.min(SLICE, Math.round(SLICE_MS / perDecl))) : SLICE;
		// Memory grows with the probes a slice runs, so a smaller slice scales its recorded peak down, over a 1 GB floor for
		// checking the file at all. A file with no history is costed at the worst peak seen, in full-size slices until it has some.
		const worst	= r?.slices?.length ? r.slices.reduce((a, b) => b.mb > a.mb ? b : a) : undefined;
		// Never below half the heap cap: garbage piles up to about that whatever a slice recorded (8 x 6144 swapped a 16 GB Mac).
		const mb	= Math.max(WORKER_HEAP_MB / 2, worst ? Math.min(worst.mb, 1024 + Math.round(worst.mb * count / Math.max(1, worst.count))) : seenMb);
		const n		= Math.max(1, Math.ceil(decls / count));
		return Array.from({length: n}, (_, i) => ({file, start: i * count, count: i === n - 1 ? 0 : count, ms: (perDecl ?? 1e6) * count, mb}));
	}));
	return slices.flat();
}

// A file's report from its slices' parts (in any order); each part's time and peak kept as the next plan's history
async function mergeParts(file: string, parts: FileReport[]) {
	parts.sort((a, b) => (a.sliceStart ?? 0) - (b.sliceStart ?? 0));
	await fs.writeFile(reportPathFor(file), JSON.stringify({ ...parts[0], sliceDecls: undefined, sliceStart: undefined, peakMb: undefined, ms: undefined,
		probes: parts.flatMap(p => p.probes), skipped: parts.flatMap(p => p.skipped),
		slices: parts.map(p => ({ start: p.sliceStart ?? 0, count: p.sliceDecls ?? 0, ms: p.ms ?? 0, mb: p.peakMb ?? 0 })) }, null, '\t'));
}

// A crashed slice leaves its file UNMEASURED, loudly: stale numbers read as "this fix changed nothing".
async function markCrashed(file: string) {
	workerFailures.push(file);
	await fs.writeFile(reportPathFor(file), JSON.stringify({
		file, lines: 0, checkErrors: [], probes: [], skipped: [], whole: { ok: false, funcs: 0 },
		parseError: 'WORKER CRASHED (not measured)',
	}, null, '\t'));
}

// Merges the parts a planned run left (`--plan`, then a `--worker` per slice): a file with any slice's part missing crashed.
async function mergePlanned() {
	const plan = JSON.parse(await fs.readFile(PLAN_FILE, 'utf8')) as Slice[];
	for (const file of new Set(plan.map(s => s.file))) {
		const paths = plan.filter(s => s.file === file).map(s => partPathFor(file, s.start));
		const parts = await Promise.all(paths.map(p => fs.readFile(p, 'utf8').then(t => JSON.parse(t) as FileReport, () => undefined)));
		if (parts.every(p => p))
			await mergeParts(file, parts.filter((p): p is FileReport => !!p));
		else
			await markCrashed(file);
		await Promise.all(paths.map(p => fs.unlink(p).catch(() => {})));
	}
}

async function runPool(targets: string[], wholeOnly: boolean): Promise<void> {
	const queue: Slice[] = wholeOnly
		? targets.map(file => ({ file, start: 0, count: 0, ms: 0, mb: WORKER_HEAP_MB / 2 }))
		: await planSlices(targets);
	const parts		= new Map<string, FileReport[]>();
	const crashed	= new Set<string>();
	let runningMb	= 0, running = 0;
	await new Promise<void>(done => {
		const pump = () => {
			// Longest first, so the slowest file is not the tail; the first job always runs, whatever its estimate.
			queue.sort((a, b) => b.ms - a.ms);
			for (let i = 0; i < queue.length && running < MAX_JOBS; ) {
				if (running && runningMb + queue[i].mb > MEM_BUDGET) {
					i++;
					continue;
				}
				const job = queue.splice(i, 1)[0];
				running++;
				runningMb += job.mb;
				void run(job).then(() => {
					running--;
					runningMb -= job.mb;
					pump();
				});
			}
			if (!running && !queue.length)
				done();
		};
		pump();
	});

	async function run(job: Slice) {
		const slice	= wholeOnly ? undefined : { start: job.start, count: job.count };
		const ok	= await runWorker(job.file, wholeOnly, slice);
		if (!ok) {
			crashed.add(job.file);
		} else if (slice) {
			const part = JSON.parse(await fs.readFile(partPathFor(job.file, slice.start), 'utf8')) as FileReport;
			await fs.unlink(partPathFor(job.file, slice.start)).catch(() => {});
			(parts.get(job.file) ?? parts.set(job.file, []).get(job.file)!).push(part);
		}
	}

	for (const [file, got] of wholeOnly ? [] : parts)
		if (!crashed.has(file))
			await mergeParts(file, got);
	for (const file of wholeOnly ? [] : crashed)
		await markCrashed(file);
}

const reportPathFor = (file: string) => path.join(OUT_DIR, path.basename(path.dirname(file)) + '.' + path.basename(file, '.ts') + '.json');

const partPathFor = (file: string, start: number) => reportPathFor(file).replace(/\.json$/, `.part${start}.json`);

function runWorker(file: string, wholeOnly: boolean, slice?: { start: number; count: number }): Promise<boolean> {
	const args = [
		`--max-old-space-size=${WORKER_HEAP_MB}`, '-r', 'ts-node/register/transpile-only',
		__filename, '--worker', file,
		...(wholeOnly ? ['--whole'] : []),
		...(LIVE ? ['--live'] : []),
		...(slice ? ['--slice', `${slice.start}:${slice.count}`] : []),
	];
	const t0 = Date.now();
	return new Promise(resolve => {
		let fatal = '';
		const child = execFile(process.execPath, args, {
			cwd: path.resolve('.'),
			maxBuffer: 1 << 28,
			env: { ...process.env, TS_NODE_COMPILER_OPTIONS: '{"module":"commonjs","target":"es2022","rootDir":".","ignoreDeprecations":"6.0"}' },
		}, async err => {
			if (err) {
				process.stderr.write(`  worker for ${file} exited: ${fatal || err.message.split('\n')[0]}\n`);
				// A crashed worker must NOT leave the previous run's JSON in place: the aggregate renders from
				// disk, so stale numbers would read as "this fix changed nothing" -- which is exactly how a whole
				// session's movement went unnoticed once. Replace it with a loud, unmeasured report instead.
				if (!slice)
					await markCrashed(file);
			}
			process.stderr.write(`  ${file}${slice ? ` [${slice.start}+${slice.count || 'rest'}]` : ''}: ${((Date.now() - t0) / 1000).toFixed(0)}s${err ? ' CRASHED' : ''}\n`);
			resolve(!err);
		});
		child.stderr?.on('data', d => {
			const lines = String(d).split('\n');
			fatal ||= lines.find(l => l.startsWith('FATAL ERROR')) ?? '';
			process.stderr.write(lines.filter(l => l.startsWith('  ')).map(l => l + '\n').join(''));
		});
	});
}

(async () => {
	const args		= process.argv.slice(2);
	const wholeOnly	= args.includes('--whole');
	const workerIdx	= args.indexOf('--worker');
	const files		= args.filter((a, i) => !a.startsWith('--') && !(workerIdx >= 0 && i === workerIdx + 1));

	await fs.mkdir(OUT_DIR, { recursive: true });
	if (!LIVE && !existsSync(path.join(SNAPSHOT, 'SNAPSHOT.json'))) {
		process.stderr.write(`no source snapshot at ${SNAPSHOT}: run compiler/survey/selfhost-snapshot.sh first, or pass --live to survey the working tree\n`);
		process.exitCode = 1;
		return;
	}

	if (workerIdx >= 0) {
		const file = args[workerIdx + 1];
		const sliceIdx = args.indexOf('--slice');
		const slice = sliceIdx >= 0 ? { start: +args[sliceIdx + 1].split(':')[0], count: +args[sliceIdx + 1].split(':')[1] } : undefined;
		const report = await survey(file, wholeOnly, slice);
		report.peakMb	= Math.round(process.resourceUsage().maxRSS / 1024);
		report.ms		= Math.round(process.uptime() * 1000);
		await fs.writeFile(slice ? partPathFor(file, slice.start) : reportPathFor(file), JSON.stringify(report, null, '\t'));

		return;
	}

	// `--aggregate` re-renders the tables from the per-file JSON already on disk, without re-running
	// the workers -- a 10-minute run should not have to be repeated to fix a reporting bug.
	// Snapshotted BEFORE the workers overwrite anything, so the run can report what MOVED. Without this
	// a session that clears a wall for thirty declarations and one that fixes a single symptom look
	// identical -- both leave `compiled` flat, because blockers are serial and a declaration reads
	// "failed" whether eight or three of them remain.
	const start		= compilerState();
	const targets	= files.length ? files : TARGETS;
	// `--plan` lists the slices a run would start, for CI to fan out; it writes PLAN_FILE for `--merge` to check the parts against.
	if (args.includes('--plan')) {
		const plan = await planSlices(targets);
		await fs.writeFile(PLAN_FILE, JSON.stringify(plan, null, '\t'));
		console.log(JSON.stringify(plan.map(({ file, start, count }) => ({ file, start, count }))));
		return;
	}
	if (!args.includes('--aggregate')) {
		try { await fs.copyFile(AGG_FILE, PREV_FILE); } catch { /* first run, or no previous aggregate */ }
		// Reports are kept ACROSS runs on purpose (planning reads one to size a file's slices),
		// but a file that is no longer a TARGET must not keep contributing a row. Pruned only on a
		// whole-TARGETS run: a subset run (`selfhost-survey.sh one.ts`) must not discard every other report.
		if (!files.length)
			await pruneReports(new Set(TARGETS.map(reportPathFor)));
		if (args.includes('--merge')) {
			await mergePlanned();
		} else {
			process.stderr.write(`surveying ${targets.length} files: up to ${MAX_JOBS} workers within ${(MEM_BUDGET / 1024).toFixed(1)} GB ...\n`);
			await runPool(targets, wholeOnly);
		}
	}

	// Drops the per-file reports of files this run does not survey. A stale one otherwise renders as a
	// PHANTOM row: when `TS/towasm-asm.ts` was folded away, its old JSON kept reporting a deleted file's
	// declarations -- and their failures and causes -- in the totals.
	async function pruneReports(keep: Set<string>) {
		for (const name of await fs.readdir(OUT_DIR))
			if (name.endsWith('.json') && !/\.part\d+\.json$/.test(name) && !keep.has(path.join(OUT_DIR, name)))
				await fs.rm(path.join(OUT_DIR, name), { force: true });
	}

	const reports: FileReport[] = [];
	// `.partN.json` are a sliced run's intermediates -- they are merged into the file's own report and unlinked, but a
	// manual or interrupted slice can leave one behind, and counting it would add a phantom row for the same file.
	for (const name of (await fs.readdir(OUT_DIR)).filter(n => n.endsWith('.json') && !/\.part\d+\.json$/.test(n)).sort())
		reports.push(JSON.parse(await fs.readFile(path.join(OUT_DIR, name), 'utf8')));

	const all: Site[] = [];
	for (const r of reports) {
		// A file that didn't parse has no checker/codegen findings to report -- and `whole` is still the
		// unset initial value, so pushing it here yields a message-less Site that breaks grouping.
		if (r.parseError) {
			all.push({ file: r.file, decl: '<file>', kind: '-', stage: 'parse', message: 'DOES NOT PARSE: ' + r.parseError });
			continue;
		}
		all.push(...r.checkErrors);
		for (const p of r.probes)
			if (!p.ok && p.message)
				all.push({ file: r.file, decl: p.decl, kind: p.kind, stage: 'codegen', message: p.message });
		if (!r.whole.ok && !r.probes.length && r.whole.message)
			all.push({ file: r.file, decl: '<whole file>', kind: '-', stage: 'codegen', message: r.whole.message });
	}

	// `--aggregate` re-renders an earlier run, so it keeps that run's provenance rather than describing the tree now.
	const prov: Provenance = args.includes('--aggregate') ? JSON.parse(await fs.readFile(AGG_FILE, 'utf8')).provenance : provenance(start);
	const notBaseline = unreliable(prov);
	console.log(`# Self-hosting survey\n`);
	console.log(`Compiler: tison HEAD \`${prov.head}\` (${prov.subject})${prov.dirty?.length ? ` — ${prov.dirty.length} uncommitted files` : ' — clean tree'}, ${prov.when}\n`);
	if (notBaseline)
		console.log(`**NOT A BASELINE**: ${notBaseline}. These numbers describe no single commit, so the next run's delta against them won't either.\n`);
	console.log(prov.source === 'live' ? 'Source: **the LIVE tree** (`--live`) -- deltas mix compiler progress with source edits\n' : `Source: snapshot \`${prov.source}\`\n`);
	console.log('## Per-file status\n');
	console.log('| file | lines | checker errs | probed | compiled | failed | distinct causes | not probeable | whole-file funcs |');
	console.log('|---|---|---|---|---|---|---|---|---|');
	for (const r of reports) {
		const ok		= r.probes.filter(p => p.ok).length;
		const distinct	= new Set(r.probes.filter(p => !p.ok).map(p => cause(p.message!))).size;
		if (r.parseError) {
			console.log(`| ${r.file} | ${r.lines} | **does not parse** | - | - | - | - | - | - |`);
			continue;
		}
		console.log(`| ${r.file} | ${r.lines} | ${r.checkErrors.length} | ${r.probes.length} | ${ok} | ${r.probes.length - ok} | ${distinct} | ${r.skipped.length} | ${r.whole.ok ? r.whole.funcs : 'fails'} |`);
	}

	// Ranked by declarations unblocked -- this is the work queue. A row's count is how many probes that ONE
	// cause blocks, not how many separate problems it is; a single module-level declaration routinely blocks
	// every probe in its file (and, via imports, in several others).
	console.log('\n## Causes, ranked by declarations unblocked\n');
	console.log('| blocks | files | cause |');
	console.log('|---|---|---|');
	for (const [k, sites] of clusters(all)) {
		const fileSet	= [...new Set(sites.map(s => path.basename(s.file)))];
		const fileList	= fileSet.length > 3 ? `${fileSet.slice(0, 3).join(', ')} +${fileSet.length - 3}` : fileSet.join(', ');
		console.log(`| ${sites.length} | ${fileList} | ${k.slice(0, 130)} |`);
	}

	console.log('\n## Shapes (hint only -- two causes sharing a shape MAY share a root, verify before assuming)\n');
	console.log('| blocks | distinct causes | shape |');
	console.log('|---|---|---|');
	for (const [k, sites] of groupBy(all, shape))
		console.log(`| ${sites.length} | ${new Set(sites.map(s => cause(s.message))).size} | ${k.slice(0, 130)} |`);

	const probed	= reports.reduce((n, r) => n + r.probes.length, 0);
	const compiled	= reports.reduce((n, r) => n + r.probes.filter(p => p.ok).length, 0);
	const skipped	= reports.reduce((n, r) => n + r.skipped.length, 0);
	const noParse	= reports.filter(r => r.parseError).length;
	console.log(`\n## Totals\n`);
	console.log(`- ${compiled}/${probed} top-level declarations compile in isolation; ${skipped} more need a driver to be measurable at all`);
	console.log(`- ${noParse}/${reports.length} target files do not parse at all`);
	console.log(`- ${all.length} failures, from ${clusters(all).length} distinct causes`);

	// Diffed against the previous run's aggregate (`selfhost-survey.prev.json`), snapshotted above.
	try {
		const prev = JSON.parse(await fs.readFile(PREV_FILE, 'utf8'));
		console.log(`\n## Since the previous run (\`${prev.provenance?.head ?? '?'}\`)\n`);
		const prevWhy = unreliable(prev.provenance);
		if (prevWhy)
			console.log(`**The previous run is not a baseline** (${prevWhy}): read this delta as noise, not movement.\n`);
		if (prev.provenance?.source !== prov.source)
			console.log(`**The SOURCE changed** (\`${prev.provenance?.source ?? 'live, unrecorded'}\` -> \`${prov.source}\`): this delta is the new source's, not the compiler's.\n`);
		console.log(renderDelta(declStates(prev.reports), declStates(reports)));
	} catch {
		console.log(`\n## Since the previous run\n\n- no previous aggregate to diff against`);
	}

	await fs.writeFile(AGG_FILE, JSON.stringify({ provenance: prov, reports, causes: clusters(all).map(([k, s]) => ({ cause: k, blocks: s.length, files: [...new Set(s.map(x => x.file))], sites: s })) }, null, '\t'));

	// Loud, and non-zero: a crashed worker means those files were NOT measured, so every number above that
	// mentions them is the previous run's. Silence here once made a real regression read as "no change".
	if (workerFailures.length) {
		console.log(`\n## NOT MEASURED\n\n${workerFailures.map(f => `- worker crashed: \`${f}\` -- its rows above are STALE`).join('\n')}`);
		process.exitCode = 1;
	}
})();
