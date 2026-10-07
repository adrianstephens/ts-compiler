## Rename ledger — old names in older memories

Rename freely; **do not rewrite the historical changelogs**, just add a line here. Older entries (and commit
titles) keep the old name, and this resolves them. `assistant/memory-refs.ts` lists names in `memory/` that
no longer exist in the tree — run it after a rename and fix what is LIVE; historical mentions stay.

| was | is now | when |
|---|---|---|
| `TS/towasm.ts` | `ts/wasm-backend.ts` (was `TS/backend.ts` until the 2026-09-30 split) | `ed2d662` |
| `TS/towasm-analysis.ts` | folded into `ts/wasm-backend.ts` | `307aa89` |
| `TS/towasm-types.ts`, `TS/towasm-asm.ts`, `tocode.ts` | folded away / renamed (`tocode.ts` → `printer.ts`) | earlier |
| `wasm-types.ts` | `wasm/codegen.ts` (was `wasm-codegen.ts` until the split) | `a69d68a` |
| `wasm-asm.ts` | folded into `wasm/codegen.ts` | `deb2d18` |
| `TSWError` → `WasmError` | `W.Error` (the module is imported as `W`) | `efe46bd`, then the user's pass |
| `WasmScalar`/`WasmType`/`WasmElementI` | `Scalar`/`Type`/`ElementI` | the user's pass |
| `ARR_WTYPE` | `ARRAY` | the user's pass |
| `wasmTypeEq`, `wasmTypeKey`, `intWasmType`, `combineUnionWtypes` | `typeEq`, `typeKey`, `intType`, `combineUnion` | the user's pass |
| `typeofHeapType(tag, types)` | `Types.heapType(tag)` | `b858045` |
| `PRIMITIVE_TAGS` | `T.LITERAL_PRIMITIVES` | type-utils regroup, 2026-09-18 |
| `T.restElementTypes` | `T.elementTypes` (spreads now contribute their element) | type-utils regroup, 2026-09-18 |
| `containsInfer`/`containsThis` | `containsKind(t, kind)` | type-utils regroup, 2026-09-18 |
| backend-only helpers in type-utils (`substituteClassTypeParam` … `arrayPartOf`) | unexported functions in `backend.ts` | type-utils regroup, 2026-09-18 |
| most of `type-utils.ts` | `TS/type-core.ts` (type-utils re-exports it); `arrayMember`/`objectPrototypeMember`/`callablePrototypeMember` → `TS_SEMANTICS` | type-core split, 2026-09-18 |
| the whole `tison/src/examples/` tree | the `compiler` package (`compiler/src/`): `vsdg`/`transpile` at the root (`common`/`walker` moved to tison, see below), `wasm/` (`codegen`, `wat-parser`), `ts/`, `cpp/`, `py/`, `cg/` | split out of tison, 2026-09-30 |
| `examples/TS/backend.ts`, `CPP/backend.ts`, `PY/backend.ts` | `ts/wasm-backend.ts`, `cpp/wasm-backend.ts`, `py/wasm-backend.ts` | same |
| `wasm-codegen.ts`, `wat-parser.ts`, `cg-grammar.ts` | `wasm/codegen.ts`, `wasm/wat-parser.ts`, `cg/grammar.ts` | same |
| `TS/`, `CPP/`, `PY/` dirs | `ts/`, `cpp/`, `py/` | same |
| `dist/examples/...`, `npm run examples`, `cd src/examples && tsc -p .` | `dist/...`, `npm run build:emit` (one tsconfig now, so the "needs its own tsconfig" trap is gone) | same |
| `tison/test`, `tison/assistant`, `tison/memory` (compiler-side) | `compiler/test`, `compiler/assistant`, `compiler/memory`; engine memories stay in `tison/memory` | same |
| `tison/src/examples/common.ts`, `walker.ts` (the shared AST shapes / walker types) | `tison/src/ast.ts`, `tison/src/walker.ts`, imported as `@isopodlabs/tison/ast` and `@isopodlabs/tison/walker` | moved into tison so parser-only consumers need not pull in the compiler, 2026-09-30 |
| `scad_parser.ts` | deleted from tison by the user (lives in their vscode extension); its memory `tison_scad_port.md` moved to `tison/memory` | 2026-09-30 |

The module dropped its `wasm`/`Wasm` prefixes throughout: the file is already named `wasm-codegen.ts` and
is imported as `W`, so `W.Type` beats `WT.WasmType`.

## Engine memories live in tison

`tison/` is now only the parser generator; this package (`compiler/`, `@isopodlabs/compiler`) is the
compiler infrastructure built on it. Engine facts — architecture, table cache, PEG back end, `Manual()`,
precedence resolution, debugging technique, cloud-agent deps — are in `../tison/memory/MEMORY.md`.

## Project rules

- [track TOTAL size; consolidate every session](feedback_track_total_size.md) — net line delta in every commit, `src` total in the handoff (31,906 at `d4fb83f`); extend the duplicated mechanism, never add a near-copy; 4b lands deletion-first
- [SIZE REDUCTION PLAN](compiler_size_reduction_plan.md) — **the work queue for cutting thousands of lines**: wasm-backend.ts examined end to end, 7 families it re-derives (bindings, module resolution, literal shapes, two type walks, expandos, type queries, comments), order, gates, progress
- [diagnostic positions are lookahead](diagnostic_positions_are_lookahead.md) — a node's `pos` is the token AFTER it (reduce lookahead), so `@ts-expect-error` needs start positions first; corpus errors under a directive are real
- [no name special-casing in wasm-backend.ts](feedback_no_name_special_casing.md) — find the structural trigger, never hardcode a method/function name
- [keep the checker stateless](feedback_no_checker_state.md) — prefer untyped AST-node stamping over new checker state
- [don't simplify deps for self-hosting](feedback_no_simplifying_deps_for_selfhosting.md) — hard constructs need a real compiler feature
- [no JSON.stringify on AST/Type](feedback_no_json_stringify_ast.md) — bigints throw; print with `T.typeKey` / `T.exprKey` / `T.stmtKey`
- [no unimplemented-throws tests](feedback_no_unimplemented_throws_tests.md) — `checkThrows` is for permanent enforced behavior only
- [codegen perf](tison_codegen_perf.md) — where a self-compile probe's time goes; isOpen memo + typeId undefined-field fix + typeId member compare took it 321 -> 152 s; what's still open
- [survey in CI](tison_survey_ci.md) — the survey as a GitHub Actions workflow: plan / slice matrix / merge; sees only PUSHED commits; results in the `survey-results` artifact
- [SESSION HANDOFF](tison_session_handoff.md) — **read this at cold start**: live state (survey 399/421 at `11aa1d6`, top blockers), user decisions, what's deliberately unfixed, what the user hasn't decided
- [harness portability](tison_harness_portability.md) — for running tison under a DIFFERENT agent harness: cwd, gate order, the acceptance numbers at `ec2a21f`, which instruments gate by EXIT CODE (difftest and vsdg-check do; the survey is a probe to be read), and what does not travel (the transcript)
- [session boundaries](feedback_session_boundaries.md) — when the user asks "continue or start fresh?", recommend; default fresh after a committed fix, always after a compaction
- [build and tests](compiler_build_and_tests.md) — tests import the BUILT `dist/`; `build` vs `build:emit`; the `dist/ts/lib` copy traps
- [two-tier gates](feedback_two_tier_gates.md) — fast gates while iterating, full set once before the commit; measured 10.1 gate runs per commit. **`test-towasm.ts` and `test-checker.ts` read `dist/` — `npm run build:emit` first, on both sides of an A/B**
- [index wasm-backend.ts before hunting](feedback_towasm_symbol_index.md) — one-off `grep -n` symbol index; the file was named in 575 separate read/grep calls over 8 sessions
- **Scratch and instruments live in `compiler/assistant/`** (2026-09-14, d8f407c; the workspace root is not a project). Older memories write instrument paths as `assistant/…` — read those as `compiler/assistant/…`. They are still RUN from the workspace root, where `node_modules` is. The survey itself is tracked in `compiler/survey/` (`bash compiler/survey/selfhost-survey.sh`; outputs still in `compiler/assistant/`), and runs in CI too: [survey in CI](tison_survey_ci.md). Generated markdown gets `.md`, not `.txt`.

## Semantic conformance (current method)

- [conformance sweeps](tison_conformance_sweeps.md) — **start here for new work**: per-lib-area differential sweeps are the gate now, not the survey; 10 groups, 6 green, remaining divergences listed
- [workaround inventory](tison_workaround_inventory.md) — audit of every leniency/`any`-fallback/cast site: what is NOT a workaround, what is open (silent `any`, accepts-bad-code, towasm gaps) with the proper fix and order, plus checker rules learnt removing them
- [unknown-name diagnostic (TS2304)](tison_unknown_name_diagnostic.md) — types+values behind `Scope.unknownNames` (on in tsw/test-towasm, off in corpus); forced-on corpus causes; `import()`/`import.meta`/`globalThis` modelled 2026-09-28; `unique symbol` unmodelled
- [corpus error dump](tison_corpus_errdump.md) — per-ERROR corpus A/B; `corpus-ab.sh` totals hide a false-positive-for-true-positive trade

## Engine and parsers

- [decorator support](tison_decorator_support.md) — CLOSED: class/member/parameter decorators
- [official TS test suite](tison_official_ts_test_suite.md) — corpus run vs real tsc tests; 2936→1519 threw. **`npm run gate` is the fast pre-commit ratchet.** Harness was silently dead for 79 commits — read the traps
- [AST convergence](tison_ast_convergence.md) — 3 parser ASTs converged onto common.ts shapes
- [py-parser](tison_py_parser.md) — off-side rule done purely in the lexer
- [jsx-parser](tison_jsx_parser.md) — LALR reduce-lookahead leaks + JSX-vs-generic-arrow ambiguity
- [glsl-parser](tison_glsl_parser.md) — GLSL over c-parser; the two LALR conflicts (unit-reduction nonterminal, scalar_type reduce/reduce) and the `ArrayDecl` size seam
- [hlsl-msl-parsers](tison_hlsl_msl_parsers.md) — HLSL/MSL over cpp-parser; the `Definition<S>` statement seam, exported `scope_prefix`/`skip`/`>>` terminals, semantics-vs-bitfield and qualified-name resolutions; Cg/Slang ride HLSL
- [slang-parser](tison_slang_parser.md) — Slang over hlsl-parser; `interface` as a Definition to dodge chain re-instantiation, and the `__target_switch` label-folding technique (its `case` is token-identical to a `switch` case)
- [wat-parser exceptions](tison_wat_parser_exceptions.md) — exceptions + multi-value blocktypes, verified vs wasmtime

## TS-to-wasm compiler

- [type-core / Semantics split](tison_type_core_semantics.md) — `type-core.ts` is language-neutral (TS vocabulary), `type-utils.ts` is JS's layer; a root `Scope` carries its language's `Semantics`; Python imports type-core only
- [CHECKER TYPE STAMPS -- current plan](tison_checker_type_stamps.md) — the checker records each expression's final type, the backend reads instead of re-checking; codegen keeps its freedom to pick simpler representations; the backend compiles its input AST literally (VSDG is optional, outputs a new AST)
- [Promise runtime](tison_promise_runtime.md) — the lib's standard Promise is one struct for every `Promise<T>` (value stored `any` + the stored-field class layout rule); how async functions settle and resume it; remaining gaps
- [REPRESENTATION TABLE](tison_representation_table.md) — which wasm representations are valid for which TS types, and that the BACKEND alone decides (never a stamp)
- [type vs representation](tison_type_vs_representation.md) — many-to-one and must stay separable; tags name representations, and it is what lets `Node[]`/`Foo[]` share one physical array type
- [array identity — RESOLVED](tison_array_identity.md) — `Array<T>` owns a `RawArray` field; the compiler knows only `RawArray`; the traps hit, the pre-existing bugs found, and why struct merging wasn't built
- [towasm](tison_towasm.md) — **the authoritative gap list is `ts/wasm-backend.ts`'s own header comment**; this covers design invariants
- [comment pass tooling](tison_comment_pass_tooling.md) — rewriting comments in any file safely: `comment-blocks.js` lists, compact `@a-b`/`@+n` edits, `towasm-comment-pass.js apply`+`verify` (printer-proven code identity); never a bare `ts.createScanner`
- [CROSS-LANGUAGE PLAN](tison_towasm_cross_language_plan.md) — why/where the TS-specific half of the wasm backend separates from `wasm/codegen.ts`: the file-splitting rule (**no split without a reason; a component's axis is the file's axis**), the rejected `TSEmitter`/relaxed-VSDG, the shelved `TypeOracle`+IR seam, unfinished generic-core extractions, do-not-merge traps
- [module records](tison_module_records.md) — a module is `TS.Module` (body+scope+filename), not a bare `Stmt[]`; run all FOUR tsconfigs
- [nested array element kind](tison_nested_array_element_kind.md) — inner arrays keep their DECLARED kind (`objectArrayKind`'s comment lies); `a.push([])` into `number[][]` still traps
- [towasm capabilities](tison_towasm_capabilities.md) — index of closed feature work + the checker fixes whose blast radius exceeded their bug report
- [difftest cross-module cases](tison_difftest_cross_module.md) — `addModule`/`addCross` + `--only`; the only instrument that sees cross-module bugs
- [SELF-HOSTING PLAN](tison_towasm_self_hosting_plan.md) — goal: wasm-backend compiles its OWN source unmodified (never adapt a surveyed file). Distilled: instruments (`selfhost-survey.sh` reads MOVED/REGRESSED not the total, `probe-decl.ts`, `difftest.sh`, `corpus-ab.sh`) and their traps, the codegen/checker design invariants, user decisions, recorded-open items. Live numbers are in the handoff
- [checker perf debugging](tison_checker_perf_debugging.md) — `sample <pid>`, or `assistant/inspect-profile.mjs` when JIT frames are `???`; count resolve depth bails first
- [interface inheritance](tison_interface_inheritance.md) — `extends` IS an intersection; last part = most concrete, and all four consumers must read it backwards
- [closure-param causes](tison_closure_param_causes.md) — the survey's `closure parameter 'X'` rows are THREE unrelated blockers, not one; read before working that row
- [unbound type param row](tison_unbound_type_param_row.md) — **RESOLVED**: the ~109-decl `T'367` row was `inferTypeArgs` leaking a generic argument's own type param; fixed with `baseSignature` (TS's `getBaseSignature`). Also the stack-trace technique that found it
- [checker inference](tison_checker_inference.md) — distributive conditionals, contextual callback returns, const contexts, template literal expansion, and probe traps (literal leniency, silent `any` members)
- [nominal class refs](tison_nominal_class_refs.md) — **`resolve` keeps class refs nominal; `resolveMembers` is the opt-out** (4 sites); replaced 8 per-site guards
- [scope stamping](tison_scope_stamping.md) — how checker scopes reach towasm (statement/branch stamps); **don't "fix" `narrowedTypeOf`**; why block-node scopes were measured and declined
- [checker narrowing plan](tison_checker_narrowing_plan.md) — user plans integer/range narrowing in the checker (not started as of 2026-07-31)
- [ReadType resolution](tison_readtype_resolution.md) — TStoDecl's resolveTypes for pe.ts `.d.ts`; checker bugs it flushed out; known-unfixed: `_` key bloat and TStoDecl's load-bearing `checkBlock`
- [C++ back end](tison_cpp_backend.md) — `cpp/wasm-backend.ts` (379 lines) over the neutral `wasm/codegen.ts`; **the neutrality gate**, keep `test-cpp-backend.ts` green. Written without changing one neutral line; found the `emitIf` depth trap and a real tison precedence bug
- [Python back end](tison_py_backend.md) — `py/wasm-backend.ts` minimal annotated-scalar subset over `wasm/codegen.ts`; test expectations come from CPython. Forced the py float-literal `raw` fix
- [vsdg dialects](tison_vsdg_dialects.md) — the VSDG core + per-language dialects: the three objects a language supplies, THE TEST for what belongs in the core, shape stamps, the verbatim-fallback rule, shared switch, and the core bugs the multi-language work surfaced
- [vsdg C++ dialect](tison_vsdg_cpp.md) — the widened top level (`Definition | Stmt`), typed constant folding, `++`/`--` as an unmodelled re-binding mutation, switch, C++-specific bugs/limits
- [vsdg node type](tison_vsdg_node_type.md) — RawNode & INode discriminated union; gate = `compiler/assistant/vsdg-check.sh`

- [object shapes keyed by bare name](tison_shape_key_collision.md) — same-named interfaces in two modules share one struct; qualify by module
---

*`archive/` holds older dated originals; the ledger and git (`1c439ff` = pre-distillation text of the five largest notes) hold the rest. Distilled 2026-09-30.*

*Migrated out of the global auto-memory store (`~/.claude/projects/-Volumes-DevSSD-dev-packages/memory/`)
on 2026-09-09 so tison's memories travel with the tison repo.*
