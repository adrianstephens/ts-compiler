---
name: tison-session-handoff
description: LIVE cold-start state for the wasm-backend self-hosting work -- where things stand (survey at 11aa1d6, 2026-10-05; binary work to 2026-10-06), the top blockers, what the user decided and has not decided, open-not-fixed items, and the contracts to know before editing codegen. Read this before anything else.
metadata:
  node_type: memory
  type: project
  modified: 2026-10-06
---

**Read this first, then [[tison_towasm_self_hosting_plan]] (distilled: instruments, traps, design invariants) only for a specific
topic.** This file is live state: **rewrite it wholesale, do not append.** Target ~120 lines.

**2026-09-30 STRUCTURE CHANGE**: `tison/src/examples/` was split out into the `compiler` package (`compiler/`; this memory
dir, `assistant/`, `test/` moved with it; tison keeps only the parser generator + `ast.ts`/`walker.ts`). Old paths in older
memories resolve through the rename ledger in MEMORY.md. Run everything from the WORKSPACE ROOT (`node_modules` is there),
e.g. `bash compiler/assistant/selfhost-survey.sh`. The survey compiles `compiler/src/...` and `tison/src/...` targets from a
snapshot (`selfhost-snapshot.sh` takes tison, compiler, binary-libs, binary). Verified after the split: all suites, corpus gate
838 = baseline, `vsdg-check.sh`, survey end to end. **Run the survey with `SURVEY_HEAP_MB=6144`** -- `wasm/codegen.ts --whole` and
wasm-backend.ts slice 0 peak above the 2 GB default and report CRASHED otherwise. **6144 x the default 8 workers swapped this
16 GB Mac to a halt (2026-10-01)**: the scheduler now costs every job at >= half the heap cap (V8's garbage ceiling), so 6144
runs ~2 workers here -- slower, but the machine stays usable. Ask before a full run; `SURVEY_JOBS` caps it further.

## State at 2026-10-06

Survey at `11aa1d6` gave 399/421; since then the binary-libs wasm.ts work: the instruments now resolve the bare `@isopodlabs/binary`
to SOURCE (`assistant/sibling-paths.ts`, shared by every probe), which exposed the real binary gaps, fixed one by one (abstract
classes; imported superclasses; class values; static fields as lazy globals; JSON lib; Awaited lib; symbol-keyed fields; index
signatures; union of generic signatures; template-resolution fallback for generic instances; ...). Next: wasm.ts `insertFactory`/
`WasmModule` probes stop at `RemainingRepeat<...>` "closure parameter 'v' needs an explicit number/boolean/object type";
`binary-libs/assistant/tt.ts` (`bin.as(UINT8, ...)`) stops at `Awaited<ReadType<any>>` (the deferred any+infer conditional above).
Re-run the survey before trusting rows.

## The direction since 2026-09-21 (the user's) and what it settled

`wasm-backend.ts` had grown by giving each failing case its own path because it RE-DERIVED types the checker already knew. Now **the
checker stamps each expression's type** (`checkedTypeOf`, [[tison_checker_type_stamps]], ~94% coverage) and **representation is the
backend's own choice** ([[tison_representation_table]]). Landed: backend consolidation (W.Type guards, one closure-call path, one runtime-
helper mechanism, `resolvePlace` for every place read/write, `classifyCall`/`emitCallee`/`emitGuardedCall`/`dispatchArm`, `emitShortCircuit`);
call resolution reads the checker's stamp (`checkedCallOf` = `{sig, typeArgs}`; deleted `inferCallTypeArgs`/`overloadForArgs`/the
checker's `resolveOverload`; `implementationOf` + `callTypeArgs`); narrowing machinery in the backend deleted; canonical boxing
(`coerceValue`); the interrupted resumable unification (generators and async share `resumableFrame`/`emitResumableBody`); the checker owns
flow and numeric ranges (below); machine types; **type parameters are opaque as TS's** (`302be07`); TS's inference PRIORITY (a callback's
return outranks the destination, which only fills a parameter nothing else spoke for; codegen keeps the caller's layout by FLOW:
`callTypeArgs` instantiates with the destination's argument where the checker's is an ANONYMOUS object shape, the destination is struct
shapes, and every argument still fits). wasm-backend.ts ~11.0k -> ~10.5k lines.

**Rules learned (checker/flow/scale)**
- `checkStmt` returns its flow (`undefined` = never falls out); `joinFlow` merges; `break`/`continue` deliver to a `FlowTarget`; a loop head
  iterates QUIETLY (`Scope.quiet`) to a fixpoint then one real walk. A check narrows iff it reports, stamps, or is quiet -- a QUERY (the
  backend's `checkerTypeOf`) must not mutate its scope; never RESOLVE a declared type during hoisting (bakes an interface before a later
  lib block merges into it -- hit twice); never re-type an expression with `err` (duplicate diagnostics -- hit twice).
- Numeric ranges in the flow: `rangeStep` = the USER'S RULE (`++`/`--`/`+= a`/`-= a`/`x = x +- a` never overflow i32, else i64, both sides
  fit); loop heads `rangeWiden` to machine limits then step down; `combineTypes` merges true intervals; a `let`'s representation = the hull
  of its stamped reads+writes (`d.flowType`). `NumRange.integer` EXCLUDES -0. 32-bit `+ - *` keeps 32 bits only where the checker's stamp
  says i32/u32, else `f64`. u32 compares `_u`; mixed i32/u32 compare as f64 (NOT i64). Bigints are `i32`/`i64` where the checker proves the
  range; `scalarBinding` reads a machine-scalar binding as it (a boxed union narrowed to `number` must unbox -- letting every binding win
  regressed 60 rows).
- Machine types: lib.d.ts declares `Int<Bits, Signed>`/`Float<Bits>` (built in by being declared in the ROOT = lib scope) and `i8..u64/f32/
  f64` as applications; `T.machineOf` follows the alias chain from the DECLARATION, never a name. User: an annotation is TRUSTED, not
  checked -- the value is converted into its slot automatically, SATURATING (`trunc_sat`) is fine; a machine type's JS semantics are
  `number`'s for Bits <= 53 and `bigint`'s above. `machineSlot` is honest (i8/i16 -> i32, u8/u16 -> u32, u64 own); a NUMBER's box is ALWAYS
  `f64`; a slot holding two array storages opens PER DECLARATION (user chose per-slot over per-type; aliasing kept); out-of-range packed
  writes WRAP.
- Scale: fluent builders (`B<T & F<T>>`) double per step, so printed keys (`typeKey`) are exponential -- use `T.typeId` (structural hash,
  DAG-linear; lives on the node, skips checker stamps) for any equality/cache/set key; `resolve`'s structural cache is weak. A cycle guard
  must be a WeakMap (a Map OOMed the workers). Each named alias body resolves with its OWN depth budget (`resolveAliasBody`). Conditionals
  distribute at their own node; `mentionsAbstract` must cover indexed/keyof/mapped/conditional kinds. An undeclared TYPE name is silently
  "abstract" (no TS2304 for types): suspect a missing lib name whenever a conditional over concrete-looking types stays deferred.
- A stamp is taken when a closure is first checked, so a `let`/`const` declared LATER in its block was unbound there: `hoist` binds each lazily
  (`Scope.addLazyValue`); speculative walks (`trying`) stamp nothing and undo what they wrote onto the AST (`ahead`/`written`). `var` is
  function-scoped (`scope.varScope()`; backend `hoistVars`). A node codegen SYNTHESIZES is typed with `typeOf(..., overStamps)`.
- Proof a refactor changes no behaviour: **a WAT A/B over the towasm suite** (`suite-wat-diff.py before.out after.out` names the tests whose
  printed WAT changed; `test-watdiff.py before.out after.out <test>` shows one) -- stronger than difftest agreeing. A snippet runs with
  `towasm-run.ts file.ts export...` (reads dist/).
- **A checker change needs a self-hosting gate too**: `SNAP=<packages root|snapshot> errcount.ts <surveyed files>` counts checker errors under
  the survey's sibling-source resolution and the wasm lib. The corpus A/B (TS's lib, single files) and test-checker cannot see a lazily
  inferred IMPORT read during a trial (db47972: walker.ts 1 -> 13 errors, both instruments green). Probes, all `SNAP`-aware where they load
  modules: `probe-ctx.ts file [lines]` (expected/checked per call/new/arrow/array, `KINDS=`), `probe-obj.ts file [lines]` (object literals'
  flow/expected/checked), `probe-call.ts file` (each call's resolved overload). In wasm-backend/codegen code a stack needs
  `new globalThis.Error().stack`: codegen.ts's own `Error` class shadows the global and has no stack.
- The checker never reports an unknown name for TYPES; for values TS2304 is behind `Scope.unknownNames` ([[tison_unknown_name_diagnostic]]).

## Gates baseline (2026-10-06)

corpus A/B vs `07b036e`: ERROR +24 (was +13), GAP 195. The +11 from index-signature checking (`b6996e0`) are 10 errors tsc ITSELF
reports (the corpus's tsc-clean classification is stale for them -- always re-run real tsc on a new corpus error, matching by
line-1 as well, since our positions are the NEXT token's) + 1 false positive left: reverseMappedTupleContext.ts:47 (reverse-mapped
inference through a nested homomorphic mapped type falls back to the constraint). difftest 2232/2234. Self-check errcount:
checker/type-core/codegen 0, wasm.ts 2, wasm-backend.ts 8. **test-towasm reads `dist`: `npm run build` before it** (lib files too).
User decisions all DONE (builder types + dynamic-object `I`; `#own:` override slots; `new Map()` contextual; class values = constructor
closures with a per-class env tag, statics read by tag).
**Checker queue (left):** declarations checked WIDENED (`const r: 'a' = 'b'` GAPs; flow ranges vs literals); `unique symbol`; a call on
an intersection of function types picks only the first signature (`p('x')` on `((s: number) => R) & ((s: string) => R)` errs);
`any extends P<infer R>` stays deferred (TS: both branches, a naked `infer` binds `any`, a nested one `unknown`; collapsing it broke
corpus cases where an erased placeholder stood for a type parameter, so it was reverted).

## Next up (2026-09-30, end of session)

0. **Size** ([[feedback_track_total_size]]): tracked src (`ts/` sans lib + `wasm/` + `vsdg.ts` + `transpile.ts`) 29,149 at the
   2026-10-03 session end (wasm-backend.ts 9,174, after the comment pass; measured from committed content -- the user's transpile.ts edits are uncommitted). The work queue is [[compiler_size_reduction_plan]] (whole-file examination, 2026-10-02); near-clone
   scanning is NOT the method (user: it only finds local copies).
1. **Step 4b DONE `0c24195`** (user chose "unbuilt shapes"): the open-shape walk records each object literal's `shapeKey` (member
   names; at its slot and as its own type); a struct shape no literal builds is open (`isOpen` in the backend, shared by typeOf/
   ownerFor/holdsLayout/spread). Repros `tb/d.ts`, `tb/litkey.ts` run. +20 lines net (not deletion-first: `resolvePlace`'s `refined`
   clause is still needed for `'in'` narrowing). **Survey NOT yet measured for it** -- the run was killed (memory, above).
2. **lib.d.ts audit IN PROGRESS.** Instrument `assistant/lib-audit.ts` -> `lib-audit.md`: the MERGED lib (lib.d.ts + lib/*.ts
   classes, whose methods join the interface as overloads) vs TS's es5..es2024, per member, `- TS` / `+ ours` signatures. The lib
   declared what the RUNTIME implements, so every fix is runtime + declaration. Done: `d794c65` (position args, no-arg toFixed/
   toPrecision/Error; `clampIndex`/`relativeIndex` replace 6 clamp copies), `362e7ab` (flatMap value-or-array, RegExp(re), raw,
   PromiseLike), `ca616df` VARIADICS (user: per-arity bodies -- an `__asm` body can be one overload (`ClassInfo.inlineOverloads`), so
   `Math.max(a, b)` stays one `f64.max`; `namedBody` maps an AMBIENT signature to the implementation with the same parameters, so
   lib.d.ts restates each overload pair the class implements). **Gates for lib work**: towasm, lib-decls, `tsc -p src/ts/lib`
   (now `noEmit`), difftest. The corpus A/B checks against TS's own `lib.esnext.full` -- it CANNOT see our lib. Then (2026-10-01):
   `8a4ffd8` numbers print as JS does (Burger & Dybvig over bigints, 0/4,424 vs node; ~30 us per fraction -- a machine-int
   Ryu is the speed-up), `toExponential()` no-arg; IIFE parameters typed by their arguments (checker); **`this` parameters**
   (`CallSig.thisType`, inferred from the receiver -- binary's `WithStaticGet.get<X>(this: X)`), lib InstanceType/
   ConstructorParameters/Required. Not done: TS2684 (receiver fits `this`). **2026-10-02 `flat(depth)` DONE** (TS's
   `FlatArray`; `_flatInto<E, F>` recurses per element type). It forced five general fixes: a value-level `this:` is lifted
   into `thisType` by `JS.Params` (9 `key !== 'this'` filters deleted; codegen counted it as an argument); `stampScope` stamped
   a generic METHOD member's own type params with the class scope, so every method's `<A>` was an undeclared, anything-relating
   name (now real -- surfaced a true TS2322 in the corpus); TS's apparent-type inference (a type-param argument infers through
   its constraint); `related` recursed with the RESOLVED other side, losing the by-name Array fast path (corpus GAP -6);
   codegen's `staticGuard` folds `&&`/`||`; a cast through `unknown`/`any` is a checked scalar<->ref conversion (`coerceValue`).
   Left: Promise chaining/`all` (Promise is no PromiseLike); `Map/Set.keys()` return arrays (deliberate, accepts more than TS);
   `divideAndConquerIntersections.ts` now GAPs (a TS perf stress test whose generic method was vacuous before). The audit's
   `?` rows are static fields typed by initializer, an instrument blind spot. The "Missing" section is runtime coverage.

## Waiting on the user

**String cheap representation.** Done: each literal is materialized once. The data segment is PASSIVE (copy-only), so a bare `u32` offset
cannot be a string. Options put to the user: (1) offset+length packed in an `i64` (`.length` a shift, materialize on char access);
(2) bytes also in linear memory (`charCodeAt`/compare/print read in place); (3) stop. Either changes how every discriminated union
(`type: 'call'`) is held.

## Decided by the user -- do not re-open

- A stamp is a TYPE; the representation is the BACKEND's, free to be simpler, converting only where needed. Cheap forms are STACK
  representations; pseudo-types are a separate mechanism that forces a slot's. A `const` may keep a narrower SCALAR its initializer built; a
  `let` takes a representation covering every assignment (only immutable values -- `const a = [1,2]; a.push(3)` needs the `Array`).
- **No runtime checks** for cheap forms: only what the checker proves. Rawness is NAMED (Array is never a special case).
- VSDG is optional and runs BEFORE check+stamp; the backend compiles whatever AST it gets literally, in tree order. Inlining is a VSDG prepass.
- Erasure prefers per-instantiation structs (a widening flow OPENS the slot); do NOT erase in the checker to match codegen.
- Type parameters opaque as TS (`302be07`); TS's inference priority (2026-09-28); the generic conditional stays deferred (2026-09-30).
- Dynamic-objects step 4 (2026-09-30): (a) a generic class WITH methods also erases its reference type arguments (one struct,
  methods compiled erased), so `this as never` across instantiations is identity; (b) an object type with no buildable struct
  layout is held as the dynamic object and read through the any-field dispatch (identity kept; slower, accepted).
- Architecture SETTLED: `ts/wasm-backend.ts` is the TS half, `wasm/codegen.ts` the neutral half; a file is earned by cross-language reuse
  only; `TSEmitter` rejected; **do not split `ts/wasm-backend.ts` for navigability**; neutral extraction is exhausted, measured; wasm
  knowledge is NOT language-neutral (`numericOpInline` encodes JS semantics). **`cpp/wasm-backend.ts` is the neutrality gate**: keep
  `test-cpp-backend.ts` green. See [[tison_towasm_cross_language_plan]].

## The survey -- OCCASIONALLY, never as a gate (user's call)

Slow (~20-35 min) and causes friction: run it deliberately, not after every commit (2026-09-22 ran it per commit -- don't). Gates are
difftest, the corpus A/B (for checker/lib changes) and the suites. It catches what suites miss (it found the `x as T` operand gap), so
run it after a change to how the backend READS types. Read `REGRESSED` against a run with no **NOT A BASELINE** banner (it hashes
`compiler/src` at start and end). Use `SURVEY_HEAP_MB=6144`.

## Open, NOT fixed

- Codegen cannot narrow an `Array<any>` instance's result to the array the checker types (`mixed.flat()`, a predicate `filter` over
  `(number|string)[]`): `cannot convert Array<any> to Array<number>`. An array boxed into `any` with no element context cannot be narrowed
  back (`arr:ref` vs `arr:f64`). Narrowing `g.t === 'MC'` doesn't drop an arm whose `t?: never`; that fallback widens `{a: 1}` to `{a: number}`.
- wasm/codegen.ts (snapshot) has 2 checker errors: 605 (callback return vs `ReadType<...>`) and 802 (`{ref: 'any'}` vs `wasm.ParamType[]`).
- **Diagnostic positions are the NEXT token's** (the LALR reduce stamps `actionTok.pos`), so an error can sit lines below its node and the
  corpus A/B then shows a real tsc error on a different line. Fix: record each frame's first-token pos.
- A non-bare `declare const x: typeof f` annotation resolves eagerly at hoist time (probe with a type alias). `NoPromise<Promise<'z'>>`
  doesn't yield `'z'`. C1 (a var_decl checks its initializer WIDENED; `const x: 10n = 10n` is rejected). tison's `Promise` is no
  `PromiseLike`; `Promise<number>.then(async z => 2)` exhausts `isAssignable`'s depth. `gen.next()` with `N = undefined` demands an argument.
  The checker types `new Set([...a, ...b])` as `Set<any>`. `v.pos = 7` on `number[] & {pos}` is `unknown field`. 3 peg.ts rows: `cannot convert
  Generator<any> to Generator<NonTerminal>`. Numeric `let` messages print the precise value where tsc says `number`.
  A class field inferred from an integer literal (`y = 1`, typed `i32`) is accepted where a `string` is wanted (MISSED error, found
  2026-10-03; a `let k = 1` is rejected correctly).
- Codegen: class-NAME triggers remain (`Map` in `ensureAnyEntries`, `Array` in `expandArrayMembers`); `var_decl`'s three statement-stamp queries
  decide representation and must wait for the layer; through `any`: reading a dynamic object traps (shares `Map`'s struct -- fix is a distinct
  struct, not a `Map` arm), `anyTypedArray.length`, `any + any` assumes numbers, `m.get(k)` into `number`; the object literal's three spread
  classifications use different owner resolvers (unifying is a behaviour change); native bigint comparisons / unary `-` for two machine-int
  bigints still widen to limbs (candidate); the BigInt survey row (6) is an overload-resolution gap in `candidateFits`; no definite-assignment
  diagnostic; a closure capturing a HOST IMPORT doesn't resolve; `Buffer.toString` only 'latin1'/'binary'; `lib/node/fs.ts` compile-tested only;
  flow-directed literal layout (deferred by the user); `c1662ba` has no regression test; the `OneOf` precedence defect
  ([[tison_precedence_resolution]]; `termOneOf` is NOT the fix -- user rejected it).
- Instruments to remember: `diag-snippet.ts '<src>'` (checker diagnostics), `esnext-snippet.ts '<src>'` (against lib.esnext.full as
  test-checker does), `callstamp-probe.ts '<src>'` (stamps: sig, origin, type args), `tsc-classify.ts` (real tsc on corpus files; TS 6
  defaults `strict` ON, the corpus assumes OFF), `src-errors.sh` (tison-style code the corpus misses), `official-one.ts`, `flowtype-dump.ts`,
  `flow-probe.ts`, `counter-bounds.ts`, `inspect-heap.mjs <port> [secs]` / `inspect-profile.mjs` (a crashed probe writes no `--cpu-prof`;
  attach an inspector), `probe-decl.ts` with `WAT=<regex>`/`STACK=1`/`STACK_DEPTH`.

## Contracts worth knowing before editing codegen

- `emitIf`/`emitBlock`/`emitLoop` own the levels they open; callers do no depth bookkeeping. Locals are named and freed by `FunctionContext`;
  wrap assignment sites in `ctx.inScope` or slots leak. `Types` owns the shapes and dedupes structurally; `closureTypes` is a signature
  REGISTRY, not a cache. `typeIndex: -1` is a real `ClassInfo` state; `thisWtype` is the "processed" test. Every conversion of an emitted
  value goes through `coerceValue` (logical-type rules); `coerceTop` is physical only.
- **Never `git diff src/` wholesale for an A/B patch** -- name the files (it once captured the user's work).

## Tree state

**2026-10-01 mistake, user to decide:** `ca616df` (my variadics commit) also contains the user's in-progress
`src/cpp/c-parser.ts` and new `src/cpp/glsl-parser.ts`, swept in by `git add src`; left as is (no history rewrite).
`0d94b27` deleted 16 lib `.js` files a type-check had emitted into `d794c65`.

**Never trust this line -- re-check `git status`; the user edits and commits concurrently.** At 2026-09-30: `compiler` HEAD `aa1d4bf`+ (memory
commits after), `tison` HEAD `4c7f25e`+; the user's `scad_parser.ts` is out of tison (it no longer trips NOT A BASELINE here).

Related: [[feedback_session_boundaries]], [[feedback_two_tier_gates]], [[tison_towasm]], [[tison_checker_type_stamps]],
[[tison_representation_table]].
