---
name: tison-towasm-self-hosting-plan
description: "wasm-backend.ts self-hosting (compile+run the compiler's own source WITHOUT adapting it) -- goal and scope, the instruments and their traps, the design invariants and user decisions that came out of ~100 fixes, and the still-open items. Distilled 2026-09-30 from a 180KB diary; per-fix history is in git (pre-distillation text: commit 1c439ff)."
metadata:
  type: project
---

**Goal (2026-08-19)**: `ts/wasm-backend.ts` compiles its own implementation and the compiled-to-wasm result *runs* as a
working compiler: real input, correct executable output. "Passes the checker" is not the goal.

**Live state is NOT here** -- read [[tison_session_handoff]] first, and run the survey before believing any number in
any memory. This file keeps what outlives a measurement.

## Scope

In: `ts/wasm-backend.ts`, `ts/checker.ts`, `ts/type-utils.ts` (+`type-core.ts`), `ts/walker.ts`, `ts/transform.ts`,
`ts/printer.ts`, `ts/js-parser.ts`, `ts/ts-parser.ts`, `wasm/codegen.ts`, tison's `src/{tison,core,lalr,peg}.ts`,
`binary-libs/src/wasm.ts` (the survey's TARGETS list is the truth). True bootstrap: the image parses raw TS source text
itself, including the parser engine and grammars -- tison is not a native pre-pass. Out: `tableCache.ts` (fs/crypto/zlib
convenience wrapper; user: skip it entirely), `module-loader.ts`. wasm.ts uses 26 `bin.*` entry points, so the whole
`binary` package (~4.7k lines) is transitively needed; real target is ~27k lines.

**Standing rule**: a dependency's real source is never rewritten to dodge a compiler gap
([[feedback_no_simplifying_deps_for_selfhosting]]). Hard constructs need a real compiler feature. `binary-libs/wasm.ts`'s
generic metaprogramming is hand-asserted via casts and erased; the runtime under it is ordinary dynamic JS that must
genuinely run ([[feedback_types_vs_runtime_behavior]]). Rewriting a surveyed file to make it compile improves the
number without improving the compiler -- that is gaming the instrument (a real mistake made once, `pathKey`). The one
sanctioned exception: JSON was removed from the surveyed set because those files wanted string-quoting and record
equality, not a serializer (`quoteString` in the printer, `entryKey` in lalr). Don't cite it as licence.

## Instruments (all in `compiler/assistant/`, run from the WORKSPACE ROOT; `npx ts-node -T` needs `NODE_OPTIONS=--no-experimental-detect-module`)

- **`selfhost-survey.sh`** -- the cause table = the work queue. PRINTS tables to stdout (redirect yourself); writes
  `selfhost-survey.json` + per-file JSON. `--whole` skips per-declaration probing (~15s); full run ~47 min. Input is a
  frozen snapshot (`selfhost-snapshot.sh`, committed source of tison/compiler/binary-libs/binary) so deltas measure the
  compiler, not edits; `--live` surveys the working tree. Prints "Since the previous run": declarations MOVED TO A NEW
  CAUSE / newly compile / REGRESSED -- **this is the metric, not the flat compiled total** (blockers are serial: a
  declaration reads "failed" whether eight or three remain; 43/258 stayed flat through fixes that moved 11-77).
  - **NOT A BASELINE banner**: the survey hashes `compiler/src` at start and end and lists dirty files; a run whose hash
    moved or that measured uncommitted `src/` is noise. Don't commit to `src/` while one runs. A worker loads the
    compiler when IT starts, so a 40-min run over a moving tree measures several compilers (52 false regressions once).
  - **It probes every file as the ENTRY module**, so it cannot see cross-module bugs (a fix took difftest 46 -> 15
    unsupported and moved the survey by 0). difftest-with-imports is the instrument for that class.
  - It never serializes, so it cannot see invalid wasm; `validate-whole.ts` (serialize + `new WebAssembly.Module`) does.
  - A cause row renames when its message is reworded or contains a counter (`T'NNNNN`): normalize before diffing; read
    ERR rows' counts, not strings. After any checker/lib change diff the cause TABLE for new `ERR:` rows -- the "Since"
    summary hid a regression (14 blocks became checker ERRs) once. Adding top-level functions adds blocks of their own.
  - **Check determinism before trusting a delta**: run one probe 3-5x. (It was nondeterministic until an import-cycle
    race was fixed; `TStypeCheckAsync` now resolves imports one at a time, in source order.)
  - Never leave a toggle that reads `process.env` inside a surveyed file (wasm-backend.ts is one): the survey compiles
    the toggle and reports a fake `unresolved identifier 'process'` row that masks real ones. Remove before surveying.
  - A row that vanishes right after a narrowing/mapping change: probe one of its declarations before believing it (a
    "closed" row was once my own mapping onto `any`, to which everything is assignable).
  - A worker that dies reports CRASHED; 2 GB worker heap is the cap -- `wasm/codegen.ts --whole` needs more (it ends in
    `Invalid string length`, a known pre-existing codegen failure).
- **`probe-decl.ts <file> <decl>`** -- compiles ONE declaration exactly as the survey does (seconds). How most real work is
  done: fix, re-probe the same 5 declarations, watch the error move. Env: `WHOLE_FIRST=1|check`, `SHOW=<const>`. A probe's
  `at L:C` can be in ANY module it reaches (the message now prints `module:line:col`). **Probe the REAL declaration before
  trusting a hand repro matches it.** When a probe prints nothing, rerun it unfiltered before concluding a path wasn't reached.
- **`difftest.sh`** -- differential CODEGEN test (~2100 cases, green, 0 disagreements): compiles a snippet to wasm, runs it,
  runs the same source under node, compares with `Object.is` (strings by content hash `n=(n*31+c)%1000000007`, never
  `.length`). No expected outputs to author. Cases export `main(): number`. Runs `node --experimental-wasm-exnref`
  (`NODE_OPTIONS` refuses that flag) and a real WASI sandbox; `addModule`/`addCross` express sibling-module cases. It does
  NOT prove new lib code compiles -- unreached lib declarations are never codegen'd. Lives in the gitignored
  `assistant/`, so ALSO add a `test-towasm` regression for anything it finds.
- **`corpus-ab.sh [base-rev]`** -- checker A/B against the official TS corpus: worktree at base, `node_modules`
  symlinked, two ~7 min concurrent runs, non-zero exit if `threw`/GAP/ERROR rose; logs in `assistant/corpus-ab/`. `npm run
  gate` is PARSER-only -- never cite it as checker coverage. **Classify new corpus errors per LINE against real `tsc`**
  (run from `tests/cases` with a relative path; a bad option prints an error a line-anchored regex reads as "no errors");
  a corpus file with no `.errors.txt` here counts as tsc-clean, so correct new errors look like false positives.
  Technique for removing a leniency: a self-restoring script flips it back on IN PLACE, checks only the ~15 files it
  exposed, reports how many of the listed false positives remain (23 -> 0), over `check-corpus-files.ts`.
- **`parse-one.ts`** -- does tison's OWN parser read this file? Run after every edit to a surveyed file; nothing else
  catches a parser gap (known one: a lone spread in a parenthesized object literal `l => ({ ...l })`).
- Others: `errcount.ts` (checker errors for named files in seconds, bisect against an old worktree), `npm run libdecls`
  (ratchet: lib.d.ts declarations vs `lib/*.ts` implementations; `--update` re-baselines), `wrun-wat.ts` (`WAT=1` prints
  `mod.toWAT()` -- read the WAT instead of reasoning), `probe-fsrun.ts` (`TRACE=1` logs each WASI errno), `vsdg-check.sh`.
- **`ts/lib/` has its own tsconfig** (`noLib`, against `lib.d.ts`'s ambient declarations; zero errors; VSCode uses it):
  `cd src/ts/lib && npx tsc -p . --noEmit` after touching `lib/`. It is the ONLY thing type-checking those files (the main
  tsconfig and eslint exclude them). With `noLib`, a global the lib uses must be declared in `lib.d.ts`; having both an
  ambient declaration and the real `export class` is the working pattern.

## Traps that recur (each cost real time)

- **The error text names the site that GAVE UP, not the thing that broke** (4+ times: "indexing is only supported on
  number[]" was an `any` receiver; "unknown method 'join'" the method existed; "unresolved identifier 'path'" a bodyless
  module). Probe before believing a cause row. A missing FEATURE is usually a red herring: probe what the failing path
  emits before building the feature you think is missing.
- **A repro that works standalone but not in the real files**: stop peeling the standalone one and reproduce the IMPORT
  (single-file / named import / namespace import / module-level const split a 4-layer problem in minutes).
- **One module-level statement blocking a whole file**: the start function evaluates every top-level const, so a single
  unrepresentable one failed the module. `onTopLevelError` makes it recoverable (omitted -> rethrows; the CLI must not
  emit a module whose init silently didn't run); `isAliasInit` skips aliases/type-only exports. When a file dies on one
  line, check whether the start function is evaluating something nothing reads. Pre-`25d2cc0` "moved N" figures measured
  that coupling, not progress.
- **A hang is a failure**: towasm tests, difftest, gate and lint all passed while a survey hung 100 minutes in a
  `typeOf` re-entry. "The survey stops progressing on one file" is a failure, not slowness.
- **Instrument/shell traps**: `cd` into a comparison worktree persists across Bash calls (HEAD measured twice); parallel
  Bash calls share one cwd -- use `( cd X && ... )`; read the provenance stamp, not HEAD (23 uncommitted files were
  mis-attributed to a commit); `tsconfig.json` includes only `src/**`, so `test/` is never typechecked; an accepted-but-
  unused parameter is not a type error (`makeCachedParser` silently dropped `recover`, disabling ASI, producing 119
  bogus walker errors); the workaround-guard hook matches `Workarounds:` in the Bash COMMAND text, so `git commit -F file`
  never satisfies it -- pass the message inline; a survey result pre-dating `compiler/` split cites old paths.
- **Run the slow attributing instruments (survey, corpus-ab) BEFORE committing** a checker/type-utils/lib change; three
  commits once existed only to repair the one before. `test-vsdg` and the parser tests too, not just towasm/checker/gate/
  difftest (a pattern-default lowering was wrong for days because it was never run).
- "File X compiles" means nothing alone: towasm is demand-driven, a file of exported generics with no driver emits an empty
  module. The suite was structurally blind to module-level aggregate state until tests were written for it.
- A top-level const is reached from THREE directions (the start function, `lazyGlobalFor`, and `case 'call'` going straight
  to `ensureLazyGlobal`); fixing one or two looks like progress and leaves the bug.

## Design invariants and facts (the checker/codegen contract)

**Identity and layout**
- Struct identity is the physical LAYOUT, not the type's printed text: wasm struct fields are mutable, hence invariant, so
  two instantiations with the same layout but two structs can never convert. One struct per layout (`ownsLayout`/
  `layoutArgKey`/`layoutTwin`): a scalar or typed-array-tag argument gets its own struct, a reference argument erases to its
  constraint. Keying per TS argument was tried and failed (unconvertible `R<C>`/`R<{x}>`; polymorphic recursion overflow).
  Any keying that can grow without bound needs a finite key set, not a guard. "Log the LAYOUT, not just the key."
- Shared PHYSICAL storage for ref elements (`arr:ref`) is right (wasm-GC arrays are invariant); shared CLASS identity for
  `Array<T>` is the over-reach (the collapse of `Array<T>` to `Array<any>`). **Do not monomorphize per T** (measured:
  difftest unsupported 16 -> 71); adapt callbacks at the boundary (coerce each arg, both sides must be REFERENCE types -- a
  scalar mismatch is lossy and must stay an error). Concrete decoupling: pin `Array<T>`'s `thisWtype` to the element
  kind's array type, coerce element reads/writes inside methods.
- A named alias/interface and the identical inlined shape must share one struct, keyed structurally; a real `class` stays
  nominal. `matchObjectShape`'s "exactly one candidate" scans must dedupe by identity.
- Generic interfaces: one struct per layout (above). `interface X extends Y`: X's wasm type is a SUBTYPE of Y (Y's full
  layout, expandos and `#ext` included, repeated as the prefix). Any set of structs with a common field layout can be given
  a base retroactively (closures share `{(ref func),(ref $envBase)}` -> the `typeof x === 'function'` tag).
- A named struct passed where a STRUCTURAL type is expected: user decision -- MONOMORPHIZE the callee per concrete argument
  struct (direct field reads, same object, mutations visible).
- bigint has TWO physical forms (literal = `i64.const`; `BigInt` class = `u32[]`); `typeofHeapType` conflates bigint limbs
  with `boolean[]`; `bigCompare` is sign-first and sign-extended. `number`/`boolean` both lower to `f64`/`i32`: `emitAs` asks
  the checker which when BOXING and unboxing must mirror it (a numeric LITERAL type has compact integer storage).
- A string and a real array share `arr:i16`: only the checker's type tells them apart (`''` is falsy, `[]` truthy).
- Every scalar can be null-boxed (a box is a one-field struct); `u32`/`u64` normalise to their signed twins. `any` is
  NULLABLE (`REF_ANY_NULLABLE`); optional fields are null-boxed (so `??=` leaves a stored `0` alone). Anything entering an
  `any` slot must be in its logical type's canonical form (use `T.lookupMember`'s declared type, not the getter body's).
- `FunctionContext.temp` compares scratch types by `wasmTypeKey`, not identity.
- Array patterns lower to indexing only for arrays/tuples; iterables go through the iteration protocol (user decision
  2026-09-13): `iteratesByProtocol` drives `for...of` and array patterns, Map/Set iterate live through the lib generator
  `__towasm_indexed`. A pattern default applies where the element is `undefined`, never for `null`.
- Intersection of an array and extra properties (`ReadonlyArray<string> & {raw}`, `WithTextPos<T>`): physically the
  array; `arrayPartOf` finds it and BOTH `typeOf` and `ownerFor` go through it; the extras get no slot. Match each part's
  own WRITTEN shape, never through `T.resolve` (resolving `Array<string>` expands the class and loses what's sought).
- A static member cannot see its class's type parameters (real TS); `substituteClassTypeParam` restores statics verbatim.

**Resolution and scopes**
- Anything that runs WHILE a shape is being resolved must ask the CHECKER (`isAssignable`, `lookupMember`), never `typeOf`:
  `buildObjectShape` survives recursive types only via a placeholder struct registered before members resolve, and a
  `typeOf` from inside re-enters below it and never terminates. `typeOfActive` only catches re-entry on the SAME node.
- `T.resolve` does not resolve union members and a `never` member makes a union look unanswerable: use
  `T.unionMembers(t, scope)` (RAW members, deliberately -- resolved members break `ownerFor`'s nominal `ref` fast path);
  `isUninhabited` for `never`. The owner-resolving paths (`flattenOwners`, the dispatch gates) keep their own raw walks.
- `narrowedTypeOf` vs `ctx.scope`: `ctx.scope` is the baseline; consult the narrowed scope only where the baseline is `any`
  (taking it unconditionally resolved a clean nominal `Map<K,V>` into its structural shape and broke `set`'s `this`).
  Narrowing introduced inside an expression (ternary branch, `&&`/`||` right operand) is re-derived by codegen with the
  exported pure `narrow`. Synthetic statements (for-of/destructuring `var_decl`s) are never stamped. A generic INSTANCE loses
  all stamps (`substituteTypeParams` deletes them) -- re-check each instance as its own declaration (`instantiateDecl`);
  reading the template's narrowing through the instance's args cannot work. Still stale: generic METHOD instances and
  generic closure literals erased to bounds.
- Imported modules ARE checked (`checkHoisted`, muted, stamping, once per module record); a module-local name in an imported
  function resolves through the module's INTERNAL scope (stamped by `exportScope`), not `libGlobal`. `ClassInfo` records its
  declaring scope + canonical path; read `homeModule` off the ORIGINAL decl (an instantiation replaces `decl`). A `typeof X`
  type query carries its declaring scope. A lazy global's initializer compiles in `moduleScopeOf(homeModule)`.
  `__dirname`/`__filename` are per-MODULE bindings (`checker.bindModuleNames`), never lib globals.
- Class member `sealed` leniency is gone; a nullish member is never "narrower" (assignability is not subtyping for
  `undefined`); an inferred type predicate is valid only when its false branch is exact (TS 5.5); `super` is bound to the
  base class (`classBodyScopes`, key `'super()'` for the constructor call). Guard exclusion uses `precise` assignability.
- **`staticGuard` DELETES code on precise assignability, so any leniency left in precise mode is a miscompile, not a missed
  error** (function arity was unchecked; `has0args(f2)` folded to `true`). Still lenient in precise mode: parameter TYPES,
  an object with a call member as any function, a missing return type.
- A callback nested in an argument keeps the FIRST context it is typed in: any pass that types arguments before the final
  one (an overload trial, towasm re-asking) must use the final pass's context (`argContext`). Overloads: towasm picks a
  body with the checker's per-candidate test (`candidateFits`); a member with several bodies needs `@ts-expect-error` on
  EVERY body; the lib's own tsc error set must equal HEAD's pre-existing set.
- DO NOT TIGHTEN `isAssignable` before type-argument inference is precise: the leniencies absorb errors inference creates
  (constraint-instead-of-argument substitution is the recurring culprit); tightening first turns silent imprecision into
  false positives, which block `tsw` outright. Order: precision first, then tighten. See [[tison_workaround_inventory]].

**Globals, modules, lib**
- Module-level state: a top-level `const`/`let` of a non-constant value is a null slot + wrapper that runs the initializer
  ONCE (`ensureLazyGlobal`; the start function FORCES the wrapper rather than re-emitting); entry-module declarators live in
  `topLevelVars`; a non-entry scalar's slot is a BOX and goes through `coerceTop`. A closure never captures a module-level
  const (`resolvesGlobally`, like namespace imports). Static lib globals have ONE identity (`'#lib'`) for the whole lib --
  per-file or per-caller identity would give each referencing module its own copy of shared state.
- `lib/*.ts` proper is STATIC (concatenated into `LIB_AST`, globbed with `lib.d.ts` first, linked into every module); `lib/node/*.ts`
  is ON DEMAND (ordinary modules resolved by `ModuleLoader.get0` ahead of `node_modules`; adding a builtin is a new file).
  Rules for `lib/node/*`: reference the static lib, NEVER `import` it (a second bump-allocator `heap` over one memory =
  silent corruption; ambient-declare in `lib.d.ts`); `const x = __asm<...>('...')` binds in ANY module now, but allocator
  rules stand: `heap` is a bump OFFSET, only `__allocMark`/`__allocRelease` reclaim, release only once survivors are in GC
  memory, and release BEFORE throwing. A host import in an on-demand module registers through `LIB_HOST_IMPORTS` (scans all
  module bodies). `readFileSync` concatenates per byte (quadratic, known).
- `lib.d.ts` restates by hand what `lib/*.ts` implements (two consumers: tsc under `noLib`, and `LIB_DECL_MAP`). The
  Error/Map duplicates are gone; **`Array`'s ambient `declare class` is the curated view of what `T[]` means and MUST STAY**
  (removing it took walker.ts 1 -> 29 checker errors; nothing but the survey's "checker errs" column caught it).
  `String`/`RegExp` cannot be global classes (`interface String` is needed for primitive mapping). A cross-lib-file
  reference to an `export`ed name needs an ambient declaration (the file is a module to tsc).
- Lib fidelity: wherever towasm's lib shape diverges from TS's, tsc-clean code gets checker errors (a no-arg `new Map()` is
  `Map<any,any>` in TS's overload, a generic class here). Index-write lowering uses `__get`/`__set` (renamed from
  `get`/`set`); structural fallback to `Map`'s real `get`/`set` only for an index-signature receiver.
- `{[k:string]: V}` routes to `Map<string,V>`; dot and bracket reads are the same access (routed ahead of getter/field).
- `Number('abc')` is NaN, not `parseFloat`; the primitive wrappers' CALL lowers to the constructor, which must really
  convert; edge cases written first find unrelated lib bugs (`getUnsigned` off-by-one, `String(NaN)`, `bigFromNumber` sign).
- A WASI `path_open` must ask for exact rights (all-ones -> ENOTCAPABLE); discarded errnos make garbage lengths that look
  like hangs; this runtime's `charCodeAt` TRAPS out of range where JS gives NaN. `tsw` instantiates the bytes before
  writing (`new WebAssembly.Module`, not `validate`) but a host-capability message (`--experimental`/`not enabled`/
  `unsupported feature`) warns and still writes (node needs `--experimental-wasm-exnref` for exception handling).
- Memory is declared when the emitted code actually uses a memory instruction -- not by the NAME of an allocator global
  (name special-casing).
- Async: each EXPORT is re-pointed at a wrapper (`__towasm_exitCall`) that drains the microtask queue after the real call;
  "outermost" is STRUCTURAL (only the export table points at wrappers, so no depth counter), gated on the `microtasks`
  lazy-global slot existing. A host call to an export IS the job. Resolve-then-read in the same synchronous call gives 0,
  as in real JS; tests that asserted otherwise were wrong-per-JS (verified in node).

**Dynamic `any` (design decisions)**
- Truthiness/`typeof`/`in`/field read on a boxed `any` are one project (`emitAnyTruthy`, `ensureAnyIn`, `ensureAnyField`
  sharing `lateWorklist` deferral since the candidate set is "every class ever reached"). `typeof x === 'object'` is the
  COMPLEMENT of the tags that have a physical form. `typeof x === 'lit'` is static where the checker settles it, a null
  test where only nullability varies, else `ref.test` for the four one-form tags. `any` is never a boolean condition by
  guessing: find what types it as `any` upstream.
- Calls on `any`/`unknown` (user decision 2026-09-13): DYNAMIC CALL CONVENTION -- boxed args to a per-(name, arity)
  dispatch type-testing the value against every reachable class and closure type (`ensureAnyCallDispatch`,
  `ensureAnyDispatch`); a closure is `{code, env, length}` (`fn.length` for `has0args`). Limit: a closure type first
  registered in the late worklist is not a candidate. `(x as T)` as a method owner on `unknown` is UNSOUND (tried, removed).
- Expandos on untyped receivers (`stampPos<T>` writes `pos` through `T`/`any`): `collectReceivedExpandos` follows the
  receiver backwards to its sources (param -> callers' args, local -> assigned values, call -> callees' returns, function
  values tracked to a fixpoint). Holes: trails ending at a value typed `any`, function values stored in fields -- a stamp
  reaching one hits `unreachable` at RUN time, invisible to the survey. A jump in a row from 0 to 34 is not "blocker order"
  until struct layouts (`super=`) are compared.
- Defaults: a default that can't be re-emitted at the call site is applied in the CALLEE (`let p = #param$i ?? <default>`,
  `defaultsWithImplicitUndefined`); a closure literal follows its WANTED slot (forcing every closure default into the callee
  broke `fnLength`).
- Nested functions are hoisted per statement list (`emitStmts`, created before the first statement mentioning them);
  a closure in its own initializer finds itself via `FunctionContext.initializing` (don't widen the shallow forward-holder
  scan to outer blocks). A name-based mention test must respect shadowing.
- `&&`/`||` yield an OPERAND; `%` is fmod (`|x|<|y| -> x`, copysign); `!` routes through `emitTruthy`; NaN is falsy
  (`abs(x) > 0`); `null === undefined` is false (separated statically); never extend that to a type carrying NEITHER nullish
  kind (this compiler hands back a physical `undefined` where the type says it can't be).

## User decisions on record (don't re-litigate)

Dynamic call convention for `any` (above); iterate by protocol, not by materializing; monomorphize generic interfaces
per layout; monomorphize callees for structural params; static overloads via the checker's per-candidate test rather than a
run-time `instanceof` split; rename the index convention to `__get`/`__set`; skip tableCache.ts; do not embed the lib to
dodge a blocker; embedding/rewriting a target is never the answer; fix type-argument precision before tightening
assignability; pick work by the cause table's breadth, not by file order (the phased by-file roadmap in
`~/.claude/plans/witty-plotting-kernighan.md` is the wrong cut).

## Recorded-open as of 2026-09-14 (verify against the handoff before working any of these)

- Checker: `for...of` over a tuple value; lib `IteratorResult` is one class, not TS's discriminated union (so a user
  iterator's yield comes out `Y | R`); a generator returning `undefined` throws "unsupported return type" (`void` works);
  `Map` assignable to `{[k:string]: V}` (unverified, A/B first); `ts-parser` drops a declared `this:` parameter; a class
  field typed only by its INITIALIZER reads as `any` (annotate fields in checker tests).
- Codegen: mutual recursion between nested functions (`ensureForwardHolder` scans only `var_decl` siblings); the intrinsic
  `object` type has no representation (should be a non-null `anyref`); computed-key read/write on an `any` receiver
  (`out[k]`, `(OP as any)[v.op]` -- needs a generated per-class property dispatch or a dynamic object representation);
  `Array.sort` default comparator must compare by STRING conversion and sort IN PLACE (two further codegen bugs block the
  fix: `String(a) < String(b)` -> "local '$exp' redeclared", in-place `Array._copy` over `this` -> illegal cast; `_copy` with
  the destination first needs an explicit `<T>`); a defaulted-trailing-param function can't coerce to a shorter signature
  in every case; `??=` on `f32`/`i64`/`u32` optional fields; an assignment to a lib module-level global wrote a LOCAL
  (re-check); a type admitting `null` as a default param is rejected; async/generator functions reject defaults;
  a generic INTERFACE `T[]` field `arr:ref` vs `arr:f64` at one use site (two physical forms, no aliasing-preserving
  conversion) -- partly addressed by layout keying.
- Instrument: tableCache.ts is out of scope; making `ModuleLoader` read package `exports` would fix `tsw`-the-CLI too (the
  survey works around it with a `paths` option mapping `@isopodlabs/*/` to the sibling `src/` trees, because a `.d.ts`
  has no bodies to compile).
