---
name: tison-session-handoff
description: LIVE cold-start state for the wasm-backend work — where things stand, what is in progress, what the user has not decided. Read this before anything else.
metadata:
  node_type: memory
  type: project
  modified: 2026-09-29
---

**Read this first, and usually instead of [[tison-towasm-self-hosting-plan]]** (2233 lines — open it only for the
history of a specific row). This file is live state: **rewrite it wholesale, do not append.** Target ~120 lines.

## Latest (2026-09-30)

**DONE `1295278`: dynamic-object step 2.** An EMPTY literal whose context names no layout (`any`/`unknown`/`{}`/`object`/none) is
`DynamicObject<any>` (`contextualDynamicOwner`, now ahead of the union-member match); `collectExpandoFields` puts no expando on a
member-less shape (it had been one program-wide struct for every `{}`).
**DONE `2d786a5`+`b84847a`: the `EnumValue<EnumType>` row.** Root: `keyof (A | B)` was `never` and `(A|B)[K]` never distributed.
Now TS's key sets (`keysOf` in resolve's `keyof`: aliases PEELED not resolved, so `keyof Record<string,T>` stays `string`; a
string index adds `number`; union = intersect, intersection = union; private/#members dropped), union-object and union-key
indexed access, a homomorphic mapped type over an object maps its MEMBERS (index signatures kept), `{[K in never]: X}` is `{}`.
**DONE `ce614e6` (user approved 2026-09-30): a generic conditional stays DEFERRED, as TS's** (`deferred` in type-core): kept as a
conditional unless definitely true (strict) or TS's `T extends U ? T : never` simplification; an `any` check still takes both
branches. Relations: conditional source through `deferredBranches`, conditional target = fits both branches. `isAbstract(keyof P)`
is back. Exposed + fixed in the same commit: a generic TARGET signature binds its type params (both sides; `inProgress` shared,
no depth spent); `stampScope` stamped a nested generic signature's own `T` with the outer scope; `instantiateInContextOf` passed
scopes swapped; an arrow adopts a generic context's type params; **TS 3.4 higher-order inference** (`liftGeneric`/`withLifted` in
checker: generic-function args deferred, instantiated where the context is determined, else lifted fresh into their own scope).
wasm.ts probe 42 s / 2.2 GB. Known gap: an UNDECLARED name relates to anything, even strict.
**DONE `274886b` (user approved): numeric keys.** `JS.Key = string | number | {computed}`; `numberKey` returns the number; only
`keyof` reads it, everything else names via `JS.keyName`/`String`. Noted: `0 | 16` is held as a numeric RANGE (prints `number`).
Corpus since dd64ba2: ERROR 1005 -> 999; every new error in between was checked against real tsc.
**Survey at `b84847a`** (SURVEY_HEAP_MB=6144; banner-marked only for the user's scad_parser.ts): 314/403, 107 failures / 35
causes. backend.ts is MEASURED again (its worker had crashed), so +62 probeable. Top rows:
- **60, backend.ts + wasm-codegen.ts: `Invalid string length`** -- `resolvePlace`'s "is indexed but is not an array" message
  prints `T.typeKey` of makeAsm's `I` (the TreeBuilder fluent type, exponential to print) and overflows. Two bugs: the MESSAGE
  (needs a bounded printer), and the REAL cause, `I[type]` (wasm-codegen.ts ~938): an object indexed by a union of literal
  keys (`type` is a scalar-name union), which `resolvePlace` only handles for arrays. `probe-decl.ts` takes `STACK_DEPTH=80`.
- **6, wasm.ts: `unknown method 'as'`** on `bin.as(SLEB128, ...)` (top-level `const S32`, wasm.ts:47) -- `bin` read as an object
  whose type lacks `as` (star re-export via `export * from './types'`). A 3-module repro of the same shape compiled fine.

## Earlier (2026-09-29, late)

**DONE `302be07`: type parameters are opaque, as TS's** (the user chose TS's model before dynamic-object step 2). `resolve`
keeps a type parameter as itself; unconstrained is `unknown` (`{}` without strictNullChecks); `unknown` is a top type only
as a TARGET; `this` in `class C<V>` is `C<V>` (codegen's instantiation copy is stamped `instanceOf`). The commit message
lists the ~15 TS rules the change exposed as missing, each implemented. **Scale:** fluent builders (`B<T & F<T>>`) double
per step, so printed keys (`typeKey`) are exponential there -- use `T.typeId` (structural hash, DAG-linear) for any
equality/cache/set key on types; `resolve` also caches expensive kinds by scoped `typeId`.
Survey: run with **SURVEY_HEAP_MB=6144** -- backend.ts slice 0 peaks at 6.1 GB (1303 s; the pre-`302be07` compiler needed
4.1 GB, so the 2 GB default never fit it). `da19727` cut the rest: `typeId` lives on the node and skips checker stamps,
resolve's structural cache is weak. 314/341 compile; top row `EnumValue<EnumType>` has no representation (6, wasm.ts).
Instruments for memory: `assistant/inspect-heap.mjs <port> [secs]` (live-allocation sampling by caller, the twin of
`inspect-profile.mjs`); a crashed probe writes no `--cpu-prof`, so attach an inspector instead. Corpus +145 vs
`0e3b11b`, but 120 are true positives in a test with no `.errors.txt` and most others match real tsc
(`assistant/tsc-classify.ts` runs real tsc on corpus files; TS 6 defaults `strict` ON, the corpus assumes OFF). 6 genuine
FPs left (listed in the commit). Instruments: `assistant/esnext-snippet.ts '<src>'` checks a snippet against
lib.esnext.full exactly as test-checker does; `probe-decl.ts` prints a throw's stack with `STACK=1`.

**Dynamic objects (TreeBuilder in binary-libs wasm.ts), four steps, the user chose option 2:**
1. DONE `68e9cb5`: `{[k: string]: V}` is the lib's `DynamicObject<V>` (map.ts); `dynamicObjectArms` in every erased cascade.
   The spread clone (`ensureAnySpreadClone`) has NO arm yet.
2. DONE `1295278` (above).
3. NEXT: a callable object gaining run-time-keyed properties (`Object.assign(anyFn, anyObj)`, `tb/c.ts`).
4. Undecided: the built dynamic object read statically as `T`; `this as never` across instantiations (`tb/d.ts`).

## Before (2026-09-28, evening)

Survey top row `unresolved identifier 'Uint8Array'` (55) is CLOSED: `LIB_DECLS` skipped the lib's `declare global` vars, so a
closure naming `Uint8Array` took it for a capture. Then `makeAsm` hit `wasm.Instr` narrowing to `never` under `'k' in i`; three
roots fixed: numeric keys were source text (`0x20` named "0x20", not "32" -- `numberKey`/`numberValue` in js-parser), a type
index by a number (`T[1]`) never resolved (`T.literalKey`), and the type printer dropped `typeof f<A>`'s type args so `typeKey`
merged instantiations (Instr: 33 members -> 546). Corpus A/B ERROR -24, all false positives.
**DONE (the user chose the closure-subtype design): callable objects** -- a shape with call signature(s) and fields is a struct
extending the closure struct ([[tison-representation-table]] has the row). wasm.ts's `I.more({ i32: Object.assign(function ...,
{...}) })` values now compile. **Next blocker on makeAsm: `TreeBuilder.more`'s own body is dynamic** --
`Object.assign(v, existing)` between two `any`s ("needs sources that write their keys out") and `(this.root as any)[k] = ...`.
Not built: `Object.assign` onto an EXISTING callable object (a later mutation, not creation), and a function-typed value that
flows into a callable-object slot other than as a literal (no fields to build it with -- honestly unsupported).
Still open from before: C1 (a var_decl checks its initializer WIDENED -- now also `const x: 10n = 10n` is rejected);
`test-ts-parser` dies on `dwg/` (the user's local edit skips it); tison's `Promise` is no `PromiseLike`;
`Promise<number>.then(async z => 2)` exhausts isAssignable's depth. `assistant/diag-snippet.ts '<src>'` prints a snippet's
checker diagnostics.

## Earlier 2026-09-28

Commits `51684da`..`9afb355`: TS2304 behind `Scope.unknownNames`, `import()`/`import.meta`/`globalThis` modelled, isAssignable
coinductive for ref pairs, TS inference priority, TS's strict callback rule (`callbackPair`/`callbackRelated`), union-target
inference, explicit type args filter overloads by arity (`typeArgArityFits`). Variance MEASUREMENT was built and dropped (900+
depth exhaustions per measurement).

## Before: HEAD `ed4944c` (2026-09-27, late)

Survey at `bc160d4` (clean baseline): 312/403, top row `closure parameter 'a'` (59, backend.ts + wasm-codegen.ts).
That was a REGRESSION from `f2b24e9`, bisected: the lib lacked `ArrayBufferLike`, `isAbstract` reads an undeclared
name as an unbound type param, and the now-uncapped `mentionsAbstract` reached it inside `wasm.Instr`, so
`ReadType<T[keyof T]>` never distributed and `Instr['op']` was `any`. `ed4944c` declares it; those decls are back at
**`unresolved identifier 'Uint8Array'` -- the next blocker** (probe `makeAsm` in wasm-codegen.ts). Trap: an undeclared
TYPE name is silently "abstract" (no TS2304 for types) -- suspect a missing lib name whenever a conditional over
concrete-looking types stays deferred. Probe with snapshot paths: the live `binary/src` has the user's uncommitted edits.

## Before: HEAD `a47fe3f`+ (2026-09-27)

2026-09-27: tasks A/B/C of the consolidation brief landed (`07c4d12`, `0465a3b`, `e4d9677`, `a47fe3f`), described under
Queued 2. Survey 312/403 at `a47fe3f`, no REGRESSED (a transient 60-row regression from `07c4d12` was fixed by `e4d9677`); the 60 Generator rows moved to `unknown field 'id'`. Instrument: `assistant/suite-wat-diff.py before.out after.out` names the towasm tests whose
printed WAT changed (capture `npx ts-node -T compiler/test/test-towasm.ts > x.out` on each side).

## Earlier: HEAD `a5043ab`+ (2026-09-26)

The direction since 2026-09-21 (the user's): backend.ts had grown by giving each failing case its own path, because
it RE-DERIVED types the checker already knew. Now **the checker stamps each expression's type**
(`checkedTypeOf`, [[tison-checker-type-stamps]]) and **representation is the backend's own choice**
([[tison-representation-table]]). Landed, in order: consolidation steps 5/4/1 (W.Type guards; one closure-call
path; one runtime-helper mechanism) · checker stamps (94% coverage) · narrowing machinery deleted (`stmtScope`,
`inNarrowed`, `typeScope`) · canonical boxing (`coerceValue`) and a `const` keeping its scalar · range widening for
bigint lets · **bigints as `i32`/`i64` where the checker proves the range** · `Number(any)` picks the overload that
dispatches at run time · a string literal materialized once per program · generator/async functions registered
under their module-qualified name (were colliding into a malformed module).
backend.ts 11,003 → ~10,500 lines. Gates at `70edf4d`: difftest 2227/2234 · 0 disagree · 7 unsupported (the same 7
as baseline), towasm, checker, four tsconfigs, corpus A/B unchanged.

## DONE 2026-09-25: the interrupted resumable unification (`2c4b61a`)

`resumableFrame`/`emitResumableBody`/`emitFrameInit`/`compileResumableOuter` are shared by generators and async
functions; `emitResumableDispatch` owns its loop (`loadState`). Proven a pure refactor: the towasm suite's generated
WAT is byte-identical (213,104 lines). **A WAT A/B over the suite is the check for any refactor that claims no
behaviour change** -- stronger than difftest agreeing.

## DONE 2026-09-25: the checker owns flow and numeric ranges

- `42d3a6e` accessor pairs carry a `writeType`; `ed1813d` `.length` is `u32`, pseudo-types are ranges (`toRange`),
  inference unforces a pseudo-type candidate to `number`.
- `c660e4c` **checkStmt returns its flow** (`undefined` = never falls out); `joinFlow` merges at every merge point;
  `break`/`continue` deliver to a `FlowTarget` on the scope; a loop head iterates QUIETLY (`Scope.quiet`: no stamps,
  no reports) to a fixpoint, then one real walk. Deleted assignRights/alwaysExits/endsFunction & co.
- `6ac49b9` **numeric ranges in the flow**: declarations/assignments/steps narrow to ranges; `rangeStep` = the
  USER'S RULE (`++`/`--`/`+= a`/`-= a`/`x = x +- a` never overflow the i32, else i64, both sides fit); loop heads
  `rangeWiden` to machine limits then step down to recover a test's bound; `combineTypes` merges true intervals.
- `bc05d03` **a `let`'s representation = the hull of its stamped reads+writes** (`d.flowType`, via `Scope.binding`,
  crossing closures); backend `slotType` names an integer range as `i32`/`u32`. collectRangeWidenings is GONE.
- Rules learned the hard way: a check narrows iff it reports, stamps, or is quiet -- a QUERY (backend
  `checkerTypeOf`) must not mutate its scope; never RESOLVE a declared type during hoisting (bakes an interface
  before a later lib block merges into it -- hit twice: `W.ARRAY`'s `Type`, `Intl.Collator`); never re-type an
  expression with `err` (duplicate diagnostics -- hit twice).
- Instruments: `assistant/src-errors.sh` (tison/src checker output, diff two trees -- the corpus misses tison-style
  code), `official-one.ts` (one corpus file as the harness checks it), `flowtype-dump.ts`, `flow-probe.ts`,
  `counter-bounds.ts`.

## Machine types (user's design, 2026-09-25)

`e155b70`: lib.d.ts declares `Int<Bits, Signed>`/`Float<Bits>` (built in: identified by being declared in the ROOT = lib
scope, since tsc rejects `intrinsic` outside its own libs and checks this lib) and `i8..u64/f32/f64` as applications.
`T.machineOf(t, scope)` follows the alias chain from the DECLARATION (never a name); `T.machineRange`. WASM_PSEUDO_TYPES,
PSEUDO_RANGES and the builtinTypes rows are gone. User decisions: an annotation is TRUSTED, not checked -- the value is converted into its slot
automatically, and SATURATING (`trunc_sat`) is fine (user, 2026-09-25: the point is the automatic conversion); a machine type's JS semantics are `number`'s for Bits <= 53 and `bigint`'s above (i64/u64).

## Queued

1. DONE `6de123e` (`Int<64>` bigint-valued) and `0ce7fc3` (typed-array ELEMENTS are `T`: `assemble` asm switches
   on `$T`, bigint `__set` overload via `bigWord`, `TYPED_ARRAY_RANGES` deleted). Rules it settled: `machineSlot` is
   honest (i8/i16 -> i32, u8/u16 -> u32, u64 its own); a NUMBER's box is ALWAYS `f64` (into `any` and into a nullable
   union) whatever its compact form; constructors specialise structurally like functions; an index write stores the
   SETTER's parameter type; `hasMethod` checks accessors without overload resolution (inherited too).
   Rawness is NAMED (user: Array is never a special case); a non-escaping param specialises; readonly alone doesn't
   make a copy sound.
   DONE `7589a98`: a slot holding two array storages opens PER DECLARATION (user chose per-slot over per-type and over
   copying; aliasing kept). `Scope.declarator` gives a name's declaring node; `collectOpenShapes` returns `openSlots`/
   `openReads`; codegen's `OPEN_SLOT` marks an open slot's type. **Still per-TYPE (correct, program-wide):** flows into an
   array element, a method parameter (methods aren't specialised per layout; overrides share a signature), a closure
   parameter, a function return. A packed rest bundle (`a.push(x)` on a `u8[]`, `...xs: u8[]`) is built as a packed
   literal is (`elementValueType`); out-of-range values WRAP (packed `array.set`), not saturate.
2. DONE consolidation step 2 (`8e08db3`, `3076e31`): one `resolvePlace(target, ctx, write)` classifies every place for reads
   and writes; `Place` = operands (each emitted at a given wtype) + `load`/`store`; `emitPlaceRead` does `?.` and bounded
   reads generically. Audit leftovers judged NOT worth it (measured 2026-09-26): the function-body prelude (its 5 scope-root
   orders are deliberate -- a function's `declScope` is its most specific scope, a class's is unreliable, a lazy global's
   must win; ~30 lines of boilerplate left), generator/async (already factored to what differs; ~15 lines).
   **DONE 2026-09-26: call resolution reads the checker's stamp (steps 1-2).** `checkedCallOf(e)` = `{ sig, typeArgs }` (`8f5d640`),
   safe to consume since `db83cf8` (no overload-TRIAL or quiet-loop stamps; `unstamped` strips it; `CallSig.origin` names the member
   a signature came from, kept by `lookupMember`). The lib's double description was the blocker; the user chose option 1 (the
   checker resolves what codegen compiles): `544b0d8` typed-array values are `typeof TypedArray<u8>` etc. in typedarray.ts's
   `declare global` (TS instantiation expressions + `declare global` in a global-space block are checker features now; a
   MODULE's `declare global` is still ignored -- hoisting it locally shadowed a global it must merge with, +2 corpus FPs).
   Backend `416cc54`: a call site is `CallSite` = the source node, or bare args for a call codegen makes itself;
   `resolvedCall` resolves the latter as the same call on a receiver typed as the implementation (`$receiver` in a child scope),
   and `Number(x)`/`BigInt(x)`/`String(x)` (codegen LOWERS a call on a class to its constructor) as `new` on the class.
   `implementationOf` = the one body, or the one `sig.origin` names (`namedBody`, through `templateOf` for a generic
   instance's copied members) + the any-argument widest POLICY. `callTypeArgs` = the stamp's type args where it resolved the
   compiled decl, else the decl's type params inferred from the resolved signature as instantiated (an overload's generic
   implementation: `Array.reduce`) + the storage-refinement POLICY. DELETED: `inferCallTypeArgs`, `overloadForArgs`, the
   checker's `resolveOverload`. Type-arg disagreements with the old re-derivation, decided: the checker is right each time --
   `isL<K extends keyof TM>(t, 'string')` keeps `K = "string"` (the old `string` broke the constraint), `rules(rule(a),
   rule(b))` instantiates each inner call at its own callback (was the outer union), a callback annotated `[string, Node]`
   is not `readonly`; an alias expanded to its object type (`Pair`) is the same type (checker cosmetics, not fixed). WAT
   +71 lines (+0.03%): two tests compile one more instance each, for those two decisions.
   Survey after `416cc54`: 132 decls REGRESSED, all one cause -- a stamp is taken when a closure is first checked, and a
   `let`/`const` declared LATER in its block was unbound (`any`) there. `2491c21`: `hoist` binds each lazily
   (`Scope.addLazyValue`, typed by `hoistVar` into a throwaway scope on first read); speculative walks (`trying`) stamp no
   scope, flow slot or callback context either. That walk runs OUT OF ORDER, while earlier declarations are placeholders, so
   what it writes onto the AST (a callback's fixed parameters, an arrow's inferred return, `lazyReturnType`'s memo) is undone
   after it (`ahead`/`written`: property descriptors restored) -- else 36 grammar decls (ts-parser/js-parser) regressed. `134ae8c`: an implementation's type args (a lib.d.ts declaration compiled from lib/*.ts) come from a plain
   structural match of declared types, not value inference (which reads `u8` as `number`). Then: an assignment's value is
   contextually typed by the target's DECLARED type (TS never narrows a target); +2 corpus "false positives" are TRUE errors
   tsc reports too -- excessPropertyCheckWithUnions.ts has no `.errors.txt` in the checkout, so the corpus calls it tsc-clean.
   **DONE 2026-09-28 (user chose it): TS's inference PRIORITY.** `settleFromReturn` is deleted: a callback's return outranks
   the destination, which only fills a parameter nothing else spoke for (`Inference.inferred`'s fallback). Codegen keeps the
   caller's layout by FLOW instead: `callTypeArgs` instantiates a generic call with the destination's type argument where the
   checker's is an ANONYMOUS object shape, the destination is struct shapes (`isStructShapes`: no `any`/index signature/
   scalar -- widening into a `Record` made `stampPos<T>` a `Map` and regressed 135 survey decls), and every argument still
   fits (`argsFit`). Tried and dropped as unneeded: building the literal from a stamped flow slot (`flowOwner`). DONE: a namespace qualifying a call builds no object (`395543b`); a union of generic
   instances meets the union it is passed as (`04f1229`, fixed by `f198436`: a value member pairs ONLY with its own
   declaration's instantiation, and a NON-class generic is sketched by `layoutArgs` as `openKey` keys it -- a class keeps its
   args' layouts, `ensureClass` collapses them only for a method-less class). The Generator blocker those rows then hit
   is DONE (`0465a3b`): a node codegen SYNTHESIZES (a for-of's `x[Symbol.iterator]()`, a desugared assignment) was re-typed
   in `ctx.scope`, which carries no flow narrowing (`sw.arms` inside `if (sw)` read as `any`, so `Set<any>`), while emission
   read the stamps. Checker `typeOf(..., overStamps)`: a query returns a stamped node's stamp; the backend's `checkerTypeOf`
   sets it exactly when the queried node is unstamped. DONE `8163238`+`9b3ee08`: that was DEPTH exhaustion -- `resolve`'s budget was shared down a
   chain of named aliases, so `Omit<Local,'type'>` over `ReadType<typeof Local>`, resolved deep in a whole program, came back
   empty. Each named alias body now resolves with its own budget (`resolveAliasBody`: same-args re-entry is a cycle, a nesting
   cap reports a GAP). Its cycle guard must be a WeakMap: a Map held every type entry and OOMed the survey's workers.
   DONE `0dc7a86`: `k in o` with a runtime key (`ensureAnyIn()` compares it with each representation's member names).
   **Next blocker on those 59 rows: `closure parameter 'a' needs an explicit ... type`** in makeAsm's `i.arms.find(a => ...)`.
   Root, pre-existing (same with the alias-budget change reverted): binary-libs' `wasm.Instr = bin.ReadType<typeof Instr>`,
   where `Instr` is a `bin.Switch(...)` over the whole opcode table (spreads of `mapTable(...)`), does NOT resolve in tison's
   checker -- a parameter typed `wasm.Instr` gets no representation and no errors, so `WatInstr` cannot narrow on `op` and the
   callback's `a` gets no contextual type. DONE `18bc93b`..`cc1e63e` (9 checker commits): generic spread, `infer` vs primitives/
   methods, PromiseLike, `!` context, union base-matching, variadic tuples, reverse mapped inference, type-param context,
   constraint-checked inference -- makeInstr/Switch/NoPromise now type. DONE `00c43ec`: the Instr runaway was resolve's depth
   BAIL (a conditional's taken branch spent depth; a bail uncaches every enclosing level) -- Instr now resolves and narrows
   in ~10 s. Survey after it: still 312/403, but the 55-row blocker moved on to `unresolved identifier 'Uint8Array'`
   (backend.ts, wasm-codegen.ts); next is `EnumValue<EnumType>` has no representation (7, wasm.ts). Then `a085b42`..`a7f6a56`
   fixed the false positives that exposed (predicate filter/find, keyof computed keys, per-key mapped index, flat). `f2b24e9`:
   conditionals distribute at their own node; the OOM that first blocked it was `mentionsAbstract` missing indexed/keyof/
   mapped/conditional kinds, so FlattenOps<S> over an abstract S looked concrete and unrolled. Also 3 peg.ts rows: `cannot convert Generator<any> to
   Generator<NonTerminal>` (the reverse direction; not investigated).
   **DONE step 3:** `classifyCall(e, ctx, want)` decides a call's `Callee` once (asm, `.call`, self-recursion, declared function incl.
   import/namespace, construct incl. `C(x)` on a class, `Object` intrinsic, builtin, static, method/super, union, any-dispatch,
   closure, any-callee); `emitCallee` emits it -- `case 'call'` and `case 'new'` are one line. `emitGuardedCall` is the one `?.` guard
   (method, union, dispatch, closure); `emitReceiverCall` the one receiver emitter; `dispatchArm` the one runtime-dispatch arm
   (`ensureAnyDispatch`, `ensureAnyCallDispatch`); `emitCall` lost its import/class fallback. Suite WAT byte-identical;
   backend.ts -52 lines. Not merged, deliberately: the analysis pass's two callee resolvers (`calleeOf` for escaping params,
   `monomorphized` for slots) answer slightly different questions (nested `function_decl`s), so unifying them is a behaviour change.
   DONE `e92fd8e`: `namedCallee` reads the stamp (arrow/function-expression signatures carry an `origin`).
   **Task 4 DONE** (`1b96123` compound assignment; `a47fe3f`): `emitShortCircuit` is the one lowering for `&&`/`||`/`??` and
   `&&=`/`||=`/`??=`; `admitsLiterals` the one literal-discriminant test (three shape matchers); `emitDiscarded`; the binary
   default arm keeps its decision order with one `identity` emitter. backend.ts -126 lines, suite WAT instruction-identical
   (local order only). `&&`/`||`'s `anyref` fallback for an unrepresentable result is gone (throws, as `??` did). NOT merged,
   judged not worth it: the object literal's three spread classifications (Map path, struct path, `emitUnionShapedLiteral`)
   use different owner resolvers (`ownerOf` / `flattenOwners` / `ownerFor`); unifying them is a behaviour change (the Map
   path would start handling anonymous-shape spreads). A candidate next step: native bigint comparisons (`s === 2n` on two
   machine-int bigints still widens both to limbs and calls `BigInt.eq`) and native unary `-`.
   DONE (`07c4d12`, `e4d9677`): a small bigint in a machine-int local. `scalarBinding`: a name whose binding is a machine
   scalar reads as it (`wtypeOf`, `operandInfo`); any other binding defers to its type (a boxed union narrowed to `number`
   must unbox -- letting every binding win regressed 60 survey rows via `negValue`). `wasmTypeOf` gives a bigint literal its
   machine int; `coerceTop` converts limbs into an `i32` slot (`bigWord`) as into `i64`, so a bigint op with no native form
   (`v / 2n`, `-t`) can land in a proven-small `let`.
   `assistant/callstamp-probe.ts '<src>'` prints a snippet's stamps (sig, origin, type args).
   **Survey regression from `7589a98` (found 2026-09-26, bisected):** 170 decls stopped compiling. Fixed: `anyVal[i] = v`
   (`541f9c3`, 133 decls); `noteTypes` opened an ARRAY type on differing element SKETCH, now on differing element STORAGE
   (`rawElemKind`) -- `Rules<any>` was opened against `any[]`, both `anyref` arrays (ts-parser.ts, 23 decls).
   Fixed too (js-parser.ts, 13 decls): an OVERLOADED function's implementation with an inferred return built its literal as a
   shape of its own, matched to the declared interface (`Rule<any>`) only if that class happened to be registered already --
   compile ORDER decided it. `overloadedReturn`: such an implementation returns, and builds, its signatures' return type
   (compileFunc and emitClosureLiteral). `probe-decl.ts` has `WAT=<regex>` to print matching functions.
3. Found, not fixed: numeric `let` messages print the precise value where tsc says `number`.
   DONE: `var` is function-scoped. Checker: a `var` binds in `scope.varScope()` (a `checkBlock` body -- function, program,
   static block -- or a namespace body; nested blocks use `checkNestedBlock`); `hoistVar`'s `home` binds, its `scope`
   types and narrows. Backend: `hoistVars` declares each at a body's entry, typed from the checker's binding in the
   body's scope (stamped on its first statement); `case 'var_decl'` then ASSIGNS. The entry module's `var`s (any block depth)
   are default-initialized mutable globals registered just before `__toplevel` (earlier, `typeOf(number[])` ran before
   the Array classes and broke type finality), and `__toplevel` assigns them; an imported module's takes the `let` path.
   **The checker never reports an unknown name** (no TS2304) -- see [[tison-unknown-name-diagnostic]] for the causes
   blocking it; `import(...)` typing and `globalThis` wait on the user.
   DONE `a5043ab`: u32 compares `_u`, mixed i32/u32 compare as f64 (NOT i64 -- an `i64` operand unboxes `any` as a
   bigint and trapped). `3a3f4ff`: limbs -> i64/u64 slot (low 64 bits, `bigWord`).
   DONE: 32-bit `+ - *` keeps 32 bits only where the checker's stamp (`typeAt(e, false)`) is i32/u32,
   else it is `f64` (exact JS); a compound op's proof is its SLOT. The checker stamps `x + a` in `x = x + a` with the
   STEPPED range (`stampStep`), so the user's never-overflows rule keeps such loops in `i32.add`.
   DONE: a literal operand's wtype is its own value's range, and a 32-bit `+ - *` operand's is what its op emits
   (`operandInfo`), so `s = s + i * 2` is all `i32`. `NumRange.integer` now EXCLUDES -0 (an i32 cannot hold it): `-x`
   with x possibly 0, `0 * -n`, a `-0` literal (`T.isIntValue`) are not ints; unary `-` reads the proven result too.
   u64 values compare/add via limbs (`BigInt_add`), correct but not the cheap path.

## Waiting on the user

**String cheap representation.** Done: each literal is materialized once (`4e654df`). The data segment is PASSIVE
(copy-only), so a bare `u32` offset cannot be a string -- nothing recovers its length or chars. Options put to the
user: (1) offset+length packed in an `i64` (`.length` a shift, materialize on char access); (2) bytes also in
linear memory (`charCodeAt`/compare/print read in place); (3) stop. Either changes how every discriminated union
(`type: 'call'`) is held -- their comparisons must work against both forms.

## Decided by the user -- do not re-open

- A stamp is a TYPE; the representation is the BACKEND's, free to be simpler, converting only where needed.
- Cheap forms are STACK representations; pseudo-types (`i32`…) are a separate mechanism that forces a slot's.
- A `const` may keep a narrower SCALAR its initializer built; a `let` takes a representation covering every
  assignment. Only immutable values -- `const a = [1,2]; a.push(3)` needs the `Array`.
- **No runtime checks** for cheap forms: only what the checker proves.
- VSDG is optional and runs BEFORE check+stamp; the backend compiles whatever AST it gets literally, in tree order.
- Erasure: prefers B (per-instantiation structs, a widening flow OPENS the slot); `a19b015` is the expedient A.
- Do NOT erase in the checker to match codegen. Inlining is a VSDG prepass, not a backend pass.

## The self-hosting survey -- OCCASIONALLY, never as a gate (user's call)

It is slow (~20-35 min) and causes friction: run it deliberately, not after every commit (2026-09-22 ran it per
commit -- don't). Gates are difftest, the corpus A/B (for checker/lib changes) and the suites. It does catch what
suites miss (it found the `x as T` operand gap), so run it after a change to how the backend READS types. Read
`REGRESSED` against a run with no **NOT A BASELINE** banner; the survey now hashes `tison/src` at start and end.
Run from the workspace root with the ABSOLUTE script path (a relative one failed when the shell cwd drifted).

## Open, NOT fixed

- **Codegen cannot narrow an `Array<any>` instance's result** to the array the checker types (`mixed.flat()`, a predicate
  `filter` over `(number|string)[]`): `cannot convert Array<any> to Array<number>`.
- Narrowing `g.t === 'MC'` does not drop an arm whose `t?: never`, and that fallback widens `{a: 1}` to `{a: number}`.
- wasm-codegen.ts (snapshot) still has 2 checker errors: 605 (callback return vs `ReadType<...>`) and 802
  (`{ref: 'any'}` vs `wasm.ParamType[]`); not investigated.
- **Diagnostic positions are the NEXT token's** (the LALR reduce stamps `actionTok.pos`), so an error can sit lines below
  its node; corpus A/B then shows a real tsc error on a different line. Fix: record each frame's first-token pos.
- A non-bare `declare const x: typeof f` annotation resolves eagerly at hoist time (probe with a type alias instead).
- `NoPromise<Promise<'z'>>` does not yield `'z'` (infer through `then`'s callback parameter); numeric key `0x00` prints as "0x00".

- **Found 2026-09-22:** `gen.next()` with `N = undefined` demands an argument (checker/lib);
  class-NAME triggers remain (`Map` in `ensureAnyEntries`, `Array` in `expandArrayMembers`); `var_decl`'s three
  statement-stamp queries decide representation and must wait for the layer (measured 7 → 15 unsupported).
- **`c1662ba` has NO regression test** (needs the `Record` shape actually OPEN and the param escaping).
- **Through `any`:** reading a dynamic object traps (it shares `Map`'s struct -- fix is a distinct struct, not a
  `Map` arm); a WRITE `anyVal[i] = v`; `anyTypedArray.length`; `any + any` assumes numbers; `m.get(k)` into `number`.
- **An array boxed into `any` with no element context cannot be narrowed back** (`arr:ref` vs `arr:f64`).
- The checker types `new Set([...a, ...b])` as `Set<any>` (masked by `3465685`, not repaired).
- `v.pos = 7` on `number[] & {pos}` is `unknown field` -- make the carrier `Array` where `arrayPartOf` answers.
- Flow-directed literal layout (deferred by the user) -- lalr.ts `makeLexer`'s literal escaping into `recover`.
- The `OneOf` precedence defect ([[tison-precedence-resolution]]); `termOneOf` is NOT the fix (user rejected it).
- The BigInt survey row (6) is an overload-resolution gap in `candidateFits`; unchosen.
- No definite-assignment diagnostic (TS2564/5); a closure capturing a HOST IMPORT does not resolve;
  `Buffer.toString` only 'latin1'/'binary'; `lib/node/fs.ts` compile-tested only.

## Architecture -- SETTLED, do not re-propose

**`TS/backend.ts` is the TS half, `wasm-codegen.ts` the neutral half; a file is earned by cross-language reuse
only.** `TSEmitter` is rejected. **Do not split `TS/backend.ts` for navigability** (the consolidation audit's
"step 9" is therefore off the table). Neutral extraction is exhausted, measured. Moving a genuinely neutral
function onto `FunctionContext`/`Types`/`ClassInfo` is still right. wasm-knowledge is NOT language-neutral
(`numericOpInline` encodes JS semantics). **`CPP/backend.ts` is the neutrality gate**: keep `test-cpp-backend.ts`
green.

## Contracts worth knowing before editing codegen

- `emitIf`/`emitBlock`/`emitLoop` own the levels they open; callers do no depth bookkeeping.
- Locals are named and freed by `FunctionContext`; wrap assignment sites in `ctx.inScope` or slots leak.
- `Types` owns the shapes and dedupes structurally; `closureTypes` is a signature REGISTRY, not a cache.
- `typeIndex: -1` is a real `ClassInfo` state; `thisWtype` is the "processed" test (`99325ea`).
- Every conversion of an emitted value goes through `coerceValue` (logical-type rules); `coerceTop` is physical only.
- **Never `git diff src/` wholesale for an A/B patch** -- name the files (it once captured the user's work).

## Tree state

**Never trust this line -- re-check `git status`; the user edits and commits concurrently.** At 2026-09-25:
At 2026-09-27 late: HEAD `ed4944c`; the user's uncommitted `src//scad_parser.ts` (it trips the survey's NOT A BASELINE check). Survey 312/403 at `bc160d4`.

Related: [[feedback-session-boundaries]], [[feedback-two-tier-gates]], [[tison-towasm]],
[[tison-checker-type-stamps]], [[tison-representation-table]].
