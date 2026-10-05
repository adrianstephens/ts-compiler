---
name: tison-workaround-inventory
description: Audit (2026-09-11, kept current to 2026-09-14) of every leniency / any-fallback / cast site in checker, type-utils, transform and the wasm backend -- what is NOT a workaround, what is still open (silent `any`, accepted-bad-code, towasm gaps) with the proper fix and order, and the checker rules learnt while removing them. Distilled 2026-09-30; per-fix history is in git (pre-distillation: 1c439ff).
metadata:
  type: project
---

Audit of the workaround markers (see `CLAUDE.md` "Fix problems; never work around them"), probed through `assistant/corpus-one.ts`
(lib.esnext.full, as the corpus). **Verdict: every site is fixable properly; none needs to stay lenient.** Order: B -> D -> C -> A
cleanup. B before C because B's `any`s both hide errors AND cost towasm typed codegen; C only accepts bad code. Interleave with the
corpus false positives, which outrank all of this by the priority rule (a false positive blocks `tsw`; a miss does not). When removing a
leniency exposes false positives, those are the real bugs: fix them, never restore the leniency.

**Method for each removal**: `corpus-ab.sh`, classify new errors per LINE against real tsc (`node_modules/.bin/tsc --ignoreConfig
--noEmit --strict --target es2022 file.ts` -- TS 6 refuses files beside a tsconfig otherwise), and ALWAYS re-run the WHOLE
`self-errors.sh`: one fix once removed 2 errors in type-utils/backend and silently added 9 in js-parser/ts-parser while the corpus A/B
was neutral (the corpus uses lib.esnext.full, so a towasm-lib-scope regression is invisible to it). The checker's own errors on tison's
sources went 74 -> ~16 over the leniency removals; the survey, not checker errors, is the unit of progress (7 of 14 files had zero
errors and compiled nothing).

## A. Not workarounds (TS does the same, or an endorsed convention) -- reword, don't remove

- Implicit `any` for an unannotated param/field/accessor with no initializer or context; circular inference -> `any` (TS 7022/7023, could
  emit those). Unresolved import -> `any`, diagnosed in transform.ts. `any` operands propagate.
- Depth-limit bails (`hitDepthLimit`): bounded budget, reported -- TS has 2589 for the same.
- towasm generic erasure (`p.constraint ?? T.ANY`): a codegen strategy, but it must erase to ONE layout per generic shape (`ownsLayout`,
  see [[tison_towasm_self_hosting_plan]]).
- towasm's ~45 `... not supported` throws: honest refusals (the header's gap list), not silent.
- `(x as any).pos` / `.scope` / `.contextualType` stamps: untyped stamping is the endorsed convention ([[feedback_no_checker_state]]).
  Cleanup only: `getPos()` exists; add one `scopeOf`/`stampScope` accessor pair so the cast lives in one place.
- checker.ts's header ("every gap errs lenient") states the old policy -- rewrite it.

## B. Missing modeling -> silent `any` (hides errors AND forces towasm onto boxed/dynamic paths)

DONE: iteration protocol (`T.iterationTypes`, `T.memberKey`); tagged templates; `yield` result / generator N type; `o.constructor`.
OPEN:
- **Indexed access with a non-literal key**: `o[k]` with `k: "a"|"b"` -> any. Fix: key's literal members -> union of member types;
  `keyof T` -> `T[K]`; a plain string without an index signature -> TS 7053.
- **Definite member absence**: `lookupMember` returns undefined for both "absent" and "can't tell", and `sealed()` is true only for
  object/intersection, so `"abc".nope`, `u.nope` on `string|number`, calling an uncallable non-object type `any` silently. Fix:
  three-valued lookup; primitives (via boxed), literals, unions (every member), class refs and functions are sealed. (Class-instance
  sealing is DONE -- see below; the rest is not.)
- **Uninferrable type param** -> `default ?? constraint ?? any`, sometimes with no GAP (`declare function g<T>(): T; g().foo` is silent);
  TS >= 3.5 infers `unknown`. `typeOf`'s `default: return T.ANY` -> exhaustive `never` switch; instantiation expression on a non-callable
  -> TS 2635.
- `?.` on a `never`/nullish-only receiver reports nothing (TS 2339 on never). Object rest in a destructuring pattern binds `any`;
  an array-literal initializer gets no contextual type from its binding pattern (TS's implied type). `super` in an OBJECT LITERAL method
  reads `any` (never a false positive). A declared `this:` parameter is dropped by ts-parser (deliberate: TS erases it at call sites), so a
  non-arrow function's own `this` is `any` with one; keeping it needs a non-positional `thisType` field on the signature.
- **A class field typed only by its INITIALIZER reads as `any`** through a reference to the class (`class K { f = 1 }; const q: string =
  k.f` is clean) -- look at `pendingFieldInit`'s lazy getter firing outside the class body. Tests annotate fields meanwhile.
- **Expando declared types**: `f.p = v` declares `p` but the declared type (union of ALL assignments, object literals normalized) isn't
  built, so `f.p` reads fall to untyped absence and assignment narrowing is skipped for expandos.
- Rest ARGUMENTS (`f(...xs)`) and positional arguments filling a rest parameter are not checked (`k("x")` against `...args: number[]` is
  clean). var_decl diagnostics land at the next token, not the declaration.
- **TS's own `MapConstructor` loses a mapped call's types**: `new Map([1,2].map(x => [String(x), x]))` infers `Map<any,any>` while a
  declared generic function of the same shape infers `<string, number>` -- look at `T.unionSignature` pre-empting the overload path in
  `case 'new'`.
- `let` assignment narrowing: narrowings aren't invalidated by reassignment, so only `const` narrows by its initializer. Numbers have no
  freshness (a `0` from `n && x` widens to `number` in a `let`, so a later `if (v)` can't remove it; tsc keeps and drops it).
- **OPEN, the closure half of flow containers**: an arrow / function expression / object-literal method / class-expression member carries
  EVERY outer narrowing; tsc 6 carries only a const's, or a param's/function-local `let`'s when the closure is past its last assignment
  (none in a nested function), never a `var`, a module-level `let`, or a property path.
- **OPEN, blocked (lib `flatMap`)**: towasm's lib declares `callback: (...) => U[]` where TS declares `U | readonly U[]`, so `xs.flatMap(x
  => f(x) ?? [])` is rejected and U infers `any`. Needs union-target inference first (`U | readonly U[]` against `string[]` must give `U =
  string`, TS's `inferToMultipleTypes`); a first attempt cost +8 errors because concrete alternatives must still be tried against the
  WHOLE argument and "an inference was made" is too coarse a signal. An empty `[]` contextually typed by `U | readonly U[]` also leaks
  the callee's unbound parameter.

## C. Accepting incorrect code (lower priority; each removal exposes false positives -- fix those)

1. **Widened source into a literal target** (`const x: "a" = str`, `` `a${number}` = str `` accepted). ROOT CAUSE: the var_decl check
   types its initializer WIDENED, so even a variable declared `{ kind: "b" }` reads `{ kind: string }` and the leniency keeps that passing.
   Fix both together: checks use the precise init type, then return false. (Literal freshness is now in; inference's supertype choice
   uses `precise` mode.)
2. DONE (plain call on a construct-only value = TS2348; fixed the lib gap `Array(n)`/`RegExp(src, flags)` with `ArrayConstructor`/
   `RegExpConstructor`). STILL OPEN: the `new`-on-a-call-signature direction (TS7009, gated on `noImplicitAny`, untracked here; enforcing
   it unconditionally cost 56 false positives) -- needs `noImplicitAny` tracking first. Found: towasm `Array<number>(3)` doesn't compile
   while `new Array<number>(3)` does (the CALL path doesn't specialise a generic class constructor); JS says they're identical, so route a
   plain call on a constructor-backed lib value through the construct path.
3. Overload no-fit -> WARNING with args unchecked (TS 2769); needs exact overload resolution.
4. Methods compared as their function type per overload: DONE. STILL OPEN: call/index members, function params, missing returns --
   `(x: number) => x` into `(x: string) => number` is accepted. Fix: function-typed props contravariant.
5. Class refs compared by members: MOSTLY DONE (a type-parameter DESTINATION is still checked through its constraint; TS keeps T opaque;
   truly unresolved names still pass -- an unresolvable name should be a TS 2304 at its reference). **DO NOT TIGHTEN `isAssignable`
   further until type-argument precision is fixed** (constraint-instead-of-argument substitution is the recurring culprit; tightening
   first measured ~1:1 true to false positives).
6. `narrowByDiscriminant` keeps a member on an unresolvable discriminant (falls out of B's member-absence work).

## D. towasm-specific

- The checker should stamp its chosen overload signature on the call node (like `contextualType`) and towasm read it, instead of
  `resolveOverload` re-resolving with its own tie-break (one source of truth). Multi-body overloads exist only in towasm's bundled lib,
  where the checker picks AMBIENT signatures with no body.
- `as unknown as` casts and `new TSWError(e as any, ...)`: widen the helper/`TSWError` parameter types instead ([[feedback_avoid_unsafe_casts]]).
- Gaps found: a struct of one interface can't be passed where an object type with optional fields is expected (`path.format(path.parse(x))`);
  an anonymous object type with overloaded methods can't be a method receiver ("field 'X' redeclares an inherited field"); `Object`
  intrinsics are recognised by name (`objectIntrinsic`), not resolution; towasm's lib has no `Iterable` (so TS's `Object.fromEntries`
  can't be declared), `Object.assign`, `String.fromCodePoint`; its `Promise.then` returns `void` and doesn't chain; a missing lib GLOBAL
  fails at codegen ("'new' is only supported for a known class") and, in a module-level const, blocks EVERY declaration in the file --
  `grep -E "^(const|let) .*new [A-Z]"` finds it in seconds (it was `WeakSet`/`SyntaxError`, 56 declarations). An ambient `declare var Map`
  would merge as an intersection whose class `constructor` part picks first -- needs an ambient-first rule for class+var merges.
- **SOURCE CHANGED, gap left open (user's call, 2026-10-05, binary `HEAD` "merge(): copy fields only")**: binary's `merge(obj, value)`
  (common.ts) did `Object.setPrototypeOf(obj, value.constructor.prototype)`, re-classing a plain object as `value`'s class. towasm cannot:
  a struct's class is fixed. The line was REMOVED from binary for expedience, so binary no longer behaves as it did under node. Proper fix:
  a mutable prototype link on `DynamicObject` (plain `{}`s), with prototype-chain dispatch for methods, `instanceof` and `.constructor`,
  which needs class methods compiled for a dynamic `this`. Restore the line in binary once that exists. The user says the result
  MUST inherit the class's methods; no case is known yet (binary-libs has none; maybe fonts/bitmaps/archives). A/B 2026-10-05: their tests
  give byte-identical output with and without the line, but only testfont, test_dds and test_7z actually run (quadratic: missing export;
  test_psd: unhandled rejection; tar/zip: missing fixtures, Windows paths). Without identity it is feasible: `merge` returns `value`
  augmented with `obj`'s other fields, readers use `s.obj = merge(...)`, and class instances get an `#ext` map (as closures have) for
  the undeclared fields, `C & {fields}` held as `C`. Deferred until a real case is found (user, 2026-10-05). Related, also open: a generic
  instantiation is its own class (statics per `ClassInfo`), so a user generic's instances have different `.constructor`s; method values
  (`obj.m`) have no identity; a dynamic `A.prototype` read builds a fresh object each time.

## Checker rules learnt (keep; they are TS facts and traps)

- **Generic call inference is ONE shared implementation** (`T.Inference`, with polarity): covariant candidates -> common supertype
  (same-base literals UNION); contravariant only when no covariant; type params FIXED as each context-sensitive callback is typed, left
  to right. Return-type inference has the lowest priority for a callback's return. Overload resolution is TS's two passes (callbacks
  untyped, then fixed by the first fitting candidate); the overload trial types each argument against the candidate's own parameter.
- Type walks must be DAG-aware (`searchOnce`/`rewriteOnce`): a new recursive type walk that isn't goes exponential on nested generics
  (7z.ts hit 4 GB). Diagnostics print types within a budget.
- **Declaration merging must not WALK the merged types**: `intersectTypes`' `typeKey` dedupe printed each part, forcing a class's lazy
  field-initializer getters mid-`hoist` (lib `String.charCodeAt = __asm<...>` inferred before `__asm` was bound, memoized `any`). Use
  `joinTypes` (flatten + identity dedupe). Any new eager walk of a class shape during hoisting reintroduces this class of bug.
- **Intersection normalization** (TS getIntersectionType) is IN (`domainOf`/`unitOf`/`reduceIntersection`, `resolve`'s `case 'intersection'`).
  tsc 6.0.3 rules: `X & any` is `any`; `T & unknown` and `{}` beside an object drop out; `never` from disjoint domains (`string & number`,
  `object & string`), a nullish beside an object, distinct units, conflicting literal discriminants; `'a' & string` is `'a'`; `{a:string} &
  {a:number}` is NOT never. TS distributes over a union member but DISPLAYS the undistributed origin. An intersection of type parameters
  relates by its own constraint (`intersectionConstraint`); a function's apparent type is the global `Function` interface; an
  intersection holding `never` IS `never` at instantiation (`reduceInstantiated`, which makes a phantom parameter infer nothing).
- **Reductions that DISCARD a part must read the part AS WRITTEN, never as resolved**: `resolve` answers `any`/`unknown` when it gives up
  (a deferred conditional, a depth bail), so dropping such a part turns "couldn't evaluate" into a reduction.
- `isAssignable` must defer expanding a non-primitive ref source to its members while `dst` is still a union/intersection, or an
  `Array<X>` source never reaches an `Array<Y>` destination through an extra union level (only the TOWASM lib scope reproduces it, where
  `Array` is a real class; test-towasm's `arrayThroughUnion` guards it and test-checker CANNOT).
- Flow containers (`Scope.flowBoundary`): a function declaration and a class declaration's members (property initializers too) see outer
  declared types, never narrowings. Const contexts are `const<inner>` (`inner` = the contextual type it replaces, deciding whether an array
  is readonly); `as const` object properties are not yet marked readonly. Destructuring a union binds each member's own position; an
  equality with a literal drops non-comparable members (but the literal isn't boxed, so `'a'` vs `{ length: number }` is dropped where TS
  keeps it); an inferred return adds `undefined` only when the end is reachable (`endsFunction`).
- Member-absence sealing for class instances was one line (`resolveMembers` in `sealed`) but cost 44 corpus errors until EIGHT modelling
  gaps landed first: computed `[Symbol.iterator]` members, mixin members, `this` in a static member, construct signatures on a
  constructor-typed `T`, polymorphic `this` returns, a guard narrowing to a supertype keeping the subtype, `this` in a nested `function`,
  `partiallyAnnotatedFunctionInferenceWithTypeParameter` (undiagnosed). `super` in a class is bound (see [[tison_towasm_self_hosting_plan]]).
- A **struct-identity rule** closed ~77+20 survey declarations (details in [[tison_towasm_self_hosting_plan]]): identity is physical
  layout, not `T.typeKey`; `layoutTwin` (key = fields SORTED, each by stored wasm type, refs canonicalized; only FINAL supertype-free
  shapes; refused if a later type already names the index) is used by both shape builders. A merged struct's `thisTsType` is the
  FIELD-WISE UNION of the merged shapes -- not a widening (widening broke `matchObjectShape`'s discriminant tiebreak, since every
  single-field `{type: <tag>}` shape shares one layout); no representable union -> refuse the merge. The `ensureClass` merge is
  restricted to METHOD-FREE classes by measurement (a method body is compiled against the instantiation it was reached through, so
  merging methodful instantiations runs code built for one layout against the other); `name === 'Array'` is the one method-bearing
  collapse known sound. `matchObjectShape` already matches by field-name SET, so field order was never a problem.

## Instrument and leak lessons

- **A memory leak, ~140MB per compile, was found and fixed**: transform.ts's process-wide module-scope caches (`importScopeCache`,
  `waitingFor`, `ownScopeSettled`) were strong `Map`s keyed by `LoadedModule`; every compile builds a fresh `ModuleLoader`, so every
  module `Scope` and its whole type/AST graph stayed live. Final shape: one `ModuleMemo` (`shape`/`own`/`waiting`) STAMPED on the module
  record via a single `memoOf` accessor (the convention `src.program.scope ??= inner` already uses), so a memo lives exactly as long as its
  module. REJECTED: `ModuleLoader` instance fields (package modules are shared across loaders -- `NodeModules.found` is static -- relative
  ones are per-loader). Reuse is preserved because the caches are keyed by OBJECT IDENTITY. **How to find the next leak**: bisect with env
  flags in the survey (`DBG_MEM` per-probe heap, `DBG_NOCODEGEN`, `DBG_NOCHECK`, `DBG_FRESHLIB`, `DBG_REUSE`, `DBG_GC`); parse alone flat,
  parse+check growing, re-checking one cached AST flat said "checking pins each parsed AST".
- **The survey CAN lie**: a crashed worker used to leave that file's PREVIOUS JSON on disk and the tables render from disk, so crashed
  rows read as "nothing changed". A failed worker now overwrites its report with `parseError: 'WORKER CRASHED (not measured)'`, a `## NOT
  MEASURED` section prints and it exits non-zero -- always look for `worker for ... exited`. `--aggregate` (and every run) re-renders
  from whatever is on disk, blending vintages: `stat -f '%Sm %N' assistant/selfhost-survey/*.json` before quoting a number; only a full
  clean run licenses a headline figure.
- `--slice start:count` bounds a worker to that many declarations and writes `.partN.json`; the parent retries a crashed file in slices
  of 24 and merges (type-utils' 113 probes in one process exhaust the 8 GB heap).
- `probe-one-decl.ts <file> <declName>` compiles ONE declaration the way the survey does and prints the error WITH its position (the
  survey strips positions deliberately, to cluster causes) -- how to turn a cluster back into a source line.
- The local TypeScript checkout lacks ~1339 `.errors.txt` that git tracks, so ~1300 tsc-rejected corpus tests count as "clean";
  difftest's TS side is transpile-only, so invalid-TS cases can slip in.
- Pre-existing: `tison/test/test-tison.ts:96` fails to parse (`(_, ctx) => ({...ctx})` in `Rule(...)`).
