---
name: tison-checker-inference
description: "tison checker inference/conditional mechanisms added 2026-09-08 — distributive conditionals, contextual callback returns, provisional bindings, tuple inference, and the `undefined` binding the wasm path was missing."
metadata:
  type: project
---

Five connected checker mechanisms, all landed 2026-09-08 while clearing wasm-backend.ts:193's
`new Map(LIB_AST.filter(...).map(n => [n.name, n]))`. Read together: they are how a type argument
gets inferred through a nested generic call.

**Tuple inference (`9603085`).** `inferTypeArgs` had cases for array/ref/intersection/conditional/
function but NONE for a tuple, so `constructor(entries: [K, V][])` inferred nothing and every
entries-style construction was `<any, any>` — which towasm rejects outright.

**Contextual array literals (`9603085`).** A generic parameter's declared type is deliberately NOT
passed as an argument's expected type. An array literal is the exception: `case 'array'`'s `wantTuple`
needs only the tuple SHAPE, and the type params inside `[K, V][]` land solely as per-position expected
types where an unresolved ref is inert. **The shape is the information, the leaves are inert** — that
principle recurs in all of this.

**Contextual callback RETURN + provisional bindings (`af8175a`).** Reverse matching (`expected` vs
`sig.returnType`) already existed and already fired, binding `.map`'s `U = [K, V]`. Two things were
missing: `applyContextualParams` typed a callback's PARAMETERS but nothing typed its RETURN (so the
literal never became a tuple), and the placeholder binding was taken as the ANSWER — `out`'s
first-wins guard then made the deferred body-derived inference a no-op and `K`/`V` leaked out as
`Map<K,V>`. A binding still mentioning an unsolved param now yields to the argument's own type.
**A hint must carry structure**: threading a bare unsolved `R` through cost 2 real diagnostics
(`after<V, R>` in binary/src/interop.ts), found by bisecting with env toggles, not by reasoning.

**Distributive conditionals (`ba8a867`, `e536ffd`).** `Extract<T,U> = T extends U ? T : never` only
works if the union distributes; tested whole it fails and the entire family (`Extract`/`Exclude`/
`Omit`) collapsed to `never` — assignable to everything, so it failed SILENTLY, surfacing only as a
member read coming back `any`. Distributed at the ALIAS-INSTANTIATION site, not the conditional node:
each arm must see the member substituted for `T` in its BRANCHES too, and by the time a conditional
node exists that has already happened. Only when every type argument is CONCRETE (real TS defers
otherwise). `e536ffd`: a DOTTED name is never a type parameter — `scope.type` doesn't split on '.', so
`TS.Stmt` looked unbound and blocked its own distribution.

**`undefined` had no binding on the wasm path (`f37c63c`).** `makeLibScope` starts from a bare
`new Scope` and builds globals from `lib.d.ts`, which CANNOT declare `undefined` — real tsc rejects it
as a built-in conflict. `T.makeGlobal` binds it for the checker-only path. So the identifier typed as
`any`, `cond ? x : undefined` came out `number | any`, and the `any` swallowed the union leaving
nothing nullable for a later `!== undefined`. One `addValue` in `makeLibScope`.

**Measuring these**: `corpus-ab.sh`'s total LIES here — the distributive fix read as +4 errors and all
four were TRUE POSITIVES that TypeScript's own `.errors.txt` baselines require (`omitTypeTestErrors01`,
`intersectionsAndOptionalProperties`, both built on `Omit`). Attribute with
`assistant/corpus-errdump.ts` and check the TS baseline before believing a regression. See
[[tison_corpus_errdump]].

**Const contexts and template literals (`87e2045`, 2026-09-10).** `as const` / a `const` type
param's argument make a READONLY TUPLE (`CONST_CONTEXT` travels as the expected type, so the
`recurseCache` stays sound). Making `E4 = [...] as const` a real tuple exposed two older gaps:
`inferTypeArgs` fixed `T` from a tuple's FIRST element against `readonly T[]` (now pools and unions
every element), and template literal types were NEVER evaluated -- a `Literal` whose value is a
parts array, which `isLiteral(t, 'string')` also accepts. `resolve` now expands finite ones to their
cross product (`expandTemplate`); unexpandable ones match as a regex (`templatePattern`).

**Probe traps found doing it**: (1) `isAssignable(string, 'x')` is TRUE by design (widened-source
leniency) and declarations widen their init first, so `const f: 'x' = 'q'` is SILENT -- a probe on a
literal mismatch needs `as const` or a non-literal source. (2) A read of a missing member on an
OPAQUE type is silently `any`, so a "does this key exist" probe proves nothing; assert the member's
TYPE (`const bad: string = s.yx` must error). (3) test-ts-parser prints its errors to STDERR.

Related: [[tison_nominal_class_refs]], [[tison_towasm_self_hosting_plan]].

## TS-faithful fallbacks and what they exposed (2026-10-04: cd5f1e5, b2f7375, follow-up df5652a)

An uninferred type parameter is `unknown` (was `any`), and `unknown` as a source fits only a top type (it fitted every class).
**Measure with `corpus-ab.sh <rev>`** -- `npm run gate` is parser-only; three commits that session cited it as checker
evidence and were wrong. The corpus showed ERROR +16 / GAP +11, all inference gaps the `any` had hidden; the follow-up
(see its commit message) fixed them TS's way: async return/`await` contexts `T | PromiseLike<T>`, `yield*` context,
`T & C` narrowing of a type-parameter value, `NoInfer<T>` = `T`, `ReadonlyArray<A>` and namespace-spelled refs in return
inference, object types inferring index signatures from properties, result context heard FIRST (reaching only a nested
generic call's context, unsolved params as `unknown`), `void`-accepting trailing params optional, no GAP for a param fixed
to type a callback. Net vs the session's base: GAP -65, ERROR +2.

**Open:** genericContextualTypes1 `f13` -- `compose(unbox, unlist)` against `<T>(x: Box<T[]>) => T`. B infers `unknown[]`:
`unlist` is instantiated in context `(b: W) => C` (not lifted, since `B` already has the candidate `W`), `T[]` vs `W` infers
nothing. TS's higher-order inference (instantiateTypeWithSingleGenericCallSignature / unique type parameters) unifies the
lifted parameters. Also open: an error inside a callback two generic calls deep is not reported (`x.length` on `number`).
Instrument: `assistant/probe-ctx.ts file.ts` prints each call/arrow's expected and checked type.
