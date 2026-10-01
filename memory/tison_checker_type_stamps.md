---
name: tison-checker-type-stamps
description: "PLAN (2026-09-22): the checker stamps each expression's final type; the backend READS stamps and only maps them to wasm -- plus the two constraints the user set: codegen keeps its freedom to pick simpler representations, and the backend compiles whatever AST it is given literally (VSDG output included)"
metadata:
  type: project
---

**Why:** the checker computes every expression's type (narrowing included) but records none -- its exported
`typeOf(e, scope)` recomputes from scratch, and only STATEMENTS carry a stamped scope. So wasm-backend.ts re-runs the
checker (53 `checkerTypeOf`, 61 `narrowedTypeOf` calls) and must guess which scope to ask in (`ctx.scope` = the
slot's declared type, `stmtScope` = narrowed, `physicalScope`), and re-applies `narrow()` itself inside
ternaries/`&&` (`withNarrowed`). Each wrong guess became a local patch: the "every failing case got its own path"
sprawl the user objected to (wasm-backend.ts ~11k lines, 2026-09-21).

**Plan:** the check pass stamps its FINAL answer on every expression (narrowed type) and every binding (declared
type) -- untyped AST-node stamping, per [[feedback-no-checker-state]]. The backend reads stamps; no scope choice,
no re-check, no re-narrowing. Order: stamp, measure where stamps disagree with what the backend computes now
(each disagreement is a deletable backend patch or a real checker bug), then switch the backend over area by area.

**Constraint 1 -- representation freedom (the user's, 2026-09-22):** a stamp is the TS TYPE; the wasm
REPRESENTATION stays the backend's choice, and may be simpler than the type calls for (`i32` for an
integer-range `number` via `collectRangeWidenings`, a raw array rather than `Array<T>`), with conversions only
where really needed. Stamping must not collapse representation into type -- see [[tison-type-vs-representation]].

**Constraint 2 -- the backend compiles its input literally (the user's, 2026-09-22):** the VSDG is an OPTIONAL
optimisation pass that outputs a NEW AST; the backend compiles whatever AST it gets very literally, in the
evaluation order the trees define -- no reordering of its own. VSDG output is fresh nodes, so they carry no
stamps -- so the pipeline is parse -> (optional VSDG, which needs no checker information) -> check+stamp -> backend
(the user, 2026-09-22). The VSDG is not wired into tsw/transform/backend yet; this is the rule for when it is.

**Known wrinkles:** a generic body is checked once but compiled per instantiation (stamps hold type params, to be
substituted as declared types already are); the checker evaluates some expressions speculatively (overload
resolution, contextual typing trials with different `expected`), so a stamp must be the check pass's final
answer, not the last trial's; synthesized nodes the backend builds (`Identifier('$key')` in runtime helpers)
never met the checker and need their type supplied at construction.

## Step 1 done: the checker stamps (2026-09-22)

`checkedTypeOf(e)` (checker.ts) is the type the CHECK PASS gave `e`: precise (unwidened), narrowed where it stands,
first real check wins. `stamp` is threaded, not global: `typeOf1` (the check pass's typeOf) passes it, and so do
`checkFunctionBody`/`checkClass`/`hoistVar` when their caller stamps -- so a closure body walked by an overload TRIAL
(`candidateFits`, the arg trial) never stamps, and neither do `narrow`'s re-walks, hoist-time typing, return-type
inference or generic templates. No mutation: `T.stampScope` on every result was tried and removed (it tags shared
type objects). Corpus A/B identical on every count; difftest unchanged.

**Measured** (`assistant/stamp-agreement.js`, a `-r` preload over difftest's 2213 programs; `stamp-coverage.ts` lists a
program's unstamped nodes): the backend makes **504,664** typeOf queries (~228 per program). 266k agree with the
stamp, 49k disagree, 190k hit unstamped nodes. Disagreements: `this` stamp vs the concrete class (37k -- substitute
`this`); a narrowed stamp vs a query that lost the narrowing (`Tok` vs `Tok | undefined`, `number` vs `any`: the stamp
is BETTER, ~10k); a type param stamp in a generic body vs the instantiation's type (substitute); `number` vs the
backend's range-widened `i32` (representation, constraint 1). Unstamped: 125k are lib class bodies reached via
`ensureClass` (generic templates, or bodies the backend clones per instantiation) -- the next thing to explain.

## Coverage to 94% (2026-09-22)

- `ensureClass` reprocessed every scalar-backed class (`Number` 1524x over 52 programs) because `typeIndex === -1`
  meant both "unprocessed" and "no struct"; `thisWtype` is now the processed test (`99325ea`). Queries 505k -> 382k.
- Generic INSTANCES are substituted copies re-checked by `checkHoisted` (`instantiateDecl`, `ensureClass`); the copy
  drops `checkedType` as it drops `scope` (`unstamped`). Type stamps are taken in generic templates too (a template
  node carries `T`; the backend compiles the copies). Scope stamps keep their template rule.
- **Tried and reverted:** clearing a class instance's `typeParams` (as a function instance's are) so its re-check is not
  template-flagged. It gives lib instance bodies statement scopes they never had, and the backend's scope-guessing then
  emitted INVALID wasm (`i32.trunc_sat_f64_s` on an `i32`; 7 -> 97 difftest unsupported). The cure is the backend
  reading stamps, not keeping scopes imprecise -- revisit once it does.
- Now 295k agree / 63k disagree / 24k unstamped. Checker precision gap: a class body's `this` is the bare class ref, no
  type args, so in an instance copy `this.data` stamps `RawArray<any>` where the instance has `RawArray<i32>`.
  Remaining unstamped: synthesized nodes (`this` with no pos, `$spread$from$`, `#for0$arr`), and lib `ArrayBase` /
  `x instanceof ArrayBase` reads.

## What type stamps replace (the user asked, 2026-09-22)

The backend reads scope stamps in ~19 places. The NARROWING ones -- a statement's `.scope` feeding `ctx.stmtScope`, a
branch's `.scope` (`stampBranch`, ternary/`&&`), the analysis passes that walk statements to re-query types -- exist
only so the backend can re-ask for a type in the right place, and go once it reads type stamps. A declaration's own
type (`fd.scope.value(name)`) becomes a stamp on the declaration. STAYING: module scopes (`m.scope`, `ast.scope`:
names -> declarations, type aliases across modules) and the `declScope` tags on type refs. Caveat: the checker itself
uses `fn.scope` / `body[0].scope` as an "already walked" marker to skip muted re-walks -- that job needs another marker
(the type stamp can serve) before statement scope stamps can be dropped.

## First backend read of stamps (2026-09-22, `3dd6cd8`, `3e4596c`)

`ctx.stampedTypeOf(e)` = `checkedTypeOf(e)` with a method's polymorphic `this` substituted by `ctx.owner.thisTsType`.
`narrowedValueTypeOf` now takes a union/`any` receiver's NARROWING from it (no `stmtScope` re-check); the declared type
stays the representation (`backToDeclaredMembers`). Each gap a stamp read exposed was a real bug, fixed at its source:
- instance copies SHARED untouched nodes, so instantiations read each other's stamps (`Set<string>` saw `Set<number>`):
  `unstamped` now always copies;
- a narrowed PATH (`e.value`) was answered from the narrowing table without typing its receiver `e`;
- `x as T` never typed `x` at all (survey: printer.ts `printer`, `(m as any).kind` after an exhausted switch);
- `ensureUnionFieldDispatch` was cached without its result type, which is the CALL SITE's: a non-null site's
  dispatcher served a nullable one and trapped.
Lesson: a stamp read that falls back to the declared type hides a missing stamp. The survey caught the one the suites
didn't -- so run it after a change to how the backend READS types. Occasionally, never as a per-commit gate: the user's
call (it is slow and causes friction), see [[tison-session-handoff]].

**Next:** delete `stmtScope`/`inNarrowed`/`typeScope` (5 `inNarrowed`, 7 narrowing-scope `checkerTypeOf`s, 77 `typeScope`
uses that only resolve type names) and the per-statement `stmtScope` update in `emitStmt`.

## The narrowing machinery is deleted (2026-09-22, `36a419c`)

Gone from wasm-backend.ts: `ctx.stmtScope` (per-statement, from the checker's scope stamp), `inNarrowed` (re-running
`narrow()` for a ternary/`&&` branch), `typeScope`. Replacements: `ctx.typeAt(e)` (the stamp, widened as
`checkerTypeOf` widens, falling back to `ctx.scope` for nodes synthesized after the check pass) and
`physicalTypeOf` (a call/`new`/array literal has no slot, so its representation is its own checked type -- what
`inNarrowed` was really feeding: `p.t ? [p.t] : []` is a `number[]`). `typeScope` was only ever a scope to resolve
type NAMES in.

**Measured boundary (do not cross without the representation layer):** `case 'var_decl'`'s three statement-scope
queries (`d.init.object` for a typed array's element type, the generic-method-return check, `tsType ??=`) decide a
LOCAL'S REPRESENTATION, not its type -- switching them to stamps took difftest 7 -> 15 unsupported
(`cannot convert ref:Array<any> to ref:Array<number>`, `arr:f64` vs `arr:ref`). They keep reading the statement
stamp until representation is explicit. Same tension: `ctx.scope` holds the backend's own range-widened `i32`
bindings, which is why a stamp (`number`) and a query (`i32`) legitimately differ.
