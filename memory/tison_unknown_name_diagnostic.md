---
name: tison-unknown-name-diagnostic
description: TS2304 "Cannot find name" is reported for types AND values behind `Scope.unknownNames` (on in tsw and test-towasm, off in the corpus harness); what forcing it on for the corpus still exposes, by cause
metadata:
  type: project
  modified: 2026-09-27
---

## Optional, landed 2026-09-27 (types `51684da`, values after)

`Scope.unknownNames = true` (inherited, like `nullChecks`; root default off) reports a type ref naming nothing where it
was written. `unknownTypeNames` (checker.ts) COLLECTS the entry program's refs before checking -- checking writes
contextual param types and inferred returns onto the AST, whose refs (a lib signature's `U`) are not source -- and
judges them after, against each ref's `declScope`. Names a type binds itself (type params, mapped key, `infer`) are
tracked during the walk. Only the ENTRY program is judged, not imported modules. On in `tsw.ts` and test-towasm's
`programScope()`; off for the corpus harness, which checks each `@filename` part in isolation.
Forced on for the corpus it adds +693 on tsc-clean files: multi-file/import isolation (`JSX.*`, `React.*`,
`im_private_*`, `create<T>()` over an import), mislabelled tests (errorsInGenericTypeReference.ts), and
**`unique symbol` (26): the checker has no model of it** -- the parser emits a ref named `unique symbol` that nothing
resolves; the fix is a real type node, not skipping the name. Probe: `assistant/unknown-names-probe.ts '<src>'`.
VALUES: `case 'identifier'` reports when `scope.value` misses and the flag is on. A named function expression's own
name is now bound (lazily) in its body. Forced on for the corpus (REBUILD `dist/` on both sides of the toggle -- the
harness runs `dist/`), types+values are +1246 on tsc-clean files; `import` (219) and `globalThis` (13) led the value side.
BOTH FIXED 2026-09-28: `import(...)` is an `import_call` node (`arguments` as written; TS1325/TS1450 for spread/arity), typed
`Promise<namespace>` from a module the async check resolves onto it (`resolveDynamicImports`, literal specifiers only;
otherwise `Promise<any>`, as TS); `import.meta` is `import_meta`, typed `ImportMeta` (lib.d.ts: Node's url/dirname/filename).
`globalThis` is bound lazily in each global space (`globalObject`: `var`s, functions, namespaces as `typeof` members, plus
an `any` index -- TS7017 needs noImplicitAny, which this checker does not track). A sync-checked script is now a global space
too (`checkEntry` sets `globalSpace`). The 2026-09-26 cause list below is otherwise still the map.

## Value names: the 2026-09-26 analysis (flag did not exist yet)

The checker's `case 'identifier'` returns `scope.value(name) ?? T.ANY` and reports nothing, so every unbound name is a
silent `any`. That hid the `var` block-scoping bug (`c7f9f2e`). Reporting it is a few lines in that case:

    if (src) return recurse(src);
    const t = scope.value(e.name);
    if (!t && err) err(SEVERITY.ERROR, pos)`Cannot find name '${e.name}'`;   // then `any`: tsc's error type
    return t ?? T.ANY;

**Not landed**: at `ae33c59` it adds +574 tsc-clean false positives (corpus A/B), and a false positive outranks a
missed error ([[feedback-fix-prerequisites-not-workarounds]]). Land it only when that delta is ~0.

Already fixed on the way: `arguments` bound in every non-arrow body (`ae33c59`); nested parser-built identifiers
had no `pos` and crashed the reporter -- 76 files threw (`33d38c1`).

Remaining causes, 2026-09-26 (574 reports):
- **`import`** (219): `import(...)`/`import.meta` parse as a call/member on an Identifier named `import` (a reserved
  word). Needs real dynamic-import typing (`Promise<typeof module>`, `ImportMeta`); `Promise<any>` would be an any-fallback. **User to decide.**
- **Multi-file tests** (114 in 70 files): a name declared in a LATER `@filename` of a script test -- tsc has one
  global program scope across script files; the harness checks files one at a time.
- **`globalThis`** (13): tsc types it as a LIVE view of all globals (script `var`s included); a snapshot after the lib
  would still reject `globalThis.myVar`. **User to decide.**
- **Single-file gaps** (~230 in 110 files), sampled: a named function expression's own name inside its body
  (`function somefn() { return somefn; }`, recursive named lambdas); a class expression's name in its body/statics;
  ambient-module and dotted-namespace names (`Foo.Bar.foo`, `A.B.C`); a later parameter in an earlier default;
  `for (var of of of)`; a class used before its declaration statement.
- **Mislabelled tests**: some tests exist to produce TS2304 but the local corpus has no `.errors.txt` for them
  (`maximum10SpellingSuggestions.ts`), so they count as tsc-clean. Check a file's baseline before "fixing" it.

Instrument: `assistant/corpus-ab.sh`; `diff corpus-ab/{base,head}-false-positives.txt | grep "Cannot find name"`.
