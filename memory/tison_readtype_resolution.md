---
name: tison-readtype-resolution
description: "TStoDecl's resolveTypes (structural type resolution + class-heritage hoisting for binary-libs' pe.ts .d.ts output) -- what it does, the checker bugs it flushed out (as rules), the two known-unfixed issues (`_` discriminant key bloat; TStoDecl's own checkBlock pass is load-bearing), and the tracing methodology. Distilled 2026-09-30 from rounds written 2026-07; the checker has changed a lot since (opaque type params, deferred conditionals) -- re-verify before leaning on a specific claim."
metadata:
  type: project
---

## What `TStoDecl` (ts/transform.ts) does beyond declScope qualification

`resolveTypes(entryScope, importScope)` is the `onType` callback driving `TStoDecl`'s final print walk:
1. **Structural resolution of nameless constructs** (`mapped`/`conditional`/`indexed_access`/`keyof`/`typeof`) via `T.resolve(scope, type, undefined,
   stopAtRef=true)` -- `stopAtRef` (default false, zero effect on other callers) makes the `ref` case stop at the first named type instead of drilling to
   full structure; only this printing pass passes `true`.
2. **Un-inlines refs whose own declared body is resolvable** (e.g. `bin.ReadType<T>`, a conditional: TS doesn't give conditional results a stable alias
   identity either). Plain named refs (interfaces/classes/ordinary aliases) stay names.
3. **`findDeclaredName`**: after a resolve yields a structural result, reference-identity-check it (`Scope.findDeclaredName`, walking `.parent`, each scope's
   OWN type map) against every declared type in scope; if the shape literally IS a class/interface's registered type, print that name.
4. **`bin.Class(spec)`-as-heritage hoisting**: an `extends` clause that is a call can't survive into ambient `.d.ts`; `stripClassDecl` (single strip pass, once
   per class) synthesizes `declare const Foo_base: <computed type>` ahead of the class and rewrites `extends` to it (as tsc's declaration emitter does); the
   bases are prepended before the single print walk so the same `onType` pass resolves them.
5. **Constrained-generic overload expansion** (`expandConstrainedGeneric`): `f<T extends "A"|"B">(x: T): R<T>` -> one non-generic overload per literal member
   (`ReadDirectory(name: "IAT"): MappedMemory` instead of one generic signature dragging in the whole lookup table).

## Checker/printer rules the work flushed out (each was a real bug)

- **`mapArray` collapses an empty array to `undefined`; `mapArrayA` doesn't.** A mandatory-but-possibly-empty array field (tuple `elements`) must use
  `mapArrayA` or the printer crashes on a legitimately empty `[]`. Check this first when such a field crashes the printer.
- `matchInfer`'s object-pattern case must handle `call`/`construct` members (a `{new(s:any): infer R}` pattern was silently skipped, so the match vacuously
  succeeded with `R` unbound, leaking a bare `R`), including when `a` is a bare `constructor`/`function` type; an `a` that is an INTERSECTION must try each
  member (`get<T> = ((s:sync)=>T) & ((s:async)=>Promise<T>)`); a ref pattern against a resolved PRIMITIVE is `false` (a primitive can never satisfy
  `PromiseLike<infer R>`), but an object stays `undefined` (it could be a thenable).
- Cycle guards must key on `(alias, argument)`, not the alias alone: `ReadType<T>` legitimately re-enters itself per nested field with a different `T`. With
  no false cycle to bound it, resolution then needs a real depth cap. A catch for a cycle bail must wrap EVERY branch that can throw it (foreign/unreachable-ref
  inline branches too), keyed off one `topLevel` flag.
- Object-literal SPREAD types (`{...X, k: y}`) merge the spread operand's members (later overrides earlier); bail to `any` only when the operand has no
  determinable object shape.
- `isAssignable` must not treat `Array`/`ReadonlyArray` refs as "unresolved named type: be lenient" -- a plain object wrongly "extended `readonly unknown[]`"
  and misrouted `ReadType<T>` into `TupleReadType` (129/129 checks wrongly true).
- **`resolve()`'s `mapped` case with an `as` clause** (key remapping) used to be left opaque verbatim (K unsubstituted -- the source of leaked bare infer names).
  Now: for each candidate key resolve `nameType` with it substituted; skip on `never`, use a string/number literal as the output key, and bail the WHOLE mapped
  type to opaque if any candidate's key can't be determined ("never guess"). A mapped type's CONSTRAINT may be an INTERSECTION (`keyof T & (string | number)`):
  split into members, resolve each, use the member that reduces to literals; detect homomorphic `keyof` from any member.
- Making opaque types evaluate exposes previously-masked bugs (the intersection-of-overloads one regressed corpus ERROR 18 -> 38 until fixed). "Opaque is checked
  leniently elsewhere" is how such bugs hide.

Outcome (as of 2026-07): `Section_base`, `COFF_base`, `COFFSymbol_base`, `RESOURCE_DATA_ENTRY_base`, `PE_base`, `DOS_HEADER`/`EXE_HEADER` in `pe.debug.d.ts` fully
resolved (no bailing `bin.ReadType<{...}>` left except the legitimate top-level `Directory` alias). Cosmetic residue, deliberately left: object-typed fields keep a
redundant `X extends PromiseLike<infer R> ? R : X` wrapper (correct, verbose).

## Known-unfixed (do not re-attempt without budgeting a full investigation)

**A. `PE`'s spurious `_` key / output bloat** (tison's `pe.d.ts` 4736 lines vs tsc's 629). `PE`'s spec has `_: bin.Switch('Magic', {...})`; `NonMerged<T>` should DROP it
(letting `AllCorrelated<T>` splice its members in) but tison keeps `_: bin.CorrelatedMerge<{...}>`, roughly doubling output. Root cause (traced): `isAssignable`'s
`dst.type==='object'` check has `if (m.type !== 'property' ...) return true` -- a blanket lenient pass for `call`/`construct` dst members, so `T["_"] extends {new(...args:any):any}`
vacuously holds for EVERY field and takes the keep-`K` branch. Making those members real checks is necessary but NOT sufficient: it unmasks a second, load-bearing
leniency -- the absent-property fallback `hasMod(m,'optional') || !sealed(src,scope) || recurse(UNDEFINED, m.typeAnnotation, depth-1)` lets a required property typed `any`
pass when genuinely absent (e.g. `NoPromise(R) extends MergeBase<any>` is true for any `R`). Removing it is real-TS semantics but lost real fields (`Name`,
`PointerToRawData`, `Characteristics`, `Machine`, the whole `opt`) in `Section_base`/`COFF_base`/`DOS_HEADER` -- some other consumer relies on it. A third gap in
`binary-archives/src/zip.ts`: `ZIPheader = Pick<bin.ReadType<typeof file_header>, ...> & {...}` -- `atime`/`ctime`/`uid`/`gid` (present only in some branches of a nested
`extra` merge, hence optional via `MergeResult`'s `as undefined extends B[K] ? K : never` clause) came out non-optional (2 corpus ERRs). Both `isAssignable` changes were
REVERTED; current state is an understood, accepted trade-off. Don't re-apply the two changes without first finding what relies on any-absorbs-absent (field by field).

**B. `TStoDecl`'s own `checkBlock` pass is load-bearing, not redundant.** `TStypeCheck`/`TStypeCheckAsync` already stamp the checked top-level `Scope` onto `ast.scope`, and
`TStoDecl` builds ANOTHER scope and re-runs `checker.checkBlock(ast.body, global)` -- it looks like duplicate work, and the same dedup was verified safe for `TStoWasm` (its
subset has no classes/overloads). For `TStoDecl` it regressed `PE.ReadDirectory`'s overloaded returns (`[string, any][]` / `{[key: string]: any}` collapsed to `any`); preserving
the parent/child Scope shape without the `checkBlock` call did the same, so it is `checkBlock`'s own walk over `ast.body` (probably overload-group matching in
`inferReturn`/`checkClassMembers` for un-annotated overload members) that is needed. Not root-caused; reverted.

## Methodology (worth repeating)

Every one of these bugs was found by INSTRUMENTING and TRACING actual runtime values (`new Error().stack`, targeted `console.error` dumps of `check`/`t.checkType`/`t.extendsType` at
each suspect layer, gated behind `env.DEBUG_*` and removed after) -- never by reasoning about what "should" happen. An earlier version concluded an "architectural dead end needing
structural equality or type interning"; that was wrong -- switching the cycle-guard key to `T.typeKey` changed NOTHING, which was the proof the problem was wrong-path resolution
caused by real fixable bugs, not undetectable cycles. Plausible hypotheses were falsified this way; don't skip to a fix from how the code "should" behave. To type-check these files use
the compiler package's tsconfig (the old root tsconfig didn't cover them).
