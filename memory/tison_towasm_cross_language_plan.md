---
name: tison-towasm-cross-language-plan
description: "Architecture rationale for separating the language-neutral wasm half from the TS-specific backend: what couples the backend to TS, the file-splitting rule and neutrality test, what is done (wasm/codegen.ts), what the user rejected (TSEmitter class split, relaxed VSDG), the unfinished generic-core extractions, and the shelved TypeOracle/IR seam. Distilled 2026-09-30 from a 48KB plan; step-by-step history is in git (pre-distillation: 1c439ff)."
metadata:
  type: project
  modified: 2026-09-30
---

Read [[tison_session_handoff]] first for live work; this plan must not silently displace the self-hosting row.
**The axis is TS-specificity. Navigation ease is a hoped-for by-product and must not choose the axis.** The near-term goal
is SEPARATING the TS-specific code from the language-neutral half, not building a second backend language.

## What couples `TStoWasm` to TypeScript (measured 2026-09-16, `ts/wasm-backend.ts` then 12.4k lines)

1. **AST vocabulary** -- ~515 literal `.type` comparisons, 62 distinct tags, 9 AST switches. The small, mechanical half
   (`common.ts`, now `@isopodlabs/tison/ast`, converged the leaf shapes; PY reuses them for expressions, CPP for control flow).
2. **Semantic type model** (`ts/type-utils` -- `T.` referenced ~400x): the REAL gate. Everything valuable the backend does
   (struct layout, monomorphization, closure signatures, `any`/union dispatch, vtables) is type-directed; a language with no
   semantic types has nothing to lower from. PY/CPP have no type model (CPP only a scalar fold model and declarators).
3. **Checker protocol** -- `checkerTypeOf` (~51 sites), `narrow`, `candidateFits`, `checkBlock`, `checkHoisted`, and UNWRITTEN
   stamp reads off AST nodes (`ast.scope` must be a checker `Scope`; `(stmt as any).scope`, `branch.scope`). This contract lived
   only in two files' heads; writing it down is the cheapest first deliverable.
4. `TStoWasm` is ONE closure (a ~10.6k-line function with ~207 nested functions sharing state by capture), so any partition is
   a real refactor. The neutral/TS dependency is one-way: TS -> neutral (`mod`/`funcs`/`globals`/`lazyGlobals` have 0 neutral
   references), and the shared state a split needs is small (16 data members + 6 injected callbacks).

**A rule-based "neutral" cut (a declaration is neutral iff it names no TS/JS/T/checker/AST tag) gives 94/6 and is NOT a cut
line**: it slices inseparable clusters (`toValType` neutral, its only data source `ensureClass` TS). The drag is the TYPE MODEL
carried in shared SHAPES (`FunctionContext`, `ClassInfo`, `FuncSig`/`ResolvedParam`), not the functions. Cut the types first.

## Seams considered

- A. Add PY/CPP case labels to the 9 switches -- **rejected** (tag special-casing; multiplies per language; the name lies).
- B. A `Language<E,S,T>` interface over the AST -- rejected as the primary seam (~300 members; forces every language to
  implement TypeScript's type system). A small tag-level version may stay.
- **C (recommended destination, SHELVED): two seams** like the VSDG's -- a `TypeOracle` (~15 facts: primitive kind, struct shape
  + fields, array element kind, class hierarchy + method table, call signature, union members, nullability, literal value, declared
  type of a node) and a target-shaped fully-lowered `Wasm IR` (locals, classified calls, resolved operators, control flow,
  constructions, coercions, tagged with ShapeIds into the oracle). Each language writes AST -> IR and answers the oracle; the
  language-free half writes IR -> wasm and never sees a source tag. Only if a second language is wanted: oracle, then IR, then one
  vertical slice plus a cross-language differential instrument modelled on `difftest.sh`.

## Decisions (all closed)

1. **The VSDG is an unrelated optimisation pass**, not a backend input (it is syntax-preserving by design -- `passthru`/
   `verbatim`/`suppressed` give up and pass through opaquely; types are one optional annotation; nothing consumes it, the backend
   imports it 0 times). If convergence happens later, take it then; do not design for it.
2. **`lib` is per language**: `ts/lib/**`, `LIB_DIR`/`LIB_FILES`/`LIB_AST`/`LIB_DECLS`/`LIB_DECL_MAP`/`LIB_AMBIENT_MODULES`/
   `hostImportsIn`/`makeLibScope` travel with the TS half; a new language brings its own stdlib over the same wasm runtime.
3. No second backend language now. Structural work lands before self-hosting rows (done in staged commits).
4. **REJECTED by the user (2026-09-17): converting `TStoWasm` to a class / `TSEmitter`.** It would be ~90% of the file, so the
   split buys nothing; every "blocked until Step 5" note means "not happening". The neutral layer (~1k lines) was reached
   WITHOUT it, as plain functions and methods on `FunctionContext`/`Types`/`ClassInfo`/`DataSection`/`TagSection`. Moving an
   individual genuinely-neutral function onto those is still right. Do not revive the class split as "unlocking" the neutral half.
   Do not re-propose splitting `wasm-backend.ts` for navigability: size is not an axis.

## The rules that govern every step

- **File-splitting rule (user, 2026-09-16): don't split files without a reason.** A module earns existence by having (or
  anticipating) MORE THAN ONE consumer, or by ENFORCING something that would otherwise be a convention. TS-specific types and
  TS-specific code generation stay in one file (`towasm-types.ts` was created and folded back the same day; builtins stay in the
  language's codegen).
- **A component's axis is the file's axis**: neutral iff it only manipulates neutral representations (WAT/wasm instructions) and
  ASKS the language for every source-type question through a host. AST analysis (free variables, mention tests...) answers
  questions about a language's AST, so it is per-language and stays with that language -- "no wasm concepts" means it doesn't
  belong inside the backend file, not that it belongs in a shared root. The inline-asm machinery is the neutral component
  (`wasm/codegen.ts`); only its SPELLING (`isAsm`, declared-type lowering, `declFor`, what a `TYPEINDEX` names) is per language.
- **The seam is a concrete base interface plus a language subtype, never a type parameter**, never `any`/`unknown` for a payload,
  never a cast (`AsmDecl extends WT.ClosureSig` adds only `typeIndex(text)`; a generic `AsmTypes<TA>` + adapter was tried and was
  larger AND forced). Where neutral code must construct a payload it calls a factory the language supplies.
- **The boundary is enforced by imports, not a lint rule**: a neutral module imports only `common`/`wasm/codegen`/`wasm`/
  `wat-parser` and its own submodules; the language module imports it, never the reverse. The divider (state it in the neutral
  module's header): **ask about types freely; answering with a representation (`WasmType`, `ClassInfo`, an index, an
  instruction) is codegen, however type-flavoured the reasoning** -- so `wasmTypeOf` stays though it reasons only about TS types.
- Closure payloads: `ClosureSig {params, result, hasRest?}` is the PHYSICAL shape `WasmType.closure` names; `FuncSig extends
  ClosureSig` adds `defaults`/`resolvedParams`/`restElem`, kept BESIDE it in `closureBindings: WeakMap<ClosureSig, FuncSig>`
  keyed by object IDENTITY (shape-keyed would answer wrongly for `(x?: Stmt)` vs `(x?: Stmt[])`), via one `closureWtype(sig)` and
  `closureSigOf(w)` that THROWS on a miss. (Making `FuncSig` carry TS types had made `WasmType`/`FuncSig` mutually recursive.)
- Import-graph fact: `type-utils` imports TS/JS/`common`/walker/printer and NOT `checker`; `checker` imports `type-utils`. Anything
  calling `checkerTypeOf`/`narrow`/`candidateFits` therefore cannot move to `type-utils`.

## Done

- `wasm/codegen.ts`: `WasmType`/`Scalar`.., `ClosureSig`, `ARRAY`/`REF_*`, `CLOSURE_FIELDS`, helpers, the inline-asm island
  (`assertFlatInstrs`, `expandTypeSwitch`, `resolveAsmLocals`, `resolveTypeExprs`), and the packed-kind pseudo-type names
  (`PSEUDO_TYPES`/`isPseudoType`/`pseudoValueType`; `type-utils`' `WASM_PSEUDO_TYPES` derives from it -- one owner, was three).
- `makeLibScope(libAst)` lives in `checker.ts` (24 callers incl. gitignored instruments); `inferTypeArgMap` is exported from
  `checker.ts` and `inferCallTypeArgs` adapts codegen's arguments to it (the duplicate, already drifted, is deleted).
- The survey's TARGETS include the extracted modules (otherwise a declaration moved out of a surveyed file reads as progress).

## Not done (only with a reason -- a second user, or two implementations of one policy)

- **`layout.ts`**: the printer layout skeleton (`indented`, `withParens`, `poss`, `maybe`, `operator`; ~60-80 lines identical across
  `ts/printer`, `py/printer`, `cpp/printer`), also the one place to fix the shared-`newline` state leak; `Printer<K>` already exists
  in `walker` with zero implementations. Must NOT absorb precedence/operator tables or node cases. **`guard<R>(types)`** -> `walker`
  (byte-identical in `cpp/walker` and `ts/walker`). **`buildStateMachine`** (~226 lines, builds only its own segments, AST surface
  ~4 facts + `bodyOf`/`withBody` + a `walkerB`; PY already parses `await`/`yield`) -> `statemachine.ts`, as separation not reuse;
  `StateMachineToAST` (no callers) stays behind. These are the only extractions with a proven second user.
- Leave alone (one possible user each): `Inference` (best shape, but PY's route is annotations, not TS's type system), `Scope`
  (storage generic, every rule TS's), diagnostics (`show()` drags the TS printer), `bindingNames`/`pathKey`/`withScope`.
- Optional Step 4 (shape neutralisation: `FuncCtx` ~250 neutral lines + `FunctionContext extends FuncCtx` ~60 TS lines; the same
  base+subtype for `ClassInfo`/`FuncSig`/`ResolvedParam`): typing neutral members' parameter as `ctx: FuncCtx` is what would
  ENFORCE the boundary. Not started; weigh against decision 4.
- `emitCallArgs` takes a signature's four parts instead of the signature (11 call sites): duplication, not a blocker.
- Per-language static-subset contract (needed only when a language is added): the backend's value is that it is NARROW AND LOUD.
  TS: passed `TStypeCheck`. C++: declared types + class layout + overload resolution (a resolution pass, not inference).
  **Python: PEP 484 annotations required on everything reaching a wasm-visible construct** -- annotations are the interface;
  unannotated -> refuse, never `any`. That row is what makes PY reachable.

## Traps recorded so they are not "fixed" into bugs

- `alwaysTruthy` (codegen) vs `T.isTruthy`: the same question with deliberately DIFFERENT answers (a boxed `any` slot may hold
  `Stmt | undefined`). Never fold together.
- codegen's `PRIMITIVE_TAGS` is `{string,number,boolean,bigint}`; `T.SIMPLE_TYPES` adds `symbol,undefined`: unifying changes `symbol`.
- `indexSignatureValueType` vs `T.indexSignatureOf`, `arrayPartOf` vs `T.arrayUnionAsArray`, `elementKindOfType` vs the private
  `T.arrayLikeElement`: complementary -- codegen needs the UNRESOLVED, as-written view `T.resolve` destroys (a `u8` tag vs `number`;
  a tag vs a class name). `shapeKey`/`layoutArgKey` are deliberately weaker keys than `T.typeKey`: five key functions over three
  vocabularies, do not merge.
- `asmDeclaredType` is NOT a duplicate of `typeOf`/`wasmTypeOf`: `builtinTypes` holds only `i32/i64/f32/f64/u32` and `T.resolve`
  leaves pseudo-type names unresolved, so `typeOf(RefType('i8'))` is `undefined` while an asm signature's `i8` means `i32`.
  Deleting it means teaching the general mapper the pseudo-type spellings: a general, difftest-gated codegen change.
- `collectRangeWidenings`, `ownerFor`/`arrayKindOf`-style helpers, `staticGuard`, `iteratesByProtocol`, `narrowedTypeOf` read like
  type algebra but are codegen POLICY over codegen's own `stmtScope`; they stay.

## Refuse these (the workarounds this plan exists to avoid)

Adding PY/CPP case labels to the TS switches; lowering an unmodeled construct as `any`/default instead of refusing; any per-language
name special-case in the language-free half; weakening `test-towasm` expectations for a second language (a new language is additive,
the TS path's bytes must not move); treating the VSDG's `passthru` as an escape hatch in the backend path -- the principled channel is
the inline-asm island (`__asm`/`$T`, WAT text): "I can't model this" is spelled in the source language, at the source, visibly.

Related: [[tison-towasm]], [[tison-vsdg-dialects]], [[tison-vsdg-node-type]], [[tison-ast-convergence]],
[[tison-towasm-self-hosting-plan]], [[tison-session-handoff]].
