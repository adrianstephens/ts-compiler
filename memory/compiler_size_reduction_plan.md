---
name: compiler-size-reduction-plan
description: The 2026-10-02 whole-file examination of ts/wasm-backend.ts -- seven families of work the backend re-derives that the checker, its scopes or a single mechanism already own, with line counts, the target mechanism for each, the order, and which need a user decision. The work queue for cutting the compiler by thousands of lines.
metadata:
  type: project
---

The user (2026-10-02): near-clone scanning is not enough; wanted a deep examination of how the code works together, aiming
for a cut "of the order of thousands of lines", mostly from `ts/wasm-backend.ts`, "which has had stuff handled elsewhere
added to it many times". The whole file (10,450 lines; ~2,000 of them comments) was read end to end. The finding: the bloat is
not copy-paste but **the backend keeping private copies of knowledge the checker already has** (bindings, flows, name/module
resolution, contextual types), plus several mechanisms built twice. Line counts are of the code as of `dfc6d96`.

## The families (est. saving in wasm-backend.ts)

1. **Bindings and flows, re-analysed (~970 lines -> ~350).** Three whole-program walks each build their own binding/call graph:
   closure capture (`ownBoundNames`, `collectFreeVars`, `collectClosureFreeVars`, `namesSelfAsValue`, `collectCapturedMutables`,
   `closureDefaultIsSelfContained`, `ctorNeedsEarlyThis`, `ensureForwardHolder`, `needsHolder`, `resolvesGlobally`, `emitStmts`'
   per-statement free-name re-walk, which is quadratic); `collectExpandoFields`' Container/Binding/Fn points-to graph (L1681-1947);
   `collectOpenShapes`' `slotOf`/`escapingParams`/`walk`. Target: ONE binding analysis -- each identifier to its declaration
   (the checker's scopes already hold `declarator(name)`), each function's free/assigned/captured sets memoized per node -- that
   all three read.
2. **Name and module resolution (~400 -> ~175).** `stmtHomeModule`, `topLevelVars`, `functionDeclByName`/`homeKey`, `moduleFunctions`,
   `namedImportsByModule` lookups, `resolveDecl`, `lazyGlobalFor`'s three branches, `functionValueDecl`, `isModuleValue`,
   `classRefTarget`/`classAliasTarget`/`isAliasInit`, `classIdentity`/`moduleTag`/`moduleTagOf`/`otherDeclaration`/`shapeEntries`/
   `classEntries`, `LIB_MODULE`. Target: identity is the DECLARATION node (the checker resolves a name, imports included, to it;
   each declaration knows its module); maps keyed by decl, not by mangled name strings.
3. **Which struct an object literal builds (~450 -> ~200).** `case 'object'` tries six owner-finders then guesses
   (`matchObjectShape`, `matchObjectShapeByType`, `findObjectShapeByType`, `contextualShapeOwner`, `matchContextualUnionMember`,
   `spreadOwner`, `emitUnionShapedLiteral`, `holdsLayout`, `layoutTwin`...). Target: the checker stamps the contextual type it
   checked the literal against (the union member its discriminants select, as TS does); the literal is built as that type's struct.
4. **Two type-to-representation walks (~370 -> ~220).** `typeOf`/`wasmTypeOf` and `ownerFor`/`flattenOwners`/`tupleArrayOwner` walk
   the same TS type cases separately; `layoutSketch`/`genericSketch`/`ownsLayout` are a third, pre-codegen copy. Target: one
   `representation(t) -> { wtype, owner }`.
5. **Expandos and accessors on structs (~350 -> ~100). NEEDS A USER DECISION.** Statically computed expando fields
   (`collectExpandoFields` first half, `addExpandoFields`), `#get:`/`#set:` companions in every field read/write, and
   `emitObjectDefineProperty`'s three cases. Option: every key a struct gains at run time lives in its one `#ext` dynamic object
   (slower reads of expandos -- the AST `scope`/`pos` stamps -- accepted before for dynamic objects).
6. **The type-query zoo (~300 -> ~150).** `checkerTypeOf`, `typeAt`, `stampedTypeOf`, `narrowedTypeOf`, `narrowedValueTypeOf`,
   `physicalTypeOf`, `wtypeOf`, `operandInfo`, `scalarBinding`, `arrayKindOf`, `objectArrayKind`, `elementKindOfType`, `storageKindOf`,
   `physicallyAny`, and `case 'var_decl'`'s ~70 lines of type special cases (TypedArray alias, erased generic method returns).
   Target: stamps complete (a synthesized node is typed where it is built), one `typeAt` and one `wtypeOf`.
7. **Comments (~2,000 lines, 585 over the 2-line cap, many 200-300 chars).** Trimmed inside each family as it is rewritten,
   then one pass with the printer-based code-identity gate ([[tison_comment_pass_tooling]]). ~600-800.

Total ~2,300 lines from wasm-backend.ts. `checker.ts` (3,756) and `type-core.ts` (3,880) were NOT examined; do that next.

## Order and gates

6 first (foundation for 3 and 4), then 1, 2, 4, 3; 5 after the user decides. Each family lands deletion-first, its own
commit(s), net line delta in the message. Refactor proof: the towasm WAT A/B (`suite-wat-diff.py`; build:emit on both sides);
then checker, cpp-backend, difftest; the survey once per family. A WAT change is allowed only when explained.

## Progress

- 2026-10-02 `835a5d9`: function prelude (`declareFunc`/`beginBody`/`emitFuncBody`, `resolveParams` takes the rest): -6
  lines (its commit message wrongly says -20).
