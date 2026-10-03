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
5. **Expandos and accessors on structs. DECIDED 2026-10-02: keep the static fields** (the user: `#ext` must not exist on structs
   that don't need it, and deciding that is the same analysis as deciding the precise field; adding fields lazily during codegen was
   considered and rejected -- it cannot place a write through an `any`/type-parameter receiver, and needs late-bound field indices).
   So only family 1's work applies to `collectExpandoFields`. Original note: Statically computed expando fields
   (`collectExpandoFields` first half, `addExpandoFields`), `#get:`/`#set:` companions in every field read/write, and
   `emitObjectDefineProperty`'s three cases. Option: every key a struct gains at run time lives in its one `#ext` dynamic object
   (slower reads of expandos -- the AST `scope`/`pos` stamps -- accepted before for dynamic objects).
6. **The type-query zoo (~300 -> ~150).** `checkerTypeOf`, `typeAt`, `stampedTypeOf`, `narrowedTypeOf`, `narrowedValueTypeOf`,
   `physicalTypeOf`, `wtypeOf`, `operandInfo`, `scalarBinding`, `arrayKindOf`, `objectArrayKind`, `elementKindOfType`, `storageKindOf`,
   `physicallyAny`, and `case 'var_decl'`'s ~70 lines of type special cases (TypedArray alias, erased generic method returns).
   Target: stamps complete (a synthesized node is typed where it is built), one `typeAt` and one `wtypeOf`.
7. **Comments (~2,000 lines, 585 over the 2-line cap, many 200-300 chars).** Trimmed inside each family as it is rewritten,
   NOT a separate pass: the 2026-09-17 pass already ran, and the user chose to let load-bearing blocks exceed the cap
   ([[tison_comment_pass_tooling]]). Trim only what a change touches.

Total ~1,700 lines of code from wasm-backend.ts. `checker.ts` (3,756) and `type-core.ts` (3,880) were NOT examined; do that next.

## Order and gates

6 first (foundation for 3 and 4), then 1, 2, 4, 3; 5 after the user decides. Each family lands deletion-first, its own
commit(s), net line delta in the message. Refactor proof: the towasm WAT A/B (`suite-wat-diff.py`; build:emit on both sides);
then checker, cpp-backend, difftest; the survey once per family. A WAT change is allowed only when explained.

## Progress

- 2026-10-02 `835a5d9`: function prelude (`declareFunc`/`beginBody`/`emitFuncBody`, `resolveParams` takes the rest): -6
  lines (its commit message wrongly says -20).
- 2026-10-02 `981a774`: `ownerFor` derived from `typeOf` (primitive wrapper by `typeofName`, a class ref by name, else the
  class `typeOf`'s ref names): -95 (message says -96).
- 2026-10-02 `04241ca`: `for...in` desugars to `Object.keys(obj)` (the checker types it); `case 'var_decl'`'s AST re-typing
  (TypedArray-alias element, method owner's declared return) deleted: -98.
- 2026-10-02 `d1ceeb8`: one memoized `closureFree(fn)`/`freeIn(body, bound)` replaces collectFreeVars/collectClosureFreeVars and
  the re-walks in collectCapturedMutables, namesSelfAsValue, closureDefaultIsSelfContained, usesThis, emitStmts: -100.
- 2026-10-02 `8c037ea`: `SCALAR_CONVERSIONS` table in coerceTop; `in` uses `emitTestsAny`; a union spread uses `emitTypeCascade`: -31.
- Session total: tracked src 31,988 -> 31,658 (-330); wasm-backend.ts 10,475 -> 10,145.

## Learned (do not retry blind)

- **Family 3 via the checker's flow slot does not delete `matchContextualUnionMember`.** `stampFlow` already discriminates an
  object literal's union context (`discriminateContext`) and stamps the member; a literal with that stamp gets the same owner the
  backend finds. But a literal under a GENERIC return (`rule<T>(x => ({params}))`) has no flow (its slot is `T`), and its context
  (`{params} | {params; rest}`, inferred) has no unit discriminant -- only the backend's required-field match picks a layout, which TS
  never needs to. Recursing `stampFlow` into a literal's elements and property values (tried, reverted) adds stamps but deletes nothing.
- **`collectExpandoFields`' Container/Binding tree -> checker `declarator()`/`decl()` saves only ~25 lines**: a named function
  expression's own name has no declarator (`addLazyValue` only), and imports copy `decl` (the statement), not the declarator.
- **The deep lever is the SYNTHESIZED node.** Most fallback typing (`checkerTypeOf` on unstamped nodes, `typeAt`'s query path,
  `ctx.contextualReturn` writes at ~12 sites, `var_decl`'s `!stamped` branch) exists because desugarings (for-of, destructuring,
  spread, typeof, switch, entries, defaults) build AST the checker never saw. Checking each synthesized statement in `ctx.scope`
  (muted, stamping) would make stamps complete and let those go. Architectural: put to the user before doing it.

## Generated code (user decisions, 2026-10-02)

The user: codegen should not synthesize AST and re-lower it. Two kinds, both decided:
- **Kind 2 -- AST as a macro assembler inside codegen** (built over values codegen already holds, typed through made-up scope
  names): **emit directly**, even where that costs lines ("direct emission is simpler and has already found a bug").
- **Kind 1 -- language lowerings** (for-of, destructuring, switch comparisons, `**`, `+str`, string `+`, tagged templates, delete,
  Object.assign, parameter defaults, super(...) binding): move into **transform.ts**, and the result is **checked** with
  `checkSynthesized` (checker.ts) before codegen compiles it literally. VSDG's pre-check rewrites exist too (`ts/vsdg.ts`).

Primitives built for this (wasm-backend.ts): `emitCallOn(cls, name, HeldArg[])` (receiver on the stack; overload by the args' TS
types via `overloadByTypes`, virtual via `methodFor`, `__asm` via `inlineFor`), `HeldArg`/`localArg`/`stringArg`/`fieldArg`,
`emitMemberRead`, `emitKeyedField`/`emitKeyEq`, `emitBoxedField`/`emitBoxedFieldWrite`, `coerceAs`/`canonicalFor` (box into, or
unbox out of, `any` by a DECLARED type -- a number is the f64 box), `elementTypeOf`. Lib: `DynamicObject.spread`.
`checkSynthesized(stmts, scope)` stamps only unstamped statements/expressions in a child scope, over parts' stamps; user code
(already stamped) is skipped, so nesting costs nothing.

Done (each WAT-verified; most WAT-identical): keyed field access, dynamic-object dispatcher arms, bounded reads, Object.entries,
constructor field writes, `.call`, typeof-as-value, place stores, dynamic-object literal, overload by types, ensureAnyIndex,
copyElements, method-value wrapper, switch slot, `#ext` read; kind 1: for...of (`lowerForOf`). Size: 31,658 -> 31,799 (+141).

Left, kind 2: the union-shaped object literal (`emitUnionShapedLiteral`: needs `case 'object'` to take pre-held spread operands,
Tested-style) and compound assignment (`$compound$`: needs `case 'binary'` to take a held left operand). Kind 1 destructuring DONE (`lowerPattern` in transform.ts, one lowering: `PatternLowering` empty for VSDG -- unchanged output,
`patternBindings` collects it -- or a temp per level plus the checked "iterates?"/"absent?" answers for codegen; each declaration is
`emit`ted in order and codegen's emit checks then compiles it; `drainIterator` moved too). `checkSynthesized` checks INTO the scope
it is given (callers make the child). **Rule for every lowering: never reuse a node object -- a checked node holds ONE stamp**, so a
shared `elem`/`r`/`i` read in a narrowed branch got the unnarrowed type (found on patternDefaults; temps are now node factories).
Then (2026-10-02, all WAT-verified): `lowerExpr` (regex literal, `+str`, `**`, string `+`, tagged template) + `checkSynthesizedExpr`;
`lowerCompound` (`t op= v` -> `t = t op v`, the object/index held unless a pure path: WAT -2,894, arithmetic unchanged);
`lowerConditionalSpread`, `lowerObjectAssign`; switch comparisons, delete, var redeclaration, param binding, super(...) binding,
default re-emission all go through `lowering(ctx)` (temp / emit = check then compile / check). The union-shaped literal's arms bind
`const m = src as M` (checked). Runtime helpers' params are plain locals. Made-up typed scope names: none left but `resolvedCall`'s
`$receiver` (an oracle query for a call codegen itself makes; a type-level inference path would replace it).
**Generic method instances were compiled UNCHECKED** (functions and classes were re-checked): `checkMethodInstance` (checker.ts,
via `checkMember` split out of `checkClass`) fixes it. That exposed a checker bug, fixed: under `precise` (TS's subtype relation)
an `any` source related structurally to every object target, so `any[] <: number[][]` held and `Array.isArray` narrowed
`number[][]` to `any[]`. With every declaration checked, `case 'var_decl'`'s unstamped fallback is deleted.
Then type-core.ts: conditional-type `infer` is inferred by `inferTypeArgs` (each `infer X` a type parameter, the instantiated
pattern then checked by assignability, as TS) -- `matchInfer`, a second structural walk, deleted: -148. `inferTypeArgs` gained
what only `matchInfer` had (array from tuple, `[H, ...R]`, a rest parameter against the argument's positions with a tuple
rest expanded, call/construct signature members). Corpus GAP -27; ERROR +3, all real (promiseTry.ts lines under
`@ts-expect-error`, unsupported: [[diagnostic-positions-are-lookahead]]).
Family 2 (2026-10-02), identity = the declaration the checker's scope reaches: `resolvesGlobally` is "declared at or above the
module's scope" (`Scope.declaring`): -15. `Scope.copy` and `hoist`'s `case 'import'` now carry the DECLARATOR across an import (an
own value hid it), so `scope.declarator(name)` reaches a module const anywhere; `moduleBindings` (by declarator) replaces
`topLevelVars` and `lazyGlobalFor`'s import branch: -11 (message says -12). `functionOf(name, scope)` (decl or promoted const's
declarator -> `moduleFunctions`) replaces `resolveDecl`/`importedFunction`/per-site import lookups: -16; an imported promoted const
is now called directly. Left: `collectExpandoFields`' import lookup, `stmtHomeModule`/`classIdentity`/`moduleTag` (class
identity by module string), `funcs`/`functionDeclByName` keyed by `homeKey` strings, `LIB_DECL_MAP` (a re-parse of the lib).
Family 1 / expandos (2026-10-03): `collectExpandoFields` is ONE walk with names resolved through the checker's scopes: -57.
The old private resolution ignored block scope (a `for (const [l, r] ...)` `r` linked to another block's `const r`; one false
edge took checker.ts's walk from ~2k to ~57k visits and grew every AST shape a `typeAnnotation` field), read annotations by NAME
program-wide, and typed writes in arrow bodies in the outer scope. Verified by running old and new side by side (new is a subset
on checker/transform; every drop traced to a false edge). Typing it exposed a checker bug: `extends W.Base` made the class `any`
(`superClassRef` moved to the checker: -3), which exposed three more false positives in wasm-backend.ts, each fixed: an array
binding pattern gives its initializer a tuple context with elements widened by context (+4; message says +6), a `this is` guard
narrows a union receiver (-3), intersection members dedupe by scoped identity, not name (+1). Then `collectModules`' named-import
map and `TStoWasm`'s `namedImports` parameter, unread since `functionOf`, deleted: -60.
2026-10-03 session 2 (each WAT-identical unless noted; difftest 2229/2234 throughout): `declaredShape` shared by matchObjectShape/
findObjectShapeByType (-47); contextualShapeOwner folded into matchContextualUnionMember, which gained method members and an
anon fallback for an ambiguous member (-21); try's caught body and finally net, one helper each (-39); template literal lowers
to the `stringTemplate` call in transform.ts (-32; 4 tests' WAT -1 line: substitutions pass as the rest's nullable `any`);
bigint limb encoder one loop (-19); arrayKindOf folded into objectArrayKind (-14); dead commented-out code in TStoDecl/
type-utils/vsdg (-11); switch's two strategies share `emitCases` (-43). **Tried and kept: `spreadOwner`** -- without it
type-utils' `withReturnType` `{...m, returnType}` builds a sibling struct and needs a coercion (probe-decl WAT A/B).
`contextualShapeOwner`/`matchContextualUnionMember` deletions are invisible to the suite: their cases depend on which shapes the
whole program built (no small repro), so reason from the code and A/B a probe where one exists.
Commit-message deltas that are wrong: the bigint-limb commit (-27, truly -19); 835a5d9 (-20, truly -6), 981a774 (-96, -95), 3ac24ad (-4, -2), the fresh-node commit (+3,
+1), the method-instance commit (+18, truly +12). This log is right.
Measured: the fallback typing that exists ONLY for synthesized nodes is small (most of the 47 `checkerTypeOf` calls query source
nodes); kind 1's gain is architectural, not lines.

