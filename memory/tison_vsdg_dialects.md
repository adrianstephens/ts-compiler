---
name: tison-vsdg-dialects
description: "compiler/src/vsdg.ts is the language-neutral VSDG core; ts/vsdg.ts, py/vsdg.ts, cpp/vsdg.ts are per-language dialects. The seam (what the three objects a language supplies are, and the test for what belongs in the core), the shape stamps, the verbatim-fallback rule, shared switch lowering, and the core bugs the multi-language work surfaced. Distilled 2026-09-30; history in git (1c439ff)."
metadata:
  type: project
---

2026-09-14: the VSDG middle end was made applicable to Python (then C++, [[tison_vsdg_cpp]]). Split by **impedance, not size**: one core
(`vsdg.ts`: `RawNode`/`INode`, `Scope`/`ScopeMu`, `VSDG` (a plain `Map`), `buildLoop`, `mergeState`/`reconcileVariables`, `Optimize`
(fold/CSE/dead-branch), `BlockTree`, `applyGlobalCodeMotion`, and the seam interfaces it NAMES: `Recurse`/`Dialect`/`Emitter`) plus one file
per language (`TSDialect`/`TSBuilder`/`TSEmitter` + the language's `BuildVSDG`/`Optimize`/`applyGlobalCodeMotion`/`BuildProgram`). Generics
are `<E, S, T>` (expr, stmt, type annotation, destructuring target). Node model: [[tison_vsdg_node_type]]. Terminology: "dialect" means the
`Dialect` object; the implementation of all three halves is "the language".

## The three objects a language supplies (one job each; the split is by core PHASE, which is why it reads as confusing at first)

- **`Dialect` -- FACTS only**: `identifierName`/`identifier`/`literal`/`literalValue`/`truthy`/`exprKey`/`stmtKey`/`isCSEUnsafe`/`foldable`/
  `foldValue`/`isCalleeEdge`. No walker, no lowering, no reconstruction. Passed EXPLICITLY to the free passes (`optimize(graph, dialect)`,
  `optimizeStructuralCSE(graph, dialect, protectedIds)`), never carried by the graph.
- **LOWERING -- the language's own `walkerB` + `lowerStatement`/`lowerExpression`, with NO INTERFACE.** They are methods on each language's
  `VSDGBuilder` subclass, whose base supplies the primitives they call (`makeNode`/`connectEnd`/`rebindVar`/`bindVar`/`buildLoop`/
  `walkBranch`/`mergeState`/`reconcileVariables`/`buildFunctionBody`/`lowerVerbatim`). `VSDGBuilder` has NO abstract members (`abstract` is a
  marker only -- don't look for overrides); the walker is a PARAMETER and never stored on the builder: `BuildVSDG` is
  `const builder = new TSBuilder(); builder.walkerB().statements(ast); return builder.finish();`, and the primitives that need the walker lazily
  take it as a parameter. One builder per run (it holds the scopes and expression/name maps).
- **`Emitter` -- RECONSTRUCTION**: `rebuildPayload`/`emitNamedSlot`/`rebuildFunctionDecl` plus the language's own printer, one instance per
  `BuildProgram` call. Its members stay `abstract` because they are genuine template-method steps (`emitChain`/`emitControlNode`/
  `emitLocalStatements` are concrete algorithms calling `this.makeIf(...)`/`this.rebuildPayload(...)` at fixed points); the lowering hooks are
  the OPPOSITE (`lowerStatement` DRIVES the primitives in an order it chooses -- a client, not a step).
  `emitLocalStatements` calls `buildExpr` (NOT `rebuildPayload`) for the effect/function-expression slot. Because the three parsers converge on
  common.ts, the CORE implements every constructor whose shape is shared (`makeIf`/`makeWhile`/`makeDoWhile`/`makeReturn`/`makeBreak`/
  `makeContinue`/`makeExpressionStmt`/`makeConditional`/`makeNot`/`isBreakStmt`); a language overrides only where its representation differs
  (body slots, py's deliberately UNSPELLED empty `else:`, switch, try, temp decls). `makeBlock` adapts a statement ARRAY to the language's body
  slot; `undefined` means "no body at all" (it must handle it, or every if/while without an `else` crashes in `BuildProgram`).
  Handing a `Common.If` back as `S` needs ONE assertion (`admit`/`admitExpr`): the compiler knows only a type parameter's CONSTRAINT, a lower
  bound never an upper; `S extends { type: string }` lets `isBreakStmt` read `stmt.type` with no cast.
  `Common.DoWhile` takes `(body, test)` -- backwards, it throws INSIDE the printer, leaving its shared indent state elevated and failing ~14
  LATER cases with spurious indentation (a cascade that looks like unrelated bugs).

**THE TEST for anything belonging in `vsdg.ts`: is it named in a type position the CORE uses?** `Dialect` yes (optimize/fold/CSE/builder/
Emitter), `Recurse` yes (every primitive), `Emitter` yes, `SwitchSyntax` yes (a `buildSwitch` parameter), a `Lowering` interface NO (the core
only takes a `Recurse`; it merely restated each language's own walker API) -- deleted. Wrong shapes recorded so they don't come back:
`Dialect.walk(ast, onStmt, onExpr, begin)` (the `begin` continuation existed only to hand the recurse back -- the dialect doing the core's job)
and `Dialect.walkerB(onStatement, onExpression)` (right data direction, wrong owner: a lowering concern on the facts object). The WALKER
belongs to the language's lowering half. `Recurse` is the narrowed walker shape handlers need: `recurse.statement(s)` DRIVES a subtree by
composing a language's `lowerStatement` with its grammar's descent, so driver and handler are never the same function.

## Core idioms

- **Shape STAMPS keep the core language-free** (same as `switchInternal`/`scopeAnchorId`/`capturedRead`): `plainAssign` (a mutation whose port 0
  is the never-read old value), `freshTarget` (an lvalue address that must always rebuild), `suppressed` (verbatim fallback), `handlerTypeNodeId`
  (`except` keeps its type; added to `collectProtectedNodeIds`). `isVestigialEdge` stays a `RawNode` method with no dialect reference.
- **Literal-ness is a dialect FACT, not a stamp**: `Dialect.literalValue(e)` is the inverse of `Dialect.literal(value)` (invariant
  `literalValue(literal(v)) === v`) and the ONE thing deciding whether the core may fold/CSE/inline a node; the core asks through ONE helper,
  `isLiteral(dialect, node)`, a TYPE PREDICATE (`node is NodeOf<...,'floating'>`) so the tag test is written once. A distinct 'literal' tag was
  rejected (relocates the information, forces the fold to mutate the discriminant or rebuild+rewire, adds a `case` to every switch). Exclusions
  live in ONE named place per language: CPP answers undefined for `'a'`/`nullptr`/`sizeof(T)`, PY for f-strings with interpolation and its own
  `imaginary`. A fold's VALUE is opaque to the core (`unknown` through `literalValue`/`foldValue`/`literal`), which is how C++'s typed scalar
  travels inside it. `Dialect.truthy(value)`: the core must not assume `!!v` (a C++ value carrying a TYPE is an object, always true).
  `Literal.raw` (optional) keeps a source literal's own spelling (a C++ suffix IS its type; `1u` != `1`); adding the optional second parameter to
  `Literal(value, raw)` broke an `Array.map(Literal)` (index arrived as `raw`).
- **Destructured params are the language's business**: `ParamSlot = { name } | { token, desugar(tempName) }` -- the core allocates the hidden temp and
  its port, the SLOT carries the step finishing the binding (a closure, since finishing a pattern WALKS statements = lowering; `Dialect.desugarPattern`
  deleted). `destructuredParams` is `Map<unknown, string>` keyed by whatever token the language uses.
- **`switch` is SHARED**: `VSDGBuilder.buildSwitch` owns the whole cascade (discriminant wrapper, per-case match flags, the `__hit` flag, the per-case
  SCOPE, state gammas, `break_scope` wiring); a language supplies only `SwitchSyntax<E,S,T>` (`local(value, name)`, `comparison(discName, test)` --
  `===` vs `==`, `condition(hit, match, others)`, `setHit(hit)`). Two measured reasons it had to be the core's: the per-case scope (TS CRASHED on
  `case 1: let y = 1;`) and the naming scheme: each helper's NAME is built at its own `local` call from the id its node is about to get (borrowed
  WITHOUT consuming an id): `__disc_6`/`__match0_10`/`__hit_13`, per-helper numbers, only unique per switch (the helpers live in the ENCLOSING
  scope, so two switches would collide on a fixed name) -- borrowing the counter leaves later ids alone. `local` must never spell an empty `name`.
  `bindVar(node)` (name already on the node, nothing re-bound) is the primitive for declaration sites; `rebindVar`'s `isDeclaration` flag stays
  for PY's walrus (nameless `mutation`) and C++'s assignment-that-declares; NOT for TS `import` bindings, which create a never-bound name on
  purpose (`bindVar` would set `bound` and print a spurious `let x;`). Divergence: the per-case scope means a declaration in one case is not
  visible to a later case (real JS has one block scope for the whole switch); the builder drops it on the case-1 path instead of initialising it.
  Both are a runtime error on the enter-at-case-2 path, so nothing that worked regressed.
- **Body slots are `S[]`, not `S`.** js/c wrap in `Block`; py needs the array as-is. Do not reintroduce a `makeBlock` on the core's surface (it would
  force a fake block node on Python).

## THE VERBATIM FALLBACK RULE

An unmodelled statement must go through `lowerVerbatim(s, walk)`, **never `process(s)` alone**: `process` lowers a construct's insides but never anchors
the construct, so it VANISHES and its body runs unconditionally; even anchored, its insides were scheduled at `block_entry` and printed twice.
`lowerVerbatim` descends (bindings the text mentions keep a reader) while stamping everything it creates `suppressed`, then anchors the statement as
one opaque step, restoring `end`/`exited`/`brokeOut` first. It fixed FOUR live TS-path miscompiles: `try { g(); } finally { h(); }` -> `g(); h();`;
`for await (const x of y) { g(x); }` -> `const x; g(x);`; `L: { g(); }` printed twice; same for `with`. Behaviour of unmodelled constructs is now
"prints verbatim, exactly once". A consumer that is itself `suppressed` cannot recompute a value inline (`needsTemp` forces materialisation);
`resolveNode` returns the bare name for a node both `suppressed` AND `bound` (a name rebound inside a verbatim statement is defined only by its text).

## Core bugs found by the multi-language work (all fixed; recorded as classes of mistake)

- `new Set<NodeId>(graph.root)` -- a NodeId is a string, so a set of its CHARACTERS; the root was never protected (`[graph.root]`);
  `foldDeadBranches` also MOVES `graph.root` to the winning branch's tail when it removes a root gamma.
- `buildEffectExpr`'s `case 'unary'` was dead code from when `await` was a `Unary`; now `case 'await'`. `GetNode`'s `throw "missing node"` became
  a real `Error` naming the id.
- **Postfix `x++`**: the old-value snapshot is a pure value GCM sinks to its consumer's block, possibly PAST the increment, so `g(i++)` could read
  the NEW value. Fix: the dialect's postfix lowering wires the snapshot INTO the increment as a scheduling-only consumer edge
  (`connectValue(oldNode, 0, node, 1)`); `RawNode.isVestigialEdge` calls that port vestigial (never a value read -- an unused snapshot materialises
  nothing) while `scheduleLate`'s `isSchedulingRelevant` still counts it. TS's `unary_post_old` uses `resolveOperand` not `resolveTarget` (share the
  target's materialised read or a member target is evaluated twice). TS is the only dialect with a postfix lowering.
- **Empty-`if` husk**: a branch pair whose only content is the value it merges reconstructs that value at its consumer, leaving neither arm a
  statement; the anchoring `if` printed regardless. It now drops UNLESS the condition is not a pure subgraph (`isPureSubgraph`; a call like `g()`
  prints nowhere else) or is materialised (`nodeVariableNames.has(conditionId)`).
- **Impure condition of a merged value printed TWICE**: `valueConsumers`'s "port 0 of a control node is a state edge" rule is wrong for per-variable
  merges, whose port 0 IS the condition they print; it now counts that port so the call materialises. That exposed `buildConditional`'s
  `cond ? x : x -> x` collapse dropping the condition (and the call) entirely; guarded on `isPureSubgraph(condition)` (`return g() ? i : i;` is
  odd-looking but correct).
- **A DEAD name's mutation took its effectful RHS with it** (`int r = 0; r = g(x); return 0;` lost `g`). A declaration's initialiser never had the
  hole -- the tell. `surfacesValue` follows the chain of inlinable slots to whatever actually prints (cycle guard); a non-deferred effect with no
  live consumer prints as a bare statement. Safe default: an unmodelled mutation in a dead branch prints (`operator[]`/`operator++` behind a member
  target can do anything); the exception is what the DIALECT proves (CPP's `++`/`--` on a plain name claims `mutatesBindingId`).
- **OPEN, PRE-EXISTING, not switch-specific**: two SIBLING scopes each declaring the SAME name print the second declaration as a bare ASSIGNMENT
  (`if (x) { let y = ... } else { let y = ... }` prints `y = h(2);`; two sibling `while`s too) -- the reconstruction's flat name table remembers a
  name as bound once ANY earlier declaration claimed it. Only when the value can't inline; still parses; silently retargets at the first binding or a
  global. Fix in the printer/reconstruction, not by re-nesting scopes per dialect.

## Python specifics

Assignment is a statement, so a `mutation` rebuilds via `rebuildMutationStatement` and a value form exists only as `(x := v)`; the core's `var` =
the declaration of a name, `mutation` = rebinds one -- Python spells both the same, so the choice comes from `scope.get(name) === undefined` and
`declKind` is `'assign'`/`'annotate'`. `for x in it:` has no exit CONDITION (exhaustion raises), so it becomes a per-loop-sentinel iterator loop
(`__miss1 = object(); __it1 = iter(it); while True: __r1 = next(__it1, __miss1); if __r1 is __miss1: break; ...`), deliberately NOT try/except (the
target would be bound in only one of the handler's branches and no merge can reconcile a one-sided name). `compare` folds via its own `calcCompare`
(mixed-kind operands left alone: Python orders them differently from JS and `1 < 'a'` RAISES). A bare literal statement is a docstring/directive.
`makeTry` takes a `{param, type, body}` handler (JS `catch (e)` matches nothing; Python's `except E:` must keep E).
**Deliberate Python gaps (each prints verbatim)**: `with`, `del`, `assert`, `global`/`nonlocal`, loop `else:`, multiple `except` clauses, `try/else`,
class bases beyond the first, decorators, a comprehension's own loop structure, parameter defaults.

## Gate and instruments

**`compiler/assistant/vsdg-check.sh`**: `npm run build:emit` FIRST (every suite imports `../dist`; without a build a green suite tests the last emit),
`tsc` on the package, vsdg-only `tsc` on test/ (test/ has pre-existing errors; tsc's exit status is ignored and `... | grep | head` inside an `if` tests
head's status), then `test-vsdg` (TS; must stay BYTE-IDENTICAL -- they are the TS path's invariant), `test-vsdg-py`, `test-vsdg-cpp`. Differential probes
`probe-vsdg-ts.ts`/`probe-vsdg-py.ts` push the SAME shape through both dialects (the verbatim bugs only appeared once a Python construct, `with`, hit
what TS didn't test); `ifelse-shape-probe.ts` shows before/after for if/else shapes. Keep them.
