---
name: tison-vsdg-cpp
description: "compiler/src/cpp/vsdg.ts -- the C++ half of the language-neutral VSDG: the widened top level (Definition vs Stmt), what is modelled vs verbatim, the typed constant-fold model, `++`/`--` as an unmodelled mutation that re-binds its name, switch, and the C++-specific bugs and limits found. Distilled 2026-09-30; history in git (1c439ff)."
metadata:
  type: project
---

Built 2026-09-14..16 (dialect + builder + emitter + pipeline; folding; switch; ~41 exact-output cases in `test/test-vsdg-cpp.ts`). `CPP.parse` is ASYNC
(the preprocessor's include resolver), so this suite's harness is async -- the only harness difference. Seam design: [[tison_vsdg_dialects]].

## The one structural difference: the top level is DEFINITIONS

`CPP.Definition` (function_def/namespace/template/out-of-class member defs/...) is NOT a subset of `CPP.Stmt`, so this language's `S` is the widened
`TopLevel = Definition | Stmt`; `Emitter.build()`/`emitChain` hand back a MIXED list, so a caller dispatches per item (`isDefinition(item)` is exported:
the printer has separate `definition` and `statement` entry points). `walkerB()` bridges the walker's kinds: only tags that CANNOT be a statement go to
`w.definition` (`DEFINITION_ONLY` = function_def/namespace/linkage/template/method_def/operator_def/constructor_def/destructor_def/static_member_def);
everything else -- including `declaration`/`typedef`/`using`/`static_assert`, which are in BOTH unions -- goes to `w.statement`. The widened `S` also
removed the blocker that made C++ look hard (the builder never sees the top-level array; `BuildVSDG` owns the walk start).

## C++-specific lowering decisions

- `T` is the whole `CPP.DeclarationSpec`, so a declaration prints itself (storage class included). C++ var nodes carry NO `declKind`: a `var` WITH a
  `typeAnnotation` prints a declaration, one WITHOUT prints a plain `x = 1;` (a name a verbatim statement declared, or a global) -- a type can never be
  invented on this AST. `needsDirectPlacement` (CORE) treats a var with a `typeAnnotation` as a declaration too (declKind would read as "may be elided"
  and an assignment's own TARGET would resolve to the initializer: `0 = 1`). `makeTempDecl` uses `auto`.
- An assignment is an EXPRESSION and a mutation either way (`lowerAssign`); a name never seen declared / not local to the function gets forcedPrint (a
  store to a global is observable). `a->b` is modelled (core member node `pointerMember?: boolean` stamp). Everything else unmodelled becomes an EFFECT
  (ordered, printed verbatim, never assumed pure): `new`/`delete`/`functional_cast`/`cpp_cast`/`typeid`/`alignof`; lambdas build a function region (below);
  `++`/`--` re-bind their name (below).
- A declaration is modelled only when every declarator is a plain INITIALISED NAME (`int *p = ...` needs a type rewrite; `int x;` has nothing to bind
  but must print: both verbatim). A function_def with any parameter DEFAULT stays verbatim (the default lives only in the verbatim signature, so a name it
  mentions would look unread and be elided). A parameter's name comes from `declaratorName`, which digs through pointer/array/reference wrappers.
- **A parameter node is a `var` with `name` set but NEVER `bound`** -- that keeps `emitLocalStatements` from printing a parameter as a named slot
  (`slotName(node)` undefined) and `resolveNode`'s no-declKind case resolves it by name.
- No constant folding when there's no type to fold in (a literal whose spelling can't pin a type -- `long double`, string literal, `nullptr`, `sizeof` --
  or an operation C++ leaves undefined/unspellable).

## Constant folding -- a typed scalar model

C++ arithmetic is defined in terms of a TYPE, and the only type this AST has is a literal's SUFFIX. So `Literal` has an optional `raw` (source spelling):
c-parser keeps it, `cpp/printer.ts`'s `literal()` prints it verbatim (a suffixed literal now ROUND-TRIPS; `exprKey` no longer keys `1u` and `1` alike), and
`cppDialect.literalValue` reads the type back out of it.
- `Scalar = { kind, value }` (6 integer types + float/double + bool) travels between a fold's operands and result; `Dialect.literal`/`literalValue`/`truthy`
  speak it; nothing else in the core sees it. The model lives in `cpp/walker.ts` (`Scalar`/`calcBinary`/`calcUnary`/`scalarFor`/`spellScalar`) beside the
  walker, as TS/PY keep `calcUnary`/`calcBinary`.
- Integer work is in BigInt (js's `<<`/`>>>`/`&` coerce through int32). Narrowing is `BigInt.asUintN`/`asIntN` (= C++'s conversion; `asIntN(bits, v) === v` is
  "fits a signed type"). Both operands are CONVERTED to the common type first (`0u - 1 < 1u` is false; a JS folder says true).
- REFUSED (no fold): a signed result that doesn't fit (UB; unsigned wraps by definition); `/` `%` by zero; `INT_MIN / -1`; `%` and bitwise/shift on a float;
  `1 << 31`; shifts >= the width; a result past 2^53 (`~0ull` has no spelling). `||`/`&&` return a BOOL (js's `1 && 2` is 2); a float result keeps a `.` (`3.0`)
  and rounds through `Math.fround` for `float`. LP64 assumed (Windows' LLP64 differs; no spelling distinguishes them).
- A `?:` on a constant test is NOT folded by the floating-node protocol (a conditional's branches needn't be literals; dropping the losing subgraph is what
  the gamma path `foldDeadBranches` does and a `floating` node can't). `Dialect.truthy` serves the constant-condition case.

## Grammar bugs found (c-parser, PRE-EXISTING)

1. FIXED: the unary rule built every prefix operator as `'+'` (the matched operator was captured and discarded): `-x`/`!x`/`~x`/`*p`/`&x`/`++x` all parsed
   AND printed as `+operand`.
2. **OPEN (verify before relying), pinned in the suite as two `KNOWN BUG:` cases**: c-parser's expression grammar is the single-block-plus-`WithPrec` shape
   `py-parser.ts`'s header warns against (right-associative, wrongly-nested trees when the operator sits behind a `OneOf`): `-1 + 2` parses as `-(1 + 2)`
   and `10 - 2 - 3` as `10 - (2 - 3)`, so the pipeline prints `-3` and `11` where C++ says `1` and `5` -- a wrong TREE becomes a wrong CONSTANT under
   folding. Fix is the documented precedence CASCADE (one nonterminal per level, right operand a different one, as `js-parser`'s `binaryChain`) in both
   `c-parser.ts` and `cpp-parser.ts` (whose `new`/`delete`/`spread` are pushed onto the same flat level). The two cases fail the moment it is fixed.

## switch

The cascade is the CORE's (`buildSwitch`); `CPPBuilder` implements `SwitchSyntax` (`local` = an `auto`-typed hidden var, `comparison` = `==`, `condition`,
`setHit` = an identifier-spelled `true`; there is no boolean literal on this AST). C++'s own parts: the body is FLAT (`case 1: g(); break;` parses as three
SIBLINGS; `case 1: case 2: g();` chains through the label) and is regrouped by `switchCasesOf` (= `transpile.ts`'s `cppSwitchToTs` algorithm), which returns
undefined for what it can't regroup (a statement before the first label, a second `default:`) -- those stay verbatim, as does an empty switch;
`makeSwitch` wraps a case that DECLARES in its own block (`case 1: { int y = 1; ... }`) since C++ forbids jumping past an initialisation.
**STILL OPEN**: a switch whose case bodies are only pure assignments ELIDES into a ternary (TS does too) and C++ then prints the stores as assignment
TARGETS inside it (`... ? v = 1 : v`) while the declaration `int v = 0;` doesn't print -- invalid C++. Candidate fix: make `nodesAt` add port-2
direct-placement nodes to an anchor's block even when `blockIds` exists.

## Bugs found (classes of mistake)

1. **SHARED with PY/TS, fixed only in CPP**: a name mentioned ONLY as a bare identifier inside verbatim text had no graph reader, so its declaration was
   elided (`int x = 1; switch (x) {...}` printed a switch reading undeclared `x`). Fix in `lowerExpression`'s 'identifier' case: while `this.verbatim`,
   connect the resolved node to a fresh `readOnly(expr)` reading node (inherently `suppressed`). TS/PY still have it; earlier tests only mentioned names as
   CALL OPERANDS, which do create edges.
2. **c-parser ambiguity forks**: `S *p = 0;` with an unknown type name forks into a pointer declaration and a multiplication and BOTH readings come back as a
   NESTED LIST where a statement is expected (alternatives, not a sequence; lowering both ran the statement twice). CPP takes the first; no other consumer
   handles the shape.
3. A declaration was elided while a surviving store named it (`int x = 1; if (0) { x = 2; } else { x = 3; } return x;` printed `return x = 3;`). `hasForcedSibling`
   misses a store INLINED into its reader; replaced by `nameStoredTo(name, id)` (a declaration survives when any node binds the name OR any `mutation`'s payload
   targets it -- folding a branch away bypasses the gammaValue that held the name, leaving only the store). **Tried and reverted: force-printing every store**
   -- tidier but it REORDERS the store against the read that was inlining it and duplicates it, since `resolveNode` resolves a name only once `names` has it
   (print order, not build order). Keep the store inlined, keep the declaration.
4. **Lambdas leaked their body into the enclosing function** (the unmodelled-expression fallback descends into everything). Now `case 'lambda'` builds a real
   function region (`buildFunctionBody` + `entry.expr = e` + `end = entry`) and does NOT descend; `paramSlotsOf(params)` split out for a lambda's own parameter
   list and `readOnly(expr)` gives a reader to a name only the lambda's TEXT mentions (a capture the body never reads, a parameter default) -- without it the fix
   would have regressed. PY has the identical leak (`PYBuilder`'s `case 'lambda'` walks `e.body` BEFORE `buildFunctionBody`) plus a printer wart on
   `lambda: (a := 1)`.

## Not modelled (verbatim, deliberately)

classes/structs/unions/templates/namespaces/`using`, typedefs, `goto`/labels, `throw`/`try`, range-`for`, initializer lists, non-name declarators. **Try/catch is a
real SEAM problem**, not just unimplemented: the core's handler type is an `E` (`handlerTypeNodeId` resolves through `resolveNode`) while C++'s `catch (T e) T` is a
`TypeName`, which has no expression form on this AST -- modelling it needs the seam widened (its own type parameter, or a `TypeName`-shaped side channel), not a
hack in the dialect.

## `++`/`--`: an unmodelled mutation that still re-binds the NAME it rewrites

Falling through to the unmodelled-expression fallback is NOT safe in a graph that CSEs: it never re-binds the name, so CSE merged a read before the increment
with one after (`g(i * 2); i++; h(i * 2);` printed `auto t0 = i * 2; g(t0); i++; h(t0);` -- the shared temp is scheduled above the increment). The member form
escaped by luck (each `s.x` reads a separate CSE-skipped `member` node). `lowerUnmodelledMutation` (reached from `case 'unary'`/`'unary_post'` for `++`/`--`) keeps
the expression OPAQUE (an `effect`, verbatim, state-chained) and, for a plain identifier, re-binds the name to a fresh name-only `var` alias (`this.scope.set(name,
alias)` + `this.threadMutation(alias)`, never `bound`) so its mutation marker orders later reads after the increment; the alias prints nothing (`emitNamedSlot`
returns undefined for a `var` with no `inputs[0]`). Rebinding to the `effect` node itself would NOT work: `slotName` is undefined for an effect, so every later read
would print the whole `i++` text. **Why not modelled TS's way**: for C++ `x++` on a class type is a real `operator++` call whose value is a COPY, so TS's
materialisation (`auto t0 = x; x++;`) is only equivalent for scalars and this pass has no types; `auto t0 = x++;` is the faithful form. CPP never uses
`unary_post`/`unary_post_old`. Prefix `++x` could be a real `mutation` but would degrade the shape (`g(++x)` -> `++x; g(x)`) for no gain.
- **What it claims**: the effect is stamped `mutatesBindingId` (the alias) = "does nothing but rewrite that binding". "Builtin" is the documented assumption (the
  same stand-in as `pure<name>` for calls); a member/index target claims NOTHING. The core uses it once, in `emitLocalStatements`' effect branch: value unused AND no
  live reader of the binding -> a dead store that drops (`int f(int i) { i++; return 0; }` prints `return 0;`; `s.x++` still prints).
- **Two traps**: (1) live readers must be scanned RAW (`outputs[0]`, skipping only vestigial edges), NOT through `valueConsumers` -- a loop-carried read arrives
  on a mu's feedback port which that calls scheduling-only, and dropping `for (...; i++)`'s update on that basis is a miscompile; (2) the operand read is a real
  edge of its own (port 1 of the effect; nothing reads it, the payload prints verbatim) -- without it a later `i++`'s dependence on an earlier one is INVISIBLE and the
  earlier looked dead.
- Boundary (measured, `cpp-incdec-shapes-probe.ts`): KEPT whenever the name is read by anything that prints (a later `g(i)`, a store, a loop-carried read, even a
  VERBATIM statement's mention via `readOnly`); dropped when its only readers are themselves dead. WART (cosmetic, pinned as `KNOWN WART`): the check is per-node, not
  transitive, so `i++; i++; return 0;` keeps the first. Twelve live shapes are pinned (loop TEST, ternary condition, two arguments, two in one expression,
  member/index targets, prefix, pre-increment value read later): two live miscompiles were found here precisely because nothing was pinned.
