---
name: tison-py-backend
description: PY/backend.ts — the minimal Python wasm back end (annotated scalar subset), the second non-TS consumer of wasm-codegen.ts. Scope, the deliberate CPython departures, and the int/float literal bug it forced.
metadata:
  type: project
  modified: 2026-09-21
---

`src/examples/PY/backend.ts` (`PYtoWasm`) + `test/test-py-backend.ts`. Written in the mould of [[tison-cpp-backend]]
with **no change to `wasm-codegen.ts`**. Not a checker: the subset is the STATICALLY typed one. Params and
returns are annotated `int`/`float`/`bool`/`None` (i64/f64/i32/void), and a local takes the type of its first
assignment. Anything else throws `W.Error`. The header comment lists the scope and the CPython departures.

`test-py-backend.ts` compiles, instantiates and RUNS the output. **Every expected value came from CPython on the
same source**, so `//`, `%`, `/` and value-returning `and`/`or` are checked against the real semantics, not against
our reading of them. Keep it that way when adding cases.

**Deliberate departures (documented in the header, not silent):** `int` is i64 (wraps/traps, no bigint); a local
read on a path that never assigned it reads zero (no `UnboundLocalError`); `and`/`or` on mixed types give the wider
type. Float `//`/`%`, `**`, shifts are REFUSED, not approximated: float `//` is not `floor(a / b)` in CPython
(`1 // 0.1 == 9.0`).

**Prerequisite found here:** py-parser gave `1` and `1.0` the same `Literal(1)`, so the AST had no int/float
distinction (and the printer wrote `1.0` back as `1`, changing meaning). Fix: a float literal keeps its source
spelling in `raw` (the field C++ already uses where the spelling is the type); the printer prints `raw`. An int has
no `raw`. Any pass reading py literals must use `raw !== undefined` for float-ness, not `Number.isInteger(value)`.
**Still open, verified 2026-09-21:** `PY/walker.ts`'s `calcBinary` folds over bare values, so `2.5 * 2` returns `5` and `PY/vsdg.ts:108` writes it back as an int literal (a float folded into an int). Needs the fold to carry float-ness.

Not built, natural next steps: `print` (a host import shifts function indices), strings, lists, `**` with a
constant exponent, definite-assignment analysis to close the zero-read gap.
