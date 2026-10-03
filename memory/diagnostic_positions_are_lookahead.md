---
name: diagnostic-positions-are-lookahead
description: A node's `pos` (and so every checker diagnostic's line:col) is the LALR lookahead token at reduce time -- the token AFTER the node, possibly on a later line -- not the node's start. Blocks line-based features such as @ts-expect-error.
metadata:
  type: project
---

`tison/src/lalr.ts`'s reduce stamps `vals.pos = actionTok.pos`, and `stampPos` copies it onto the node, so `pos` is the
token that follows the node. `const x: number = "s";` followed by a blank line and `const y...` reports x's error at
the `const` of y's line (3:1). A call reports at its `;` (`promiseTry.ts` 23:41).

**Why it matters:** `// @ts-expect-error` / `// @ts-ignore` (tsc silences errors on the next code line) were tried
2026-10-02 as a filter over diagnostics by line (`withoutDirected` in transform.ts, from tsw.ts and test-ts-official.ts)
and backed out: an end position on the line after a directive wrongly silenced the PREVIOUS statement's error, and an error
in a multi-line statement lands below the directive's line. The checker has no directive support, so the corpus A/B counts
real errors under `@ts-expect-error` (promiseTry.ts 23/28/30) as false positives.

**How to apply:** directive support needs START positions first (record the first token's position at reduce, in tison),
then a filter keyed on the error node's start line. Read any corpus "false positive" on a line under a directive as a
true error.
