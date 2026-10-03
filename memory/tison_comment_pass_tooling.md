---
name: tison-comment-pass-tooling
description: "how to rewrite comments in any compiler file safely: compact edit lists anchored to original lines, applied by towasm-comment-pass.js and proven code-identical by a printer-based verify; the bare-createScanner template trap"
metadata:
  node_type: memory
  type: project
---

Never let an editor reproduce code. The pipeline (all in `assistant/`, kept as instruments):

1. `node comment-blocks.js <file> <from> <to>` lists each run of comment-only lines with the code line after it (`»` = tab), plus
   trailing comments (`@nT`). Read ~600-800 lines at a time; output past ~30KB gets persisted, so keep ranges modest.
2. Write a compact edit file: `@a-b` then the replacement `//` lines unindented (the block's indentation is added; none = delete);
   `@+n` INSERTS comment lines before line n (to move a stranded comment to its owner); a line starting with `»` sets explicit tabs.
   `python3 comment-edits.py <baseline> <compact> <out.json>` converts it.
3. `HEADER=0,0 ALLOW_BLOCK=1 node towasm-comment-pass.js apply <baseline> <a.json> <b.json>... <out>` validates and splices: only
   comment-only ranges (or one trailing comment keeping its code prefix), never a banner, directive or protected header (default
   `18,128` = wasm-backend.ts's gap list; `HEADER=0,0` elsewhere). `ALLOW_BLOCK=1` lets a `/** */` doc block become a doc block or
   `//` lines, and a `/* */` block be deleted outright (commented-out code).
4. `node towasm-comment-pass.js verify <baseline> <candidate>` reprints both with `ts.createPrinter({removeComments: true})` and
   requires byte equality. Copy the candidate over src only if `cmp` shows src still equals the baseline (the user edits concurrently).

Keep edits anchored to ONE baseline copy per file and accumulate edit files; re-apply all of them each round. Watch two traps: an
`@+n` right after a replaced block makes a 3-line comment (merge instead), and `@+n` must name the declaration line, not a blank above it.

**Never analyse a file with a bare `ts.createScanner`.** With `skipTrivia` it reads the backtick closing `${...}` as a new
`TemplateHead` and swallows code. Comment ranges come from the AST (`getLeadingCommentRanges`/`getTrailingCommentRanges`).

History: the 2026-09-17 pass (wasm-backend.ts only, 449 -> 274 long blocks). The 2026-10-03 pass (user-approved: "remove historical
narration, keep the why", <= 2 lines) covered wasm-backend, checker, type-core, transform, type-utils, src/vsdg, ts/cpp/py vsdg and
wasm/codegen: -2,105 lines. Left alone deliberately: the grammar files (ts/js/py/glsl/wat-parser, cg/grammar -- the user trimmed
js/ts-parser comments themselves, glsl is their current work) and files with the user's uncommitted edits.
