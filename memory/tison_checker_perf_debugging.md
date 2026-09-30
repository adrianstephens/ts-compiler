---
name: tison-checker-perf-debugging
description: How to root-cause a type-checker performance hang/exponential-blowup in tison's checker.ts/type-utils.ts — empirical bisection + real stack traces over --prof, which gave misleading data twice in one session.
metadata:
  node_type: memory
  type: feedback
  originSessionId: dd9b34bb-3a6a-434d-b03c-a908764c046d
  modified: 2026-08-24T01:33:31.082Z
---

Root-caused a real 16+-hour type-check hang in `binary-libs/src/wasm.ts` down to 844ms
(see [[tison_towasm_self_hosting_plan]] for the full writeup and the actual fix). The technique that
got there, and the dead ends that cost the most time, are worth keeping for the next hang like this.

**`--prof` (V8's log-based profiler) gave actively misleading data twice in one session — don't trust
it alone for this codebase.** Once it attributed 78% of all ticks to an unrelated V8-internal
`metrics::Recorder` C++ symbol with no real JS callers shown; once it made a trivial 4-line test file
look dominated by `node::fs::Access`, when a live stack trace on the *same* hang showed clean, unrelated
deep JIT recursion with zero filesystem involvement. **macOS's `sample <pid> <secs> -file <out>` gave
the correct, real call stack both times `--prof` didn't** — use it directly on a live hung process
instead of (or at minimum alongside) `--prof`, especially once `--prof`'s own story stops making sense.

**When a profiler's own hot-function list doesn't collapse under a targeted memoization fix, verify
empirically whether it's really a *missing cache* (same logical work redone) before designing more
caching layers — it might be a *different* bug: a duplicated-evaluation bug elsewhere producing
genuinely distinct objects each time.** The tell: add a `WeakSet` at the suspect hot line and check
whether repeat "hits" are the *same* object reference recurring, or brand-new objects every time. Here,
524,288 resolutions of one class's own type at a 20-call chain were **all genuinely distinct objects**
(zero repeats) — meaning no reader-side cache (however cleverly keyed) could ever fix it, since each
object still needs at least one visit. Two reasonable-looking targeted caches were tried and measured
before this was understood, and neither moved the timing at all — cheap to try, but don't keep
iterating on caching without first checking whether repetition is even the right frame.

**Once duplication is suspected upstream of the profiler's hot spot, get a real stack trace at a
specific occurrence count, not just a hot-function list.** A counter (`if (occurrenceCount === 1000)
console.error(new Error().stack)`) at the exploding line, checked at a moderate sample point (not the
first few calls, which are often setup noise), pinpointed the exact two call sites
(`checker.ts:1189` vs `:1208`) computing the same receiver expression's type through two independent
paths — one directly, one indirectly through a sibling case's own internal re-derivation. This is the
same "temporary print/instrumentation in the hot path, remove after" technique from
[[tison_debugging_technique]] (used there for parser conflicts), just applied to the checker instead —
the general lesson (empirical > guessing, delete the instrumentation once done) transfers directly.

**When a duplicate-evaluation bug's fix drops the diagnostic count, verify it's the *same* locations
before trusting it, not just a smaller number.** A memoization fix that eliminates redundant
re-evaluation naturally also eliminates redundant re-*reporting* of whatever diagnostics that
evaluation produced — that's correct and expected, not a regression, but only if it's true. Checked by
comparing diagnostic line:col locations before/after, not just counts: confirmed the drop (55→33 on a
bisected repro) was 100% exact duplicates at identical locations, not coverage lost from different
ones.

**Timing measurements that don't correlate with code complexity at all are worth checking for
concurrent system load before trusting them as a property of the code.** A meaningful chunk of this
session's early confusion (a trivial file sometimes running in 600ms, sometimes 45+ seconds, with no
relationship to what was in it) turned out to be a real, separate module-loader caching bug PLUS likely
contention from another concurrently-running corpus-test process on the same machine. `ps aux | grep
node` before trusting an anomalous timing result is cheap and would have saved real time here.

**Update 2026-09-27: `sample` can come back with every JS frame `???` (no JIT symbols) -- then use
`assistant/inspect-profile.mjs`.** Start the probe with `node --inspect=PORT -r ts-node/register/transpile-only ...`,
then `node assistant/inspect-profile.mjs PORT 30 6`: a CPU profile (self + inclusive per function) plus
`Debugger.pause` stack samples of the live, busy process. It found the ReadType runaway (`00c43ec`) in one run.

**Check `resolve`'s depth BAILS first.** A bail (`depthBails`) leaves every enclosing resolution uncached,
so a budget exhausted deep inside turns bounded work into millions of repeats. Symptom: alias-body resolutions
in the millions over a few hundred distinct (alias, args) pairs, with fresh objects each time. Count bails per
site before designing a cache; the fix was a budget rule (a conditional's taken branch is a tail step).

Related: [[tison_towasm_self_hosting_plan]] (the actual bug and fix this technique found),
[[tison_debugging_technique]] (the parser/grammar-side sibling catalog this borrows its empirical-first
philosophy from), [[feedback_verify_refactor_wins]] (the same "count actual deltas, don't assume"
discipline applied here to diagnostic counts).

**isAssignable's depth budget (2026-09-28).** The relation is coinductive for ref pairs (`inProgress`, keyed by
`relationKey`: names with fresh `'N` suffixes stripped + identity; NEVER `typeKey`, which printed a resolved lib type past
V8's string limit). Making union-member steps free (so only structural descent spends depth) looked principled but blew
APISample_jsdoc.ts from 15 s to >180 s -- union-vs-union search is exponential without TS's relation cache. Reverted. Open:
`Promise<number>.then(async z => 2)` still exhausts the budget of 10 without any cycle (a legit ~12-step comparison).
Instruments: `assistant/corpus-timing.ts [file...]` (per-file ms), `assistant/corpus-one-diags.ts <file...>` (all
diagnostics as the harness checks), `assistant/corpus-warn-dump.sh` (every corpus WARNING, for diffing two builds).

