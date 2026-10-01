---
name: feedback-track-total-size
description: The user worries the compiler is getting too bloated to reason about -- TOTAL size, not any one file. Consolidation is a standing rule every session carries, not a deferred project.
metadata:
  type: feedback
---

The user (2026-09-30): "I worry that the code is getting too bloated to reason about. It's not about making any one file
smaller, but the overall size ... I fear we're losing track of the consolidation."

**Why:** the 2026-09-21 audit (`assistant/backend-consolidation-audit.md`) found the bloat is NEAR-COPIES -- one mechanism rebuilt
per case. Fix-driven sessions add a few lines per site and nothing ever deletes them; consolidation only happened when a
session was explicitly about it.

**How to apply:**
- Every commit message states its net line delta in `src/`; the handoff records the `compiler/src` total at session end
  (31,906 at `d4fb83f`; wasm-backend.ts 10,427).
- Before adding lines for a fix, look for the mechanism it duplicates (`assistant/near-clone-scan.js`) and extend that instead
  ([[feedback_prefer_extending_existing_mechanism]]). Example missed 2026-09-30: the `await` trampoline and the generator step
  both needed "build from the erased class's own signature" -- two sites, should be one helper.
- New features land deletion-first where they overlap existing paths (step 4b must REPLACE `resolvePlace`'s separate erased-
  receiver branches, not add one).
- Splitting files is not the goal (user decision: no split for navigability); deleting code is.
