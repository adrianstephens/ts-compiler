---
name: instrument-self-compile-trap
description: a debug line added to wasm-backend.ts is ALSO compiled by the self-hosting probe of wasm-backend.ts -- probe a separate snapshot of the committed sources instead
metadata:
  type: project
---

The TStoWasm probe compiles `compiler/src/ts/wasm-backend.ts` with the compiler running from that same file, so a temporary
`console.log(new globalThis.Error().stack)` in it changes the SUBJECT too (2026-10-08: the probe then stopped on the debug line,
"'new' is only supported for a known class"). String throws carry no stack, so instrumenting is often needed.

**How to apply:** snapshot the committed sources into a scratch dir and probe that, while the live `src/` carries the instrumentation:

    SURVEY_SNAPSHOT=compiler/assistant/probe-snap sh compiler/survey/selfhost-snapshot.sh
    SNAP=compiler/assistant/probe-snap npx ts-node -T compiler/assistant/probe-decl.ts compiler/assistant/probe-snap/compiler/src/ts/wasm-backend.ts TStoWasm

Never point `SURVEY_SNAPSHOT` at the survey's own `selfhost-snapshot` (its deltas assume a deliberate refresh). Remove the
instrumentation by inverse edit, not `git checkout -- <path>`, and delete `probe-snap` afterwards.

Related: [[tison_session_handoff]], [[tison_towasm_self_hosting_plan]].
