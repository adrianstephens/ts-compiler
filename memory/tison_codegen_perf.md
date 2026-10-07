---
name: tison-codegen-perf
description: Where a self-compile probe's codegen time goes (profiled 2026-10-07), what was fixed (321 -> 152 s), and what is still open -- read before working on survey/self-compile speed
metadata:
  type: project
---

A wasm-backend.ts survey probe compiles ~4400 functions (nearly the whole backend) in ~5 min; the survey repeats that per
declaration, which is why `wasm-backend.ts` slices dominate a survey's wall time. Profiled with `assistant/inspect-profile.mjs`
on one probe (`assistant/time-probe.sh`: slice 2:1, `rawElemKind`, prints ms and funcs; baseline 321 s / 4364 funcs):

- ~37% assignability (`isAssignable` -> `related`) from `collectOpenShapes`' `noteSlot`: half its `as` case (each union member of
  the operand checked against the slot), half `isOpen` -> `unbuiltShape`.
- ~16% printing types (`typeKey`) in `backToDeclaredMembers` (every narrowed read in `emitTruthy`), plus much of the 26% GC.

Fixed (2026-10-07), 321 -> 152 s on that probe:
- `isOpen` memoized per node (`8837d71`): 321 -> 250 s, output identical.
- `typeId` hashed keys whose value is `undefined`, which `typeKey` skips, so equal-printing types got different ids. `openKey`
  keys open shapes by `typeId`, so a shape `collectOpenShapes` opened (wasm.Instr's `if` member) was missed by `ownerFor` and
  compiled as a fixed struct. The fix makes the self-compile route `'dst' in i` etc. through `_any_in__*`: CORRECT, not a regression.
- `backToDeclaredMembers` compares by `typeId`: 230 -> 152 s, and an UNSTAMPED narrowed ref (`out instanceof Inference` in
  `inferTypeArgs`) now maps back to the stamped declared member instead of resolving nowhere into `<any dispatch>.add`.

Still open: ~37% in `collectOpenShapes`' assignability checks (half its `as` case); and the survey recompiling the same ~4400
functions per wasm-backend.ts declaration.

**How to apply:** diff emitted function NAMES (not counts) for any codegen perf change. `layoutArgKey` (the generic-layout key)
names structs and functions, so it stays on `typeKey`: switched to `typeId`, names became hashes. See [[tison-survey-ci]] for where slice times show up.
