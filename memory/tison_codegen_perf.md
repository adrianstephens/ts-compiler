---
name: tison-codegen-perf
description: Where a self-compile probe's codegen time goes (profiled 2026-10-07), what was fixed, and the open typeId lead -- read before working on survey/self-compile speed
metadata:
  type: project
---

A wasm-backend.ts survey probe compiles ~4400 functions (nearly the whole backend) in ~5 min; the survey repeats that per
declaration, which is why `wasm-backend.ts` slices dominate a survey's wall time. Profiled with `assistant/inspect-profile.mjs`
on one probe (`assistant/time-probe.sh`: slice 2:1, `rawElemKind`, prints ms and funcs; baseline 321 s / 4364 funcs):

- ~37% assignability (`isAssignable` -> `related`) from `collectOpenShapes`' `noteSlot`: half its `as` case (each union member of
  the operand checked against the slot), half `isOpen` -> `unbuiltShape`.
- ~16% printing types (`typeKey`) in `backToDeclaredMembers` (every narrowed read in `emitTruthy`), plus much of the 26% GC.

Fixed: `isOpen` memoized per node (`8837d71`): 321 -> 250 s, output identical (function NAMES diffed).

**Open lead -- `typeId` vs `typeKey`.** `typeId` hashes keys whose value is `undefined` (`readonly: undefined`), which `typeKey`
skips, so equal-printing types get different ids (contradicting its own comment). The fix (one filter clause) is parked in
`assistant/typeid-undefined-fields.patch`. With it, `backToDeclaredMembers` comparing by `typeId` takes the probe to ~150 s -- but
the fix alone changes the self-compile: `wasm.Instr`'s `{op:"if"; blockType: BlockType; ...}` member loses its struct owner, so
`'dst' in i` in binary-libs' `toWAT` falls to `_any_in__*`. Suspect: caches keyed by UNSCOPED `typeId` (e.g. `bound:` relations,
alias-args keys, union dedupe) conflating same-printing types from different declaration scopes, which the stray `undefined`
fields used to keep apart. Find which before landing the fix; do not land the `typeId` switch without it.

**How to apply:** diff emitted function NAMES (not counts) for any codegen perf change; `openKey`'s result names functions, so
switching it to `typeId` turns names into hashes. See [[tison-survey-ci]] for where slice times show up.
