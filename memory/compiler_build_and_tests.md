---
name: compiler-build-and-tests
description: how compiler/ builds and how its tests are launched -- tests import the BUILT dist, build vs build:emit, the dist/ts/lib copy traps (moved here from tison_project at the compiler split)
metadata:
  type: project
---

- **The suite imports the BUILT package** (`'../dist/...'`, switched 2026-09-15), still run by ts-node `-T`,
  so a run tests what ships and `test/tsconfig.json` type-checks against `dist/**/*.d.ts` (src type errors no
  longer leak into a test run). `npm run build` in compiler is now the COMPLETE build -- `tsc && postbuild (copylib + tsw shebang)` -- and it copies the lib FIRST, because a failing `tsc -b` skips npm's `postbuild` and would
  otherwise leave dist half-complete (stale lib = silently wrong checker/towasm counts). It is strict (exits
  nonzero on type errors); `npm run build:emit` is the tolerant twin (`tsc; postbuild`) used by
  `gate`/`checker`/`libdecls`/`ast-gate.sh` so those still run while src is red. **How tests are launched**:
  the WORKSPACE config (`packages.code-workspace`) -- "Test current" runs `${file}` under ts-node with
  `preLaunchTask: build-current-folder` = `npm run build` in the file's folder (its `debug.onTaskErrors:
  debugAnyway` lets the launch continue while that build reports errors). `compiler/.vscode/launch.json`'s own
  "Test" config runs a `test/test.ts` that does not exist -- vestigial, nobody uses it.
- **`dist/ts/lib` is a COPY** (`copylib`, via `postbuild` and `build:emit`), and it arms two traps
  that hid it for weeks: `cp -r src/.../lib dist/.../lib` nests `lib/lib` when the target exists, and npm
  SKIPS `postbuild` entirely when `tsc -b` exits nonzero. Both fixed 2026-09-15 -- `ts/wasm-backend.ts` reads that
  lib at runtime, so a stale copy silently shifts checker/towasm results (it moved test-ts-parser's counts).
- One tsconfig now (the old `src/examples` needed its own invocation; that trap is gone with the split).
