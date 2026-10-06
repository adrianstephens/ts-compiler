---
name: tison-survey-ci
description: The self-hosting survey runs as a GitHub Actions workflow in ts-compiler -- how it splits, what it needs pushed, where results land
metadata:
  type: project
---

The survey (`compiler/survey/`, tracked since 2026-10-06; it was untracked scratch in `assistant/`) runs in CI as
`.github/workflows/survey.yml` in ts-compiler, started by hand (`workflow_dispatch`, input `snapshot`: `previous` | `heads`).
Local runs are memory-bound (16 GB Mac, a 6 GB worker heap, ~2 workers, ~2 hours); CI gives each slice its own 16 GB runner,
20 at a time.

- `plan` job: checks out the packages root (for `package.json`/lock) and tison, compiler, binary, binary-libs beside it,
  `npm ci`, `survey/ci-workspace.sh link|build` (the `@isopodlabs` links, and the three libraries' `dist/`, which the
  compiler loads at run time), re-takes the previous successful run's snapshot revisions (or HEADs), and prints the
  slices with `selfhost-survey.sh --plan`.
- `slice` matrix: one `--worker <file> --slice start:count` each; `count` 0 is "to the end" (checking can add
  declarations, so a file's last slice is open-ended).
- `merge` job: `--merge` checks the parts against the plan (a missing part marks its file NOT MEASURED and fails the run
  after publishing), renders the tables onto the run's summary page, and uploads `survey-results` (90 days): the next
  run's delta baseline, slice-time history and snapshot revisions.

**Why:** a full local run ties the Mac up for hours; CI's wall time is the slowest slice (`SURVEY_SLICE_S` sizes them).

**How to apply:** CI sees only PUSHED commits -- of the compiler and of whatever the snapshot names in the other repos.
A run with `snapshot: previous` but no previous successful run falls back to HEADs. Compare deltas only between runs
whose summary shows the same snapshot. See [[tison-session-handoff]] for the local survey.
