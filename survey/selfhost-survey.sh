#!/bin/sh
# Self-hosting survey. Runs from the packages root (where node_modules is), whatever the current directory.
#
#   compiler/survey/selfhost-survey.sh                    # whole dependency set
#   compiler/survey/selfhost-survey.sh --whole            # skip per-declaration probing (fast, ~15s)
#   compiler/survey/selfhost-survey.sh path/to/one.ts     # a single file
#   compiler/survey/selfhost-survey.sh --aggregate        # re-render tables from existing per-file JSON
#   compiler/survey/selfhost-survey.sh --live             # survey the working tree, not the snapshot
#   compiler/survey/selfhost-survey.sh --plan             # print every slice as JSON (what CI fans out)
#   compiler/survey/selfhost-survey.sh --worker <file> --slice <start>:<count>   # one slice
#   compiler/survey/selfhost-survey.sh --merge            # merge the slices' parts, then render as a run does
#
# The surveyed SOURCE is the frozen snapshot `selfhost-snapshot.sh` takes (it refuses to run without one), so a
# delta measures the compiler; refresh the snapshot deliberately, and read that run's delta as the source's.
#
# PRINTS the tables to stdout -- redirect them yourself. Writes $SURVEY_OUT (default compiler/assistant)/selfhost-survey.json
# (scriptable) and per-file JSON under $SURVEY_OUT/selfhost-survey/.
#
# Read the "Causes, ranked by declarations unblocked" table as the work queue. Re-run after each
# fix and diff: the table delta is the unit of progress. A fix that moves one row by one is
# evidence you fixed a symptom, not a cause.
set -e
cd "$(dirname "$0")/../.."
exec npx ts-node -T \
	--compilerOptions '{"module":"commonjs","target":"es2022","rootDir":".","ignoreDeprecations":"6.0"}' \
	compiler/survey/selfhost-survey.ts "$@"
