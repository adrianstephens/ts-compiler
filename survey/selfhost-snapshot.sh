#!/bin/sh
# Freezes the self-hosting survey's INPUT, so its deltas measure the compiler and not edits to the surveyed
# source. Run from anywhere; overwrites any previous snapshot.
#
#   compiler/survey/selfhost-snapshot.sh                    # tison, compiler, binary-libs and binary at their HEADs
#   compiler/survey/selfhost-snapshot.sh <compiler-rev>     # compiler at that revision (the others at HEAD)
#   REV_tison=d152c61 REV_binary=3afc83d ... selfhost-snapshot.sh   # any repo at a given revision (REV_binary_libs for binary-libs)
#
# Committed source only: `git archive` never sees uncommitted edits. Each repo's `src/` lands under
# $SURVEY_SNAPSHOT (default compiler/assistant/selfhost-snapshot)/<repo>/src, the layout the survey's relative imports
# expect, with the revisions in SNAPSHOT.json. Refresh deliberately, and take a survey right after -- that run's delta is
# the new source's, not the compiler's.
set -e
cd "$(dirname "$0")/../.."
SNAP=${SURVEY_SNAPSHOT:-compiler/assistant/selfhost-snapshot}
rm -rf "$SNAP"
mkdir -p "$SNAP"
json=""
for repo in tison compiler binary-libs binary; do
	given=$(eval echo "\${REV_$(echo "$repo" | tr - _):-}")
	[ "$repo" = compiler ] && given=${given:-${1:-}}
	rev=$(git -C "$repo" rev-parse --short "${given:-HEAD}")
	mkdir -p "$SNAP/$repo"
	git -C "$repo" archive "$rev" src | tar -x -C "$SNAP/$repo"
	json="$json\"$repo\": \"$rev\", "
done
printf '{ %s"taken": "%s" }\n' "$json" "$(date -u +%Y-%m-%dT%H:%M:%SZ)" > "$SNAP/SNAPSHOT.json"
cat "$SNAP/SNAPSHOT.json"
