#!/bin/sh
# Readies a packages workspace checked out from scratch (the packages root, with tison, compiler, binary and binary-libs
# beside each other) for the survey, as CI checks it out. Run after `npm ci` in the packages root.
#
#   compiler/survey/ci-workspace.sh link    # node_modules/@isopodlabs/* links to the sibling repos, as the local workspace has them
#   compiler/survey/ci-workspace.sh build   # their dist/, which the compiler loads at run time
set -e
cd "$(dirname "$0")/../.."
case "$1" in
link)
	for dir in . compiler tison binary-libs; do
		mkdir -p "$dir/node_modules/@isopodlabs"
		ln -sfn "$PWD/tison" "$dir/node_modules/@isopodlabs/tison"
		ln -sfn "$PWD/binary" "$dir/node_modules/@isopodlabs/binary"
		ln -sfn "$PWD/binary-libs" "$dir/node_modules/@isopodlabs/binary_libs"
	done
	;;
build)
	# binary-libs compiles with binary's transform through ts-patch, so binary goes first and TypeScript is patched
	npx ts-patch install
	npm run build --prefix binary
	npm run build --prefix binary-libs
	npm run build --prefix tison
	;;
*)
	echo "usage: $0 link|build" >&2
	exit 2
	;;
esac
