import * as path from 'path';

// `ModuleLoader` paths sending the sibling packages to their SOURCE under `root` (the packages root, or a snapshot of it), relative to
// `fileDir`: their `exports` maps name built `dist/*.js`, with no bodies to compile. Prefix-matched in order, so bare names go last.
export function siblingSourcePaths(fileDir: string, root: string): Record<string, string[]> {
	const rel = (pkg: string) => path.relative(fileDir, path.resolve(root, pkg, 'src')) + '/';
	return {
		'@isopodlabs/tison/':		[rel('tison')],
		'@isopodlabs/binary_libs/':	[rel('binary-libs')],
		'@isopodlabs/binary/':		[rel('binary')],
		'@isopodlabs/tison':		[rel('tison') + 'tison'],
		'@isopodlabs/binary':		[rel('binary') + 'index'],
	};
}
