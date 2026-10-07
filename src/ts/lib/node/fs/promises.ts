// `fs/promises` over `fs`'s synchronous WASI calls: each promise settles at once, its call having already completed; a failed call
// rejects with the error `fs` throws.
import { readFileSync, writeFileSync, readdirSync, statSync, Dirent } from '../fs';

export function readFile(p: string): Promise<Buffer>;
export function readFile(p: string, encoding: string): Promise<string>;
export async function readFile(p: string, encoding?: string): Promise<string | Buffer> {
	return encoding === undefined ? readFileSync(p) : readFileSync(p, encoding);
}

export async function writeFile(p: string, data: string | Buffer): Promise<void> {
	if (typeof data === 'string')
		writeFileSync(p, data);
	else
		writeFileSync(p, data);
}

export async function access(p: string): Promise<void> {
	statSync(p);
}

export function readdir(p: string): Promise<string[]>;
export function readdir(p: string, options: { withFileTypes: true }): Promise<Dirent[]>;
export async function readdir(p: string, options?: { withFileTypes?: boolean }): Promise<string[] | Dirent[]> {
	return options?.withFileTypes ? readdirSync(p, { withFileTypes: true }) : readdirSync(p);
}
