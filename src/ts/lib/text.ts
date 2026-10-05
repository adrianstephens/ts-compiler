/// <reference path="./lib.d.ts" />
import { TypedArray } from './typedarray';

//-----------------------------------------------------------------------------
//	TextEncoder / TextDecoder (WHATWG Encoding): UTF-8 both ways, and UTF-16LE decoding
//-----------------------------------------------------------------------------

// The Unicode scalar value at `i`: a surrogate pair's code point, a lone surrogate's U+FFFD (a USVString's conversion).
function scalarAt(s: string, i: number): number {
	const c = s.charCodeAt(i);
	if (c < 0xd800 || c > 0xdfff)
		return c;
	const d = c <= 0xdbff && i + 1 < s.length ? s.charCodeAt(i + 1) : 0;
	return d >= 0xdc00 && d <= 0xdfff ? 0x10000 + ((c - 0xd800) << 10) + (d - 0xdc00) : 0xfffd;
}

// `cp` as UTF-16 code units, appended to `out` (mutated).
function pushCodePoint(out: number[], cp: number): void {
	if (cp > 0xffff) {
		out.push(0xd800 + ((cp - 0x10000) >> 10));
		out.push(0xdc00 + ((cp - 0x10000) & 0x3ff));
	} else {
		out.push(cp);
	}
}

export class TextEncoder {
	get encoding(): string { return 'utf-8'; }

	encode(input: string = ''): TypedArray<u8> {
		const bytes: number[] = [];
		for (let i = 0; i < input.length; i++) {
			const c = scalarAt(input, i), n = c < 0x80 ? 1 : c < 0x800 ? 2 : c < 0x10000 ? 3 : 4;
			// The lead byte's marker bits, then six bits per continuation byte, highest first.
			bytes.push(n === 1 ? c : ((0xf00 >> n) & 0xff) | (c >> (6 * (n - 1))));
			for (let k = n - 2; k >= 0; k--)
				bytes.push(0x80 | ((c >> (6 * k)) & 0x3f));
			if (n === 4)
				i++;
		}
		const out = new TypedArray<u8>(bytes.length);
		for (let i = 0; i < bytes.length; i++)
			out[i] = bytes[i];
		return out;
	}
}

export class TextDecoder {
	readonly encoding: string;
	readonly fatal: boolean;
	readonly ignoreBOM: boolean;

	constructor(label: string = 'utf-8', options?: { fatal?: boolean; ignoreBOM?: boolean }) {
		const l = label.trim().toLowerCase();
		this.encoding	= l === 'utf-8' || l === 'utf8' || l === 'unicode-1-1-utf-8' ? 'utf-8' : l === 'utf-16le' || l === 'utf-16' ? 'utf-16le' : '';
		this.fatal		= options?.fatal ?? false;
		this.ignoreBOM	= options?.ignoreBOM ?? false;
		if (!this.encoding)
			throw new RangeError(`TextDecoder: the encoding '${label}' is not supported`);
	}

	decode(input?: ArrayBuffer | ArrayBufferView, options?: { stream?: boolean }): string {
		if (options?.stream)
			throw new TypeError('TextDecoder: streaming decode is not supported');
		if (!input)
			return '';
		const units = input instanceof ArrayBuffer
			? this.units(input, 0, input.byteLength)
			: this.units(input.buffer, input.byteOffset, input.byteOffset + input.byteLength);
		return String.fromCharCode(...units);
	}

	// The UTF-16 code units `b[start, end)` decodes to.
	private units(b: ArrayBuffer, start: number, end: number): number[] {
		return this.encoding === 'utf-8' ? this.utf8(b, start, end) : this.utf16le(b, start, end);
	}

	// An undecodable sequence: U+FFFD, or a TypeError when `fatal`.
	private invalid(): number {
		if (this.fatal)
			throw new TypeError(`TextDecoder: the ${this.encoding} data is invalid`);
		return 0xfffd;
	}

	// WHATWG's UTF-8 decoder: a malformed sequence is ONE U+FFFD up to the byte that breaks it, which is then read afresh.
	private utf8(b: ArrayBuffer, start: number, end: number): number[] {
		const out: number[] = [];
		let i = !this.ignoreBOM && end - start >= 3 && b[start] === 0xef && b[start + 1] === 0xbb && b[start + 2] === 0xbf ? start + 3 : start;
		while (i < end) {
			const c		= b[i++];
			const need	= c < 0x80 ? 0 : c >= 0xc2 && c <= 0xdf ? 1 : c >= 0xe0 && c <= 0xef ? 2 : c >= 0xf0 && c <= 0xf4 ? 3 : -1;
			let cp		= need === 0 ? c : need === 1 ? c & 0x1f : need === 2 ? c & 0x0f : c & 0x07;
			// The second byte's range excludes overlongs, surrogates and code points past U+10FFFF.
			let lo = c === 0xe0 ? 0xa0 : c === 0xf0 ? 0x90 : 0x80, hi = c === 0xed ? 0x9f : c === 0xf4 ? 0x8f : 0xbf, k = 0;
			for (; k < need && i < end && b[i] >= lo && b[i] <= hi; k++, i++) {
				cp = (cp << 6) | (b[i] & 0x3f);
				lo = 0x80;
				hi = 0xbf;
			}
			pushCodePoint(out, need < 0 || k < need ? this.invalid() : cp);
		}
		return out;
	}

	// Code-unit pairs, low byte first; a lone surrogate or an odd final byte is invalid.
	private utf16le(b: ArrayBuffer, start: number, end: number): number[] {
		const out: number[] = [];
		let i = !this.ignoreBOM && end - start >= 2 && b[start] === 0xff && b[start + 1] === 0xfe ? start + 2 : start;
		for (; i + 1 < end; i += 2) {
			const c = b[i] | (b[i + 1] << 8);
			const d = c >= 0xd800 && c <= 0xdbff && i + 3 < end ? b[i + 2] | (b[i + 3] << 8) : 0;
			if (d >= 0xdc00 && d <= 0xdfff) {
				out.push(c);
				out.push(d);
				i += 2;
			} else {
				out.push(c >= 0xd800 && c <= 0xdfff ? this.invalid() : c);
			}
		}
		if (i < end)
			out.push(this.invalid());
		return out;
	}
}
