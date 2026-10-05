/// <reference path="./lib.d.ts" />

//-----------------------------------------------------------------------------
//	JSON
//-----------------------------------------------------------------------------

type Replacer = ((this: any, key: string, value: any) => any) | (number | string)[] | null;
type Reviver = (this: any, key: string, value: any) => any;

function hex4(c: number): string {
	let out = '\\u';
	for (let shift = 12; shift >= 0; shift -= 4) {
		const d = (c >> shift) & 15;
		out += String.fromCharCode(d < 10 ? 0x30 + d : 0x57 + d);
	}
	return out;
}
// A hex digit's value, or -1.
function hexValue(c: number): number {
	return c >= 0x30 && c <= 0x39 ? c - 0x30 : (c | 0x20) >= 0x61 && (c | 0x20) <= 0x66 ? (c | 0x20) - 0x57 : -1;
}

// ES2019's well-formed JSON.stringify: a lone surrogate is escaped, a pair kept.
function quote(s: string): string {
	let out = '"';
	for (let i = 0; i < s.length; i++) {
		const c = s.charCodeAt(i);
		if (c === 0x22)
			out += '\\"';
		else if (c === 0x5c)
			out += '\\\\';
		else if (c === 0x08)
			out += '\\b';
		else if (c === 0x0c)
			out += '\\f';
		else if (c === 0x0a)
			out += '\\n';
		else if (c === 0x0d)
			out += '\\r';
		else if (c === 0x09)
			out += '\\t';
		else if (c < 0x20)
			out += hex4(c);
		else if (c >= 0xd800 && c <= 0xdbff && i + 1 < s.length && (s.charCodeAt(i + 1) & 0xfc00) === 0xdc00)
			out += s[i] + s[++i];
		else if (c >= 0xd800 && c <= 0xdfff)
			out += hex4(c);
		else
			out += s[i];
	}
	return out + '"';
}

class JSONStringifier {
	readonly stack: any[] = [];
	constructor(readonly replacer: ((this: any, key: string, value: any) => any) | undefined, readonly keys: string[] | undefined, readonly gap: string) {}

	// SerializeJSONProperty: `undefined` where the property is to be left out.
	property(holder: any, key: string, indent: string): string | undefined {
		let value = holder[key];
		if (value !== null && (typeof value === 'object' || typeof value === 'bigint') && typeof value.toJSON === 'function')
			value = value.toJSON(key);
		if (this.replacer)
			value = this.replacer.call(holder, key, value);
		if (value === null)
			return 'null';
		switch (typeof value) {
			case 'boolean':	return value ? 'true' : 'false';
			case 'string':	return quote(value);
			case 'number':	return value === value && value !== Infinity && value !== -Infinity ? String(value) : 'null';
			case 'bigint':	throw new TypeError('Do not know how to serialize a BigInt');
			case 'object':	return Array.isArray(value) ? this.array(value, indent) : this.object(value, indent);
			default:		return undefined;
		}
	}
	private enter(value: any): void {
		if (this.stack.indexOf(value) >= 0)
			throw new TypeError('Converting circular structure to JSON');
		this.stack.push(value);
	}
	private wrap(open: string, parts: string[], close: string, indent: string, inner: string): string {
		if (!parts.length)
			return open + close;
		return this.gap
			? open + '\n' + inner + parts.join(',\n' + inner) + '\n' + indent + close
			: open + parts.join(',') + close;
	}
	private object(value: any, indent: string): string {
		this.enter(value);
		const inner = indent + this.gap, parts: string[] = [];
		for (const k of this.keys ?? Object.keys(value)) {
			const v = this.property(value, k, inner);
			if (v !== undefined)
				parts.push(quote(k) + (this.gap ? ': ' : ':') + v);
		}
		this.stack.pop();
		return this.wrap('{', parts, '}', indent, inner);
	}
	private array(value: any, indent: string): string {
		this.enter(value);
		const inner = indent + this.gap, parts: string[] = [];
		for (let i = 0; i < value.length; i++)
			parts.push(this.property(value, String(i), inner) ?? 'null');
		this.stack.pop();
		return this.wrap('[', parts, ']', indent, inner);
	}
}

class JSONParser {
	i = 0;
	constructor(readonly text: string) {}

	fail(): never {
		throw new SyntaxError(this.i < this.text.length ? `Unexpected token '${this.text[this.i]}' in JSON at position ${this.i}` : 'Unexpected end of JSON input');
	}
	// The code unit at the cursor, or -1 past the end.
	code(): number {
		return this.i < this.text.length ? this.text.charCodeAt(this.i) : -1;
	}
	skip(): void {
		for (let c = this.code(); c === 0x20 || c === 0x09 || c === 0x0a || c === 0x0d; c = this.code())
			this.i++;
	}
	expect(s: string): void {
		if (this.text.slice(this.i, this.i + s.length) !== s)
			this.fail();
		this.i += s.length;
	}
	value(): any {
		this.skip();
		switch (this.text[this.i]) {
			case '{':	return this.object();
			case '[':	return this.array();
			case '"':	return this.string();
			case 't':	this.expect('true');	return true;
			case 'f':	this.expect('false');	return false;
			case 'n':	this.expect('null');	return null;
			default:	return this.number();
		}
	}
	object(): any {
		const o: { [k: string]: any } = {};
		this.i++;
		this.skip();
		if (this.text[this.i] === '}') {
			this.i++;
			return o;
		}
		for (;;) {
			this.skip();
			if (this.text[this.i] !== '"')
				this.fail();
			const k = this.string();
			this.skip();
			this.expect(':');
			o[k] = this.value();
			this.skip();
			if (this.text[this.i] === '}') {
				this.i++;
				return o;
			}
			this.expect(',');
		}
	}
	array(): any[] {
		const a: any[] = [];
		this.i++;
		this.skip();
		if (this.text[this.i] === ']') {
			this.i++;
			return a;
		}
		for (;;) {
			a.push(this.value());
			this.skip();
			if (this.text[this.i] === ']') {
				this.i++;
				return a;
			}
			this.expect(',');
		}
	}
	string(): string {
		let out = '';
		for (let start = ++this.i; ; ) {
			const c = this.code();
			if (c < 0x20)
				this.fail();
			if (c === 0x22) {
				out += this.text.slice(start, this.i++);
				return out;
			}
			if (c !== 0x5c) {
				this.i++;
			} else {
				out += this.text.slice(start, this.i);
				out += this.escape();
				start = this.i;
			}
		}
	}
	escape(): string {
		const e = this.text[++this.i];
		this.i++;
		switch (e) {
			case '"': case '\\': case '/':	return e;
			case 'b':	return '\b';
			case 'f':	return '\f';
			case 'n':	return '\n';
			case 'r':	return '\r';
			case 't':	return '\t';
			case 'u': {
				let code = 0;
				for (let end = this.i + 4; this.i < end; this.i++) {
					const d = hexValue(this.code());
					if (d < 0)
						this.fail();
					code = code * 16 + d;
				}
				return String.fromCharCode(code);
			}
			default:
				this.i--;
				return this.fail();
		}
	}
	number(): number {
		const m = /^-?(0|[1-9][0-9]*)(\.[0-9]+)?([eE][+-]?[0-9]+)?/.exec(this.text.slice(this.i));
		if (!m)
			this.fail();
		this.i += m[0].length;
		return Number(m[0]);
	}
}

// InternalizeJSONProperty: the reviver sees every value bottom-up; one returning `undefined` deletes its property.
function revive(holder: any, key: string, reviver: Reviver): any {
	const value = holder[key];
	const visit = (k: string) => {
		const v = revive(value, k, reviver);
		if (v === undefined)
			delete value[k];
		else
			value[k] = v;
	};
	if (Array.isArray(value)) {
		for (let i = 0; i < value.length; i++)
			visit(String(i));
	} else if (value !== null && typeof value === 'object') {
		Object.keys(value).forEach(visit);
	}
	return reviver.call(holder, key, value);
}

export class JSON {
	static stringify(value: any, replacer?: Replacer, space?: string | number): string | undefined {
		const gap = typeof space === 'number' ? ' '.repeat(Math.min(10, Math.max(0, Math.floor(space)))) : typeof space === 'string' ? space.slice(0, 10) : '';
		const keys = Array.isArray(replacer) ? replacer.map(k => String(k)).filter((k, i, all) => all.indexOf(k) === i) : undefined;
		return new JSONStringifier(typeof replacer === 'function' ? replacer : undefined, keys, gap).property({ '': value }, '', '');
	}
	static parse(text: string, reviver?: Reviver): any {
		const p = new JSONParser(text), value = p.value();
		p.skip();
		if (p.i < text.length)
			p.fail();
		return reviver ? revive({ '': value }, '', reviver) : value;
	}
}
