/// <reference path="./lib.d.ts" />

//-----------------------------------------------------------------------------
//	Proxy
//-----------------------------------------------------------------------------

// A proxy is an object of its own whose every property operation goes to its handler's trap where it has one, else to its target. Typed as its
// target, it is held as `any`, so only the backend's `any` dispatchers reach it, each through these.
export class Proxy<T extends object> {
	constructor(private readonly target_: T, private readonly handler_: ProxyHandler<T>) {}

	_get(p: string | symbol): any {
		const h = this.handler_;
		return h.get ? h.get(this.target_, p, this) : (this.target_ as any)[p];
	}
	_set(p: string | symbol, value: any): boolean {
		const h = this.handler_;
		if (h.set)
			return h.set(this.target_, p, value, this);
		(this.target_ as any)[p] = value;
		return true;
	}
	_has(p: string | symbol): boolean {
		const h = this.handler_;
		return h.has ? h.has(this.target_, p) : p in this.target_;
	}
	_delete(p: string | symbol): boolean {
		const h = this.handler_;
		return h.deleteProperty ? h.deleteProperty(this.target_, p) : delete (this.target_ as any)[p];
	}
	// `Object.keys/values/entries`: the target's keys (no `ownKeys` trap), each value through `get`.
	_anyEntries(which: string): RawArray<any> {
		const keys = Object.keys(this.target_), out = new RawArray<any>(keys.length);
		for (let i = 0; i < keys.length; i++)
			out[i] = which === 'keys' ? keys[i] : which === 'values' ? this._get(keys[i]) : [keys[i], this._get(keys[i])];
		return out;
	}
}
