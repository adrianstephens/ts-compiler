/// <reference path="./lib.d.ts" />

//-----------------------------------------------------------------------------
//	Promise (async/await)
//-----------------------------------------------------------------------------

// No host-driven asynchrony: "pending" only ever means waiting on other compiled code to resolve it.
// The microtask queue is module state, drained when the outermost exported call returns (`__towasm_exitCall`), as node
// checkpoints at callback depth 0; a re-entrant export does not run continuations early. towasm emits the hooks only
// in a program that reached the queue.
const microtasks: (() => void)[] = [];

export function __towasm_exitCall(): void {
	drainMicrotasks();
}

export function drainMicrotasks(): void {
	while (microtasks.length > 0) {
		const task: (() => void) | undefined = microtasks.shift();
		if (task)
			task();
	}
}

const PENDING = 0, FULFILLED = 1, REJECTED = 2;

interface PromiseFulfilledResult<T> {
	status: 'fulfilled';
	value: T;
}
interface PromiseRejectedResult {
	status: 'rejected';
	reason: any;
}
type PromiseSettledResult<T> = PromiseFulfilledResult<T> | PromiseRejectedResult;

export class Promise<T> {
	private state: number = PENDING;
	// `any`, not `T`: a stored `T` would give every instantiation its own struct, and a promise reaches code typed for another (`all`, `resolve`).
	private value: any = undefined;
	private reason: any = undefined;
	// Run once settled, each as its own microtask.
	private reactions: (() => void)[] = [];

	constructor(executor: (resolve: (value: T | PromiseLike<T>) => void, reject: (reason?: any) => void) => void) {
		// The two functions resolve together, once: whichever is called first wins.
		let done = false;
		try {
			executor(value => {
				if (!done) {
					done = true;
					this.adopt(value);
				}
			}, reason => {
				if (!done) {
					done = true;
					this.rejectWith(reason);
				}
			});
		} catch (e) {
			if (!done) {
				done = true;
				this.rejectWith(e);
			}
		}
	}

	// Also how an async function settles its result (`__asyncResult`): `adopt` for its `return`, `rejectWith` for what escapes it.
	private rejectWith(reason: any): void {
		this.settle(REJECTED, undefined, reason);
	}

	// Resolution with a promise follows it, in a job of its own (NewPromiseResolveThenableJob).
	private adopt(value: T | PromiseLike<T>): void {
		if (value === this)
			this.rejectWith(new TypeError('Chaining cycle detected for promise'));
		else if (value instanceof Promise)
			microtasks.push(() => value.then(v => this.settle(FULFILLED, v, undefined), r => this.rejectWith(r)));
		else
			this.settle(FULFILLED, value, undefined);
	}

	private settle(state: number, value: any, reason: any): void {
		this.state	= state;
		this.value	= value;
		this.reason	= reason;
		for (const job of this.reactions)
			microtasks.push(job);
		this.reactions = [];
	}

	then<TResult1 = T, TResult2 = never>(onfulfilled?: ((value: T) => TResult1 | PromiseLike<TResult1>) | undefined | null, onrejected?: ((reason: any) => TResult2 | PromiseLike<TResult2>) | undefined | null): Promise<TResult1 | TResult2> {
		return new Promise<TResult1 | TResult2>((resolve, reject) => {
			const job = () => {
				try {
					if (this.state === FULFILLED)
						resolve(onfulfilled ? onfulfilled(this.value) : this.value);
					else if (onrejected)
						resolve(onrejected(this.reason));
					else
						reject(this.reason);
				} catch (e) {
					reject(e);
				}
			};
			if (this.state === PENDING)
				this.reactions.push(job);
			else
				microtasks.push(job);
		});
	}

	catch<TResult = never>(onrejected?: ((reason: any) => TResult | PromiseLike<TResult>) | undefined | null): Promise<T | TResult> {
		return this.then(undefined, onrejected);
	}

	finally(onfinally?: (() => void) | undefined | null): Promise<T> {
		return this.then(value => {
			if (onfinally)
				onfinally();
			return value;
		}, reason => {
			if (onfinally)
				onfinally();
			throw reason;
		});
	}

	// `value` is absent only through the first overload, where `U` is `void`.
	static resolve(): Promise<void>;
	static resolve<U>(value: U | PromiseLike<U>): Promise<U>;
	static resolve<U>(value?: U | PromiseLike<U>): Promise<U> {
		return value instanceof Promise ? value : new Promise<U>(resolve => resolve(value as U));
	}

	static reject<U = never>(reason?: any): Promise<U> {
		return new Promise<U>((_, reject) => reject(reason));
	}

	static all<U>(values: readonly (U | PromiseLike<U>)[]): Promise<U[]> {
		return new Promise<U[]>((resolve, reject) => {
			const results	= new Array<U>(values.length);
			let remaining	= values.length;
			if (remaining === 0)
				resolve(results);
			values.forEach((value, i) => Promise.resolve(value).then(v => {
				results[i] = v;
				if (--remaining === 0)
					resolve(results);
			}, reject));
		});
	}

	static allSettled<U>(values: readonly (U | PromiseLike<U>)[]): Promise<PromiseSettledResult<U>[]> {
		return new Promise<PromiseSettledResult<U>[]>(resolve => {
			const results	= new Array<PromiseSettledResult<U>>(values.length);
			let remaining	= values.length;
			const done		= (i: number, result: PromiseSettledResult<U>) => {
				results[i] = result;
				if (--remaining === 0)
					resolve(results);
			};
			if (remaining === 0)
				resolve(results);
			values.forEach((value, i) => Promise.resolve(value).then(v => done(i, { status: 'fulfilled', value: v }), r => done(i, { status: 'rejected', reason: r })));
		});
	}

	static race<U>(values: readonly (U | PromiseLike<U>)[]): Promise<U> {
		return new Promise<U>((resolve, reject) => values.forEach(value => Promise.resolve(value).then(resolve, reject)));
	}

	static any<U>(values: readonly (U | PromiseLike<U>)[]): Promise<U> {
		return new Promise<U>((resolve, reject) => {
			const errors	= new Array<any>(values.length);
			let remaining	= values.length;
			if (remaining === 0)
				reject(new AggregateError(errors, 'All promises were rejected'));
			values.forEach((value, i) => Promise.resolve(value).then(resolve, r => {
				errors[i] = r;
				if (--remaining === 0)
					reject(new AggregateError(errors, 'All promises were rejected'));
			}));
		});
	}
}

// An async function's result, settled by the code `compileAsyncFunc` emits.
export function __asyncResult<T>(): Promise<T> {
	return new Promise<T>(() => {});
}
