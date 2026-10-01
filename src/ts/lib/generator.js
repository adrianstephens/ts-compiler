/// <reference path="./lib.d.ts" />
//-----------------------------------------------------------------------------
//	Generator (function*/yield)
//-----------------------------------------------------------------------------
// The 'value'/'done' pair every '.next()' call returns -- a real (named) class, not an anonymous
// object type, so it composes with the ordinary generic-class machinery (`ensureClass`) instead of
// needing the narrower non-generic object-literal-alias path ('ensureObjectShape').
export class IteratorResult {
    value;
    done;
    constructor(value, done) {
        this.value = value;
        this.done = done;
    }
}
// A generator instance is just a named wrapper around its own resumable "step" closure --
// backend.ts's 'compileGeneratorFunc' builds that closure (code + a per-instance frame holding the
// resume state, and every local/param live across a yield) exactly the way an ordinary
// arrow/function-expression closure is built, then constructs 'new Generator(step)' the same way
// any other class gets constructed. 'next()' calling the closure-typed 'step' field is what taught
// 'emitMethodCall' to call a closure through a field, not just a bare local -- a real, general
// capability, not something special-cased to generators.
export class Generator {
    step;
    constructor(step) {
        this.step = step;
    }
    // An omitted argument resumes with `undefined`, as JS does.
    next(v) {
        return this.step(v);
    }
    // A generator is its own iterator.
    [Symbol.iterator]() {
        return this;
    }
}
