---
name: tison-promise-runtime
description: The wasm lib's standard Promise and how async functions drive it (2026-10-03) -- one struct for every Promise<T>, the class layout rule that allows it, and the remaining gaps
metadata:
  type: project
---

`src/ts/lib/promise.ts` is the standard Promise (executor, rejection, chaining, catch/finally, resolve/reject/all/allSettled/race/any),
replacing a non-standard one (`new Promise<T>(initial)` + public `.resolve`). Commits 0ec203b..a824a5a, 2026-10-03.

**One struct for every `Promise<T>`.** A promise routinely reaches code typed for another instantiation (`Promise.all`, `resolve`'s
adoption via `instanceof Promise`), and two instantiations with different layouts cannot convert (a `ref.cast` traps). So the class
stores its value as `any`, and the backend's class-layout rule (`classLayoutParams` in wasm-backend.ts) keys an instantiation only by
the type parameters its STORED fields mention. Every parameter still counts for an unannotated field, a base class, an index signature
or any `__asm` in the body (`RawArray`/`TypedArray` lay out by `T`). An unannotated lib field (`private state = PENDING`) silently
re-splits the layout -- annotate it.

**Async functions** (`compileAsyncFunc`): the result comes from the lib's `__asyncResult<T>()` (instantiated by `instantiateFunc`),
settled through the PRIVATE `adopt` (a returned promise is followed) and `rejectWith`. The step body is wrapped in `emitCatching`, so
anything escaping rejects the result. Every `await` resumes via `then(onFulfilled, onRejected)` trampolines; the rejected one sets the
frame's `threw` flag and the step re-throws the reason on entry (equivalent at the await point because an await inside `try` is
unsupported). A non-promise operand is awaited through a settled promise, so it resumes a tick later, as JS does.

**Why:** the user asked for the Promise to be "fixed" to the standard API. The runtime faithfulness tests read results through a SECOND
exported call: continuations drain when an export returns (`__towasm_exitCall`).

**How to apply:** remaining gaps (in the backend header): a non-Promise thenable is not followed; `finally(f)` does not wait on a
promise `f` returns; and a method call on a value `instanceof`-narrowed to a generic class whose instantiations differ in layout (the
narrowed `C<any>` is not a `C<number>`'s struct). That last one wants a union dispatch over every instantiation, like
`ensureInstanceTest`. Instruments: `assistant/towasm-run.ts` (compile a snippet, call exports in order) and `assistant/test-watdiff.py`
(one test's WAT diff between two suite outputs). Related: [[tison-checker-type-stamps]], [[compiler-size-reduction-plan]].
