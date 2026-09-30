---
name: tison-representation-table
description: "which wasm representations are valid for which TS types, and WHO decides -- the backend alone, never a checker stamp (the user, 2026-09-22); read with tison-type-vs-representation and tison-checker-type-stamps"
metadata:
  type: project
---

Read from the code at `36a419c`: `builtinTypes` (backend.ts ~647), `wasmTypeOf`, `typeOfUncached`,
`W.intType`/`elementKind`/`combineUnion`, `Types.nullable`/`box`/`array`, `collectRangeWidenings`, `ownsLayout`.

**A stamp is a TYPE. A representation is the BACKEND's choice** (the user, 2026-09-22) -- nothing about it is
stamped, and codegen keeps the freedom to pick a simpler one (`i32` for an integer-range `number`, raw storage
instead of `Array<T>`) with conversions only where they are really needed. See [[tison-type-vs-representation]].

## Valid representations per type

| TS type | canonical | also valid (who/when) | notes |
|---|---|---|---|
| `number` | `f64` | `i32`/`u32` (`W.intType` from a range/integer-literal type, a `let`'s flow hull (`d.flowType`, the checker's record of every stamped read and write; backend `slotType` names it `i32`/`u32`)); `i64`/`u64`/`f32` via a pseudo-type annotation (`i32`…`f64`, `WASM_PSEUDO_TYPES`); box `{typeIndex, primKind}` when nullable; `REF_ANY` in an `any` slot | a boxed `number` must be the f64 box -- `ensureAnyField`'s `canonicalOf` re-boxes an `i32` field, or the reader's cast traps |
| `boolean` | `i32` | box `{primKind:'i32'}` when nullable; `REF_ANY` boxed | |
| `string` | `{arr:'i16'}` | **INTENDED, not implemented**: a `u32` offset into the module's passive data segment (with its length), materialised to `{arr:'i16'}` only where an operation needs the array | `data.intern(s)` already returns that offset, but `emitStringConst` materialises eagerly at every use; the `String` class owns its methods but has no struct (`typeIndex` -1) |
| `bigint` | `{arr:'i32'}` magnitude array | **INTENDED, not implemented**: `i32`/`u32`/`i64`/`u64` for a value that provably fits | today `i64`/`u64` are pseudo-types of `number` (`class: 'Number'`), so a bigint as a machine int is not expressible at all |
| `T[]`, `Array<T>`, `ReadonlyArray<T>` | `Array<T>` struct (`{ref}`) owning a `RawArray<T>` field | raw `{arr:kind}` storage where only elements matter; element kind = `W.elementKind(typeOf(T))` -- `f64`/`i32`/`i64`/`f32`, `i8`/`i16` packed, else `'ref'` | `Array<any>` backs every non-scalar element (`ownsLayout`): `Node[]` and `Foo[]` share one physical array |
| tuple | `{arr:'ref'}` | via `tupleArrayOwner`, an `Array` like any other | heterogeneous elements have no single scalar kind |
| `Uint8Array` & co | `TypedArray<T>` class over `{arr:'i8'…}` | the tag (`u8`, `i32`…) decides packing; resolving the tag AS a type loses it | |
| class / interface / object shape | struct `{typeIndex}` | `REF_ANY` when the shape is OPEN (`openShapes`) or reached through `any`; index-signature objects become `Map<string,V>`; a call-signature-only shape becomes a closure | a constructor with an explicit `return` gives a scalar- or array-backed class instead (`typeIndex` -1 for scalar) |
| function type | `{closure}` struct `{code, env, length}` | a named function used as a value gets a zero-capture wrapper | overload sets merge (`mergeOverloadSigs`) or have no representation |
| callable object (`F & {p}`, an interface with a call signature AND members) | a shape (`{ref}`) whose struct EXTENDS the closure struct: `#code`/`#env`/`#length` (immutable, `W.CALLABLE_PREFIX`) then its fields; `ClassInfo.callable` holds the closure wtype | -- | the user chose this, 2026-09-28. Built only where the properties are known at creation: `Object.assign(fn, {k: v})` and a function literal whose target is the type (`emitCallableObject`); a struct cannot gain fields later. Calls go through `closurePart(w)`; `coerceTop` passes it as its closure (a subtype, no instruction). `mergeIntersection` folds a function part into a `call` member |
| union | the members' shared representation when they agree (`W.combineUnion`) | `f64` when every member is scalar-like; else `REF_ANY` (boxed) | nullable-only unions collapse to `nullable(base)` |
| `null`/`undefined` alone | `REF_ANY_NULLABLE` | | |
| `any`, `unknown` | `REF_ANY_NULLABLE` | | `object` is `REF_ANY` (never null) |
| `void` | `'void'` | | function result only -- never a param, local or field; boxed as `any` where a field/param needs one |
| `this` | the owner's representation | | substituted by the backend (`T.substituteThisType`) |
| generic `T` | per instantiation | erased to `any` where the layout does not depend on it (`ownsLayout`: only `number`/`boolean`/`any` and the pseudo-types own a layout) | |

## Where the choice is made today (and what the layer must own)

A binding's representation is decided once, at its declaration (`declareValue`/`addField`/`resolveParam`), and is
what `ctx.lookup(name).wtype` holds. An expression's is whatever `emitExpr` returns. Conversions happen at exactly
one place, `coerceTop(got, ctx, want)`.

The problem is not the choices, it is that they are re-derived: `case 'var_decl'` asks the CHECKER three type
questions to decide a local's representation (a typed array's elements as `number`, a generic method's return,
`tsType ??=`), and the backend stores its own choices as TS types in `ctx.scope` (a range-widened local is declared
`i32`), so a later type query answers with a representation. That is why stamps and queries legitimately disagree
(`number` vs `i32`), and why switching those three queries to stamps took difftest 7 -> 15 unsupported
([[tison-checker-type-stamps]]).

## Intended representations not yet present (the user, 2026-09-22)

Both are ordinary backend choices under the rule above -- a `bigint`/`string` TYPE with a cheaper representation --
and both need the same three things before they are sound, the lesson `ensureAnyField`'s `canonicalOf` already
records: (1) a method call on the cheap form still dispatches to the owning class (`BigInt`/`String`), as a boxed
`number` does for `Number`; (2) `coerceTop` converts both ways at boundaries (widen an `i32` bigint to the magnitude
array, materialise a string offset via `array.new_data`); (3) anything entering an `any` slot is boxed in the type's
ONE canonical form, or the reader's cast traps.

**These are STACK representations, not annotations** (the user's clarification, 2026-09-22). The pseudo-types
(`i32`, `u64`, …) are a separate, existing mechanism: an explicit type that FORCES a slot's representation. What is
missing is the value's own choice as it flows: in `let v: bigint = 1n + 2n`, the operands and the sum can be held as
`u32` and widen to the magnitude array only where they meet `v`'s annotated slot; in `const v = 1n + 2n`, `v` is
typed `bigint` but its binding can simply KEEP the `u32` the expression produced.

- **bigint as `i32`/`u32`/`i64`/`u64`** wherever the value provably fits (literals, a range, the result of an
  operation on such values), widened only at a boundary: an annotated slot, a param/field, a return, an `any` box.
  A reassigned `let` needs a common representation up front, the way `collectRangeWidenings` already picks one for
  a numeric `let`.
- **string as a `u32` data offset** for interned/literal strings: pass-through, comparison and printing can read the
  segment; anything that indexes or mutates materialises first.

## Measured: what "a const keeps its value's representation" needs first (2026-09-22)

Tried, measured, reverted (nothing committed). `case 'var_decl'` already declares the local with what emission
RETURNED (`storage`), so the only change needed is to stop forcing a `want`. Three things came out of it:

1. **`want` is not just a coercion target** -- emitters use it to decide how to BUILD (an array literal's element
   kind, boxing, closure shape). Dropping it: difftest 2133/2213, 4 wrong answers, 76 unsupported.
2. **Only an immutable value may keep a narrower form.** `const a = [1, 2]; a.push(3)` needs the `Array` that owns
   the raw storage; keeping the storage broke push/pop/shift/unshift (4 wrong answers). Scalars are the safe case --
   and are exactly the intended bigint/string cheap forms.
3. **The blocker: canonical boxing.** With `const` scalars keeping `u32`/`i32` (28+26+25+… real cases in the towasm
   suite, each one a conversion avoided), `constTupleLiteral` traps: a `number` must box as the `f64` box whatever
   its physical form, or the reader's cast fails. `emitAs` can canonicalize because it sees the expression and its
   type; `coerceTop` cannot -- it has only physical types. So **boxing must take the value's logical type**
   (`ensureAnyField`'s `canonicalOf` is the same rule, solved locally) before a binding may keep a cheaper form.

Order that follows: canonical boxing by logical type -> `const` keeps its scalar -> bigint/string cheap forms.

## DONE, `cb93636`: canonical boxing, and a const keeps its scalar

`coerceValue(e, got, ctx, want)` is `coerceTop` for a value whose EXPRESSION is known, and every conversion of an
emitted value goes through it; `boxesAsBoolean` (the node's stamp, not `ctx.scope`) decides which box, since `i32`
is both a `boolean` and a compact `number`. `coerceTop` keeps only the physical cases, for helper bodies with no
expression. A `const` holding a scalar then keeps whatever narrower scalar its initializer built -- 332 locals in
the towasm suite (167 `u32`, 140 `i32`), each a conversion avoided. Both limits are measured, not assumed: an
object/array must still meet its declared representation (`pushMutates`), and `want` stays a HINT because emitters
use it to decide how to build. Next: bigint on the stack as `i32`/`u32`/`i64`/`u64`, then string as a data offset.

## DONE, `7f79eeb`+`1f0448e`: bigint as a machine int

A bigint takes an `i32`/`i64` representation wherever the checker PROVED the range fits (`1n + 2n` is `3n`), and
widens to the magnitude array only at a boundary -- no runtime checks: an unprovable value keeps the array, which has
no narrowing conversion and so never reaches a machine-int slot. `W.bigIntType` is SIGNED forms only (the widening
writes a 32-bit value as one two's-complement limb, so a `u32` >= 2^31 reads back negative); literals emit the
constant into any machine-int target; `add`/`sub`/`mul` on two machine-int operands with a proven result emit the
native op; `coerceValue` widens before BOXING, or `typeof x === 'bigint'` reads false (measured).

**A `const` takes its initializer's precise type only where that lands on a SCALAR.** Applied generally it makes
`[1, 2]` a tuple -- a different representation from the widened `number[]` -- and broke 5 cases (copyWithin x2,
async x3); TS widens array/object literals for a `const` too. A `let` always takes the widened type.

**Found, pre-existing, now in backend.ts's gap list:** `const a: any = BigInt(5); Number(a)` traps -- `Number(any)`
picks its conversion statically and casts to the number box, where `a.toString()` dispatches on the runtime type and
works. Verified failing at HEAD before this work. Next intended representation: string as a `u32` data offset.

## SETTLED (user, 2026-09-25): arrays of machine types -- Array is NOT a special case

Do not re-open. `u8[]` IS `Array<u8>` (rawness is NAMED: [[tison-array-identity]]), and its storage is `RawArray<u8>`,
packed `i8` -- a machine-type argument owns a generic class's layout exactly as it would for any class (`ownsLayout`).
A value of another layout reaching such a slot follows the general rules, never an Array rule: a NON-escaping parameter
specializes its callee for the argument's layout (`structuralParams`); an escaping slot OPENS (erasure "B"). A literal is
built AS its slot's storage (`aabbfa8`). Open: an escaping packed-array slot -- opening it traps on the read back
through `any`, whose array dispatch does not know packed instantiations yet. The user's question (`readonly` makes a
copy sound?): only if the parameter also does not escape (a kept copy misses the caller's later writes; `===` differs).
