---
name: tison-slang-parser
description: Slang front end over hlsl-parser (src/cpp/slang-parser.ts) — interfaces/associatedtype, generics (both syntaxes) + where, extension/typealias/import, let/ref, and the __target_switch label-folding technique
metadata:
  type: project
---

2026-09-30, following `tison_hlsl_msl_parsers.md`: added `src/cpp/slang-parser.ts` (Slang, shader-slang) over
`hlsl-parser.ts`, with `test/test-slang-parser.ts`. Same extension pattern; imports `hlsl-parser` so the
whole chain c → cpp → hlsl is in place before its pushes. **Load order: c → cpp → hlsl → slang.**

**What it adds:** `interface IFoo : IBase { associatedtype T; T get(); }` (the interface name and each
associatedtype register as type names at head-reduce time, so a method's `T` return parses);
`__generic<T : IFoo>` (with optional `typename`/`class` and an optional `where` clause) and the newer
`T f<T>(T x) where T : IFoo` form; `extension T { ... }`, `typealias X = Y;`, `import a.b;`/`import "f";`;
`let` locals (typed and inferred); `ref`/`__ref`/`__constref` parameter qualifiers; `__target_switch`/
`__stage_switch`.

**`interface` is a Definition, not a new `type_specifier`.** That is the decision that keeps this file from
having to re-instantiate cpp's whole `DeclSpec`/`Declarator`/`ParameterDecl` chain just to widen
`TypeSpecifierExt` (chained generic extension cannot widen a union fixed inside cpp). The interface name is
registered and then used as an ordinary type; `associatedtype` members live in a local `InterfaceMember`
union built over cpp's `struct_declaration` (referenced, not pushed onto, so `associatedtype` cannot leak
into ordinary struct bodies).

**`__target_switch` — the real grammar finding.** A target label (`case glsl:`) is the *same token sequence*
as a `switch`'s own `case` statement, so a dedicated `target_case` nonterminal loses the case boundary: LALR
shifts the next `case` into the running body and the whole switch collapses to ONE case (measured: 1 case
with labels `[["glsl"]]` instead of 3). Precedence cannot fix it either -- tison's shift/reduce resolution
defaults to shift when the shift side has no rule precedence, and c-parser's `case` rule cannot be given one
from outside. The fix used: parse the body as a plain `List(C.statement)` (c-parser's `case`/`default`
statements already capture the labels exactly), then fold them back into `TargetCase[]` in the rule action,
walking chained `case`/`default` bodies to merge multiple labels and accumulating non-label statements into
the preceding case's body. Deterministic, and no silent misparse. A nested `switch` is one statement, so its
cases never surface at this level. This "parse with the generic shape, reinterpret in the action" technique
is the general answer for a label that is token-identical to an existing statement form.

**New-style generics (`T f<T>(T x)`) and the lexer's timing.** The return type is lexed *before* `<T>` can
register `T`, so an unregistered return type gets its own `IDENT`-rooted rule that builds
`{type: RefType($[0])}`; the registered case uses `C.declaration_specifiers`. `f<T>(` lexes as cpp's
`TEMPLATE_FN` (its `TEMPLATE_CALL_RE` fires), so the rules start with `TEMPLATE_FN '<'`. The four-way cross
product (empty params × where × definition/prototype) is generated at module load, `as any` on the rhs only
(the same concession cpp makes for generated shapes). Non-type params (`int N`) are a
`specifier_qualifier_list IDENT` form and are deliberately NOT registered as types.

**Omissions (documented in the file):** `__subscript`/`__init` accessor syntax, module-system semantics,
conformance/capability/target-set resolution. `implementing IFoo;` parses as a member, nothing resolves it.
Weight: 356 lines of parser + 306 of test.

**Verification:** `test-slang-parser.ts` 7 samples + 3 isolation checks (cParser rejects Slang; hlsl-parser
and cpp-parser still parse), exit non-zero on failure. Regressions: GLSL/HLSL/MSL tests green, `test-c-parser`
clean, `test-cpp-parser` corpus failures **744** (unchanged).
