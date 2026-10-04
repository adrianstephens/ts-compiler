---
name: tison-glsl-parser
description: GLSL front end over c-parser (src/cpp/glsl-parser.ts) — what it reuses, the two LALR conflicts the extension hit, the ArrayDecl size-seam fix, and the shared-rule load-order caveat
metadata:
  type: project
---

2026-09-30: added `src/cpp/glsl-parser.ts` (319 lines) + `test/test-glsl-parser.ts` (264 lines), a GLSL
(desktop 4.x + ESSL) front end that extends `c-parser.ts` exactly the way `cpp-parser.ts` does: AST widens
through the `X`/`E`/`S`/`R`/`P` seams, new productions are `.push()`ed onto the base's exported rule arrays,
and the parser is built with `makeCachedParser` + `siblingSource(__filename,'c-parser')`. No build-system
change; it is a sibling of cpp-parser, not a dependency of it.

What it adds: builtin type names (`GLSL_BUILTIN_TYPES`, ~140 vec/mat/sampler/image/atomic names) registered
as `ctx.typedefNames` at parse time (reusing c-parser's IDENT callback untouched); four disjoint qualifier
terminals (`in/out/inout/uniform/attribute/varying/buffer/coherent/restrict/readonly/writeonly`,
`smooth/flat/noperspective`, `lowp/mediump/highp`, `invariant/precise/centroid/sample/patch`);
`layout(...)`; head-time `struct` name registration (c-parser's monolithic `struct IDENT {` form removed
with `removeRules`, same call cpp makes — registering at the `}` peek is too late); interface blocks
(`uniform Block { ... } ubo;`); struct-member arrays; constructor/functional casts; zero-arg calls;
empty `for` clauses; `discard`; `precision`; `invariant gl_Position;`; standalone `layout(...) in;`.

**Two LALR conflicts found building it, both from adding a second reading to an existing token:**

1. **A combined qualifier nonterminal is fatal next to interface blocks.** Wrapping the four qualifier
   terminals in a `Rules<GlslQualifier>` nonterminal needs a unit reduction after the terminal; that
   conflicts with `specifier_qualifier_list -> glsl_storage_qualifier interface_block`, which must *shift*
   the next token. tison resolved it toward the block reading, so `layout(...) in vec3 position;` died with
   "Expected: {" at the declarator. Fix: one `Rule([terminal, specifier_qualifier_list], ...)` per qualifier
   terminal, no nonterminal (a loop over `QUALIFIERS`). General lesson: in this engine, never put a
   unit-reduction nonterminal on a token that another alternative shifts from the same state.
2. **A `scalar_type` nonterminal over c-parser's `int/float/double` reduce/reduces against
   `type_specifier -> 'int'`.** It lost the declaration reading and made `int i = 0;` fail with "Expected: (".
   Fix: spell the scalar constructors as the bare keyword terminals c-parser already interns
   (`Rule(['int', '(', ...])`), so the single terminal keeps both readings; `uint`/`bool` are registered type
   names and go through the `TYPE_NAME` constructor rule. A helper (`construct`) is needed because object
   literals returned from a `flatMap` get no contextual type and `type` widens to `string`.

**Base seam change (`c-parser.ts`, type-only, JS identical):** `ArrayDecl<T>` gained an `X` seam
(`size?: TypeSpecifier<X> | Expr<X>`), threaded as the third parameter of `Declarator`/`AbstractDeclarator`.
The old comment declined this ("obscure path, not worth threading"), but a language whose array sizes can
hold its own expression forms needs it. `NoInfer<X>` on the `ArrayDecl` *function*'s size parameter is
load-bearing: without it TS infers `X` from the argument (`TypeSpecifier<never>` is a plain union, so
`ArrayDecl(...)` in c-parser's own rules returns `ArrayDecl<..., TypeSpecifier>` and every
`Rules<AbstractDeclarator>` callback fails to typecheck). With it, `X` comes from the contextual return type
or defaults to `never`.

**Load-order caveat (unchanged from the general extension hazard):** every extension mutates c-parser.ts's
*shared* rule objects in place, so importing glsl-parser and cpp-parser in one process contaminates whichever
builds second. The built `cParser` tables are compiled at c-parser.ts's module load and stay correct
(test asserts cParser still rejects `layout(location=0) in vec3 p;` after glsl-parser loads). Import
order if both are ever needed: c → cpp → glsl. For several shader dialects in one process, prefer
jsx-parser's runtime `add()`/`remove()` or a parameterized grammar builder over more load-time mutation.

**Simplifications (in the file header):** no `float[3] a;` array-type-before-name; `true`/`false` are
identifiers; `shared`/`subroutine`/`packed`/`row_major` left as identifiers so they can head `layout(...)`
items. Parses but does not validate.

**Verification:** `npx ts-node -T test/test-glsl-parser.ts` — 6 shader samples + a cParser-isolation check,
exit code 1 on any failure. `test-cpp-parser.ts` corpus failures 744 (unchanged pre-existing count);
`test-c-parser.ts` clean. src total 47,380 (was 47,061; +319 new file, +4 net c-parser).
