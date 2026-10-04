---
name: tison-hlsl-msl-parsers
description: HLSL and MSL front ends over cpp-parser (src/cpp/hlsl-parser.ts, msl-parser.ts) — what each reuses, the cpp seam changes they needed, the conflicts resolved, and their coverage of Cg/Slang
metadata:
  type: project
---

2026-09-30, following `tison_glsl_parser.md`: added the cpp-based shader front ends.
`src/cpp/hlsl-parser.ts` (264 lines, base cpp-parser) and `src/cpp/msl-parser.ts` (146 lines, base
cpp-parser), with `test/test-hlsl-parser.ts` (252) and `test/test-msl-parser.ts` (227). Same extension
pattern as GLSL-over-c-parser: widen through the seam types, `.push()` new productions onto the base's
exported rule arrays, `makeCachedParser` + `siblingSource` for both ancestors.

**HLSL** (`hlslParser`): registered builtin type names (~250 `float2`/`half4x4`/`Texture2D`/`StructuredBuffer`
spellings + `vector`/`matrix` template heads, so cpp's generic machinery gives `ConstantBuffer<T>`); one
qualifier terminal (`in/out/inout/uniform/precise/groupshared/shared/row_major/column_major/snorm/unorm/
nointerpolation/linear/centroid/sample/noperspective/globallycoherent`); `:` annotations
(`SV_Target`, `register(b0, space0)`, `packoffset(c0.x)`) on struct members, parameters, init-declarators and
function returns; `cbuffer`/`tbuffer` blocks; `[numthreads(8,8,1)]` attribute wrappers; `discard`.
**Cg and Slang ride this grammar for their shader-language core**; Cg FX (`technique`/`pass`/`sampler_state`)
and Slang's `interface`/`associatedtype` are NOT included (full Cg FX already lives in the standalone,
own-AST `src/cg/grammar.ts`).

**MSL** (`mslParser`): address-space/stage qualifiers (`device/constant/thread/threadgroup/ray_data/
object_data`, `vertex/fragment/kernel`, which are leading specifier qualifiers, so `vertex float4 main0(...)`
is just a qualified specifier list); MSL types (`halfN`/`packed_floatN`/`floatNxM`/`texture2d`/`depth2d`/
`vec`/`matrix`/`array`/`sampler`/`atomic`); qualified names as types and values (`access::read`,
`mem_flags::mem_threadgroup`, `metal::float4`); a half-literal terminal (`1.0h`). **`[[...]]` attributes need
no grammar at all** — cpp-parser.ts's lexer already skips them, so `float4 pos [[attribute(0)]];` parses as
`float4 pos ;` and leaves no AST trace (same trade cpp makes for `[[nodiscard]]`).

**Three cpp-parser.ts seam changes** (all backward-compatible; +23/-14):
1. **`Definition<S = Stmt>` is now generic in the statement seam**, and `NamespaceDecl`/`LinkageSpec`/
   `TemplateDecl` with it. cpp's top-level union has non-generic additions (`OutOfClassMethod`, ...), so a
   further extension cannot re-instantiate it by hand without near-copying that list; the type parameter is
   the general fix (the same role `S` plays in c-parser's `Definition<D,X,E,S>`). HLSL uses it for
   `Definition = CPP.Definition<Stmt> | ...` with `Stmt = CPP.Stmt | {type:'discard'}`.
2. **`skip`, `scope_prefix`, `RIGHT_SHIFT`, `RIGHT_SHIFT_ASSIGN` are exported.** The first two so an
   extension reuses rather than copies them (MSL's `access::read` needs `scope_prefix`); the `>>`/`>>=`
   terminals must be re-declared by name in every grammar that reuses cpp's template rules, or
   `Box<Box<int>>` mis-lexes — exporting cpp's own is the only way to get the templateDepth callback.
3. (Type-only, no runtime change.) No c-parser/`ArrayDecl` change was needed here: HLSL/MSL add no new
   expression forms, so their array sizes are already cpp expressions and the base-typed call suffices. An
   attempt to thread cpp's `ExprAdditions` into `Declarator`'s array-size seam was reverted — it broke
   `src/cpp/walker.ts` for no gain.

**Two conflicts/gaps hit and how they were resolved:**
- **HLSL semantics collide with C++ bitfields.** A struct semantic (`float4 pos : POSITION;`) is the token
  sequence `IDENT ':' IDENT`, exactly c-parser's bitfield form (`IDENT ':' constant_expression`), so
  `removeRules` drops the bitfield alternatives first (HLSL has none). Same head-time reasoning as cpp's own
  `removeRules` calls.
- **MSL `access::read` and `mem_flags::mem_threadgroup`.** cpp only reaches qualified names via
  `scope_prefix TYPE_NAME` (types) or inside template arguments; MSL needs an IDENT tail as a type and a
  qualified value in expression position. The MSL parser pushes `[CPP.scope_prefix, C.IDENT]` onto
  `specifier_qualifier_list` and both `scope_prefix` forms onto `primary_expression` — safe because
  `TYPE_SCOPE` exists only where the source has `::`.
- MSL half literals (`1.0h`) got their own terminal; c-parser's FLOAT_LITERAL only knows `f`/`l`.

**Verification:** `test-hlsl-parser.ts` 5 samples + 2 isolation checks, `test-msl-parser.ts` 5 + 2, both exit
non-zero on failure. Regressions all green: `test-c-parser` clean, `test-glsl-parser` 7/7,
`test-vsdg-cpp` 0 failures, `test-cpp-backend` all passed, `test-cpp-parser` corpus failures **744**
(unchanged). src total 47,948 (+410 new parser files, +9 net cpp-parser).

**Load order (deferred by the user, still real):** c-parser → cpp-parser → {glsl, hlsl, msl}, and any two
shader extensions cannot share a process without contamination — all mutate c-parser's/cpp-parser's shared
rule arrays. Each test file loads exactly one. The fix (runtime `add()`/`remove()` like jsx-parser, or a
parameterized grammar builder) is the same work item noted in `tison_glsl_parser.md`.
