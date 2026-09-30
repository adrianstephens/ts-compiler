# SCAD port (OpenSCAD parser.y → tison)

`src/examples/scad_parser.ts` is a port of OpenSCAD's `parser.y`; the reference grammar is checked in
beside it as `src/examples/openscad.y` (2011-era, `%expect 0`), the design doc is
`assistant/scad-tison-blueprint.md`, and `test/test-scad-parser.ts` is the acceptance test (run it with
`npx ts-node -T` from the workspace root). Instruments: `assistant/scad-conflicts.ts` (the blueprint's
`%expect 0` gate — prints `parser.tables.conflicts`) and `assistant/scad-snippets.ts` (one-line snippets →
the shape the rules produced).

Public entry point: `parser.parse(code, filename = 'main.scad')`. It builds the `Ctx` itself — bison's
driver owns that (`scope_stack.push(rootfile->scope)` before parsing, pop after), so a caller that only
has source text cannot supply one — and returns the `SourceFile` everything was registered into. Before
2026-09-23 the exported `parser` was the raw `makeParser` handle, which needs a `Ctx`: `parser.parse(code)`
threw `Cannot read properties of undefined (reading 'assignments')`.

## tison mechanisms this port tripped over (all three are recurring traps, not SCAD-specific)

1. **An inline action inside an rhs is numbered as a symbol.** bison's `$<inst>$ = $1` … `$$ = $<inst>2`
   idiom (stash a value in a mid-rule action, read it back after) is `$[1]` in the *following* action —
   `$[2]` is the next real symbol. And the inline action must `return` the value it stashes; one that only
   pushes `scope_stack` yields `undefined` for every module call, so every call site reduced to the child
   statement's value (`';'`, `'{'`, …) instead of a `ModuleInstantiation`. Same numbering as bison: the
   action occupies its own slot. `if_statement` had it right, `module_instantiation` did not.

2. **`WithPrec(rule, PREC.x)` gets its *level* only from `spec.precedence`.** Pass the map to `makeParser`
   (`precedence: PREC`) or every entry keeps `level: undefined`. Two arms carrying the same unlevelled
   entry then compare *equal* rather than ordered, which `setAction` resolves as a **GLR fork**, not an
   error: both branches run their mutating actions against the shared ctx and scope objects, so the result
   is duplicated/garbled (a dangling `else` produced an extra top-level `if` plus a doubled statement
   chain). Give the arms distinct levels (bison's `%nonassoc NO_ELSE` < `%nonassoc TOK_ELSE`) and the
   conflict resolves to a plain shift. tison carries a *terminal's* precedence on the rule that would
   shift it, which is why the else arm itself needs `PREC.else`.

3. **A `Rules` factory whose "empty" alternative is only a comment has no empty production.** The `input`
   rule read `Rules<void>(self => [ /* empty */ Rule([self, 'use', …]), … ])` — the `/* empty */` bison
   alternative next to rule 1 was left as a bare comment, so the start symbol had no way in: state 0 held
   only the skip entries, and the first token reported `Unexpected character 'm' at line 3, col 1.
   Expected: (nothing)` — the tell for "empty production missing", since nothing can ever be shifted.

## OpenSCAD facts, verified against its `src/core/lexer.l`

- `IDSTART [a-zA-Z_$]`, `IDREST [a-zA-Z0-9_]` — `$fs`, `$fn` are ordinary identifiers (`$` is start-only).
- `use`/`include` are keywords ONLY when a `<path>` follows (`use[ \t\r\n]*"<"`); otherwise they fall
  through to the ID rule, so `use = 1;` and `x = include;` are legal. Handled by a `terminal(...)`
  callback returning `ID` (the ts-parser `GET`/`SET` pattern), not by a grammar trick.
- Numbers: `0x{H}+ | {D}+{E} | {D}*\.{D}+{E}? | {D}+\.{D}*{E}? | {D}+` — the *integer* is a separate
  flex alternative, and the port had dropped it (`/[0-9]+\.[0-9]*…/` requires a `.`), so `x = 1;` did not
  lex. Hex (and any binary/octal form) is NOT implemented — blueprint §4 open item 4.
- Strings: C-like escapes (`\n \t \r \\ \"`, plus `\xNN`/`\u{...}` in modern OpenSCAD), so the value is
  decoded in the rule action, not by `JSON.parse` (which is what wat-parser can use, WAT being JSON-ish).
- `TOK_EOT` / `fileEnded` do not exist in the port: it registers includes for a resolver instead of
  splicing tokens, so the lexer's `\x03` marker and the `{ fileEnded = true; }` statement have no analogue
  yet.
