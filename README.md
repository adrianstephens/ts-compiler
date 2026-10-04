# @isopodlabs/compiler

Compiler infrastructure built on [`@isopodlabs/tison`](../tison): parsers, a language-neutral middle end and a WebAssembly back end.

```
src/
  vsdg.ts                  language-neutral VSDG middle end (graph, GCM, CSE, folding)
  transpile.ts             source-to-source transpilation between the languages
  wasm/                    codegen.ts (language-neutral wasm emission), wat-parser.ts
  ts/                      TypeScript/JavaScript/JSX: parsers, checker, printer, VSDG dialect,
                           wasm-backend.ts, tsw.ts (the `tsw` CLI), lib/ (the runtime it compiles)
  cpp/                     C, C++, GLSL, HLSL, MSL and Slang: preprocessor, parsers, printer, VSDG dialect, wasm-backend.ts
  py/                      Python: parser, printer, VSDG dialect, wasm-backend.ts
  cg/                      the Cg grammar
```

The shared AST node constructors and walker types live in tison (`@isopodlabs/tison/ast`, `/walker`), so
parser-only consumers don't need this package.

Each language directory owns its parser, walker, printer, VSDG dialect and its back end for a given target
(`<target>-backend.ts`); `wasm/` depends on no language.

## Build and test

`npm run build` (`tsc`, then copies `ts/lib` and marks `tsw` executable); `npm run build:emit` is the
tolerant twin that continues past type errors. The suites in `test/` import the built `dist/`, so build first.
