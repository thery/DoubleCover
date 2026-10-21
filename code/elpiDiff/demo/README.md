# elpiDiff in the browser (Julia demo)

A static web page: write a small Julia function and get the Julia code of its
derivative in tangent and/or adjoint-value mode (the adjoint that also returns the value: a forward sweep recording on a tape only what the reverse sweep needs, then the reverse sweep), produced by elpiDiff running in the
browser. There is no server and no numerical evaluation.

```
Julia text (textarea)
   │  tree-sitter-julia (wasm) + jlparse.js        same facts as tools/julia2elpi.jl
   ▼
jl-function facts ──► jlfront.elpi (jl-to-l0) ──► L0 ──► adjudge.elpi + jsdrive.elpi (js-to-julia)
                       Elpi 3.7.3 compiled to wasm (wasm_of_ocaml), sources compiled once at load
   ▼
tangent / adjoint Julia code; jlfront's refusals and the tool's diagnostics, as messages
```

## Choosing the arguments to differentiate

300 ms after each edit, the page lists the arguments of every function under
the program, with a checkbox: checked (differentiated) by default for a real
or an array, greyed with the reason for an `Int`, a `Bool`, an array the
function writes, or an unsupported type. On Differentiate, each unchecked box
adds the fact `jl-passive "F" "X"` to the AST facts, as
`examples/julia/run.sh --passive F:X` does (see
[../examples/julia](../examples/julia/README.md#choosing-the-arguments-to-differentiate)).
When the code changes, the list is rebuilt and keeps the choice of every
argument whose function and name did not change; a new name starts checked.

## Files

Sources (written for the demo):

| file | role |
|---|---|
| `index.html` | the page (layout, light and dark styles, header with the conventions) |
| `app.js` | UI: loading, examples menu, the arguments to differentiate, Differentiate, panels |
| `jlparse.js` | tree-sitter CST → the Elpi terms of `tools/julia2elpi.jl` (`j`, `jsym`, `jint`, `jfloat`, `jbool`, `jother`) |
| `pipeline.js` | facts → L0 → tangent/adjoint, on the Elpi JS API (shared by the page and the node tests); the arguments of each function (`argumentsOf`) and the `jl-passive` facts of a choice |
| `examples.js` | the examples menu (from `examples/julia/functions.jl`, plus a refused `while`) |
| `elpi/demo.elpi` | the program compiled at load: `accumulate jlfront. accumulate jsdrive.` |
| `elpi/ast.elpi` | empty: jlfront accumulates it; the facts are added per click as a new unit |
| `elpi/jsdrive.elpi` | `js-to-julia`: adjudge's `to-julia`, printing instead of writing files (from the spike) |
| `build.sh`, `package.json`, `package-lock.json` | build |
| `test/` | tests (below); not published |

Copied by `build.sh` (published):

| file | size | gzip -9 |
|---|---:|---:|
| `vendor/tree-sitter-julia.wasm` (tree-sitter-julia 0.23.1) | 6 223 352 | 569 027 |
| `vendor/web-tree-sitter.wasm` (web-tree-sitter 0.26.13) | 201 535 | 80 433 |
| `vendor/web-tree-sitter.js` (source-map line removed) | 153 622 | 31 128 |
| `elpi/elpijs.bc.wasm.assets/code-*.wasm` (Elpi 3.7.3 + driver) | 950 854 | 237 759 |
| `elpi/elpijs.bc.wasm.js` (wasm_of_ocaml loader) | 17 348 | 6 983 |
| `elpi/*.elpi`: 21 files of elpiDiff (jl-ast, jlfront, adjudge and what it accumulates) | 190 k | 54 k |
| `elpi/files.json` (the list the page loads) | 366 | 181 |
| `vendor/LICENSE.*` | 2 k | 1 k |

With the page's own files (36 k raw, 13 k gzip), the whole site is **7.7 MB raw,
0.99 MB gzipped**; the Julia grammar is 80 % of the raw size.

## Building

Versions: OCaml 4.14.2, dune 3.24.2, js_of_ocaml / wasm_of_ocaml 6.4.1 (opam
switch `elpi-js`), binaryen 123 (`wasm-opt`, e.g. `npm install binaryen@123` and its
`node_modules/.bin` on `PATH`), Elpi 3.7.3 (its source is fetched into `ws/elpi-3.7.3` by
`opam source elpi.3.7.3`), node 22, web-tree-sitter 0.26.13
and tree-sitter-julia 0.23.1 (exact versions in `package.json`/`package-lock.json`).

```sh
cd code/elpiDiff/demo
eval $(opam env --switch elpi-js --set-switch)   # OCaml 4.14.2 + js_of_ocaml, wasm_of_ocaml 6.4.1
export PATH=<binaryen>/node_modules/.bin:$PATH
./build.sh
```

`build.sh` runs `npm ci --ignore-scripts` if needed and copies the two tree-sitter
wasm files and `web-tree-sitter.js` into `vendor/`; runs
`dune build --profile release driver/elpijs.bc.wasm.js` in `ws/` (skip with
`SKIP_WASM=1`) and copies the bundle into `elpi/`; copies the elpiDiff sources
into `elpi/` and writes `elpi/files.json`. The page compiles the `.elpi`
sources at load (the spike showed that shipping precompiled units does not pay
off in wasm).

## Serving locally

The page loads its files with `fetch`, so it needs HTTP (not `file://`):

```sh
cd code/elpiDiff/demo && python3 -m http.server 8000
# open http://localhost:8000/
```

## Hosting

Everything is static. For GitHub Pages, publish these files and directories,
keeping the layout: `index.html app.js jlparse.js pipeline.js examples.js
vendor/ elpi/` (not `node_modules/`, `test/`, the build files). The loaders use
`WebAssembly.instantiateStreaming`, so the host must serve `.wasm` as
`application/wasm`: GitHub Pages and `python3 -m http.server` do. Any static host
works the same way; gzip or brotli on `.wasm` cuts the download from 7.7 MB to
about 1 MB.

## Tests

```sh
node test/equiv.mjs        # walker facts vs tools/julia2elpi.jl, and the L0 of native jlfront from both
node test/floatrepr.mjs    # Julia's repr of Float64/Float32 literals vs Julia, 4010 random values
node test/pipeline.cjs     # the page's pipeline under node (wasm) vs the native pipeline (test/native.sh), also with passive arguments
node test/cdp.js           # the page in headless Chrome: load time, examples through the UI, unchecked arguments, phone width, dark mode
```

They need `julia` (`JULIA=`, default `~/.juliaup/bin/julia`), a native `elpi`
3.7.3 on `PATH`, `google-chrome` and `python3` (cdp.js), and `ELPIDIFF` (default: the
parent directory, `code/elpiDiff`). `test/native.sh FILE OUT [PASSIVE]` is
`examples/julia/run.sh [--passive PASSIVE]` writing into `OUT`. (Node prints a
MODULE_TYPELESS_PACKAGE_JSON warning for the ES modules;
`--disable-warning=MODULE_TYPELESS_PACKAGE_JSON` hides it.)

Results (2026-10-20): `equiv.mjs`: all 20 files (functions.jl and 19 cases in
`test/cases`, 9 of them refused and 1 syntax error) give identical facts and the
same L0 or the same refusal; `pipeline.mjs` and `cdp.js`: tangent and adjoint
byte-identical to the native pipeline after the first line (which names the
source), including all of `functions.jl` against `examples/julia/out/`, and with
passive arguments: `pipeline.cjs` on 4 choices over `functions.jl` (2
differentiated, 2 refused with the same reason), `cdp.js` through the checkboxes
(`f` with `x2` unchecked, `advect!` with `c` unchecked, the list kept across
edits, `Int`/`Bool`/written arrays greyed, phone width in light and dark).

## What the walker does not reproduce exactly

The walker rebuilds Julia's `Expr` for everything the front end accepts and
for the usual refused syntax (`while`, tuples, chained comparisons, `&&`/`||`,
keyword and default arguments, `where`, broadcasting, field access, strings,
macros, `->`, `begin`, `local`). Not reproduced exactly, but still refused by
jlfront with a reason:

- `let`, `try`, `do` blocks (`do` is reported as a syntax error), `quote`,
  comprehensions and other constructs it does not know: an expression whose head
  is tree-sitter's name for it;
- string escapes and `$` interpolation are approximate (`jother` text);
- non-decimal float literals (`0x1p3`) beyond the simple form.
