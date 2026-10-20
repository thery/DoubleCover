#!/bin/sh
# build.sh: assembles the static site in this directory from
#   1. the npm packages web-tree-sitter and tree-sitter-julia (package.json, exact versions) -> vendor/
#   2. the wasm build of Elpi with its JS driver (ws/, dune + wasm_of_ocaml)              -> elpi/elpijs.bc.wasm.js + .assets/
#   3. the Elpi sources: the page's own (elpi-src/) and those of elpiDiff the Julia
#      pipeline needs                                                                       -> elpi/*.elpi + elpi/files.json
# ELPIDIFF: the elpiDiff directory (default: the parent directory). WS: the dune workspace of the driver.
set -e
cd "$(dirname "$0")"
ELPIDIFF=${ELPIDIFF:-..}
WS=${WS:-ws}

# 1. tree-sitter
[ -d node_modules/web-tree-sitter ] || npm ci --ignore-scripts
mkdir -p vendor
cp node_modules/web-tree-sitter/web-tree-sitter.wasm node_modules/tree-sitter-julia/tree-sitter-julia.wasm vendor/
sed '/^\/\/# sourceMappingURL=/d' node_modules/web-tree-sitter/web-tree-sitter.js > vendor/web-tree-sitter.js
cp node_modules/web-tree-sitter/LICENSE vendor/LICENSE.web-tree-sitter
cp node_modules/tree-sitter-julia/LICENSE vendor/LICENSE.tree-sitter-julia

# 2. Elpi in wasm (switch elpi-js; binaryen's wasm-opt on PATH)
if [ -z "$SKIP_WASM" ]; then
  [ -d "$WS/elpi-3.7.3" ] || opam source elpi.3.7.3 --dir "$WS/elpi-3.7.3"
  (cd "$WS" && dune build --profile release driver/elpijs.bc.wasm.js)
fi
mkdir -p elpi
rm -rf elpi/elpijs.bc.wasm.assets
cp "$WS/_build/default/driver/elpijs.bc.wasm.js" elpi/
cp -r "$WS/_build/default/driver/elpijs.bc.wasm.assets" elpi/
chmod -R u+w elpi/elpijs.bc.wasm.js elpi/elpijs.bc.wasm.assets

# 3. elpiDiff: front/jlfront.elpi, adjudge.elpi and what they accumulate
# (paths relative to elpiDiff's elpi/, kept in the site: accumulate uses them)
SRC="front/jl-ast front/jlfront adjudge lang/syntax lang/anf lang/operations lang/well-formed
     analysis/activity analysis/tbr analysis/annotate modes/derivative modes/tangent modes/adjoint
     modes/simplify back/target back/lower back/cxx back/gallina back/julia back/show back/dump"
for f in $SRC; do mkdir -p "elpi/$(dirname $f)"; cp "$ELPIDIFF/elpi/$f.elpi" "elpi/$f.elpi"; done
cp elpi-src/*.elpi elpi/
OWN="demo ast jsdrive"
{ printf '['; sep=''; for f in $OWN $SRC; do printf '%s"%s.elpi"' "$sep" "$f"; sep=', '; done; printf ']\n'; } > elpi/files.json
echo "built: $(du -sh --exclude=node_modules --exclude=test . | cut -f1)"
