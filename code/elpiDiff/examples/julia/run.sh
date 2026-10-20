#!/bin/sh
# run.sh [FILE.jl]: differentiates the Julia functions of FILE (default
# functions.jl) in tangent and adjoint mode, from Julia to Julia:
#   FILE.jl → Julia's AST (tools/julia2elpi.jl) → L0 in Elpi (jlfront.elpi): out/primal.elpi
#          → the passes of the tool → L2′ → Julia (julia.elpi): out/tangent.jl, out/adjoint.jl
# then, for functions.jl, runs them against finite differences and the
# dot-product test (tools/juliatest.jl). Needs julia (with StaticArrays) and elpi.
set -e
cd "$(dirname "$0")"
CODE=../..
SRC=${1:-functions.jl}
JULIA=${JULIA:-julia}
mkdir -p out

$JULIA $CODE/tools/julia2elpi.jl $SRC > out/ast.elpi
elpi -I $CODE -I out $CODE/jlfront.elpi -exec jl-to-l0 -- examples/julia/$SRC > out/front.log 2>&1 \
  || { grep -A1 "Fatal error" out/front.log | tail -1; exit 1; }
sed -n '/^% .* in L0/,/^Success/p' out/front.log | grep -v '^Success' > out/primal.elpi
echo "L0: out/primal.elpi"

for m in tangent adjoint; do
  elpi -I $CODE out/primal.elpi -exec to-julia -- examples/julia $m out > out/$m.log 2>&1 \
    || { grep -v '^$' out/$m.log | tail -5; exit 1; }
  echo "$m: out/$m.jl"
  [ -f out/diagnostics.txt ] && cat out/diagnostics.txt
done

if [ "$SRC" = functions.jl ]; then
  $JULIA $CODE/tools/juliatest.jl $SRC out
fi
