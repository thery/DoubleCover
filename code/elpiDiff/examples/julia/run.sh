#!/bin/sh
# run.sh [--passive F:X,G:Y,…] [FILE.jl]: differentiates the Julia functions of FILE (default
# functions.jl) in tangent and adjoint mode, from Julia to Julia:
#   FILE.jl → Julia's AST (tools/julia2elpi.jl) → L0 in Elpi (jlfront.elpi): out/primal.elpi
#          → the passes of the tool → L2′ → Julia (julia.elpi): out/tangent.jl, out/adjoint.jl
# then, for functions.jl, runs them against finite differences and the
# dot-product test (tools/juliatest.jl). Needs julia (with StaticArrays) and elpi.
# --passive F:X,… makes the argument X of the function F passive (not
# differentiated; F as in the source, the trailing ! optional): it adds the
# facts `jl-passive "F" "X"` to the AST. OUT=dir writes into dir instead of out.
set -e
PASSIVE=
if [ "$1" = --passive ]; then PASSIVE=$2; shift 2; fi
cd "$(dirname "$0")"
CODE=../..
SRC=${1:-functions.jl}
JULIA=${JULIA:-julia}
OUT=${OUT:-out}
mkdir -p $OUT

$JULIA $CODE/tools/julia2elpi.jl $SRC > $OUT/ast.elpi
for p in $(echo "$PASSIVE" | tr ',' ' '); do
  case $p in *:*) ;; *) echo "--passive: $p is not F:X"; exit 1;; esac
  echo "jl-passive \"${p%%:*}\" \"${p#*:}\"." >> $OUT/ast.elpi
done
elpi -I $CODE/elpi -I $OUT $CODE/elpi/front/jlfront.elpi -exec jl-to-l0 -- examples/julia/$SRC > $OUT/front.log 2>&1 \
  || { grep -A1 "Fatal error" $OUT/front.log | tail -1; exit 1; }
sed -n '/^% .* in L0/,/^Success/p' $OUT/front.log | grep -v '^Success' > $OUT/primal.elpi
echo "L0: $OUT/primal.elpi"

for m in tangent adjoint; do
  elpi -I $CODE/elpi $OUT/primal.elpi -exec to-julia -- examples/julia $m $OUT > $OUT/$m.log 2>&1 \
    || { grep -v '^$' $OUT/$m.log | tail -5; exit 1; }
  echo "$m: $OUT/$m.jl"
  [ -f $OUT/diagnostics.txt ] && cat $OUT/diagnostics.txt
done

if [ "$SRC" = functions.jl ]; then
  $JULIA $CODE/tools/juliatest.jl $SRC $OUT "$PASSIVE"
fi
