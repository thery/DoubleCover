#!/bin/sh
# native.sh FILE.jl OUT [PASSIVE]: the native pipeline of elpiDiff's examples/julia/run.sh
# (julia2elpi.jl, jlfront.elpi with native elpi, to-julia), writing into OUT
# instead of examples/julia/out: OUT/primal.elpi, OUT/tangent.jl, OUT/adjoint.jl,
# OUT/diagnostics.txt, or OUT/refused.txt with jlfront's reason. PASSIVE is
# run.sh's --passive F:X,G:Y,…: the facts jl-passive "F" "X" added to the AST.
set -e
ELPIDIFF=${ELPIDIFF:-$(cd "$(dirname "$0")/../.." && pwd)}
JULIA=${JULIA:-$HOME/.juliaup/bin/julia}
SRC=$1; OUT=$2; PASSIVE=$3
mkdir -p "$OUT"; rm -f "$OUT"/*
$JULIA --startup-file=no $ELPIDIFF/tools/julia2elpi.jl "$SRC" > "$OUT/ast.elpi"
for p in $(echo "$PASSIVE" | tr ',' ' '); do
  echo "jl-passive \"${p%%:*}\" \"${p#*:}\"." >> "$OUT/ast.elpi"
done
if ! elpi -I $ELPIDIFF/elpi -I "$OUT" $ELPIDIFF/elpi/front/jlfront.elpi -exec jl-to-l0 -- examples/julia/$(basename "$SRC") > "$OUT/front.log" 2>&1; then
  sed -n '/Fatal error:/,$p' "$OUT/front.log" | sed '1s/Fatal error: *//' | tr '\n' ' ' | sed 's/ *$//; s/^ *//' > "$OUT/refused.txt"
  exit 0
fi
sed -n '/^% .* in L0/,/^Success/p' "$OUT/front.log" | grep -v '^Success' > "$OUT/primal.elpi"
for m in tangent adjoint; do
  elpi -I $ELPIDIFF/elpi "$OUT/primal.elpi" -exec to-julia -- examples/julia $m "$OUT" > "$OUT/$m.log" 2>&1
done
