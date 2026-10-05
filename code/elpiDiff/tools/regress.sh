#!/bin/bash
# regress.sh [code dir]: regenerates every reference case with the code in
# the given directory and compares with the committed outputs, modulo the
# names of the generated locals (canon.py).
CODE=${1:-$(cd $(dirname $0)/.. && pwd)}
CASES=$(dirname ${CASES:-$HOME/claudeExp/elpi/cases})
TOOLS=$(cd $(dirname $0) && pwd)
OUT=$(mktemp -d)
cd $CASES
n=0; bad=0; same=0
for c in cases/*/; do
  c=${c%/}; [ -f $c/primal.elpi ] || continue
  mkdir -p $OUT/$c
  for m in tangent adjoint; do
    if ! elpi -I $CODE $c/primal.elpi -exec main -- $c $m $OUT/$c > $OUT/$c/$m.log 2>&1 || ! grep -q '^Success' $OUT/$c/$m.log || grep -q 'Warning' $OUT/$c/$m.log; then
      echo "FAIL $c $m"; grep -v '^$' $OUT/$c/$m.log | head -15; bad=$((bad+1)); fi
  done
  for f in tangent.hpp adjoint.hpp diagnostics.txt; do
    [ -f $c/$f ] || continue
    if [ ! -f $OUT/$c/$f ]; then echo "MISSING $c/$f"; bad=$((bad+1)); continue; fi
    if cmp -s $c/$f $OUT/$c/$f; then n=$((n+1)); same=$((same+1))
    elif diff -q <(python3 $TOOLS/canon.py $c/$f) <(python3 $TOOLS/canon.py $OUT/$c/$f) >/dev/null; then n=$((n+1))
    else echo "DIFF $c/$f"; diff <(python3 $TOOLS/canon.py $c/$f) <(python3 $TOOLS/canon.py $OUT/$c/$f) | head -10; bad=$((bad+1)); fi
  done
done
echo "$n identical modulo binder names ($same byte for byte), $bad problems"
rm -rf $OUT
