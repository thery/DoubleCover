#!/bin/bash
# numtest.sh [code dir]: generates every case with the code in the given
# directory, then compiles and runs its test.cpp against the generated headers,
# with the stand-in check.hpp of shim/ (tangent and adjoint against dual
# numbers, adjoint against finite differences, dot-product test).
CODE=${1:-$(cd $(dirname $0)/.. && pwd)}
HERE=$(cd $(dirname $0) && pwd)
CASES=$(dirname ${CASES:-$HOME/claudeExp/elpi/cases})
OUT=$(mktemp -d)
cd $CASES
total=0; bad=0
for c in cases/*/; do
  c=${c%/}; [ -f $c/test.cpp ] || continue
  mkdir -p $OUT/$c; cp $c/test.cpp $c/primal.hpp $OUT/$c/
  for m in tangent adjoint; do
    elpi -I $CODE $c/primal.elpi -exec main -- $c $m $OUT/$c > $OUT/$c/$m.log 2>&1
    if ! grep -q '^Success' $OUT/$c/$m.log || grep -q 'Warning' $OUT/$c/$m.log; then echo "GEN FAIL $c $m"; bad=$((bad+1)); fi
  done
  if ! g++ -std=c++20 -Wall -Wextra -Werror -O1 -I $HERE/shim -I $OUT/$c $OUT/$c/test.cpp -o $OUT/$c/test 2> $OUT/$c/cc.log; then
    echo "COMPILE FAIL $c"; grep -E "error" $OUT/$c/cc.log | head -5; bad=$((bad+1)); continue; fi
  r=$($OUT/$c/test); echo "$c: $(echo "$r" | tail -1 | sed 's/^ *//')"
  echo "$r" | grep FAIL | head -3
  echo "$r" | tail -1 | grep -q " 0 failures" || bad=$((bad+1))
done
echo "== $bad problems"
[ -n "$KEEP" ] && echo "kept in $OUT" || rm -rf $OUT
