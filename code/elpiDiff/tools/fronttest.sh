#!/bin/bash
# fronttest.sh [code dir]: the C++ front end against the hand-written terms.
# For every reference case with a primal.hpp, clang parses it
# (clang2elpi.py), cxxfront.elpi translates it to L0, and the tool generates
# the tangent and adjoint headers from that L0; they must be those generated
# from the hand-written primal.elpi, modulo the names of the generated locals
# (canon.py) and the name of the source in the first line.
CODE=${1:-$(cd $(dirname $0)/.. && pwd)}
CASES=$(dirname ${CASES:-$HOME/claudeExp/elpi/cases})
TOOLS=$(cd $(dirname $0) && pwd)
OUT=$(mktemp -d)
cd $CASES
ok=0; bad=0
for c in cases/*/; do
  c=${c%/}; [ -f $c/primal.hpp ] || continue
  mkdir -p $OUT/$c/front $OUT/$c/hand
  python3 -I $TOOLS/clang2elpi.py $c/primal.hpp > $OUT/$c/front/ast.elpi
  if ! elpi -I $CODE -I $OUT/$c/front $CODE/cxxfront.elpi -exec cxx-to-l0 -- $c/primal.hpp \
       > $OUT/$c/front/out.log 2>&1 || ! grep -q '^Success' $OUT/$c/front/out.log; then
    echo "REFUSED $c: $(grep -A1 "Fatal error" $OUT/$c/front/out.log | tail -1)"; bad=$((bad+1)); continue
  fi
  sed -n '/^% .* in L0/,/^Success/p' $OUT/$c/front/out.log | grep -v '^Success' > $OUT/$c/front/primal.elpi
  if [ ! -f $c/primal.elpi ]; then
    echo "NO TERM $c (translated, but no hand-written primal.elpi to compare with)"; continue; fi
  for m in tangent adjoint; do
    elpi -I $CODE $OUT/$c/front/primal.elpi -exec main -- $c $m $OUT/$c/front > /dev/null 2>&1
    elpi -I $CODE $c/primal.elpi -exec main -- $c $m $OUT/$c/hand > /dev/null 2>&1
    if [ ! -f $OUT/$c/hand/$m.hpp ]; then continue; fi
    if [ -f $OUT/$c/front/$m.hpp ] && diff -q <(python3 $TOOLS/canon.py $OUT/$c/hand/$m.hpp) \
         <(python3 $TOOLS/canon.py $OUT/$c/front/$m.hpp) > /dev/null; then ok=$((ok+1))
    else
      echo "DIFF $c $m"; bad=$((bad+1))
      diff <(grep -v "^ *%" $c/primal.elpi | grep -v '^$') <(grep -v '^ *%' $OUT/$c/front/primal.elpi | grep -v '^$') | head -20
    fi
  done
done
echo "$ok headers identical from clang and from the hand-written terms, $bad problems"
[ -n "$KEEP" ] && echo "kept in $OUT" || rm -rf $OUT
