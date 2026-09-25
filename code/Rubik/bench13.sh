#!/bin/sh
# =========================================================================
#  bench13.sh -- the superflip row to depth thirteen, three programs, ONE core
#
#    CORE=2 HCOSET=/path/to/hcoset ./bench13.sh
#
#  1. hcoset, its search at 13 ("Tests at 13 ... in T")
#  2. the OCaml prototype as committed, and rubik_row_exp's variants:
#     the typed rank, the bit-mask rank, and hcoset's last level
#  3. the Rocq run to 13 (RowRun13.v): the WHOLE run, not the search alone
#
#  Every count at 13 must agree: 19 186 816 solutions, 13 538 360 new,
#  14 731 320 done.  Run it alone on the machine.
# =========================================================================
set -e
CORE=${CORE:-0}
SF="U R2 F B R B2 R U2 L B2 R U' D' R2 F R' L B2 U2 F2"
cd "$(dirname "$0")"
ulimit -s unlimited

if [ -n "$HCOSET" ]; then
  echo "--- hcoset, core $CORE"
  (cd "$(dirname "$HCOSET")" && taskset -c $CORE "$HCOSET" -t 1 -S 13 -d 13 \
     U1R2F1B1R1B2R1U2L1B2R1U3D3R2F1R3L1B2U2F2 | grep "Tests at 13")
fi

cd ocaml
make rubik_row_fold rubik_row_exp
echo "--- OCaml, core $CORE (search at 13)"
line () { grep 'depth 13 :' | sed 's/.*solutions, \([0-9]*\) new, \([0-9]*\) done.*search \([0-9.]*\) s.*/new=\1 done=\2 search=\3 s/'; }
printf "committed:           "; ROWFOLD=1 taskset -c $CORE ./rubik_row_fold 12 13 "$SF" 13 | line
printf "typed rank:          "; ROWFOLD=1 taskset -c $CORE ./rubik_row_exp 12 13 "$SF" 13 | line
printf "+ bit-mask rank:     "; EXP_BITRANK=1 ROWFOLD=1 taskset -c $CORE ./rubik_row_exp 12 13 "$SF" 13 | line
printf "+ last level:        "; EXP_BITRANK=1 EXP_LAST=1 ROWFOLD=1 taskset -c $CORE ./rubik_row_exp 12 13 "$SF" 13 | line
printf "no mark (floor):     "; EXP_LAST=1 EXP_NOMARK=1 ROWFOLD=1 taskset -c $CORE ./rubik_row_exp 12 13 "$SF" 13 | line
cd ..

echo "--- Rocq, core $CORE (the whole run to 13: bitleaf, then the old leaf)"
make RowFoldCubDefB.vo RowFoldCubDefI.vo
taskset -c $CORE coqc -R . Rubik RowRun13.v 2>&1 | grep -v Warning | grep "Finished\|= "
