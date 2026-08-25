#!/bin/sh
# =========================================================================
#  Build the folded row and run it.
#
#    ./mkrowfold.sh build    build the files and stop
#    ./mkrowfold.sh chk      build, then RowFoldChk -- the numbers
#    ./mkrowfold.sh grow     build, then RowFoldGrow -- the ladder
#    ./mkrowfold.sh          build, then RowFoldRun -- the ball of H
#
#  RUN chk FIRST.  It says whether the folded row is RIGHT: it must print
#  2560, which is what the prototype has after depth ten.  The ladder only
#  says how fast it is, and a fast wrong answer is worth nothing.
#
#  It does NOT use _CoqProject, for the reason mkrow.sh does not either: that
#  file lists the seventeen Runp1 pieces, which are 87 CPU-hours.
#
#  ulimit -s unlimited is not optional: RowTabF.v is 5.4 MB of list.
#
#  THE ROW MUST BE BUILT FIRST (./mkrow.sh), and the phase one fold too --
#  Fold, FoldTables and P1FTable are built here only if they are missing.
#
#  Measured on gukesh: RowTabF 2 m 10, RowFoldTab 1 m 55, the rest seconds.
# =========================================================================
set -e
cd "$(dirname "$0")"
ulimit -s unlimited

# the phase one fold, only if it is not there
for f in Fold FoldTables P1Fdec P1FTable; do
  if [ ! -f "$f.vo" ]; then
    echo "--- $f (missing)"
    coqc -R . Rubik "$f.v"
  fi
done

for f in RowFold RowMask RowTabF RowFoldTab RowFoldSrch; do
  echo "--- $f"
  coqc -R . Rubik "$f.v"
done
echo "the folded row is built"

case "$1" in
  build) exit 0 ;;
  chk)   echo "--- RowFoldChk (must print 2560)"; coqc -R . Rubik RowFoldChk.v ;;
  grow)  echo "--- RowFoldGrow (the ladder)";     coqc -R . Rubik RowFoldGrow.v ;;
  *)     echo "--- RowFoldRun (the ball of H)";   coqc -R . Rubik RowFoldRun.v ;;
esac
