#!/bin/sh
# =========================================================================
#  The row to one depth, timed -- one process per depth, run together.
#
#    ./mkrowdepth.sh 10 11 12 13 14
#
#  One Eval gives one answer, so a per depth timing needs a per depth run,
#  and each run redoes every level below its own.  That is the price of
#  having the numbers side by side.
#
#  EACH ONE SITS AT ABOUT 15 GB, measured, and flat.  Five together is
#  about 77, so look at `free -g' before asking for more.
#
#  It writes RowFoldD<n>.v from RowFoldClimb.v so there is one source for
#  the instance, and depth<n>.log beside it.  Both are generated: they are
#  not to be checked in.
#
#  THE COUNTS ARE THE CHECK.  The prototype's, for the superflip's row:
#    10  2 560     12  1 192 960     14    148 423 860
#    11 72 832     13 14 731 320     15  1 173 663 208
# =========================================================================
set -e
cd "$(dirname "$0")"
ulimit -s unlimited

[ $# -gt 0 ] || { echo "usage: ./mkrowdepth.sh <depth> [<depth> ...]"; exit 1; }

for n in "$@"; do
  f=RowFoldD$n
  sed '/^Time Eval native_compute in frunl/d' RowFoldClimb.v > $f.v
  echo "Time Eval native_compute in frunl $n 0 (mkempty tt) (mkempty tt) [::]." >> $f.v
  echo "--- depth $n -> depth$n.log"
  ( /usr/bin/time -f "depth $n: %e s wall, %M KB" \
      coqc -R . Rubik $f.v > depth$n.log 2>&1
    echo "depth $n done" ) &
done
wait
echo "all done; the counts are in depth*.log"
