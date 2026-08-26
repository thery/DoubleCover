#!/bin/sh
# =========================================================================
#  The row to each depth, timed, one process per depth, all at once.
#
#    ./mkrowdepth.sh cut   10 11 12 13 14
#    ./mkrowdepth.sh climb 10 11 12 13
#
#  cut   -- RowFoldCut.v, with hcoset's last two cuts
#  climb -- RowFoldClimb.v, without them
#
#  One Eval gives one answer, so a per depth timing needs a per depth run,
#  and each redoes every level below its own.  That is the price of having
#  the numbers side by side instead of one after another.
#
#  EACH ONE SITS AT ABOUT 15 GB, measured, and flat.  Five together is
#  about 77, so look at `free -g' before asking for more.
#
#  It writes RowFoldD<n>.v and depth<n>.log.  Both are generated and are
#  not checked in.
#
#  THE COUNTS ARE THE CHECK.  The prototype's, for the superflip's row:
#    10  2 560     12  1 192 960     14    148 423 860
#    11 72 832     13 14 731 320     15  1 173 663 208
# =========================================================================
set -e
cd "$(dirname "$0")"
ulimit -s unlimited

case "$1" in
  cut)   src=RowFoldCut.v;   run='frunc @N@ 0 0%uint63 (mkempty tt) (mkempty tt) [::]' ;;
  climb) src=RowFoldClimb.v; run='frunl @N@ 0 (mkempty tt) (mkempty tt) [::]' ;;
  *) echo "usage: ./mkrowdepth.sh <cut|climb> <depth> [<depth> ...]"; exit 1 ;;
esac
shift
[ $# -gt 0 ] || { echo "usage: ./mkrowdepth.sh <cut|climb> <depth> ..."; exit 1; }

for n in "$@"; do
  f=RowFoldD$n
  sed '/^Time Eval native_compute in/d' $src > $f.v
  echo "Time Eval native_compute in $(echo "$run" | sed "s/@N@/$n/")." >> $f.v
  echo "--- depth $n -> depth$n.log"
  ( /usr/bin/time -f "depth $n: %e s wall, %M KB" \
      coqc -R . Rubik $f.v > depth$n.log 2>&1
    echo "depth $n done" ) &
done
wait
echo "all done; grep for the counts in depth*.log"
