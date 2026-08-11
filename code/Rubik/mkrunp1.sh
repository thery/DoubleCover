#!/bin/sh
# Regenerate the eighteen pieces of the phase 1 search, one per second move,
# both root moves inside -- the same decomposition mkfar.sh uses, so the two
# experiments are comparable piece for piece.
#
# MEMORY: each piece loads the whole phase 1 table.  Since the fold that is
# p1ftab and not p1tab, so about 0.85 GB and not 4.15 -- MEASURED at n = 16,
# 8.2 GB across nine workers.  All EIGHTEEN then fit in one wave: say
# `make p1run P1RUN_GB=3', which computes the -j, rather than one of your
# own.  P1RUN_GB=6 gave -j9 and was right for the unfolded table.
#   ./mkrunp1.sh          depth 14, vm
#   ./mkrunp1.sh 15       depth 15, vm
#   EVAL=native ./mkrunp1.sh 14    depth 14, native_compute
cd "$(dirname "$0")"
D=${1:-14}
case "$D" in ''|*[!0-9]*) echo "usage: ./mkrunp1.sh [depth]" >&2; exit 1;; esac
[ "$D" -ge 3 ] || { echo "depth must be at least 3" >&2; exit 1; }
R=$((D - 2))
E=${EVAL:-native}   # native, measured 1.5x on wall for this search
case "$E" in vm|native) ;; *) echo "EVAL must be vm or native" >&2; exit 1;; esac
# WRITE ONLY WHAT CHANGED.  `make test' runs this script every time, and a
# file rewritten with the same content still gets a new mtime, which make
# reads as work to do: rewriting the eighteen pieces re-ran the whole search
# on a tree that was already finished.
replace () {   # replace <candidate> <target>, and say whether it moved
  if [ -f "$2" ] && cmp -s "$1" "$2"; then rm -f "$1"; return 1; fi
  mv "$1" "$2"
}

changed=0
for j in 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17; do
  n=$(printf "%02d" $j)
  sed -e "s/@N@/$n/g" -e "s/@J@/$j/g" -e "s/@D@/$R/g" -e "s/@DEPTH@/$D/g" -e "s/@CAST@/$E/g" \
      Runp1_task.v.in > "Runp1_$n.v.new"
  replace "Runp1_$n.v.new" "Runp1_$n.v" && changed=$((changed + 1))
done

# THE DEPTH LIVES IN TWO PLACES.  Runp1.v's p1depth is what Farp1inst's
# theorem is stated at, and what p1searchd's statement uses through p1droot;
# the eighteen generated files carry the same number independently.  Left
# unsynchronised, ./mkrunp1.sh 19 gives searches at depth 17 and a p1searchd
# still stated at 12, and Farp1inst fails -- AFTER the multi-day run.
grep -q "^Definition p1depth := $D\.$" Runp1.v || {
  sed -i "s/^Definition p1depth := .*/Definition p1depth := $D./" Runp1.v
  grep -q "^Definition p1depth := $D\.$" Runp1.v || {
    echo "failed to set p1depth in Runp1.v" >&2; exit 1; }
  changed=$((changed + 1)); }

# ---- and _CoqProject, or make has no rule for any of them ----------------
# The same step mkp1chk.sh does for its slices.  Without it,
#   make -j9 Runp1_00.vo ... Runp1_17.vo
# stops at `No rule to make target Runp1_01.vo'.
# IN PLACE, where the block already is.  Dropping the lines and appending
# them at the end reorders _CoqProject on every checkout, and a reordered
# _CoqProject is a rewritten one, which is a full coqdep pass.
awk '
  /^Runp1_[0-9]/ {
    if (!seen) { for (j = 0; j < 18; j++) printf "Runp1_%02d.v\n", j; seen = 1 }
    next }
  { print }
  END { if (!seen) for (j = 0; j < 18; j++) printf "Runp1_%02d.v\n", j }
' _CoqProject > _CoqProject.new
replace _CoqProject.new _CoqProject && changed=$((changed + 1))

if [ "$changed" = 0 ]; then
  echo "Runp1_00.v .. Runp1_17.v are already at depth $D (root depth $R), $E"
else
  echo "wrote $changed file(s) for depth $D (root depth $R), $E"
  echo "  the eighteen pieces, Runp1.v's p1depth, and _CoqProject so make has"
  echo "  rules for them -- rebuild Runp1.vo before the pieces"
fi
