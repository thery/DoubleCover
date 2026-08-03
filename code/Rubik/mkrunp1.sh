#!/bin/sh
# Regenerate the eighteen pieces of the phase 1 search, one per second move,
# both root moves inside -- the same decomposition mkfar.sh uses, so the two
# experiments are comparable piece for piece.
#
# MEMORY: each piece loads the whole phase 1 table, about 8 GB resident.
# Far_??.v loads only fstab and is small, so it parallelises 18 ways; this
# does NOT.  Six at a time on a 62 GB machine, not eighteen.
#   ./mkrunp1.sh          depth 14, vm
#   ./mkrunp1.sh 15       depth 15, vm
#   EVAL=native ./mkrunp1.sh 14    depth 14, native_compute
cd "$(dirname "$0")"
D=${1:-14}
case "$D" in ''|*[!0-9]*) echo "usage: ./mkrunp1.sh [depth]" >&2; exit 1;; esac
[ "$D" -ge 3 ] || { echo "depth must be at least 3" >&2; exit 1; }
R=$((D - 2))
E=${EVAL:-vm}
case "$E" in vm|native) ;; *) echo "EVAL must be vm or native" >&2; exit 1;; esac
for j in 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17; do
  n=$(printf "%02d" $j)
  sed -e "s/@N@/$n/g" -e "s/@J@/$j/g" -e "s/@D@/$R/g" -e "s/@DEPTH@/$D/g" -e "s/@CAST@/$E/g" \
      Runp1_task.v.in > "Runp1_$n.v"
done
echo "wrote Runp1_00.v .. Runp1_17.v at depth $D (root depth $R), $E"
