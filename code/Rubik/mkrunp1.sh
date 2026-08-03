#!/bin/sh
# Regenerate the eighteen pieces of the phase 1 search, one per second move,
# both root moves inside -- the same decomposition mkfar.sh uses, so the two
# experiments are comparable piece for piece.
#
# MEMORY: each piece loads the whole phase 1 table, about 8 GB resident.
# Far_??.v loads only fstab and is small, so it parallelises 18 ways; this
# does NOT.  Six at a time on a 62 GB machine, not eighteen.
cd "$(dirname "$0")"
for j in 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17; do
  n=$(printf "%02d" $j)
  sed -e "s/@N@/$n/g" -e "s/@J@/$j/g" Runp1_task.v.in > "Runp1_$n.v"
done
echo "wrote Runp1_00.v .. Runp1_17.v"
