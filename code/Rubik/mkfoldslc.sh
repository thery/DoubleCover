#!/bin/sh
# =========================================================================
#  Regenerate the twenty seven slices of the orbit certificate.
#
#  2187 twists, eighty one to a slice, exactly as the P1Chk slices cut the
#  rank certificate.  Foldrun.v glues them and lists them by name, so if
#  this count changes Foldrun.v has to change with it.
# =========================================================================
cd "$(dirname "$0")"
for j in 0 1 2 3 4 5 6 7 8 9 10 11 12 13 \
         14 15 16 17 18 19 20 21 22 23 24 25 26; do
  n=$(printf "%02d" $j)
  k=$((j * 81))
  sed -e "s/@N@/$n/g" -e "s/@K@/$k/g" Foldslc_task.v.in > "Foldslc_$n.v"
done
