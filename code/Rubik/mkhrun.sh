#!/bin/sh
# Write the pieces of the quarter-turn run: Reid's six positions, each cut
# into NJ jobs over its 120 two-move prefixes.
#
#   ./mkhrun.sh          six positions, twelve jobs each
#   ./mkhrun.sh 8        eight jobs each
#
# WHY TWELVE AND NOT 120.  Every job loads the whole folded table, MEASURED at
# 4.4 GB, so roquableu's 62 GB holds about twelve of them at once -- and the
# 29 GB flat table must be out of /dev/shm by then.  A job per prefix would
# load the table 120 times to no purpose, so the prefixes are dealt round
# robin instead, exactly as the prototype deals them.
#
# The depths are Reid's: position 0 through 22 quarter turns and the other
# five through 21, less the two moves of the prefix.
cd "$(dirname "$0")"

NJ=${1:-12}
case "$NJ" in ''|*[!0-9]*) echo "usage: ./mkhrun.sh [jobs]" >&2; exit 1;; esac
[ "$NJ" -ge 1 ] || { echo "jobs must be at least one" >&2; exit 1; }

# WRITE ONLY WHAT CHANGED: a file rewritten with the same content still gets a
# new mtime, and make reads that as a search to run again.
replace () {
  if [ -f "$2" ] && cmp -s "$1" "$2"; then rm -f "$1"; return 1; fi
  mv "$1" "$2"
}

changed=0
k=0
while [ "$k" -lt 6 ]; do
  if [ "$k" = 0 ]; then D=20; else D=19; fi
  j=0
  while [ "$j" -lt "$NJ" ]; do
    n=$(printf "%d_%02d" "$k" "$j")
    nw=$(( (120 - j + NJ - 1) / NJ ))
    sed -e "s/@N@/$n/g" -e "s/@K@/$k/g" -e "s/@D@/$D/g" \
        -e "s/@J@/$j/g" -e "s/@NJ@/$NJ/g" -e "s/@NW@/$nw/g" \
        HRun_task.v.in > "HRun_$n.v.new"
    replace "HRun_$n.v.new" "HRun_$n.v" && changed=$((changed + 1))
    j=$((j + 1))
  done
  k=$((k + 1))
done

echo "$((6 * NJ)) pieces, $changed rewritten"
echo "run them with, say:"
echo "  ls HRun_*.v | xargs -P 12 -I{} rocq compile -R . Rubik {}"
