#!/bin/sh
# =========================================================================
#  Build the folded map and run it.
#
#    ./mkrowfold.sh          build the three files, then run RowFoldRun
#    ./mkrowfold.sh build    build them and stop
#
#  It does NOT use _CoqProject, for the same reason mkrow.sh does not: that
#  file lists the seventeen Runp1 pieces, which are the depth nineteen search
#  and 87 CPU-hours.  This builds four files and nothing else.
#
#  ulimit -s unlimited is not optional: RowTabF.v is 5.4 MB of list.
#
#  What it costs, measured on gukesh: RowTabF 2 m 10, RowFoldTab 1 m 55,
#  RowFold seconds.  RowFoldRun is the RUN and its cost is its own -- read
#  the head of that file before starting it.
# =========================================================================
set -e
cd "$(dirname "$0")"
ulimit -s unlimited

for f in RowFold RowTabF RowFoldTab; do
  echo "--- $f"
  coqc -R . Rubik "$f.v"
done
echo "the folded map is built"

if [ "$1" = "build" ]; then exit 0; fi
echo "--- RowFoldRun (the run)"
coqc -R . Rubik RowFoldRun.v
