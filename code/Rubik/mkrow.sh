#!/bin/sh
# =========================================================================
#  Build the row and nothing else.
#
#    ./mkrow.sh        with the job count of the machine
#    ./mkrow.sh 18     with eighteen workers
#
#  `make' on this directory builds _CoqProject, and _CoqProject holds the
#  seventeen Runp1 pieces -- the depth nineteen search, 87 CPU-hours, which
#  is the lower bound's certificate and not something to run while working.
#  This builds the row's own chain and its tables, and stops.
#
#  The tables are the slow part: RowTabP.v is 5.4 MB of list and the checks
#  over 40320 ranks are vm_computes.  ulimit -s unlimited is not optional --
#  a list that long overflows the stack without it.
# =========================================================================
set -e
cd "$(dirname "$0")"
ulimit -s unlimited
JOBS=${1:-$(nproc)}
[ -f Makefile ] || rocq makefile -f _CoqProject -o Makefile
make -j"$JOBS" Row.vo RowMap.vo RowRun.vo RowFinal.vo RowInst.vo \
                RowTabL.vo RowTabP.vo RowTab.vo RowDummy.vo
echo "the row is built; the four checks in RowTab.v passed"
