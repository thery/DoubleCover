#!/bin/sh
# =========================================================================
#  Build the row and nothing else.
#
#    ./mkrow.sh        with the job count of the machine
#    ./mkrow.sh 18     with eighteen workers
#
#  It does NOT use _CoqProject.  Two reasons: _CoqProject holds the seventeen
#  Runp1 pieces, which are the depth nineteen search and 87 CPU-hours; and it
#  lists files that are EMITTED rather than kept -- HSweep.v, P1Fold.v and
#  the rest -- so `rocq makefile' on it fails outright on a machine where
#  they have not been generated.  This writes its own list of the row's files
#  and builds those.  Everything they depend on is already compiled.
#
#  ulimit -s unlimited is not optional: RowTabP.v is 5.4 MB of list and the
#  stack overflows without it.
# =========================================================================
set -e
cd "$(dirname "$0")"
ulimit -s unlimited
JOBS=${1:-$(nproc)}

{ echo "-R . Rubik"
  echo
  for f in Lehmer Row RowMap RowRun RowFinal Fsinj RowInst \
           RowTabL RowTabP RowTab RowMemb RowLeaf \
           RowMoveH RowMoveM RowParity RowPartM \
           RowPartC RowPartU RowMoveC RowMoveU RowMembChk \
           RowUp8inv RowUp8ok RowUp4inv RowUp4ok RowPar8 RowPar4 \
           RowWits RowWitsChk RowInH RowDummy RowReal \
           RowCub RowCubi RowCubInst RowCubReal; do
    echo "$f.v"
  done
} > _RowProject

rocq makefile -f _RowProject -o Makefile.row
make -f Makefile.row -j"$JOBS"
echo "the row is built"
