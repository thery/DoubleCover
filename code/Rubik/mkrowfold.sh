#!/bin/sh
# =========================================================================
#  Build the folded row and run it.
#
#    ./mkrowfold.sh build    build the files and stop
#    ./mkrowfold.sh chk      build, then RowFoldChk -- the numbers
#    ./mkrowfold.sh grow     build, then RowFoldGrow -- the ladder
#    ./mkrowfold.sh why      build, then RowFoldWhy -- where the time goes
#    ./mkrowfold.sh edge     build, then RowFoldEdge -- what one step costs
#    ./mkrowfold.sh mark     build, then RowFoldMark -- what marking costs
#    ./mkrowfold.sh place    build, then RowFoldPlace -- which part of it
#    ./mkrowfold.sh fast     build, then RowFoldFast -- what int63 is worth
#    ./mkrowfold.sh wide     build, then RowFoldWide -- how wide a node is
#    ./mkrowfold.sh okm      build, then RowFoldOkm -- what the move table is worth
#    ./mkrowfold.sh leaf     build, then RowFoldLeaf -- the test at the end
#    ./mkrowfold.sh climb    build, then RowFoldClimb -- the row, both wins in
#    ./mkrowfold.sh cut      build, then RowFoldCut -- with hcoset's last two cuts
#    ./mkrowfold.sh pos      build, then RowFoldPos -- what a smaller position is worth
#    ./mkrowfold.sh cub      build, then RowFoldCub -- the real twenty cubies
#    ./mkrowfold.sh cubrun   build, then RowFoldCubRun -- the row, folded map
#    ./mkrowfold.sh proof    build, then RowFoldCubProof -- THE CERTIFICATE
#    ./mkrowfold.sh t10      build, then RowFoldRun10 -- the proved run, depth 10
#    ./mkrowfold.sh t13      ... depth 13
#    ./mkrowfold.sh t15      ... depth 15  (run the three side by side)
#    ./mkrowfold.sh o10      RowFoldOpt10 -- EVERY optimization on, depth 10
#    ./mkrowfold.sh o13      ... depth 13
#    ./mkrowfold.sh o15      ... depth 15
#    ./mkrowfold.sh o20      ... depth 20  (run the four side by side)
#    ./mkrowfold.sh cubplain build, then RowCubRun -- the row, plain map
#    ./mkrowfold.sh          build, then RowFoldRun -- the ball of H
#
#  RUN chk FIRST.  It says whether the folded row is RIGHT: it must print
#  2560, which is what the prototype has after depth ten.  The ladder only
#  says how fast it is, and a fast wrong answer is worth nothing.
#
#  It does NOT use _CoqProject, for the reason mkrow.sh does not either: that
#  file lists the seventeen Runp1 pieces, which are 87 CPU-hours.
#
#  ulimit -s unlimited is not optional: RowTabF.v is 5.4 MB of list.
#
#  THE ROW MUST BE BUILT FIRST (./mkrow.sh), and the phase one fold too --
#  Fold, FoldTables and P1FTable are built here only if they are missing.
#
#  Measured on gukesh: RowTabF 2 m 10, RowFoldTab 1 m 55, the rest seconds.
# =========================================================================
set -e
cd "$(dirname "$0")"
ulimit -s unlimited

# A target is stale when its .vo is missing, older than its own source, or
# older than the .vo of anything that source requires.  mkfold.sh's test,
# word for word: without it this script recompiled RowTabF -- two minutes of
# list -- on every run, and the whole point of `chk' is to be quick.
prereqs () {   # the .vo of every in-project file that $1 requires
  awk '/Require/, /\.[ \t]*$/ {
         gsub(/^From +[A-Za-z]+ +/, ""); gsub(/Require|Import|Export/, "");
         gsub(/-\(notations\)/, ""); gsub(/\./, " "); print }' "$1" |
  tr ' \t' '\n\n' | grep -v '^$' | sort -u |
  while read m; do [ -f "$m.v" ] && echo "$m.vo"; done
}

stale () {     # stale <base>: does <base>.vo have to be rebuilt?
  if [ ! -f "$1.vo" ]; then return 0; fi
  if [ "$1.v" -nt "$1.vo" ]; then return 0; fi
  for p in $(prereqs "$1.v"); do
    if [ -f "$p" ] && [ "$p" -nt "$1.vo" ]; then return 0; fi
  done
  return 1
}

build () {     # build <base>
  if stale "$1"; then
    echo "--- $1"
    coqc -R . Rubik "$1.v"
  else
    echo "$1.vo is current"
  fi
}

# EVERY in-project file the folded row needs, in dependency order, each only
# if it is stale.  The order is coqdep's; it was hand-written before and was
# missing Sym16Row and the whole RowMembChk chain, which is what made a clean
# tree fail.  A file already current is skipped, so a long one is built only
# when it really is absent.
for f in Fold P1Fold FoldTables P1Fdec P1F_00 P1F_01 P1F_02 P1F_03 P1F_04 \
         P1FTable P1Table Row RowMap Fsinj FsmChk Lehmer RowRun RowFinal \
         RowInst RowTabP RowMemb RowCub RowCubi RowCubInst RowFold Sym16 \
         RowFoldPart RowTabF RowFoldTab RowTabL RowTab RowFoldSym RowMoveH \
         RowPartC RowPartM RowPartU RowLeaf RowUp4ok RowUp8ok RowFoldConj \
         RowFoldOk RowFoldEmpty RowFoldGath RowFoldLvl Sym16Row RowFoldMem \
         RowFoldSrc RowFoldTot RowMoveC RowMoveM RowMoveU RowParity \
         RowMembChk RowFoldWrite RowFoldPorb RowMask RowFoldSrch \
         RowFoldRun RowFoldFinal RowInH RowPar4 RowPar8 RowUp4inv \
         RowUp8inv RowWits RowWitsChk RowReal RowFoldCubReal RowMembi \
         RowOkm; do
  build "$f"
done
echo "the folded row is built"

case "$1" in
  build) exit 0 ;;
  chk)   echo "--- RowFoldChk (must print 2560)"; coqc -R . Rubik RowFoldChk.v ;;
  grow)  echo "--- RowFoldGrow (the ladder)";     coqc -R . Rubik RowFoldGrow.v ;;
  why)   echo "--- RowFoldWhy (where the time goes)"
         coqc -R . Rubik RowFoldWhy.v ;;
  edge)  echo "--- RowFoldEdge (what one step costs)"
         coqc -R . Rubik RowFoldEdge.v ;;
  mark)  echo "--- RowFoldMark (what marking costs)"
         coqc -R . Rubik RowFoldMark.v ;;
  place) echo "--- RowFoldPlace (which part of it)"
         coqc -R . Rubik RowFoldPlace.v ;;
  fast)  echo "--- RowFoldFast (what int63 is worth; must print 71296 twice)"
         coqc -R . Rubik RowFoldFast.v ;;
  wide)  echo "--- RowFoldWide (how many moves a node is offered)"
         coqc -R . Rubik RowFoldWide.v ;;
  okm)   echo "--- RowFoldOkm (the move table; must print 3148501 three times)"
         coqc -R . Rubik RowFoldOkm.v ;;
  leaf)  echo "--- RowFoldLeaf (the end test; must print 1438464 three times)"
         coqc -R . Rubik RowFoldLeaf.v ;;
  climb) echo "--- RowFoldClimb (the row to ten and to thirteen)"
         coqc -R . Rubik RowFoldClimb.v ;;
  cut)   echo "--- RowFoldCut (the last two cuts; 14 must give 148423860)"
         coqc -R . Rubik RowFoldCut.v ;;
  pos)   echo "--- RowFoldPos (the position; must print 1438464 three times)"
         coqc -R . Rubik RowFoldPos.v ;;
  cub)   echo "--- RowFoldCub (the real twenty; must print 1438464 three times)"
         coqc -R . Rubik RowFoldCub.v ;;
  cubrun) echo "--- RowFoldCubRun (the row on the folded map, twenty carried)"
         coqc -R . Rubik RowFoldCubRun.v ;;
  t10)   echo "--- RowFoldRun10 (the proved run to ten, timed)"
         coqc -R . Rubik RowFoldRunT.v; coqc -R . Rubik RowFoldRun10.v ;;
  t13)   echo "--- RowFoldRun13 (the proved run to thirteen, timed)"
         coqc -R . Rubik RowFoldRunT.v; coqc -R . Rubik RowFoldRun13.v ;;
  t15)   echo "--- RowFoldRun15 (the proved run to fifteen, timed)"
         coqc -R . Rubik RowFoldRunT.v; coqc -R . Rubik RowFoldRun15.v ;;
  o10)   echo "--- RowFoldOpt10 (every optimization, depth 10)"
         coqc -R . Rubik RowFoldOptT.v; coqc -R . Rubik RowFoldOpt10.v ;;
  o13)   echo "--- RowFoldOpt13 (every optimization, depth 13)"
         coqc -R . Rubik RowFoldOptT.v; coqc -R . Rubik RowFoldOpt13.v ;;
  o15)   echo "--- RowFoldOpt15 (every optimization, depth 15)"
         coqc -R . Rubik RowFoldOptT.v; coqc -R . Rubik RowFoldOpt15.v ;;
  o20)   echo "--- RowFoldOpt20 (every optimization, depth 20)"
         coqc -R . Rubik RowFoldOptT.v; coqc -R . Rubik RowFoldOpt20.v ;;
  proof) echo "--- RowFoldCubProof (THE CERTIFICATE: must print true)"
         coqc -R . Rubik RowFoldCubReal.v
         coqc -R . Rubik RowFoldCubProof.v ;;
  cubplain) echo "--- RowCubRun (the row on the plain map; must print true)"
         coqc -R . Rubik RowCubRun.v ;;
  *)     echo "--- RowFoldRun (the ball of H)";   coqc -R . Rubik RowFoldRun.v ;;
esac
