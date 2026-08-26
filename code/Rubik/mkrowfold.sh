#!/bin/sh
# =========================================================================
#  Build the folded row and run it.
#
#    ./mkrowfold.sh build    build the files and stop
#    ./mkrowfold.sh chk      build, then RowFoldChk -- the numbers
#    ./mkrowfold.sh grow     build, then RowFoldGrow -- the ladder
#    ./mkrowfold.sh why      build, then RowFoldWhy -- where the time goes
#    ./mkrowfold.sh edge     build, then RowFoldEdge -- what one step costs
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

# the phase one fold, and the row's own files, each only if it is stale
for f in Fold FoldTables P1Fdec P1FTable \
         RowFold RowMask RowTabF RowFoldTab RowFoldSrch; do
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
  *)     echo "--- RowFoldRun (the ball of H)";   coqc -R . Rubik RowFoldRun.v ;;
esac
