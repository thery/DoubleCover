#!/bin/sh
# =========================================================================
#  Build the folded phase 1 table: the tables p1gen emits, then their
#  chunks compiled.
#
#    ./mkfold.sh          emit if missing, then compile with the job count
#    ./mkfold.sh 4        the same with four workers
#    KEEP=0 ./mkfold.sh   re-emit even if the files are there
#
#  64 430 orbits x 2187 twists = 140 908 410 entries against 2 217 093 120,
#  so five distance chunks and three for the rank under each symmetry,
#  where the unfolded table needs seventy one.
#
#  A chunk is ~40 MB of Rocq and takes about thirteen minutes and 9 GB, so
#  the eight together are about 1.7 CPU-h against 8.8 for the unfolded set.
# =========================================================================
set -e
cd "$(dirname "$0")"

JOBS=${1:-3}

need=0
[ -f P1Fold.v ] || need=1
for i in 00 01 02 03 04; do [ -f "P1F_$i.v" ] || need=1; done
for i in 00 01 02; do [ -f "P1R_$i.v" ] || need=1; done

if [ "$need" = "1" ] || [ "${KEEP:-1}" = "0" ]; then
  echo "emitting the folded tables"
  # p1gen is a build product, so a fresh clone has to make it first
  [ -x bench/p1gen ] ||
    (cd bench && ocamlfind ocamlopt -package unix -linkpkg \
       cubedata.ml p1gen.ml -o p1gen)
  (cd bench && ./p1gen 9 emitfold)
else
  echo "folded tables already emitted, skipping (KEEP=0 to redo)"
fi

# a 40 MB array literal overflows the default stack at parse time
ulimit -s unlimited

echo "compiling P1Fold.v"
rocq compile -R . Rubik P1Fold.v

echo "compiling the eight chunks with $JOBS workers"
{ for i in 00 01 02 03 04; do echo "P1F_$i.v"; done
  for i in 00 01 02; do echo "P1R_$i.v"; done; } |
  xargs -P "$JOBS" -I{} rocq compile -R . Rubik {}

echo "compiling the glue"
rocq compile -R . Rubik P1FTable.v
rocq compile -R . Rubik P1RTable.v

# Foldcert.v is the run: the twelve checks at the emitted tables.  It is NOT
# in _CoqProject -- it requires P1Fold and P1RTable, which do not exist until
# the lines above have run, and coqdep would refuse the whole project.
echo "running the twelve checks (Foldcert.v)"
rocq compile -R . Rubik Foldcert.v
echo "done"
