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
  # p1gen is a build product and gitignored, so it is either missing or
  # whatever was built here last.  REBUILD IT IF THE SOURCE IS NEWER: an old
  # binary emits the old set of files and the failure then looks like a
  # missing P1Fold.v three lines further down.
  if [ ! -x bench/p1gen ] || [ bench/p1gen.ml -nt bench/p1gen ] ||
     [ bench/cubedata.ml -nt bench/p1gen ]; then
    echo "building bench/p1gen"
    (cd bench && ocamlfind ocamlopt -package unix -linkpkg \
       cubedata.ml p1gen.ml -o p1gen)
  fi
  (cd bench && ./p1gen 9 emitfold)
  # say what is missing, rather than let rocq report a file it cannot find
  for f in P1Fold.v P1FTable.v P1RTable.v; do
    [ -f "$f" ] || { echo "p1gen did not write $f -- is bench/p1gen current?" >&2
                     exit 1; }
  done
else
  echo "folded tables already emitted, skipping (KEEP=0 to redo)"
fi

# a 40 MB array literal overflows the default stack at parse time
ulimit -s unlimited

# NO NATIVE COMPILER ON THE TABLES.  In a native switch coqc also builds a
# .cmx for every file, and for a 40 MB array literal that dwarfs the .vo.
# Nothing here is ever native_computed -- Foldcert.v and the certificate are
# vm_compute throughout -- so the .cmx would never be loaded.
ROCQ="rocq compile -native-compiler no"

echo "compiling P1Fold.v"
$ROCQ -R . Rubik P1Fold.v

echo "compiling the eight chunks with $JOBS workers"
{ for i in 00 01 02 03 04; do echo "P1F_$i.v"; done
  for i in 00 01 02; do echo "P1R_$i.v"; done; } |
  xargs -P "$JOBS" -I{} $ROCQ -R . Rubik {}

echo "compiling the glue"
$ROCQ -R . Rubik P1FTable.v
$ROCQ -R . Rubik P1RTable.v

# Foldcert.v is the run: the twelve checks at the emitted tables.  It is NOT
# in _CoqProject -- it requires P1Fold and P1RTable, which do not exist until
# the lines above have run, and coqdep would refuse the whole project.
echo "running the twelve checks (Foldcert.v)"
$ROCQ -R . Rubik Foldcert.v
echo "done"
