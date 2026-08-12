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
# The native step is what eats the machine: ocamlopt -shared on a 40 MB
# literal is about 6.5 GB, MEASURED on roquableu, where seven at once filled
# 64 GB and swapped.  So the .vo files are built with JOBS workers and the
# .cmxs are precompiled with NJOBS, which is small on purpose.
NJOBS=${2:-2}

need=0
[ -f P1Fold.v ] || need=1
for i in 00 01 02 03 04; do [ -f "P1F_$i.v" ] || need=1; done
for i in 00 01 02; do [ -f "P1R_$i.v" ] || need=1; done

if [ "$need" = "1" ] || [ "${KEEP:-1}" = "0" ]; then
  echo "emitting the folded tables"
  # p1gen rewrites EVERY file it emits and this script calls it as soon as
  # ONE of them is missing.  So remember what is here: a file that comes back
  # byte for byte the same gets its old timestamp put back, or its .vo -- and
  # the eight chunks and twelve checks under it -- would be redone for
  # nothing.
  stamp=$(mktemp)
  for f in P1Fold.v P1FTable.v P1RTable.v P1F_[0-9][0-9].v P1R_[0-9][0-9].v; do
    if [ -f "$f" ]; then
      echo "$(md5sum "$f" | cut -d' ' -f1) $(date -r "$f" +%s) $f"
    fi
  done > "$stamp"
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
  kept=0
  while read -r m t f; do
    if [ -f "$f" ] && [ "$(md5sum "$f" | cut -d' ' -f1)" = "$m" ]; then
      touch -d "@$t" "$f"
      kept=$((kept + 1))
    fi
  done < "$stamp"
  rm -f "$stamp"
  echo "  $kept emitted file(s) came back unchanged and kept their date"
else
  echo "folded tables already emitted, skipping (KEEP=0 to redo)"
fi

# a 40 MB array literal overflows the default stack at parse time
ulimit -s unlimited

# ---- what still has to be built ------------------------------------------
# These files are OUT of _CoqProject, so coqdep never sees them and make
# cannot tell what is current.  Without the test below every run of this
# script redid the lot -- the twelve checks alone are the better part of an
# hour -- on a tree where nothing had changed.
#
# A target is stale when its .vo is missing, older than its own source, or
# older than the .vo of anything that source requires.  The requires are read
# off the file, so nothing here has to be kept in step by hand.
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

build () {     # build <base> [extra rocq flags]
  b=$1; shift
  if stale "$b"; then
    echo "compiling $b.v"
    ./rocqtime.sh "$b" "$@"
  else
    echo "$b.vo is current"
  fi
}

build P1Fold

chunks() { for i in 00 01 02 03 04; do echo "P1F_$i"; done
            for i in 00 01 02; do echo "P1R_$i"; done; }

# the `|| :' matters under set -e: the assignment takes the status of the
# loop, and a loop whose last chunk was current ends on a false
todo=$(chunks | while read b; do if stale "$b"; then echo "$b"; fi; done) || :
if [ -z "$todo" ]; then
  echo "the eight chunks are current"
else
  echo "compiling $(echo "$todo" | wc -w) of the eight chunks with $JOBS workers"
  echo "$todo" | xargs -P "$JOBS" -I{} ./rocqtime.sh {} -native-compiler no
fi

# A missing .cmxs is what makes the glue fail, so this has to happen -- but
# it is NOT cheap and rocq does NOT skip the ones that are current: ~6 min a
# chunk, MEASURED on roquableu, which at two at a time is ~24 min, more than
# everything else in the fold together.  So the test is here: a .cmxs newer
# than its .vo is done.
todo=$(chunks | while read b; do
         if [ ! -f ".coq-native/NRubik_$b.cmxs" ] ||
            [ "$b.vo" -nt ".coq-native/NRubik_$b.cmxs" ]; then echo "$b"; fi
       done) || :
if [ -z "$todo" ]; then
  echo "the eight .cmxs are current"
else
  echo "precompiling $(echo "$todo" | wc -w) .cmxs with $NJOBS workers, ~6 min each"
  echo "$todo" | xargs -P "$NJOBS" -I{} ./rocqtime.sh --native {}
fi

build P1FTable
build P1RTable

# The in-project half, and only now: FoldTables.v requires P1Fold, so none of
# these can be built before the lines above have run.  They ARE in
# _CoqProject, so make knows their order; MAKEFLAGS is cleared because this
# script is itself called from a recipe and would otherwise look for the
# parent's jobserver.
# PHASE=tables stops here, with the emitted tables built and nothing else.
# It is what `make timed' wants: everything past this line drags the whole
# project in through FoldChecks -> Farp1 -> P1Fsm, and a file built here is
# a file the timing table never sees.  Run the script again with no PHASE to
# finish; the part above is then a no-op.
if [ "${PHASE:-all}" = tables ]; then
  echo "PHASE=tables: the emitted tables are built, stopping"
  exit 0
fi

echo "the fold's in-project files"
MAKEFLAGS= make -j"$JOBS" FoldTables.vo FoldStabiliser.vo FoldRankCert.vo \
                          FoldChecks.vo FoldAssembly.vo

# FoldChecksRun.v is the run: the twelve checks at the emitted tables.  It is NOT
# in _CoqProject -- it requires P1Fold and P1RTable, which do not exist until
# the lines above have run, and coqdep would refuse the whole project.
echo "the thirteen checks, in three files"
./mkfoldrun.sh
todo=$(for i in 00 01 02; do
         if stale "FoldRun_$i"; then echo "FoldRun_$i"; fi; done) || :
if [ -z "$todo" ]; then
  echo "the thirteen checks are current"
else
  echo "running $(echo "$todo" | wc -w) of them with $JOBS workers"
  echo "$todo" | xargs -P "$JOBS" -I{} ./rocqtime.sh {}
fi
build FoldChecksRun

# The orbit certificate, cut into twenty seven slices of eighty one twists.
# As one file it is a single process and the rank certificate it replaces
# ran nine at a time, so the slices are what puts the wall time back.
echo "generating the twenty seven slices"
./mkfoldorbit.sh
todo=$(for i in 00 01 02 03 04 05 06 07 08 09 10 11 12 13 \
                14 15 16 17 18 19 20 21 22 23 24 25 26; do
         if stale "FoldOrbit_$i"; then echo "FoldOrbit_$i"; fi; done) || :
if [ -z "$todo" ]; then
  echo "the twenty seven certificates are current"
else
  echo "running $(echo "$todo" | wc -w) of them with $JOBS workers"
  echo "$todo" | xargs -P "$JOBS" -I{} ./rocqtime.sh {}
fi

# and the fold at the table: the three slot equations, stabC, and the glue.
# Out of _CoqProject for the same reason as FoldChecksRun.
build FoldAtTable
echo "done"
