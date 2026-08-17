#!/bin/sh
# =========================================================================
#  Build the Rocq side of Reid's quarter-turn table: the small tables, then
#  the chunks of the folded one, then the file that gathers the chunks.
#
#    ./mkhtbl.sh          emit what is missing, then compile
#    ./mkhtbl.sh 3 2      three .vo workers, two native workers
#    KEEP=0 ./mkhtbl.sh   emit the chunks again even if they are there
#
#  It needs ocaml/h_fold14.tbl, which `make hfold' writes and which needs
#  the 29 GB table in /dev/shm.  Nothing here reads either of them: a chunk
#  comes from the folded file and the small tables from nothing at all.
#
#  WHAT IT COSTS, measured on roquableu on 17 August 2026.  A chunk is a
#  42 MB literal: 7 min 37 and 8.8 GB to compile, of which almost all is the
#  ocamlopt pass for the .cmxs, and 42.5 MB of .vo.  There are 59 of them, so
#  this is ~7.5 CPU-h, and the memory is why NJOBS is two or three and not
#  eighteen -- three at a time is ~27 GB.  The small tables are 1 min and
#  2.1 GB, once.
# =========================================================================
set -e
cd "$(dirname "$0")"

JOBS=${1:-3}
NJOBS=${2:-2}

# a 42 MB array literal overflows the default stack at parse time
ulimit -s unlimited

# ---- the small tables ----------------------------------------------------
if [ ! -f HTables.v ] || [ "${KEEP:-1}" = "0" ]; then
  echo "emitting HTables.v"
  (cd ocaml && make -s mtabs)
fi

# ---- the chunks of the folded table --------------------------------------
# THE CHUNK COUNT IS NOT WRITTEN DOWN HERE.  The dump prints it, and it is
# read off that: a fold with a different family count would silently leave
# the last chunks out if this script held its own number.
# The probe rewrites HFold_00.v, which would make its .vo look stale and cost
# eight minutes for nothing -- MEASURED.  So its date is put back if the file
# came out byte for byte the same, the trick mkfold.sh uses.
echo "asking the dump how many chunks there are"
if [ -f HFold_00.v ]; then
  m0=$(md5sum HFold_00.v | cut -d' ' -f1); t0=$(date -r HFold_00.v +%s)
else
  m0=; t0=
fi
NCH=$( (cd ocaml && make -s hdump CHUNK=0) 2>&1 >/dev/null |
       sed -n 's/.*, \([0-9]*\) chunks.*/\1/p')
if [ -n "$m0" ] && [ "$(md5sum HFold_00.v | cut -d' ' -f1)" = "$m0" ]; then
  touch -d "@$t0" HFold_00.v
  echo "  HFold_00.v came back unchanged and kept its date"
fi
case "$NCH" in
  ''|*[!0-9]*) echo "the dump did not say how many chunks -- is the fold there?" >&2
               exit 1 ;;
esac
echo "  $NCH chunks"

names() { i=0; while [ "$i" -lt "$NCH" ]; do
            printf 'HFold_%02d\n' "$i"; i=$((i + 1)); done; }

for b in $(names); do
  if [ ! -f "$b.v" ] || [ "${KEEP:-1}" = "0" ]; then
    n=$(echo "$b" | sed 's/HFold_0*//'); n=${n:-0}
    echo "emitting $b.v"
    (cd ocaml && make -s hdump CHUNK="$n")
  fi
done

# ---- compiling ------------------------------------------------------------
# The same two passes as mkfold.sh, and for the same reason: the .vo is cheap
# and the .cmxs is not, so they get different worker counts.  A .cmxs newer
# than its .vo is done, which is the only way to avoid redoing all 59.
stale () {
  [ ! -f "$1.vo" ] || [ "$1.v" -nt "$1.vo" ]
}

todo=$(for b in $(names); do if stale "$b"; then echo "$b"; fi; done) || :
if [ -z "$todo" ]; then
  echo "the $NCH chunks are current"
else
  echo "compiling $(echo "$todo" | wc -w) chunk(s) with $JOBS workers"
  echo "$todo" | xargs -P "$JOBS" -I{} ./rocqtime.sh {} -native-compiler no
fi

todo=$(for b in $(names); do
         if [ ! -f ".coq-native/NRubik_$b.cmxs" ] ||
            [ "$b.vo" -nt ".coq-native/NRubik_$b.cmxs" ]; then echo "$b"; fi
       done) || :
if [ -z "$todo" ]; then
  echo "the $NCH .cmxs are current"
else
  echo "precompiling $(echo "$todo" | wc -w) .cmxs with $NJOBS workers, ~7 min each"
  echo "$todo" | xargs -P "$NJOBS" -I{} ./rocqtime.sh --native {}
fi

# ---- the native side of what HFoldAll requires --------------------------
# HFoldAll takes setl from HSearch, so ITS .cmxs has to be there too, and the
# files above are compiled with the native pass off.  Without this the last
# step fails with "Unbound module NRubik_HSearch" after three hours of
# chunks -- MEASURED, the first time this script was run.
for b in HRoot HCoord HSearch HTables; do
  if [ -f "$b.vo" ] && { [ ! -f ".coq-native/NRubik_$b.cmxs" ] ||
                         [ "$b.vo" -nt ".coq-native/NRubik_$b.cmxs" ]; }; then
    echo "precompiling $b.cmxs"
    ./rocqtime.sh --native "$b"
  fi
done

# ---- the file that gathers the chunks ------------------------------------
# GENERATED, because the number of chunks is the fold's business and not
# this file's.  hfoldall is deliberately NOT evaluated here: the search takes
# it as an argument, so it is built once when a run starts, and evaluating it
# in this file would put a second copy of every chunk in its own .vo.
echo "writing HFoldAll.v"
{
  echo '(* =========================================================================  *)'
  echo '(*  HFoldAll.v -- GENERATED by mkhtbl.sh, do not edit.                        *)'
  echo '(* =========================================================================  *)'
  echo
  echo 'From Stdlib Require Import Uint63.'
  echo 'From Stdlib Require Import -(notations) PArray.'
  echo 'From mathcomp Require Import all_ssreflect.'
  printf 'Require Import Rubik.HSearch'
  for b in $(names); do printf ' Rubik.%s' "$b"; done
  echo '.'
  echo
  echo 'Local Open Scope uint63_scope.'
  echo
  echo "(* the $NCH chunks of the folded table, in order                              *)"
  printf 'Definition hchunks : seq (PArray.array int) :=\n  [::'
  i=0
  for b in $(names); do
    if [ "$i" = 0 ]; then printf ' h_chunk_%02d' "$i"
    else printf ';\n   h_chunk_%02d' "$i"; fi
    i=$((i + 1))
  done
  echo '].'
  echo
  echo 'Definition hfoldall : PArray.array (PArray.array int) :='
  echo "  setl (PArray.make $NCH%uint63 (PArray.make 1%uint63 0%uint63))"
  echo '       0%uint63 hchunks.'
} > HFoldAll.v

if stale HFoldAll; then
  echo "compiling HFoldAll.v"
  ./rocqtime.sh HFoldAll -native-compiler no
fi
if [ ! -f .coq-native/NRubik_HFoldAll.cmxs ] ||
   [ HFoldAll.vo -nt .coq-native/NRubik_HFoldAll.cmxs ]; then
  echo "precompiling HFoldAll.cmxs"
  ./rocqtime.sh --native HFoldAll
fi

echo "done: the table is ready for a run"
