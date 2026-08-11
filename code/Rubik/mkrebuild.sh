#!/bin/sh
# =========================================================================
#  A full rebuild from nothing, timed, at a chosen depth.
#
#      ./mkrebuild.sh 16
#
#  Everything a build wrote goes: the .vo of the whole project AND of the
#  fold's files, which are out of _CoqProject and which `make cleanall'
#  therefore does not know about, the .glob, the native .cmxs, and the two
#  timing logs.  The emitted tables go too and p1gen writes them again.
#
#  WHAT IS KEPT, and why:
#    bench/*.tbl, phase1_cap*.tbl   hours of BFS, and p1gen does not need
#                                   them to emit
#    glob/                          the .glob copied off another machine
#
#  WHAT IT COSTS: the twelve checks are 40 to 60 min, the eight chunks
#  ~1.7 CPU-h, the twenty seven slices 9 min wall at -P 9, and the eighteen
#  searches 1200 s of CPU each at n = 18 (MEASURED, 117 s at n = 17).  With
#  the timing job count at three this is a night, not an afternoon.
# =========================================================================
set -e
cd "$(dirname "$0")"

D=${1:-16}
case "$D" in ''|*[!0-9]*) echo "usage: ./mkrebuild.sh [depth]" >&2; exit 1;; esac

ulimit -s unlimited

echo "== removing what the last build wrote"
# mkrunp1.sh first: `make' cannot so much as run coqdep while a file named
# in _CoqProject is missing, and the eighteen pieces are emitted, not
# tracked.  The `|| :' is for the same reason -- on a tree that has never
# been built there may be others, and the rm below covers what it misses.
./mkrunp1.sh "$D" > /dev/null
make cleanall || :                  # the _CoqProject half
rm -f *.vo *.vos *.vok *.glob *.v.timing .*.aux
rm -rf .coq-native
rm -f fold-timing.log time-of-build*.log

echo "== removing the emitted tables"
# The fold's are named in .gitignore; P1Small.v, P1Fs.v, P1Ts.v are tracked
# and p1gen overwrites them in place, so they are not removed -- a deleted
# tracked file is a worse state to be in than a stale one.
rm -f P1Fold.v P1F_[0-9][0-9].v P1R_[0-9][0-9].v P1FTable.v P1RTable.v
rm -f P1Fsm.v

echo "== rebuilding p1gen and emitting the small tables"
(cd bench && rm -f p1gen &&
   ocamlfind ocamlopt -package unix -linkpkg cubedata.ml p1gen.ml -o p1gen &&
   ./p1gen 9 small)

# THE DUMMY TRAP.  P1Ts.v and P1Fs.v are in git as dummies -- `[:: 0]' --
# so that the development compiles on a machine without the real tables.  A
# run against a dummy is silent and its answer is nonsense.  Test the
# STRUCTURE, not the size.
for f in P1Fsm.v P1Ts.v P1Fs.v; do
  [ -f "$f" ] || { echo "$f was not emitted -- did p1gen 9 small run?" >&2
                   exit 1; }
done
grep -q "^Definition fsm_chunk_02" P1Fsm.v ||
  { echo "P1Fsm.v has no fsm_chunk_02: it is the pre-chunking table" >&2
    exit 1; }
for f in P1Ts.v P1Fs.v; do
  if grep -q ":= \[:: 0\]" "$f"; then
    echo "$f is still the dummy -- p1gen did not overwrite it" >&2
    exit 1
  fi
done

echo "== the timed build at depth $D"
DEPTH=$D exec make timed
