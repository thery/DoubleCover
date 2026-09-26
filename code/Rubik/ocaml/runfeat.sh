#!/bin/sh
# runfeat.sh -- build the translation and its mkfeat.py variants with the
# flags native_compute uses (-Oclassic), inlining forced, and run each to
# thirteen twice, ALL AT ONCE: one core and about 2 GB a run.  Every count
# must be 14 731 320.
#   ./runfeat.sh <code/Rubik> <generated tables dir> <rowtrans_consts.txt>
set -e
cd "$(dirname "$0")"
R=${1:-..}; G=${2:-..}; C=${3:-../rowtrans_consts.txt}
FLAGS=${FLAGS:--Oclassic -inline 1000}
python3 mkfeat.py > /dev/null
cp rubik_row_rocq.ml feat/v_base.ml
V="base f1int f2bool f3accu f4type f5case f6arr fall"
for v in $V; do
  ( cd feat && ocamlfind ocamlopt -package unix -linkpkg $FLAGS -w -8 \
      v_$v.ml -o v_$v ) &
done
wait
ulimit -s unlimited
for r in 1 2; do
  for v in $V; do
    ( ./feat/v_$v fold "$R" "$G" "$C" 13 | grep -v "tables built" \
        | tr '\n' ' ' > feat/out_${v}_$r ) &
  done
done
wait
for v in $V; do
  for r in 1 2; do printf "%-8s %s\n" $v "$(cat feat/out_${v}_$r)"; done
done
