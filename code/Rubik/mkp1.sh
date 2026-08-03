#!/bin/sh
# Build the phase 1 table: 71 chunks of Rocq literals, then P1Table.v.
#
# THIS IS A ROQUABLEU JOB, NOT A DESKTOP ONE.  Projected from chunk 0,
# measured 2026-08-01:
#
#     per chunk   7m26 wall, 12.1 GB peak RSS, 42 MB of .v, 62.8 MB of .vo
#     all 71      8.8 CPU-hours, 2.9 GB of .v, 4.5 GB of .vo
#
# The peak RSS is what bounds JOBS: 12.1 GB per worker means 4 on a 62 GB
# machine, not 24.  Going wider swaps and is slower than going narrower.
#
#   ./mkp1.sh              emit and compile everything, 4 workers
#   JOBS=6 ./mkp1.sh       more workers -- check the RAM first
#   ./mkp1.sh 12 19        only chunks 12 .. 19 (P1Table.v is still written)
#
# Nothing here is required by the rest of the development: Phase1.v takes
# the table as a Section variable and uses p1dummy until this has run.

set -e
JOBS=${JOBS:-4}
cd "$(dirname "$0")"

FIRST=${1:-0}
LAST=${2:-70}

if [ ! -x bench/p1gen ]; then
  echo "building bench/p1gen"
  (cd bench && ocamlfind ocamlopt -package unix -linkpkg \
     cubedata.ml p1gen.ml -o p1gen)
fi

# The BFS is ~2 minutes and 2.1 GB before a single literal is written, and
# the packing self check runs before the write, so a wrong table costs
# minutes rather than hours.
echo "emitting chunks $FIRST .. $LAST"
(cd bench && ./p1gen 9 emit "$FIRST" "$LAST")

# ulimit: a 42 MB list literal overflows the default 8 MB stack at PARSE
# time, long before any proof runs.
ulimit -s unlimited

echo "compiling chunks with $JOBS workers"
seq -w "$FIRST" "$LAST" | xargs -P "$JOBS" -I{} \
  rocq compile -R . Rubik "P1_{}.v"

if [ "$FIRST" = "0" ] && [ "$LAST" = "70" ]; then
  echo "compiling P1Table.v"
  rocq compile -R . Rubik P1Table.v
else
  echo "partial range: P1Table.v not compiled (it needs all 71 chunks)"
fi
