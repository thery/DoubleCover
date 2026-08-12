#!/bin/sh
# =========================================================================
#  Compile one file and append its wall time to fold-timing.log.
#
#      ./rocqtime.sh P1Fold                 rocq compile P1Fold.v, timed
#      ./rocqtime.sh P1F_00 -native-compiler no
#
#  The fold's files are out of _CoqProject, so coq_makefile's `pretty-timed'
#  never sees them.  This is how they reach a timing table too.  The log is
#  appended to, never truncated: delete it to start a fresh table.
# =========================================================================
cd "$(dirname "$0")"

# --native times `rocq native-precompile' instead, the step that turns a
# chunk's .vo into a .cmxs.  It is ~6 min a chunk, MEASURED on roquableu --
# more than the whole of the rest of the fold -- and it was the one step
# with no line in the log.
if [ "$1" = "--native" ]; then
  shift
  b=$1
  t0=$(date +%s)
  rocq native-precompile -R . Rubik "$b.vo" || exit 1
  echo "$b.cmxs $(( $(date +%s) - t0 )) s" >> fold-timing.log
  exit 0
fi

b=$1
shift
t0=$(date +%s)
rocq compile "$@" -R . Rubik "$b.v" || exit 1
echo "$b.v $(( $(date +%s) - t0 )) s" >> fold-timing.log
