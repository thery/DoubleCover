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
b=$1
shift
t0=$(date +%s)
rocq compile "$@" -R . Rubik "$b.v" || exit 1
echo "$b.v $(( $(date +%s) - t0 )) s" >> fold-timing.log
