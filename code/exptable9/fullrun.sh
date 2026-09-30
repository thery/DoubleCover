#!/bin/sh
# The check of the whole archive of Paul's k = 9, l = 6 tables.
# Usage: ./fullrun.sh ARCHIVE [J]
#   ARCHIVE  all.tar.bz2 (its sha256 is checked), or any tar.bz2 of in* files
#   J        number of parallel workers (default 20)
# It unpacks the archive into tables/, writes Data_N.v and Run_N.v for every
# file (mksample.sh), runs them all (make -jJ sample), then builds
# SampleAll.v: every line of every file satisfies the six conditions.
set -e
ARCH=$1
J=${2:-20}
[ -f "$ARCH" ] || { echo "usage: $0 archive.tar.bz2 [jobs]"; exit 1; }

# The archive Paul sent, all 687184 lines.
SUM=f509e74ec47064ede889eea481decf2a8f8f7a57fcba875796bd17413e58b85e
if [ "$(basename "$ARCH")" = all.tar.bz2 ]; then
  echo "$SUM  $ARCH" | sha256sum -c
fi

mkdir -p tables
tar xjf "$ARCH" -C tables
echo "$(ls tables | wc -l) files, $(cat tables/in* | wc -l) lines"

./mksample.sh tables/in* > mksample.log
make -j"$J" sample
make sample-all
