#!/bin/sh
# The check of the whole archive of Paul's k = 9, l = 6 tables.
# Usage: ./fullrun.sh [J] [ARCHIVE]
#   J        number of parallel workers (default 20)
#   ARCHIVE  a tar.bz2 of in* files; by default the five parts
#            archive/tables0..4.tar.bz2 of the repository (checked against
#            archive/SHA256SUMS), which hold Paul's all.tar.bz2
# It unpacks the tables into tables/, writes Data_N.v and Run_N.v for every
# file (mksample.sh), runs them all (make -jJ sample), then builds
# SampleAll.v: every line of every file satisfies the six conditions.
set -e
J=${1:-20}
ARCH=$2

mkdir -p tables
if [ -z "$ARCH" ]; then
  (cd archive && sha256sum -c SHA256SUMS)
  for P in archive/tables*.tar.bz2; do tar xjf "$P" -C tables; done
else
  tar xjf "$ARCH" -C tables
fi
echo "$(ls tables | wc -l) files, $(cat tables/in* | wc -l) lines"

./mksample.sh tables/in* > mksample.log
make -j"$J" sample
make sample-all
