#!/bin/sh
# =========================================================================
#  watchmem.sh -- sample the resident set of every process matching a
#  pattern: one line each, the total, the peak, and the swap line.
#
#    ./watchmem.sh                 the count runs (CountReal), every 5 s
#    ./watchmem.sh Runp1_ 30       the eighteen searches, every 30 s
#    ./watchmem.sh P1Chk_ 30       the twenty seven certificate slices
#    ./watchmem.sh P1Table 2       the table being glued
#
#  The largest single process is what P1RUN_GB and P1CHK_GB have to cover;
#  the total is what the RAM has to hold.  Watch the samples before the job
#  exits, not the peak alone.
# =========================================================================

PAT=${1:-CountReal}
INT=${2:-5}

peak=0        # largest single process seen
peaktot=0     # largest total seen
seen=0

while :; do
  snap=$(ps -eo pid=,rss=,etimes=,args= | grep -- "$PAT" | grep -v watchmem | \
         grep -v grep)
  if [ -z "$snap" ]; then
    if [ "$seen" = "1" ]; then
      awk -v p=$peak -v t=$peaktot 'BEGIN{
        printf "--- gone.  peak %.2f GB one process, %.2f GB together\n",
               p/1048576, t/1048576}'
    else
      echo "no process matching '$PAT'"
    fi
    exit 0
  fi
  seen=1

  tot=$(echo "$snap" | awk '{s += $2} END {print s+0}')
  [ "$tot" -gt "$peaktot" ] && peaktot=$tot
  big=$(echo "$snap" | awk 'BEGIN{m=0} {if ($2 > m) m = $2} END {print m+0}')
  [ "$big" -gt "$peak" ] && peak=$big

  date +%H:%M:%S
  echo "$snap" | awk '{printf "   %5.2f GB  t+%-6ss  pid %-8s %s\n",
                              $2/1048576, $3, $1, $NF}'
  echo "$snap" | awk -v p=$peak -v t=$peaktot -v tot=$tot 'END{
    printf "   --- %d procs, %.2f GB now, peak %.2f GB one / %.2f GB together\n",
           NR, tot/1048576, p/1048576, t/1048576}'
  free -g | sed -n '2p;3p'
  sleep "$INT"
done
