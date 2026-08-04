#!/bin/sh
# =========================================================================
#  watchmem.sh -- sample a running job's resident set, and report the peak.
#
#    ./watchmem.sh                 watch the count runs (CountReal), every 5 s
#    ./watchmem.sh Runp1_ 10       watch the real searches, every 10 s
#    ./watchmem.sh P1Table 2       watch the table being glued
#
#  THE QUESTION IT ANSWERS.  The resident set of a count run climbs with
#  depth -- 1.6 GB at depth 14, 15.3 GB at depth 16 -- and there are two
#  explanations with very different consequences:
#
#    it PLATEAUS   the table is being materialised as the search reaches
#                  more of the 71 chunks.  Bounded, harmless.
#    it CLIMBS to
#    the very end  something is retained per node.  Then depth 17 wants
#                  ten times this and depth 19 is out of reach, whatever
#                  the speed.
#
#  So watch the last few samples before the job exits, not the peak alone.
# =========================================================================

PAT=${1:-CountReal}
INT=${2:-5}

peak=0
peakt=0
seen=0

while :; do
  line=$(ps -eo pid=,rss=,etimes=,args= | grep -- "$PAT" | grep -v watchmem | \
         grep -v grep | head -1)
  if [ -z "$line" ]; then
    if [ "$seen" = "1" ]; then
      echo "--- gone.  peak $(awk -v r=$peak 'BEGIN{printf "%.2f", r/1048576}') GB\
 at t+${peakt}s"
    else
      echo "no process matching '$PAT'"
    fi
    exit 0
  fi
  seen=1
  pid=$(echo "$line"  | awk '{print $1}')
  rss=$(echo "$line"  | awk '{print $2}')
  et=$(echo "$line"   | awk '{print $3}')
  if [ "$rss" -gt "$peak" ]; then peak=$rss; peakt=$et; fi
  awk -v t="$(date +%H:%M:%S)" -v p="$pid" -v e="$et" -v r="$rss" -v k="$peak" \
      'BEGIN{printf "%s  pid %-8s t+%-6ss  RSS %6.2f GB   peak %6.2f GB\n",
             t, p, e, r/1048576, k/1048576}'
  sleep "$INT"
done
