#!/bin/sh
# Regenerate the eighteen pieces of the depth 12 search.  One per second
# move, both root moves inside, so each is one vm_compute over two searches.
# Farmain.v glues them; it lists them by name, so if this count changes
# the master has to change with it.
for j in 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17; do
  n=$(printf "%02d" $j)
  sed -e "s/@N@/$n/g" -e "s/@J@/$j/g" Far_task.v.in > "Far_$n.v"
done
