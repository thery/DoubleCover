#!/bin/sh
# One process a module, all seven goals in it.
set -e
cd "$(dirname "$0")/.."
BIG="From Interval Require Import Specific_bigint Specific_ops.\nModule SFBI2 := SpecificFloat BigIntRadix2."
gen () {
  sed -e "s|MODULE_IMPORT|$2|" -e "s|MODULE_NAME|$3|" -e "s|PREC|$4|" \
      bench/goals_template.v > "bench/goal_$1.v"
}
gen fp53   "From Interval Require Import Primitive_ops." "PrimitiveFloat"     53
gen big107 "$BIG"                                        "SFBI2"              107
gen big159 "$BIG"                                        "SFBI2"              159
gen dw107  "From dwarith Require dw_unsafe."             "dw_unsafe.DwFloatU" 107
gen tw159  "From twarith Require tw_unsafe."             "tw_unsafe.TwFloatU" 159
for m in "$@"; do
  echo "== $m =="
  coqc -native-compiler no -Q . twarith -Q ../ddouble dwarith "bench/goal_$m.v" 2>&1 \
    | grep -E "^pi|^method|^poly|^cancel|^  ok|^  refused|Finished"
done
