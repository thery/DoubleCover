#!/bin/sh
# One process a module.  Running them all in one -- which is what bench_ops.v
# used to do -- inflates whatever comes last by about 2.7x: the earlier loops
# fill the heap and the later ones pay the collections.
set -e
cd "$(dirname "$0")/.."
BIG="From Interval Require Import Specific_bigint Specific_ops.\nModule SFBI2 := SpecificFloat BigIntRadix2."
gen () {   # name import module prec
  sed -e "s|MODULE_IMPORT|$2|" -e "s|MODULE_NAME|$3|" -e "s|PREC|$4|" \
      bench/ops_template.v > "bench/gen_$1.v"
}
gen fp53   "From Interval Require Import Primitive_ops." "PrimitiveFloat"     53
gen big53  "$BIG"                                        "SFBI2"              53
gen big107 "$BIG"                                        "SFBI2"              107
gen big159 "$BIG"                                        "SFBI2"              159
gen dw107  "From dwarith Require dw_unsafe."             "dw_unsafe.DwFloatU" 107
gen tw159  "From twarith Require tw_unsafe."             "tw_unsafe.TwFloatU" 159
for m in fp53 big53 big107 big159 dw107 tw159; do
  printf '%s ' "$m"
  coqc -native-compiler no -Q . twarith -Q ../ddouble dwarith "bench/gen_$m.v" 2>&1 \
    | grep -E "Finished" | awk "{print \$4}" | tr "\n" " "
  echo
done
