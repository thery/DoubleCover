#!/bin/sh
# run.sh — xsin(x) = x * sin x, from C++ to C++ by two paths, in tangent and
# adjoint mode:
#   front: xsin.hpp → clang's AST (tools/clang2elpi.py) → L0 in Elpi (cxxfront.elpi): out/primal.elpi
#   Elpi:  L0 → Elpi passes → L2′ → lower, cxx → out/elpi/<mode>.hpp
#   Rocq:  L0 as a Rocq term (tools/torocq.elpi; the one written in Xsin.v)
#          → Rocq passes → L2′ → printed as an Elpi term (ToElpi.v)
#          → read by Elpi, checked equal to its own L2′ → lower, cxx → out/rocq/<mode>.hpp
# and checks that both paths give the same C++. Needs clang++ and the Rocq
# development built (make in ../../rocq).
set -e
cd "$(dirname "$0")"
CODE=../..
mkdir -p out/elpi out/rocq

# Front end: the C++ to L0.
python3 -I $CODE/tools/clang2elpi.py xsin.hpp > out/ast.elpi
elpi -I $CODE/elpi -I out $CODE/elpi/front/cxxfront.elpi -exec cxx-to-l0 -- examples/xsin/xsin.hpp 2>/dev/null \
  | sed -n '/^% .* in L0/,/^Success/p' | grep -v '^Success' > out/primal.elpi
cat out/primal.elpi

# Xsin.v starts from this L0.
printf 'accumulate torocq.\naccumulate primal.\n' > out/l0-to-rocq.elpi
elpi -I $CODE/elpi -I $CODE/tools -I out out/l0-to-rocq.elpi -exec to-rocq 2>/dev/null | grep '^Definition' > out/xsin_fn.v
tr -s ' \n' ' ' < Xsin.v | grep -qF "$(tr -s ' \n' ' ' < out/xsin_fn.v | sed 's/ $//')" \
  && echo "Xsin.v: its L0 is the one from the C++"

# Elpi path.
for m in tangent adjoint; do
  elpi -I $CODE/elpi out/primal.elpi -exec main -- examples/xsin $m out/elpi >/dev/null 2>&1
done

# Rocq path: Xsin.v prints the two programs as Elpi terms, tangent first.
rocq compile $(sed -n "s|^-R \([^ ]*\) ElpiDiff|-R $CODE/rocq/\1 ElpiDiff|p" $CODE/rocq/_CoqProject) Xsin.v > out/rocq/Xsin.out
sed -n 's/^ *= "\(dfunction .*\)"$/\1/p' out/rocq/Xsin.out | sed 's/""/"/g' > out/rocq/terms
{ echo '% the L2′ programs computed by Rocq (Xsin.v)'
  sed -n '1s/.*/rocq-l2 "tangent" (&)./p; 2s/.*/rocq-l2 "adjoint" (&)./p' out/rocq/terms
} > out/rocq/l2.elpi
printf 'accumulate fromrocq.\naccumulate primal.\naccumulate l2.\n' > out/rocq/run.elpi
for m in tangent adjoint; do
  elpi -I $CODE/elpi -I $CODE/tools -I out -I out/rocq out/rocq/run.elpi \
    -exec from-rocq -- examples/xsin $m out/rocq 2>&1 | grep "L2′"
done

# The two paths agree.
for m in tangent adjoint; do
  cmp out/elpi/$m.hpp out/rocq/$m.hpp && echo "$m.hpp: the same C++ from Elpi and from Rocq"
done
