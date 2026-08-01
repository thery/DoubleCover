# The hard-to-round search for exp on [0.25, 0.25001), in Capla.
#
# Three files and this Makefile, self-contained:
#
#   poly.b       21 limbs of 32 bits, the certified degree-7 polynomial
#   htr.b        the search, as a producer (htr_search) and as a checker
#                (htr_check).  Starts with `include! poly`
#   test_htr.c   the C driver: Capla has no input/output, so this holds
#                the arrays and does the printing
#
# CCOMP must point at the Capla compiler.  Building it, for reference:
#
#   git clone --recurse-submodules \
#       https://gitlab.inria.fr/fresco/capla/compiler.git
#   cd compiler
#   ./configure x86_64-linux -libdir $(pwd)/runtime -bindir $(pwd)
#   make
#
# Its configure accepts Rocq 8.15 to 9.0 and refuses 9.1.
#
#   make check-full     the search: prints the 5 cases and the candidate
#                       count, which must equal htr_plain.c's output
#   make check-oracle   the checker: the 5 known cases accepted, and the
#                       three ways an oracle can be wrong rejected
#
# Both take about three minutes; the interval holds ~1.8e11 points.

CCOMP ?= $(HOME)/git/capla-compiler/ccomp

all: test_htr

test_htr: htr.b poly.b test_htr.c
	$(CCOMP) htr.b test_htr.c -o $@

# What Capla generates, for reading: the unverified C backend, and the
# assembly.
gen-c: htr.b poly.b
	$(CCOMP) -dcaplac -c htr.b -o /dev/null

gen-s: htr.b poly.b
	$(CCOMP) -S htr.b

check-full: test_htr
	./test_htr

check-oracle: test_htr
	./test_htr -check

clean:
	rm -f test_htr htr.c htr.s *.o

.PHONY: all gen-c gen-s check-full check-oracle clean
