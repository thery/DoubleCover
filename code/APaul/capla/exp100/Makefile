# The Capla exp100 (a probe for doc/exp100-capla-plan.typ).
# Needs the opam switch capla: eval $(opam env --switch=capla)
CAPLA ?= $(HOME)/git/capla-compiler
CCOMP := $(CAPLA)/ccomp

all: test_capla

# The Capla program and exp100.c side by side, both through ccomp.
test_capla: exp100.b test_capla.c ../../exp100/exp100.c ../../exp100/exp100_table.h
	$(CCOMP) -O2 exp100.b test_capla.c -o $@

test: test_capla
	./test_capla 1000000

# The program as a Rocq term and the proofs: make -C proof all.

clean:
	rm -f test_capla *.o
