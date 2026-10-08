# The Capla search_filter (htr_filter.b) on the new Capla (ccomp in the
# opam switch capla3).
CCOMP ?= $(shell opam var bin --switch=capla3)/ccomp
FILTERDIR ?= $(HOME)/git/exp-full-proof/filter
R ?= 1000000

all: filter

# the Capla program and the C driver, both through ccomp
filter: htr_filter.b filter_main.c ../../exp100/exp100.c ../../exp100/exp100.h ../../exp100/exp100_table.h
	$(CCOMP) -O2 htr_filter.b filter_main.c -o $@

# the inputs kept on the table file in0, each line cut to N/R inputs,
# against the C filter of $(FILTERDIR)
check: filter
	./filter -reduce $(R) $(FILTERDIR)/in0 > check_capla.txt
	$(FILTERDIR)/filter -reduce $(R) $(FILTERDIR)/in0 > check_c.txt
	cmp check_capla.txt check_c.txt
	@echo "check passed: $$(wc -l < check_capla.txt) inputs kept by both"

# the program as a Rocq term and the proofs: make -C proof

clean:
	rm -f filter *.o check_capla.txt check_c.txt

.PHONY: all check clean
