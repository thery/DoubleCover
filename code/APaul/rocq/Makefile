# Build the Rocq certificates for the al.c hard-to-round search.
# Requires: rocq/coqc with coq-interval, coq-flocq, coq-coquelicot installed.

COQFLAGS := -R . APaulRocq

# Bench.v is excluded from the default build (it runs a timed workload);
# run it on demand with `make bench`.
VFILES := $(filter-out Bench.v, $(wildcard *.v))
VOFILES := $(VFILES:.v=.vo)

all: $(VOFILES)

# inter-file dependencies
Certif.vo: Data.vo
Hrc.vo: Data.vo
Search.vo: Cheb.vo Lefevre.vo Lefevre63.vo

%.vo: %.v
	coqc $(COQFLAGS) $<

# Cross-machine timing: prints two `Time` lines (see Bench.v for extrapolation).
bench: Search.vo Lefevre63.vo
	coqc $(COQFLAGS) Bench.v

clean:
	rm -f *.vo *.vok *.vos *.glob .*.aux
	rm -rf .coq-native

.PHONY: all clean bench
