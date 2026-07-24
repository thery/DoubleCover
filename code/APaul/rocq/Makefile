# Build the Rocq certificates for the al.c hard-to-round search.
# Requires: rocq/coqc with coq-interval, coq-flocq, coq-coquelicot installed.

COQFLAGS := -R . APaulRocq

# Bench.v / BenchNative.v are excluded from the default build (they run a
# timed workload); run them on demand with `make bench` / `make bench-native`.
VFILES := $(filter-out Bench.v BenchNative.v FirstHRC.v, $(wildcard *.v))
VOFILES := $(VFILES:.v=.vo)

all: $(VOFILES)

# inter-file dependencies
Certif.vo: Data.vo
Hrc.vo: Data.vo
Search.vo: Cheb.vo Lefevre.vo Lefevre63.vo

%.vo: %.v
	coqc $(COQFLAGS) $<

# Cross-machine timing: prints the `Time` lines (see Bench.v for extrapolation).
bench: Search.vo Lefevre63.vo
	coqc $(COQFLAGS) Bench.v

# Same workloads via native_compile (needs a native-compiler-enabled build).
first-hrc: Search.vo Lefevre63.vo
	coqc $(COQFLAGS) FirstHRC.v

bench-native: Search.vo Lefevre63.vo
	coqc $(COQFLAGS) BenchNative.v

clean:
	rm -f *.vo *.vok *.vos *.glob .*.aux
	rm -rf .coq-native

.PHONY: all clean bench bench-native first-hrc
