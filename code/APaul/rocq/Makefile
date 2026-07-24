# Build the Rocq certificates for the al.c hard-to-round search.
# Requires: rocq/coqc with coq-interval, coq-flocq, coq-coquelicot installed.

COQFLAGS := -R . APaulRocq

VFILES := $(wildcard *.v)
VOFILES := $(VFILES:.v=.vo)

all: $(VOFILES)

# inter-file dependencies
Certif.vo: Data.vo
Hrc.vo: Data.vo
Search.vo: Poly.vo Lefevre.vo Lefevre63.vo

%.vo: %.v
	coqc $(COQFLAGS) $<

clean:
	rm -f *.vo *.vok *.vos *.glob .*.aux
	rm -rf .coq-native

.PHONY: all clean
