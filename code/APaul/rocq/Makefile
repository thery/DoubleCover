# Build the Rocq certificates for the al.c hard-to-round search.
# Requires: rocq/coqc with coq-interval, coq-flocq, coq-coquelicot installed.

VFILES := $(wildcard *.v)
VOFILES := $(VFILES:.v=.vo)

all: $(VOFILES)

%.vo: %.v
	coqc $<

clean:
	rm -f *.vo *.vok *.vos *.glob .*.aux
	rm -rf .coq-native

.PHONY: all clean
