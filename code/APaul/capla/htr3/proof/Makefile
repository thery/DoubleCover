# The proof of add.b (htr3.c's multi-limb addition) on Capla's semantics.
# Needs the opam switch `capla`: eval $(opam env --switch=capla)
CAPLA ?= $(HOME)/git/capla-compiler
DIRS := lib common x86_64 x86 backend cfrontend driver cparser bfrontend
INC := $(foreach d,$(DIRS),-R $(CAPLA)/$(d) compcert.$(d)) \
       -R $(CAPLA)/flocq Flocq -R $(CAPLA)/MenhirLib MenhirLib

all: add_proof.vo

# The Capla program as a Rocq term.
add.v: add.b
	$(CAPLA)/ccomp -dcaplarocq -c add.b && rm -f add.o

add_proof.vo: add_proof.v add.v
	coqc $(INC) add_proof.v

clean:
	rm -f add.v *.vo *.vok *.vos *.glob .*.aux add.o
