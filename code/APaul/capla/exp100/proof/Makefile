# The proofs of the Capla exp100 (../exp100.b) on Capla's semantics; a probe
# for doc/exp100-capla-plan.typ.  Needs the opam switch capla (Rocq 9.0).
CAPLA ?= $(HOME)/git/capla-compiler
DIRS := lib common x86_64 x86 backend cfrontend driver cparser bfrontend
INC := $(foreach d,$(DIRS),-R $(CAPLA)/$(d) compcert.$(d)) \
       -R $(CAPLA)/MenhirLib MenhirLib -R . Exp100Capla
COQC := coqc $(INC)

all: NumAddProof.vo

exp100.v: ../exp100.b
	cp ../exp100.b exp100.b && $(CAPLA)/ccomp -dcaplarocq -c exp100.b && \
	  rm -f exp100.b exp100.o
	# Capla's PrintCoq.ml prints Salloc as Salloc (i, e): a pair, not two
	# arguments; fixed here.
	sed -i -E 's/Salloc \(VAR ([0-9]+%positive "[^"]*"), /Salloc (VAR \1) (/' $@

exp100.vo: exp100.v
ExpBase.vo: ExpBase.v exp100.vo
NumAddProof.vo: ExpBase.vo

%.vo: %.v
	$(COQC) $<

clean:
	rm -f exp100.v *.vo *.vok *.vos *.glob .*.aux
