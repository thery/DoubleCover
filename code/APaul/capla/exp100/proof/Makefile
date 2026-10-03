# The proofs of the Capla exp100 (../exp100.b) on Capla's semantics; a probe
# for doc/exp100-capla-plan.typ.  Needs the opam switch capla (Rocq 9.0).
MD := exp100-model
CAPLA ?= $(HOME)/git/capla-compiler
DIRS := lib common x86_64 x86 backend cfrontend driver cparser bfrontend
INC := $(foreach d,$(DIRS),-R $(CAPLA)/$(d) compcert.$(d)) \
       -R $(CAPLA)/MenhirLib MenhirLib -R . Exp100Capla -Q $(MD) Exp100
COQC := coqc $(INC)

# The shared pure-Z model (ExpTable.v ... ExpLimbs.v of ../../../exp100/rocq)
# is copied into $(MD)/ and built there as Exp100, so that no .vo is written
# next to the Rocq 9.1 builds of ../../../exp100/rocq.  $(MD) is not a Rocq
# identifier, so -R . Exp100Capla does not map it a second time.
MODEL_SRC := ../../../exp100/rocq
MODEL_V := $(MD)/ExpTable.v $(MD)/ExpConsts.v $(MD)/ExpModel.v \
           $(MD)/ExpModelBounds.v $(MD)/ExpLimbs.v
MODEL := $(MODEL_V:.v=.vo)

all: $(MODEL) NumAddProof.vo Bridge.vo

# the model: a copy of each file, refreshed when the original changes
$(MD)/%.v: $(MODEL_SRC)/%.v
	mkdir -p $(MD)
	cp $< $@

$(MD)/%.vo: $(MD)/%.v
	coqc -Q $(MD) Exp100 $<

$(MD)/ExpConsts.vo: $(MD)/ExpTable.vo
$(MD)/ExpModel.vo: $(MD)/ExpConsts.vo
$(MD)/ExpModelBounds.vo: $(MD)/ExpModel.vo
$(MD)/ExpLimbs.vo: $(MD)/ExpConsts.vo

# keep the copies, which make would delete as intermediate files
.SECONDARY: $(MODEL_V)

exp100.v: ../exp100.b
	cp ../exp100.b exp100.b && $(CAPLA)/ccomp -dcaplarocq -c exp100.b && \
	  rm -f exp100.b exp100.o
	# Capla's PrintCoq.ml prints Salloc as Salloc (i, e): a pair, not two
	# arguments; fixed here.
	sed -i -E 's/Salloc \(VAR ([0-9]+%positive "[^"]*"), /Salloc (VAR \1) (/' $@

exp100.vo: exp100.v
ExpBase.vo: ExpBase.v exp100.vo
NumAddProof.vo: ExpBase.vo
Bridge.vo: ExpBase.vo $(MD)/ExpLimbs.vo

%.vo: %.v
	$(COQC) $<

clean:
	rm -f exp100.v *.vo *.vok *.vos *.glob .*.aux
	rm -rf $(MD)

.PHONY: all clean
