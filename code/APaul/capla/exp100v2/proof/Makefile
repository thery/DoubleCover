# The proofs of the Capla exp100 (../exp100.b) on the new Capla, after
# ~/git/capla-proofexamples: Capla installed in the opam switch capla2
# (From compcert Require Import CaplaProof), the build by rocq makefile
# from _RocqProject.
#
# The shared pure-Z model (ExpNum.v ... ExpLimbs.v of ../../../exp100/rocq)
# is COPIED into $(MD)/ and built there as Exp100, so that no .vo is
# written next to the Rocq 9.1 builds of ../../../exp100/rocq.  $(MD) is
# not a Rocq identifier, so -R . Exp100Capla2 does not map it twice.
CCOMP ?= ccomp
MD := exp100-model
MODEL_SRC := ../../../exp100/rocq
MODEL_V := $(MD)/ExpNum.v $(MD)/ExpTable.v $(MD)/ExpConsts.v $(MD)/ExpModel.v \
           $(MD)/ExpModelBounds.v $(MD)/ExpLimbs.v
ROCQ_MAKEFILE := Makefile.rocq

all: $(ROCQ_MAKEFILE)
	$(MAKE) -f $(ROCQ_MAKEFILE) all

# the model: a copy of each file, refreshed when the original changes
$(MD)/%.v: $(MODEL_SRC)/%.v
	mkdir -p $(MD)
	cp $< $@

# the program as a Rocq term
exp100.v: ../exp100.b
	cp ../exp100.b exp100.b && $(CCOMP) -dcaplarocq -c exp100.b && \
	  rm -f exp100.b exp100.o

$(ROCQ_MAKEFILE): _RocqProject $(MODEL_V) exp100.v
	rocq makefile -f _RocqProject -o $@

clean:
	if [ -f $(ROCQ_MAKEFILE) ]; then $(MAKE) -f $(ROCQ_MAKEFILE) clean; fi
	rm -f $(ROCQ_MAKEFILE) $(ROCQ_MAKEFILE).conf .$(ROCQ_MAKEFILE).d exp100.v
	rm -rf $(MD)

.PHONY: all clean
.SECONDARY: $(MODEL_V)
