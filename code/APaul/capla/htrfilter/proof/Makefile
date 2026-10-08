# The proofs of the Capla search plus filter (../htr_filter.b) on the new
# Capla, after ../../exp100v2/proof: Capla installed in the opam switch
# capla3 (From compcert Require Import CaplaProof), the build by rocq
# makefile from _RocqProject.
#
# The models are COPIED, never compiled in place: the files of
# ../../../rocq into $(HD)/ (built there as APaulRocq; Shift.v,
# TaylorScan.v and HtrMath.v get `Set SsrOldRewriteGoalsOrder.` after their
# mathcomp Require, since CaplaProof's mathcomp changed the default), the
# exp100 model of ../../../exp100/rocq into $(MD)/ (Exp100), the table
# check of ../../../../exptablekl into $(KD)/ (ExpTableKL) and
# ../../../vst/TableCands.v into $(VD)/ (HtrVst).  These directory names
# are not Rocq identifiers, so -R . HtrFilterCapla does not map them twice.
CCOMP ?= ccomp
HD := htr-model
HTR_SRC := ../../../rocq
HTR_V := $(HD)/HtrDefs.v $(HD)/Shift.v $(HD)/TaylorScan.v $(HD)/TaylorReal.v \
         $(HD)/TaylorLink.v $(HD)/HtrMath.v
HTR_OLD := $(HD)/Shift.v $(HD)/TaylorScan.v $(HD)/HtrMath.v
KD := tablekl-model
KL_SRC := ../../../../exptablekl
KL_V := $(KD)/ExpCheck.v $(KD)/ExpParse.v $(KD)/ExpTaylor.v $(KD)/ExpArith.v \
        $(KD)/ExpEncl.v $(KD)/ExpProof.v $(KD)/ExpHard.v
VD := vst-model
VST_SRC := ../../../vst
VST_V := $(VD)/TableCands.v
MD := exp100-model
MODEL_SRC := ../../../exp100/rocq
MODEL_V := $(MD)/ExpNum.v $(MD)/ExpTable.v $(MD)/ExpConsts.v $(MD)/ExpModel.v \
           $(MD)/ExpModelBounds.v $(MD)/ExpLimbs.v \
           $(MD)/ExpBits.v $(MD)/ExpHard.v $(MD)/ExpTaylor.v $(MD)/ExpBudget.v \
           $(MD)/ExpBound.v $(MD)/ExpFilter.v $(MD)/ExpSpec.v
ROCQ_MAKEFILE := Makefile.rocq

all: $(ROCQ_MAKEFILE)
	$(MAKE) -f $(ROCQ_MAKEFILE) all

# the models: a copy of each file, refreshed when the original changes
$(HTR_OLD): $(HD)/%.v: $(HTR_SRC)/%.v
	mkdir -p $(HD)
	awk '{print} !d && /^From mathcomp Require/ {print "Set SsrOldRewriteGoalsOrder."; d=1}' \
	  $< > $@

$(HD)/%.v: $(HTR_SRC)/%.v
	mkdir -p $(HD)
	cp $< $@

$(KD)/%.v: $(KL_SRC)/%.v
	mkdir -p $(KD)
	cp $< $@

$(VD)/%.v: $(VST_SRC)/%.v
	mkdir -p $(VD)
	cp $< $@

$(MD)/%.v: $(MODEL_SRC)/%.v
	mkdir -p $(MD)
	cp $< $@

# the program as a Rocq term
htr_filter.v: ../htr_filter.b
	cp ../htr_filter.b htr_filter.b && $(CCOMP) -dcaplarocq -c htr_filter.b && \
	  rm -f htr_filter.b htr_filter.o

$(ROCQ_MAKEFILE): _RocqProject $(HTR_V) $(MODEL_V) $(KL_V) $(VST_V) htr_filter.v
	rocq makefile -f _RocqProject -o $@

clean:
	if [ -f $(ROCQ_MAKEFILE) ]; then $(MAKE) -f $(ROCQ_MAKEFILE) clean; fi
	rm -f $(ROCQ_MAKEFILE) $(ROCQ_MAKEFILE).conf .$(ROCQ_MAKEFILE).d htr_filter.v
	rm -rf $(HD) $(MD) $(KD) $(VD)

.PHONY: all clean
.SECONDARY: $(HTR_V) $(MODEL_V) $(KL_V) $(VST_V)
