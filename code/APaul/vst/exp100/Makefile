# The VST proof of ../../exp100/exp100.c.  Needs the opam switch vst
# (Rocq 9.0, CompCert, VST): run first
#   eval $(opam env --root=/home/thery/opam-rocq.9.1.0 --switch=vst)
# The integer model (ExpTable.v, ExpConsts.v, ExpModel.v of
# ../../exp100/rocq) is copied into $(MD)/ and built there as Exp100, so
# that no .vo is written next to the Rocq 9.1 builds of ../../exp100/rocq.
# $(MD) is not a Rocq identifier, so -Q . E does not map it a second time.
COQC := coqc
MD := exp100-model
COQFLAGS := -Q . E -Q $(MD) Exp100
SRC := ../../exp100
MODEL_SRC := $(SRC)/rocq

MODEL_V := $(MD)/ExpNum.v $(MD)/ExpTable.v $(MD)/ExpConsts.v $(MD)/ExpModel.v
MODEL := $(MODEL_V:.v=.vo)
PROOFS := exp100_clight.vo Common.vo Spec.vo Rows.vo Verif_simple.vo \
          Verif_bits.vo Verif_mulshr.vo Verif_reduce.vo CoreBounds.vo \
          Verif_core.vo \
          TopLemmas.vo Verif_top.vo

all: $(MODEL) $(PROOFS)

# the model: a copy of each file, refreshed when the original changes
$(MD)/%.v: $(MODEL_SRC)/%.v
	mkdir -p $(MD)
	cp $< $@

$(MD)/%.vo: $(MD)/%.v
	$(COQC) -Q $(MD) Exp100 $<

$(MD)/ExpConsts.vo: $(MD)/ExpTable.vo $(MD)/ExpNum.vo
$(MD)/ExpModel.vo: $(MD)/ExpConsts.vo

# keep the copies, which make would delete as intermediate files
.SECONDARY: $(MODEL_V)

# the Clight program VST reasons on (generated)
exp100_clight.v: $(SRC)/exp100.c $(SRC)/exp100.h $(SRC)/exp100_table.h
	clightgen -normalize -o $@ $(SRC)/exp100.c

%.vo: %.v
	$(COQC) $(COQFLAGS) $<

Common.vo: $(MODEL) exp100_clight.vo
Spec.vo Rows.vo: Common.vo
Verif_simple.vo Verif_bits.vo Verif_mulshr.vo Verif_reduce.vo \
  Verif_core.vo Verif_top.vo: Spec.vo
Verif_core.vo: Rows.vo CoreBounds.vo
TopLemmas.vo: Spec.vo
Verif_top.vo: TopLemmas.vo
CoreBounds.vo: $(MODEL)

clean:
	rm -f *.vo *.vos *.vok *.glob .*.aux exp100_clight.v
	rm -rf $(MD)

.PHONY: all clean
