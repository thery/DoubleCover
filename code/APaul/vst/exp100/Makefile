# The VST proof of ../../exp100/exp100.c.  Needs the opam switch vst
# (Rocq 9.0, CompCert, VST): run first
#   eval $(opam env --root=/home/thery/opam-rocq.9.1.0 --switch=vst)
# The integer model (ExpTable.v, ExpConsts.v, ExpModel.v of
# ../../exp100/rocq) and its real-number theorems (up to ExpSpec.v) are
# copied into $(MD)/ and built there as Exp100, so that no .vo is
# written next to the Rocq 9.1 builds of ../../exp100/rocq.
# $(MD) is not a Rocq identifier, so -Q . E does not map it a second time.
COQC := coqc
MD := exp100-model
COQFLAGS := -Q . E -Q $(MD) Exp100
SRC := ../../exp100
MODEL_SRC := $(SRC)/rocq

MODEL_V := $(MD)/ExpNum.v $(MD)/ExpTable.v $(MD)/ExpConsts.v $(MD)/ExpModel.v
MODEL := $(MODEL_V:.v=.vo)
# the real-number side of ../../exp100/rocq, up to ExpSpec.v, copied likewise
REAL_V := $(MD)/ExpModelBounds.v $(MD)/ExpBits.v $(MD)/ExpHard.v \
          $(MD)/ExpTaylor.v $(MD)/ExpBudget.v $(MD)/ExpBound.v \
          $(MD)/ExpFilter.v $(MD)/ExpSpec.v
REAL := $(REAL_V:.v=.vo)
PROOFS := exp100_clight.vo Common.vo Spec.vo Rows.vo Verif_simple.vo \
          Verif_bits.vo Verif_mulshr.vo Verif_reduce.vo CoreBounds.vo \
          Verif_core.vo \
          TopLemmas.vo Verif_top.vo Verif_all.vo \
          exp100_main_clight.vo InitConsts.vo Verif_main.vo \
          Verif_prog.vo

all: $(MODEL) $(REAL) $(PROOFS)

# the model: a copy of each file, refreshed when the original changes
$(MD)/%.v: $(MODEL_SRC)/%.v
	mkdir -p $(MD)
	cp $< $@

$(MD)/%.vo: $(MD)/%.v
	$(COQC) -Q $(MD) Exp100 $<

$(MD)/ExpConsts.vo: $(MD)/ExpTable.vo $(MD)/ExpNum.vo
$(MD)/ExpModel.vo: $(MD)/ExpConsts.vo
$(MD)/ExpModelBounds.vo $(MD)/ExpBits.vo $(MD)/ExpHard.vo: $(MD)/ExpModel.vo
$(MD)/ExpBudget.vo: $(MD)/ExpModelBounds.vo $(MD)/ExpTaylor.vo
$(MD)/ExpBound.vo: $(MD)/ExpBits.vo $(MD)/ExpBudget.vo
$(MD)/ExpFilter.vo: $(MD)/ExpModelBounds.vo $(MD)/ExpHard.vo
$(MD)/ExpSpec.vo: $(MD)/ExpBound.vo $(MD)/ExpFilter.vo

# keep the copies, which make would delete as intermediate files
.SECONDARY: $(MODEL_V) $(REAL_V)

# the Clight program VST reasons on (generated)
exp100_clight.v: $(SRC)/exp100.c $(SRC)/exp100.h $(SRC)/exp100_table.h
	clightgen -normalize -o $@ $(SRC)/exp100.c

# exp100.c with a main (exp100_main.c includes it), for semax_prog
exp100_main_clight.v: exp100_main.c $(SRC)/exp100.c $(SRC)/exp100.h \
  $(SRC)/exp100_table.h
	clightgen -normalize -o $@ exp100_main.c

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
InitConsts.vo: Common.vo
Verif_main.vo: Verif_all.vo InitConsts.vo exp100_main_clight.vo
Verif_prog.vo: Verif_main.vo
Verif_all.vo: Verif_simple.vo Verif_bits.vo Verif_mulshr.vo Verif_reduce.vo \
  Verif_core.vo TopLemmas.vo Verif_top.vo $(REAL)

clean:
	rm -f *.vo *.vos *.vok *.glob .*.aux exp100_clight.v exp100_main_clight.v
	rm -rf $(MD)

.PHONY: all clean
