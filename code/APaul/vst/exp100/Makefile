# Probes for the VST proof of ../../exp100/exp100.c (see
# ../../exp100/PICKUP-vst.md and doc/exp100-vst-plan.typ).  Run first
#   eval $(opam env --root=/home/thery/opam-rocq.9.1.0 --switch=vst)
COQC := coqc
COQFLAGS := -Q . E
SRC := ../../exp100

PROOFS := exp100_clight.vo Limbs.vo Common.vo Spec.vo Verif_zero.vo \
          Verif_add.vo Rows.vo

all: $(PROOFS)

exp100_clight.v: $(SRC)/exp100.c $(SRC)/exp100.h $(SRC)/exp100_table.h
	clightgen -normalize -o $@ $(SRC)/exp100.c

%.vo: %.v
	$(COQC) $(COQFLAGS) $<

Common.vo: Limbs.vo exp100_clight.vo
Spec.vo: Common.vo
Verif_zero.vo Verif_add.vo: Spec.vo
Rows.vo: Common.vo

clean:
	rm -f *.vo *.vos *.vok *.glob .*.aux exp100_clight.v

.PHONY: all clean
