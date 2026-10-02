# The search of htr.c for one line, in C, verified with VST.
# Needs the opam switch `vst` (Rocq 9.0, CompCert, VST): run
#   eval $(opam env --root=/home/thery/opam-rocq.9.1.0 --switch=vst)
# first.  `make htr3` needs only gcc.

COQC := coqc
COQFLAGS := -Q . HtrVst -Q link/apaul APaulRocq -Q link/exptablekl ExpTableKL
CLIGHTGEN := clightgen

PROOFS := Words.vo htr3_clight.vo Common.vo Spec_add.vo Verif_sub.vo \
          Verif_add.vo Verif_tstep.vo Fdiff.vo Verif_difftab.vo \
          Spec_search.vo Verif_search.vo Verif_htr3.vo TableCands.vo \
          VstTable.vo

all: htr3 $(PROOFS)

.PHONY: all ports clean

# The search with its driver, by gcc.
htr3: htr3.c main.c
	gcc -O2 -Wall htr3.c main.c -lm -o $@

# The Clight program VST reasons on (generated).
htr3_clight.v: htr3.c
	$(CLIGHTGEN) -normalize -o $@ htr3.c

PORTFLAGS := -Q link/apaul APaulRocq -Q link/exptablekl ExpTableKL
link/%.vo: link/%.v
	$(COQC) $(PORTFLAGS) $<

%.vo: %.v
	$(COQC) $(COQFLAGS) $<

Common.vo: Words.vo htr3_clight.vo
Verif_sub.vo: Common.vo
Spec_add.vo: Common.vo
Verif_add.vo: Spec_add.vo
Fdiff.vo: Words.vo
Verif_difftab.vo: Fdiff.vo Verif_sub.vo
Verif_tstep.vo: Spec_add.vo
Spec_search.vo: Fdiff.vo Verif_tstep.vo
Verif_search.vo: Spec_search.vo Verif_difftab.vo Verif_sub.vo
Verif_htr3.vo: Verif_search.vo Verif_add.vo
TableCands.vo: link/apaul/HtrMath.vo link/exptablekl/ExpHard.vo
VstTable.vo: Spec_search.vo TableCands.vo link/exptablekl/ExpProof.vo

# The ports: links to the Rocq files of code/APaul/rocq (link/apaul) and of
# code/exptablekl (link/exptablekl), built here in the switch vst.
APAUL := HtrDefs Shift TaylorScan TaylorReal TaylorLink HtrMath
EXP := ExpCheck ExpParse ExpParseSpec ExpTaylor ExpArith ExpEncl ExpProof \
       ExpCover ExpHard
ports: $(APAUL:%=link/apaul/%.vo) $(EXP:%=link/exptablekl/%.vo)

link/apaul/TaylorScan.vo: link/apaul/Shift.vo
link/apaul/TaylorLink.vo: link/apaul/Shift.vo link/apaul/TaylorScan.vo \
  link/apaul/TaylorReal.vo
link/apaul/HtrMath.vo: link/apaul/HtrDefs.vo link/apaul/TaylorLink.vo
link/exptablekl/ExpParse.vo link/exptablekl/ExpTaylor.vo \
  link/exptablekl/ExpArith.vo link/exptablekl/ExpEncl.vo \
  link/exptablekl/ExpHard.vo: link/exptablekl/ExpCheck.vo
link/exptablekl/ExpParseSpec.vo link/exptablekl/ExpCover.vo: \
  link/exptablekl/ExpParse.vo
link/exptablekl/ExpProof.vo: link/exptablekl/ExpParse.vo \
  link/exptablekl/ExpTaylor.vo link/exptablekl/ExpArith.vo \
  link/exptablekl/ExpEncl.vo

clean:
	rm -f htr3 *.vo *.vos *.vok *.glob .*.aux htr3_clight.v
	rm -f link/*/*.vo link/*/*.vos link/*/*.vok link/*/*.glob link/*/.*.aux
