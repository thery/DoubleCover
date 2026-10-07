# The search of one line (../htr3.c) followed by the filter of
# ../../exp100/exp100.c, verified with VST.  Needs the opam switch vst:
#   eval $(opam env --root=/home/thery/opam-rocq.9.1.0 --switch=vst)
# The proofs of ../ (htr3, `make` there, with `make ports`) and of
# ../exp100 (`make` there) must be built first: their .vo are reused here,
# nothing is written outside this directory.
COQC := coqc
# htr3-vo/ holds links to the .vo of ../ (HtrVst): -Q .. would also map
# this directory and ../exp100 a second time.  htr3-vo is not a Rocq
# identifier, so -Q . HF does not map it.
COQFLAGS := -Q htr3-vo HtrVst -Q . HF -Q ../link/apaul APaulRocq \
            -Q ../link/exptablekl ExpTableKL -Q ../exp100 E \
            -Q ../exp100/exp100-model Exp100

PROOFS := htr_filter_clight.vo FCommon.vo Spec_filter.vo Verif_filter.vo \
          Verif_htrfilter.vo Bits.vo FilterTable.vo

HTR3 := Words htr3_clight Common Spec_add Verif_sub Verif_add Verif_tstep \
        Fdiff Verif_difftab Spec_search Verif_search Verif_htr3 TableCands \
        VstTable

all: links $(PROOFS)

links:
	mkdir -p htr3-vo
	for f in $(HTR3); do ln -sf ../../$$f.vo htr3-vo/$$f.vo; done

# The Clight program VST reasons on (generated).
htr_filter_clight.v: htr_filter.c ../htr3.c ../../exp100/exp100.c \
  ../../exp100/exp100.h ../../exp100/exp100_table.h
	clightgen -normalize -o $@ htr_filter.c

%.vo: %.v
	$(COQC) $(COQFLAGS) $<

FCommon.vo: htr_filter_clight.vo
Spec_filter.vo: FCommon.vo
Verif_filter.vo: Spec_filter.vo
Verif_htrfilter.vo: Verif_filter.vo
FilterTable.vo: Spec_filter.vo Bits.vo

clean:
	rm -f *.vo *.vos *.vok *.glob .*.aux htr_filter_clight.v

.PHONY: all links clean
