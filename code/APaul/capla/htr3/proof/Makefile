# The proofs of the Capla htr3 (../run/htr3.b) on Capla's semantics.
# Needs the opam switch `capla` (Rocq 9.0): eval $(opam env --switch=capla)
# The plan: doc/htr3-capla-plan.typ.
CAPLA ?= $(HOME)/git/capla-compiler
DIRS := lib common x86_64 x86 backend cfrontend driver cparser bfrontend
INC := $(foreach d,$(DIRS),-R $(CAPLA)/$(d) compcert.$(d)) \
       -R $(CAPLA)/MenhirLib MenhirLib \
       -R . Htr3 -Q ../apaul APaulRocq -Q ../exptable9 ExpTable9
COQC := coqc $(INC)

all: add_proof.vo SearchProof.vo HtrFinal.vo HtrTable.vo

# The Capla programs as Rocq terms.
add.v: add.b
	$(CAPLA)/ccomp -dcaplarocq -c add.b && rm -f add.o
htr3.v: ../run/htr3.b
	cp ../run/htr3.b htr3.b && $(CAPLA)/ccomp -dcaplarocq -c htr3.b && rm -f htr3.b htr3.o

add_proof.vo: add_proof.v add.v
../apaul/HtrDefs.vo: ../apaul/HtrDefs.v
htr3.vo: htr3.v
HtrBase.vo: HtrBase.v htr3.vo ../apaul/HtrDefs.vo
AddwProof.vo SubwProof.vo: HtrBase.vo
TstepProof.vo: AddwProof.vo
DifftabProof.vo: SubwProof.vo
SearchProof.vo: DifftabProof.vo TstepProof.vo
HtrFinal.vo: SearchProof.vo ../apaul/TaylorLink.vo ../apaul/HtrMath.vo
HtrTable.vo: HtrFinal.vo ../exptable9/ExpProof.vo ../exptable9/ExpHard.vo

# The ports: the Rocq files of code/APaul/rocq (mirror ../apaul) and the proof
# files of code/exptable9 (mirror ../exptable9), built in the switch capla.
# Capla must be configured with -use-external-Flocq: the exptable9 files use
# Interval, built on the opam Flocq, and both are loaded together.
PORTCOQC := coqc -Q ../apaul APaulRocq -Q ../exptable9 ExpTable9
APAUL := Shift TaylorScan TaylorReal TaylorLink HtrMath
EXP := ExpCheck ExpParse ExpParseSpec ExpTaylor ExpArith ExpEncl ExpProof \
       ExpCover ExpHard
ports: $(APAUL:%=../apaul/%.vo) $(EXP:%=../exptable9/%.vo)

../apaul/TaylorScan.vo: ../apaul/Shift.vo
../apaul/TaylorLink.vo: ../apaul/Shift.vo ../apaul/TaylorScan.vo ../apaul/TaylorReal.vo
../apaul/HtrMath.vo: ../apaul/HtrDefs.vo ../apaul/TaylorReal.vo ../apaul/Shift.vo \
  ../apaul/TaylorScan.vo ../apaul/TaylorLink.vo
../exptable9/ExpParse.vo: ../exptable9/ExpCheck.vo
../exptable9/ExpParseSpec.vo: ../exptable9/ExpCheck.vo ../exptable9/ExpParse.vo
../exptable9/ExpTaylor.vo ../exptable9/ExpArith.vo ../exptable9/ExpEncl.vo: \
  ../exptable9/ExpCheck.vo
../exptable9/ExpProof.vo: ../exptable9/ExpCheck.vo ../exptable9/ExpParse.vo \
  ../exptable9/ExpTaylor.vo ../exptable9/ExpArith.vo ../exptable9/ExpEncl.vo
../exptable9/ExpCover.vo: ../exptable9/ExpCheck.vo ../exptable9/ExpParse.vo
../exptable9/ExpHard.vo: ../exptable9/ExpCheck.vo

$(filter-out ../apaul/HtrDefs.vo,$(APAUL:%=../apaul/%.vo)) $(EXP:%=../exptable9/%.vo): \
  %.vo: %.v
	$(PORTCOQC) $<

%.vo: %.v
	$(COQC) $<

# rocq-mcp only accepts load paths inside its workspace (here ..): mcp
# hard-links Capla's libraries into ../caplalib and writes ../_CoqProject.
mcp:
	rm -rf ../caplalib
	cd $(CAPLA) && find $(DIRS) MenhirLib -name '*.v' -o -name '*.vo' | \
	  while read f; do mkdir -p $(CURDIR)/../caplalib/$$(dirname $$f); \
	    ln -f $$f $(CURDIR)/../caplalib/$$f; done
	{ for d in $(DIRS); do echo "-R caplalib/$$d compcert.$$d"; done; \
	  echo "-R caplalib/MenhirLib MenhirLib"; \
	  echo "-R proof Htr3"; echo "-Q apaul APaulRocq"; \
	  echo "-Q exptable9 ExpTable9"; } > ../_CoqProject

clean:
	rm -f add.v htr3.v *.vo *.vok *.vos *.glob .*.aux *.o \
	  ../apaul/*.vo ../apaul/*.vok ../apaul/*.vos ../apaul/*.glob ../apaul/.*.aux \
	  ../exptable9/*.vo ../exptable9/*.vok ../exptable9/*.vos ../exptable9/*.glob \
	  ../exptable9/.*.aux
