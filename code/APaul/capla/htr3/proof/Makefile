# The proofs of the Capla htr3 (../htr3.b) on Capla's semantics.
# Needs the opam switch `capla` (Rocq 9.0): eval $(opam env --switch=capla)
# The plan: doc/htr3-capla-plan.typ.
CAPLA ?= $(HOME)/git/capla-compiler
DIRS := lib common x86_64 x86 backend cfrontend driver cparser bfrontend
INC := $(foreach d,$(DIRS),-R $(CAPLA)/$(d) compcert.$(d)) \
       -R $(CAPLA)/flocq Flocq -R $(CAPLA)/MenhirLib MenhirLib \
       -R . Htr3 -Q apaul APaulRocq
COQC := coqc $(INC)

all: add_proof.vo SearchProof.vo

# The Capla programs as Rocq terms.
add.v: add.b
	$(CAPLA)/ccomp -dcaplarocq -c add.b && rm -f add.o
htr3.v: ../htr3.b
	cp ../htr3.b htr3.b && $(CAPLA)/ccomp -dcaplarocq -c htr3.b && rm -f htr3.b htr3.o

add_proof.vo: add_proof.v add.v
apaul/HtrDefs.vo: apaul/HtrDefs.v
htr3.vo: htr3.v
HtrBase.vo: HtrBase.v htr3.vo apaul/HtrDefs.vo
AddwProof.vo SubwProof.vo: HtrBase.vo
TstepProof.vo: AddwProof.vo
DifftabProof.vo: SubwProof.vo
SearchProof.vo: DifftabProof.vo TstepProof.vo

%.vo: %.v
	$(COQC) $<

clean:
	rm -f add.v htr3.v *.vo *.vok *.vos *.glob .*.aux *.o \
	  apaul/*.vo apaul/*.vok apaul/*.vos apaul/*.glob apaul/.*.aux
