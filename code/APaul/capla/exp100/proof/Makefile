# The proofs of the Capla exp100 (../exp100.b) on Capla's semantics; a probe
# for doc/exp100-capla-plan.typ.  Needs the opam switch capla (Rocq 9.0).
MD := exp100-model
CAPLA ?= $(HOME)/git/capla-compiler
DIRS := lib common x86_64 x86 backend cfrontend driver cparser bfrontend
INC := $(foreach d,$(DIRS),-R $(CAPLA)/$(d) compcert.$(d)) \
       -R $(CAPLA)/MenhirLib MenhirLib -R . Exp100Capla -Q $(MD) Exp100
COQC := coqc $(INC)

# The shared pure-Z model (ExpNum.v ... ExpLimbs.v of ../../../exp100/rocq)
# is copied into $(MD)/ and built there as Exp100, so that no .vo is written
# next to the Rocq 9.1 builds of ../../../exp100/rocq.  $(MD) is not a Rocq
# identifier, so -R . Exp100Capla does not map it a second time.
MODEL_SRC := ../../../exp100/rocq
MODEL_V := $(MD)/ExpNum.v $(MD)/ExpTable.v $(MD)/ExpConsts.v $(MD)/ExpModel.v \
           $(MD)/ExpModelBounds.v $(MD)/ExpLimbs.v
MODEL := $(MODEL_V:.v=.vo)
# the real-number side of ../../../exp100/rocq, up to ExpSpec.v, copied likewise
REAL_V := $(MD)/ExpBits.v $(MD)/ExpHard.v $(MD)/ExpTaylor.v \
          $(MD)/ExpBudget.v $(MD)/ExpBound.v $(MD)/ExpFilter.v $(MD)/ExpSpec.v
REAL := $(REAL_V:.v=.vo)

PROOFS := NumAddProof.vo NumBasicProof.vo NumSubProof.vo NumLtProof.vo \
  NumMulProof.vo NumBitsProof.vo ReduceProof.vo ExpCoreProof.vo \
  DecideProof.vo ExpTopProof.vo RowCall.vo CaplaFinal.vo

all: $(MODEL) $(REAL) $(PROOFS)

# the model: a copy of each file, refreshed when the original changes
$(MD)/%.v: $(MODEL_SRC)/%.v
	mkdir -p $(MD)
	cp $< $@

$(MD)/%.vo: $(MD)/%.v
	coqc -Q $(MD) Exp100 $<

$(MD)/ExpConsts.vo: $(MD)/ExpTable.vo $(MD)/ExpNum.vo
$(MD)/ExpModel.vo: $(MD)/ExpConsts.vo
$(MD)/ExpModelBounds.vo: $(MD)/ExpModel.vo
$(MD)/ExpLimbs.vo: $(MD)/ExpNum.vo
$(MD)/ExpBits.vo $(MD)/ExpHard.vo: $(MD)/ExpModel.vo
$(MD)/ExpBudget.vo: $(MD)/ExpModelBounds.vo $(MD)/ExpTaylor.vo
$(MD)/ExpBound.vo: $(MD)/ExpBits.vo $(MD)/ExpBudget.vo
$(MD)/ExpFilter.vo: $(MD)/ExpModelBounds.vo $(MD)/ExpHard.vo
$(MD)/ExpSpec.vo: $(MD)/ExpBound.vo $(MD)/ExpFilter.vo

# keep the copies, which make would delete as intermediate files
.SECONDARY: $(MODEL_V) $(REAL_V)

exp100.v: ../exp100.b
	cp ../exp100.b exp100.b && $(CAPLA)/ccomp -dcaplarocq -c exp100.b && \
	  rm -f exp100.b exp100.o
	# Capla's PrintCoq.ml prints Salloc as Salloc (i, e): a pair, not two
	# arguments; fixed here.
	sed -i -E 's/Salloc \(VAR ([0-9]+%positive "[^"]*"), /Salloc (VAR \1) (/' $@

exp100.vo: exp100.v

# the probe of a call with a row T[j] (RowCall.v)
rowcall.v: rowcall.b
	$(CAPLA)/ccomp -dcaplarocq -c rowcall.b && rm -f rowcall.o
RowCall.vo: rowcall.vo
ExpBase.vo: ExpBase.v exp100.vo
NumAddProof.vo: ExpBase.vo $(MD)/ExpLimbs.vo
Bridge.vo: ExpBase.vo $(MD)/ExpLimbs.vo
Specs.vo: Bridge.vo $(MD)/ExpModel.vo
# each spec file: statements first (Admitted), proofs by tasks T2..T13
NumBasicProof.vo NumSubProof.vo NumLtProof.vo NumMulProof.vo \
  NumBitsProof.vo ReduceProof.vo: Specs.vo $(MD)/ExpModelBounds.vo
ExpCoreProof.vo: NumAddProof.vo Specs.vo $(MD)/ExpModelBounds.vo \
  NumBasicProof.vo NumSubProof.vo NumLtProof.vo NumBitsProof.vo \
  NumMulProof.vo ReduceProof.vo
DecideProof.vo: NumAddProof.vo NumBasicProof.vo NumSubProof.vo \
  NumLtProof.vo NumBitsProof.vo
ExpTopProof.vo: ExpCoreProof.vo DecideProof.vo
# group A: shared tactics and pure lemmas
GroupALemmas.vo: Specs.vo $(MD)/ExpModelBounds.vo
NumBasicProof.vo NumSubProof.vo NumLtProof.vo NumBitsProof.vo \
  DecideProof.vo ExpTopProof.vo: GroupALemmas.vo
NumBitsProof.vo: NumBasicProof.vo
# pure lemmas for the alloc functions (mul_ln2, guess_n, the top)
ReduceLemmas.vo: Specs.vo
TopLemmasCapla.vo: Specs.vo $(MD)/ExpModelBounds.vo
ReduceProof.vo: NumMulProof.vo ReduceLemmas.vo GroupALemmas.vo
ExpTopGen.vo: TopLemmasCapla.vo GroupALemmas.vo
ExpEnclGen.vo: TopLemmasCapla.vo GroupALemmas.vo
ExpTopProof.vo: ExpTopGen.vo
# the final theorems, on the reals
CaplaFinal.vo: ExpTopProof.vo $(MD)/ExpSpec.vo

%.vo: %.v
	$(COQC) $<

# rocq-mcp (server rocq-mcp-capla): it reads the load path from this
# directory's _CoqProject; mcp writes it from INC.
mcp:
	echo $(INC) | sed 's/ -\([RQ]\) /\n-\1 /g' > _CoqProject

clean:
	rm -f exp100.v rowcall.v *.vo *.vok *.vos *.glob .*.aux
	rm -rf $(MD)

.PHONY: all clean mcp
