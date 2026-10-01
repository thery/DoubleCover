# The check of Paul's k = 9, l = 6 tables.
# mksample.sh writes Data_N.v, Run_N.v and Cover_N.v for each table file;
# then
#   make -jJ sample
#   make sample-all
COQFLAGS := -R . ExpTable9

all: ExpProof.vo ExpParseSpec.vo ExpCover.vo

ExpParse.vo: ExpCheck.vo
ExpParseSpec.vo: ExpCheck.vo ExpParse.vo
ExpTaylor.vo ExpArith.vo ExpEncl.vo: ExpCheck.vo
ExpProof.vo: ExpCheck.vo ExpParse.vo ExpTaylor.vo ExpArith.vo ExpEncl.vo
ExpCover.vo: ExpCheck.vo ExpParse.vo

RUNS := $(sort $(wildcard Run_*.v))
COVERS := $(sort $(wildcard Cover_*.v))
sample: $(RUNS:.v=.vo) $(COVERS:.v=.vo)
$(RUNS:.v=.vo): Run_%.vo: Run_%.v Data_%.vo ExpCheck.vo ExpParse.vo
	coqc $(COQFLAGS) $<
$(COVERS:.v=.vo): Cover_%.vo: Cover_%.v Data_%.vo ExpCover.vo
	coqc $(COQFLAGS) $<

sample-all: SampleAll.vo AllCover.vo
SampleAll.vo: SampleAll.v ExpProof.vo ExpParseSpec.vo $(RUNS:.v=.vo)
	coqc $(COQFLAGS) $<
AllCover.vo: AllCover.v ExpProof.vo ExpParseSpec.vo ExpCover.vo \
  $(RUNS:.v=.vo) $(COVERS:.v=.vo)
	coqc $(COQFLAGS) $<

# The bit-flip test: make test
test: ExpMutate.vo
ExpMutate.vo: ExpCheck.vo ExpParse.vo MutData.vo

%.vo: %.v
	coqc $(COQFLAGS) $<

clean:
	rm -f *.vo *.vok *.vos *.glob .*.aux
