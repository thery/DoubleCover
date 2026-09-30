# The check of Paul's k = 9, l = 6 tables.
# mksample.sh writes Data_N.v and Run_N.v for each table file; then
#   make -jJ sample
COQFLAGS := -R . ExpTable9

all: ExpProof.vo ExpParseSpec.vo

ExpParse.vo: ExpCheck.vo
ExpParseSpec.vo: ExpCheck.vo ExpParse.vo
ExpTaylor.vo ExpArith.vo ExpEncl.vo: ExpCheck.vo
ExpProof.vo: ExpCheck.vo ExpParse.vo ExpTaylor.vo ExpArith.vo ExpEncl.vo

RUNS := $(sort $(wildcard Run_*.v))
sample: $(RUNS:.v=.vo)
$(RUNS:.v=.vo): Run_%.vo: Run_%.v Data_%.vo ExpCheck.vo ExpParse.vo
	coqc $(COQFLAGS) $<

sample-all: SampleAll.vo
SampleAll.vo: SampleAll.v ExpProof.vo ExpParseSpec.vo $(RUNS:.v=.vo)
	coqc $(COQFLAGS) $<

%.vo: %.v
	coqc $(COQFLAGS) $<

clean:
	rm -f *.vo *.vok *.vos *.glob .*.aux
