# The check of Paul's k = 9, l = 6 tables.
# mksample.sh writes Data_N.v and Run_N.v for each table file; then
#   make -jJ sample
COQFLAGS := -R . ExpTable9

all: ExpCheck.vo ExpParse.vo

ExpParse.vo: ExpCheck.vo

RUNS := $(sort $(wildcard Run_*.v))
sample: $(RUNS:.v=.vo)
$(RUNS:.v=.vo): Run_%.vo: Run_%.v Data_%.vo ExpCheck.vo ExpParse.vo
	coqc $(COQFLAGS) $<

%.vo: %.v
	coqc $(COQFLAGS) $<

clean:
	rm -f *.vo *.vok *.vos *.glob .*.aux
