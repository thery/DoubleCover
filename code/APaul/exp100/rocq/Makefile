# exp100 in Rocq: the constants, the model of exp100.c on Z and its
# real-number theorems (../PICKUP-common.md).  ExpTable.v is written by
# gen_v.py from ../exp100_table.h; the build fails if it is out of date.
# Built with Rocq 9.1 and Interval (the switch native).
COQFLAGS := -R . Exp100

all: ExpSpec.vo ExpLimbs.vo

# ExpTable.v must be the text gen_v.py writes from the C table
check-table: gen_v.py ../exp100_table.h ExpTable.v
	./gen_v.py ../exp100_table.h | cmp - ExpTable.v

table:
	./gen_v.py ../exp100_table.h > ExpTable.v

# checked again only when the C table, gen_v.py or ExpTable.v change
ExpTable.vo: ExpTable.v gen_v.py ../exp100_table.h
	./gen_v.py ../exp100_table.h | cmp - ExpTable.v
	coqc $(COQFLAGS) $<
ExpConsts.vo: ExpTable.vo
ExpModel.vo: ExpConsts.vo
ExpModelBounds.vo: ExpModel.vo
ExpLimbs.vo: ExpConsts.vo
ExpBits.vo: ExpModel.vo
ExpHard.vo: ExpModel.vo
ExpBudget.vo: ExpModelBounds.vo ExpTaylor.vo
ExpBound.vo: ExpBits.vo ExpBudget.vo
ExpFilter.vo: ExpModelBounds.vo ExpHard.vo
ExpSpec.vo: ExpBound.vo ExpFilter.vo

%.vo: %.v
	coqc $(COQFLAGS) $<

clean:
	rm -f *.vo *.vok *.vos *.glob .*.aux

.PHONY: all check-table table clean
