# The constants of exp100, certified (step 3 of ../README).
# ExpTable.v is written by gen_v.py from ../exp100_table.h; the build
# fails if it is out of date.  Built with Rocq 9.1 and Interval (the
# switch native).
COQFLAGS := -R . Exp100

all: ExpSpec.vo

# ExpTable.v must be the text gen_v.py writes from the C table
check-table: gen_v.py ../exp100_table.h ExpTable.v
	./gen_v.py ../exp100_table.h | cmp - ExpTable.v

table:
	./gen_v.py ../exp100_table.h > ExpTable.v

ExpTable.vo: check-table
ExpConsts.vo: ExpTable.vo
ExpModel.vo: ExpConsts.vo
ExpBits.vo: ExpModel.vo
ExpHard.vo: ExpModel.vo
ExpBound.vo: ExpBits.vo ExpTaylor.vo
ExpFilter.vo: ExpHard.vo
ExpSpec.vo: ExpBound.vo ExpFilter.vo

%.vo: %.v
	coqc $(COQFLAGS) $<

clean:
	rm -f *.vo *.vok *.vos *.glob .*.aux

.PHONY: all check-table table clean
