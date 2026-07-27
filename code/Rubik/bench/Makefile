# Can the Rocq kernel hold, and reload, a table the size the superflip lower
# bound needs?  See README.md.
#
#   make          the 1M and 268M entry tables (a minute)
#   make huge     the 1G entry table -- needs about 9 GB free
#   make store    compute a table and put the VALUE in a .vo
#   make read     Require that .vo and read the table back
#   make clean

ROCQ ?= rocq compile

all: small big

Big.vo: Big.v
	$(ROCQ) Big.v

small: Big.vo
	@rm -f Run1M.vo
	$(ROCQ) Run1M.v

big: Big.vo
	@rm -f Run268M.vo
	$(ROCQ) Run268M.v

huge: Big.vo
	@rm -f Run1G.vo
	$(ROCQ) Run1G.v

store: Big.vo
	@rm -f Store.vo
	$(ROCQ) Store.v
	@ls -l Store.vo

read: store
	@rm -f Read.vo
	$(ROCQ) Read.v

clean:
	rm -f *.vo *.vok *.vos *.glob .*.aux

.PHONY: all small big huge store read clean
