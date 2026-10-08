# ccomp -dcaplarocq on one.b and two.b, then the difference between the two
# terms of the function zero2.
CCOMP ?= ccomp

diff: one.v two.v
	@awk '/^Definition f_zero2 :=/{p=1} /^Definition / && !/f_zero2/{p=0} p' one.v > zero2_one.txt
	@awk '/^Definition f_zero2 :=/{p=1} /^Definition / && !/f_zero2/{p=0} p' two.v > zero2_two.txt
	-diff zero2_one.txt zero2_two.txt

%.v: %.b
	$(CCOMP) -dcaplarocq -c $< && rm -f $*.o

clean:
	rm -f one.v two.v zero2_one.txt zero2_two.txt
