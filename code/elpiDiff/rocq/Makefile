# make: compiles the Rocq development (rocq makefile generates CoqMakefile)
all: CoqMakefile
	$(MAKE) -f CoqMakefile
CoqMakefile: _CoqProject
	rocq makefile -f _CoqProject -o CoqMakefile
clean: CoqMakefile
	$(MAKE) -f CoqMakefile clean
	rm -f CoqMakefile CoqMakefile.conf
.PHONY: all clean
