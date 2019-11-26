all: coqcompile

coqcompile:
	coq_makefile -f _CoqProject -o Makefile_coq
	$(MAKE) -f Makefile_coq > /dev/null

clean: 
	$(MAKE) -f Makefile_coq clean
