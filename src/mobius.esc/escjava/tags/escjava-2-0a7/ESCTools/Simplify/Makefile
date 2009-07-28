# Copyright 2003, David R. Cok

# author: David Cok

export TOP = ..
include ${TOP}/Makefile.defs

export OUTPUTDIR = PPC_DARWIN

build:
	cd cgi-utils; cm3; sudo /sw/bin/cm3 -ship
	cd digraph; cm3; sudo /sw/bin/cm3 -ship
	cd prover; cm3; sudo /sw/bin/cm3 -ship
	cd simplify; cm3 -override; sudo /sw/bin/cm3 -ship

test:
	$(MAKE) -C simplify/test test

perf:
	cd simplify/test/perf; runtests
	

clean:
	rm -rf cgi-utils/$(OUTPUTDIR)
	rm -rf digraph/$(OUTPUTDIR)
	rm -rf prover/$(OUTPUTDIR)
	rm -rf simplify/$(OUTPUTDIR)
