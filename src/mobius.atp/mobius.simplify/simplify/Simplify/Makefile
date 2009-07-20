# Copyright 2003, David R. Cok

# author: David Cok

export TOP = ..
include ${TOP}/Makefile.defs

export OUTPUTDIR = I386_DARWIN 

build:
	cd cgi-utils; cm3; sudo cm3 -ship
	cd digraph; cm3; sudo cm3 -ship
	cd prover; cm3; sudo cm3 -ship
	cd simplify; cm3 -override; sudo cm3 -ship

test:
	$(MAKE) -C simplify/test test

perf:
	cd simplify/test/perf; ./runtests
	
clean:
	rm -rf cgi-utils/$(OUTPUTDIR)
	rm -rf digraph/$(OUTPUTDIR)
	rm -rf prover/$(OUTPUTDIR)
	rm -rf simplify/$(OUTPUTDIR)
