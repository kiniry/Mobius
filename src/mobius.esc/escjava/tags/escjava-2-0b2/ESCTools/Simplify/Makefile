# Copyright 2003, David R. Cok
# Modified 2007, Mobius Project, Systems Research Group, University College Dublin

# author: David Cok

export TOP = ..
include ${TOP}/Makefile.defs

export OUTPUTDIR = PPC_DARWIN
export CM3 = /opt/local/cm3/bin/cm3

build:
	cd cgi-utils; $(CM3); $(CM3) -ship
	cd digraph; $(CM3); $(CM3) -ship
	cd prover; $(CM3); $(CM3) -ship
	cd simplify; $(CM3) -override; $(CM3) -ship

test:
	$(MAKE) -C simplify/test test

perf:
	cd simplify/test/perf; runtests
	

clean:
	rm -rf cgi-utils/$(OUTPUTDIR)
	rm -rf digraph/$(OUTPUTDIR)
	rm -rf prover/$(OUTPUTDIR)
	rm -rf simplify/$(OUTPUTDIR)
