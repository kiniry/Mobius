
export TOP = ../../../..
include ${TOP}/Makefile.defs

runtests:
	@echo JCF tests
	@echo SKIPPING `grep -v OK info | awk '{print $$1}'`
	@for i in `grep OK info | awk '{print $$1}'` ; do \
		    echo `grep $$i info | grep OK ` ; \
		    escjava -classpath . -quiet $$i/*.java; \
	done
