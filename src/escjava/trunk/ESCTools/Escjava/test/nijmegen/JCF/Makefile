

runtests:
	@echo JCF tests
	@echo SKIPPING `grep -v OK info | awk '{print $$1}'`
	@for i in jcf* ; do \
		if [[ `grep $$i info | grep OK ` ]] ; then \
		    echo `grep $$i info | grep OK ` ; \
		    ( cd $$i; escjava -classpath .. -quiet *.java );\
		fi; \
	done
