# $Id$
# Copyright 2000, 2001, Compaq Computer Corporation

export TOP=../../../..
include ${TOP}/Makefile.defs

runtest:
	@echo "TESTING Javafe: test/javafe/test"
	@cd lex; ${MAKE} runtest
	@cd fe; ${MAKE} runtest

clean: 
	cd lex; ${MAKE} clean
	cd fe; ${MAKE} clean

# $(foreach jar,$(wildcard $${d}/jars/*.jar),$(jar):)

# @note kiniry 25 Dec 2005 - Only the source of the JDK that we are
# currently running in (1.4 at this time) should completely typecheck.
# @see bug #142
.PHONY: typecheckJDK typecheckOldJDK typecheckJDK14
typecheckJDK: typecheckOldJDK typecheckJDK14

typecheckOldJDK:
	-for d in ${JDK_PRE14_SOURCES}; do \
	    echo "===== type checking $${d}" ;\
	    if [ -e $${d} ]; then \
	    (cd $${d} && \
		echo `find . -name '*.java'` | xargs -n 300 \
		${JAVA} \
		-classpath ${CAN_CLASSDIRECTORY} \
		javafe.test.Print \
		-classpath $${d}$(call canonicalize,:$${d}/jars/classes.jar:$${d}/jars/rt.jar:$${d}/jars/tools.jar:$${d}/jars/ui.jar) \
		-typecheck -noprint -preferSource) ;\
	    else \
		echo "      $${d} does not exist";\
	    fi ;\
	done

typecheckJDK14:
	-for d in ${JDK_14_SOURCES}; do \
	    echo "===== type checking $${d}" ;\
	    if [ -e $${d} ]; then \
	    (cd $${d} && \
		echo `find . -name '*.java'` | xargs -n 300 \
		${JAVA} \
		-classpath ${CAN_CLASSDIRECTORY}$(call canonicalize,:classes.jar) \
		 javafe.test.Print \
		-classpath $${d}$(call canonicalize,:$${d}/jars/classes.jar:$${d}/jars/rt.jar:$${d}/jars/tools.jar:$${d}/jars/ui.jar) \
		-source 1.4 \
		-typecheck -noprint -preferSource ) ;\
	    else \
		echo "      $${d} does not exist";\
	    fi ;\
	done

.PHONY: typecheckJavafe
typecheckJavafe:
	@echo "===== type checking the Javafe package ====="
	@cd ${ESCTOOLS_ROOT}/Javafe/java && \
		for d in ast parser tc util filespace reader decsrc genericfile ; do \
		echo -n "$${d}	" ;\
		echo `find javafe/$${d} -name '*.java'` | xargs -n 300 \
			${JAVA} -classpath ../classfiles${EXTRA_CP} javafe.test.Print \
			-classpath "${call canonicalize,.:../../Utils${EXTRA_CP}}" \
			-typecheck -noprint  ;\
		done 
	@echo -n "javafe/.	"
	@cd ${ESCTOOLS_ROOT}/Javafe/java && \
		${JAVA} -classpath ../classfiles${EXTRA_CP} javafe.test.Print \
		-classpath "${call canonicalize,.:../../Utils${EXTRA_CP}}" \
		-typecheck -noprint  javafe/*.java ;\


# End of Makefile
