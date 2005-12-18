# Copyright 2000, 2001, Compaq Computer Corporation

export TOP=../../../..
include ${TOP}/Makefile.defs

runtest:
	@echo "TESTING Javafe: test/javafe/test"
	cd lex; ${MAKE} runtest
	cd fe; ${MAKE} runtest

clean: 
	cd lex; ${MAKE} clean
	cd fe; ${MAKE} clean

# $(foreach jar,$(wildcard $${d}/jars/*.jar),$(jar):)

.PHONY: typecheckJDK
typecheckJDK:
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
	cd ${ESCTOOLS_ROOT}/Javafe/java && \
		for d in ast parser tc util filespace reader decsrc genericfile ; do \
		echo -n $${d} ;\
		echo `find javafe/$${d} -name '*.java'` | xargs -n 300 \
			${JAVA} -classpath ../classfiles javafe.test.Print \
			-classpath "${call canonicalize,.:../../Utils}" \
			-typecheck -noprint  ;\
		done && \
			${JAVA} -classpath ../classfiles javafe.test.Print \
			-classpath "${call canonicalize,.:../../Utils}" \
			-typecheck -noprint  javafe/*.java ;\
