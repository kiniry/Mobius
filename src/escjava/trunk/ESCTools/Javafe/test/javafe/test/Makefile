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

.PHONY: typecheckJDK
typecheckJDK:
	-for d in ${JDK_PRE14_SOURCES}; do \
	    echo ===== Typechecking $${d} ;\
	    (cd $${d} && \
		echo `find . -name '*.java'` | xargs -n 300 \
		${JAVA} -classpath ${CAN_CLASSDIRECTORY} javafe.test.Print \
		-classpath $${d} -source 1.4 \
		-typecheck -noprint -preferSource ) ;\
	done
	-for d in ${JDK_14_SOURCES}; do \
	    echo ===== Typechecking $${d} ;\
	    (cd $${d} && \
		echo `find . -name '*.java'` | xargs -n 300 \
		${JAVA} -classpath ${CAN_CLASSDIRECTORY} javafe.test.Print \
		-classpath $${d} -source 1.4 \
		-typecheck -noprint -preferSource ) ;\
	done

.PHONY: typecheckJavafe
typecheckJavafe:
	@echo ===== Typechecking the Javafe package =====
	cd ${ESCTOOLS_ROOT}/Javafe/java && \
	for d in ast parser tc util filespace reader decsrc genericfile ; do \
	echo `find javafe/$${d} -name '*.java'` | xargs -n 300 \
	    ${JAVA} -classpath ../classfiles javafe.test.Print \
	    -classpath "${call canonicalize,.:../../Utils}" \
	    -typecheck -noprint  ;\
	done && \
	    ${JAVA} -classpath ../classfiles javafe.test.Print \
	    -classpath "${call canonicalize,.:../../Utils}" \
	    -typecheck -noprint  javafe/*.java ;\
