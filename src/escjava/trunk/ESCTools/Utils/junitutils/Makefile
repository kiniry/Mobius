export TOP = ../..
include ${TOP}/Makefile.defs
# The above defines JUNIT_LIB and JAVAC and ESCJ.

.PHONY: clean
clean:
	@rm -f *.class classes.stamp

.PHONY: build
build: classes.stamp

classes.stamp: *.java
	${JAVAC} -classpath $(call canonicalize,${JUNIT_LIB}) $?
	touch classes.stamp

.PHONY: test
test:

CP = ${call canonicalize,${JUNIT_LIB}:${ESCTOOLS_ROOT}/Utils}

.PHONY: esctest
esctest:
	${ESCJ} -classpath ${CP} *.java
