export TOP = ../..
include ${TOP}/Makefile.defs
# The above defines JUNIT_LIB and JAVAC and ESCJ.

.PHONY: clean
clean:
	@rm -f *.class classes.stamp

.PHONY: build
build: classes.stamp

CP = ${call canonicalize,${ESCTOOLS_ROOT}/Utils:${JUNIT_LIB}}

classes.stamp: *.java
	${JAVAC} -classpath ${CP} $?
	touch classes.stamp

.PHONY: test
test: build

.PHONY: esctest
esctest:
	${ESCJ} -classpath ${CP} *.java
