export TOP = ../..
include ${TOP}/Makefile.defs
# The above defines JUNIT_LIB and JAVAC.

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
