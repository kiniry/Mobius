# Copyright 2000, 2001, Compaq Computer Corporation

TOP = ../../../../..
include ${TOP}/Makefile.defs

## Conditionally defined here, just in case it is not defined in the environment
export JAVA ?= java

## When the Makefile is run from JAVAFE_ROOT, this variable is set and exported.
## It is conditionally defined here so that the tests in this directory can
## be run via this Makefile directly.  The definition here must be the same as
## it is in ${JAVAFE_ROOT}
export CLASSDIRECTORY ?= ${JAVAFE_ROOT}/classfiles

## These define the executable and the options used to run the tests.  The
## -classpath option is tacked on in the do% target below since it is 
## specific to the test directory.
export TOOLCMD = ${JAVA} -mx40m -classpath ${CLASSDIRECTORY} javafe.test.Print -bootclasspath ${JDK_BINARIES}
export TOOLARGS = -noprint -typecheck
export TOOL = ${TOOLCMD} ${TOOLARGS}

runtest: septests
#runtest: diffs

all: outputs javac diffs compare summary

FILELIST = `ls | grep test | grep -v -f skip`
#FILELIST = test9 test1007 test12 test13 test15 test18 test20 test4 test5 test6

# Runs each test and does its comparison; also utilizes the skip file
septests:
	@touch skip
	@echo SKIPPING tests: `cat skip`
	@for t in ${FILELIST} ; do \
		echo "   Testing" $$t ... ;\
		${MAKE} --no-print-directory do$$t ; \
	done

outputs:
	./make_outputs

javac:
	./make_javac

diffs: outputs
	-./make_diffs

compare: outputs javac
	./make_comparsions

summary: test*
	./make_summary

# This target executes and compares a given test, e.g. 'make dotest1'
# executes and compares test1
## Must have variables JAVA and JAVAFE_ROOT set
do%:
	@( cd $*; \
	   export CLASSPATH=`pwd`; \
	   export TOOL="${TOOL} -classpath `pwd`" ; \
	   ./run 2>&1 | sed "s|`pwd`|<TEST>|g" > out)
	@diff $*/out $*/ans

## This target simply executes a given test, e.g. 'make extest1' runs test1
## Must have variables JAVA and JAVAFE_ROOT set
ex%:
	(  cd $*; \
	   export CLASSPATH=`pwd`; \
	   export TOOL="${TOOL} -classpath `pwd`" ; \
	   ./run )

clean: 
	rm -rf *.class test*/*.class
	rm -rf test*/out
	rm -rf test*/outc
	rm -rf log comparsions summary
	rm -rf _tmp_classes
	find . -name \*~ -exec rm {} \;

prepjdk:
	cat ${SOURCEDIRECTORY}/test/javafe/parser/test/jdk-1.0.2-files | xargs ${JAVA} javafe.test.PrepTest -classpath ${CLASSPATH}:/usr/local/Java/src/jdk-1.0.2 -v
	cat ${SOURCEDIRECTORY}/test/javafe/parser/test/jdk-1.1.18-files | xargs ${JAVA} javafe.test.PrepTest -classpath ${CLASSPATH}:/usr/local/Java/src/jdk-1.18_03 -v
	cat ${SOURCEDIRECTORY}/test/javafe/parser/test/jdk-1.2.2-files | xargs ${JAVA} javafe.test.PrepTest -classpath ${CLASSPATH}:/usr/local/Java/src/jdk-1.2.2_012 -v
	cat ${SOURCEDIRECTORY}/test/javafe/parser/test/jdk-1.3.1-files | xargs ${JAVA} javafe.test.PrepTest -classpath ${CLASSPATH}:/usr/local/Java/src/jdk-1.3.1_06 -v
	cat ${SOURCEDIRECTORY}/test/javafe/parser/test/jdk-1.4.1-files | xargs ${JAVA} javafe.test.PrepTest -classpath ${CLASSPATH}:/usr/local/Java/src/jdk-1.4.1_01 -v
