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
## Define, use CLASSPATH so it can be overridden during release testing
export CLASSPATH ?= $(call canonicalize,${CLASSDIRECTORY})

## These define the executable and the options used to run the tests.  The
## -classpath option is tacked on in the do% target below since it is 
## specific to the test directory.
ifdef JDK_BINARIES
  JBIN = -bootclasspath $(call canonicalize,${JDK_BINARIES})
else
  JBIN =
endif

export TOOLCMD = ${JAVA} -mx40m -classpath $(call canonicalize,${CLASSDIRECTORY}) javafe.test.Print ${JBIN}
export TOOLARGS = -noprint -typecheck -quiet
export TOOL = ${TOOLCMD} ${TOOLARGS}

runtest: septests
#runtest: diffs

all: outputs javac diffs compare summary

ifdef ALLTESTS
FILELIST = `ls | grep test | grep -v -f skip`
else
FILELIST = `ls | grep test | grep -v -f skip -f skipunlessall `
endif

# Runs each test and does its comparison; also utilizes the skip file
septests:
	@touch skip skipunlessall
	@echo Performing tests with
	@echo "    TOOL: ${TOOL}"
	@echo "    CLASSPATH: ${CLASSPATH}"
	@echo SKIPPING tests: `grep -v '^#' skip`
ifndef ALLTESTS
	@echo tests NOT INCLUDED - ALLTESTS not defined: ` grep -v '^#' skipunlessall`
endif
	@for t in ${FILELIST} ; do \
		echo -n '.' ; \
		${MAKE} --no-print-directory do$$t ; \
	done
	@echo " "

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
do%: testclasses
	@( cd $*; \
	   export TOOL="${TOOL} -classpath ." ; \
	   ./run 2>&1 | sed "s|`pwd`|<TEST>|g" > out)
	@diff $*/out $*/ans || echo Test $* failed

testclasses: ${CLASSDIRECTORY}/javafe/test/Print.class

${CLASSDIRECTORY}/javafe/test/Print.class:
	${MAKE} -C ${JAVAFE_ROOT} javafe_test

## This target simply executes a given test, e.g. 'make extest1' runs test1
## Must have variables JAVA and JAVAFE_ROOT set

%-run:
	(  cd $*; \
	   export JAVAFE=$(call canonicalize,${ESCTOOLS_ROOT}/Javafe); \
	   export CLASSPATH=$(call canonicalize,$*) ;\
	   export TOOL="${TOOL} -classpath ." ; \
	   ./run )

clean: 
	rm -rf *.class test*/*.class
	rm -rf test*/out
	rm -rf test*/outc
	rm -rf log comparsions summary
	rm -rf _tmp_classes
	find . -name \*~ -exec rm {} \;
