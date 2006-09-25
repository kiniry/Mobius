# Copyright 2000, 2001, Compaq Computer Corporation
# Altered extensively by David R. Cok as part of the 2003 upgrade of
# the ESC tools.

# author: David Cok
# author: Joe Kiniry

JAVAFE_VERSION=1.0

export TOP = ..
include ${TOP}/Makefile.defs
# The above defines JAVAFE_ROOT, JAVAC, JAVAC_FLAGS

# Various conventional UNIX tools are used in the following, including cc in 
# preprocess only mode.

##############################################################################
## Variables needed in the Makefile.
export CLASSDIRECTORY = ${JAVAFE_ROOT}/classfiles
export SOURCEDIRECTORY = ${JAVAFE_ROOT}/java
export TESTSOURCEDIRECTORY = ${JAVAFE_ROOT}/test
export CAN_CLASSDIRECTORY = ${call canonicalize,${CLASSDIRECTORY}}

## This one is needed in submakes that don't define their own classpath
export CLASSPATH = $(call canonicalize,${CLASSDIRECTORY}:${ESCTOOLS_ROOT}/Utils)

##############################################################################

.PHONY: default all build buildall test 

default: build

all: clean build test docs

build: fixperms compile

buildall: compileall

jar: build test
	jar cf dist/lib/javafe-$(JAVAFE_VERSION).jar -C classfiles .

ifdef ALLTESTS
test: extensive_tests self_typecheck typecheckJDK14
else
test: runtest self_typecheck
endif

###########################################################################
# build targets

SOURCEFILES := java/javafe/*.java java/javafe/*/*.java java/tohtml/*.java

CLASSESSTAMP = classes.stamp

SHELLSCRIPTS =	java/javafe/ast/make_tags \
		java/javafe/ast/insert_ensures

.PHONY: fixperms compile compileall javafeall source jtools

fixperms:
	@chmod 755 $(SHELLSCRIPTS)

## Compiles everything that is missing or out of date
compile: ${CLASSDIRECTORY} source ${CLASSESSTAMP}

## Compiles all out of date java files
${CLASSESSTAMP}: ${SOURCEFILES}
	${JAVAC} ${JAVAC_FLAGS} -classpath $(call canonicalize,${CLASSDIRECTORY}:${SOURCEDIRECTORY}:${ESCTOOLS_ROOT}/Utils) \
	  -d $(call canonicalize,${CLASSDIRECTORY}) $?
	touch ${CLASSESSTAMP}

## Full compile, including all java files, whether out of date or not
compileall: ${CLASSDIRECTORY} source javafeall

## Compiles all java files, whether out of date or not
javafeall:
	( cd java; \
	${JAVAC} ${JAVAC_FLAGS} -classpath $(call canonicalize,${CLASSDIRECTORY}:${SOURCEDIRECTORY}:${ESCTOOLS_ROOT}/Utils) \
	  -d $(call canonicalize,${CLASSDIRECTORY}) \
	  `find javafe -name "*.java"` \
	  `find tohtml -name "*.java"` )
	touch ${CLASSESSTAMP}

## Runs all targets that create java files using other tools
source: 
	${MAKE} -C astgen
	${MAKE} -C java/javafe/ast source
	${MAKE} -C java/javafe/tc source

## Creates the output directory (where class files go), if necessary
${CLASSDIRECTORY}:
	mkdir -p ${CLASSDIRECTORY}

## Builds other tools (FIXME - do we need this? - not part of the regular build)
jtools:	
	${MAKE} -C java/jtools

###########################################################################
# clean targets

.PHONY: clean cleanclasses

clean: cleanclasses
	rm -f doc/javadoc/*.html ${CLASSESSTAMP}
	${MAKE} -C java/javafe/ast clean
	${MAKE} -C test/javafe/parser/test clean
	${MAKE} -C java/javafe/tc clean
	${MAKE} -C test/javafe/test clean
	${MAKE} -C java/jtools clean
	${MAKE} -C astgen clean     ##  Has to be last - used by others

# Erase ${CLASSDIRECTORY}
cleanclasses:
	rm -rf ${CLASSDIRECTORY}
	-rm -rf ${JAVAFE_CLASSFILES4RAC}

###########################################################################
## docs targets

.PHONY: docs

docs:	
	@true

## javadocs are generated from the parent directory now

###########################################################################
## test targets

JAVAFETESTTARGETS = \
		javafe/test/Print.java			\
		javafe/test/SuperlinksTest.java		\
		javafe/test/SupertypeTest.java		\
		javafe/test/CountFilesLoaded.java	\
		javafe/test/LocTool.java		\
		javafe/test/lex/TestLex.java		\
		javafe/parser/test/TestLex.java		\
		javafe/parser/test/TestExpr.java	\
		javafe/parser/test/TestParse.java

## Runs basic tests on Javafe

.PHONY: runtest extensive_tests test_jdk_sources typecheckJDK \
	self_typecheck test_release javafe_test

runtest: javafe_test
	${MAKE} -C test/javafe/parser/test runtest
	${MAKE} -C java/javafe/util runtest
	${MAKE} -C test/javafe/test JAVAFE_CLASSPATH_CAN="${call canonicalize,${JAVAFE_CLASSPATH}}" runtest

## Runs basic tests, plus some (but not all) that are long
extensive_tests: javafe_test runtest
	${MAKE} -C test/javafe/parser/test bigtests

# This is included in extensive_tests above
test_jdk_sources:
	${MAKE} -C test/javafe/parser/test testparsejdkidempotence

## Runs the Javafe tool on bodies of code
typecheckJDK: javafe_test
	${MAKE} -C test/javafe/test typecheckJDK

self_typecheck:
	${MAKE} -C test/javafe/test typecheckJavafe

## This tests a binary release that is untarred in the RELTEMP directory,
## with RELCLASSPATH pointing to the esctools1.jar file that is being tested.
## The current directory should be the usual ESCTOOLS_ROOT directory so that
## the tests are available.
test-release: 
	@echo TESTING RELEASE - Javafe
	${MAKE} JAVAFE_CLASSPATH=$(call canonicalize,${RELCLASSPATH}) CLASSDIRECTORY=$(call canonicalize,${RELTEMP}) javafe_test
	${MAKE} ALLTESTS=1 CLASSPATH=$(call canonicalize,${RELCLASSPATH}) -C java/javafe/util runtest
	${MAKE} ALLTESTS=1 JAVAFE_CLASSPATH_CAN=$(call canonicalize,${RELCLASSPATH}) CLASSPATH=$(call canonicalize,${RELCLASSPATH}:${RELTEMP}) -C test/javafe/test runtest
	${MAKE} ALLTESTS=1 CLASSPATH=$(call canonicalize,${RELCLASSPATH}:${RELTEMP}) -C test/javafe/parser/test runtest
	rm -rf ${RELTEMP}/*

## This builds tests; presumes that the build has been made
javafe_test:
	@echo "building: ${JAVAFETESTTARGETS}"
	@( cd test; \
	  ${JAVAC} -classpath $(call canonicalize,${JAVAFE_CLASSPATH}:${TESTSOURCEDIRECTORY}) \
	  -d $(call canonicalize,${CLASSDIRECTORY}) \
	  ${JAVAFETESTTARGETS} )
