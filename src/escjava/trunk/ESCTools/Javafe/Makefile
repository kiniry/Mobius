# Copyright 2000, 2001, Compaq Computer Corporation
# Altered extensively by David R. Cok as part of the 2003 upgrade of
# the ESC tools.


export TOP = ..
include ${TOP}/Makefile.defs
# The above defines JAVAFE_ROOT, JAVAC, JAVAC_FLAGS

# Various conventional UNIX tools are used in the following, including cc in 
# preprocess only mode.

##############################################################################
## Variables needed in the Makefile.
export CLASSDIRECTORY=${JAVAFE_ROOT}/classfiles
export SOURCEDIRECTORY=${JAVAFE_ROOT}/java
export TESTSOURCEDIRECTORY=${JAVAFE_ROOT}/test

export CLASSES=${CLASSDIRECTORY}
export CLASSPATH=${CLASSES}:.

##############################################################################

.PHONY: default
default: build

.PHONY: all
all: clean build test docs

.PHONY: build
build: compile

.PHONY: buildall
buildall: compileall

.PHONY: test
test: javafe_test runtest

## FIXME - install stuff needs work
.PHONY: install
install: clean build javafe_test javadoc zip

###########################################################################
# build targets

SOURCEFILES := java/javafe/*.java java/javafe/*/*.java java/tohtml/*.java

CLASSESSTAMP = classes.stamp


.PHONY: compile
compile: $(CLASSDIRECTORY) source $(CLASSESSTAMP)

$(CLASSESSTAMP): $(SOURCEFILES)
	$(JAVAC) $(JAVAC_FLAGS) -classpath ${CLASSPATH}:${SOURCEDIRECTORY} \
	  -d ${CLASSDIRECTORY} $?
	touch $(CLASSESSTAMP)

.PHONY: compileall
compileall: $(CLASSDIRECTORY) source javafeall

.PHONY: javafeall
javafeall:
	( cd java; \
	$(JAVAC) $(JAVAC_FLAGS) -classpath ${CLASSPATH}:${SOURCEDIRECTORY} \
	  -d ${CLASSDIRECTORY} `find javafe -name "*.java"` \
				`find tohtml -name "*.java"` )
	touch $(CLASSESSTAMP)

.PHONY: source
source: 
	${MAKE} -C astgen
	${MAKE} -C java/javafe/ast source
	${MAKE} -C java/javafe/tc source

$(CLASSDIRECTORY):
	mkdir -p $(CLASSDIRECTORY)

.PHONY: jtools
jtools:	
	${MAKE} -C java/jtools

###########################################################################
## install targets

## FIXME - FIX THIS, and install in general

.PHONY: zip
zip:
	rm -f ${CLASSDIRECTORY}/javafe.zip
	cd ${CLASSDIRECTORY}; jar -cf0 javafe.zip javafe tohtml
	chmod a+r ${CLASSDIRECTORY}/javafe.zip


###########################################################################
# clean targets

.PHONY: clean
clean: cleanclasses
	rm -f doc/javadoc/*.html $(CLASSESSTAMP)
	${MAKE} -C java/javafe/ast clean
	${MAKE} -C test/javafe/parser/test clean
	${MAKE} -C java/javafe/tc clean
	${MAKE} -C test/javafe/test clean
	${MAKE} -C java/jtools clean
	${MAKE} -C astgen clean          ##  Has to be last

.PHONY: cleanclasses
cleanclasses:
	rm -rf $(CLASSDIRECTORY)


###########################################################################
## docs targets

.PHONY: docs
docs:	

## javadocs are generated from the parent directory

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
		javafe/parser/test/TestParse.java	\


.PHONY: runtest
runtest:
	${MAKE} -C test/javafe/parser/test runtest
	${MAKE} -C java/javafe/util        runtest
	${MAKE} -C test/javafe/test        runtest

.PHONY: javafe_test
javafe_test:
	( cd test; \
	javac -classpath ${CLASSPATH}:${SOURCEDIRECTORY}:${TESTSOURCEDIRECTORY} \
	  -d ${CLASSDIRECTORY} ${JAVAFETESTTARGETS} )

###########################################################################
## misc targets

OTHERSOURCEFILES = astgen/ast*.c astgen/ast*.h astgen/ast*.l
TESTHARNESSFILES = test/javafe/parser/test/Test*.java test/javafe/test/*.java

.PHONY: wc
wc:
	# --- Non-java Source files ---
	wc ${OTHERSOURCEFILES}
	# --- Java Source files ---
	wc ${SOURCEFILES}
	${JAVA} javafe.CountLines ${JAVASOURCEFILES}
	# jrun javafe.parser.test.TestParse print ${JAVASOURCEFILES} | wc
	# --- Test harness files ---
	wc ${TESTHARNESSFILES}
	${JAVA} javafe.CountLines ${TESTHARNESSFILES}
	# jrun javafe.parser.test.TestParse print ${TESTHARNESSFILES} | wc




.PHONY: esc
esc: source
	cd java; \
	date; \
	escjava -classpath ${CLASSPATH} -f `find javafe -name "*.java"` \
	date
