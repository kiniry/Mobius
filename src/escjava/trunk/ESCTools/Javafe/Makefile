# Copyright 2000, 2001, Compaq Computer Corporation

# Need to source setup{.sh} before calling gnumake

.PHONY: all
all: clean javafe javafe_test runtest

.PHONY: everything
everything: clean javafe javafe_test javadoc runtest

.PHONY: install
install: clean javafe javafe_test javadoc zip

# Check that 'source setup' has been run in the Javafe directory:
# if ESCJ is defined, then the following line will fail
.PHONY: sourcecheck
sourcecheck:
	@if [ ! ${JAVAFE_ROOT} ]; then \
	  echo "You must source the 'setup[.sh]' script before running make."; \
	  false; \
	fi

.PHONY: zip
zip: sourcecheck
	rm -f ${CLASSDIRECTORY}/javafe.zip
	cd ${CLASSDIRECTORY}; jar -cf0 javafe.zip javafe tohtml
	chmod a+r ${CLASSDIRECTORY}/javafe.zip

.PHONY: source
source:
	cd astgen; ${MAKE}
	cd java/javafe/ast; ${MAKE} source
	cd java/javafe/tc; ${MAKE} source

.PHONY: clean
clean: cleanclasses sourcecheck
	cd doc/javadoc; rm -f *.html
	cd java/javafe/ast; ${MAKE} clean
	cd test/javafe/parser/test; ${MAKE} clean
	cd java/javafe/tc; ${MAKE} clean
	cd test/javafe/test; ${MAKE} clean
	cd java/jtools; ${MAKE} clean
	cd astgen; ${MAKE} clean

.PHONY: cleanclasses
cleanclasses:
	cd classfiles; find . -name \*.class | xargs rm -f

.PHONY: jtools
jtools:	javafe
	cd java/jtools; ${MAKE}

.PHONY: doc
doc:	javadoc

.PHONY: javadoc
javadoc: source 
	cd java; \
        ${JAVADOC} -classpath ${CLASSPATH} \
	  -sourcepath ${SOURCEDIRECTORY}:${TESTSOURCEDIRECTORY} \
	  -d ${JAVADOCDIRECTORY} \
          javafe javafe.ast javafe.parser  \
	  javafe.reader javafe.genericfile javafe.filespace \
	  javafe.tc javafe.util
#	  jtools.jwhich jtools.jls
#	  jtools.jcheck
#         jtools.jcheck.parseTypes

.PHONY: runtest
runtest:
	cd test/javafe/parser/test; 	${MAKE} runtest
	cd java/javafe/util; 		${MAKE} runtest
	cd test/javafe/test; 		${MAKE} runtest

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

#
# Code for fast incremental recompilation of javafe:
#

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

.PHONY: javafe
javafe: source sourcecheck
	cd java; \
	javac -g -classpath ${CLASSPATH}:${SOURCEDIRECTORY} \
	  -d ${CLASSDIRECTORY} `find javafe -name "*.java"`; \
	javac -g -classpath ${CLASSPATH}:${SOURCEDIRECTORY} \
	  -d ${CLASSDIRECTORY} `find tohtml -name "*.java"`;

.PHONY: javafe_test
javafe_test: javafe sourcecheck
	cd test; \
	javac -classpath ${CLASSPATH}:${SOURCEDIRECTORY}:${TESTSOURCEDIRECTORY} \
	  -d ${CLASSDIRECTORY} ${JAVAFETESTTARGETS}

.PHONY: compile
compile: javafe javafe_test zip sourcecheck

.PHONY: esc
esc: source
	cd java; \
	date; \
	escjava -classpath ${CLASSPATH} -f `find javafe -name "*.java"` \
	date
