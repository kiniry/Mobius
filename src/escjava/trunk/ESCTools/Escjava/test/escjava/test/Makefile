# Copyright 2003 ...
#

export TOP = ../../../..
include ${TOP}/Makefile.defs

TESTSOURCEDIRECTORY ?= ${ESCJAVA_ROOT}/test
PARSER_TEST_PACKAGE = escjava.parser.test
PARSER_TEST_DIR = ${TESTSOURCEDIRECTORY}/escjava/parser/test

## ESC_CLASSPATH is the classpath needed to run escj
export ESC_CLASSPATH ?= $(call canonicalize,${ESCJAVA_ROOT}/classfiles:${ESCJAVA_ROOT}/../Javafe/classfiles)
export ESCJ ?= ${ESCJAVA_ROOT}/escj

## Some tests need a few system spec files.  We include the ones that are part
## of the build so that they are consistent across platforms and users for tests
##export SYSTEM_SPECS = ${ESCTOOLS_ROOT}/Escjava/release/master/specs
export SYSTEM_SPECS = ${ESCTOOLS_ROOT}/specs

###########################################################################

compile_escjava_parser_test_programs:
	${JAVAC} ${JAVAC_FLAGS} \
		-classpath $(call canonicalize,${ESCJAVA_CLASSPATH}) \
		-d $(call canonicalize,${CLASSDIRECTORY}) \
		$(call canonicalize,${PARSER_TEST_DIR}/TestLex.java) \
		$(call canonicalize,${PARSER_TEST_DIR}/TestEscPragmaParser.java)

###########################################################################
## parser test targets


test:	compile_escjava_parser_test_programs \
	test_lexer test_parser test_parser_idempotence test_escjava

test_and_clean: test clean

test_escjava: CLASSPATH = $(call canonicalize,.:${ESCJAVA_CLASSPATH}:${SYSTEM_SPECS})
test_escjava:
ifdef ESCTOOLS_RELEASE
	env ESCTOOLS_RELEASE=$(ESCTOOLS_RELEASE) \
	env ESC_CLASSPATH=$(call canonicalize,${ESCJAVA_ROOT}/classfiles:${ESCJAVA_ROOT}/../Javafe/classfiles) \
	./rtestall
else
	env ESC_CLASSPATH=$(call canonicalize,${ESCJAVA_ROOT}/classfiles:${ESCJAVA_ROOT}/../Javafe/classfiles) \
	./rtestall
endif

%-run:
	env $(call canonicalize,CLASSPATH=.:${ESCJAVA_CLASSPATH}:${SYSTEM_SPECS}) \
	env ESC_CLASSPATH=$(call canonicalize,${ESCJAVA_ROOT}/classfiles:${ESCJAVA_ROOT}/../Javafe/classfiles) \
	./rtest $* || diff --strip-trailing-cr $*/out $*/ans

temp:
	cd test32; \
	env $(call canonicalize,CLASSPATH=.:${ESCJAVA_CLASSPATH}:${SYSTEM_SPECS}) \
	env ESC_CLASSPATH=$(call canonicalize,${ESCJAVA_ROOT}/classfiles:${ESCJAVA_ROOT}/../Javafe/classfiles) \
	escjava -v -plainwarning -notrace -warn Deadlock SynchHotspot.java

CD_AND_JAVA = cd $(PARSER_TEST_DIR); $(JAVA) -classpath $(call canonicalize,$(ESCJAVA_CLASSPATH)) $(PARSER_TEST_PACKAGE)

test_lexer: compile_escjava_parser_test_programs
	@echo "test_lexer: "
	$(CD_AND_JAVA).TestLex GoodPragmas.j | tee GoodPragmas.out | diff --strip-trailing-cr - GoodPragmas.ans
	$(CD_AND_JAVA).TestLex GoodSpecExpr.j | tee GoodSpecExpr.out | diff --strip-trailing-cr - GoodSpecExpr.ans
	$(CD_AND_JAVA).TestLex GoodJmlPragmas.j | tee GoodJmlPragmas.out | diff --strip-trailing-cr - GoodJmlPragmas.ans
	$(CD_AND_JAVA).TestLex lookahead GoodPragmas.j | tee GoodPragmas-lookahead.out | diff --strip-trailing-cr - GoodPragmas.ans
	$(CD_AND_JAVA).TestLex lookahead GoodSpecExpr.j | tee GoodSpecExpr-lookahead.out  | diff --strip-trailing-cr - GoodSpecExpr.ans
	$(CD_AND_JAVA).TestLex lookahead GoodJmlPragmas.j | tee GoodJmlPragmas-lookahead.out | diff --strip-trailing-cr - GoodJmlPragmas.ans

test_parser: compile_escjava_parser_test_programs
	$(CD_AND_JAVA).TestEscPragmaParser print TypeDeclElemPragmas1.java | \
		tee TypeDeclElemPragmas1.out | \
		diff --strip-trailing-cr - TypeDeclElemPragmas1.ans

test_parser_idempotence: compile_escjava_parser_test_programs
	$(CD_AND_JAVA).TestEscPragmaParser progress check idempotence \
		*.java ../../../../java/escjava/ast/*.java

clean:	clean_out_and_diff clean_escjava_parser_test

clean_escjava_parser_test:
	rm -f ${PARSER_TEST_DIR}/*.out
	rm -f ${CLASSDIRECTORY}/javafe/parser/test/*.class

clean_out_and_diff:
	rm -f test*/out test*/diffs out diffs
	for f in test* ; do \
		( cd $$f; rm -f out diffs `cat .cvsignore` ;);\
	done

# End of file
