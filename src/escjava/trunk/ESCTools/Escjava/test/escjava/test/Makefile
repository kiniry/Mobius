# Copyright 2003 ...
#

export TOP = ../../../..
include ${TOP}/Makefile.defs

export ESC_CLASSPATH ?= ${ESCJAVA_ROOT}/classfiles:${ESCJAVA_ROOT}/../Javafe/classfiles
export ESCJ = ${ESCJAVA_ROOT}/escj -quiet
export BOOTCLASSPATH ?= ${JDK_BINARIES}
#export BOOTCLASSPATH ?= ${JDKSPEC_ROOT}:${JDK_BINARIES}

###########################################################################

compile_escjava_parser_test_programs:
	@${JAVAC} ${JAVAC_FLAGS} \
		${PARSER_TEST_DIR}/TestLex.java \
		${PARSER_TEST_DIR}/TestEscPragmaParser.java

###########################################################################
## parser test targets

PARSER_TEST_PACKAGE = escjava.parser.test
PARSER_TEST_DIR = ${TESTSOURCEDIRECTORY}/escjava/parser/test

test:	test_lexer_and_parser test_escjava

test_and_clean: test clean

test_escjava:
	./rtestall

%-run:
	./rtest $*

test_lexer_and_parser:	compile_escjava_parser_test_programs \
	test_lexer test_parser test_parser_idempotence 

CD_AND_JAVA = cd $(PARSER_TEST_DIR); $(JAVA) -classpath $(ESCJAVA_CLASSPATH) $(PARSER_TEST_PACKAGE)

test_lexer: compile_escjava_parser_test_programs
	@echo "test_lexer: "
	$(CD_AND_JAVA).TestLex GoodPragmas.j    | tee GoodPragmas.out | diff - GoodPragmas.ans
	$(CD_AND_JAVA).TestLex GoodSpecExpr.j   | tee GoodSpecExpr.out | diff - GoodSpecExpr.ans
	$(CD_AND_JAVA).TestLex GoodJmlPragmas.j | tee GoodJmlPragmas.out | diff - GoodJmlPragmas.ans
	$(CD_AND_JAVA).TestLex lookahead GoodPragmas.j | tee GoodPragmas-lookahead.out | diff - GoodPragmas.ans
	$(CD_AND_JAVA).TestLex lookahead GoodSpecExpr.j | tee GoodSpecExpr-lookahead.out  | diff - GoodSpecExpr.ans
	$(CD_AND_JAVA).TestLex lookahead GoodJmlPragmas.j | tee GoodJmlPragmas-lookahead.out | diff - GoodJmlPragmas.ans

test_parser: compile_escjava_parser_test_programs
	$(CD_AND_JAVA).TestEscPragmaParser print TypeDeclElemPragmas1.java | \
		diff - TypeDeclElemPragmas1.ans

test_parser_idempotence: compile_escjava_parser_test_programs
	$(CD_AND_JAVA).TestEscPragmaParser progress check idempotence \
		*.java $(SOURCEDIRECTORY)/escjava/ast/*.java

clean:	clean_out_and_diff clean_escjava_parser_test

clean_escjava_parser_test:
	rm -f ${PARSER_TEST_DIR}/*.out
	rm -f ${CLASSDIRECTORY}/javafe/parser/test/*.class

clean_out_and_diff:
	rm -f test*/out test*/diffs out diffs

# End of file
