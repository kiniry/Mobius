# Copyright 2000, 2001, Compaq Computer Corporation

JAVA ?= java

runtest: testlex testexpr testparseidempotence testpragmalexer testpragmaparser

big: runtest testexprbig testparsejdkidempotence

clean:
	rm -f *~ *.out

testlex:
	${JAVA} javafe.parser.test.TestLex \
	  < simpletoks > simpletoks.out \
	  && diff simpletoks.Lex simpletoks.out
	${JAVA} javafe.parser.test.TestLex \
	  < literaltoks > literaltoks.out \
	  && diff literaltoks.Lex literaltoks.out
	${JAVA} javafe.parser.test.TestLex lookahead javakeywords \
	  < simpletoks > simpletoks.out \
	  && diff simpletoks.Lookahead simpletoks.out
	${JAVA} javafe.parser.test.TestLex lookahead javakeywords \
	  < literaltoks > literaltoks.out \
	  && diff literaltoks.Lookahead literaltoks.out

testpragmalexer:
	${JAVA} javafe.parser.test.TestLex parsepragmas javakeywords \
	  < pragmatoks >pragmatoks.out \
	&& diff pragmatoks.out pragmatoks.ans

testpragmaparser:
	${JAVA} javafe.parser.test.TestParse idempotence check HasPragmas.j

testexpr:
	${JAVA} javafe.parser.test.TestExpr check < test-exprs1.j
	${JAVA} javafe.parser.test.TestExpr check compare < compare-exprs-small.j

testparseidempotence:
	${JAVA} javafe.parser.test.TestParse diff simpletoks simpletoks
	${JAVA} javafe.parser.test.TestParse progress check idempotence \
		compilation-unit.j *.java ${JAVAFE_ROOT}/java/javafe/parser/*.java \
		${JAVAFE_ROOT}/java/javafe/ast/*.java
# The first line above tests the diff algorithm...


testexprbig:
	${JAVA} javafe.parser.test.TestExpr check compare < compare-exprs-big.j

# @note kiniry 13 Jan 2002 - Should cause two exceptions in 1.4.1 files.
testparsejdk:
	cat jdk-1.0.2-files | xargs ${JAVA} javafe.parser.test.TestParse progress check silent
	cat jdk-1.1.18-files | xargs ${JAVA} javafe.parser.test.TestParse progress check silent
	cat jdk-1.2.2-files | xargs ${JAVA} javafe.parser.test.TestParse progress check silent
	cat jdk-1.3.1-files | xargs ${JAVA} javafe.parser.test.TestParse progress check silent
	cat jdk-1.4.1-files | xargs ${JAVA} javafe.parser.test.TestParse progress check silent

# @note kiniry 13 Jan 2002 - Should cause two exceptions in 1.4.1 files.
testparsejdkidempotence:
	${JAVA} javafe.parser.test.TestParse diff simpletoks simpletoks
	cat jdk-1.0.2-files | xargs ${JAVA} javafe.parser.test.TestParse progress silent idempotence
	cat jdk-1.1.18-files | xargs ${JAVA} javafe.parser.test.TestParse progress silent idempotence
	cat jdk-1.2.2-files | xargs ${JAVA} javafe.parser.test.TestParse progress silent idempotence
	cat jdk-1.3.1-files | xargs ${JAVA} javafe.parser.test.TestParse progress silent idempotence
	cat jdk-1.4.1-files | xargs ${JAVA} javafe.parser.test.TestParse progress silent idempotence

testparse:
	${JAVA} javafe.parser.test.TestParse progress check print verboseprogress\
		compilation-unit.j *.java \
		${JAVAFE_ROOT}/java/javafe/parser/*.java \
		${JAVAFE_ROOT}/java/javafe/ast/*.java

