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

.PHONY: jdk_source_listings
jdk_source_listings:
	find ${JDK10_SOURCES} -follow -name "*.java" -print > jdk-1.0-files 
	find ${JDK11_SOURCES} -follow -name "*.java" -print > jdk-1.1-files 
	find ${JDK12_SOURCES} -follow -name "*.java" -print > jdk-1.2-files 
	find ${JDK13_SOURCES} -follow -name "*.java" -print > jdk-1.3-files 
	find ${JDK14_SOURCES} -follow -name "*.java" -print > jdk-1.4-files 

testparsejdkidempotence:
	${JAVA} javafe.parser.test.TestParse diff simpletoks simpletoks
	cat jdk-1.0-files | xargs ${JAVA} javafe.parser.test.TestParse progress silent idempotence
	cat jdk-1.1-files | xargs ${JAVA} javafe.parser.test.TestParse progress silent idempotence
	cat jdk-1.2-files | xargs -n 1000 -s 1024 ${JAVA} javafe.parser.test.TestParse progress silent idempotence
	cat jdk-1.3-files | xargs -n 1000 -s 1024 ${JAVA} javafe.parser.test.TestParse progress silent idempotence
	cat jdk-1.4-files | xargs -n 1000 -s 1024 ${JAVA} javafe.parser.test.TestParse progress silent idempotence

testparse:
	${JAVA} javafe.parser.test.TestParse progress check print verboseprogress \
		compilation-unit.j *.java \
		${JAVAFE_ROOT}/java/javafe/parser/*.java \
		${JAVAFE_ROOT}/java/javafe/ast/*.java

