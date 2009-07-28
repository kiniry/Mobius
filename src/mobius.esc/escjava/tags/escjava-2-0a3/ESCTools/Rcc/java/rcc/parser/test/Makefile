# Copyright 2000, 2001, Compaq Computer Corporation

P = rcc.parser.test

runtest: full testparseidempotence

full: java
	javac -d ${CLASSDIRECTORY}  TestRccPragmaParser.java

java:
	echo Nothing to do

clean:
	rm -f *~ *.out00
	rm -rf *.class ${CLASSDIRECTORY}/javafe/parser/test/*.class

testparseidempotence:
	${JAVA} ${P}.TestRccPragmaParser progress check idempotence \
		*.java ../*.java 




