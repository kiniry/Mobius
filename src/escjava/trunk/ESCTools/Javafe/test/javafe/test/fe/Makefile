# Copyright 2000, 2001, Compaq Computer Corporation

runtest: diffs

all: outputs javac diffs compare summary

outputs:
	make_outputs

javac:
	make_javac

diffs: outputs
	make_diffs

compare: outputs javac
	make_comparsions

summary: test*
	make_summary

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
