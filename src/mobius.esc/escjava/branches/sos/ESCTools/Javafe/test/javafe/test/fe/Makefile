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
	cat ${SOURCEDIRECTORY}/javafe/parser/test/jdk-files | xargs ${JAVA} javafe.test.PrepTest -classpath ${CLASSPATH}:/udir/stata/src/jdk-alpha/src/share/java -v
