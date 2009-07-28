# Copyright 2000, 2001, Compaq Computer Corporation

all: source
	javac -d ${CLASSDIRECTORY} *.java

full: source
#	javac -d ${CLASSDIRECTORY} *.java

source:
	echo Nothing to do

clean: 
	cd test; ${MAKE} clean
	rm -f *~
	rm -rf *.class ${CLASSDIRECTORY}/escjava/parser/*.class

runtest:
	cd test; ${MAKE} runtest
