all: source
	javac -d ${CLASSDIRECTORY} *.java

full: source
	$(JAVAC) -d ${CLASSDIRECTORY} *.java

source:
	echo Nothing to do

clean: 
	rm -f *~
	rm -rf *.class ${CLASSDIRECTORY}/escjava/parser/*.class

runtest:
	cd ${TESTSOURCEDIRECTORY}/escjava/parser/test; ${MAKE} runtest
