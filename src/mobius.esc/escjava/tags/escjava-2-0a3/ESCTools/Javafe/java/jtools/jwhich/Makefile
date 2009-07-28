# Copyright 2000, 2001, Compaq Computer Corporation

all: man1/jwhich.1 man1/jwhich.html
	${JAVAC} -d ${CLASSDIRECTORY} *.java

clean: 
	rm -f *.class
	rm -f man1/*.1 man1/*.html

.SUFFIXES: .class .java .1 .mtex .html

.mtex.1:
	mtex2man < $*.mtex > $*.1

.mtex.html:
	mtex2html < $*.mtex > $*.html
