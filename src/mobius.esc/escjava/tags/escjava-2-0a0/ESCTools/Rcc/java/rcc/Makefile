# Copyright 2000, 2001, Compaq Computer Corporation

class:	source
	${JAVAC} -d ${CLASSDIRECTORY} Root.java

full:	source
	cd ast; ${MAKE} full
	cd parser; ${MAKE} full
	cd tc; ${MAKE} full
	${JAVAC} -d ${CLASSDIRECTORY} *.java

source:
	cd ast; ${MAKE} source
	cd parser; ${MAKE} source
	cd tc; ${MAKE} source

clean:
	cd ast; ${MAKE} clean
	cd parser; ${MAKE} clean
	cd tc; ${MAKE} clean
	cd test; ${MAKE} clean
	rm -f *~ -rf *.class ${CLASSDIRECTORY}/rcc/*.class

runtest:
	cd ast; ${MAKE} runtest
	cd parser; ${MAKE} runtest
	cd test; ${MAKE} runtest
	cd tc; ${MAKE} runtest

doc:    doc/rccjava.mtex
	mtex2man < doc/rccjava.mtex > ${RCC_ROOT}/doc/man1/escjava.1
	mtex2html < doc/rccjava.mtex > ${RCC_ROOT}/doc/escjava.html

# Counting size of source

JAVASOURCEFILES = ast/*.java parser/*.java prover/*.java tc/*.java translate/*.java
OTHERSOURCEFILES = 
TESTHARNESSFILES = 

wc:
	# --- Non-java Source files ---
	wc ${OTHERSOURCEFILES}
	# --- Java Source files ---
	wc ${JAVASOURCEFILES}
	jrun javafe.parser.test.TestParse print ${JAVASOURCEFILES} | wc
	# --- Test harness files ---
	wc ${TESTHARNESSFILES}
	jrun javafe.parser.test.TestParse print ${TESTHARNESSFILES} | wc





