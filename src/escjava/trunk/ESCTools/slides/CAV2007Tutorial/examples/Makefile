# $Id$

# A simple makefile for working with jmlunit

CLASSPATH=.
JML = jml -Q -e
JMLC = jmlc -Q -e
JMLRAC = jmlrac
JMLUNIT = jmlunit -i

TYPES = ArrayFind

all: compile runtests

check:
	$(JML) $(addsuffix .java,$(TYPES))

compile: $(addsuffix .class,$(TYPES))

%.class:	$(addsuffix .java,%)
		$(JMLC) $<

runtests: ArrayFind_JML_TestData.class ArrayFind_JML_Test.class
	$(JMLC) $(addsuffix .java,$(TYPES))
	$(JMLRAC) ArrayFind_JML_Test

ArrayFind_JML_TestData.class: ArrayFind_JML_TestData.java
	javac ArrayFind_JML_TestData.java

ArrayFind_JML_Test.class: ArrayFind_JML_Test.java 
	javac ArrayFind_JML_Test.java

generate: ArrayFind_JML_TestData.java ArrayFind_JML_Test.java

ArrayFind_JML_TestData.java: ArrayFind.java 
	$(JMLUNIT) ArrayFind.java

ArrayFind_JML_Test.java: ArrayFind.java Lift.java LiftType.java
	$(JMLUNIT) ArrayFind.java

clean: cleanclasses

cleanclasses:
	rm -f *.class
