# $Id$

# A simple makefile for working with jmlunit

CLASSPATH='.;c:\cygwin\usr\local\junit\junit.jar'
JML = jml -Q -e
# flags below are for JML common tools release 5.4, adjusting for the future
# JMLC = jmlc -Q -e -o
JMLC = jmlc -Q --universes --neutralContext
JMLRAC = jmlrac
JMLUNIT = jmlunit -i
JAVAC = javac
ESCJAVA = escjava2 -nonNullByDefault -CounterExample

TYPES = ArrayOps BagOfInt

all: compile runtests

check checkall:
	$(JML) $(addsuffix .java,$(TYPES))

esc ESC: $(addsuffix .esc,$(TYPES))

compile: $(addsuffix .class,$(TYPES))

runtests: $(addsuffix _JML_TestData.class,$(TYPES)) \
          $(addsuffix _JML_Test.class,$(TYPES))
	$(JMLC) $(addsuffix .java,$(TYPES))
	for f in $(addsuffix _JML_Test,$(TYPES)); \
	do \
		$(JMLRAC) $f; \
	done

%.esc: %.java
	$(ESCJAVA) $< 

generate: $(addsuffix _JML_TestData.java,$(TYPES)) \
          $(addsuffix _JML_Test.java,$(TYPES))

%_JML_TestData.class: %_JML_TestData.java
	javac $<

%_JML_Test.class: %_JML_Test.java 
	javac $<

%.class: $(addsuffix .java,%)
	$(JMLC) $<

%_JML_TestData.java: %.java
	$(JMLUNIT) $<

%_JML_Test.java: %.java
	$(JMLUNIT) $<

clean: cleanclasses

cleanclasses:
	rm -f *.class
