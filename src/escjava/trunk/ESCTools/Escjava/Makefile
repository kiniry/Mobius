# Copyright 2000, 2001, Compaq Computer Corporation

# Need to source setup before calling gnumake

all: clean depend escjava doc runtest

zip: 
	rm -f ${CLASSDIRECTORY}/escjava.zip
	rm -f ${CLASSDIRECTORY}/decsrc
	rm -rf ${CLASSDIRECTORY}/javafe
	ln -s ${SRCCLASSDIRECTORY}/decsrc ${CLASSDIRECTORY}/decsrc
	ln -s $(JAVAFE_ROOT)/classes/javafe ${CLASSDIRECTORY}/javafe
	cd ${CLASSDIRECTORY}; jar -cf0 escjava.zip decsrc javafe escjava
	rm -f ${CLASSDIRECTORY}/decsrc
	rm -f ${CLASSDIRECTORY}/javafe

source:
	cd java/escjava; ${MAKE} source

clean: cleanclasses
	cd java/escjava; ${MAKE} clean
	cd test; ${MAKE} clean
	rm -f doc/escjava.html doc/man1/*.1
	cd doc/javadoc; rm -f *.html
	find . -name mon.out -exec rm -f {} \;
	rm -f ${CLASSDIRECTORY}/escjava.zip ${CLASSDIRECTORY}/javafe
	rm -f ${CLASSDIRECTORY}/compiled.zip

cleanclasses:
	cd classes; find . -name \*.class -exec \rm -f {} \;

doc:	javadoc
	cd java/escjava; ${MAKE} doc

#
# JBKBINARIES added here as a kludge to make sure javadoc sees java.util.Arrays
#
javadoc: source
	cd java; \
	${JAVADOC} -d ${JAVADOCDIRECTORY} \
		-sourcepath ${CLASSPATH}:${JAVAFE_ROOT}/java:${JDKBINARIES} \
		-package \
                escjava escjava.ast escjava.backpred escjava.parser \
		escjava.prover escjava.tc escjava.translate \
                javafe javafe.ast javafe.parser  \
		javafe.reader javafe.genericfile javafe.filespace \
		javafe.tc javafe.util 

fastdoc: source
	cd java; \
	CLASSPATH="${CLASSPATH}:${JAVAFE_ROOT}/java"; \
	export CLASSPATH; \
	${JAVADOC} -d ${JAVADOCDIRECTORY} \
                escjava escjava.ast escjava.parser escjava.prover escjava.tc

fixdoc:
	find doc/javadoc -name \*.html -exec doc/fixup {} \;


runtest:
	cd java/escjava; ${MAKE} runtest
	cd test; ${MAKE} runtest

houdinitest:
	cd java/houdini/test; ${MAKE} runtest

bigtest:
	cd ${ESCJAVA_ROOT}/java/escjava; \
	escjava -nocheck -v \*.java ast/*.java parser/*.java tc/*.java bacpred/*.java prover/*.java

wc:
	cd java/escjava; ${MAKE} wc


#
# Code for fast incremental recompilation of escjava:
#

ESCJAVATARGETS =	escjava.Main				\
			escjava.parser.test.TestLex		\
			escjava.parser.test.TestEscPragmaParser \
			escwizard.AnnotationInserter		\
			houdini.Main				\
			houdini.AnnLinks			\
			tohtml.DeclLinks			\
			instrumenter.Main			\
			houdini.CopyLoaded			\
			escjava.prover.SimplifyTest		


depend: source
	cd java; CLASSPATH=${LCLASSPATH} \
		javadepend -g -d ${CLASSDIRECTORY} ${ESCJAVATARGETS} \
		| grep -v /udir/qadeer > ../sources

escjava: source		# depend
	cd java; \
		javac -g -d ${CLASSDIRECTORY} `cat ../sources`


compile: escjava
	(cd classes; swift -O2  ${ESCTOOLS_JARS}/javafe.jar \
		`sed 's/\.java/\.class/' ../sources` \
		-o ${CLASSDIRECTORY}/compiled.zip)

