# Copyright 2000, 2001, Compaq Computer Corporation

# Need to source setup before calling gnumake

.PHONY: all
all: clean escjava doc runtest

# Check that 'source setup' has been run in the Javafe directory:
# if ESCJ is defined, then the following line will fail
.PHONY: sourcecheck
sourcecheck:
	@if [ ! ${ESCJAVA_ROOT} ]; then \
	  echo "You must source the 'setup[.sh]' script before running make."; \
	  false; \
	fi

.PHONY: zip
zip: 
	rm -f ${CLASSDIRECTORY}/escjava.zip
	rm -f ${CLASSDIRECTORY}/decsrc
	rm -rf ${CLASSDIRECTORY}/javafe
	ln -s ${SRCCLASSDIRECTORY}/decsrc ${CLASSDIRECTORY}/decsrc
	ln -s $(JAVAFE_ROOT)/classes/javafe ${CLASSDIRECTORY}/javafe
	cd ${CLASSDIRECTORY}; jar -cf0 escjava.zip decsrc javafe escjava
	rm -f ${CLASSDIRECTORY}/decsrc
	rm -f ${CLASSDIRECTORY}/javafe

.PHONY: source
source:
	cd java/escjava; ${MAKE} source

.PHONY: clean
clean: cleanclasses
	cd java/escjava; ${MAKE} clean
	cd test; ${MAKE} clean
	cd test/escjava/test; ${MAKE} clean
	rm -f doc/escjava.html doc/man1/*.1
	find doc/javadoc -name "*.html" -exec rm -f {} \;
	find . -name mon.out -exec rm -f {} \;
	rm -f ${CLASSDIRECTORY}/escjava.zip ${CLASSDIRECTORY}/javafe
	rm -f ${CLASSDIRECTORY}/compiled.zip

.PHONY: cleanclasses
cleanclasses:
	cd classfiles; find . -name \*.class -exec \rm -f {} \;

.PHONY: doc
doc:	javadoc
	cd java/escjava; ${MAKE} doc

.PHONY: javadoc
javadoc: source
	cd java; \
	${JAVADOC} -classpath ${CLASSPATH} \
	  -sourcepath ${SOURCEDIRECTORY}:${TESTSOURCEDIRECTORY}:${JAVAFE_ROOT}/java \
	  -d ${JAVADOCDIRECTORY} \
          escjava escjava.ast escjava.backpred escjava.parser \
	  escjava.prover escjava.tc escjava.translate \
          javafe javafe.ast javafe.parser  \
	  javafe.reader javafe.genericfile javafe.filespace \
	  javafe.tc javafe.util 

.PHONY: fastdoc
fastdoc: source
	cd java; \
	CLASSPATH="${CLASSPATH}:${JAVAFE_ROOT}/java"; \
	export CLASSPATH; \
	${JAVADOC} -d ${JAVADOCDIRECTORY} \
                escjava escjava.ast escjava.parser escjava.prover escjava.tc

.PHONY: fixdoc
fixdoc:
	find doc/javadoc -name \*.html -exec doc/fixup {} \;

.PHONY: runtest
runtest:
	cd java/escjava; ${MAKE} runtest
	cd test; ${MAKE} runtest
	cd test/escjava/test; ${MAKE} runtest

.PHONY: bigtest
bigtest:
	cd ${ESCJAVA_ROOT}/java/escjava; \
	escjava -nocheck -v \*.java ast/*.java parser/*.java tc/*.java bacpred/*.java prover/*.java

.PHONY: wc
wc:
	cd java/escjava; ${MAKE} wc

.PHONY: depend
depend: source
	cd java; CLASSPATH=${LCLASSPATH} \
		javadepend -g -d ${CLASSDIRECTORY} ${ESCJAVATARGETS} \
		| grep -v /udir/qadeer > ../sources

.PHONY: escjava
escjava: source
	cd java; \
	javac -g -classpath ${CLASSPATH}:${SOURCEDIRECTORY}:${JAVAFE_CLASSFILES} \
	-d ${CLASSDIRECTORY} `find escjava -name "*.java"`

.PHONY: compile
compile: escjava
# 	(cd classfiles; swift -O2  ${ESCTOOLS_JARS}/javafe.jar \
# 		`sed 's/\.java/\.class/' ../sources` \
# 		-o ${CLASSDIRECTORY}/compiled.zip)

