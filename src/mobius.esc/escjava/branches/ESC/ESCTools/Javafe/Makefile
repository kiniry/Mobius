# Copyright 2000, 2001, Compaq Computer Corporation

# Need to source setup before calling gnumake

all: clean depend javafe javadoc runtest


install: clean depend javafe javadoc prot zip

classdirCheck:
	# Check that 'source setup' has been run in the Javafe directory:
	# if ESCJ is defined, then the following line will fail
	expandpath .${ESCJ}${ESCJ}${ESCJ}

zip: classdirCheck
	rm -f ${CLASSDIRECTORY}/javafe.zip
	cd ${CLASSDIRECTORY}; jar -cf0 javafe.zip javafe tohtml
	chmod a+rw ${CLASSDIRECTORY}/javafe.zip

prot:
	chmod -fR a+rwX .
	find /src/escjava/CVS -exec chmod -f a+rwX {} \;

source:
	cd astgen;			${MAKE}
	cd java/javafe/ast; 		${MAKE} source
	cd java/javafe/tc; 		${MAKE} source


clean: cleanclasses classdirCheck
	rm -f ${CLASSDIRECTORY}/compiled.zip
	cd doc/javadoc; rm -f *.html
	cd java/javafe/ast;         	${MAKE} clean
	cd java/javafe/parser/test; 	${MAKE} clean
	cd java/javafe/tc;          	${MAKE} clean
	cd java/javafe/test;        	${MAKE} clean
	cd java/jtools; 	    	${MAKE} clean
	cd astgen; 		    	${MAKE} clean

cleanclasses:
	cd classes; find . -name \*.class | xargs rm -f
	rm -f classes/.javamake


jtools:	javafe
	cd java/jtools; ${MAKE}

doc:	javadoc

javadoc: source 
	cd java; \
        ${JAVADOC} -d ${JAVADOCDIRECTORY} \
                javafe javafe.ast javafe.parser  \
		javafe.reader javafe.genericfile javafe.filespace \
		javafe.tc javafe.util \
		jtools.jwhich jtools.jls
#		jtools.jcheck \
#		jtools.jcheck.parseTypes


runtest:
	cd java/javafe/parser/test; 	${MAKE} runtest
	cd java/javafe/util; 		${MAKE} runtest
	cd java/javafe/test; 		${MAKE} runtest


OTHERSOURCEFILES = astgen/ast*.c astgen/ast*.h astgen/ast*.l
TESTHARNESSFILES = java/javafe/parser/test/Test*.java java/javafe/test/*.java

wc:
	# --- Non-java Source files ---
	wc ${OTHERSOURCEFILES}
	# --- Java Source files ---
	wc ${SOURCEFILES}
	${JAVA} javafe.CountLines ${JAVASOURCEFILES}
	# jrun javafe.parser.test.TestParse print ${JAVASOURCEFILES} | wc
	# --- Test harness files ---
	wc ${TESTHARNESSFILES}
	${JAVA} javafe.CountLines ${TESTHARNESSFILES}
	# jrun javafe.parser.test.TestParse print ${TESTHARNESSFILES} | wc


#
# Code for fast incremental recompilation of javafe:
#

JAVAFETARGETS = javafe.ast.DefaultVisitor		\
		javafe.filespace.Resolve		\
		javafe.CountLines			\
		javafe.TestTool				\
		javafe.test.Print			\
		javafe.test.SuperlinksTest		\
		javafe.test.SupertypeTest		\
		javafe.test.CountFilesLoaded		\
		javafe.test.LocTool			\
		javafe.test.lex.TestLex			\
		javafe.parser.test.TestLex		\
		javafe.parser.test.TestExpr		\
		javafe.parser.test.TestParse		\
		javafe.util.CorrelatedReaderTest	\
		javafe.util.FilterCorrelatedReader	\
		tohtml.DeclLinks			\
		tohtml.Java2Html			\
		javafe.ast.Util				\
		javafe.PrintSpec			\
		javafe.CopyLoaded

depend: source classdirCheck
	cd java; CLASSPATH=${LCLASSPATH} \
		javadepend -d ${CLASSDIRECTORY} ${JAVAFETARGETS} \
		| egrep -v '^/' > ../sources

javafe: source classdirCheck		# depend
	cd java; \
		javac -d ${CLASSDIRECTORY} `cat ../sources`

compile: javafe zip classdirCheck
	swift -O2 ${CLASSDIRECTORY}/javafe.zip -o ${CLASSDIRECTORY}/compiled.zip

esc: source
	cd java; \
	date; \
	escjava -classpath ${CLASSPATH} -f ../sources; \
	date
