# Copyright 2000, 2001, Compaq Computer Corporation

# Need to source setup before calling gnumake

all: clean depend rcc doc runtest prot

zip: 
	rm -f ${CLASSDIRECTORY}/rcc.zip
	rm -rf ${CLASSDIRECTORY}/javafecompile
	ln -s $(JAVAFE_ROOT)/classes/javafe ${CLASSDIRECTORY}/javafe
	cd ${CLASSDIRECTORY}; jar -cf0 rcc.zip javafe rcc
	rm -f ${CLASSDIRECTORY}/javafe

source:	
	$(MAKE) -C java/rcc source

clean: cleanclasses
	$(MAKE) -C java/rcc clean
	find -name mon.out | xargs rm -f
	rm -f ${CLASSDIRECTORY}/rcc.zip ${CLASSDIRECTORY}/javafe

cleanclasses:
	cd classes && find . -name \*.class -exec \rm -f {} \;

prot:
	chmod -fR a+rwX .

doc:	
	javadoc
	cd java/rcc; ${MAKE} doc

javadoc: source
	cd java; \
	CLASSPATH="${CLASSPATH}:${JAVAFE_ROOT}/java"; \
	export CLASSPATH; \
	${JAVADOC} -d ${JAVADOC_GEN_DIR} -package \
                rcc rcc.ast  rcc.parser \
                javafe javafe.ast javafe.parser  \
		javafe.reader javafe.genericfile javafe.filespace \
		javafe.tc javafe.util

fastdoc: source
	cd java; \
	CLASSPATH="${CLASSPATH}:${JAVAFE_ROOT}/java"; \
	export CLASSPATH; \
	${JAVADOC} -d ${JAVADOC_GEN_DIR} \
                rcc rcc.ast rcc.parser rcc.tc

fixdoc:
	find doc/javadoc -name \*.html -exec doc/fixup {} \;


runtest:
	cd java/rcc; ${MAKE} runtest

bigtest:
	cd ${RCC_ROOT}/java/rcc; \
	rcc -nocheck -v \*.java ast/*.java parser/*.java tc/*.java 

wc:
	cd java/rcc; ${MAKE} wc


#
# Code for fast incremental recompilation of rcc:
#

RCCTARGETS =	rcc.Main  \
		rcc.ast.CloneWithSubstitution \
		rcc.ast.EqualsAST \
		rccwizard.Main \
		escwizard.AnnotationInserter \
		tohtml.Java2Html\
		rccwizard.AnnLinks


#depend: source
#	cd java; CLASSPATH=${LCLASSPATH} \
#		javadepend -d ${CLASSDIRECTORY} ${RCCTARGETS} \
#		> ../sources

#rcc: source		# depend
#	cd java; \
#		javamake -d ${CLASSDIRECTORY} `cat ../sources`

depend:


rcc:	source
	cd java; \
	${JAVAC} -d ${CLASSDIRECTORY} \
	./rcc/Main.java \
	./rcc/RccOptions.java \
	./rcc/ast/CloneWithSubstitution.java\
	./rcc/ast/EqualsAST.java\
	./rccwizard/Main.java\
	./escwizard/AnnotationInserter.java\
	./rccwizard/AnnLinks.java\
	./rcc/ast/NoWarn.java\
	./rcc/ast/RccPrettyPrint.java\
	./rcc/ast/TagConstants.java\
	./rcc/parser/RccPragmaParser.java\
	./rcc/tc/TypeCheck.java\
	./rcc/tc/TypeSig.java\
	./rcc/tc/Types.java\
	./rcc/ast/CloneAST.java\
	./rcc/ast/MultipleSubstitution.java\
	./rcc/ast/EqualityVisitorSuper.java\
	./rcc/ast/EqualsASTNoDecl.java\
	./rccwizard/AnnotationVisitor.java\
	./escwizard/FileCollection.java\
	./escwizard/FileInfo.java\
	./escwizard/Instr.java\
	./escwizard/WorkItem.java\
	./rcc/ast/NowarnPragma.java\
	./rcc/ast/ArrayGuardModifierPragma.java\
	./rcc/ast/GeneratedTags.java\
	./rcc/ast/GuardedByModifierPragma.java\
	./rcc/ast/HoldsStmtPragma.java\
	./rcc/ast/RequiresModifierPragma.java\
	./rcc/ast/ThreadLocalStatusPragma.java\
	./rcc/ast/GenericArgumentPragma.java\
	./rcc/ast/GenericParameterPragma.java\
	./rcc/ast/ReadOnlyModifierPragma.java\
	./rcc/parser/ErrorPragmaParser.java\
	./rcc/parser/PragmaLex.java\
	./rcc/tc/FlowInsensitiveChecks.java\
	./rcc/tc/PrepTypeDeclaration.java\
	./rcc/tc/PrepPart.java\
	./rcc/tc/GhostEnv.java\
	./rcc/ast/CloneVisitorSuper.java\
	./rcc/ast/Substitution.java\
	./rcc/ast/SubstitutionVec.java\
	./rcc/ast/GhostDeclPragma.java\
	./rcc/ast/VisitorArgResult.java\
	./rccwizard/Annotator.java\
	./escwizard/NowarnInstr.java\
	./escwizard/PragmaInstr.java\
	./rcc/ast/Visitor.java\
	./rcc/ast/CloneForInstantiation.java\
	./rcc/ast/ErrorMsg.java\
	./rcc/tc/LockStack.java\
	./rcc/tc/EnvForInstantiation.java\
	./rcc/tc/Instantiation.java\
	./rcc/tc/InstantiationVec.java\
	./rcc/ast/IntegerVec.java
