# Copyright 2000, 2001, Compaq Computer Corporation
# Copyright 2003 University of Nijmegen
# Copyright 2003 David R. Cok
# This file is extensively revised in the 2003 ESC revision.

export TOP = ..
include ${TOP}/Makefile.defs
# Must define:	ESCJAVA_ROOT, JAVAFE_ROOT, JAVAC, JAVAC_FLAGS

# Various conventional UNIX tools are used in the following, including
# cc in preprocess only mode.  Also, the "astgen" and "astfilelist"
# programs in Javafe are used here.

###########################################################################
# Defining relevant directory locations and other variables.

ESCJAVA_SOURCE_DIR = $(ESCJAVA_ROOT)/java
JAVASOURCEFILES = $(ESCJAVA_SOURCE_DIR)/escjava/ast/*.java \
	$(ESCJAVA_SOURCE_DIR)/escjava/backpred/*.java \
	$(ESCJAVA_SOURCE_DIR)/escjava/parser/*.java \
	$(ESCJAVA_SOURCE_DIR)/escjava/prover/*.java \
	$(ESCJAVA_SOURCE_DIR)/escjava/reader/*.java \
	$(ESCJAVA_SOURCE_DIR)/escjava/sp/*.java \
	$(ESCJAVA_SOURCE_DIR)/escjava/tc/*.java \
	$(ESCJAVA_SOURCE_DIR)/escjava/translate/*.java \
	$(ESCJAVA_SOURCE_DIR)/escjava/*.java
OTHERSOURCEFILES = /dev/null
TESTHARNESSFILES = /dev/null


export CLASSDIRECTORY=${ESCJAVA_ROOT}/classfiles
export SOURCEDIRECTORY=${ESCJAVA_ROOT}/java
export TESTSOURCEDIRECTORY=${ESCJAVA_ROOT}/test

## FIXME - check and fix this
ESCJAVA_CLASSPATH ?= $(JAVAFE_ROOT)/classfiles:$(CLASSDIRECTORY):$(ESCJAVA_ROOT)/jars/mochalib.jar:$(ESCJAVA_ROOT)/jars/javafe.jar:$(ESCJAVA_ROOT)/jars/escjava.jar:$(ESCJAVA_ROOT)/jars/decsrc.jar:..:.:

## FIXME -- add onto theprevious path ???  SOURCEPATH???
JAVAC_FLAGS = -g -classpath $(ESCJAVA_CLASSPATH) \
	-sourcepath $(SOURCEPATH) \
	-d $(CLASSDIRECTORY) 

###########################################################################
.PHONY: all
all: clean build docs test

.PHONY: build
build: compile

.PHONY: buildall
buildall: compileall

.PHONY: test
test: test_escjava



###########################################################################
# Documentation targets.

# mtex2man and mtex2html are not generally available so we turn this
# off for now - FIXME
.PHONY: docs
#docs: docs_escjava
docs:

ESCJAVA_CORE_DOC = $(ESCJAVA_ROOT)/java/escjava/escjava.mtex

.PHONY: docs_escjava
docs_escjava:	$(ESCJAVA_CORE_DOC)
	cc -C -E $(ESCJAVA_CORE_DOC) | grep -v "^#" | mtex2man \
		> $(ESCJAVA_ROOT)/doc/man1/escjava.1
	cc -C -E $(ESCJAVA_CORE_DOC) | grep -v "^#" | mtex2html \
		> $(ESCJAVA_ROOT)/doc/escjava.html
	cc -C -E -DPUBLIC $(ESCJAVA_CORE_DOC) | grep -v "^#" | mtex2man \
		> $(ESCJAVA_ROOT)/doc/man1/escjava-public.1
	cc -C -E -DPUBLIC $(ESCJAVA_CORE_DOC) | grep -v "^#" | mtex2html \
		> $(ESCJAVA_ROOT)/doc/escjava-public.html


###########################################################################
# Compilation targets.

STAMPFILE = classes.stamp

## These targets must be in the given order.  We use classes.stamp
## instead of allclasses here to enable incremental builds.  This
## incremental compilation is not robust - removing individual .class
## files will cause not everything to be built.  Also sometimes .java
## files ought to be recompiled if dependencies change, even if the
## file has not been modified.  If in doubt do a clean before a build
## - it doesn't take long.
.PHONY: compile
compile: $(CLASSDIRECTORY) generate_files $(STAMPFILE)

.PHONY: compileall
compileall: $(CLASSDIRECTORY) generate_files allclasses

.PHONY: allclasses
allclasses:
	@$(JAVAC) $(JAVAC_FLAGS) $(JAVASOURCEFILES)
	touch $(STAMPFILE)

$(STAMPFILE): $(JAVASOURCEFILES)
	$(JAVAC) $(JAVAC_FLAGS) $?
	touch $@

$(CLASSDIRECTORY):
	mkdir -p $@

.PHONY: generate_files
generate_files: generate_escjava_ast_source generate_escjava_backpred

###########################################################################
# source file generation for escjava.ast

AST_DIR = $(ESCJAVA_SOURCE_DIR)/escjava/ast
JAVAFE_AST_DIR = $(JAVAFE_ROOT)/java/javafe/ast

# Dependence on Javafe astgen programs:

ASTGEN = $(JAVAFE_ROOT)/astgen/astgen
ASTFILELIST = $(JAVAFE_ROOT)/astgen/astfilelist

$(ASTFILELIST) $(ASTGEN):
	${MAKE} -C $(JAVAFE_ROOT)/astgen

# Generating Java files:

VECTEMPLATE = $(JAVAFE_ROOT)/java/javafe/util/_TYPE_Vec.j

# The component type for these (e.g. FieldDecl.java) is in Javafe.
JavafeTypeVec = \
	$(AST_DIR)/FieldDeclVec.java $(AST_DIR)/LocalVarDeclVec.java \
	$(AST_DIR)/GenericVarDeclVec.java

# The component type for these (e.g. GuardedCmd.java) is in Escjava.
TypeVec = \
	$(AST_DIR)/GuardedCmdVec.java  \
	$(AST_DIR)/ConditionVec.java  \
	$(AST_DIR)/ExprModifierPragmaVec.java \
	$(AST_DIR)/CondExprModifierPragmaVec.java \
	$(AST_DIR)/ExprDeclPragmaVec.java \
	$(AST_DIR)/ExprStmtPragmaVec.java \
	$(AST_DIR)/VarExprModifierPragmaVec.java \
	$(AST_DIR)/DefPredVec.java \
	$(AST_DIR)/DecreasesInfoVec.java

.PHONY: generate_escjava_ast_source
generate_escjava_ast_source: $(AST_DIR)/GeneratedTags.java $(TypeVec) $(JavafeTypeVec)

# FIXME - ought to make these depend on the component type.
$(AST_DIR)/%Vec.java: $(VECTEMPLATE)
	@if [ -e $(ESCJAVA_ROOT)/java/escjava/ast/$*.java ]; then \
		sed s/_TYPE_/$*/g $(VECTEMPLATE) | \
		sed s/_PKG_/escjava.ast/g              | \
		sed s/_COMPONENTPKG_/escjava.ast/g > $@ ;\
	elif [ -e $(JAVAFE_ROOT)/java/javafe/ast/$*.java ]; then \
		sed s/_TYPE_/$*/g $(VECTEMPLATE) | \
		sed s/_PKG_/escjava.ast/g              | \
		sed s/_COMPONENTPKG_/javafe.ast/g > $@ ;\
	else \
		echo "Could not find component for $@" ;\
	fi


# This also generates all the .java files implied by "hierarchy.j".
$(AST_DIR)/GeneratedTags.java: $(ASTGEN) $(AST_DIR)/hierarchy.j
	@(cd $(AST_DIR); $(ASTGEN) < hierarchy.j; \
	grep -v "//@" AnOverview.java > AnOverview.tmp; \
	mv AnOverview.tmp AnOverview.java; \
	grep -v "//@" GCExpr.java > GCExpr.tmp; \
	mv GCExpr.tmp GCExpr.java; \
	grep -v "//@" GuardedCmd.java > GuardedCmd.tmp; \
	mv GuardedCmd.tmp GuardedCmd.java)
## The above grep's etc. are a kludge and ought to be fixed. - FIXME

.PHONY: clean_escjava_ast
clean_escjava_ast: $(ASTFILELIST)
	(cd $(AST_DIR); rm -f `$(ASTFILELIST) < $(AST_DIR)/hierarchy.j`)
	rm -f *~ $(TypeVec) $(JavafeTypeVec) $(AST_DIR)/ASTGEN* $(AST_DIR)/zASTGEN* *.tmp
	rm -f $(AST_DIR)/*.class $(CLASSDIRECTORY)/escjava/ast/*.class


###########################################################################
## Generating the source files in backpred.

BACKPRED_DIR = $(ESCJAVA_SOURCE_DIR)/escjava/backpred
DEFAULT_UNIV_BACKPRED = $(BACKPRED_DIR)/DefaultUnivBackPred.java

.PHONY: generate_escjava_backpred
generate_escjava_backpred: $(DEFAULT_UNIV_BACKPRED)

$(DEFAULT_UNIV_BACKPRED): $(BACKPRED_DIR)/UnivBackPred.ax
	@rm -f $(DEFAULT_UNIV_BACKPRED)
	@echo 'package escjava.backpred;' > $(DEFAULT_UNIV_BACKPRED)
	@echo 'class DefaultUnivBackPred {' >> $(DEFAULT_UNIV_BACKPRED)
	@echo '  static String s =' >> $(DEFAULT_UNIV_BACKPRED)
	@sed -e 's/"/\\"/g' \
	  -e 's/^/    "/' \
	  -e 's/$$/\\n" +/' \
	  $(BACKPRED_DIR)/UnivBackPred.ax >> $(DEFAULT_UNIV_BACKPRED)
	@echo '    "";' >> $(DEFAULT_UNIV_BACKPRED)
	@echo '}' >> $(DEFAULT_UNIV_BACKPRED)

.PHONY: clean_escjava_backpred
clean_escjava_backpred:
	rm -f $(DEFAULT_UNIV_BACKPRED)

###########################################################################
# Clean targets.
## FIXME - Check all these

.PHONY: clean clean_escjava clean_tests clean_classfiles \
	clean_docs clean_javadocs clean_misc clean_jars cleanarchives

clean: clean_classfiles clean_docs clean_escjava clean_tests \
	clean_misc clean_jars clean_archives

clean_escjava: clean_escjava_ast clean_escjava_backpred 

clean_tests: clean_escjava_parser_test clean_test_escjava

clean_classfiles:
	rm -rf $(CLASSDIRECTORY)

clean_docs: clean_javadocs
	rm -f doc/escjava.html doc/escjava-public.html doc/man1/*.1

clean_javadocs:
	rm -rf $(JAVADOCDIR)

clean_misc:
	rm -f $(STAMPFILE)
	find . -name mon.out -exec rm -f {} \;
	rm -f ${TESTSOURCEDIRECTORY}/escjava/test/*/log ${TESTSOURCEDIRECTORY}/matrix/log
	find . -name 'core.*' -exec rm -f {} \;

clean_jars:
#	rm -f $(ESCTOOLS_JARS)/*.jar

clean_archives:
	rm -f $(CLASSDIRECTORY)/escjava.zip $(CLASSDIRECTORY)/javafe.zip
	rm -f $(CLASSDIRECTORY)/compiled.zip

###########################################################################
# Deliverable generation targets.

## FIXME - check this out - move it one level up???

archives: archive_esctools
	cd $(ESCTOOLS_ROOT); \
	tar cjf $(PROJECT)-$(VERSION).tbz $(PROJECT)

jars: jar_javafe jar_escjava #jar_escjava_complete

jar_javafe: #compile_javafe

jar_escjava: compile_escjava
	cd $(CLASSDIRECTORY); \
	jar -cf0 $(ESCTOOLS_JARS)/escjava.jar escjava

jar_escjava_complete: compile_escjava
	cd $(CLASSDIRECTORY); \
	jar -cf0 $(ESCTOOLS_JARS)/escjava.jar decsrc javafe escjava

###########################################################################
# Testing targets.

TOP_ESCJAVA_TEST_DIR = $(TESTSOURCEDIRECTORY)/escjava/test

.PHONY: self_test test_escjava_parser

self_test: compile
	cd $(ESCJAVA_SOURCE_DIR)/escjava; \
	escjava -nocheck -v \*.java ast/*.java parser/*.java \
	  tc/*.java bacpred/*.java prover/*.java

test_escjava: build build_javafe_test test_escjava_parser clean_test_escjava
	(cd $(TOP_ESCJAVA_TEST_DIR); \
	rtestall)

.PHONY: build_javafe_test
build_javafe_test:
	make -C ${JAVAFE_ROOT} javafe_test

clean_test_escjava:
	(cd $(TOP_ESCJAVA_TEST_DIR); \
	rm -f test*/out test*/diff)

test_matrix:
	(cd $(TESTSOURCEDIRECTORY)/matrix; \
	escjava *.java;)


###########################################################################
## parser test targets

test_parser: test_escjava_parser test_matrix self_test

PARSER_TEST_PACKAGE = escjava.parser.test
PARSER_TEST_DIR = $(TESTSOURCEDIRECTORY)/escjava/parser/test

test_escjava_parser: compile_escjava_parser_test_programs \
		test_lexer test_parser test_parser_idempotence

compile_escjava_parser_test_programs:
	$(JAVAC) $(JAVAC_FLAGS) \
		$(PARSER_TEST_DIR)/TestLex.java \
		$(PARSER_TEST_DIR)/TestEscPragmaParser.java

clean_escjava_parser_test:
	rm -f $(PARSER_TEST_DIR)/*.out
	rm -f $(CLASSDIRECTORY)/javafe/parser/test/*.class

test_lexer: compile_escjava_parser_test_programs
	(cd $(PARSER_TEST_DIR); \
	$(JAVA) $(PARSER_TEST_PACKAGE).TestLex GoodPragmas.j | diff - GoodPragmas.ans; \
	$(JAVA) $(PARSER_TEST_PACKAGE).TestLex GoodSpecExpr.j | diff - GoodSpecExpr.ans; \
	$(JAVA) $(PARSER_TEST_PACKAGE).TestLex GoodJmlPragmas.j | diff - GoodJmlPragmas.ans; \
	$(JAVA) $(PARSER_TEST_PACKAGE).TestLex lookahead GoodPragmas.j | diff - GoodPragmas.ans; \
	$(JAVA) $(PARSER_TEST_PACKAGE).TestLex lookahead GoodSpecExpr.j | diff - GoodSpecExpr.ans; \
	$(JAVA) $(PARSER_TEST_PACKAGE).TestLex lookahead GoodJmlPragmas.j | diff - GoodJmlPragmas.ans)

test_parser: compile_escjava_parser_test_programs
	(cd $(PARSER_TEST_DIR); \
	$(JAVA) $(PARSER_TEST_PACKAGE).TestEscPragmaParser print \
		TypeDeclElemPragmas1.java | \
		diff - TypeDeclElemPragmas1.ans)

test_parser_idempotence: compile_escjava_parser_test_programs
	(cd $(PARSER_TEST_DIR); \
	$(JAVA) $(PARSER_TEST_PACKAGE).TestEscPragmaParser progress check idempotence \
		*.java $(SOURCEDIRECTORY)/escjava/ast/*.java)


###########################################################################
# Miscellaneous targets.

.PHONY: word_count

# Roughly counting size of source.

word_count:
# --- Non-java Source files ---
	wc $(OTHERSOURCEFILES)
# --- Java Source files ---
	wc $(JAVASOURCEFILES)
	java javafe.parser.test.TestParse print $(JAVASOURCEFILES) | wc
# --- Test harness files ---
	wc $(TESTHARNESSFILES)
	java javafe.parser.test.TestParse print $(TESTHARNESSFILES) | wc

# @todo Add javancss count here as well.


