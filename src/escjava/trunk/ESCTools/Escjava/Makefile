# Copyright 2000, 2001, Compaq Computer Corporation
# Copyright 2003 University of Nijmegen

# Need to source setup.sh before calling GNU make!

ESCJAVA_SOURCE_DIR = $(ESCJAVA_ROOT)/java
JAVASOURCEFILES = $(ESCJAVA_SOURCE_DIR)/escjava/ast/*.java \
	$(ESCJAVA_SOURCE_DIR)/escjava/parser/*.java \
	$(ESCJAVA_SOURCE_DIR)/escjava/prover/*.java \
	$(ESCJAVA_SOURCE_DIR)/escjava/tc/*.java \
	$(ESCJAVA_SOURCE_DIR)/escjava/translate/*.java
OTHERSOURCEFILES = /dev/null
TESTHARNESSFILES = /dev/null

.PHONY: all everything sourcecheck archives \
	jars jar_javafe jar_escjava_complete \
	docs docs_escjava javadoc

all: clean compile test_escjava

everything: clean compile doc test_escjava test_matrix self_test

# Initialization targets.

# Check that 'source setup' has been run in the Javafe directory:
# if ESCJ is defined, then the following line will fail
sourcecheck:
	@if [ ! $(ESCJAVA_ROOT) ]; then \
	  echo "You must source the 'setup[.sh]' script before running make."; \
	  false; \
	fi

###########################################################################
# Deliverable generation targets.

PROJECT = ESCTools
VERSION = February-2003

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

# Documentation targets.

docs: docs_escjava

ESCJAVA_CORE_DOC = $(ESCJAVA_ROOT)/java/escjava/escjava.mtex

docs_escjava:	$(ESCJAVA_CORE_DOC)
	cc -C -E $(ESCJAVA_CORE_DOC) | grep -v "^#" | mtex2man \
		> $(ESCJAVA_ROOT)/doc/man1/escjava.1
	cc -C -E $(ESCJAVA_CORE_DOC) | grep -v "^#" | mtex2html \
		> $(ESCJAVA_ROOT)/doc/escjava.html
	cc -C -E -DPUBLIC $(ESCJAVA_CORE_DOC) | grep -v "^#" | mtex2man \
		> $(ESCJAVA_ROOT)/doc/man1/escjava-public.1
	cc -C -E -DPUBLIC $(ESCJAVA_CORE_DOC) | grep -v "^#" | mtex2html \
		> $(ESCJAVA_ROOT)/doc/escjava-public.html

PACKAGE_LIST = escjava escjava.ast escjava.backpred escjava.parser \
	  escjava.prover escjava.tc escjava.translate \
          javafe javafe.ast javafe.parser  \
	  javafe.reader javafe.genericfile javafe.filespace \
	  javafe.tc javafe.util

javadoc: compile
	$(JAVADOC) -sourcepath $(SOURCEPATH) \
	  -d $(JAVADOCDIRECTORY) \
          $(PACKAGE_LIST)

###########################################################################
# Top-level compilation targets.

.PHONY: compile compile_escjava compile_tests

compile compile_escjava: compile_escjava_ast compile_escjava_backpred \
	compile_escjava_parser compile_escjava_prover compile_escjava_tc \
	compile_escjava_translate

compile_tests: compile_escjava_parser_test_programs

###########################################################################
# Clean targets.

.PHONY: clean clean_escjava clean_tests clean_classfiles \
	clean_docs clean_javadocs clean_misc clean_jars cleanªrchives

clean: clean_classfiles clean_docs clean_escjava clean_tests

clean_escjava: clean_escjava_ast clean_escjava_backpred clean_escjava_parser \
	clean_escjava_prover clean_escjava_tc clean_escjava_translate

clean_tests: clean_escjava_parser_test clean_test_escjava

clean_classfiles:
	cd classfiles; find . -name "*.class" -exec rm -f {} \;

clean_docs:
	rm -f doc/escjava.html doc/escjava-public.html doc/man1/*.1

clean_javadocs:
	find doc/javadoc -name "*.html" -exec rm -f {} \;

clean_misc:
	find . -name mon.out -exec rm -f {} \;

clean_jars:
	rm -f $(ESCTOOLS_JARS)/*.jar

clean_archives:
	rm -f $(CLASSDIRECTORY)/escjava.zip $(CLASSDIRECTORY)/javafe
	rm -f $(CLASSDIRECTORY)/compiled.zip

###########################################################################
# Testing targets.

TOP_ESCJAVA_TEST_DIR = $(TESTSOURCEDIRECTORY)/escjava/test

.PHONY: self_test test_escjava_parser

self_test: compile
	cd $(ESCJAVA_SOURCE_DIR)/escjava; \
	escjava -nocheck -v \*.java ast/*.java parser/*.java \
	  tc/*.java bacpred/*.java prover/*.java

test_escjava: compile_escjava test_escjava_parser clean_test_escjava
	(cd $(TOP_ESCJAVA_TEST_DIR); \
	rtestall)

clean_test_escjava:
	(cd $(TOP_ESCJAVA_TEST_DIR); \
	rm -f test*/out test*/diff)

test_matrix:
	(cd $(TOP_ESCJAVA_TEST_DIR)/matrix; \
	escjava *.java;)

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

###########################################################################
# escjava.ast

AST_DIR = $(ESCJAVA_SOURCE_DIR)/escjava/ast

# Dependence on Javafe astgen programs:

ASTGEN = $(JAVAFE_ROOT)/astgen/astgen
ASTFILELIST = $(JAVAFE_ROOT)/astgen/astfilelist

$(ASTFILELIST) $(ASTGEN):
	(cd $(JAVAFE_ROOT)/astgen; $(MAKE))

# Generating Java files:

VECTEMPLATE = $(JAVAFE_ROOT)/java/javafe/util/_TYPE_Vec.j

ESCJAVA_AST_HIERARCHY = $(AST_DIR)/hierarchy.j

TypeVec = \
	$(AST_DIR)/GuardedCmdVec.java $(AST_DIR)/GenericVarDeclVec.java \
	$(AST_DIR)/ConditionVec.java $(AST_DIR)/LocalVarDeclVec.java \
	$(AST_DIR)/ExprModifierPragmaVec.java $(AST_DIR)/ExprDeclPragmaVec.java \
	$(AST_DIR)/ExprStmtPragmaVec.java $(AST_DIR)/FieldDeclVec.java \
	$(AST_DIR)/VarExprModifierPragmaVec.java $(AST_DIR)/DefPredVec.java \
	$(AST_DIR)/LocalVarDeclVec.java $(AST_DIR)/DecreasesInfoVec.java

$(AST_DIR)/FieldDeclVec.java: $(VECTEMPLATE)
	@sed s/_TYPE_/FieldDecl/g $(VECTEMPLATE) | \
        sed s/_PKG_/escjava.ast/g              | \
        sed s/_COMPONENTPKG_/javafe.ast/g > $@

$(AST_DIR)/GenericVarDeclVec.java: $(VECTEMPLATE)
	@sed s/_TYPE_/GenericVarDecl/g $(VECTEMPLATE) | \
        sed s/_PKG_/escjava.ast/g              | \
        sed s/_COMPONENTPKG_/javafe.ast/g > $@

$(AST_DIR)/LocalVarDeclVec.java: $(VECTEMPLATE)
	@sed s/_TYPE_/LocalVarDecl/g $(VECTEMPLATE) | \
        sed s/_PKG_/escjava.ast/g              | \
        sed s/_COMPONENTPKG_/javafe.ast/g > $@

$(AST_DIR)/%Vec.java: $(VECTEMPLATE)
	@sed s/_TYPE_/$*/g $(VECTEMPLATE) | \
        sed s/_PKG_/escjava.ast/g              | \
        sed s/_COMPONENTPKG_/escjava.ast/g > $@

generate_escjava_ast_source: $(AST_DIR)/GeneratedTags.java $(TypeVec) $(ASTGEN)

$(AST_DIR)/GeneratedTags.java: $(ASTGEN) $(ESCJAVA_AST_HIERARCHY)
	(cd $(AST_DIR); $(ASTGEN) < hierarchy.j; \
	grep -v "//@" AnOverview.java > AnOverview.tmp; \
	mv AnOverview.tmp AnOverview.java; \
	grep -v "//@" GCExpr.java > GCExpr.tmp; \
	mv GCExpr.tmp GCExpr.java; \
	grep -v "//@" GuardedCmd.java > GuardedCmd.tmp; \
	mv GuardedCmd.tmp GuardedCmd.java)

ESCJAVA_CLASSPATH ?= $(ESCJAVA_ROOT)/Javafe/classfiles:$(ESCJAVA_ROOT)/Escjava/classfiles:$(ESCJAVA_ROOT)/jars/mochalib.jar:$(ESCJAVA_ROOT)/jars/javafe.jar:$(ESCJAVA_ROOT)/jars/escjava.jar:$(ESCJAVA_ROOT)/jars/decsrc.jar:..:.:

JAVAC_FLAGS = -g -classpath $(ESCJAVA_CLASSPATH) \
	-sourcepath $(SOURCEPATH) \
	-d $(CLASSDIRECTORY) 

compile_escjava_ast: generate_escjava_ast_source generate_escjava_backpred
	$(JAVAC) $(JAVAC_FLAGS) $(AST_DIR)/*.java

clean_escjava_ast: $(ASTFILELIST)
	for file in `$(ASTFILELIST) < $(ESCJAVA_AST_HIERARCHY)`; \
	do \
		rm -f $(AST_DIR)/$$file; \
	done
	rm -f *~ $(TypeVec) $(AST_DIR)/ASTGEN* $(AST_DIR)/zASTGEN* *.tmp
	rm -f $(AST_DIR)/*.class $(CLASSDIRECTORY)/escjava/ast/*.class

###########################################################################
# escjava.backpred

BACKPRED_DIR = $(ESCJAVA_SOURCE_DIR)/escjava/backpred
DEFAULT_UNIV_BACKPRED = $(BACKPRED_DIR)/DefaultUnivBackPred.java

.PHONY: compile_escjava_backpred generate_escjava_backpred clean_escjava_backpred

compile_escjava_backpred: generate_escjava_backpred
	$(JAVAC) $(JAVAC_FLAGS) $(BACKPRED_DIR)/*.java

generate_escjava_backpred:
	rm -f $(DEFAULT_UNIV_BACKPRED)
	echo 'package escjava.backpred;' > $(DEFAULT_UNIV_BACKPRED)
	echo 'class DefaultUnivBackPred {' >> $(DEFAULT_UNIV_BACKPRED)
	echo '  static String s =' >> $(DEFAULT_UNIV_BACKPRED)
	sed -e 's/"/\\"/g' \
	  -e 's/^/    "/' \
	  -e 's/$$/\\n" +/' \
	  $(BACKPRED_DIR)/UnivBackPred.ax >> $(DEFAULT_UNIV_BACKPRED)
	echo '    "";' >> $(DEFAULT_UNIV_BACKPRED)
	echo '}' >> $(DEFAULT_UNIV_BACKPRED)

clean_escjava_backpred:
	rm -f $(CLASSDIRECTORY)/escjava/backpred/*.class
	rm -f $(DEFAULT_UNIV_BACKPRED)

###########################################################################
# escjava.parser

PARSER_DIR = $(ESCJAVA_SOURCE_DIR)/escjava/parser
TEST_PARSER_DIR = $(ESCJAVA_TEST)

.PHONY: all_escjava_parser, compile_escjava_parser, clean_escjava_parser, \
	test_escjava_parser, compile_escjava_parser_test_programs, \
	clean_escjava_parser_test, test_lexer, test_parser, test_parser_idempotence

all_escjava_parser: compile_escjava_parser test_escjava_parser

compile_escjava_parser:
	$(JAVAC) $(JAVAC_FLAGS) $(PARSER_DIR)/*.java

clean_escjava_parser:
	rm -f $(CLASSDIRECTORY)/escjava/parser/*.class

PARSER_TEST_PACKAGE = escjava.parser.test
PARSER_TEST_DIR = $(TESTSOURCEDIRECTORY)/escjava/parser/test

test_escjava_parser: compile_escjava_parser compile_escjava_parser_test_programs \
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
# escjava.prover

PROVER_DIR = $(ESCJAVA_SOURCE_DIR)/escjava/prover

.PHONY: compile_escjava_prover clean_escjava_prover

compile_escjava_prover:
	$(JAVAC) $(JAVAC_FLAGS) $(PROVER_DIR)/*.java

clean_escjava_prover:
	rm -f $(CLASSDIRECTORY)/escjava/prover/*.class

###########################################################################
# escjava.tc

TC_DIR = $(ESCJAVA_SOURCE_DIR)/escjava/tc

.PHONY: compile_escjava_tc clean_escjava_tc

compile_escjava_tc:
	$(JAVAC) $(JAVAC_FLAGS) $(TC_DIR)/*.java

clean_escjava_tc:
	rm -f $(CLASSDIRECTORY)/escjava/tc/*.class

###########################################################################
# escjava.translate

TRANSLATE_DIR = $(ESCJAVA_SOURCE_DIR)/escjava/translate

.PHONY: compile_escjava_translate clean_escjava_translate

compile_escjava_translate:
	$(JAVAC) $(JAVAC_FLAGS) $(TRANSLATE_DIR)/*.java

clean_escjava_translate:
	rm -f $(CLASSDIRECTORY)/escjava/translate/*.class

