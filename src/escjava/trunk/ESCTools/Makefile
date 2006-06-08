## $Id$
##
## This file is part of ESC/Java2 from 2003 onward.
##
## author: David Cok
## author: Joe Kiniry
## author: Patrice Chalin
##

export TOP = .
include Makefile.defs

################################################################################
## These are the standard targets.  They are executed in all the
## subdirectories that are listed in the SUBDIRS variable:
##  clean - removes all files created by a build
##  build - compiles out of date generated source and class files (default)
##  buildall - creates all generated source and class files 
##  test  - runs the tests (build must have been run)
##  alltests - test + rarely used or long tests
##  docs  - creates all docs; to get javadocs you must execute the
##          make from this directory
##  all   - does all of the above
##  patch-release  - makes the tar file constituting a patch release
##  source-release - makes the tar file constituting a full source release
##  binary-release - makes the tar file constituting a binary release
##  releases-notests - makes both releases without doing any tests
##  releases - makes both releases with tests after
##
## You can run each of these in a subdirectory and only apply it to
## the code in that subdirectory, if you like.  Note though, that the
## subdirectories other than Javafe presume that Javafe has been
## built.

export ESCJAVA = ${ESCTOOLS_ROOT}/Escjava/escj

# List subprojects in the order in which they should be built.  Javafe
# must be before any other ESCTools directories.
SUBDIRS = Utils Javafe Escjava 

.PHONY: default all all+ nodocs nodocs+ jars

default: build

all: clean build jars test quiet-docs

all+: clean build jars quiet-docs alltests

nodocs: clean build jars test

nodocs+: clean build jars alltests

jars: $(ESCJAVA2_SPECS_JAR) jar srcjar

################################################################################
## Top-level build and test rules

.PHONY: build buildall test javafetests escjavatests alltests \
	javafealltests escjavaalltests findbugs self_typecheck

build buildall: fix-perms
	for d in $(SUBDIRS) ; do \
	    $(MAKE) -C $$d $@ || exit 1; \
	done

source: fix-perms
	$(MAKE) -C Javafe source
	$(MAKE) -C Escjava source generate_files

test: build
	for d in $(SUBDIRS) ; do \
	    $(MAKE) -C $$d $@ || exit 1; \
	done

javafetests: build
	$(MAKE) -C Javafe test || exit 1;

escjavatests: build
	$(MAKE) -C Escjava test || exit 1;

alltests:	build
	${MAKE} test ALLTESTS=1
	${MAKE} specs_test

javafealltests: build
	$(MAKE) -C Javafe test ALLTESTS=1 || exit 1;

escjavaalltests: build
	$(MAKE) -C Escjava test ALLTESTS=1 || exit 1;

ifdef FINDBUGS
findbugs: jar
	${FINDBUGS} -textui esctools2.jar
endif

self_typecheck: build
	$(MAKE) -C Escjava self_typecheck

self_esc: build
	$(MAKE) -C Escjava self_test

################################################################################
## Test using jmlc compiled sources:

# Eventually use $(SUBDIRS).  For now only test Escjava
jmlc_test:
	$(MAKE) -C Utils build
	@echo CLASSPATH=${CLASSPATH}
	@echo
	for d in Escjava ; do \
	    $(MAKE) -C $$d USE_RAC=1 test || exit 1; \
	done

################################################################################
## General rules to clean up build tree

.PHONY: fix-perms

## This rule is needed because CVS does not properly keep permissions
## (expecially x bits), so sometimes we need a reset.  Delete the
## datestamp file ".perms-fixed" to force re-execution.
fix-perms:	.perms-fixed

.perms-fixed:
	@if [ ! -e ".perms-fixed" ]; \
	then \
		find $(ESCTOOLS_ROOT) -type f \
		\( -name "*.[0-9]" -or \
		   -name "*.[chjlo]" -or \
		   -name "*ans" -or \
		   -name "*diff" -or \
		   -name "*.el" -or \
		   -name "*.gif" -or \
		   -name "*.html" -or \
		   -name "*.spec" -or \
		   -name "*.j*" -or \
		   -name "*Make*" -or \
		   -name "*out" -or \
		   -name "README*" -or \
		   -name "*.txt" -or \
		   -name "*.zip" \) \
		-exec chmod 644 {} \; &&\
		find $(ESCTOOLS_ROOT) -type f \
		\( -name "*.sh" -or \
		   -name "*.pl" -or \
		   -name "rtest*" -or \
		   -name "escj" -or \
		   -name "escj.bat" -or \
		   -name "escjava2.exe" -or \
		   -name "escjava2" -or \
		   -name "escjava.bat.win" -or \
		   -name "escjava.linux" -or \
		   -name "escjava.nt.win" -or \
		   -name "escjava.solaris" -or \
		   -name "escjava.tru64" -or \
		   -name "run" -or \
		   -name "*_tags" -or \
		   -name "Simplify-1.5*" -or \
		   -name "insert_ensures" \) \
		-exec chmod 755 {} \; &&\
		touch .perms-fixed; \
	fi

################################################################################
## Clean rules

.PHONY: clean clean-release clean-norel clean-release-test clean-norel-noreltemp

# To really clean, we need to clean Javafe last since some of its
# tools are used in cleaning.
clean: clean-norel clean-release clean-release-test cleanup

# Cleans out the release directory
clean-release:
	rm -rf ${RELDIR}

# Cleans everything except the release directory
clean-norel: clean-norel-noreltemp
	rm -rf ${RELTEMP}

# Cleans release test directory
clean-release-test:
	rm -rf ${RELTEST}

# Cleans everything except the various release directories (test,
# temp, release)
clean-norel-noreltemp:
	rm -rf ${PATCH_DIR}
	for d in $(SUBDIRS) ; do \
	  if [ !"$$d"=="Javafe" ]; then \
	    ( $(MAKE) -C $$d clean || exit 1) ; fi ; \
	done
	$(MAKE) -C docs clean
	$(MAKE) -C papers clean
	$(MAKE) -C slides clean
	$(MAKE) -C Javafe clean
	rm -f $(JAR_FILES)/*.jar
	rm -f tags TAGS SpecTest.java .specs

# Cleans all backups files, log files, CVS merge files, etc.
cleanup:
	-find ${ESCTOOLS_ROOT} \
		\( -name "*~" -or -name "*.#*" -or -name "semantic.cache*" \) \
		-exec rm -f {} \; > /dev/null 2>&1

################################################################################
## Specifications

$(ESCJAVA2_SPECS_JAR):
	(cd specs; jar cf $(ESCJAVA2_SPECS_JAR) .)

# RDG: We are not shipping jmlspecs.jar right now because the large VC
# conditions generated for the full JML specs can make our theorem prover choke

#$(JML2_SPECS_JAR):
#ifdef JML_ROOT
#	${MAKE} -C ${JML_ROOT} jmlspecs-jar
#	cp ${JML_ROOT}/bin/jmlspecs.jar ${JML2_SPECS_JAR}
#else
#	@echo NOT REMAKING JARS FROM JML - since JML_ROOT not defined
#	@true
#endif

################################################################################
## Rules to build documentation

.PHONY: alldocs textdocs quiet-docs docs slides papers javadoc jmldoc jml

alldocs: textdocs javadoc

textdocs: quiet-docs slides papers

quiet-docs:
	-${MAKE} docs > docs_log 2>&1

docs:
	-${MAKE} -C docs build

slides:
	${MAKE} -C slides build

papers:
	${MAKE} -C papers build

# Choose which specs you wish to use for documentation generation and
# typechecking.

# The CVS HEAD JML specs,
#SPECS = ${JML_ROOT}/specs:${JML_ROOT}
# The latest JML stable release specs.
#SPECS = /usr/local/Java/JML/specs:/usr/local/Java/JML
# The ESC/Java2 specs.
SPECS = $(ESCTOOLS_ROOT)/specs

## Javadoc depends on the build target since some of the .java files
## are generated in the course of the build (e.g. the AST classes).
## TODO: Should have -overview , header, footer, bottom, group,
## stylesheetfile link/linkoffline, subpackages -FIXME Kiniry
javadoc: build
	rm -rf $(JAVADOC_GEN_DIR)
	mkdir -p $(JAVADOC_GEN_DIR)
	mkdir -p $(JAVADOC_GEN_DIR)/images
	cp $(DOCS_STYLESHEET) $(JAVADOC_GEN_DIR)
	cp $(JAVAFE_ROOT)/doc/javadoc/images/*.gif $(JAVADOC_GEN_DIR)/images
	$(JAVADOC) -sourcepath \
	  $(call canonicalize,$(SOURCEPATH):$(JUNIT_SOURCEPATH)) \
	  -classpath $(call canonicalize,${CLASSPATH}:${JUNIT_LIB}:${ANT_LIB}:${XMLRPC_LIB}) \
	  -overview docs/overview.html \
	  -header $(COPYRIGHT) \
	  -footer $(COPYRIGHT) \
	  -bottom '<a href="http://secure.ucd.ie/products/opensource/ESCJava2/">The ESC/Java2 Project Homepage</a>' \
	  -stylesheetfile $(DOCS_STYLESHEET) \
	  -private \
	  -doctitle "ESCTools API" \
	  -windowtitle "ESCTools" \
	  -author -version -use \
	  -linksource \
	  -group EscJava "escjava.*" \
	  -group Javafe  "javafe.*" \
	  -group Utils   "junitutils.*" \
	  -tag warning -tag todo -tag note -tag design -tag usage \
	  -tag requires \
	  -d $(JAVADOC_GEN_DIR) \
          $(PACKAGE_LIST)

jmldoc: build
	rm -rf $(JMLDOC_GEN_DIR)
	mkdir -p $(JMLDOC_GEN_DIR)
	mkdir -p $(JMLDOC_GEN_DIR)/images
	cp $(JAVAFE_ROOT)/doc/javadoc/images/*.gif $(JMLDOC_GEN_DIR)/images
	$(JMLDOC) -sourcepath \
	  $(call canonicalize,$(SOURCEPATH):$(SPECS):$(JUNIT_SOURCEPATH)) \
	  -classpath "$(call canonicalize,${ESC_CLASSPATH}:${JUNIT_LIB}:${ANT_LIB}:${XMLRPC_LIB}:)${CLASSPATH}" \
	  -private --source 1.4 \
	  -doctitle "ESCTools API" \
	  -windowtitle "ESCTools" \
	  -author -version -use \
	  -linksource \
	  -group EscJava "escjava.*" \
	  -group Javafe  "javafe.*" \
	  -group Utils   "junitutils.*" \
	  -tag warning -tag todo -tag note -tag design -tag usage \
	  -tag requires \
	  -d $(JMLDOC_GEN_DIR) \
	  -A \
          $(PACKAGE_LIST)

################################################################################
## JML checker targets:

JML_PACKAGES=junitutils javafe escjava

# TODO: Add package decsrc
jml: build
	$(JML) \
	  --sourcepath "$(call canonicalize,$(SOURCEPATH):$(SPECS))" \
	  --classpath "$(call canonicalize,${ESCJAVA_BUILD_CLASSPATH}:)${CLASSPATH}" \
	  -a -A --purity -n \
	  --keepGoing --source 1.4 --Quiet --recursive \
	  $(JML_PACKAGES)

#===============================================================================
## JMLc targets:
#
.PHONY: jmlc jmlc_utils jmlc_fe jmlc_ej jmlc_with_new_semantics

# FIXME: Javafe and Escjava Makefiles should be adapted like the Utils Makefile
# so that the build target's behavior is altered when USE_JMLC is defined.

jmlc: jmlc_utils jmlc_fe jmlc_ej jmlc_with_new_semantics

jmlc_utils:
	$(MAKE) USE_JMLC=1 -C Utils buildall

jmlc_fe: ${JAVAFE_CLASSFILES4RAC}
	export JMLC_XMX=512M; \
	$(MAKE) JMLC_CLASSFILES_DIR=${JAVAFE_CLASSFILES4RAC} \
		TARGET=javafe \
		JMLC_FLAGS='--excludefiles "^(ASTNode|TypeDeclElem)\.java"' \
		jmlc1

jmlc_ej: ${ESCJAVA_CLASSFILES4RAC}
	export JMLC_XMX=512M; \
	$(MAKE) JMLC_CLASSFILES_DIR=${ESCJAVA_CLASSFILES4RAC} \
		TARGET=escjava \
		JMLC_FLAGS='--excludefiles "^(SPVC)\.java"' \
		jmlc1

# Some files cannot be compiled under the current/old semantics because the generated code
# has a try/catch block that is beyond the limits of the VM.  Hence, we compile these files
# separately using the new semantics (-T).
jmlc_with_new_semantics:
	$(MAKE) JMLC_CLASSFILES_DIR=${JAVAFE_CLASSFILES4RAC} \
		TARGET='Javafe/java/javafe/ast/ASTNode.java' \
		JMLC_FLAGS='-T' jmlc1
	$(MAKE) JMLC_CLASSFILES_DIR=${JAVAFE_CLASSFILES4RAC} \
		TARGET='Javafe/java/javafe/ast/TypeDeclElem.java' \
		JMLC_FLAGS='-T' jmlc1
	$(MAKE) JMLC_CLASSFILES_DIR=${ESCJAVA_CLASSFILES4RAC} \
		TARGET='Escjava/java/escjava/sp/SPVC.java' \
		JMLC_FLAGS='-T' jmlc1

${JAVAFE_CLASSFILES4RAC}:
	mkdir ${JAVAFE_CLASSFILES4RAC}
${ESCJAVA_CLASSFILES4RAC}:
	mkdir ${ESCJAVA_CLASSFILES4RAC}

JMLC_CLASSFILES=jmlc_classfiles

${JMLC_CLASSFILES}:
	mkdir ${JMLC_CLASSFILES}

#..............................................................................
# Run jmlc on each file one by one (which seems to give us the best results for now)
jmlc1b1: build jmlc_javafe_1b1 jmlc_escjava_1b1

jmlc_javafe_1b1:
	@echo "JAVAFE============================================================"
	for f in `find Javafe/java -name *.java ! -name "*/jcheck/*"`; do \
		${MAKE} JMLC_CLASSFILES_DIR=${JAVAFE_CLASSFILES4RAC} TARGET=$$f jmlc1; \
	done;
	${MAKE} jmlc_javafe_cleanup

jmlc_escjava_1b1:
	@echo "ESCJAVA============================================================"
	for f in `find Escjava/java -name *.java`; do \
		${MAKE} JMLC_CLASSFILES_DIR=${ESCJAVA_CLASSFILES4RAC} TARGET=$$f jmlc1; \
	done
	${MAKE} jmlc_escjava_cleanup

# Apply jmlc to one TARGET at a time; class files are to be saved in JMLC_CLASSFILES_DIR.
jmlc1:
	$(JMLC) \
	  --sourcepath "$(call canonicalize,$(SOURCEPATH):$(SPECS))" \
	  --classpath "$(call canonicalize,${ESCJAVA_BUILD_CLASSPATH}:)${CLASSPATH}" \
	  -d $(JMLC_CLASSFILES_DIR) \
	  -a -A --purity \
	  -n \
	  --keepGoing --source 1.4 --Quiet --recursive \
	  $(JMLC_FLAGS) \
	  $(TARGET) \
	  && touch .jmlc

# If the new jmlc target works, then the following three targets will no longer be
# necessary. --PC

# Next three `cleanup' targets will remove zero-sized class files that JMLc 
# leaves hanging around when it dies during the compilation of a file.
jmlc_javafe_cleanup:
	${MAKE} JMLC_CLASSFILES_DIR=${JAVAFE_CLASSFILES4RAC} post_jmlc_cleanup
jmlc_escjava_cleanup:
	${MAKE} JMLC_CLASSFILES_DIR=${ESCJAVA_CLASSFILES4RAC} post_jmlc_cleanup

post_jmlc_cleanup:
	@for f in `find $(JMLC_CLASSFILES_DIR) -name *.class`; do \
		if [ ! -s $$f ]; then \
			echo "  removing zero-sized class file: $$f"; \
			rm $$f; \
		fi; \
	done

################################################################################
## Rules to build various release types

.PHONY: releases test-releases releases-notests source-release patch-release \
	jar srcjar binary-release test-binary-release test-patch-release \
	generate-patches generate-archives generate-specs-archive \
	generate-toplevel-archive zero-length-files version

## FIXME: get mocha right

releases: releases-notests 
	${MAKE} test-releases

test-releases:
	@echo "Testing release versions .........."
	${MAKE} test-binary-release
	${MAKE} test-patch-release
	${MAKE} test-source-release

releases-notests:
	@echo "Making release versions ${ESC_PROJECT}-${ESC_VERSION} ........"
	${MAKE} patch-release
	${MAKE} binary-release
	${MAKE} source-release

source-release: cleanup alldocs
	@echo "Creating source release .........."
#	RELDIR is the staging area for all files
#	First copy all .class files to sub and build a jar file
	mkdir -p ${RELDIR}
	rm -rf ${RELTEMP}
	mkdir -p ${RELTEMP}
	${MAKE} jars
#	Now copy in all specs, new and old
	rm -rf ${RELTEMP}/specs
	cp -r ${ESCJAVA2_SPECS} ${RELTEMP}
	rm -rf ${RELTEMP}/original-specs
	cp -r ${ORIG_SRC_SPECS} ${RELTEMP}
#       Copy all source code, tests, libs, Makefiles, ChangeLog, etc.
	cp -r ${UTILS_SOURCE_DIR} ${RELTEMP}
	cp -r ${MOCHA_SOURCE_DIR} ${RELTEMP}
	cp -r ${JAVAFE_SOURCE_DIR} ${RELTEMP}
	cp -r ${ESCJAVA_SOURCE_DIR} ${RELTEMP}
	cp ${XMLRPC_LIB} ${RELTEMP}/xmlrpc.jar
	cp Makefile* ${RELTEMP}
	cp build.xml ${RELTEMP}
	cp prj.el ${RELTEMP}
	cp ChangeLog ${RELTEMP}
#	Copy Javadoc API docs
	cp -r $(JAVADOC_GEN_DIR) ${RELTEMP}
#	Copy papers and slides and other documentation
	mkdir ${RELTEMP}/papers
	cp papers/*.pdf ${RELTEMP}/papers
	mkdir ${RELTEMP}/slides
	cp slides/ETAPSTutorial/*.pdf ${RELTEMP}/slides
	cp slides/introjml.pdf ${RELTEMP}/slides
	cp slides/escjava_demo.pdf ${RELTEMP}/slides
	mkdir ${RELTEMP}/docs
	cp docs/Escjava2-ImplementationNotes/*.pdf ${RELTEMP}/docs
	cp docs/Escjava2-Extending/Escjava2-Extending.pdf ${RELTEMP}/docs
	cp docs/Escjava2-Logics/Escjava2-Logics.pdf ${RELTEMP}/docs
	cp docs/Escjava2-Provers/Escjava2-Provers.pdf ${RELTEMP}/docs
	cp docs/ESCJAVA-UsersManual.html ${RELTEMP}/docs
	cp -r Escjava/release/master/examples ${RELTEMP}
#	Copy actual jar files with all ESC/Java2's classfiles and the two jar files
#       with specs in them.
	cp esctools2.jar ${RELTEMP}
	cp $(ESCJAVA2_SPECS_JAR) ${RELTEMP}
#	cp $(JML2_SPECS_JAR) ${RELTEMP}
# 	Copy other miscellaneous files
	${MAKE} clean-norel-noreltemp
	cp ${ESCJAVA_ROOT}/escj ${RELTEMP}
	cp ${ESCJAVA_ROOT}/escj.bat ${RELTEMP}
	cp ${ESCJAVA_ROOT}/escjava2.exe ${RELTEMP}
	cp ${ESCJAVA_ROOT}/escjava2.sample ${RELTEMP}
	cp ${ESCJ_SIMPLIFY_DIR}/Simplify-1.5.4* ${RELTEMP}
	cp README.first README.txt ${RELTEMP}
	cd release-files; cp `ls | grep -v CVS` ${RELTEMP}
	-find ${RELTEMP} -name "CVS" -exec rm -rf {} \; > /dev/null 2>&1
	-find ${RELTEMP} -name ".cvsignore" -exec rm -rf {} \; > /dev/null  2>&1
	-find ${RELTEMP} -name "*~" -or -name ".#*" -exec rm -f {} \; > /dev/null 2>&1
	cd ${RELTEMP}; tar cjvf ${RELDIR}/${RELSRCTAR}.tbz *
	cd ${RELTEMP}; tar czvf ${RELDIR}/${RELSRCTAR}.tgz *
	cd ${RELTEMP}; zip -Ar ${RELDIR}/${RELSRCTAR}.zip *
	rm -rf ${RELTEMP}

patch-release: clean
	@echo "Creating patch release .........."
	rm -rf ${PATCH_DIR}
	mkdir -p ${PATCH_DIR}
	${MAKE} jars generate-patches generate-archives zero-length-files
	cp ${ESCTOOLS_ROOT}/install.sh ${PATCH_DIR}
	mkdir -p ${RELDIR}
	cd ${PATCH_DIR}; tar cvjf ${RELDIR}/${RELPATCHTAR}.tbz .
	cd ${PATCH_DIR}; tar cvzf ${RELDIR}/${RELPATCHTAR}.tgz .
	cd ${PATCH_DIR}; zip -Ar ${RELDIR}/${RELPATCHTAR}.zip .
	rm -rf ${PATCH_DIR}

version:
	$(MAKE) -C Escjava version

jar:	build
	mkdir -p ${RELTEMP}/sub
	cp ${ESCTOOLS_ROOT}/Escjava/java/escjava/vcGeneration/xml/*.xslt ${ESCJAVA_CLASSFILES}/escjava/vcGeneration/xml
	cp ${ESCTOOLS_ROOT}/Escjava/java/escjava/vcGeneration/xml/xmlprover.dtd ${ESCJAVA_CLASSFILES}/escjava/vcGeneration/xml
	cp -r ${JAVAFE_CLASSFILES}/* ${RELTEMP}/sub
	cp -r ${ESCJAVA_CLASSFILES}/* ${RELTEMP}/sub
	mkdir -p ${RELTEMP}/sub/junitutils
	( cd ${ESCTOOLS_ROOT}/Utils/junitutils; \
	  cp `find . -name '*.class'` ${RELTEMP}/sub/junitutils )
	( cd ${RELTEMP}/sub; jar xf $(ESCJAVA2_SPECS_JAR) )
	( cd ${RELTEMP}/sub; rm -rf `find . -name CVS`; )
	( cd ${RELTEMP}/sub; jar cmf ../../manifest.txt \
	  ${RELJAR} *; jar i ${RELJAR}; )
#	 ${JARMUPDATE} manifest.txt ${RELJAR}
	rm -rf ${RELTEMP}/sub
	cp ${RELJAR} ${ESCTOOLS_ROOT}

srcjar:
	mkdir -p ${RELTEMP}/sub
	cp -r ${ESCTOOLS_ROOT}/Javafe/java/* ${RELTEMP}/sub
	cp -r ${ESCTOOLS_ROOT}/Escjava/java/* ${RELTEMP}/sub
	cp -r ${ESCJAVA2_SPECS} ${RELTEMP}/sub/specs
	cp -r ${ORIG_SRC_SPECS} ${RELTEMP}/sub/original-specs
	mkdir -p ${RELTEMP}/sub/junitutils
	(cd ${ESCTOOLS_ROOT}/Utils/junitutils; \
	  cp `find . -name '*.java'` ${RELTEMP}/sub/junitutils)
	( cd ${RELTEMP}/sub; rm -rf `find . -name CVS`; )
	( cd ${RELTEMP}/sub; jar cf ${RELSRCJAR} *; )
	rm -rf ${RELTEMP}/sub
	cp ${RELSRCJAR} ${ESCTOOLS_ROOT}

.PHONY: binary-release
binary-release: build jars alldocs cleanup
	@echo "Creating binary release .........."
#	RELDIR is the staging area for all files
#	First copy all .class files to sub and build a jar file
	mkdir -p ${RELDIR}
	rm -rf ${RELTEMP}
	mkdir -p ${RELTEMP}
	${MAKE} jars
#	Now copy in all specs, new and old
	rm -rf ${RELTEMP}/specs
	cp -r ${ESCJAVA2_SPECS} ${RELTEMP}
	-find ${RELTEMP}/specs -name "CVS" -exec rm -rf {} \; > /dev/null  2>&1
	rm -rf ${RELTEMP}/original-specs
	cp -r ${ORIG_SRC_SPECS} ${RELTEMP}
	-find ${RELTEMP}/original-specs -name "CVS" -exec rm -rf {} \; > /dev/null  2>&1
#	Copy Javadoc API docs
	cp -r $(JAVADOC_GEN_DIR) ${RELTEMP}
#	Copy papers and slides and other documentation
	mkdir ${RELTEMP}/papers
	cp papers/*.pdf ${RELTEMP}/papers
	mkdir ${RELTEMP}/slides
	cp slides/ETAPSTutorial/*.pdf ${RELTEMP}/slides
	cp slides/introjml.pdf ${RELTEMP}/slides
	cp slides/escjava_demo.pdf ${RELTEMP}/slides
	mkdir ${RELTEMP}/docs
	cp docs/Escjava2-ImplementationNotes/*.pdf ${RELTEMP}/docs
	cp docs/Escjava2-Extending/Escjava2-Extending.pdf ${RELTEMP}/docs
	cp docs/Escjava2-Logics/Escjava2-Logics.pdf ${RELTEMP}/docs
	cp docs/Escjava2-Provers/Escjava2-Provers.pdf ${RELTEMP}/docs
	cp docs/ESCJAVA-UsersManual.html ${RELTEMP}/docs
	cp -r Escjava/release/master/examples ${RELTEMP}
	-find ${RELTEMP}/examples -name "CVS" -exec rm -rf {} \; > /dev/null 2>&1
#	Copy actual jar files with all ESC/Java2's classfiles and the two jar files
#       with specs in them.
	cp esctools2.jar ${RELTEMP}
	cp $(ESCJAVA2_SPECS_JAR) ${RELTEMP}
#	cp $(JML2_SPECS_JAR) ${RELTEMP}
# 	Copy other miscellaneous files
	${MAKE} clean-norel-noreltemp
	${MAKE} -C Utils/junitutils build
	cp ${ESCJAVA_ROOT}/escj ${RELTEMP}
	cp ${ESCJAVA_ROOT}/escj.bat ${RELTEMP}
	cp ${ESCJAVA_ROOT}/escjava2.exe ${RELTEMP}
	cp ${ESCJAVA_ROOT}/escjava2.sample ${RELTEMP}
	cp ${ESCJ_SIMPLIFY_DIR}/Simplify-1.5.4* ${RELTEMP}
	cp README.first README.txt ${RELTEMP}
	cd release-files; cp `ls | grep -v CVS` ${RELTEMP}
	-find ${RELTEMP} -name "*~" -exec rm -f {} \; > /dev/null 2>&1
	cd ${RELTEMP}; tar cjvf ${RELDIR}/${RELTAR}.tbz *
	cd ${RELTEMP}; tar czvf ${RELDIR}/${RELTAR}.tgz *
	cd ${RELTEMP}; zip -Ar ${RELDIR}/${RELTAR}.zip *
	rm -rf ${RELTEMP}

test-binary-release:
	@echo "Testing binary release ............"
	rm -rf ${RELTEST}
	mkdir -p ${RELTEST}
	cp ${RELDIR}/${RELTAR}.tbz ${RELTEST}
	cd ${RELTEST} ;\
	    unset ESC_CLASSPATH ; \
	    tar xjf ${RELTAR}.tbz ;\
	    ./quicktest

## Note - we need to unset lots of environmental variables here because we
## want them to be reset based on the value of ESC_RELEASE in install.sh.
## Otherwise, since the variables are only conditionally set in Makefile.defs
## or in Makefile, they will continue to have the value already set in the
## current environment (when this Make was invoked) rather than getting new
## values when the Make in install.sh is invoked.  So include here any variable
## that is conditionally set and might have a different value when running a
## release than when running from the build environment.
test-patch-release:
	@echo "Testing patch release ........"
	rm -rf ${RELTEST}
	mkdir -p ${RELTEST}
	cd ${RELTEST}; \
		tar xvjf ${RELDIR}/*patch.tbz ;\
		unset ESCTOOLS_ROOT ;\
		unset ESC_SPECS; \
		unset JUNIT_LIB ;\
		unset ANT_LIB ;\
		unset PATCH_DIR ;\
		unset RELDIR ;\
		unset RELTEMP ;\
		unset RELTEST ;\
		unset ESCJ_SIMPLIFY_DIR; \
		unset ESC_CLASSPATH ;\
		./install.sh  ${ORIGINAL_TAR_DIR}

## These patches are used by unpacking the original
## Compaq/H.P. ESCTools sources as appropriate, cd-ing to the
## top-level directory "ESCTools" and running
##   bzcat ~/ESCTools-<version>-<date>-<envelope>.patch.bz | patch -Np1
## the appropriate number of times.

PATCH_PREFIX = ${PATCH_DIR}/${PATCH_NAME}
generate-patches: clean
	@echo "Generating patches..."
	( cd ${ESCTOOLS_ROOT}/.. ; mkdir -p ${PATCH_DIR}; \
	LC_ALL=C TZ=UTC0 diff -Naur --exclude=*.class --exclude=.#* --exclude=CVS \
		--exclude=Simplify-1* ${ESCTOOLS_ORIGINAL}/Calvin ESCTools/Calvin \
		| bzip2 > ${PATCH_DIR}/${CALVIN_PATCHES}; \
	LC_ALL=C TZ=UTC0 diff -Naur --exclude=*.class --exclude=.#* --exclude=CVS \
		--exclude=Simplify-1* --exclude=javadoc \
		${ESCTOOLS_ORIGINAL}/Escjava ESCTools/Escjava \
		| bzip2 > ${PATCH_DIR}/${ESCJAVA_PATCHES}; \
	LC_ALL=C TZ=UTC0 diff -Naur --exclude=*.class --exclude=.#* --exclude=CVS \
		${ESCTOOLS_ORIGINAL}/Houdini ESCTools/Houdini \
		| bzip2 > ${PATCH_DIR}/${HOUDINI_PATCHES}; \
	LC_ALL=C TZ=UTC0 diff -Naur --exclude=*.class --exclude=.#* --exclude=CVS \
		${ESCTOOLS_ORIGINAL}/Javafe ESCTools/Javafe \
		| bzip2 > ${PATCH_DIR}/${JAVAFE_PATCHES}; \
	LC_ALL=C TZ=UTC0 diff -Naur --exclude=*.class --exclude=.#* --exclude=CVS \
		${ESCTOOLS_ORIGINAL}/Rcc ESCTools/Rcc \
		| bzip2 > ${PATCH_DIR}/${RCC_PATCHES}; \
	LC_ALL=C TZ=UTC0 diff -Naur --exclude=PPC_DARWIN --exclude=.#* --exclude=CVS \
		--exclude=*.dylib --exclude=*.a --exclude=*.io --exclude=*.mo \
		${ESCTOOLS_ORIGINAL}/Simplify ESCTools/Simplify \
		| bzip2 > ${PATCH_DIR}/${SIMPLIFY_PATCHES}; \
	)

generate-archives: generate-toplevel-archive generate-specs-archive

## Contains both specs and original-specs for the patch release
generate-specs-archive:
	mkdir -p ${RELTEMP}
	rm -rf ${RELTEMP}/specs
	rm -rf ${RELTEMP}/original-specs
	cp -r ${ESCJAVA2_SPECS} ${RELTEMP}
	cp -r ${ORIG_SRC_SPECS} ${RELTEMP}
	-find ${RELTEMP}/specs -name "CVS" -exec rm -rf {} \;  > /dev/null 2>&1
	-find ${RELTEMP}/original-specs -name "CVS" -exec rm -rf {} \;  > /dev/null 2>&1
	(cd ${RELTEMP}; tar cjf ${PATCH_DIR}/${SPECS_TAR} specs original-specs;) 
	rm -rf ${RELTEMP}/specs ${RELTEMP}/original-specs

generate-toplevel-archive: clean
	rm -rf ${RELTEMP}/ESCTools
	mkdir -p ${RELTEMP}/ESCTools
	cp ${ESCTOOLS_ROOT}/ChangeLog ${ESCTOOLS_ROOT}/Makefile \
		${ESCTOOLS_ROOT}/Makefile.defs \
		${ESCTOOLS_ROOT}/Makefile.local.sample \
		${ESCTOOLS_ROOT}/README.first ${ESCTOOLS_ROOT}/README.txt \
		${ESCTOOLS_ROOT}/TODO.kotl ${ESCTOOLS_ROOT}/build.xml \
		${ESCTOOLS_ROOT}/clean_env.sh ${RELTEMP}/ESCTools
	cp -r ${ESCTOOLS_ROOT}/docs ${RELTEMP}/ESCTools
	cp -r ${ESCTOOLS_ROOT}/papers ${RELTEMP}/ESCTools
	cp -r ${ESCTOOLS_ROOT}/slides ${RELTEMP}/ESCTools
	cp -r ${ESCTOOLS_ROOT}/Utils ${RELTEMP}/ESCTools
	cp -r ${JAR_FILES} ${RELTEMP}/ESCTools
# 	cp $(JML2_SPECS_JAR) ${RELTEMP}/ESCTools
# 	cp $(ESCJAVA2_SPECS_JAR) ${RELTEMP}/ESCTools
	mkdir -p ${RELTEMP}/ESCTools/Escjava/release/master/bin
	cp ${ESCTOOLS_ROOT}/Escjava/release/master/bin/Simplify-1.5.4.macosx \
		${RELTEMP}/ESCTools/Escjava/release/master/bin
	-find ${RELTEMP}/ESCTools -name "CVS" -exec rm -rf {} \;  > /dev/null  2>&1
	(cd ${RELTEMP}/ESCTools; tar cjf ${PATCH_DIR}/${TOPLEVEL_TAR} . ;) 
	rm -rf ${RELTEMP}/ESCTools

## Until we can figure out how to have diff/patch detect and generate
## 0 length files, we have to archive them up all independently.
zero-length-files:
	mkdir -p ${PATCH_DIR}
	cd ${ESCTOOLS_ROOT}; \
	find . -empty ! -name .M3SHIP -print0 | \
		xargs -0 tar cjf ${PATCH_PREFIX}-ZeroLengthFiles.tbz
	( cd ${ESCTOOLS_ROOT}; \
	  for f in `cd ${ESCTOOLS_ORIGINAL}; find . -empty`; do \
	      if [ ! -e $$f ]; then echo $$f; fi; \
	  done ) > ${PATCH_PREFIX}-emptyFilesThatDisappeared

############################################################################
## Testing our specifications

.PHONY: specs_test check_specs

## Run escjava on the specs
specs_test: build
	@echo "TESTING specs..."
	${ESCJAVA} -quiet \
	  -classpath ${ESCTOOLS_ROOT} \
	  -specs ${ESCJAVA2_SPECS} \
	  java.io java.lang java.lang.reflect java.math java.net java.util java.util.regex

current_specs_test: build
	@echo "TESTING specs..."
	${ESCJAVA} -quiet \
	  -classpath ${ESCTOOLS_ROOT} \
	  -specs ${ESCJAVA2_SPECS} \
	  java.util.Calendar java.util.GregorianCalendar java.util.Date

## Experimental rule to generate a file that references every type
## that currently has a spec and run escjava2 on it to try to detect
## problems with package- and private-level types.
#check_specs: build $(JML2_SPECS_JAR)
check_specs: build
	find specs -type f | grep -v Entries | grep -v Repository | grep -v Root | \
	  grep -v "*~" | sed -e s+specs/++ | sed -e s+\\.spec++ | \
	  sed -e s+\\.refines-spec++ | sed -e s+\\.refines++ | \
	  sed -e s+\\.jml++ | sed -e s+\\.java++ | sed -e s+-java++ | \
	  sed -e s+\\.refines-java++ | sed -e s+/+.+g | \
	  grep -v VERSION | grep -v META | grep -v '\.\.' | \
	  grep -v "\.$$" | sort > .specs
	cat .specs | sed -e s+.*+import\ \&\;+ > SpecTest.java
	@echo "class SpecTest {" >> SpecTest.java
	i=0; for f in `cat .specs`; do \
	  echo "$$f x$$i ;" >> SpecTest.java ; \
	  ((i=i+1)); \
	done
	@echo "}" >> SpecTest.java
	CLASSPATH=$(call canonicalize,${CLASSPATH}:${JUNIT_LIB}:${ANT_LIB}); $(ESCJAVA) \
	  SpecTest.java
	rm -f .specs SpecTest.java

################################################################################
## Show system variables

.PHONY: show show-vars

show: show-vars

show-vars:
	@echo "CLASSPATH = $(CLASSPATH)"

################################################################################
## Simple smoke tests

.PHONY: make-test

## This is simply a smoke test of the Makefile, specific to Windows,
## thus the guard using the environmental variable COMSPEC defined by
## cygwin.
make-test:
ifdef COMSPEC
	@echo `cygpath -m $(ESCJ_SIMPLIFY_DIR)`
	@echo ${foo}
endif

# End of Makefile
