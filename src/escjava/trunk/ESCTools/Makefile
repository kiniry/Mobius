## This file is part of the 2003 Revision of the ESC Tools
##
## author: David Cok - 26 March 2003
## author: Joe Kiniry
##

export TOP = .
include Makefile.defs

## These are the standard targets.  They are executed in all the
## subdirectories that are listed in the SUBDIRS variable:
##	clean - removes all files created by a build
##	build - compiles out of date generated source and class files (default)
##	buildall - creates all generated source and class files 
##	test  - runs the tests (build must have been run)
##      alltests - test + rarely used or long tests
##	docs  - creates all docs; to get javadocs you must execute the
##		make from this directory
##	all   - does all of the above
##	release - creates a release package
##	release-notests - creates a releast package without running tests
##
## You can run each of these in a subdirectory and only apply it to
## the code in that subdirectory, if you like.  Note though, that the
## subdirectories other than Javafe presume that Javafe has been
## built.

# List subprojects in the order in which they should be built.  Javafe
# must be before any other Esctool directories.
SUBDIRS = Utils Javafe Escjava

.PHONY: default
default: build

.PHONY: all
all: clean build alltests docs

########################################### build, test

.PHONY: build buildall test
build buildall test: 
	for d in $(SUBDIRS) ; do \
	    $(MAKE) -C $$d $@ || exit 1; \
	done

.PHONY: alltests
alltests:
	${MAKE} test ALLTESTS=1

########################################### general

.PHONY: fix-perms
fix-perms:
	find $(ESCTOOLS_ROOT) -type f \
		-name "*.[0-9]" -or \
		-name "*.[chjlo]" -or \
		-name "*ans" -or \
		-name "*diff" -or \
		-name "*.el" -or \
		-name "*.gif" -or \
		-name "*.html" -or \
		-name "*.j*" -or \
		-name "*Make*" -or \
		-name "*out" -or \
		-name "README*" -or \
		-name "*.txt" -or \
		-name "*.zip" \
		-exec chmod 644 {} \;

########################################### clean

# To really clean, we need to clean Javafe last since some of its
# tools are used in cleaning.
.PHONY: clean clean-norel clean-release
clean: clean-norel clean-release

clean-release:
	rm -rf ${RELDIR}

# Cleans everything except the release directory
clean-norel:
	rm -rf ${RELTEMP}
	for d in $(SUBDIRS) ; do \
		if [ ! $$d == Javafe ]; then \
		    ( $(MAKE) -C $$d clean || exit 1) ; fi ; \
	done
	$(MAKE) -C Javafe clean

########################################### docs

.PHONY: docs
docs: javadoc
	for d in $(SUBDIRS) ; do \
	    $(MAKE) -C $$d $@ || exit 1; \
	done

PACKAGE_LIST = escjava escjava.ast escjava.backpred escjava.parser \
	  escjava.prover escjava.tc escjava.translate escjava.sp \
	  escjava.reader \
          javafe javafe.ast javafe.parser  \
	  javafe.reader javafe.genericfile javafe.filespace \
	  javafe.tc javafe.util \
	  junitutils

JAVADOC_SOURCEPATH = $(subst : ,:,$(addsuffix /java:,$(addprefix $(ESCTOOLS_ROOT)/,$(SUBDIRS)))):${ESCTOOLS_ROOT}/Utils

## Javadoc depends on the build target since some of the .java files
## are generated in the course of the build (e.g. the AST classes).
.PHONY: javadoc
javadoc:  build
	mkdir -p $(JAVADOC_GEN_DIR)/images
	cp $(JAVAFE_ROOT)/doc/javadoc/images/*.gif $(JAVADOC_GEN_DIR)/images
	$(JAVADOC) -sourcepath $(JAVADOC_SOURCEPATH):$(JUNIT_SOURCEPATH) \
	  -d $(JAVADOC_GEN_DIR) \
          $(PACKAGE_LIST)

########################################### release

## FIXME: get mocha right

.PHONY: release
release: 
	@echo Making release version ${ESC_PROJECT}-${ESC_VERSION}
	${MAKE} clean
	${MAKE} -k generate-patches
	${MAKE} build
	${MAKE} test
	${MAKE} make-release
	${MAKE} test-release

.PHONY: release-notest
release-notest:
	${MAKE} clean
	${MAKE} -k generate-patches
	${MAKE} build
	${MAKE} make-release

.PHONY: make-release
make-release:
	@ echo MAKING RELEASE
	rm -rf ${RELTEMP} ${RELDIR}
	mkdir -p ${RELTEMP} ${RELDIR}
	cp -r ${JAVAFE_CLASSFILES}/* ${RELTEMP}
	cp -r ${ESCJAVA_CLASSFILES}/* ${RELTEMP}
	cd ${RELTEMP}; jar cf ${RELDIR}/${RELJAR} *
	${MAKE} clean-norel
	${MAKE} -C Utils/junitutils build
	mkdir -p ${RELTEMP}
	cp ${ESCJAVA_ROOT}/escj ${RELDIR}
	cp ${ESCJ_SIMPLIFY_DIR}/Simplify-1.5.4* ${RELDIR}
	cp ${ESCJAVA_ROOT}/simplify ${RELDIR}/simplify-script
	cp README.first README.txt ${RELDIR}
	cd release-files; cp `ls | grep -v CVS` ${RELDIR}
	cd ${RELDIR}; tar czvf ${RELTAR} *

## FIXME - simplify script, simplify binary; alter escj to use alternate simplify script
## FIXME - also zip up the source and ship it as well.
## FIXME - tar the result; do we need an install file?  DO need install instructions and a README

.PHONY: test-release
test-release:
	export ESCTOOLS_RELEASE=${RELDIR} ;\
	${MAKE} -C Javafe  test-release ;\
	${MAKE} -C Escjava test-release 

## For this target to work, you must unpack the original ESCTools
## archives (e.g., Calvin.tar.Z, Escjava.tar.Z, etc.) into a directory
## "ESCTools.orig" that is adjacent to your "ESCTools" sandbox.  The
## Simplify package must be unpacked into the directory
## "ESCTools.orig/Simplify".  Then, this rule is run from the
## directory above the two ESCTools{.orig} directories.
.PHONY: generate-patches
generate-patches: clean
	(cd ..; \
	LC_ALL=C TZ=UTC0 diff -Naur --exclude=*.class --exclude=.#* --exclude=CVS \
		--exclude=Simplify-1* ESCTools.orig/Calvin ESCTools/Calvin \
		| bzip2 -9 > ${ESC_PROJECT}-${ESC_VERSION}-`date "+%d-%m-%y"`-Calvin.patch.bz; \
	LC_ALL=C TZ=UTC0 diff -Naur --exclude=*.class --exclude=.#* --exclude=CVS \
		--exclude=Simplify-1* --exclude=javadoc \
		ESCTools.orig/Escjava ESCTools/Escjava \
		| bzip2 -9 > ${ESC_PROJECT}-${ESC_VERSION}-`date "+%d-%m-%y"`-Escjava.patch.bz; \
	LC_ALL=C TZ=UTC0 diff -Naur --exclude=*.class --exclude=.#* --exclude=CVS \
		ESCTools.orig/Houdini ESCTools/Houdini \
		| bzip2 -9 > ${ESC_PROJECT}-${ESC_VERSION}-`date "+%d-%m-%y"`-Houdini.patch.bz; \
	LC_ALL=C TZ=UTC0 diff -Naur --exclude=*.class --exclude=.#* --exclude=CVS \
		ESCTools.orig/Rcc ESCTools/Rcc \
		| bzip2 -9 > ${ESC_PROJECT}-${ESC_VERSION}-`date "+%d-%m-%y"`-Rcc.patch.bz; \
	LC_ALL=C TZ=UTC0 diff -Naur --exclude=PPC_DARWIN --exclude=.#* --exclude=CVS \
		--exclude=*.dylib --exclude=*.a --exclude=*.io --exclude=*.mo \
		ESCTools.orig/Simplify ESCTools/Simplify \
		| bzip2 -9 > ${ESC_PROJECT}-${ESC_VERSION}-`date "+%d-%m-%y"`-Simplify.patch.bz; \
	)

.PHONY: generate-toplevel-archive
generate-toplevel-archive: clean
	mkdir -p ${RELTEMP}/ESCTools; \
	cp ${ESCTOOLS_ROOT}/ChangeLog ${ESCTOOLS_ROOT}/Makefile ${ESCTOOLS_ROOT}/Makefile.defs \
		${ESCTOOLS_ROOT}/Makefile.local.sample ${ESCTOOLS_ROOT}/README.first ${ESCTOOLS_ROOT}/README.txt \
		${ESCTOOLS_ROOT}/TODO.kotl ${ESCTOOLS_ROOT}/build.xml ${ESCTOOLS_ROOT}/clean_env.sh ${RELTEMP}/ESCTools; \
	cp -r ${ESCTOOLS_ROOT}/docs ${RELTEMP}/ESCTools; \
	cp -r ${ESCTOOLS_ROOT}/Utils ${RELTEMP}/ESCTools; \
	cp -r ${ESCTOOLS_ROOT}/jars ${RELTEMP}/ESCTools; \
	find ${RELTEMP} -name "CVS" -exec rm -rf {} \; ; \
	(cd ${RELTEMP}; \
		tar cjf ${ESCTOOLS_ROOT}/../${ESC_PROJECT}-${ESC_VERSION}-`date "+%d-%m-%y"`-TopLevel.tbz \
		ESCTools;); \
	rm -rf ${RELTEMP}/ESCTools
