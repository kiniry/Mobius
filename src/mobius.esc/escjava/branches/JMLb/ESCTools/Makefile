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
##	patch-release - makes the tar file constituting a patch release
##	binary-release - makes the tar file constituting a binary release
##	releases-notests - makes both releases without doing any tests
##	releases	- makes both releases with tests after
##
## You can run each of these in a subdirectory and only apply it to
## the code in that subdirectory, if you like.  Note though, that the
## subdirectories other than Javafe presume that Javafe has been
## built.

export ESCJAVA = ${ESCTOOLS_ROOT}/Escjava/escj

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
	##${MAKE} specs-test

########################################### general

## It does not appear that this is used anywhere - is it needed? FIXME
## I think this is needed because CVS does not properly keep
## permissions (expecially x bits), so sometimes we need a reset. -JOE

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
		-name "*.spec" -or \
		-name "*.j*" -or \
		-name "*Make*" -or \
		-name "*out" -or \
		-name "README*" -or \
		-name "*.txt" -or \
		-name "*.zip" \
		-exec chmod 644 {} \;
	find $(ESCTOOLS_ROOT) -type f \
		-name "rtest*" -or \
		-name "run" \
		-name "*_tags" \
		-name "insert_ensures" \
		-exec chmod 755 {} \;

########################################### clean

# To really clean, we need to clean Javafe last since some of its
# tools are used in cleaning.
.PHONY: clean
clean: clean-norel clean-release clean-release-test

.PHONY: clean-release
clean-release:
	rm -rf ${RELDIR}

# Cleans everything except the release directory
.PHONY: clean-norel
clean-norel: clean-norel-noreltemp
	rm -rf ${RELTEMP}

# Cleans release test directory
.PHONY: clean-release-test
clean-release-test:
	rm -rf ${RELTEST}

# Cleans everything except the various release directories (test, temp, release)
.PHONY: clean-norel-noreltemp
clean-norel-noreltemp:
	rm -rf ${PATCH_DIR}
	for d in $(SUBDIRS) ; do \
		if [ !"$$d"=="Javafe" ]; then \
		    ( $(MAKE) -C $$d clean || exit 1) ; fi ; \
	done
	$(MAKE) -C docs clean
	$(MAKE) -C Javafe clean
	rm -f jars/*.jar		## FIXME is this used?
	rm -f tags TAGS

########################################### jmlspecs

.PHONY: jmlspecs-jar
jmlspecs-jar:
ifdef JML_ROOT
	${MAKE} -C ${JML_ROOT}/JML2 jmlspecs-jar
	cp ${JML_ROOT}/JML2/bin/jmlspecs.jar ${ESCTOOLS_ROOT}
else
	@true
endif


########################################### docs

.PHONY: docs
docs: textdocs
##docs: textdocs javadoc  ## FIXME Turn off until the javadoc target is fixed

.PHONY: textdocs
textdocs: 
	${MAKE} -C docs build

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
	rm -rf $(JAVADOC_GEN_DIR)
	mkdir -p $(JAVADOC_GEN_DIR)
	mkdir -p $(JAVADOC_GEN_DIR)/images
	cp $(JAVAFE_ROOT)/doc/javadoc/images/*.gif $(JAVADOC_GEN_DIR)/images
	$(JAVADOC) -sourcepath $(call canonicalize,$(JAVADOC_SOURCEPATH):$(JUNIT_SOURCEPATH)) \
	  -classpath $(call canonicalize,${CLASSPATH}:${JUNIT_LIB}) \
	  -private \
	  -doctitle "ESCTools API" \
	  -windowtitle "ESCTools" \
	  -author -version -use \
	  -linksource \
	  -tag warning -tag todo -tag note -tag design -tag usage \
	  -d $(JAVADOC_GEN_DIR) \
          $(PACKAGE_LIST)

## Should have -overview , header, footer, bottom, group, stylesheetfile
##    link/linkoffline, subpackages  FIXME

########################################### release

## FIXME: get mocha right

.PHONY: releases
releases: releases-notests 
	${MAKE} test-releases

.PHONY: test-releases
test-releases:
	@echo "Testing release versions .........."
	${MAKE} test-binary-release
	${MAKE} test-patch-release

.PHONY: releases-notests
releases-notests:
	@echo "Making release versions ${ESC_PROJECT}-${ESC_VERSION} ........"
	${MAKE} patch-release  ## does a clean as well
	${MAKE} binary-release

.PHONY: patch-release
patch-release: clean
	@echo "Creating patch release .........."
	rm -rf ${PATCH_DIR}
	mkdir -p ${PATCH_DIR}
	${MAKE} generate-patches generate-archives zero-length-files
	cp ${ESCTOOLS_ROOT}/install.sh ${PATCH_DIR}
	mkdir -p ${RELDIR}
	cd ${PATCH_DIR}; tar cvjf ${RELDIR}/${RELPATCHTAR} .
	rm -rf ${PATCH_DIR}

.PHONY: binary-release
binary-release: build docs
	@echo "Creating binary release .........."
	## RELDIR is the staging area for all files
	## First copy all .class files to sub and build a jar file
	mkdir -p ${RELDIR}
	rm -rf ${RELTEMP}
	mkdir -p ${RELTEMP}
	mkdir -p ${RELTEMP}/sub
	cp -r ${JAVAFE_CLASSFILES}/* ${RELTEMP}/sub
	cp -r ${ESCJAVA_CLASSFILES}/* ${RELTEMP}/sub
	cd ${RELTEMP}/sub; jar cf ../${RELJAR} *
	rm -rf ${RELTEMP}/sub
	## Now copy in all specs
	rm -rf ${RELTEMP}/specs
	cp -r ${ESCTOOLS_ROOT}/specs ${RELTEMP}
	-find ${RELTEMP}/specs -name "CVS" -exec rm -rf {} \;  >& /dev/null 
	## Copy other miscellaneous files
	cp docs/Escjava2-ImplementationNotes/*.pdf ${RELTEMP}
	cp docs/ESCJAVA-UsersManual.html ${RELTEMP}
	${MAKE} clean-norel-noreltemp
	${MAKE} -C Utils/junitutils build
	cp ${ESCJAVA_ROOT}/escj ${RELTEMP}
	cp ${ESCJAVA_ROOT}/escjava2.exe ${RELTEMP}
	cp ${ESCJ_SIMPLIFY_DIR}/Simplify-1.5.4* ${RELTEMP}
	cp README.first README.txt ${RELTEMP}
	cd release-files; cp `ls | grep -v CVS` ${RELTEMP}
	cp jmlspecs.jar ${RELTEMP}
	cd ${RELTEMP}; tar cjvf ${RELDIR}/${RELTAR} *
	rm -rf ${RELTEMP}


.PHONY: test-binary-release
test-binary-release:
	@echo "Testing binary release ............"
	rm -rf ${RELTEST}
	mkdir -p ${RELTEST}
	cp ${RELDIR}/${RELTAR} ${RELTEST}
	cd ${RELTEST} ;\
	    tar xjf ${RELTEST}/${RELTAR} ;\
	    ${RELTEST}/quicktest


## Note - we need to unset lots of environmental variables here because we
## want them to be reset based on the value of ESC_RELEASE in install.sh.
## Otherwise, since the variables are only conditionally set in Makefile.defs
## or in Makefile, they will continue to have the value already set in the
## current environment (when this Make was invoked) rather than getting new
## values when the Make in install.sh is invoked.  So include here any variable
## that is conditionally set and might have a different value when running a
## release than when running from the build environment.
.PHONY: test-patch-release
test-patch-release:
	@echo "Testing patch release ........"
	rm -rf ${RELTEST}
	mkdir -p ${RELTEST}
	cd ${RELTEST}; \
		tar xvjf ${RELDIR}/*patch.tbz ;\
		unset ESCTOOLS_ROOT ;\
		unset ESC_SPECS; \
		unset JUNIT_LIB ;\
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
.PHONY: generate-patches
generate-patches: clean
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

.PHONY: generate-archives
generate-archives: generate-toplevel-archive generate-specs-archive

.PHONY: generate-specs-archive
generate-specs-archive:
	mkdir -p ${RELTEMP}
	rm -rf ${RELTEMP}/specs
	cp -r ${ESCTOOLS_ROOT}/specs ${RELTEMP}
	-find ${RELTEMP}/specs -name "CVS" -exec rm -rf {} \;  >& /dev/null 
	(cd ${RELTEMP}; tar cjf ${PATCH_DIR}/${SPECS_TAR} specs;) 
	rm -rf ${RELTEMP}/specs

.PHONY: generate-toplevel-archive
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
	cp -r ${ESCTOOLS_ROOT}/Utils ${RELTEMP}/ESCTools
	cp -r ${ESCTOOLS_ROOT}/jars ${RELTEMP}/ESCTools
	cp ${ESCTOOLS_ROOT}/jmlspecs.jar ${RELTEMP}/ESCTools
	mkdir -p ${RELTEMP}/ESCTools/Escjava/release/master/bin
	cp ${ESCTOOLS_ROOT}/Escjava/release/master/bin/Simplify-1.5.4.macosx \
		${RELTEMP}/ESCTools/Escjava/release/master/bin
	-find ${RELTEMP}/ESCTools -name "CVS" -exec rm -rf {} \;  >& /dev/null 
	(cd ${RELTEMP}/ESCTools; tar cjf ${PATCH_DIR}/${TOPLEVEL_TAR} . ;) 
	rm -rf ${RELTEMP}/ESCTools

## Until we can figure out how to have diff/patch detect and generate
## 0 length files, we have to archive them up all independently.
.PHONY: zero-length-files
zero-length-files:
	mkdir -p ${PATCH_DIR}
	cd ${ESCTOOLS_ROOT}; \
	tar cjf ${PATCH_PREFIX}-ZeroLengthFiles.tbz \
		`find . -empty ! -name .M3SHIP`
	( cd ${ESCTOOLS_ROOT}; \
	  for f in `cd ${ESCTOOLS_ORIGINAL}; find . -empty`; do \
	      if [ ! -e $$f ]; then echo $$f; fi; \
	  done ) > ${PATCH_PREFIX}-emptyFilesThatDisappeared

############################################################################

## Run escjava on the specs
.PHONY: specs-test
specs-test:
	@echo TESTING specs
	cd specs; ${ESCJAVA} -quiet -classpath . java/*/*.spec

## This is simply a smoke test of the Makefile (particularly for Windows)
.PHONY: make-test
make-test:
	echo `cygpath -m $(ESCJ_SIMPLIFY_DIR)`
	echo ${foo}
