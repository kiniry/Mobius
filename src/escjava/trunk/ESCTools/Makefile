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
##	test  - runs the tests (biuld must have been run)
##	docs  - creates all docs; to get javadocs you must execute the
##		make from this directory
##	all   - does all of the above
##
## You can run each of these in a subdirectory and only apply it to
## the code in that subdirectory, if you like.  Note though, that the
## subdirectories other than Javafe presume that Javafe has been
## built.

## release -- What about this ??? FIXME

# List subprojects in the order in which they should be built.  Javafe
# must be before any other Esctool directories.
SUBDIRS = Utils Javafe Escjava

default: build

all: clean build test docs

build buildall test: check_env
	for d in $(SUBDIRS) ; do \
	    $(MAKE) -C $$d $@ ; \
	done

# To really clean, we need to clean Javafe last since some of its
# tools are used in cleaning.
clean: check_env
	for d in $(SUBDIRS) ; do \
		if [ ! $$d == Javafe ]; then $(MAKE) -C $$d $@ ; fi ; \
	done
	$(MAKE) -C Javafe clean

## Javadoc depends on the build target since some of the .java files
## are generated in the course of the build (e.g. the AST classes).
docs: build javadoc
	for d in $(SUBDIRS) ; do \
	    $(MAKE) -C $$d $@ ; \
	done

PACKAGE_LIST = escjava escjava.ast escjava.backpred escjava.parser \
	  escjava.prover escjava.tc escjava.translate escjava.sp \
	  escjava.reader \
          javafe javafe.ast javafe.parser  \
	  javafe.reader javafe.genericfile javafe.filespace \
	  javafe.tc javafe.util

JAVADOC_SOURCEPATH = $(subst : ,:,$(addsuffix /java:,$(addprefix $(ESCTOOLS_ROOT)/,$(SUBDIRS))))

.PHONY: javadoc
javadoc: 
	mkdir -p $(JAVADOC_GEN_DIR)/images
	cp $(JAVAFE_ROOT)/doc/javadoc/images/*.gif $(JAVADOC_GEN_DIR)/images
	$(JAVADOC) -sourcepath $(JAVADOC_SOURCEPATH) \
	  -d $(JAVADOC_GEN_DIR) \
          $(PACKAGE_LIST)

.PHONY: check_env
check_env:
	@if [ ! -d ${ESCTOOLS_ROOT} ] ; then \
	    echo "Error: ESCTools root not found: ${ESCTOOLS_ROOT}" ;\
	    echo "Set the variable ESCTOOLS_ROOT in your environment or in Makefile.local" ;\
	fi
	@if [ ! -d ${JAVAFE_ROOT} ]; then \
	    echo "Error: Javafe root not found: ${JAVAFE_ROOT}" ;\
	    echo "Javafe should be a subdirectory of the value of ESCTOOLS_ROOT"; \
	fi
	@if [ ! -d ${ESCJAVA_ROOT} ]; then \
	    echo "Error: EscJava root not found: ${ESCJAVA_ROOT}" ;\
	    echo "Escjava should be a subdirectory of the value of ESCTOOLS_ROOT"; \
	fi
	@if [ ! -d ${JDKSPEC_ROOT} ]; then \
	    echo "Error: JDK spec root not found: ${JDKSPEC_ROOT}" ;\
	    echo "Set the variable JDKSPEC_ROOT in your environment or in Makefile.local" ;\
	fi
