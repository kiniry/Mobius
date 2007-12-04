#
# MobiusLogging - An Advanced Logging and Debugging Framework for Java
# Copyright (c) 2007 Joseph Kiniry, University College Dublin
# Copyright (c) 1997-2001 Joseph Kiniry
# Copyright (c) 2000-2001 KindSoftware, LLC
# Copyright (c) 1997-1999 California Institute of Technology
# All Rights Reserved
#

#
# $Id: Makefile,v 1.2 2007/07/02 17:52:13 jkiniry Exp $
#

# The only thing that you need to change in this makefile to do a build on
# a new machine is the variable "jdkdir" below.  It should be set to the
# value of your JAVA_HOME environmental variable (the root of your JDK).

# Various environmental (shell) variables are documented below
# (e.g. QUIETJIKES, USEEMACS, etc.).  These variables are used to signal
# make to use various switches for various tools.

#---------------------------------------------------------------------
# Core
#---------------------------------------------------------------------

project =	MobiusLogging
version =	1.137-2001-Jun-19
release =	$(project)-$(version)

# Core directories.

basedir =	$(shell pwd)
srcreldir =	source
srcbasedir =	$(basedir)/$(srcreldir)
libdir =	$(basedir)/libs
jasssrcdir =	$(srcreldir)/idebug_jass

# Auto-library discovery of core JDK libs.

jdkdir =	/System/Library/Frameworks/JavaVM.framework/Versions/CurrentJDK
jdklibs0 =	$(subst $(space),:,$(wildcard $(jdkdir)/Classes/classes.jar))
jdklibs1 =	$(subst $(space),:,$(wildcard $(jdkdir)/jre/lib/*.jar))
jdklibs2 =	$(subst $(space),:,$(wildcard $(jdkdir)/jre/lib/ext/*.jar))
jdklibs3 =	$(subst $(space),:,$(wildcard /usr/local/Java/libs/*.jar))
jdklibs =	$(jdklibs0):$(jdklibs1):$(jdklibs2):$(jdklibs3)

# Jass setup.

jassclasspath =	/usr/local/Java/jass/jass.jar

# Servlet setup.
servletclasspath =	$(basedir)/jars/servlet.jar

# Auto-library discovery for UNIX and Windows.

empty:=
space:=		$(empty) $(empty)
unixlibpath =	$(subst $(space),:,$(wildcard $(libdir)/*.jar))
doslibpath =	$(subst $(space),;,$(wildcard $(libdir)/*.jar))
unixparents =	..:../..:../../..:../../../..:../../../../..
dosparents =	..;../..;../../..;../../../..;../../../../..
unixclasspath =	$(jassclasspath):$(servletclasspath):$(jdklibs):$(unixparents):$(unixlibpath):$(srcbasedir)
dosclasspath =	$(jassclasspath);$(servletclasspath);$(jdklibs);$(dosparents);$(doslibpath);$(srcbasedir)

# Top-level documentation.

htmlfiles =	$(wildcard $(basedir)/*.html)
textfiles =	$(subst .html,.txt,$(htmlfiles))

# Packages for classfile deliverables.

jarfile =	$(project).jar
zipfile =	$(project).zip
srcjar =	$(srcbasedir)/$(jarfile)
srczip =	$(srcbasedir)/$(zipfile)
srcarchives =	$(srcjar) $(srczip)

# Packages for full package deliverables.

tgzpkg =	$(basedir)/../$(release).tar.gz
zippkg = 	$(basedir)/../$(release).zip
jarpkg =	$(basedir)/../$(release).jar
archives =	$(tgzpkg) $(zippkg) $(jarpkg)

# Flags to pass to jikes and javac compilers.

corejikesflags =	-g -deprecation -depend
javacflags =		-g -deprecation

# Check to see if we are building on Windows.  If so, quote CLASSPATH
# but not JIKESPATH.  That's just how it works - it doesn't match the
# documentation.

ifdef COMSPEC
	export CLASSPATH = "$(dosclasspath)"
else
	export CLASSPATH = $(unixclasspath)
endif

ifdef COMSPEC
	export JIKESPATH = "$(CLASSPATH)"
else
	export JIKESPATH = $(CLASSPATH)
endif

# If the environmental variable QUIETJIKES is set to anything we'll tell
# jikes to not be pedantic and complain about "rendundant" interface
# information and the like that we actually like.

ifndef QUIETJIKES
	jikesflags =	$(corejikesflags) +P
else
	jikesflags =	$(corejikesflags)
endif

# If the environmental variable USEEMACS is set to anything we'll tell
# jikes to output errors and warning in an emacs-compatible format.

ifdef USEEMACS
	jflags =	$(jikesflags) +E
else
	jflags =	$(jikesflags)
endif

# If the environmental variable JAVAC is set to anything, we'll try
# to build with classic javac.  Otherwise, we'll use jikes.

ifdef JAVAC
	jc =		javac
	jflags =	$(javacflags)
else
	jc =		jikes
endif

# If the environmental variable JASSDEBUG is set to anything, we'll
# to process Jass input files with full contract checking enabled.
# Otherwise, we'll just process with pre-conditions enabled.

jasstransflags =	-nothing

ifdef JASSSHIP
	jassflags =	-source 1.4 -contract[pre]
else
	jassflags =	-source 1.4 -verbose -nothing
endif

jass =		java jass.Jass $(jassflags)
jasst =		java jass.Jass $(jasstransflags)

# If the environmental variables POLARDOC is set to anything, polardoc
# will be used to generate API docs.  Otherwise, standard javadoc is
# used.

ifdef POLARDOC
	docmaker =	polardoc
else
	docmaker =	javadoc
endif

# Flags to use during documentation generation.

docmakerflags =	-version -author -protected 

# Complete list of packages for API documentation generation.

stdpackages = \
	idebug \
	idebug.examples \
	idebug.testsuite

hcpackages = \
	idebug_jass \
	idebug_jass.examples \
	idebug_jass.testsuite

packages =	$(stdpackages) $(hcpackages)

# Sources

jassinterfaces =	$(srcreldir)/idebug_jass/DebugConstants.jass \
			$(srcreldir)/idebug_jass/DebugOutput.jass \
			$(srcreldir)/idebug_jass/examples/FrenchConstants.jass

hcjavainterfaces =	$(foreach jassfile,$(jassinterfaces),\
			$(subst .jass,.java,$(jassfile)))

hcclassinterfaces =	$(foreach javafile,$(hcjavainterfaces),\
			$(subst .java,.class,$(javafile)))

javainterfaces =	$(foreach hcjavafile,$(hcjavainterfaces),\
			$(subst idebug_jass,idebug,$(hcjavafile)))

classinterfaces =	$(foreach javaint,$(javainterfaces),\
			$(subst .java,.class,$(javaint)))

jassfiles =	$(wildcard $(srcreldir)/*/*.jass) \
		$(wildcard $(srcreldir)/*/*/*.jass)

hcjavafiles =	$(foreach jassfile,$(jassfiles),\
		$(subst .jass,.java,$(jassfile))) \
		$(hcjavainterfaces)

hcclassfiles =	$(foreach hcjavafile,$(hcjavafiles),\
		$(subst .java,.class,$(hcjavafile)))

stdjavafiles =	$(foreach hcjavafile,$(hcjavafiles),\
		$(subst idebug_jass,idebug,$(hcjavafile)))

stdclassfiles =	$(foreach javafile,$(stdjavafiles),\
		$(subst .java,.class,$(javafile)))

javafiles =	$(hcjavafiles) $(stdjavafiles)

classfiles = 	$(hcclassfiles) $(stdclassfiles)

classfiles_nopath =	$(subst $(srcreldir)/,,$(classfiles))

# The full set of directories containing source code for use during
# documentation generation.

sourcedirs =	$(srcreldir)

# Root of documentation.

basedocdir =	$(basedir)/docs

# Location of user manual.

manualdir =	$(basedocdir)/manual

# Location of html version of user manual.

htmlmanualdir =	$(manualdir)/html

# Destination for API documententation.

javadocdir =	$(basedocdir)/javadoc

# Copyright on documentation.

copyright = "MobiusLogging<br />&copy; 2007 Joseph Kiniry, University College Dublin<br />&copy; 1997-2001 Joseph Kiniry<br />&copy; 2000-2001 KindSoftware, LLC<br />&copy; 1997-1999 Caltech<br />All Rights Reserved"

# All current source code for entire project.

allsource =	$(javafiles) \
		$(wildcard $(srcreldir)/*.java) \
		$(wildcard $(srcreldir)/*/*.java) \
		$(wildcard $(srcreldir)/*/*/*.java)

#---------------------------------------------------------------------
# Rules
#---------------------------------------------------------------------

.PHONY: all 
.PHONY: distribution cleanup clean clean_testfiles clean_archives clean_distribution
.PHONY: textfiles archives sources classes clean_source test onetest 
.PHONY: documentation javadocs manual clean_docs clean_html clean_javadoc
.PHONY: packaging clean_packaging

all:	textfiles sources documentation packaging distribution

distribution:	cleanup
	find . -name "*.gz" | xargs rm -f
	(cd ..; tar czf $(release).tar.gz $(project))
	(cd ..; zip -uro $(release).zip $(project))
	(cd ..; jar cf $(release).jar $(project))

cleanup:
	find . \( -name "*~" -o \
		-name ".??*~" -o \
		-name "*#" -o \
		-name "core" -o \
		-name ".auto" -o \
		-name "*.class" -o \
		-name "*.aux" -o \
		-name "*.log" -o \
		-name "*.bbl" -o \
		-name "*.blg" \) | xargs rm -rf

clean:	cleanup clean_textfiles clean_docs \
	clean_source clean_archives clean_distribution

clean_textfiles:
	rm -f $(textfiles)

clean_archives:
	rm -f $(srcarchives)

clean_distribution:
	rm -f $(archives)

textfiles: $(textfiles)

archives: $(srcjar) $(srczip)

%.txt: %.html
	lynx -dump $< > $(basename $<).txt

#---------------------------------------------------------------------
# Core Source
#---------------------------------------------------------------------

sources:	$(javainterfaces) $(stdjavafiles) \
		$(hcjavainterfaces) $(hcjavafiles) \
		$(classfiles)

source/idebug/%.java: source/idebug_jass/%.jass
	(cd $(srcreldir); \
	cat $(subst $(srcreldir)/,,$<) | sed s/idebug_jass/idebug/ > \
	$(subst idebug_jass,idebug,$(subst .jass,.java,$(subst $(srcreldir)/,,$<))))

source/idebug_jass/%.java: source/idebug_jass/%.jass
	(cd $(srcreldir); $(jass) $(subst $(srcreldir)/,,$<))

classes:	$(classfiles)

TAGS:	$(allsource)
	(cd $(srcreldir); jtags)

source/%.class: source/%.java
	(cd $(srcreldir); $(jc) $(jflags) $(subst $(srcreldir)/,,$<))

clean_source:
	rm -f $(classfiles) \
		$(hcjavafiles) $(stdjavafiles) \
		$(otherclassfiles)

#---------------------------------------------------------------------
# Tests
#---------------------------------------------------------------------

test:	sources
	(cd $(srcreldir); \
		java idebug_jass.testsuite.TestSuite --console; \
		java idebug.testsuite.TestSuite --console; \
		java idebug_jass.testsuite.TestSuite --servletlog; \
		java idebug.testsuite.TestSuite --servletlog; \
		java idebug_jass.testsuite.TestSuite --window; \
		java idebug.testsuite.TestSuite --window; \
		java idebug_jass.testsuite.TestSuite --writer; \
		java idebug.testsuite.TestSuite --writer)

onetest:	sources
	(cd $(srcreldir); \
		java idebug_jass.testsuite.TestSuite --window;)

#---------------------------------------------------------------------
# Docs
#---------------------------------------------------------------------

documentation:	javadocs manual

javadocs:	$(javadocdir)/index.html

manual:	$(manualdir)/idebug.dvi $(manualdir)/idebug.ps \
	$(manualdir)/idebug.pdf $(htmlmanualdir)/idebug.html

clean_docs:
	rm -rf $(htmlmanualdir)/*.html $(htmlmanualdir)/*.gif \
		$(htmlmanualdir)/*.css \
		$(htmlmanualdir)/images.tex $(htmlmanualdir)/img_params.db \
		$(manualdir)/*.gz $(manualdir)/*.dvi \
		$(manualdir)/*.ps $(manualdir)/*.pdf

# Note that this rule only completely works on Joe Kiniry's machine since
# he has the full bibliography for the manual.

%.pdf:	%.tex
	(cd $(dir $<); ln -s ~/Projects/papers/kiniry/bibliography .; \
		pdflatex $(notdir $<); \
		bibtex $(basename $(notdir $<)); \
		pdflatex $(notdir $<); pdflatex $(notdir $<); \
		rm bibliography)

%.ps:	%.dvi
	dvips -f < $< > $@

%.pdf.gz:	%.pdf
	gzip -c $< > $@

%.ps.gz:	%.ps
	gzip -c $< > $@

# Note that the IDebug technical report with not be complete because the
# bibliography is not included with the release.  The core of the document
# will be rendered properly.

$(manualdir)/idebug.dvi:	$(manualdir)/idebug.tex
	(cd $(dir $<); ln -s ~/Projects/papers/kiniry/bibliography .; \
		latex idebug; bibtex idebug; \
		latex idebug; latex idebug; \
		rm bibliography)

$(htmlmanualdir)/idebug.html:	$(manualdir)/idebug.tex
	(cd $(manualdir); \
		latex2html -split 4 -address kiniry@acm.org \
			-local_icons -dir html idebug); \
	make clean_html

clean_html:
	rm -rf $(htmlmanualdir)/.???* $(htmlmanualdir)/*.pl \
		$(htmlmanualdir)/tmp $(htmlmanualdir)/WARNINGS \
		$(htmlmanualdir)/l2h* $(htmlmanualdir)/*.old

clean_javadoc:
	rm -rf $(javadocdir)/*.html \
		$(javadocdir)/idebug* \
		$(javadocdir)/images \
		$(javadocdir)/package-list \
		$(javadocdir)/stylesheet.css

#
# For Javadoc 1.2 and above.
#
$(javadocdir)/index.html: $(javafiles)
	mkdir $(javadocdir); \
	$(docmaker) -d $(javadocdir) $(docmakerflags) \
	-sourcepath $(sourcedirs) \
	-overview docs/overview.html \
	-doctitle "MobiusLogging: A Logging and Debugging Framework for Java" \
	-header $(copyright) \
	-footer $(copyright) \
	$(hcpackages)

#---------------------------------------------------------------------
# Packaging
#---------------------------------------------------------------------

VERSION:	sources
	find $(jasssrcdir) -name "*.jass" | xargs grep "\$$Id" | \
	awk "{ print \$$5 }" | sed s/1.// | awk "{ x = x + \$$0 ; print x}"

packaging:	$(srcjar) $(srczip)

clean_packaging:
	rm -f $(srcjar) $(srczip)

$(srcjar):	$(classfiles)
	(cd $(srcreldir); jar cf $(jarfile) $(classfiles_nopath))

$(srczip):	$(classfiles)
	(cd $(srcreldir); zip -ugo $(zipfile) $(classfiles_nopath))
