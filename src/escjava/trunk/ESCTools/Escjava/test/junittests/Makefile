TOP = ../../..
include ${TOP}/Makefile.defs

############################################################################
# ESCJAVA is (only) used for standalone tests
## FIXME: escjava is not part of the CVS infrastructure
export ESCJAVA ?= escjava -nowarn Deadlock -verboseTrace

# Used to invoke text-based JUnit tests
export JUNIT = $(JAVA) -Xmx256M -classpath ${ESCJAVA_CLASSPATH}:${JUNIT_UTILS_PATH}:. -Djava.io.tmpdir=/tmp -Dsimplify=${ESCJ_SIMPLIFY} junit.textui.TestRunner

# Used to invoke GUI-based JUnit tests
export JUNITSW = $(JAVA) -Xmx256M -classpath ${ESCJAVA_CLASSPATH}:${JUNIT_UTILS_PATH}:. -Djava.io.tmpdir=/tmp -Dsimplify=${ESCJ_SIMPLIFY} junit.swingui.TestRunner

# The default is to run tests without any spec files.  This is to keep them
# robust against changes in specs.  You can adjust this by adding 
# explicit command-line settings in any particular test.
export ESC_SPECS = :

##############################################################################
.PHONY: buildtests
buildtests:
	$(JAVAC) -classpath .:${JUNIT_UTILS_PATH}:${ESCJAVA_CLASSPATH} TestSuite.java
	cp Binary.javax Binary.java
	javac Binary.java
	rm Binary.java

test runtests: buildtests
	$(MAKE) skips
	$(MAKE) dotests

.PHONY: dotests
dotests: lists
	$(MAKE) notjunittests
	$(JUNIT) TestSuite

dotests-nolist: 
	$(JUNIT) TestSuite

.PHONY: swtests
swtests: lists
	$(JUNITSW) TestSuite

ALWAYSFLAGS = -nowarn Deadlock -verboseTrace -testMode -classpath .
DEFAULTFLAGS = " "

## This lists files without .java suffixes that need to be added to the
## set of junittests
OTHERTESTS = RefineT.t SpecFile.jml RefineNoJava.refines-java Binary.refines-spec NoPublic.refines-spec

## These have output that depends on initialization (e.g. what has already 
## happened in the previous junittests), so the output is more stable when
## run separately
NOTJUNITTESTS = Desugaring.java FormalNonnullInheritance.java 
## DesugaringA.java
## InheritedSpecs.java NL.java

.PHONY: lists
lists:
	@rm -f listtests
	@touch listtests
	@for f in `ls *.java ${OTHERTESTS} | grep -v -f skip`; do \
		echo -n ${ALWAYSFLAGS} " " >> listtests ; \
		( grep FLAGS $$f || echo ${DEFAULTFLAGS} ) \
		| sed -e 's?//#FLAGS:??' -e "s/\$$/ $$f/"  \
		| sed -e "s@ESCTOOLS_ROOT@${ESCTOOLS_ROOT}@" >> listtests ; \
	done

septest: 
	$(MAKE) skips
	$(MAKE) othertests
	$(MAKE) sepjavatests
	$(MAKE) notjunittests

notjunittests:
	@touch skip
	@for f in  ${NOTJUNITTESTS} ; do \
		$(MAKE) --no-print-directory $${f}-test; \
	done

sepjavatests:
	@touch skip
	@for f in `ls *.java | grep -v -f skip` ; do \
		$(MAKE) --no-print-directory $${f}-test; \
	done

skips:
	@touch skip
	@echo Skipped: `cat skip | grep -v "^#" `

othertests: $(addsuffix -test,${OTHERTESTS})

# I can't seem
# to get 2>&1 > to work in order to output directly into the -ckd file
# (FIXME)
%-test: 
	@echo Testing $* 
	@if [ ! -e $* ] ; then \
		echo No such file $* ;\
	else \
	(${ESCJAVA} -testMode -classpath . `grep '//#FLAGS:' $* | sed -e "sx//#FLAGS:xx" -e "s@ESCTOOLS_ROOT@${ESCTOOLS_ROOT}@" ` $* 2>&1 | sed -e s/x/x/ > $*-ckd ) || exit 0; \
	if [ -e $*-expected ] ; then \
		diff $*-ckd $*-expected  \
		  && rm $*-ckd ;\
	else \
		echo ... Creating $*-expected ;\
		mv $*-ckd $*-expected ;\
	fi ;\
	fi ;\

%-expected: %
	escjava -testMode `grep '//#FLAGS:' $* | sed -e "sx//#FLAGS:xx" ` $* 2>&1 > $@

clean:
	@rm -f `cat .cvsignore` core*

