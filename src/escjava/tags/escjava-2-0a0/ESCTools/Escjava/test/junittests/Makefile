TOP = ../../..
include ${TOP}/Makefile.defs

############################################################################
# ESCJAVA is (only) used for standalone tests
## FIXME: escjava is not part of the CVS infrastructure
export ESCJAVA = escjava -nowarn Deadlock -verboseTrace

# Used to invoke text-based JUnit tests
export JUNIT = $(JAVA) -Xmx256M -classpath ${ESCJAVA_CLASSPATH}:${JUNIT_UTILS_PATH}:. -Djava.io.tmpdir=/tmp -Dsimplify=${ESCJ_SIMPLIFY_SCRIPT} junit.textui.TestRunner

# Used to invoke GUI-based JUnit tests
export JUNITSW = $(JAVA) -Xmx256M -classpath ${ESCJAVA_CLASSPATH}:${JUNIT_UTILS_PATH}:. -Djava.io.tmpdir=/tmp -Dsimplify=${ESCJ_SIMPLIFY_SCRIPT} junit.swingui.TestRunner

##############################################################################
.PHONY: buildtests
buildtests:
	$(JAVAC) -classpath .:${JUNIT_UTILS_PATH}:${ESCJAVA_CLASSPATH} TestSuite.java

test runtests: buildtests
	$(MAKE) skips
	$(MAKE) dotests

.PHONY: dotests
dotests: lists
	$(JUNIT) TestSuite

.PHONY: swtests
swtests: lists
	$(JUNITSW) TestSuite

ALWAYSFLAGS = -nowarn Deadlock -verboseTrace -testMode
DEFAULTFLAGS = " "

OTHERTESTS = RefineT.t SpecFile.jml RefineNoJava.refines-java

.PHONY: lists
lists:
	@rm -f listtests
	@touch listtests
	@for f in `ls *.java ${OTHERTESTS} | grep -v -f skip`; do \
		echo -n ${ALWAYSFLAGS} " " >> listtests ; \
		( grep FLAGS $$f || echo ${DEFAULTFLAGS} ) \
		| sed -e 's?//#FLAGS:??' -e "s/\$$/ $$f/" >> listtests ; \
	done

septest: skips othertests 
	@touch skip
	@for f in `ls *.java | grep -v -f skip` ; do \
		$(MAKE) --no-print-directory $${f}-test; \
	done

skips:
	@echo Skipped: `cat skip | grep -v "^#" `

othertests: $(addsuffix -test,${OTHERTESTS})

# The sed -e s/x/x/ is just meant to be a noop since I can't seem
# to get 2>&1 > to work in order to output directly into the -ckd file
# (FIXME)
%-test: 
	@echo Testing $* 
	@-(${ESCJAVA} -testMode `grep '//#FLAGS:' $* | sed -e "sx//#FLAGS:xx" ` $* 2>&1 | sed -e s/x/x/ > $*-ckd ) || exit 0;
	@if [ -e $*-expected ] ; then \
		diff $*-ckd $*-expected  \
		  && rm $*-ckd ;\
	else \
		echo ... Creating $*-expected ;\
		mv $*-ckd $*-expected ;\
	fi ;\

%-expected: %
	escjava -testMode `grep '//#FLAGS:' $* | sed -e "sx//#FLAGS:xx" ` $* 2>&1 > $@

clean:
	@rm -f `cat .cvsignore` core*
