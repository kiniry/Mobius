# $Id$

export TOP = ../../..
include ${TOP}/Makefile.defs

############################################################################
# ESCJAVA is (only) used for standalone tests
ESCJAVA = ${ESCTOOLS_ROOT}/Escjava/escj 

_ECLASSPATH = $(call canonicalize,${ESC_CLASSPATH}:${JUNIT_UTILS_PATH}:.)
_CLASSPATH = $(call canonicalize,:${JUNIT_UTILS_PATH}:.)
_TMP = $(call canonicalize,/tmp)
_SIMP = $(call canonicalize,${ESCJ_SIMPLIFY})

_SPECS = $(call canonicalize,${ESC_SPECS})
_ESCROOT = $(call canonicalize,${ESCTOOLS_ROOT})

# Used to invoke text-based JUnit tests
export JUNIT = ${JAVA} -Xmx256M -classpath "${_CLASSPATH}" \
	-Djava.io.tmpdir=${_TMP} -Dsimplify=${_SIMP} \
	junit.textui.TestRunner

# Used to invoke GUI-based JUnit tests
export JUNITSW = $(JAVA) -Xmx256M -classpath "${_CLASSPATH}" \
	-Djava.io.tmpdir=${_TMP} -Dsimplify=${_SIMP} \
	junit.swingui.TestRunner

##############################################################################

.PHONY: buildtests
buildtests: lists
	$(JAVAC) -classpath "${_ECLASSPATH}" -source 1.4 `cat listfiles` \
		AllTests.java Suite.java LocalTestCase.java
	@echo "abc" > testfile

.PHONY: test runtests
test runtests: extests separate_java_tests

.PHONY: extests
extests: buildtests
	-${JUNIT} AllTests

.PHONY: swtests
swtests: buildtests
	-$(JUNITSW) AllTests

DEFAULTFLAGS = " "
ALWAYSFLAGS = -quiet -nowarn Deadlock -specs "${_SPECS}" -classpath "${_CLASSPATH}"

CHUNK = 40

.PHONY: lists
lists: Test*.java skip
	@-rm -f listtests listfiles
	@touch listtests
	@(ls Test*.java | grep -v -f skip > listfiles)
ifdef COMSPEC
	@for f in `cat listfiles `; do \
	        echo -n ${ALWAYSFLAGS} " " >> listtests ; \
	        ( grep FLAGS $$f || echo ${DEFAULTFLAGS} ) \
	        | sed -e 's?//#FLAGS:??' -e "s/\$$/ $$f/"  \
	        | sed -e "s@ESCTOOLS_ROOT@${ESCTOOLS_ROOT}@" \
	        | sed -e "s@.:..@.;..@" \
	        >> listtests ; \
	done
else
	@for f in `cat listfiles `; do \
	        echo -n ${ALWAYSFLAGS} " " >> listtests ; \
	        ( grep FLAGS $$f || echo ${DEFAULTFLAGS} ) \
	        | sed -e 's?//#FLAGS:??' -e "s/\$$/ $$f/"  \
		| sed -e "s@ESCTOOLS_ROOT@${ESCTOOLS_ROOT}@" \
	        >> listtests ; \
	done
endif

.PHONY: septest

.PHONY: provetests
provetests:
	@echo "Proving jdk tests..."
	${ESCJAVA} ${ALWAYSFLAGS} -classpath "${_CLASSPATH}" -specs "${_SPECS}" Test*.java

.PHONY: partjunittests
partjunittests: lists buildtests
	@echo "TESTING Escjava: junittests (in parts)"
	@$(MAKE) --no-print-directory lists
	@cp listtests listteststemp
	@cp listteststemp templist
	@while test -s templist ; do \
	    head -n ${CHUNK} templist > listtests ;\
	    ${MAKE} --no-print-directory quiet-junittests ;\
	    tail +${CHUNK} templist | tail +2 > templista ;\
	    mv templista templist; \
	done 
	@rm -f templist templista
	@mv listteststemp listtests

.PHONY: quiet-junittests
quiet-junittests:
	@$(JUNIT) Suite

.PHONY: separate_java_tests
separate_java_tests:
	@touch skip
	-@for f in `ls Test*.java | grep -v -f skip ` ; do \
		$(MAKE) --no-print-directory $${f}-test; \
	done

%.ex:
	$(JAVAC) -classpath "${_CLASSPATH}" $*.java
	-$(JUNIT) $*

%.test:
	@echo Testing $*
	$(MAKE) $*.ex
	(${ESCJAVA} ${ALWAYSFLAGS} -classpath "${_CLASSPATH}" -specs "${_SPECS}"\
		`grep '//#FLAGS:' $*.java | \
		sed -e "sx//#FLAGS:xx" -e "s@ESCTOOLS_ROOT@${ESCTOOLS_ROOT}@" ` \
		$(addsuffix .java,$*))

## This target (X-test) runs escjava against X.java, using any flags specified
## in X.java and comparing the output against the contents of X.java-expected.
## The actual output is stored in X.java-ckd if it is different.
%-test: 
	@echo Testing $* 
	@if [ ! -e $* ] ; then \
		echo No such file $* ;\
	else \
	(${ESCJAVA} ${ALWAYSFLAGS} -classpath "${_CLASSPATH}" -specs "${_SPECS}"\
		`grep '//#FLAGS:' $* | \
		sed -e "sx//#FLAGS:xx" -e "s@ESCTOOLS_ROOT@${ESCTOOLS_ROOT}@" ` \
		$* 2>&1 \
	        | sed -e "s#${_ESCROOT}#ESCTOOLSROOT#" \
                | tr '\\' '/'  \
	        | sed -e "s#${_ESCROOT}#ESCTOOLSROOT#" \
	        > $*-ckd ) || exit 0; \
	if [ -e $*-expected ] ; then \
		${DIFF} $*-ckd $*-expected  \
		  && rm $*-ckd ;\
	else \
		echo ... Creating $*-expected ;\
		mv $*-ckd $*-expected ;\
	fi ;\
	fi ;\

%-expected: %
	escjava ${ALWAYSFLAGS} \
		`grep '//#FLAGS:' $* | sed -e "sx//#FLAGS:xx"` $* 2>&1 > $@

.PHONY: clean
clean:
	@rm -f `cat .cvsignore` core*

