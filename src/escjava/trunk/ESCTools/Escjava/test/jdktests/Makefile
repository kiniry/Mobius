TOP = ../../..
include ${TOP}/Makefile.defs

############################################################################
# ESCJAVA is (only) used for standalone tests
ESCJAVA = ${ESCTOOLS_ROOT}/Escjava/escj 

##_CLASSPATH = $(call canonicalize,${ESCTOOLS_ROOT}/Escjava/java/daikon-instrumented:${ESC_CLASSPATH}:${JUNIT_UTILS_PATH}:.:/home/cok/Daikon/daikon/daikon.jar:/home/cok/Daikon/daikon/java/ajax-ship/ajax.jar)
    ## FIXME - the following line does not properly concatenate
_CLASSPATH = ${ESC_CLASSPATH}$(call canonicalize,:${JUNIT_UTILS_PATH}:.)
_TMP = $(call canonicalize,/tmp)
_SIMP = $(call canonicalize,${ESCJ_SIMPLIFY})
_SPECS = $(call canonicalize,${ESC_SPECS})

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
buildtests:
	$(JAVAC) -classpath "${_CLASSPATH}" -source 1.4 *.java

.PHONY: test runtests
test runtests: extests sepjavatests

.PHONY: extests
extests: buildtests
	-${JUNIT} AllTests


.PHONY: swtests
swtests: lists
	-$(JUNITSW) AllTests


DEFAULTFLAGS = " "
ALWAYSFLAGS = -quiet -nowarn Deadlock -specs "${_SPECS}" -classpath "${_CLASSPATH}"

CHUNK = 40

.PHONY: lists
lists: Test*.java
	@rm -f listtests
	@touch listtests
ifdef COMSPEC
	@for f in `ls Test*.java | grep -v -f skip `; do \
	        echo -n ${ALWAYSFLAGS} " " >> listtests ; \
	        ( grep FLAGS $$f || echo ${DEFAULTFLAGS} ) \
	        | sed -e 's?//#FLAGS:??' -e "s/\$$/ $$f/"  \
	        | sed -e "s@ESCTOOLS_ROOT@${ESCTOOLS_ROOT}@" \
	        | sed -e "s@.:..@.;..@" \
	        >> listtests ; \
	done
else
	@for f in `ls Test*.java | grep -v -f skip `;
do \
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
	echo "Proving jdk tests..."
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

.PHONY: sepjavatests
sepjavatests:
	@touch skip
	@for f in `ls Test*.java | grep -v -f skip ` ; do \
		$(MAKE) --no-print-directory $${f}-test; \
	done

%.test:
	@echo Testing $*
	$(JUNIT) $*
	(${ESCJAVA} -counterexample ${ALWAYSFLAGS} -classpath "${_CLASSPATH}" -specs "${_SPECS}"\
		`grep '//#FLAGS:' $*.java | \
		sed -e "sx//#FLAGS:xx" -e "s@ESCTOOLS_ROOT@${ESCTOOLS_ROOT}@" ` \
		$(addsuffix .java,$*))

%-test: 
	@echo Testing $* 
	@if [ ! -e $* ] ; then \
		echo No such file $* ;\
	else \
	(${ESCJAVA} ${ALWAYSFLAGS} -classpath "${_CLASSPATH}" -specs "${_SPECS}"\
		`grep '//#FLAGS:' $* | \
		sed -e "sx//#FLAGS:xx" -e "s@ESCTOOLS_ROOT@${ESCTOOLS_ROOT}@" ` \
		$* 2>&1 | sed -e s/x/x/ > $*-ckd ) || exit 0; \
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

