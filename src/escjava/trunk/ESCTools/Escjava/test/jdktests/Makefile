TOP = ../../..
include ${TOP}/Makefile.defs

############################################################################
# ESCJAVA is (only) used for standalone tests
ESCJAVA = ${ESCTOOLS_ROOT}/Escjava/escj 

##_CLASSPATH = $(call canonicalize,${ESCTOOLS_ROOT}/Escjava/java/daikon-instrumented:${ESC_CLASSPATH}:${JUNIT_UTILS_PATH}:.:/home/cok/Daikon/daikon/daikon.jar:/home/cok/Daikon/daikon/java/ajax-ship/ajax.jar)
_CLASSPATH = ${ESC_CLASSPATH}$(call canonicalize,:${JUNIT_UTILS_PATH}:.)
_TMP = $(call canonicalize,/tmp)
_SIMP = $(call canonicalize,${ESCJ_SIMPLIFY})
_SPECS = $(call canonicalize,.:${ESC_SPECS})

# Used to invoke text-based JUnit tests
export JUNIT = ${JAVA} -Xmx256M -classpath "${_CLASSPATH}" \
	junit.textui.TestRunner

# Used to invoke GUI-based JUnit tests
export JUNITSW = $(JAVA) -Xmx256M -classpath "${_CLASSPATH}" \
	junit.swingui.TestRunner

##############################################################################
.PHONY: buildtests
buildtests:
	$(JAVAC) -classpath "${_CLASSPATH}" *.java

.PHONY: test runtests
test runtests: extests provetests

.PHONY: extests
extests: buildtests
	${JUNIT} AllTests


.PHONY: swtests
swtests: lists
	$(JUNITSW) AllTests


DEFAULTFLAGS = " "

CHUNK = 40

.PHONY: provetests
provetests:
	echo "Proving jdk tests..."
	${ESCJAVA} -quiet -nowarn Deadlock -classpath "${_CLASSPATH}" -specs "${_SPECS}" Test*.java

.PHONY: partjunittests
partjunittests:
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


.PHONY: sepjavatests
sepjavatests:
	@touch skip
	@for f in `ls *.java | grep -v -f skip -f notjunittests` ; do \
		$(MAKE) --no-print-directory $${f}-test; \
	done

%-test: 
	@echo Testing $* 
	@if [ ! -e $* ] ; then \
		echo No such file $* ;\
	else \
	(${ESCJAVA} ${ALWAYSFLAGS} \
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

