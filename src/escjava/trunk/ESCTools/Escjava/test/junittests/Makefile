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
_SPECS = $(call canonicalize,.:${ESC_SPECS})

# Used to invoke text-based JUnit tests
export JUNIT = ${JAVA} -Xmx256M -classpath "${_CLASSPATH}" \
	-Djava.io.tmpdir=${_TMP} -Dsimplify=${_SIMP} junit.textui.TestRunner

# Used to invoke GUI-based JUnit tests
export JUNITSW = $(JAVA) -Xmx256M -classpath "${_CLASSPATH}" \
	-Djava.io.tmpdir=${_TMP} -Dsimplify=${_SIMP} junit.swingui.TestRunner

##############################################################################
.PHONY: buildtests
buildtests:
	$(JAVAC) -classpath "${_CLASSPATH}" TestSuite.java
	cp Binary.javax Binary.java
	javac Binary.java
	rm Binary.java

.PHONY: test runtests
test runtests: buildtests
	$(MAKE) skips
	$(MAKE) dotests

.PHONY: dotests
dotests: lists
	-$(MAKE) notjunittests
	-$(MAKE) partjunittests

.PHONY: junittests
junittests:
	@echo TESTING Escjava: junittests
	$(JUNIT) TestSuite

.PHONY: quiet-junittests
quiet-junittests:
	@$(JUNIT) TestSuite

.PHONY: dotests-nolist
dotests-nolist:
	$(JUNIT) TestSuite

.PHONY: swtests
swtests: lists
	$(JUNITSW) TestSuite

.PHONY: canonicalize_paths
canonicalize_paths:
ifdef COMSPEC
	@if [ ! -f .canonicalized ]; then \
		for i in *-expected; do \
			cat $${i} | sed -e "s/\\.\\//\\.\\\\/" > tmp-expected; \
			rm $${i}; mv tmp-expected $${i}; \
		done; \
	fi
	@touch .canonicalized
endif

ALWAYSFLAGS = -nowarn Deadlock -verboseTrace -testMode -classpath "${_SPECS}"

DEFAULTFLAGS = " "

## This lists files without .java suffixes that need to be added to the
## set of junittests
OTHERTESTS = \
	RefineT.t SpecFile.jml RefineNoJava.refines-java \
	Binary.refines-spec NoPublic.refines-spec

## These have output that depends on initialization (e.g. what has already 
## happened in the previous junittests), so the output is more stable when
## run separately
NOTJUNITTESTS = 
ifdef PDTESTS
## These are platform-dependent tests or tests whose output is a bit random
NOTJUNITTESTS += $(shell cat notjunittests | grep -v -f skip)
endif

.PHONY: lists
lists:
	@rm -f listtests
	@touch listtests
ifdef COMSPEC
	@for f in `ls *.java ${OTHERTESTS} | grep -v -f skip -f notjunittests`; do \
		echo -n ${ALWAYSFLAGS} " " >> listtests ; \
		( grep FLAGS $$f || echo ${DEFAULTFLAGS} ) \
		| sed -e 's?//#FLAGS:??' -e "s/\$$/ $$f/"  \
		| sed -e "s@ESCTOOLS_ROOT@${ESCTOOLS_ROOT}@" \
		| sed -e "s@.:..@.;..@" \
		>> listtests ; \
	done
else
	@for f in `ls *.java ${OTHERTESTS} | grep -v -f skip -f notjunittests`; do \
		echo -n ${ALWAYSFLAGS} " " >> listtests ; \
		( grep FLAGS $$f || echo ${DEFAULTFLAGS} ) \
		| sed -e 's?//#FLAGS:??' -e "s/\$$/ $$f/"  \
		| sed -e "s@ESCTOOLS_ROOT@${ESCTOOLS_ROOT}@" \
		>> listtests ; \
	done
endif

.PHONY: septest
septest:
	$(MAKE) skips
	$(MAKE) othertests
	$(MAKE) sepjavatests
	$(MAKE) notjunittests

.PHONY: notjunittests
notjunittests:
	@echo TESTING Escjava: notjunittests
	@touch skip
	@-for f in ${NOTJUNITTESTS} ; do \
		$(MAKE) --no-print-directory $${f}-test; \
	done

CHUNK = 40

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

.PHONY: skips
skips:
	@touch skip
	@echo Skipped: `cat skip | grep -v "^#" `

.PHONY: othertests
othertests: $(addsuffix -test,${OTHERTESTS})

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

