TOP = ../../..
include ${TOP}/Makefile.defs

##export CLASSPATH=
export ESCJAVA = escjava -nowarn Deadlock -verboseTrace
export JUNIT = $(JAVA) -Xmx256M -classpath ${ESCJAVA_CLASSPATH}:${JUNIT_UTILS_PATH}:. -Djava.io.tmpdir=/tmp -Dsimplify=${ESCJAVA_ROOT}/simplify junit.textui.TestRunner
export JUNITSW = $(JAVA) -Xmx256M -classpath ${ESCJAVA_CLASSPATH}:${JUNIT_UTILS_PATH}:. -Djava.io.tmpdir=/tmp -Dsimplify=${ESCJAVA_ROOT}/simplify junit.swingui.TestRunner

buildtests:
	javac -classpath .:${JUNIT_UTILS_PATH}:${ESCJAVA_CLASSPATH} TestSuite.java

runtests: buildtests skips lists dotests

.PHONY: dotests
dotests:
	$(JUNIT) TestSuite

.PHONY: swtests
swtests:
	$(JUNITSW) TestSuite

ALWAYSFLAGS = -nowarn Deadlock -verboseTrace -testMode
DEFAULTFLAGS = " "

.PHONY: lists
lists:
	@rm listtests
	@touch listtests
	@for f in `ls *.java | grep -v -f skip`; do \
		echo -n ${ALWAYSFLAGS} " " >> listtests ; \
		( grep FLAGS $$f || echo ${DEFAULTFLAGS} ) \
		| sed -e 's?//#FLAGS:??' -e "s/\$$/ $$f/" >> listtests ; \
	done

test: skips othertests 
	@touch skip
	@for f in `ls *.java | grep -v -f skip`; do \
	    echo Testing $${f} ;\
	    ${ESCJAVA} -testMode `grep '//#FLAGS:' $${f} | sed -e "sx//#FLAGS:xx" ` $$f 2>&1 > $${f}-ckd ; \
	    if [ -e $${f}-expected ] ; then \
		diff $${f}-ckd $${f}-expected  \
		  && rm $${f}-ckd ;\
	    else \
		echo ... Creating $${f}-expected ;\
		mv $${f}-ckd $${f}-expected ;\
	    fi ;\
	done

skips:
	@echo Skipped: `cat skip`

othertests: SpecFile.jml-test

%-test: 
	@echo Testing $* 
	@-escjava -testMode `grep '//#FLAGS:' $* | sed -e "sx//#FLAGS:xx" ` $* 2>&1 > $*-ckd 
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
