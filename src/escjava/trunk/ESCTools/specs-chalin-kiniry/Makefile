RELEASE = v0.1
BASE	= paper
BIBTEXOPT = 
BIBWARN = 'LaTeX Warning: Citation'
REFWARN = 'Rerun to get cross-references'
LATEXMAX = 6
FIGSCALE = 0.5

# CLASSPATH components

CORECP	= .
BOOTCP	= ~/Sandboxes/JML2/specs:~/Sandboxes/JML2/:/System/Library/Frameworks/JavaVM.framework/Versions/1.4.2/Classes/classes.jar
JMLCP	= /home/rg/JML/bin/jmlruntime.jar:/home/rg/JML/bin/jmljunitruntime.jar
JUNITCP	= /usr/share/java/junit.jar
CHECKSTYLECP	= /usr/local/checkstyle/checkstyle-optional.jar:/usr/local/checkstyle/checkstyle-all.jar

# local variables for build process

basedocdir =	doc
srcpath =	src
timestamppath =	timestamps
jdksrcpath =	/usr/local/Java/src/jdk-1.4
specpath =	specs
buildpath =	build
jmlc_path =	jmlc
jmlunit_path =	jmlunit
escjava =	escjava2 -source 1.4 -vclimit 2500000 -sourcepath src

# Various CLASSPATH constructions

BASE_CLASSPATH	= $(CORECP):$(JUNITCP):$(JMLCP)
JAVAC_CLASSPATH	= $(buildpath):$(BASE_CLASSPATH)
JMLC_CLASSPATH	= $(jmlc_path):$(BASE_CLASSPATH)
JUNIT_CLASSPATH	= $(jmlc_path):$(BASE_CLASSPATH)
ESCJAVA_CLASSPATH	= $(CORECP):$(JUNITCP):$(JMLCP)
UNIT_TEST_CLASSPATH	= $(jmlc_path):$(buildpath):$(JUNITCP)
CHECKSTYLE_CLASSPATH	= $(CORECP):$(CHECKSTYLECP)

javapat	=	$(srcpath)/*java
javafiles =	$(wildcard $(srcpath)/*java)
readme_file =	README.TXT
version_file =	VERSION.TXT
usermanual_dir = usermanual
usermanual_tex = $(usermanual_dir)/usermanual.tex
usermanual_pdf = $(usermanual_dir)/usermanual.pdf
usermanual_ps = $(usermanual_dir)/usermanual.ps
jmlunitpat =	$(jmlunit_path)/*java
jmlunitfiles =	$(wildcard $(jmlunit_path)/*java)
generated_jmlunitfiles	=	$(wildcard $(jmlunit_path)/*_JML_Test.java)
classfiles =	$(foreach javafile,$(javafiles),\
		$(subst .java,.class,$(javafile)))

current_focus =	src/EmptySequence.java src/NonEmptySequence.java
core_files =	Cons.java Pair.java Sequence.java EmptySequence.java NonEmptySequence.java

javadoc =	javadoc
jmldoc =	jmldoc
javadocflags =	-version -author -private -source 1.4
jmldocflags =	-version -author -private --source 1.4
javadocdir =	$(basedocdir)/javadocs
jmldocdir =	$(basedocdir)/jmldocs

main_memory_use =	-ms256M -mx256M
rac_memory_use =	-ms256M -mx320M
test_memory_use	=	-ms256M -mx320M

copyright = "CK JML Model Classes<br />&copy; 2005 Patrice Chalin and Joseph Kiniry<br />All Rights Reserved"

# implicit rules for paper documentation generation

%.ps: %.gif
	giftopnm $< | pnmtops -noturn > $@
%.ps: %.fig
	fig2dev -L ps $< > $@
%.eps: %.fig
	fig2dev -L eps $< > $@
%.pdf: %.fig
	fig2dev -L pdf $< > $@
%.pdf: %.eps
	epstopdf $< > $@
.pdf_t: %.pstex_t
	sed 's/\.pstex/\.pdf/g' $< > $@
%.pdftex: %.tex
	sed 's/\.pstex_t/\.pdf_t/g' $< > $@
%.pstex: %.fig
	fig2dev -L pstex -m $(FIGSCALE) $< > $@
%.pstex_t: %.fig
	fig2dev -L pstex_t -m $(FIGSCALE) -p `basename $< .fig`.pstex $< > $@
%.ps: %.dvi
	dvips -D600 -Ppdf $< -o $@

%.aux: %.tex
	latex $*

%.dvi: %.tex
	latex $<
	if grep $(BIBWARN) $*.log >/dev/null; \
	then bibtex $(BIBTEXOPT) $*; latex $<; latex $<; fi
	RUNS=$(LATEXMAX); \
	while [ $$RUNS -gt 0 ] ; do \
		if grep $(REFWARN) $*.log > /dev/null; \
		then latex $< ; else break; fi; \
		RUNS=`expr $$RUNS - 1`; \
	done

%.pdf: %.ps
	ps2pdf $<

# identification of phony targets

.PHONY: all build escjava test ps pdf spellcheck \
	classes jmlc jmlunit jmlunit_classes \
	escjava2-typecheck escjava2 escjava2-current escjava2-core \
	main main-jmlrac jml-junit-tests jmlrac-tests \
	source_docs javadoc jmldoc checkstyle \
	clean clean_other_stamps clean_classes clean_jmlc \
	clean_jmlcjunit clean_jmlunit \
	clean_javadoc clean_jmldoc

# targets

all:	build source_docs test escjava distr

build:	classes jml jmlc jmlunit_classes

escjava:	escjava2-typecheck escjava2

test:	jmlrac-tests

# paper documentation-related

ps:	$(BASE).ps

$(BASE).dvi:	$(BASE).tex\
		$(BASE).bbl

$(BASE).bbl:	$(BASE).aux\
		$(BASE).bib
		bibtex $(BIBTEXOPT) $(BASE)

$(BASE).ps:		$(BASE).dvi

$(BASE).pdf:	$(BASE).ps
		ps2pdf13 $(BASE).ps

pdf:		$(BASE).pdf

ps:		$(BASE).ps

spellcheck:
		aspell --lang=american --master=american -t -c $(BASE).tex
#aspell --lang=british --master=british -t -c $(BASE).tex

# targets related to building software

classes:	$(timestamppath)/classes.stamp

$(timestamppath)/classes.stamp:	$(javafiles)
	@mkdir -p $(buildpath)
	export CLASSPATH=$(JAVAC_CLASSPATH);\
	javac -g -d $(buildpath) -source 1.4 $(javapat) && \
	touch $(timestamppath)/classes.stamp

jml:	$(timestamppath)/jml.stamp

$(timestamppath)/jml.stamp:	$(javafiles)
	export CLASSPATH=$(JMLC_CLASSPATH);\
	jml --purity --Quiet --source 1.4 $(javapat) && \
	touch $(timestamppath)/jml.stamp

jmlc:	$(timestamppath)/jmlc.stamp

$(timestamppath)/jmlc.stamp:	$(javafiles)
	@mkdir -p $(jmlc_path)
	export CLASSPATH=$(JMLC_CLASSPATH);\
	jmlc --destination $(jmlc_path) \
		--purity --Quiet --source 1.4 $(javapat) && \
	touch $(timestamppath)/jmlc.stamp

jmlunit:	jmlc $(timestamppath)/jmlunit.stamp

$(timestamppath)/jmlunit.stamp:	$(javafiles)
	@mkdir -p $(jmlunit_path)
	export CLASSPATH=$(JAVAC_CLASSPATH);\
	jmlunit --destination $(jmlunit_path) \
		--sourcepath $(specpath):$(srcpath) \
		--package --source 1.4 \
		--testLevel=2 $(srcpath)/ && \
	touch $(timestamppath)/jmlunit.stamp

jmlunit_classes:	jmlunit $(timestamppath)/jmlunit_classes.stamp

$(timestamppath)/jmlunit_classes.stamp:	$(jmlunitfiles)
	@mkdir -p $(jmlc_path)
	export CLASSPATH=$(JUNIT_CLASSPATH);\
	javac -g -d $(jmlc_path) -source 1.4 $(jmlunitpat) && \
	touch $(timestamppath)/jmlunit_classes.stamp

# targets related to checking software

escjava2-typecheck:	$(timestamppath)/escjava2-typecheck.stamp

$(timestamppath)/escjava2-typecheck.stamp:	$(javafiles)
	export CLASSPATH=$(ESCJAVA_CLASSPATH);\
	$(escjava) -typecheck $(javapat) && \
	touch $(timestamppath)/escjava2-typecheck.stamp

escjava2:	$(timestamppath)/escjava2.stamp

$(timestamppath)/escjava2.stamp:	$(javafiles)
	export CLASSPATH=$(ESCJAVA_CLASSPATH);\
	$(escjava) $(javapat) && \
	touch $(timestamppath)/escjava2.stamp

escjava2-current:
	export CLASSPATH=$(ESCJAVA_CLASSPATH);\
	$(escjava) -bootclasspath $(BOOTCP) \
		$(current_focus)

escjava2-core:
	export CLASSPATH=$(ESCJAVA_CLASSPATH);\
	$(escjava) -bootclasspath $(BOOTCP) \
		$(core_files)

$(timestamppath)/checkstyle.stamp:	$(javafiles)
	export CLASSPATH=$(CHECKSTYLE_CLASSPATH); \
	java com.puppycrawl.tools.checkstyle.Main \
		-c sos-group.xml $(javafiles) &&
	touch $(timestamppath)/checkstycle.stamp

checkstyle:	$(timestamppath)/checkstyle.stamp

# executing the program

main: classes
	export CLASSPATH=$(JAVAC_CLASSPATH);\
	java $(main_memory_use) Main

main-jmlrac: jmlc
	export CLASSPATH=$(JMLC_CLASSPATH);\
	jmlrac $(rac_memory_use) Main

jml-junit-tests:	classes jmlunit_classes
	export CLASSPATH=$(UNIT_TEST_CLASSPATH);\
	jml-junit $(test_memory_use) Cons_JML_Test Pair_JML_Test Sequence_JML_Test &

jmlrac-tests:	jmlunit_classes classes
	export CLASSPATH=$(UNIT_TEST_CLASSPATH);\
	jmlrac $(test_memory_use) Cons_JML_Test
	export CLASSPATH=$(UNIT_TEST_CLASSPATH);\
	jmlrac $(test_memory_use) Pair_JML_Test
	export CLASSPATH=$(UNIT_TEST_CLASSPATH);\
	jmlrac $(test_memory_use) Sequence_JML_Test

jmlrac-tests-current:	classes jmlunit_classes
	export CLASSPATH=$(UNIT_TEST_CLASSPATH);\
	jmlrac $(test_memory_use) Cons_JML_Test

# generating source-based documentation

source_docs:	javadoc jmldoc

javadoc:	$(timestamppath)/javadoc.stamp

$(timestamppath)/javadoc.stamp:	$(javafiles)
	mkdir -p $(javadocdir); \
	export CLASSPATH=$(BASE_CLASSPATH);\
	$(javadoc) -d $(javadocdir) $(javadocflags) \
	-sourcepath .:$(srcpath):$(jdksrcpath) \
	-overview $(basedocdir)/overview.html \
	-doctitle "CK Model Classes" \
	-header $(copyright) \
	-footer $(copyright) \
	-subpackages ck; \
	touch $(timestamppath)/javadoc.stamp

jmldoc:		$(timestamppath)/jmldoc.stamp

$(timestamppath)/jmldoc.stamp:	$(javafiles)  
	mkdir -p $(jmldocdir); \
	export CLASSPATH=$(BASE_CLASSPATH);\
	$(jmldoc) -d $(jmldocdir) $(jmldocflags) \
	-sourcepath .:$(srcpath):$(jdksrcpath) \
	-overview $(basedocdir)/overview.html \
	-doctitle "CK Model Classes" \
	-header $(copyright) \
	-footer $(copyright) \
	modelclasses; \
	touch $(timestamppath)/jmldoc.stamp


release:
	echo '$(RELEASE)' > $(version_file)
	date >> $(version_file)

distr:	$(timestamppath)/distr.stamp

$(timestamppath)/distr.stamp: release classes clean_distr usermanual
	mkdir -p distr/tmp
	mkdir -p distr/koa
	mkdir -p distr/koa/lib
	mkdir -p distr/koa/doc
	cp -r xml distr/tmp
	cp -r build/* distr/tmp
	jar -J-Xmx256M -mcf MANIFEST.MF distr/koa/koa.jar -C distr/tmp .
	rm -rf distr/tmp
	cp $(JCECP) distr/koa/lib/
	cp jars/avalon-framework.jar distr/koa/lib
	cp jars/batik.jar distr/koa/lib
	cp jars/fop.jar distr/koa/lib
	cp $(usermanual_pdf) distr/koa/doc
	cd distr/koa; jar -i koa.jar
	cd distr; zip koa.zip koa/koa.jar koa/lib/*
	$(timestamppath)/touch distr.stamp

src_distr:	$(timestamppath)/src_distr.stamp 

$(timestamppath)/src_distr.stamp: distr clean_src_distr
	mkdir -p distr/koa/src/sos/koa
	mkdir -p distr/koa/doc/javadocs
	mkdir -p distr/koa/doc/jmldocs
	cp src/sos/koa/*.java distr/koa/src/sos/koa
	cp src/sos/koa/*.html distr/koa/src/sos/koa
	cp -r doc/javadocs/* distr/koa/doc/javadocs
	cp -r doc/jmldocs/* distr/koa/doc/jmldocs
	cp doc/koa.css distr/koa/doc 
	cp doc/overview.html distr/koa/doc 
	cp ChangeLog distr/koa
	cp $(version_file) distr/koa
	cd jars; cp -r src ../distr/koa/lib/
	rm -rf distr/koa/lib/src/CVS
	cat README.header > distr/$(readme_file)
	cd distr; zip -r koa.zip koa/
	cd distr; echo '' >> $(readme_file)
	cd distr; echo 'The binaries:' >> $(readme_file)
	cd distr; echo '----' >> $(readme_file)
	cd distr; unzip -l koa.zip |grep 'jar' >> $(readme_file)
	cd distr; echo '' >> $(readme_file)
	cd distr; echo 'The documentation:' >> $(readme_file)
	cd distr; echo '----' >> $(readme_file)
	cd distr; unzip -l koa.zip |grep 'docs' | grep -v 'html' |grep -v 'sos' |grep -v 'package' |grep -v 'resources' | grep -v 'stylesheet' >> $(readme_file)
	cd distr; unzip -l koa.zip |grep 'pdf' >> $(readme_file)
	cd distr; unzip -l koa.zip |grep 'package' | grep 'src' >> $(readme_file)
	cd distr; unzip -l koa.zip |grep 'Change' >> $(readme_file)
	cd distr; unzip -l koa.zip |grep 'README' >> $(readme_file)
	cd distr; unzip -l koa.zip |grep 'VERSION' >> $(readme_file)
	cd distr; echo '' >> $(readme_file)
	cd distr; echo 'The sources:' >> $(readme_file)
	cd distr; echo '----' >> $(readme_file)
	cd distr; unzip -l koa.zip |grep 'src'|grep 'sos/koa' |grep -v 'java'|grep -v 'html' >> $(readme_file)
	cd distr; unzip -l koa.zip |grep 'src'|grep 'lib' >> $(readme_file)
	cat README.footer >> distr/$(readme_file)
	cd distr; zip -r koa.zip $(readme_file)
	touch $(timestamppath)/src_distr.stamp

usermanual:	$(timestamppath)/usermanual.stamp

$(timestamppath)/usermanual.stamp:	
	cd $(usermanual_dir); make pdf && \
	touch $(timestamppath)/usermanual.stamp

# targets related to cleaning up

clean:	clean_javadoc clean_jmldoc clean_classes clean_jml clean_jmlc clean_jmlunit clean_jmlcjunit clean_other_stamps clean_distr clean_src_distr clean_usermanual
	rm -f $(BASE).dvi $(BASE).ps $(BASE).pdf
	rm -f *.log *.bbl *.blg *.aux *.out
	rm -f *.pstex *.pstex_t *.pdf *.pdf_t *.pdftex
	rm -f *.bak

clean_other_stamps:
	rm -f $(timestamppath)/escjava2-typecheck.stamp \
	  $(timestamppath)/escjava2.stamp \
	  $(timestamppath)/checkstyle.stamp

clean_classes:
	rm -rf distr $(buildpath) \
	  $(timestamppath)/classes.stamp $(timestamppath)/jmlunit_classes.stamp

clean_jml:
	rm -rf $(timestamppath)/jml.stamp

clean_jmlc:
	rm -rf $(jmlc_path) $(timestamppath)/jmlc.stamp

clean_jmlunit:
	rm -f $(generated_jmlunitfiles) $(timestamppath)/jmlunit.stamp

clean_javadoc:
	rm -rf $(javadocdir)/*.html \
		$(javadocdir)/ck* \
		$(javadocdir)/com* \
		$(javadocdir)/images \
		$(javadocdir)/package-list \
		$(javadocdir)/stylesheet.css \
		$(timestamppath)/javadoc.stamp

clean_jmldoc:
	rm -rf $(jmldocdir)/*.html \
		$(jmldocdir)/ck* \
		$(jmldocdir)/com* \
		$(jmldocdir)/images \
		$(jmldocdir)/package-list \
		$(jmldocdir)/stylesheet.css \
		$(timestamppath)/jmldoc.stamp

clean_distr:
	rm -rf distr

clean_src_distr:
	rm -rf $(timestamppath)/src_distr.stamp

clean_usermanual:
	rm -rf $(timestamppath)/usermanual.stamp
