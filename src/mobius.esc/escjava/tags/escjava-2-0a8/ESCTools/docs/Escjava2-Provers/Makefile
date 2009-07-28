#
# $Id$
#

paper =		Escjava2-Provers

talk =		

texfiles =	$(wildcard *.tex)

texifiles =	$(wildcard *.texinfo)

dvifiles =	$(foreach texfile,$(texfiles),\
		$(subst .tex,.dvi,$(texfile)))

psfiles =	$(foreach texfile,$(texfiles),\
		$(subst .tex,.ps,$(texfile)))

pdffiles =	$(foreach texfile,$(texfiles),\
		$(subst .tex,.pdf,$(texfile)))

java_files =		$(wildcard *.java)
java_texinfo_files =	$(addsuffix .texinfo,$(java_files))

PERL=perl
CODE2TEXI=$(PERL) -e 'BEGIN: while (<>) { s/\r//g; s/@/@@/g; s/\{/@\{/g; s/\}/@\}/g; } continue { print; }'

%.java.texinfo: %.java
	@$(CODE2TEXI) $< > $@

%.pdf: %.tex
	pdflatex $< $@
	make cleanup

%.pdf:	%.ps
	ps2pdf $<

%.pdf.gz: %.pdf
	gzip -c $< > $@

%.ps: %.dvi
	dvips -Pcmz -Pamz -f < $< > $@

%.ps.gz: %.ps
	gzip -c $< > $@

%.dvi: %.tex
	latex $<

# ${paper}.dvi: ${paper}.tex
# 	latex ${paper}; latex ${paper}; bibtex ${paper}; \
# 	latex ${paper}; latex ${paper}; \

# ${paper}.dvi: ${paper}.tex
# 	latex ${paper}; latex ${paper};

# ${talk}.ps: ${talk}.dvi
# 	dvips -ta4 -Pcmz -Pamz -f < $< > $@

# ${talk}.dvi: ${talk}.tex
# 	latex ${talk};

%.pdf:	%.texinfo
	texi2pdf $<
	texindex `basename $< .texinfo`.??
	texi2pdf $<

%.info:	%.texinfo
	makeinfo $<

%.txt:	%.texinfo
	makeinfo --no-headers $< -o $@

%.html:	%.texinfo
	makeinfo --html	$<

%.dvi:	%.texinfo
	texi2dvi $<
	texindex `basename $< .texinfo`.??
	texi2dvi $<

%.eps: %.fig
	fig2dev -L eps $< $@

%.pdf: %.fig
	fig2dev -L pdf $< $@

.PHONY: all build
all:	build

build:	Escjava2-Provers.pdf

Escjava2-Provers.pdf:	Escjava2-Provers.texinfo $(java_texinfo_files)

cleanup:
	rm -f _region_* *.aux *.log \
		*.cp *.cps *.fn *.fns *.ky *.kys \
		*.pg *.pgs *.tp *.tps *.vr *.vrs *.p *.k \
		*# *~

clean:
	rm -rf auto _region_* \
		$(paper).pdf $(paper).ps \
		*.aux *.log *~ *.dvi *.brf \
		*.cp *.cps *.fn *.fns *.ky *.kys \
		*.pg *.pgs *.tp *.tps *.vr *.vrs *.p *.k \
		*.bbl *.blg *.toc *.thm *.out *.cb \
		*.lof *.lot *.gz *.Z #*
