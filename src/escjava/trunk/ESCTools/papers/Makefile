#
# $Id$
#

paper =		

talk =		

texfiles =	$(wildcard *.tex)

dvifiles =	$(foreach texfile,$(texfiles),\
		$(subst .tex,.dvi,$(texfile)))

psfiles =	$(foreach texfile,$(texfiles),\
		$(subst .tex,.ps,$(texfile)))

pdffiles =	$(foreach texfile,$(texfiles),\
		$(subst .tex,.pdf,$(texfile)))

javafiles =		$(wildcard problems/*.java)
javatexinfofiles =	$(addsuffix .texinfo,$(javafiles))
PROBLEMS =	problems

PERL=perl
CODE2TEXI=$(PERL) -e 'BEGIN: while (<>) { s/\r//g; s/@/@@/g; s/\{/@\{/g; s/\}/@\}/g; } continue { print; }'

$(PROBLEMS)/%.java.texinfo : $(PROBLEMS)/%.java
	@$(CODE2TEXI) $< > $@

%.pdf: %.tex
	pdflatex $< $@

%.ps2pdf: %.ps
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

%.info:	%.texinfo
	makeinfo $<

%.txt:	%.texinfo
	makeinfo --no-headers $< -o $@

%.html:	%.texinfo
	makeinfo --html	$<

%.dvi:	%.texinfo
	texi2dvi $<

.PHONY: all build
all:	build

build:	CASSIS2004.pdf FTFJP2004.pdf PASTE2004.pdf NIII-R0413.pdf \
	jml_homework.dvi jml_homework.ps jml_homework.ps2pdf jml_homework.txt jml_homework.html

jml_homework.dvi:	jml_homework.texinfo $(javatexinfofiles)

CASSIS2004.pdf:	CASSIS2004.tex koa_state_diagram.pdf
	pdflatex CASSIS2004; bibtext CASSIS2004; pdflatex CASSIS2004; pdflatex CASSIS2004;

CASSIS2004.dvi:	CASSIS2004.tex koa_state_diagram.ps
	latex CASSIS2004; bibtext CASSIS2004; latex CASSIS2004; latex CASSIS2004;

koa_state_diagram.eps: koa_state_diagram.fig Makefile
	fig2dev -L eps koa_state_diagram.fig koa_state_diagram.eps

koa_state_diagram.pdf: koa_state_diagram.fig Makefile
	fig2dev -L pdf koa_state_diagram.fig koa_state_diagram.pdf

cleanup:
	rm -f _region_* *.aux *.log \
		*.cp *.cps *.fn *.ky *.pg *.tp *.vr \
		*# *~

clean:
	rm -rf auto _region_* \
		*.aux *.log *~ *.dvi *.ps *.pdf *.brf \
		*.cp *.cps *.fn *.ky *.pg *.tp *.vr \
		*.bbl *.blg *.toc *.thm *.out *.cb \
		*.lof *.lot *.gz *.Z #*
