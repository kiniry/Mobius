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

all:	CASSIS2004.pdf FTFJP2004.pdf PASTE2004.pdf NIII-R0413.pdf \
	jml_homework.ps2pdf jml_homework.txt jml_homework.html

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

koa_state_diagram.eps: koa_state_diagram.fig Makefile
	fig2dev -L eps koa_state_diagram.fig koa_state_diagram.eps

koa_state_diagram.pdf: koa_state_diagram.fig Makefile
	fig2dev -L pdf koa_state_diagram.fig koa_state_diagram.pdf

cleanup:
	rm -f _region_* *.aux *.log *# *~

clean:
	rm -rf auto _region_* \
		*.aux *.log *~ *.dvi ${paper}.ps ${paper}.pdf *.brf *.txt \
		*.bbl *.blg *.toc *.thm *.out *.cb \
		*.lof *.lot *.gz *.Z #*
