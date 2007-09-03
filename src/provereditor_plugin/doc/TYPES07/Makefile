#
# $Id: Makefile,v 1.1 2004/08/27 06:47:36 kiniry Exp $
#

paper =		paper

talk = 		talk

texfiles =	$(wildcard *.tex)
jpgfiles =	$(wildcard *.jpg)
dvifiles =	$(foreach texfile,$(texfiles),\
		$(subst .tex,.dvi,$(texfile)))

psfiles =	$(foreach texfile,$(texfiles),\
		$(subst .tex,.ps,$(texfile))) $(foreach jpgfile,$(jpgfiles), $(subst .jpg,.ps,$(jpgfile)))
graphicfiles =	$(foreach jpgfile,$(jpgfiles), \
             $(subst .jpg,.ps,$(jpgfile)))

pdffiles =	$(foreach texfile,$(texfiles),\
		$(subst .tex,.pdf,$(texfile)))

.PHONY: all talk archive

all:	paper.pdf

talk: 	talk.ps talk.pdf

# archive: uitp06.pdf
# 	tar cjf UITP-06.tbz \
# 		entcsmacro.sty snapshot.sty \
# 		Makefile \
# 		paper.tex paper.bib paper.bbl paper.pdf

paper.pdf: $(graphicfiles) paper.tex 
	pdflatex paper;
	pdflatex paper;
	bibtex paper;
	pdflatex paper;
	pdflatex paper;

%.pnm : %.jpg
	jpegtopnm $< > $@

%.ps : %.pnm
	pnmtops -noturn $< > $@

cleanup:
	rm -f _region_* *.aux *.log *# *~

clean:
	rm -rf auto _region_* \
		*.aux *.log *~ *.dvi ${paper}.ps ${paper}.pdf *.brf *.txt \
		*.bbl *.blg *.toc *.thm *.out *.cb *.dep \
		*.lof *.lot *.gz *.Z TAGS #*

