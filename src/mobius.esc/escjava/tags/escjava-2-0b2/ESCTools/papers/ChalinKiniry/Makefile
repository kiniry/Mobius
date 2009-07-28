#
# $Id$
#

paper =		savcbs05

talk = 		talk

texfiles =	$(wildcard *.tex)

dvifiles =	$(foreach texfile,$(texfiles),\
		$(subst .tex,.dvi,$(texfile)))

psfiles =	$(foreach texfile,$(texfiles),\
		$(subst .tex,.ps,$(texfile)))

pdffiles =	$(foreach texfile,$(texfiles),\
		$(subst .tex,.pdf,$(texfile)))

.PHONY: all talk archive

all:	${paper}.pdf view

view:
	open ${paper}.pdf

talk: 	talk.ps talk.pdf

# archive: ime.pdf
# 	tar cjf ENTCS-UITP-04.tbz \
# 		entcsmacro.sty snapshot.sty kt.tex \
# 		Makefile \
# 		ime.tex pvsui.bib ime.pdf ime.bbl \
# 		ECB.pdf function_hierarchy.pdf pvs.pdf

${paper}.pdf: ${paper}.tex
	pdflatex ${paper};
	pdflatex ${paper};
	bibtex ${paper};
	pdflatex ${paper};
	pdflatex ${paper};

cleanup:
	rm -f _region_* *.aux *.log *# *~

clean:
	rm -rf auto _region_* \
		*.aux *.log *~ *.dvi ${paper}.ps ${paper}.pdf *.brf *.txt \
		*.bbl *.blg *.toc *.thm *.out *.cb *.dep \
		*.lof *.lot *.gz *.Z TAGS #*

