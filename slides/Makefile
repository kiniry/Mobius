#
# Mobius: Mobility, Ubiquity and Security
#
# Task 3.3
#
# Program Verification Environment
#
# Makefile to build Mobius Tools Overview talk given at Madrid annual
# meeting by Joe Kiniry on 19 June 2006.

.PHONY: clean tidy view

TEXSOURCES= \
    Mobius_Tools_Overview-Madrid-19.06.2006.tex

DRAWINGS= 

PDFINCLUSIONS=

DOC= Mobius_Tools_Overview-Madrid-19.06.2006

.SUFFIXES: .fig .pdf .tex

Mobius_Tools_Overview-Madrid-19.06.2006.pdf: $(TEXSOURCES) $(DRAWINGS) $(PDFINCLUSIONS)
#	svnversion --no-newline . > svnRevision.tex  ## get version no.
	pdflatex $(DOC)
	pdflatex $(DOC)
	open $(DOC).pdf

view:
	open $(DOC).pdf

.fig.pdf:
	fig2dev -Lpdf $*.fig $*.pdf

clean:
	rm -f $(DOC).pdf
	rm -f *.log *.aux *.blg *.toc *.out *.nav *.snm

tidy: clean
	rm -f *.bak *~

### Local Variables: 
### fill-column: 70
### End: 

# End of file
