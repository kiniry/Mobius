# $Id$

FILES = JMLTutorial
PSFILES = $(FILES:%=%.ps)
PDFFILES = $(FILES:%=%.pdf)
HANDOUTS = $(FILES:%=%.ps4.pdf)

LATEX=echo n | latex
PDFLATEX=echo n | pdflatex
# mlatex is the miktex version of latex
HLATEX=echo y | mlatex
HPDFLATEX=echo y | mpdflatex
DVIPS=dvips  
PSNUP=psnup
PS2PDF=ps2pdf

pdf: $(PDFFILES)

handouts: $(HANDOUTS)

both: pdf handouts

ps: $(PSFILES)

%.pdf: %.tex
	$(PDFLATEX) $<
	$(PDFLATEX) $<

%.ps4.pdf: %.tex
	$(HPDFLATEX) $<
	$(HPDFLATEX) $<
	mv $(subst .tex,.pdf,$<) $@

%.dvi: %.tex
	$(LATEX) $<
	$(LATEX) $<

%.ps: %.dvi
	$(DVIPS) -o $@ $<

%.ps4.ps: %.ps
	$(PSNUP) -2 $< >$<4.ps

cleanall: clean
	rm -f *.pdf

clean:
	rm -f *.dvi *.ps *.log *.out *~
