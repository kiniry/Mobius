# $Id$

FILES = JMLTutorial
PSFILES = $(FILES:%=%.ps)
PDFFILES = $(FILES:%=%.pdf)
HANDOUTS = $(FILES:%=%.ps4.pdf)

LATEX=latex
PDFLATEX=pdflatex
DVIPS=dvips  
PSNUP=psnup
PS2PDF=ps2pdf

all: pdf

both: pdf handouts

pdf: $(PDFFILES)

handouts: $(HANDOUTS)

ps: $(PSFILES)

%.dvi: %.tex
	$(LATEX) $<
	$(LATEX) $<

%.ps: %.dvi
	$(DVIPS) -o $@ $<

%.pdf: %.tex
	$(PDFLATEX) $<

%.ps4.ps: %.ps
	$(PSNUP) -2 $< >$<4.ps

%.ps4.pdf: %.ps4.ps
	$(PS2PDF) $<

cleanall: clean
	rm -f *.pdf

clean:
	rm -f *.dvi *.ps *.log *.out *~

