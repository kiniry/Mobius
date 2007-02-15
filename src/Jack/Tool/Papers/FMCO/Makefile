source = main.tex

#######################################################
dest =  $(foreach sourcefile,$(source), \
             $(subst .tex,.pdf,$(sourcefile)))
destpdf =  $(foreach sourcefile,$(source), \
             $(subst .tex,.pdf,$(sourcefile)))

pngfiles =      $(wildcard *.png)

pngpsfiles =  $(foreach pngfile,$(pngfiles), \
             $(subst .png,.ps,$(pngfile)))

jpgfiles =      $(wildcard *.jpg)

jpgpsfiles =  $(foreach jpgfile,$(jpgfiles), \
             $(subst .jpg,.ps,$(jpgfile)))

dotfiles =      $(wildcard *.dot)

dotpsfiles =  $(foreach dotfile,$(dotfiles), \
             $(subst .dot,.ps,$(dotfile)))

texfiles =      $(wildcard *.tex)
bibfiles =      $(wildcard *.bib)
graphicfiles =  $(pngpsfiles) $(jpgpsfiles)

####################################################

all:  $(graphicfiles) $(dest) 
everything: all $(destpdf)

%.tex: %.java
	tiny_c2l < $< > $@ 

%.dvi: %.tex *.tex 
	latex $<
	-bibtex $*
	latex $<
	latex $<

%.png: %.dot
	dot -Tpng  -o $@ $<

%.pnm : %.png
	pngtopnm $< > $@


%.pdf : %.tex $(texfiles)  $(bibfiles)
	pdflatex $<
	-bibtex $*
	 pdflatex $<
	pdflatex $<



%.pnm : %.jpg
	jpegtopnm $< > $@


%.ps : %.dvi
	dvips $< -o

%.ps : %.pnm
	pnmtops -noturn $< > $@

%.dvi : %.tex
	texi2dvi $<
add:
	cvs add *.tex *.dot *.bib *.v

clean :
	@echo Cleaning.
	@rm -f *.html *.pdf *.dvi *~ *.ps *.log *.aux *.bbl *.blg




