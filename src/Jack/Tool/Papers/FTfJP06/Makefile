all:  llncs.ps 

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


%.pdf : %.ps
	ps2pdf $<


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
	@rm -f *.html *.pdf *.dvi *~ *.ps




