TG=   slides.ps slides.pdf
all:  real

real:  ${TG} dot 


escjava.png: escjava.dot
	dot -Tpng  -o escjava.png escjava.dot

jack.png: jack.dot
	dot -Tpng  -o jack.png jack.dot
coqeditor: CoqEditor.tex coqeditor.ps coqeditor2.ps coqeditor1.ps 
basics: basics.tex jack.ps escjava.ps
slides.dvi: slides.tex coqeditor interfacing_prover.tex basics coq.tex
	latex slides.tex	

dot: everest_logo.ps 
	psnup -2 -pa4 -r  slides.ps slides_too.ps	
	psnup -2 -pa4 slides_too.ps slides_4.ps

dot2:
	dot -Tgif  -o jack.gif jack.dot

%.png : %.dot
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

clean :
	@echo Cleaning.
	@rm -f *.html *.pdf *.dvi *~ *.ps *.log *.aux

