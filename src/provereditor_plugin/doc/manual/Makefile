TG= manual.html
CSS=../../../style.css
CSSed=..\\/..\\/..\\/style.css
all: clean real

real: ${TG}
	@make images


images:
	@echo Copying images.
	@cd img; cp * ../build

%.pdf : %.tex
	texi2pdf $<
%.ps : %.dvi
	dvips $< -o
%.dvi : %.tex
	texi2dvi $<

%.html : %.tex
	@echo "Running Hevea on $<"
	@cd build; hevea ../macro.hva ../$< 
	
	@echo "Running Hacha"
	@cd build; hacha $@ -o i$@

clean :
	@echo Cleaning.
	@rm -f *.html *.pdf *.dvi *.gif *.jpg *~ *.css *.htoc *.haux
	@rm -rf build; mkdir build 

