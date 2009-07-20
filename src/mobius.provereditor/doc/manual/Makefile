TG= manual.html
all: clean real

real: ${TG}
	@make images

install: real
	cd build; scp -r * jcharles@provereditor.gforge.inria.fr:/home/groups/provereditor/htdocs
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
	@cd build; cp ../style.css manual.css
clean :
	@echo Cleaning.
	@rm -f *.html *.pdf *.dvi *.gif *.jpg *~ *.htoc *.haux
	@rm -rf build/* 

