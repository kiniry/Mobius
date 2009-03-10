COQC=coqc


all: bicolano main
	cd classes; make all

bicolano: 
	@echo 
	@echo Making Bicolano
	@echo 
	@if [ -d Formalisation/Makefile ]; then cd Formalisation; make; fi

main: signature
	@echo 
	@echo Compiling the main files...
	@echo 
	@cd classes; make main
	$(COQC) Bico.v

signature: type
	@echo 
	@echo Compiling signatures...
	@echo 
	@cd classes; make signature
	$(COQC) Bico_signature.v

type: 
	@echo 
	@echo Compiling types...
	@echo 
	@cd classes; make type
	$(COQC) Bico_type.v


# implicit rules
%.vo : %.v
	$(COQC) $<

