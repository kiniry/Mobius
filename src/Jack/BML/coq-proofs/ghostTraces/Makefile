FILES=BasicDef.vo Semantic.vo Language.vo LogicWithGhost.vo Logic.vo 



all: clean noclean
		
noclean: $(FILES)

%.vo : 
	coqc BasicDef
	coqc Language
	coqc Semantic	 



clean: 
	rm -f *.vo *~
