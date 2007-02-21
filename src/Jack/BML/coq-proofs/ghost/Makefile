FILES=BasicDef.vo Semantic.vo Language.vo LanguageGhost.vo LogicWithGhost.vo Logic.vo axioms.vo



all: clean noclean
		
noclean: $(FILES)

%.vo : 
	coqc BasicDef
	coqc Language
	coqc LanguageGhost
	coqc Semantic	 
	coqc LogicWithGhost
	coqc Logic
	coqc axioms
	coqc Main



clean: 
	rm -f *.vo *~
