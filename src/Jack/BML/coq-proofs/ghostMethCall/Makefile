FILES=BasicDef.vo SemanticLevels.vo Language.vo LanguageGhost.vo  Logic.vo LogicWithGhost.vo  Main.vo



all: clean noclean
		
noclean: $(FILES)

%.vo : 
	coqc BasicDef
	coqc LanguageGhost
	coqc Language
	coqc SemanticLevels	 
	coqc Logic
	coqc LogicWithGhost
	coqc Main
	

clean: 
	rm -f *.vo *~
