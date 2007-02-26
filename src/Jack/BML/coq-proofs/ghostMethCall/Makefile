FILES=BasicDef.vo SemanticLevels.vo Language.vo LanguageGhost.vo  LogicLevels.voLogicWithGhost.vo  Main.vo



all: clean noclean
		
noclean: $(FILES)

%.vo : 
	coqc BasicDef
	coqc LanguageGhost
	coqc Language
	coqc SemanticLevels	 
	coqc LogicLevels
	coqc LogicWithGhost
	coqc Main
	

clean: 
	rm -f *.vo *~
