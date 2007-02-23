FILES=BasicDef.vo SemanticLevels.vo Language.vo LanguageGhost.vo  LogicLevels.vo 



all: clean noclean
		
noclean: $(FILES)

%.vo : 
	coqc BasicDef
	coqc LanguageGhost
	coqc Language
	coqc SemanticLevels	 
	coqc LogicLevels
	

clean: 
	rm -f *.vo *~
