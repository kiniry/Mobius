FILES=BasicDef.vo Semantic.vo Language.vo LanguageGhost.v  LogicPartial.vo LogicPartialGhost.vo LogicReach.vo  MainPartial.vo



all: clean noclean
		
noclean: $(FILES)

%.vo : 
	coqc BasicDef
	coqc Language
	coqc LanguageGhost
	coqc Semantic	 
	coqc LogicPartial 
	coqc LogicPartialGhost
	coqc LogicReach 
	coqc LogicReachGhost
	coqc MainPartial
	coqc MainReach

clean: 
	rm -f *.vo *~
