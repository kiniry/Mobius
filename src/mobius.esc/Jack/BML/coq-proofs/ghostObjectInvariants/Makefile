FILES=BasicDef.vo Semantic.vo Language.vo  LogicPartial.vo LanguageGhost.vo LogicPartialGhost.vo 



all: clean noclean
		
noclean: $(FILES)

%.vo : 
	coqc BasicDef
	coqc Language
	coqc Semantic	 
	coqc LogicPartial
	coqc LanguageGhost
	coqc LogicPartialGhost

clean: 
	rm -f *.vo *~
